/* Soot - a J*va Optimization Framework
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

package soot.toolkits.scalar;

import static java.util.Collections.emptyList;
import static java.util.Collections.singletonList;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import soot.IdentityUnit;
import soot.Local;
import soot.Timers;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.options.Options;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.ExceptionalGraph;
import soot.toolkits.graph.ExceptionalGraph.ExceptionDest;
import soot.toolkits.graph.UnitGraph;

/**
 * Analysis that provides an implementation of the LocalDefs interface.
 */
public class SimpleLocalDefs implements LocalDefs {
	static private class StaticSingleAssignment implements LocalDefs {
		final Map<Local, List<Unit>> result;
		StaticSingleAssignment(Local[] locals, List<Unit>[] unitList) {
			assert locals.length == unitList.length;

			final int N = locals.length;
			result = new IdentityHashMap<Local, List<Unit>>(((N*3)/2)+7);

			for (int i = 0; i < N; i++) {
				if (unitList[i].isEmpty())
					continue;
				assert unitList[i].size() == 1;
				result.put(locals[i], unitList[i]);
			}
		}

		@Override
		public List<Unit> getDefsOfAt(Local l, Unit s) {
			List<Unit> lst = result.get(l);
			// singleton-lists are immutable
			return (lst == null) ? Collections.<Unit>emptyList() : lst;
		}
	}

	static private class FlowAssignment extends ForwardFlowAnalysis<Unit, FlowAssignment.FlowBitSet> implements LocalDefs {
		class FlowBitSet extends BitSet {
			private static final long serialVersionUID = -8348696077189400377L;

			FlowBitSet () {
				super(universe.length);
			}

			@Override
			public String toString() {
				return String.valueOf(asList(0, length()));
			}

			List<Unit> asList(int fromIndex, int toIndex) {
				if ((universe.length < toIndex) || (toIndex < fromIndex) || (fromIndex < 0))
					throw new IndexOutOfBoundsException();

				toIndex = Math.min(toIndex, length());
				
				if ((fromIndex + 1) == toIndex) {
					if (get(fromIndex))
						return singletonList(universe[fromIndex]);
					return emptyList();
				}
				
				fromIndex = nextSetBit(fromIndex);
				if (0 > fromIndex || fromIndex > toIndex)
					return emptyList();
				
				BitSet bits = get(fromIndex, toIndex);
				int len = bits.cardinality();

				switch (len) {
				case 0:
					return emptyList();

				case 1:
					return singletonList(universe[(fromIndex - 1) + bits.length()]);

				default:
					Unit[] a = new Unit[len];

					for (int j = 0, i = 0; i >= 0; i = bits.nextSetBit(i + 1)) {
						int l = bits.nextClearBit(i + 1) - i;
						System.arraycopy(universe, fromIndex + i, a, j, l);
						j += l;
						i += l;
					}

					return Arrays.asList(a);
				}
			}
		}

		final Map<Local, Integer> locals;
		final List<Unit>[] unitList;
		final int[] localRange;
		final Unit[] universe;

		private Map<Unit, Integer> indexOfUnit;
		FlowAssignment(DirectedGraph<Unit> graph, Local[] locals, List<Unit>[] unitList, int units, boolean disableHybrid) {
			super(graph);

			final int N = locals.length;
			this.locals = new IdentityHashMap<Local, Integer>(((N*3)/2)+7);
			this.unitList = unitList;

			universe = new Unit[units];
			indexOfUnit = new IdentityHashMap<Unit, Integer>((units*3)/2);

			localRange = new int[N + 1];
			for (int j = 0, i = 0; i < N; localRange[++i] = j) {
				if (unitList[i].isEmpty())
					continue;

				this.locals.put(locals[i], i);

				if (unitList[i].size() >= 2) {
					for (Unit u : unitList[i]) {
						indexOfUnit.put(u, j);
						universe[j++] = u;
					}
				} else if (disableHybrid) {
					universe[j++] = unitList[i].get(0);
				}
			}

			doAnalysis();

			indexOfUnit.clear();
			indexOfUnit = null;
			
			unitToAfterFlow = null;
		}

		@Override
		protected void onComplete(FlowBitSet beforeFlow, Unit node, FlowBitSet afterFlow) {
			unitToBeforeFlow.put(node, beforeFlow);
		}

		@Override
		public List<Unit> getDefsOfAt(Local l, Unit s) {
			Integer lno = locals.get(l);
			if (lno == null)
				return emptyList();

			int from = localRange[lno];
			int to = localRange[lno + 1];
			assert from <= to;

			if (from == to) {
				assert unitList[lno].size() == 1;
				// singletonList is immutable
				return unitList[lno];
			}

			return getFlowBefore(s).asList(from, to);
		}
		
		@Override
		protected FlowBitSet flowThrough(FlowBitSet in, Unit unit) {
			if (unit.getDefBoxes().isEmpty())
				return in;
			
			FlowBitSet out = in;
			boolean isIdentity = true;
			
			// reassign all definitions
			for (ValueBox vb : unit.getDefBoxes()) {
				Value v = vb.getValue();
				if (v instanceof Local) {
					Local l = (Local) v;
					int lno = l.getNumber();

					int from = localRange[lno];
					int to = localRange[1+lno];

					if (from == to)
						continue;
					
					if (isIdentity) {
						isIdentity = false;
						out = newInitialFlow();
						copy(in, out);
					}
					
					assert from < to;

					if ((to - from) == 1) {
						// special case: this local has only one def point
						out.set(from);
					} else {
						out.clear(from, to);
						out.set(indexOfUnit.get(unit));
					}
				}
			}
			return out;
		}

		@Override
		protected void flowThrough(FlowBitSet in, Unit unit, FlowBitSet out) {
			throw new AssertionError("should never be called");
		}


		@Override
		protected void copy(FlowBitSet source, FlowBitSet dest) {
			if (dest == source)
				return;
			dest.clear();
			dest.or(source);
		}

		@Override
		protected FlowBitSet newInitialFlow() {
			return new FlowBitSet();
		}

		@Override
		protected void mergeInto(Unit succNode, FlowBitSet inout, FlowBitSet in) {
			inout.or(in);
		}

		@Override
		protected void merge(FlowBitSet in1, FlowBitSet in2, FlowBitSet out) {
			throw new AssertionError("should never be called");
		}
	}

	private LocalDefs def;

	/**
	 *
	 * @param graph
	 */
	public SimpleLocalDefs(UnitGraph graph) {
		this(graph, false);
	}

	public SimpleLocalDefs(UnitGraph graph, boolean disableHybrid) {
		this(graph, graph.getBody().getLocals(), (graph instanceof ExceptionalGraph) && !graph.getBody().getTraps().isEmpty(), disableHybrid);
	}

	SimpleLocalDefs(DirectedGraph<Unit> graph, Collection<Local> locals, boolean isExceptional, boolean disableHybrid) {
		this(graph, locals.toArray(new Local[locals.size()]), isExceptional, disableHybrid);
	}

	SimpleLocalDefs(DirectedGraph<Unit> graph, Local[] locals, boolean isExceptional, boolean disableHybrid) {
		if (Options.v().time())
			Timers.v().defsTimer.start();

		// reassign local numbers
		int[] oldNumbers = new int[locals.length];
		for (int i = 0; i < locals.length; i++) {
			oldNumbers[i] = locals[i].getNumber();
			locals[i].setNumber(i);
		}


		init(graph, locals, isExceptional, disableHybrid);

		// restore local numbering
		for (int i = 0; i < locals.length; i++) {
			locals[i].setNumber(oldNumbers[i]);
		}

		if (Options.v().time())
			Timers.v().defsTimer.end();
	}

	@SuppressWarnings("fallthrough")
	private void init(DirectedGraph<Unit> graph, Local[] locals, boolean isExceptional, boolean disableHybrid) {
		@SuppressWarnings({"unchecked", "rawtypes"})
		List<Unit>[] unitList = new List[locals.length];

		Arrays.fill(unitList, emptyList());

		boolean doFlowAnalysis = disableHybrid;

		int maxUnits = 0;

		// collect all def points
		for (Unit unit : graph) {
			for (ValueBox box : unit.getDefBoxes()) {
				Value v = box.getValue();
				if (v instanceof Local) {
					Local l = (Local) v;
					int lno = l.getNumber();
					List<Unit> t = unitList[lno];

					switch (t.size()) {
					case 0:
						t = singletonList(unit);
						break;
					case 1:
						doFlowAnalysis = true;
						t = new ArrayList<Unit>(t);
						//$$FALL-THROUGH$$
					default:
						t.add(unit);
						break;
					}

					maxUnits++;
					unitList[lno] = t;
				}
			}
		}

		if (doFlowAnalysis) {
			if (isExceptional) {
				// the ugly one: test for exceptional paths
				final ExceptionalGraph<Unit> exg = (ExceptionalGraph<Unit>) graph;

				graph = new DirectedGraph<Unit>() {

					@Override
					public List<Unit> getTails() {
						return exg.getTails();
					}

					@Override
					public List<Unit> getPredsOf(Unit s) {
						return exg.getPredsOf(s);
					}

					@Override
					public int size() {
						return exg.size();
					}

					@Override
					public Iterator<Unit> iterator() {
						return exg.iterator();
					}

					@Override
					public List<Unit> getHeads() {
						List<Unit> result = new ArrayList<Unit>(exg.getHeads());
						
						// handle unreachable traps as entry points!
						for (Trap t : exg.getBody().getTraps()) {
							Unit to = t.getHandlerUnit();
							if (exg.getExceptionalPredsOf(to).isEmpty() && !result.contains(to))
								result.add(to);
						}
						
						return result;
					}

					@Override
					public List<Unit> getSuccsOf(Unit s) {
						// getExceptionDests contains real exceptional destinations
						Collection<? extends ExceptionDest<Unit>> d = exg.getExceptionDests(s);
						
						if (d.isEmpty())
							return exg.getUnexceptionalSuccsOf(s);
						
						Unit handler = null;
						Iterator<? extends ExceptionDest<Unit>> it = d.iterator();
						while ((null == handler) && it.hasNext()) {
							handler = it.next().getHandlerNode();
						}

						if (null == handler)
							return exg.getUnexceptionalSuccsOf(s);
						
						List<Unit> result = new ArrayList<Unit>(exg.getUnexceptionalSuccsOf(s));
						result.add(handler);
						while (it.hasNext()) {
							handler = it.next().getHandlerNode();
							if (null != handler) {
								result.add(handler);
							}
						}
						
						return result;
					}
				};

				def = new FlowAssignment(graph, locals, unitList, maxUnits, disableHybrid) {
					@Override
					protected Flow getFlow(Unit from, Unit to) {
						if ((to instanceof IdentityUnit) && !exg.getExceptionalPredsOf(to).isEmpty()) {
							return Flow.IN;
						}
						return Flow.OUT;
					}
				};
			} else {
				// simple path: no exceptions so the graph can be handled as it is
				def = new FlowAssignment(graph, locals, unitList, maxUnits, disableHybrid);

			}
		} else {
			def = new StaticSingleAssignment(locals, unitList);
		}
	}

	@Override
	public List<Unit> getDefsOfAt(Local l, Unit s) {
		return def.getDefsOfAt(l, s);
	}
}
