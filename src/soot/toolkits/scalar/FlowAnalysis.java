/* Soot - a J*va Optimization Framework
 * Copyright (C) 1997-1999 Raja Vallee-Rai
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

/*
 * Modified by the Sable Research Group and others 1997-1999.
 * See the 'credits' file distributed with Soot for the complete list of
 * contributors.  (Soot is distributed at http://www.sable.mcgill.ca/soot)
 */

package soot.toolkits.scalar;

import static java.util.Arrays.copyOf;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import soot.options.Options;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.interaction.FlowInfo;
import soot.toolkits.graph.interaction.InteractionHandler;
import soot.util.ImmutableArrays;
import soot.util.Numberable;
import soot.util.PriorityQueue;

import com.google.common.collect.ForwardingMap;

/**
 * An abstract class providing a framework for carrying out dataflow analysis.
 * Subclassing either BackwardFlowAnalysis or ForwardFlowAnalysis and providing
 * implementations for the abstract methods will allow Soot to compute the
 * corresponding flow analysis.
 */
public abstract class FlowAnalysis<N, A> extends AbstractFlowAnalysis<N, A> {

	protected enum Flow {
		/**
		 * Use the in-flow
		 */
		IN {
			@Override
			<F> F getFlow(Entry<?, F> e) {
				return e.inFlow;
			}
		},
		/**
		 * Use the out-flow
		 */
		OUT {
			@Override
			<F> F getFlow(Entry<?, F> e) {
				return e.outFlow;
			}
		};

		abstract <F> F getFlow(Entry<?, F> e);
	}
	
	final static private class Entry<D, F> implements Numberable, Comparable<Entry<D, F>> {

		final static private Entry<?,?>[] EMPTY_ENTRY = {};

		final static private <D, F> Entry<D, F>[] emptyEntries() {
			@SuppressWarnings("unchecked")
			Entry<D, F>[] r = (Entry<D, F>[]) EMPTY_ENTRY;
			return r;
		}

		final static private <D, F> Entry<D, F> newEntry(D data) {
			return new Entry<D, F>(data);
		}
		
		final D data;

		int number = Integer.MIN_VALUE;
		int nextSCC;

		Entry<D, F>[] in = emptyEntries();
		Entry<D, F>[] out= emptyEntries();

		F inFlow;
		F outFlow;

		Entry(D u) {
			data = u;
		}

		@Override
		public String toString() {
			return String.valueOf(data);
		}

		/**
		 * tests if in and out flow are the same, and not null
		 * @return
		 */
		private boolean isIdentity() {
			return (inFlow == outFlow) && (null != outFlow);
		}

		@Override
		public void setNumber(int n) {
			number = n;
		}

		@Override
		public int getNumber() {
			return number;
		}

		private void addIn(Entry<D, F> e) {
			int l = in.length;
			in = copyOf(in, l + 1);
			in[l] = e;
		}

		@Override
		public int compareTo(Entry<D, F> o) {
			return number - o.number;
		}

	}

	enum InteractionFlowHandler {
		NONE,
		FORWARD {
			@Override
			<A, N> void handleFlowIn(FlowAnalysis<N, A> a, N s, A f) {
				beforeEvent(stop(s), a, s, f);
			}

			@Override
			<A, N> void handleFlowOut(FlowAnalysis<N, A> a, N s, A f) {
				afterEvent(InteractionHandler.v(), a, s, f);
			}
		},
		BACKWARD {
			@Override
			<A, N> void handleFlowIn(FlowAnalysis<N, A> a, N s, A f) {
				afterEvent(stop(s), a, s, f);
			}

			@Override
			<A, N> void handleFlowOut(FlowAnalysis<N, A> a, N s, A f) {
				beforeEvent(InteractionHandler.v(), a, s, f);
			}
		};

		<A, N> void handleFlowIn(FlowAnalysis<N, A> a, N s, A f) {}
		<A, N> void handleFlowOut(FlowAnalysis<N, A> a, N s, A f) {}

		<A, N> void beforeEvent(InteractionHandler i, FlowAnalysis<N, A> a, N s, A f) {
			i.handleBeforeAnalysisEvent(newFlowInfo(a, s, f, true, a.filterUnitToBeforeFlow));
		}

		<A, N> void afterEvent(InteractionHandler i, FlowAnalysis<N, A> a, N s, A f) {
			i.handleAfterAnalysisEvent(newFlowInfo(a, s, f, false, a.filterUnitToAfterFlow));
		}

		InteractionHandler stop(Object s) {
			InteractionHandler h = InteractionHandler.v();
			List<?> stopList = h.getStopUnitList();
			if ((stopList != null) && stopList.contains(s)) {
				h.handleStopAtNodeEvent(s);
			}
			return h;
		}

		<A, N> FlowInfo<A, N> newFlowInfo(FlowAnalysis<N, A> a, N s, A f, boolean b, Map<N, A> filter) {
			A savedFlow = filter.get(s);
			if (savedFlow == null)
				savedFlow = a.newInitialFlow();
			a.copy(f, savedFlow);
			return new FlowInfo<A, N>(savedFlow, s, b);
		}
	}
	
	enum Orderer {
		BACKWARD {
			@Override
			<K, V> Graph<V> newGraph(final DirectedGraph<K> g, final Mapper<K, V> mapper) {
				return new Graph<V>() {
					@Override
					public V[] get() {
						return mapper.newMapping(g.getTails());
					}

					@Override
					public V[] get(V v) {
						return mapper.newMapping(g.getPredsOf(mapper.getKey(v)));
					}
				};
			}
		},

		FORWARD {
			@Override
			<K, V> Graph<V> newGraph(final DirectedGraph<K> g, final Mapper<K, V> mapper) {
				return new Graph<V>() {
					@Override
					public V[] get() {
						return mapper.newMapping(g.getHeads());
					}

					@Override
					public V[] get(V v) {
						return mapper.newMapping(g.getSuccsOf(mapper.getKey(v)));
					}
				};
			}
		};
		
		abstract <K,V> Graph<V> newGraph(DirectedGraph<K> g, Mapper<K,V> mapper);
		
		private static interface Graph<D> {
			D[] get();
			D[] get(D g);
		}
		
		private static abstract class Mapper<K,V> {
			
			abstract K getKey(V value);
			abstract V getValue(K key);
			abstract V[] newArray(int size);
			
			V[] newMapping(List<K> out) {
				V[] a = newArray(out.size());
				for (int i = 0; i < a.length; i++) {
					a[i] = getValue(out.get(i));
				}
				return a;
			}
		}

		private static class Frame<V> {
			final V v;
			int i = 0;
			boolean isRoot = true;

			Frame(V v) {
				this.v = v;
			}

			static <E> Frame<E> newFrame(E v) {
				return new Frame<E>(v);
			}
		}

		/**
		 * Creates a new {@code Entry} graph based on a {@code DirectedGraph}. This includes
		 * pseudo topological order, local access for predecessors and successors, a graph
		 * entry-point and a {@code Numberable} interface.
		 * @param g
		 * @param outer out of universe node
		 * @return
		 */
		<D, F> List<Entry<D, F>> newUniverse (DirectedGraph<D> g, F f) {
			final int N = g.size();
			
			Mapper<D, Entry<D, F>> mapper = new Mapper<D, Entry<D, F>>() {
				final Map<D, Entry<D, F>> map = new IdentityHashMap<D, Entry<D, F>>((2*N)+1);
				final Entry<D, F>[] zero = Entry.emptyEntries();
				
				@Override
				D getKey(Entry<D, F> value) {
					return value.data;
				}

				@Override
				Entry<D, F> getValue(D key) {
					Entry<D, F> entry = map.get(key);
					if (entry == null) {
						map.put(key, entry = Entry.newEntry(key));
					}
					return entry;
				}

				@Override
				Entry<D, F>[] newArray(int size) {
					return Arrays.copyOf(zero, size);
				}
			};
			
			Entry<D, F> v = Entry.newEntry(null);
			v.inFlow = v.outFlow = f;
			
			return buildUniverse(newGraph(g, mapper), mapper.newArray(N), v);
		}
		
		private <D, F> List<Entry<D, F>> buildUniverse (Graph<Entry<D, F>> graph, Entry<D, F>[] result, Entry<D, F> v) {

			Deque<Frame<Entry<D,F>>> deque = new ArrayDeque<Frame<Entry<D,F>>>(result.length);
			
			v.out = graph.get();

			int rpo = result.length;

			for (Frame<Entry<D, F>> frame = Frame.newFrame(v);;frame = deque.removeFirst()) {
				v = frame.v;

				while (frame.i < v.out.length) {
					Entry<D, F> w = v.out[frame.i];

					// an unvisited child node
					if (w.getNumber() < 0) {
						v = w;
						v.out = graph.get(v);
						v.setNumber(deque.size());
						
						deque.addFirst(frame);
						frame = Frame.newFrame(v);
						continue;
					}

					if (w.getNumber() < v.getNumber()) {
						v.setNumber(w.getNumber());
						frame.isRoot = false;
					}

					frame.i++;
					w.addIn(v);
				}

				if (deque.isEmpty())
					break;

				if (frame.isRoot) {
					// number of finished frames
					int len = deque.size() - v.getNumber();
					rpo -= len;

					// first "frame"
					result[rpo + 0] = v;
					v.setNumber(rpo + 0);
					v.nextSCC = len - 0;

					// now process all tail frames
					for (int j = 1; j < len; j++) {
						v = deque.removeLast().v;
						
						result[rpo + j] = v;
						v.setNumber(rpo + j);
						v.nextSCC = len - j;
					}
				} else {
					// not a root, move frame from head to tail
					deque.addLast(frame);
				}
			}

			return ImmutableArrays.asSubList(result, rpo);
		}
	}

	
	private class DefaultMap extends ForwardingMap<N,A> {
		Map<N, A> inner;

		DefaultMap(Map<N, A> m) {
			inner = m;
		}

		@Override
		public A get(Object key) {
			A val = delegate().get(key);
			if (null == val)
				return newInitialFlow();
			return val;
		}

		@Override
		protected Map<N, A> delegate() {
			return inner;
		}
	};

	/** Maps graph nodes to OUT sets. */
	protected Map<N, A> unitToAfterFlow;

	/** Filtered: Maps graph nodes to OUT sets. */
	protected Map<N, A> filterUnitToAfterFlow = Collections.emptyMap();

	/** Constructs a flow analysis on the given <code>DirectedGraph</code>. */
	public FlowAnalysis(DirectedGraph<N> graph) {
		super(graph);

		unitToAfterFlow = new IdentityHashMap<N,A>((graph.size() * 2) + 1);

		// we are creating the mapping AFTER the flowThrough calculation,
		// unfortunately the unitTo{Before|After}Flows are "protected",
		// so this hack is required for backward-compatibility
		unitToBeforeFlow = new DefaultMap(unitToBeforeFlow);
		unitToAfterFlow = new DefaultMap(unitToAfterFlow);
	}

	/**
	 * Given the merge of the <code>out</code> sets, compute the <code>in</code>
	 * set for <code>s</code> (or in to out, depending on direction).
	 *
	 * This function often causes confusion, because the same interface is used
	 * for both forward and backward flow analyses. The first parameter is
	 * always the argument to the flow function (i.e. it is the "in" set in a
	 * forward analysis and the "out" set in a backward analysis), and the third
	 * parameter is always the result of the flow function (i.e. it is the "out"
	 * set in a forward analysis and the "in" set in a backward analysis).
	 *
	 * @param in
	 *            the input flow
	 * @param d
	 *            the current node
	 * @param out
	 *            the returned flow
	 **/
	protected abstract void flowThrough(A in, N d, A out);
	
	/**
	 * You can use this method instead of {@link #flowThrough(A, N, A)} if flow
	 * {@code A} can be used like an immutable object.
	 * 
	 * @param in the input flow
	 * @param d the current node
	 * @return  the returned flow
	 **/
	protected A flowThrough(A in, N d) {
		A out = newInitialFlow();
		flowThrough(in, d, out);
		return out;
	}

	/** Accessor function returning value of OUT set for s. */
	public A getFlowAfter(N s) {
		return unitToAfterFlow.get(s);
	}

	/**
	 * Processes a bunch of entries
	 * @param list
	 */
	private void processResult(Collection<Entry<N, A>> list) {
		for (Entry<N, A> c : list) {
			onComplete(c.inFlow, c.data, c.outFlow);
		}
	}

	/**
	 * A callback handler for result processing.
	 *
	 * This handler will be called when the analysis of a {@code node} has been completed.
	 *
	 * @param inFlow the in-flow of a node
	 * @param node the finished node
	 * @param outFlow the out-flow of a node
	 */
	abstract protected void onComplete(A inFlow, N node, A outFlow);

	/**
	 * You can specify which flow set you would like to use of node {@code from}
	 *
	 * @param source the source node, is {@code null} for entry node
	 * @param destination the destination node
	 * @return the outFlow of the source node
	 */
	protected Flow getFlow(N source, N destination) {
		return Flow.OUT;
	}

	private A getFlow(Entry<N, A> src, Entry<N, A> dst) {
		return (src.isIdentity() ? Flow.OUT : getFlow(src.data, dst.data)).getFlow(src);
	}

	private void meetFlows(Entry<N, A> e) {
		A prev = null;
		A in = null;
		for (Entry<N, A> i : e.in) {
			A flow = getFlow(i, e);
			if (null == flow)
				continue;

			if (flow == prev)
				continue;

			if (null == prev) {
				// copy reference on first match
				in = flow;
			} else {
				// second match, create new merge-point
				if (prev == in)
					copy(prev, in = newInitialFlow());

				mergeInto(e.data, in, flow);
			}
			prev = flow;
		}

		assert (null != in) : "node <"+e+"> has no in-flow";

		e.inFlow = in;
	}
	
	private Entry<N, A>[] getOut(Entry<N, A> e, InteractionFlowHandler ifh) {
		boolean isIdentity = e.isIdentity();
		
		meetFlows(e);
		
		ifh.handleFlowIn(this, e.data, e.inFlow);

		Entry<N, A>[] r = Entry.emptyEntries();
		A test = isIdentity ? e.inFlow : flowThrough(e.inFlow, e.data);
		// on first flowThrough the previous outFlow is null, this allows fail-fast equals
		// test can throw a NullPointerException implicitly!
		if (!test.equals(e.outFlow)) {
			e.outFlow = test;
			r = e.out;
		}
		
		ifh.handleFlowOut(this, e.data, e.outFlow);
		
		return r;
	}
	
	final int doAnalysis(Orderer o, InteractionFlowHandler ifh) {
		ifh = Options.v().interactive_mode() ? ifh : InteractionFlowHandler.NONE;

		final List<Entry<N, A>> universe = o.newUniverse(graph, entryInitialFlow());
		
		PriorityQueue<Entry<N, A>> base = PriorityQueue.noneOf(universe, true);
		Queue<Entry<N, A>> work = base;
		Queue<Entry<N, A>> back = PriorityQueue.noneOf(base);
		
		int numComputations = 0;

		for (int from = 0; from < universe.size(); ) {
			int to = from + universe.get(from).nextSCC;
			
			// first flow, only back-edges are interesting
			for (Entry<N, A> e : universe.subList(from, to)) {
				for (Entry<N, A> out : getOut(e, ifh)) {
					if (out.compareTo(e) <= 0) {
						back.add(out);
					}
				}
			}
			
			while (!back.isEmpty()) {
				// swap worklists
				Queue<Entry<N, A>> t = work;
				work = back;
				back = t;
				
				do {
					Entry<N, A> e = work.poll();
					for (Entry<N, A> out : getOut(e, ifh)) {
						if (out.compareTo(e) <= 0) {
							back.add(out);
						} else {
							if (out.getNumber() < to) {
								work.add(out);
							}
						}
					}
					numComputations++;
				}
				while (!work.isEmpty());
			}
	
			processResult(universe.subList(from, to));
			from = to;
		}
		
		return numComputations + universe.size();
	}
}
