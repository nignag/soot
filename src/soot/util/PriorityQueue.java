/**
 *
 */
package soot.util;

import java.util.AbstractMap;
import java.util.AbstractQueue;
import java.util.Arrays;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * A fixed size priority queue based on bitsets. The elements of the priority
 * queue are ordered according to a given universe. This priority queue does not
 * permit {@code null} elements. Inserting of elements that are not part of the
 * universe is also permitted (doing so will result in a
 * {@code NoSuchElementException}).
 *
 * @author Steven Lambeth
 * @param <E> the type of elements held in the universe
 */
abstract public class PriorityQueue<E> extends AbstractQueue<E> {
	abstract class Itr implements Iterator<E> {
		long expected = getExpected();
		int next = min;
		int now = Integer.MAX_VALUE;

		abstract long getExpected();

		@Override
		public boolean hasNext() {
			return next < N;
		}

		@Override
		public E next() {
			if (expected != getExpected())
				throw new ConcurrentModificationException();
			if (next >= N)
				throw new NoSuchElementException();

			now = next;
			next = nextSetBit(next + 1);
			return universe.get(now);
		}

		@Override
		public void remove() {
			if (now >= N)
				throw new IllegalStateException();
			if (expected != getExpected())
				throw new ConcurrentModificationException();

			PriorityQueue.this.remove(now);
			expected = getExpected();
			now = Integer.MAX_VALUE;
		}
	}

	final private static class Box implements Numberable {
		int number;

		Box(int n) {
			setNumber(n);
		}

		@Override
		public void setNumber(int n) {
			number = n;
		}

		@Override
		public int getNumber() {
			return number;
		}
	}

	final List<? extends E> universe;
	final int N;
	int min = Integer.MAX_VALUE;
	final private Map<E, Numberable> ordinalMap;

	int getOrdinal(Object o) {
		Numberable n = ordinalMap.get(o);
		if (o == null)
			throw new NullPointerException();

		if (n == null)
			throw new NoSuchElementException();

		return n.getNumber();
	}

	/**
	 * Adds all elements of the universe to this queue.
	 */
	abstract void addAll();

	/**
	 * Returns the index of the first bit that is set to <code>true</code> that
	 * occurs on or after the specified starting index. If no such bit exists
	 * then a value greater or equal than {@code N} is returned.
	 *
	 * @param fromIndex
	 *            the index to start checking from (inclusive).
	 * @return the index of the next set bit.
	 */
	abstract int nextSetBit(int fromIndex);

	abstract boolean remove(int ordinal);

	abstract boolean add(int ordinal);

	abstract boolean contains(int ordinal);

	/**
	 * {@inheritDoc}
	 *
	 */
	@Override
	final public E peek() {
		if (isEmpty())
			return null;
		min = nextSetBit(min);
		return universe.get(min);
	}

	/**
	 * {@inheritDoc}
	 *
	 */
	@Override
	final public E poll() {
		if (isEmpty())
			return null;
		return universe.get(removeMin());
	}

	int removeMin() {
		assert !isEmpty();
		int i = min = nextSetBit(min);
		remove(i);
		return i;
	}

	/**
	 * {@inheritDoc}
	 *
	 * @throws NoSuchElementException
	 *             if e not part of the universe
	 * @throws NullPointerException
	 *             if e is {@code null}
	 */
	@Override
	final public boolean add(E e) {
		return offer(e);
	}

	/**
	 * {@inheritDoc}
	 *
	 * @throws NoSuchElementException
	 *             if e not part of the universe
	 * @throws NullPointerException
	 *             if e is {@code null}
	 */
	@Override
	final public boolean offer(E e) {
		return add(getOrdinal(e));
	}

	/**
	 * {@inheritDoc}
	 *
	 */
	@Override
	final public boolean remove(Object o) {
		if ((o == null) || isEmpty())
			return false;
		try {
			return remove(getOrdinal(o));
		} catch (NoSuchElementException e) {
		}
		return false;
	}

	/**
	 * {@inheritDoc}
	 *
	 */
	@Override
	final public boolean contains(Object o) {
		if ((o == null) || isEmpty())
			return false;
		try {
			return contains(getOrdinal(o));
		} catch (NoSuchElementException e) {
		}
		return false;
	}

	/**
	 * {@inheritDoc}
	 *
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append('{');
		boolean isFirst = true;
		for (E e : this) {
			if (!isFirst) {
				sb.append(',');
			}
			sb.append(e);
			isFirst = false;
		}
		sb.append('}');
		return sb.toString();
	}

	PriorityQueue(List<? extends E> universe, Map<E, Numberable> ordinalMap) {
		this.universe = universe;
		this.ordinalMap = ordinalMap;
		this.N = universe.size();
	}

	/**
	 * Creates a new full priority queue
	 *
	 * @param universe
	 * @return
	 */
	public static <E> PriorityQueue<E> of(E[] universe) {
		return of(Arrays.asList(universe));
	}

	/**
	 * Creates a new empty priority queue
	 *
	 * @param universe
	 * @return
	 */
	public static <E> PriorityQueue<E> noneOf(E[] universe) {
		return noneOf(Arrays.asList(universe));
	}

	/**
	 * Creates a new full priority queue
	 *
	 * @param universe
	 * @return
	 */
	public static <E> PriorityQueue<E> of(List<? extends E> universe) {
		PriorityQueue<E> q = noneOf(universe);
		q.addAll();
		return q;
	}

	public static <E> PriorityQueue<E> of(PriorityQueue<E> s) {
		PriorityQueue<E> q = noneOf(s);
		q.addAll();
		return q;
	}

	public static <E> PriorityQueue<E> noneOf(PriorityQueue<E> s) {
		return newPriorityQueue(s.universe, s.ordinalMap);
	}

	/**
	 * Creates a new empty priority queue
	 *
	 * @param universe
	 * @return
	 */
	public static <E> PriorityQueue<E> noneOf(List<? extends E> universe) {
		Map<E, Numberable> ordinalMap = new IdentityHashMap<E, Numberable>((3 * universe.size()) / 2);

		int i = 0;
		for (E e : universe) {
			if (e == null)
				throw new NullPointerException("null is not allowed");
			if (ordinalMap.put(e, new Box(i++)) != null)
				throw new IllegalArgumentException("duplicate key found");
		}

		return newPriorityQueue(universe, ordinalMap);
	}

	public static <E extends Numberable> PriorityQueue<E> of(List<? extends E> universe, boolean useNumberInterface) {
		PriorityQueue<E> q = noneOf(universe, useNumberInterface);
		q.addAll();
		return q;
	}

	public static <E extends Numberable> PriorityQueue<E> noneOf(final List<? extends E> universe, boolean useNumberInterface) {
		if (useNumberInterface) {
			int i = 0;
			for (E e : universe) {
				e.setNumber(i++);
			}

			return newPriorityQueue(universe, new AbstractMap<E, Numberable>() {
				@Override
				public Numberable get(Object key) {
					if (key instanceof Numberable) {
						Numberable n = (Numberable) key;
						if (universe.get(n.getNumber()) == key)
							return n;
					}
					return null;
				}

				@Override
				public Set<java.util.Map.Entry<E, Numberable>> entrySet() {
					return Collections.emptySet();
				}
			});
		}
		return noneOf(universe);
	}


	private static <E> PriorityQueue<E> newPriorityQueue(List<? extends E> universe, Map<E, Numberable> ordinalMap) {
		if (universe.size() <= SmallPriorityQueue.MAX_CAPACITY)
			return new SmallPriorityQueue<E>(universe, ordinalMap);
		if (universe.size() <= MediumPriorityQueue.MAX_CAPACITY)
			return new MediumPriorityQueue<E>(universe, ordinalMap);
		return new LargePriorityQueue<E>(universe, ordinalMap);
	}

}
