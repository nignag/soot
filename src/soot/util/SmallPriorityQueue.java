/**
 *
 */
package soot.util;

import static java.lang.Long.numberOfTrailingZeros;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 * @author Steven Lambeth
 *
 */
class SmallPriorityQueue<E> extends PriorityQueue<E> {
	final static int MAX_CAPACITY = Long.SIZE;

	private long queue = 0;

	@Override 
	void addAll() {
		if (N == 0)
			return;

		queue = -1L >>> -N;
		min = 0;
	}

	SmallPriorityQueue(List<? extends E> universe, Map<E, Numberable> ordinalMap) {
		super(universe, ordinalMap);
		assert universe.size() <= MAX_CAPACITY;
	}

	@Override
	public void clear() {
		queue = 0L;
		min = Integer.MAX_VALUE;
	}

	@Override
	public Iterator<E> iterator() {
		return new Itr() {
			@Override
			long getExpected() {
				return queue;
			}
		};
	}

	@Override
	public int size() {
		return Long.bitCount(queue);
	}

	@Override
	public boolean isEmpty() {
		return queue == 0;
	}

	@Override
	int nextSetBit(int fromIndex) {
		assert fromIndex >= 0;

		if (fromIndex > N)
			return fromIndex;

		long m0 = -1L << fromIndex;
		long t0 = queue & m0;
		if ((t0 & -m0) != 0)
			return fromIndex;

		return numberOfTrailingZeros(t0);
	}

	@Override
	boolean add(int ordinal) {
		long old = queue;
		long mask = (1L << ordinal);
		if (0 != (mask & old))
			return false;

		queue = old | mask;
		min = Math.min(min, ordinal);
		return true;
	}

	@Override
	boolean contains(int ordinal) {
		assert ordinal >= 0;
		assert ordinal < N;

		return ((queue >>> ordinal) & 1L) == 1L;
	}

	@Override
	boolean remove(int index) {
		assert index >= 0;
		assert index < N;

		long mask = (1L << index);

		if (0 == (queue & mask))
			return false;

		queue -= mask;
		if (min == index)
			min++;

		return true;
	}

	private long getMask(Iterable<?> c) {
		long mask = 0;
		for (Object o : c) {
			mask |= (1L << getOrdinal(o));
		}
		return mask;
	}

	@Override
	public boolean removeAll(Collection<?> c) {
		long old = queue;
		queue &= ~getMask(c);
		return old != queue;
	}

	@Override
	public boolean retainAll(Collection<?> c) {
		long old = queue;
		queue &= getMask(c);
		return old != queue;
	}

	@Override
	public boolean containsAll(Collection<?> c) {
		return (getMask(c) & ~queue) == 0;
	}

	@Override
	public boolean addAll(Collection<? extends E> c) {
		if (c.isEmpty())
			return false;
		if (c instanceof SmallPriorityQueue) {
			SmallPriorityQueue<?> q = (SmallPriorityQueue<?>) c;
			if (q.universe == universe) {
				if ((queue & ~q.queue) == 0)
					return false;
				queue |= q.queue;
				min = Math.min(min, q.min);
				return true;
			}
		}
		long old = queue;
		queue |= getMask(c);
		if (old == queue)
			return false;
		min = 0;
		return true;
	}

}
