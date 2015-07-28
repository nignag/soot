package soot.util;

import java.util.BitSet;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

// QND
class LargePriorityQueue<E> extends PriorityQueue<E> {

	BitSet queue;
	private long modCount = 0;

	LargePriorityQueue(List<? extends E> universe, Map<E, Numberable> ordinalMap) {
		super(universe, ordinalMap);
		queue = new BitSet(N);
	}

	@Override
	public void clear() {
		queue.clear();
		min = Integer.MAX_VALUE;
		modCount++;
	}

	@Override
	boolean add(int ordinal) {
		if (contains(ordinal))
			return false;
		queue.set(ordinal);
		min = Math.min(min, ordinal);
		modCount++;
		return true;
	}

	@Override
	void addAll() {
		queue.set(0, N);
		min = 0;
		modCount++;
	}

	@Override
	int nextSetBit(int fromIndex) {
		int i = queue.nextSetBit(fromIndex);
		return (i < 0) ? Integer.MAX_VALUE : i;
	}

	@Override
	boolean remove(int ordinal) {
		if (!contains(ordinal))
			return false;
		queue.clear(ordinal);

		if (min == ordinal)
			min++;

		modCount++;
		return true;
	}


	@Override
	int removeMin() {
		assert !isEmpty();
		int i = queue.nextSetBit(min);
		queue.clear(i);
		min = i + 1;
		modCount++;
		return i;
	}


	@Override
	boolean contains(int ordinal) {
		return (ordinal >= min) && queue.get(ordinal);
	}

	@Override
	public Iterator<E> iterator() {
		return new Itr() {
			@Override
			long getExpected() {
				return modCount;
			}
		};
	}

	@Override
	public int size() {
		return queue.cardinality();
	}

	@Override
	public boolean isEmpty() {
		return queue.isEmpty();
	}

	@Override
	public boolean addAll(Collection<? extends E> c) {
		if (c.isEmpty())
			return false;
		if (c instanceof LargePriorityQueue) {
			LargePriorityQueue<?> q = (LargePriorityQueue<?>) c;
			if (q.universe == universe) {
				min = queue.nextSetBit(min);
				q.min = queue.nextSetBit(q.min);
				if ((q.min < min) || (queue.length() < q.queue.length())) {
					min = q.min;
					queue.or(q.queue);
				} else {
					BitSet old = (BitSet) queue.clone();
					queue.or(q.queue);
					if (old.equals(queue))
						return false;
				}

				modCount++;
				return true;
			}
		}
		return super.addAll(c);
	}
}
