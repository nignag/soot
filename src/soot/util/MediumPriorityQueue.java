/**
 *
 */
package soot.util;

import static java.lang.Long.numberOfTrailingZeros;

import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 * @author Steven Lambeth
 *
 */
class MediumPriorityQueue<E> extends PriorityQueue<E> {
	final static int MAX_CAPACITY = Long.SIZE * Long.SIZE;

	private long modCount = 0;
	private long lookup = 0;
	private long[] data;

	@Override 
	void addAll() {
		Arrays.fill(data, -1);
		data[data.length - 1] = -1L >>> -N;
		lookup = -1L >>> -data.length;
		min = 0;
		modCount++;
	}

	MediumPriorityQueue(List<? extends E> universe, Map<E, Numberable> ordinalMap) {
		super(universe, ordinalMap);
		data = new long[((N + Long.SIZE) - 1) >>> 6];
		assert (1 <= N) && (N <= MAX_CAPACITY);
	}

	@Override
	public void clear() {
		if (isEmpty())
			return;
		Arrays.fill(data, 0);
		lookup = 0;
		min = Integer.MAX_VALUE;
		modCount++;
	}

	@Override
	boolean add(int ordinal) {
		int bucket = ordinal >>> 6;
		long mask = (1L << ordinal);
		long dat0 = data[bucket];

		if (0 != (dat0 & mask))
			return false;

		data[bucket] = dat0 | mask;
		lookup |= (1L << bucket);
		min = Math.min(min, ordinal);
		modCount++;
		return true;
	}

	@Override
	boolean contains(int ordinal) {
		assert ordinal >= 0;
		assert ordinal < N;
		return ((data[ordinal >>> 6] >>> ordinal) & 1L) == 1L;
	}


	@Override
	boolean remove(int index) {
		assert index >= 0;
		assert index < N;

		int bucket = (index >>> 6);

		long mask = (1L << index);
		long dat0 = data[bucket];

		if (0 == (dat0 & mask))
			return false;

		data[bucket] = dat0 - mask;

		if (mask == dat0) {
			lookup -= (1L << bucket);
			if ((min >>> 6) == bucket)
				min = (bucket+1) << 6;
		} else {
			if (min == index)
				min++;
		}

		modCount++;

		return true;
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
		int s = 0;
		long unseen = lookup;
		while (unseen != 0) {
			long lsb = unseen & -unseen;
			unseen -= lsb;
			long d = data[Long.numberOfTrailingZeros(lsb)];
			s += Long.bitCount(d);
		}
		return s;
	}

	@Override
	public boolean isEmpty() {
		return lookup == 0;
	}

	@Override
	public boolean addAll(Collection<? extends E> c) {
		if (c.isEmpty())
			return false;
		if (c instanceof MediumPriorityQueue) {
			MediumPriorityQueue<?> q = (MediumPriorityQueue<?>) c;
			if (q.universe == universe) {
				boolean hasChanged = false;

				long unseen = q.lookup;
				while (unseen != 0) {
					long lsb = unseen & -unseen;
					unseen -= lsb;
					int i = Long.numberOfTrailingZeros(lsb);

					long a = data[i];
					long b = q.data[i];
					hasChanged |= ((b & ~a) != 0);
					data[i] = a | b;
				}

				min = Math.min(min, q.min);
				lookup |= q.lookup;
				modCount += hasChanged ? 1 : 0;

				return hasChanged;
			}
		}
		return super.addAll(c);
	}

	@Override
	int nextSetBit(int fromIndex) {
		assert fromIndex >= 0;

		int bb = fromIndex >>> 6;

		while (fromIndex < N) {
			// remove everything from t1 that is less than "fromIndex",
			long m1 = -1L << fromIndex;
			// t1 contains now all active bits
			long t1 = data[bb] & m1;

			// the expected index m1 in t1 is set
			// (optional test if NOTZ is expensive)
			if ((t1 & -m1) != 0)
				return fromIndex;

			// some bits are left in t1, so we can finish
			if (t1 != 0)
				return (bb << 6) + numberOfTrailingZeros(t1);

			// we know the previous block is empty, so we start our lookup on
			// the next one
			long m0 = -1L << ++bb;
			long t0 = lookup & m0;

			// find next used block
			if ((t0 & -m0) == 0)
				bb = numberOfTrailingZeros(t0);

			// re-assign new search index
			fromIndex = bb << 6;

			// next and last round
		}
		return fromIndex;
	}
}
