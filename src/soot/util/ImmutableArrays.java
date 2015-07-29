package soot.util;

import static java.util.Arrays.copyOfRange;

import java.util.AbstractList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.RandomAccess;

public final class ImmutableArrays {
	private ImmutableArrays() {
	}

	/**
	 * Check that fromIndex and toIndex are in range, and throw an appropriate
	 * exception if they aren't.
	 */
	private static void rangeCheck(int arrayLen, int fromIndex, int toIndex) {
		if (fromIndex > toIndex)
			throw new IllegalArgumentException("fromIndex(" + fromIndex
					+ ") > toIndex(" + toIndex + ")");
		if (fromIndex < 0)
			throw new ArrayIndexOutOfBoundsException(fromIndex);
		if (toIndex > arrayLen)
			throw new ArrayIndexOutOfBoundsException(toIndex);
	}

	private final static class Lst<E> extends AbstractList<E>
			implements RandomAccess {
		final int base;
		final int size;
		final E[] data;

		private Lst(E[] a, int fromInclusive, int toExclusive) {
			assert 0 <= fromInclusive;
			assert fromInclusive <= toExclusive;
			assert toExclusive <= a.length;
			
			base = fromInclusive;
			data = a;
			size = toExclusive - fromInclusive;
		}

		@Override
		public Object[] toArray() {
			return copyOfRange(data, base, base + size, Object[].class);
		}

		@SuppressWarnings("unchecked")
		@Override
		public <T> T[] toArray(T[] a) {
			if (a.length < size)
				return copyOfRange(data, base, base + size, (Class<? extends T[]>) a.getClass());

			System.arraycopy(data, base, a, 0, size);
			if (a.length > size)
				a[size] = null;
			return a;
		}

		@Override
		public E get(int index) {
			if ((0 > index) || (index >= size))
				throw new IndexOutOfBoundsException("expected: 0 <= " + index+ " < " + size());
			return data[base + index];
		}

		@Override
		public List<E> subList(int fromIndex, int toIndex) {
			rangeCheck(size, fromIndex, toIndex);
			return newSubList(data, base + fromIndex, base + toIndex);
		}

		@Override
		public int size() {
			return size;
		}

		@Override
		public Iterator<E> iterator() {
			return new Iterator<E>() {
				int i = 0;

				@Override
				public boolean hasNext() {
					return i < size;
				}

				@Override
				public E next() {
					if (i >= size)
						throw new NoSuchElementException();
					return get(i++);
				}

				@Override
				public void remove() {
					throw new UnsupportedOperationException();
				}
			};
		}
	}

	/**
	 * Returns an unmodifiable view of the specified array. This method allows
	 * modules to provide users with "read-only" access to internal arrays.
	 * Query operations on the returned list "read through" to the specified
	 * array, and attempts to modify the returned array, whether direct or via
	 * its iterator, result in an <tt>UnsupportedOperationException</tt>.
	 * <p>
	 *
	 * The returned list is immutable and implements {@link RandomAccess}.
	 *
	 * <p>
	 * This method also provides a convenient way to create a fixed-size list
	 * initialized to contain several elements:
	 * 
	 * <pre>
	 * List&lt;String&gt; stooges = Arrays.asUnmodifiableList(&quot;Larry&quot;, &quot;Moe&quot;, &quot;Curly&quot;);
	 * </pre>
	 *
	 * @param a
	 *            the array by which the list will be mapped
	 * @return a list view of the specified array
	 */
	static final public <T> List<T> asList(T... a) {
		return newSubList(a, 0, a.length);
	}

	static final public <T> List<T> asSubList(T[] a, int fromIndex) {
		return asSubList(a, fromIndex, a.length);
	}

	static final public <T> List<T> asSubList(T[] a, int fromIndex, int toIndex) {
		rangeCheck(a.length, fromIndex, toIndex);
		return newSubList(a, fromIndex, toIndex);
	}
	
	static final private <T> List<T> newSubList(T[] a, int fromIndex, int toIndex) {
		if (fromIndex == toIndex)
			return Collections.emptyList();
		return new Lst<T>(a, fromIndex, toIndex);
	}
}
