/* Soot - a J*va Optimization Framework
 * Copyright (C) 2007 Manu Sridharan
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
package soot.jimple.spark.ondemand;

import soot.jimple.spark.internal.TypeManager;

public enum HeuristicType {
	MANUAL {
		@Override
		public FieldCheckHeuristic getHeuristic(TypeManager tm, int maxPasses) {
			return new ManualFieldCheckHeuristic();
		}
	},
	INCR {
		@Override
		public FieldCheckHeuristic getHeuristic(TypeManager tm, int maxPasses) {
			return new InnerTypesIncrementalHeuristic(tm, maxPasses);
		}
	},
	EVERY {
		@Override
		public FieldCheckHeuristic getHeuristic(TypeManager tm, int maxPasses) {
			return EverythingHeuristic.INSTANCE;
		}
	},
	MANUALINCR {
		@Override
		public FieldCheckHeuristic getHeuristic(TypeManager tm, int maxPasses) {
			return new ManualAndInnerHeuristic(tm, maxPasses);
		}
	},
	NOTHING {
		@Override
		public FieldCheckHeuristic getHeuristic(TypeManager tm, int maxPasses) {
			return NothingHeuristic.INSTANCE;
		}
	};

	abstract public FieldCheckHeuristic getHeuristic(TypeManager tm, int maxPasses);

	/**
	 *
	 * @deprecated just use getHeuristic of {@link HeuristicType}
	 * @param type
	 * @param tm
	 * @param maxPasses
	 * @return
	 */
	@Deprecated
	public static FieldCheckHeuristic getHeuristic(HeuristicType type, TypeManager tm, int maxPasses) {
		return type.getHeuristic(tm, maxPasses);
	}

}
