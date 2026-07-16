import LeanLTL.Examples.Scenic.HighwayMerge.AccurateRearGapRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace AccurateRearGapRefinement

theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  simp [push_ltl]
