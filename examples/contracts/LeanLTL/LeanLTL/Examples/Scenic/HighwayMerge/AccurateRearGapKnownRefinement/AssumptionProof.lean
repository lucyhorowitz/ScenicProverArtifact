import LeanLTL.Examples.Scenic.HighwayMerge.AccurateRearGapKnownRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace AccurateRearGapKnownRefinement

theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  simp_all [push_ltl]
