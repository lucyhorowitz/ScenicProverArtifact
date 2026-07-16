import LeanLTL.Examples.Scenic.HighwayMerge.SafeMergeRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace SafeMergeRefinement

theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  simp [push_ltl]
