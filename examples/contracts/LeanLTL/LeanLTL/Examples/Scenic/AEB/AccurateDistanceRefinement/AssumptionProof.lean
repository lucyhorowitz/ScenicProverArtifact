import LeanLTL.Examples.Scenic.AEB.AccurateDistanceRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace AccurateDistanceRefinement


theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  simp [push_ltl]
