import LeanLTL.Examples.Scenic.DroneDistance.KeepsFollowDistanceProgressRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace KeepsFollowDistanceProgressRefinement


theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  sorry
