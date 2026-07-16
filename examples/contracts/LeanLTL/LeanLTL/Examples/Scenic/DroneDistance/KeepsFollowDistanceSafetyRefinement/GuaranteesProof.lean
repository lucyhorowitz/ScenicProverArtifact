import LeanLTL.Examples.Scenic.DroneDistance.KeepsFollowDistanceSafetyRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace KeepsFollowDistanceSafetyRefinement


theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  sorry
