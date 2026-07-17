import LeanLTL.Examples.Scenic.DroneDistance.SquaredDistanceSystemAccuracyRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace SquaredDistanceSystemAccuracyRefinement


theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t ⟨_, h⟩
  exact h
