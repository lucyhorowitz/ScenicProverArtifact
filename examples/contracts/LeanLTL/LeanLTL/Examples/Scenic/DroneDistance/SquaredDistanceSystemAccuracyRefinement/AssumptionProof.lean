import LeanLTL.Examples.Scenic.DroneDistance.SquaredDistanceSystemAccuracyRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace SquaredDistanceSystemAccuracyRefinement


theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  intro t h
  exact h
