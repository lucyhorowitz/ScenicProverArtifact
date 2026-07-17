import LeanLTL.Examples.Scenic.DroneDistance.FollowerVelocitySemanticsRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerVelocitySemanticsRefinement


theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  intro t h
  exact h
