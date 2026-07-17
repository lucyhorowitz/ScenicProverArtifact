import LeanLTL.Examples.Scenic.DroneDistance.ReportedRelativePositionAccurateRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace ReportedRelativePositionAccurateRefinement


theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  intro t h
  exact h
