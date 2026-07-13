import LeanLTL.Examples.Scenic.ReportedSquaredDistanceComputerSemantics.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace ReportedSquaredDistanceComputerSemantics

theorem imp_assumptions : LLTL[fprops] ⇒ LLTL[assumptions → guarantees] := by
  sorry
