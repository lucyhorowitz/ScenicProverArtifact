import LeanLTL.Examples.Scenic.DroneDistance.ReportedRelativePositionComputerSemantics.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace ReportedRelativePositionComputerSemantics

theorem imp_assumptions : LLTL[fprops] ⇒ LLTL[assumptions → guarantees] := by
  simp [push_ltl, CF_N3, CF_N4, CF_N5, CF, ComponentFunc]
