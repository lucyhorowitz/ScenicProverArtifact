import LeanLTL.Examples.Scenic.DroneDistance.SquaredMagnitudeComputerSemantics.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace SquaredMagnitudeComputerSemantics

theorem imp_assumptions : LLTL[fprops] ⇒ LLTL[assumptions → guarantees] := by
  simp [push_ltl, CF_N0, CF, ComponentFunc]
