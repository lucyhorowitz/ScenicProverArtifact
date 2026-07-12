import LeanLTL.Examples.Scenic.GapFusionSemantics.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace GapFusionSemantics

theorem imp_assumptions : LLTL[fprops] ⇒ LLTL[assumptions → guarantees] := by
  simp [push_ltl, CF_N5, CF_N4, CF, ComponentFunc]
