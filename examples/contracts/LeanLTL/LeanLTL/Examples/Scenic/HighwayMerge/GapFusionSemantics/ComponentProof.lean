import LeanLTL.Examples.Scenic.HighwayMerge.GapFusionSemantics.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace GapFusionSemantics

theorem imp_assumptions : LLTL[fprops] ⇒ LLTL[assumptions → guarantees] := by
  intro t hF
  simp only [TraceSet.sat_imp_iff]
  intro _
  simp only [fprops, F0, F1, guarantees, G0, G1, TraceSet.sat_and_iff] at *
  obtain ⟨hF0, hF1⟩ := hF
  simp [push_ltl, CF_N5, CF_N4, CF, ComponentFunc] at hF0 hF1 ⊢
  exact ⟨hF0, hF1⟩
