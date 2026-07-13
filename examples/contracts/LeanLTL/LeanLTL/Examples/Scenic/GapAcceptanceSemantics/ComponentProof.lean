import LeanLTL.Examples.Scenic.GapAcceptanceSemantics.Lib

open LeanLTL
open scoped LeanLTL.Notation
open TraceSet

namespace GapAcceptanceSemantics

theorem imp_assumptions : LLTL[fprops] ⇒ LLTL[assumptions → guarantees] := by
  intro t hF
  simp only [sat_imp_iff]
  intro _
  simp only [fprops, F0, guarantees, G0, G1, sat_and_iff] at *
  simp [push_ltl, CF_N1, CF, ComponentFunc, required_rear] at hF ⊢
  constructor
  · intro n hn h1 h2
    have h := hF n hn
    split_ifs at h with hc
    · exact h
    · exact absurd ⟨h1, h2⟩ hc
  · -- push_ltl normalizes the negated conjunction into a disjunction of ≤ bounds
    intro n hn h1
    have h := hF n hn
    split_ifs at h with hc
    · rcases h1 with h1 | h1 <;> linarith [hc.1, hc.2]
    · exact h
