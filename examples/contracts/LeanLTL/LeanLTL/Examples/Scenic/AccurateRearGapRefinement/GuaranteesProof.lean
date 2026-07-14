import LeanLTL.Examples.Scenic.AccurateRearGapRefinement.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace AccurateRearGapRefinement

theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t h
  rw [sat_and_iff] at h
  obtain ⟨-, hIG⟩ := h
  simp only [i_guarantees, sat_and_iff] at hIG
  obtain ⟨hIG0, hIG1⟩ := hIG
  simp only [IG0, IG1] at *
  simp only [guarantees, G0, G1]
  simp [push_ltl] at hIG0 hIG1 ⊢
  by_cases hc1 : (t.toFun! 0).N0 = 0 <;> by_cases hc2 : (t.toFun! 0).N1 ≤ 1 <;>
    simp_all
