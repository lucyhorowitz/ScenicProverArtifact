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
  obtain ⟨hIG0, hIG1, hIG2, hIG3⟩ := hIG
  simp only [IG0, IG1, IG2, IG3] at *
  simp only [guarantees, G0, G1, sat_and_iff]
  simp [push_ltl] at hIG0 hIG1 hIG2 hIG3 ⊢
  by_cases hc : ((t.toFun! 0).N0 = 0 ∧ (t.toFun! 0).N1 ≤ 1) <;> simp_all
