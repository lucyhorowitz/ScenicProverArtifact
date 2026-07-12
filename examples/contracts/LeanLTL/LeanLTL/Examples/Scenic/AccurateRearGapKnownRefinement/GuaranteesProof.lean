import LeanLTL.Examples.Scenic.AccurateRearGapKnownRefinement.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace AccurateRearGapKnownRefinement

theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t h
  rw [sat_and_iff] at h
  obtain ⟨-, hIG⟩ := h
  simp only [i_guarantees, sat_and_iff] at hIG
  obtain ⟨hIG0, hIG1, hIG2, hIG3, hIG4, hIG5⟩ := hIG
  simp only [IG0, IG1, IG2, IG3, IG4, IG5] at *
  simp only [guarantees, G0, G1, sat_and_iff]
  constructor
  · -- fused rear gap stays within the accuracy band (min of two in-band values)
    simp [push_ltl] at hIG0 hIG2 hIG4 ⊢
    intro n h_n
    have h0 := hIG0 n h_n
    have h2 := hIG2 n h_n
    have h4 := hIG4 n h_n
    rw [h4]
    constructor
    · exact le_inf h0.1 h2.1
    · exact le_trans inf_le_left h0.2
  · -- fused rear closing speed stays within the accuracy band (max of two in-band values)
    simp [push_ltl] at hIG1 hIG3 hIG5 ⊢
    intro n h_n
    have h1 := hIG1 n h_n
    have h3 := hIG3 n h_n
    have h5 := hIG5 n h_n
    rw [h5]
    constructor
    · exact le_trans h1.1 le_sup_left
    · exact sup_le h1.2 h3.2
