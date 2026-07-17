import LeanLTL.Examples.Scenic.DroneDistance.FollowerVelocitySemanticsRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerVelocitySemanticsRefinement

set_option maxHeartbeats 500000

theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t h
  rw [TraceSet.sat_and_iff] at h
  obtain ⟨_, hIG⟩ := h
  simp only [i_guarantees, TraceSet.sat_and_iff] at hIG
  obtain ⟨hIG0, hIG1, hIG2, hIG3⟩ := hIG
  simp only [IG0, IG1, IG2, IG3] at *
  simp only [guarantees, G0, G1, G2, TraceSet.sat_and_iff]
  simp [push_ltl] at hIG0 hIG1 hIG2 hIG3 ⊢
  constructor
  · intro n hn hlo hhi
    have h0 := hIG0 n hn hlo hhi
    have h3 := hIG3 n hn
    simpa [h0.1, h0.2.1, h0.2.2] using h3
  constructor
  · intro n hn hnear
    have h1 := hIG1 n hn hnear
    have h3 := hIG3 n hn
    simpa [h1.1, h1.2.1, h1.2.2] using h3
  · intro n hn hfar
    have h2 := hIG2 n hn hfar
    have h3 := hIG3 n hn
    simpa [h2.1, h2.2.1, h2.2.2] using h3
