import LeanLTL.Examples.Scenic.DroneDistance.FollowerControllerSemantics.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerControllerSemantics

set_option maxHeartbeats 1000000

theorem imp_assumptions : LLTL[fprops] ⇒ LLTL[assumptions → guarantees] := by
  intro t hF
  simp only [TraceSet.sat_imp_iff]
  intro _
  simp only [fprops, F0, F1, F2, guarantees, G0, G1, G2,
    TraceSet.sat_and_iff] at *
  obtain ⟨hF0, hF1, hF2⟩ := hF
  simp [push_ltl, CF_N0, CF_N1, CF_N2, CF, ComponentFunc] at hF0 hF1 hF2 ⊢
  constructor
  · intro n hn hlo hhi
    have h0 := hF0 n hn
    have h1 := hF1 n hn
    have h2 := hF2 n hn
    have hnotfar : ¬15.0 * 15.0 < (t.toFun! n).N3 := not_lt_of_ge hhi
    have hnotnear : ¬(t.toFun! n).N3 < 5.0 * 5.0 := not_lt_of_ge hlo
    simp only [if_neg hnotfar, if_neg hnotnear] at h0 h1 h2
    norm_num at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  constructor
  · intro n hn hnear
    have h0 := hF0 n hn
    have h1 := hF1 n hn
    have h2 := hF2 n hn
    have hnotfar : ¬15.0 * 15.0 < (t.toFun! n).N3 := by
      norm_num at hnear ⊢
      linarith
    simp only [if_neg hnotfar, if_pos hnear] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · intro n hn hfar
    have h0 := hF0 n hn
    have h1 := hF1 n hn
    have h2 := hF2 n hn
    simp only [if_pos hfar] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
