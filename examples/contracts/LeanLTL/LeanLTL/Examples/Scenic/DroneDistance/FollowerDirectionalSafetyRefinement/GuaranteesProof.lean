import LeanLTL.Examples.Scenic.DroneDistance.FollowerDirectionalSafetyRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerDirectionalSafetyRefinement

private lemma key1 : ∀ x : ℚ, 0 ≤ x * ((0.2 * x ⊔ -3.0) ⊓ 3.0) := by
  intro x
  rcases le_total (0.2 * x) (-3.0 : ℚ) with h | h
  · rw [sup_eq_right.mpr h, inf_eq_left.mpr (by norm_num)]
    nlinarith
  · rw [sup_eq_left.mpr h]
    rcases le_total (0.2 * x) (3.0 : ℚ) with h' | h'
    · rw [inf_eq_left.mpr h', ← mul_assoc, ← mul_comm, ← mul_assoc]; refine
      Rat.mul_nonneg ?_ ?_; nlinarith; linarith
    · rw [inf_eq_right.mpr h']; nlinarith

private lemma key2 : ∀ x : ℚ, x * ((-(0.2 * x) ⊔ -3.0) ⊓ 3.0) ≤ 0 := by
  intro x
  rcases le_total (-(0.2 * x)) (-3.0 : ℚ) with h | h
  · rw [sup_eq_right.mpr h, inf_eq_left.mpr (by norm_num)]
    nlinarith
  · rw [sup_eq_left.mpr h]
    rcases le_total (-(0.2 * x)) (3.0 : ℚ) with h' | h'
    · rw [inf_eq_left.mpr h', mul_neg, ← mul_assoc, ← mul_comm, ← mul_assoc, Right.neg_nonpos_iff]
      nlinarith
    · rw [inf_eq_right.mpr h']; nlinarith

private lemma clamp_range (a : ℚ) : -3.0 ≤ (a ⊔ -3.0) ⊓ 3.0 ∧ (a ⊔ -3.0) ⊓ 3.0 ≤ 3.0 :=
  ⟨le_inf le_sup_right (by norm_num), inf_le_right⟩

theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t ⟨_, ⟨hIG0, hIG1, hIG2⟩⟩
  simp [push_ltl] at hIG0 hIG1 hIG2 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- G0: too far → cmd_dot_prod ≥ 0
    intro n hn hfar
    obtain ⟨hcx, hcy, hcz⟩ := hIG2 n hn hfar
    rw [hcx, hcy, hcz]
    linarith [key1 (t.toFun! n).N4, key1 (t.toFun! n).N5, key1 (t.toFun! n).N6]
  · -- G1: too close → cmd_dot_prod ≤ 0
    intro n hn hnear
    obtain ⟨hcx, hcy, hcz⟩ := hIG1 n hn hnear
    rw [hcx, hcy, hcz]
    linarith [key2 (t.toFun! n).N4, key2 (t.toFun! n).N5, key2 (t.toFun! n).N6]
  · -- G2: in band → cmd = 0
    intro n hn hdist_above hdist_below
    aesop
  all_goals
    intro n hn
    rcases lt_or_le ((t.toFun! n).N3) (5.0 * 5.0 : ℚ) with hnear | hlo
    · obtain ⟨hcx, hcy, hcz⟩ := hIG1 n hn hnear
      first | rw [hcx] | rw [hcy] | rw [hcz]
      exact clamp_range _
    · rcases le_or_lt ((t.toFun! n).N3) (15.0 * 15.0 : ℚ) with hhi | hfar
      · obtain ⟨hcx, hcy, hcz⟩ := hIG0 n hn hlo hhi
        first | rw [hcx] | rw [hcy] | rw [hcz]
        norm_num
      · obtain ⟨hcx, hcy, hcz⟩ := hIG2 n hn hfar
        first | rw [hcx] | rw [hcy] | rw [hcz]
        exact clamp_range _
