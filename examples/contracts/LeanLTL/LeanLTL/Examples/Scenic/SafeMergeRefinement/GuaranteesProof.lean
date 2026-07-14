import LeanLTL.Examples.Scenic.SafeMergeRefinement.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace SafeMergeRefinement

set_option maxHeartbeats 1000000

/-
Proof sketch (per step n, given a lateral-progress jump before the commit point):
1. The jump exceeds the actuation slack, so by IG9 (contrapositive) the merge command
   is not 0; by IG6 it is 1.
2. By IG7, either merge_ok ≥ 1 or the sensed progress ≥ 0.6; the latter is ruled out
   by IG3 (sensed progress = true progress) and the precommit hypothesis.
3. By IG5 (contrapositive), the gap-acceptance condition held: sensed front gap > 10
   and sensed rear gap > 8 + 2 * max(0, sensed rear closing) ≥ 8.
4. By the accuracy bands IG2/IG0, the true gaps exceed 10 - 0.5 and 8 - 0.5.
-/
theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t h
  rw [sat_and_iff] at h
  obtain ⟨-, hIG⟩ := h
  simp only [i_guarantees, sat_and_iff] at hIG
  obtain ⟨hIG0, hIG1, hIG2, hIG3, hIG4, hIG5, hIG6, hIG7, hIG8, hIG9⟩ := hIG
  simp only [IG0, IG1, IG2, IG3, IG4, IG5, IG6, IG7, IG8, IG9] at *
  simp only [guarantees, G0]
  simp [push_ltl] at hIG0 hIG1 hIG2 hIG3 hIG5 hIG6 hIG7 hIG9 ⊢
  -- After the simp above the goal is fully curried: length fact, the progress jump at
  -- index (1 + n), and the precommit bound arrive as separate hypotheses.
  intro n h_n h_len h_jump h_precommit
  -- Step 1: the merge command at step n must be 1.
  have h6 := hIG6 n h_n
  have hcmd : (t.toFun! n).N5 = 1.0 := by
    rcases h6 with h60 | h61
    · exfalso
      obtain ⟨y, ⟨-, rfl⟩, h_le⟩ := hIG9 n h_n h60
      linarith
    · exact h61
  -- Step 2: the gap must have been accepted (merge_ok ≥ 1).
  have h3 := hIG3 n h_n
  have h7 := hIG7 n h_n hcmd
  have hok : (1.0 : ℚ) ≤ (t.toFun! n).N3 := by
    rcases h7 with h | h
    · linarith
    · rw [h3] at h; linarith
  -- Step 3: recover the gap-acceptance condition from IG5's contrapositive.
  have h5 := hIG5 n h_n
  have hC := mt h5 (by intro hz; rw [hz] at hok; norm_num at hok)
  push_neg at hC
  obtain ⟨h_front, h_rear⟩ := hC
  -- Step 4: transfer the sensed gaps to the true gaps via the accuracy bands.
  have h0 := hIG0 n h_n
  have h2 := hIG2 n h_n
  have hsup : (0.0 : ℚ) ≤ (0.0 : ℚ) ⊔ (t.toFun! n).N1 := le_sup_left
  constructor
  · linarith [h2.2]
  · linarith [h0.2, hsup]
