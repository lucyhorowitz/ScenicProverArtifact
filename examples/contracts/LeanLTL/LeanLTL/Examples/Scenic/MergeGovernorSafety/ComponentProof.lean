import LeanLTL.Examples.Scenic.MergeGovernorSafety.Lib

open LeanLTL
open scoped LeanLTL.Notation
open TraceSet

namespace MergeGovernorSafety

theorem imp_assumptions : LLTL[fprops] ⇒ LLTL[assumptions → guarantees] := by
  intro t hF
  simp only [sat_imp_iff]
  intro _
  simp only [fprops, F0, F1, F2, sat_and_iff] at hF
  obtain ⟨-, hF1, -⟩ := hF
  simp only [guarantees, G0, G1, G2, sat_and_iff]
  simp [push_ltl, CF_N1, CF, ComponentFunc] at hF1
  refine ⟨?_, ?_, ?_⟩
  · -- merge_cmd is always 0 or 1
    simp [push_ltl]
    intro n hn
    have h := hF1 n hn
    split_ifs at h <;> norm_num [h]
  · -- a merge command implies the gap is accepted or we are past the commit point
    simp [push_ltl]
    intro n hn hcmd
    have h := hF1 n hn
    split_ifs at h with h1 h2 h3
    · right; linarith
    · left; linarith [h2.1]
    · rw [h] at hcmd; norm_num at hcmd
    · rw [h] at hcmd; norm_num at hcmd
  · -- no acceptance and not committed implies no merge command
    simp [push_ltl]
    intro n hn hok hprog
    have h := hF1 n hn
    split_ifs at h with h1 h2 h3
    · linarith
    · linarith [h2.1]
    · linarith
    · exact h
