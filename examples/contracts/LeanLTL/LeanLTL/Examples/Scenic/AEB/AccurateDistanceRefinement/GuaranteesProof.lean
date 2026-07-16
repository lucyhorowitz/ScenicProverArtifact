import LeanLTL.Examples.Scenic.AEB.AccurateDistanceRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace AccurateDistanceRefinement


theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  simp [TraceSet.sem_imp, i_guarantees, guarantees]
  intro t h
  simp [push_ltl] at *
  intro n h_n x h_x1 h_x2
  simp_all

  by_cases h_case1: (t.toFun! 0).N3 = 0 ∨ (t.toFun! 0).N3 = 1 <;>
  by_cases h_case2: 1.8 ≤ (t.toFun! 0).N2 <;> simp_all
  . rcases h with ⟨h,_⟩
    specialize h n h_n x
    simp_all
  all_goals
    specialize h n h_n x
    simp_all
