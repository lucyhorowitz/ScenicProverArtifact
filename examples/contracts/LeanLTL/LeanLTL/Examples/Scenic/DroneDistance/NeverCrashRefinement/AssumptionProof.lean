import LeanLTL.Examples.Scenic.DroneDistance.NeverCrashRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace NeverCrashRefinement


/- Every internal assumption (IA0..IA4) is a closed rational fact — copies of the
   parameter-sanity assumptions A0..A4 — so no trace reasoning is needed. -/
theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  intro t _
  simp only [i_assumptions, IA0, IA1, IA2, IA3, IA4, TraceSet.sat_and_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [push_ltl] <;> norm_num
