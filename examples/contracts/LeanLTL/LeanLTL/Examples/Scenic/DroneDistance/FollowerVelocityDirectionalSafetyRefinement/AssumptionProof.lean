import LeanLTL.Examples.Scenic.DroneDistance.FollowerVelocityDirectionalSafetyRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerVelocityDirectionalSafetyRefinement

/- Internal assumptions are copies of the top-level ones (all closed rational
   facts), so no trace reasoning is needed. -/
theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  intro t _
  simp only [i_assumptions, IA0, IA1, IA2, TraceSet.sat_and_iff]
  refine ⟨?_, ?_, ?_⟩ <;> simp [push_ltl] <;> norm_num
