import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace KeepsFollowDistanceSafetyRefinement

structure TraceState where
  -- Props
  -- Numbers
  N0: ℚ
  N1: ℚ
  N2: ℚ
  N3: ℚ
  N4: ℚ
  N5: ℚ
  N6: ℚ
  N7: ℚ
  N8: ℚ
deriving Inhabited

-- Prop Signals

-- Numerical Signals
abbrev self.leadPos.x : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev self.leadPos.y : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev self.leadPos.z : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev self.position.x : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev self.position.y : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev self.position.z : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev self.velocity.x : TraceFun TraceState ℚ := TraceFun.of (·.N6)
abbrev self.velocity.y : TraceFun TraceState ℚ := TraceFun.of (·.N7)
abbrev self.velocity.z : TraceFun TraceState ℚ := TraceFun.of (·.N8)

-- Defs
abbrev max_dist_sq := LLTLV[(15.0) * (15.0)]
abbrev true_rel_x := LLTLV[((self.leadPos.x)) - ((self.position.x))]
abbrev true_rel_y := LLTLV[((self.leadPos.y)) - ((self.position.y))]
abbrev true_rel_z := LLTLV[((self.leadPos.z)) - ((self.position.z))]
abbrev true_dist_sq := LLTLV[((((true_rel_x)) * ((true_rel_x))) + (((true_rel_y)) * ((true_rel_y)))) + (((true_rel_z)) * ((true_rel_z)))]
abbrev disp_x := LLTLV[(𝐗 ((self.position.x))) - ((self.position.x))]
abbrev disp_y := LLTLV[(𝐗 ((self.position.y))) - ((self.position.y))]
abbrev disp_z := LLTLV[(𝐗 ((self.position.z))) - ((self.position.z))]
abbrev approach_dot := LLTLV[((((true_rel_x)) * ((disp_x))) + (((true_rel_y)) * ((disp_y)))) + (((true_rel_z)) * ((disp_z)))]
abbrev min_dist_sq := LLTLV[(5.0) * (5.0)]

-- Top Level Assumptions 
abbrev A0 := LLTL[(0) ≤ (5.0)]
abbrev A1 := LLTL[(5.0) ≤ (15.0)]
abbrev A2 := LLTL[𝐆 ((𝐗 ((←self.position.x))) = (((←self.position.x)) + ((0.1) * (𝐗 ((←self.velocity.x))))))]
abbrev A3 := LLTL[𝐆 ((𝐗 ((←self.position.y))) = (((←self.position.y)) + ((0.1) * (𝐗 ((←self.velocity.y))))))]
abbrev A4 := LLTL[𝐆 ((𝐗 ((←self.position.z))) = (((←self.position.z)) + ((0.1) * (𝐗 ((←self.velocity.z))))))]

abbrev assumptions : TraceSet TraceState := LLTL[A0 ∧ A1 ∧ A2 ∧ A3 ∧ A4]

-- Internal Assumptions 

abbrev i_assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Guarantees 
abbrev IG0 := LLTL[𝐆 (True)]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0]

-- Top Level Guarantees 
abbrev G0 := LLTL[𝐆 ((((←true_dist_sq)) > ((←max_dist_sq))) → (((←approach_dot)) ≥ (0)))]
abbrev G1 := LLTL[𝐆 ((((←true_dist_sq)) < ((←min_dist_sq))) → (((←approach_dot)) ≤ (0)))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1]

