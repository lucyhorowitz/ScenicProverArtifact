import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerMovementDirectionalSafetyRefinement

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
  N9: ℚ
  N10: ℚ
  N11: ℚ
  N12: ℚ
deriving Inhabited

-- Prop Signals

-- Numerical Signals
abbrev SCENIC_INTERNAL_VAR_0 : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev SCENIC_INTERNAL_VAR_1 : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev SCENIC_INTERNAL_VAR_2 : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev SCENIC_INTERNAL_VAR_3 : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev self.leadPos.x : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev self.leadPos.y : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev self.leadPos.z : TraceFun TraceState ℚ := TraceFun.of (·.N6)
abbrev self.position.x : TraceFun TraceState ℚ := TraceFun.of (·.N7)
abbrev self.position.y : TraceFun TraceState ℚ := TraceFun.of (·.N8)
abbrev self.position.z : TraceFun TraceState ℚ := TraceFun.of (·.N9)
abbrev self.velocity.x : TraceFun TraceState ℚ := TraceFun.of (·.N10)
abbrev self.velocity.y : TraceFun TraceState ℚ := TraceFun.of (·.N11)
abbrev self.velocity.z : TraceFun TraceState ℚ := TraceFun.of (·.N12)

-- Defs
abbrev max_dist_sq : TraceFun TraceState ℚ := LLTLV[(15.0) * (15.0)]
abbrev dot_prod : TraceFun TraceState ℚ := LLTLV[((((SCENIC_INTERNAL_VAR_1)) * (𝐗 ((self.velocity.x)))) + (((SCENIC_INTERNAL_VAR_2)) * (𝐗 ((self.velocity.y))))) + (((SCENIC_INTERNAL_VAR_3)) * (𝐗 ((self.velocity.z))))]
abbrev min_dist_sq : TraceFun TraceState ℚ := LLTLV[(5.0) * (5.0)]
abbrev true_rel_x : TraceFun TraceState ℚ := LLTLV[((self.leadPos.x)) - ((self.position.x))]
abbrev true_rel_y : TraceFun TraceState ℚ := LLTLV[((self.leadPos.y)) - ((self.position.y))]
abbrev true_rel_z : TraceFun TraceState ℚ := LLTLV[((self.leadPos.z)) - ((self.position.z))]
abbrev true_dist_sq : TraceFun TraceState ℚ := LLTLV[((((true_rel_x)) * ((true_rel_x))) + (((true_rel_y)) * ((true_rel_y)))) + (((true_rel_z)) * ((true_rel_z)))]
abbrev disp_x : TraceFun TraceState ℚ := LLTLV[(𝐗 ((self.position.x))) - ((self.position.x))]
abbrev disp_y : TraceFun TraceState ℚ := LLTLV[(𝐗 ((self.position.y))) - ((self.position.y))]
abbrev disp_z : TraceFun TraceState ℚ := LLTLV[(𝐗 ((self.position.z))) - ((self.position.z))]
abbrev approach_dot : TraceFun TraceState ℚ := LLTLV[((((true_rel_x)) * ((disp_x))) + (((true_rel_y)) * ((disp_y)))) + (((true_rel_z)) * ((disp_z)))]

-- Top Level Assumptions 
abbrev A0 : TraceSet TraceState := LLTL[((0 : ℚ)) ≤ ((5.0 : ℚ))]
abbrev A1 : TraceSet TraceState := LLTL[((5.0 : ℚ)) ≤ ((15.0 : ℚ))]
abbrev A2 : TraceSet TraceState := LLTL[𝐆 ((𝐗 ((←self.position.x))) = (((←self.position.x)) + (((0.1 : ℚ)) * (𝐗 ((←self.velocity.x))))))]
abbrev A3 : TraceSet TraceState := LLTL[𝐆 ((𝐗 ((←self.position.y))) = (((←self.position.y)) + (((0.1 : ℚ)) * (𝐗 ((←self.velocity.y))))))]
abbrev A4 : TraceSet TraceState := LLTL[𝐆 ((𝐗 ((←self.position.z))) = (((←self.position.z)) + (((0.1 : ℚ)) * (𝐗 ((←self.velocity.z))))))]

abbrev assumptions : TraceSet TraceState := LLTL[A0 ∧ A1 ∧ A2 ∧ A3 ∧ A4]

-- Internal Assumptions 
abbrev IA0 : TraceSet TraceState := LLTL[((3.0 : ℚ)) > ((0 : ℚ))]
abbrev IA1 : TraceSet TraceState := LLTL[((0 : ℚ)) ≤ ((5.0 : ℚ))]
abbrev IA2 : TraceSet TraceState := LLTL[((5.0 : ℚ)) ≤ ((15.0 : ℚ))]

abbrev i_assumptions : TraceSet TraceState := LLTL[IA0 ∧ IA1 ∧ IA2]

-- Internal Guarantees 
abbrev IG0 : TraceSet TraceState := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_0)) > ((←max_dist_sq))) → (((←dot_prod)) ≥ ((0 : ℚ))))]
abbrev IG1 : TraceSet TraceState := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_0)) < ((←min_dist_sq))) → (((←dot_prod)) ≤ ((0 : ℚ))))]
abbrev IG2 : TraceSet TraceState := LLTL[𝐆 (((((←min_dist_sq)) ≤ ((←SCENIC_INTERNAL_VAR_0))) ∧ (((←SCENIC_INTERNAL_VAR_0)) ≤ ((←max_dist_sq)))) → (((𝐗 ((←self.velocity.x))) = ((0 : ℚ))) ∧ ((𝐗 ((←self.velocity.y))) = ((0 : ℚ))) ∧ ((𝐗 ((←self.velocity.z))) = ((0 : ℚ)))))]
abbrev IG3 : TraceSet TraceState := LLTL[𝐆 (((-((3.0 : ℚ))) ≤ (𝐗 ((←self.velocity.x)))) ∧ ((𝐗 ((←self.velocity.x))) ≤ ((3.0 : ℚ))))]
abbrev IG4 : TraceSet TraceState := LLTL[𝐆 (((-((3.0 : ℚ))) ≤ (𝐗 ((←self.velocity.y)))) ∧ ((𝐗 ((←self.velocity.y))) ≤ ((3.0 : ℚ))))]
abbrev IG5 : TraceSet TraceState := LLTL[𝐆 (((-((3.0 : ℚ))) ≤ (𝐗 ((←self.velocity.z)))) ∧ ((𝐗 ((←self.velocity.z))) ≤ ((3.0 : ℚ))))]
abbrev IG6 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_1)) = (((←self.leadPos.x)) - ((←self.position.x))))]
abbrev IG7 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_2)) = (((←self.leadPos.y)) - ((←self.position.y))))]
abbrev IG8 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_3)) = (((←self.leadPos.z)) - ((←self.position.z))))]
abbrev IG9 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_0)) = (((((←SCENIC_INTERNAL_VAR_1)) * ((←SCENIC_INTERNAL_VAR_1))) + (((←SCENIC_INTERNAL_VAR_2)) * ((←SCENIC_INTERNAL_VAR_2)))) + (((←SCENIC_INTERNAL_VAR_3)) * ((←SCENIC_INTERNAL_VAR_3)))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2 ∧ IG3 ∧ IG4 ∧ IG5 ∧ IG6 ∧ IG7 ∧ IG8 ∧ IG9]

-- Top Level Guarantees 
abbrev G0 : TraceSet TraceState := LLTL[𝐆 ((((←true_dist_sq)) > ((←max_dist_sq))) → (((←approach_dot)) ≥ ((0 : ℚ))))]
abbrev G1 : TraceSet TraceState := LLTL[𝐆 ((((←true_dist_sq)) < ((←min_dist_sq))) → (((←approach_dot)) ≤ ((0 : ℚ))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1]

