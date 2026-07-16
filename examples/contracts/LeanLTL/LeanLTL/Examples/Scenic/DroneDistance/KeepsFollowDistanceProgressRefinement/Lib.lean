import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace KeepsFollowDistanceProgressRefinement

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
abbrev min_dist_sq : TraceFun TraceState ℚ := LLTLV[(5.0) * (5.0)]
abbrev min_approach_speed : TraceFun TraceState ℚ := LLTLV[((0.2) * (15.0)) ⊓ (3.0)]
abbrev max_leader_step : TraceFun TraceState ℚ := LLTLV[(2.0) * (0.1)]
abbrev next_lead_disp_x : TraceFun TraceState ℚ := LLTLV[(𝐗 ((self.leadPos.x))) - ((self.leadPos.x))]
abbrev next_lead_disp_y : TraceFun TraceState ℚ := LLTLV[(𝐗 ((self.leadPos.y))) - ((self.leadPos.y))]
abbrev next_lead_disp_z : TraceFun TraceState ℚ := LLTLV[(𝐗 ((self.leadPos.z))) - ((self.leadPos.z))]
abbrev next_lead_disp_sq : TraceFun TraceState ℚ := LLTLV[((((next_lead_disp_x)) * ((next_lead_disp_x))) + (((next_lead_disp_y)) * ((next_lead_disp_y)))) + (((next_lead_disp_z)) * ((next_lead_disp_z)))]
abbrev true_rel_x : TraceFun TraceState ℚ := LLTLV[((self.leadPos.x)) - ((self.position.x))]
abbrev true_rel_y : TraceFun TraceState ℚ := LLTLV[((self.leadPos.y)) - ((self.position.y))]
abbrev true_rel_z : TraceFun TraceState ℚ := LLTLV[((self.leadPos.z)) - ((self.position.z))]
abbrev true_dist_sq : TraceFun TraceState ℚ := LLTLV[((((true_rel_x)) * ((true_rel_x))) + (((true_rel_y)) * ((true_rel_y)))) + (((true_rel_z)) * ((true_rel_z)))]
abbrev next_true_rel_x : TraceFun TraceState ℚ := LLTLV[(𝐗 ((self.leadPos.x))) - (𝐗 ((self.position.x)))]
abbrev next_true_rel_y : TraceFun TraceState ℚ := LLTLV[(𝐗 ((self.leadPos.y))) - (𝐗 ((self.position.y)))]
abbrev next_true_rel_z : TraceFun TraceState ℚ := LLTLV[(𝐗 ((self.leadPos.z))) - (𝐗 ((self.position.z)))]
abbrev next_true_dist_sq : TraceFun TraceState ℚ := LLTLV[((((next_true_rel_x)) * ((next_true_rel_x))) + (((next_true_rel_y)) * ((next_true_rel_y)))) + (((next_true_rel_z)) * ((next_true_rel_z)))]
abbrev delta_lin : TraceFun TraceState ℚ := LLTLV[(((min_approach_speed)) - (2.0)) * (0.1)]
abbrev delta_sq : TraceFun TraceState ℚ := LLTLV[((delta_lin)) * (15.0)]

-- Top Level Assumptions 
abbrev A0 : TraceSet TraceState := LLTL[((0.2 : ℚ)) > ((0 : ℚ))]
abbrev A1 : TraceSet TraceState := LLTL[((3.0 : ℚ)) > ((0 : ℚ))]
abbrev A2 : TraceSet TraceState := LLTL[((2.0 : ℚ)) < ((←min_approach_speed))]
abbrev A3 : TraceSet TraceState := LLTL[(((0.2 : ℚ)) * ((15.0 : ℚ))) ≤ ((3.0 : ℚ))]
abbrev A4 : TraceSet TraceState := LLTL[𝐆 ((𝐗 ((←self.position.x))) = (((←self.position.x)) + (((0.1 : ℚ)) * (𝐗 ((←self.velocity.x))))))]
abbrev A5 : TraceSet TraceState := LLTL[𝐆 ((𝐗 ((←self.position.y))) = (((←self.position.y)) + (((0.1 : ℚ)) * (𝐗 ((←self.velocity.y))))))]
abbrev A6 : TraceSet TraceState := LLTL[𝐆 ((𝐗 ((←self.position.z))) = (((←self.position.z)) + (((0.1 : ℚ)) * (𝐗 ((←self.velocity.z))))))]
abbrev A7 : TraceSet TraceState := LLTL[𝐆 (((←next_lead_disp_sq)) ≤ (((←max_leader_step)) * ((←max_leader_step))))]

abbrev assumptions : TraceSet TraceState := LLTL[A0 ∧ A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7]

-- Internal Assumptions 
abbrev IA0 : TraceSet TraceState := LLTL[((0.2 : ℚ)) > ((0 : ℚ))]
abbrev IA1 : TraceSet TraceState := LLTL[((3.0 : ℚ)) > ((0 : ℚ))]
abbrev IA2 : TraceSet TraceState := LLTL[((0 : ℚ)) ≤ ((5.0 : ℚ))]
abbrev IA3 : TraceSet TraceState := LLTL[((5.0 : ℚ)) ≤ ((15.0 : ℚ))]

abbrev i_assumptions : TraceSet TraceState := LLTL[IA0 ∧ IA1 ∧ IA2 ∧ IA3]

-- Internal Guarantees 
abbrev IG0 : TraceSet TraceState := LLTL[𝐆 (((((←min_dist_sq)) ≤ ((←SCENIC_INTERNAL_VAR_0))) ∧ (((←SCENIC_INTERNAL_VAR_0)) ≤ ((←max_dist_sq)))) → (((𝐗 ((←self.velocity.x))) = ((0 : ℚ))) ∧ ((𝐗 ((←self.velocity.y))) = ((0 : ℚ))) ∧ ((𝐗 ((←self.velocity.z))) = ((0 : ℚ)))))]
abbrev IG1 : TraceSet TraceState := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_0)) < ((←min_dist_sq))) → (((𝐗 ((←self.velocity.x))) = ((((-((0.2 : ℚ))) * ((←SCENIC_INTERNAL_VAR_1))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ ((𝐗 ((←self.velocity.y))) = ((((-((0.2 : ℚ))) * ((←SCENIC_INTERNAL_VAR_2))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ ((𝐗 ((←self.velocity.z))) = ((((-((0.2 : ℚ))) * ((←SCENIC_INTERNAL_VAR_3))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]
abbrev IG2 : TraceSet TraceState := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_0)) > ((←max_dist_sq))) → (((𝐗 ((←self.velocity.x))) = (((((0.2 : ℚ)) * ((←SCENIC_INTERNAL_VAR_1))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ ((𝐗 ((←self.velocity.y))) = (((((0.2 : ℚ)) * ((←SCENIC_INTERNAL_VAR_2))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ ((𝐗 ((←self.velocity.z))) = (((((0.2 : ℚ)) * ((←SCENIC_INTERNAL_VAR_3))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]
abbrev IG3 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_1)) = (((←self.leadPos.x)) - ((←self.position.x))))]
abbrev IG4 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_2)) = (((←self.leadPos.y)) - ((←self.position.y))))]
abbrev IG5 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_3)) = (((←self.leadPos.z)) - ((←self.position.z))))]
abbrev IG6 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_0)) = (((((←SCENIC_INTERNAL_VAR_1)) * ((←SCENIC_INTERNAL_VAR_1))) + (((←SCENIC_INTERNAL_VAR_2)) * ((←SCENIC_INTERNAL_VAR_2)))) + (((←SCENIC_INTERNAL_VAR_3)) * ((←SCENIC_INTERNAL_VAR_3)))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2 ∧ IG3 ∧ IG4 ∧ IG5 ∧ IG6]

-- Top Level Guarantees 
abbrev G0 : TraceSet TraceState := LLTL[𝐆 ((((←true_dist_sq)) > ((←max_dist_sq))) → (((←next_true_dist_sq)) ≤ (((←true_dist_sq)) - ((←delta_sq)))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0]

