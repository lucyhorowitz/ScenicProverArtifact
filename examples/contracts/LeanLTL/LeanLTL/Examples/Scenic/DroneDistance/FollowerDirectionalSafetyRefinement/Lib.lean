import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerDirectionalSafetyRefinement

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
deriving Inhabited

-- Prop Signals

-- Numerical Signals
abbrev cmd_vx : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev cmd_vy : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev cmd_vz : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev dist_sq : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev rel_x : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev rel_y : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev rel_z : TraceFun TraceState ℚ := TraceFun.of (·.N6)

-- Defs
abbrev max_dist_sq : TraceFun TraceState ℚ := LLTLV[(15.0) * (15.0)]
abbrev min_dist_sq : TraceFun TraceState ℚ := LLTLV[(5.0) * (5.0)]
abbrev cmd_dot_prod : TraceFun TraceState ℚ := LLTLV[((((rel_x)) * ((cmd_vx))) + (((rel_y)) * ((cmd_vy)))) + (((rel_z)) * ((cmd_vz)))]

-- Top Level Assumptions 
abbrev A0 : TraceSet TraceState := LLTL[((3.0 : ℚ)) > ((0 : ℚ))]
abbrev A1 : TraceSet TraceState := LLTL[((0 : ℚ)) ≤ ((5.0 : ℚ))]
abbrev A2 : TraceSet TraceState := LLTL[((5.0 : ℚ)) ≤ ((15.0 : ℚ))]

abbrev assumptions : TraceSet TraceState := LLTL[A0 ∧ A1 ∧ A2]

-- Internal Assumptions 
abbrev IA0 : TraceSet TraceState := LLTL[((0.2 : ℚ)) > ((0 : ℚ))]
abbrev IA1 : TraceSet TraceState := LLTL[((0.5 : ℚ)) > ((0 : ℚ))]
abbrev IA2 : TraceSet TraceState := LLTL[((3.0 : ℚ)) > ((0 : ℚ))]
abbrev IA3 : TraceSet TraceState := LLTL[((0 : ℚ)) ≤ ((5.0 : ℚ))]
abbrev IA4 : TraceSet TraceState := LLTL[((5.0 : ℚ)) ≤ ((15.0 : ℚ))]

abbrev i_assumptions : TraceSet TraceState := LLTL[IA0 ∧ IA1 ∧ IA2 ∧ IA3 ∧ IA4]

-- Internal Guarantees 
abbrev IG0 : TraceSet TraceState := LLTL[𝐆 (((((←min_dist_sq)) ≤ ((←dist_sq))) ∧ (((←dist_sq)) ≤ ((←max_dist_sq)))) → ((((←cmd_vx)) = ((0 : ℚ))) ∧ (((←cmd_vy)) = ((0 : ℚ))) ∧ (((←cmd_vz)) = ((0 : ℚ)))))]
abbrev IG1 : TraceSet TraceState := LLTL[𝐆 ((((←dist_sq)) < ((←min_dist_sq))) → ((((←cmd_vx)) = ((((-((0.5 : ℚ))) * ((←rel_x))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←cmd_vy)) = ((((-((0.5 : ℚ))) * ((←rel_y))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←cmd_vz)) = ((((-((0.5 : ℚ))) * ((←rel_z))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]
abbrev IG2 : TraceSet TraceState := LLTL[𝐆 ((((←dist_sq)) > ((←max_dist_sq))) → ((((←cmd_vx)) = (((((0.2 : ℚ)) * ((←rel_x))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←cmd_vy)) = (((((0.2 : ℚ)) * ((←rel_y))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←cmd_vz)) = (((((0.2 : ℚ)) * ((←rel_z))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2]

-- Top Level Guarantees 
abbrev G0 : TraceSet TraceState := LLTL[𝐆 ((((←dist_sq)) > ((←max_dist_sq))) → (((←cmd_dot_prod)) ≥ ((0 : ℚ))))]
abbrev G1 : TraceSet TraceState := LLTL[𝐆 ((((←dist_sq)) < ((←min_dist_sq))) → (((←cmd_dot_prod)) ≤ ((0 : ℚ))))]
abbrev G2 : TraceSet TraceState := LLTL[𝐆 (((((←min_dist_sq)) ≤ ((←dist_sq))) ∧ (((←dist_sq)) ≤ ((←max_dist_sq)))) → ((((←cmd_vx)) = ((0 : ℚ))) ∧ (((←cmd_vy)) = ((0 : ℚ))) ∧ (((←cmd_vz)) = ((0 : ℚ)))))]
abbrev G3 : TraceSet TraceState := LLTL[𝐆 (((-((3.0 : ℚ))) ≤ ((←cmd_vx))) ∧ (((←cmd_vx)) ≤ ((3.0 : ℚ))))]
abbrev G4 : TraceSet TraceState := LLTL[𝐆 (((-((3.0 : ℚ))) ≤ ((←cmd_vy))) ∧ (((←cmd_vy)) ≤ ((3.0 : ℚ))))]
abbrev G5 : TraceSet TraceState := LLTL[𝐆 (((-((3.0 : ℚ))) ≤ ((←cmd_vz))) ∧ (((←cmd_vz)) ≤ ((3.0 : ℚ))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1 ∧ G2 ∧ G3 ∧ G4 ∧ G5]

