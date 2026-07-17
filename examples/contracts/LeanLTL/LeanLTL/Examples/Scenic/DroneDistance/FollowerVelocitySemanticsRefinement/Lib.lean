import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerVelocitySemanticsRefinement

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
deriving Inhabited

-- Prop Signals

-- Numerical Signals
abbrev SCENIC_INTERNAL_VAR_0 : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev SCENIC_INTERNAL_VAR_1 : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev SCENIC_INTERNAL_VAR_2 : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev SCENIC_INTERNAL_VAR_3 : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev SCENIC_INTERNAL_VAR_4 : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev SCENIC_INTERNAL_VAR_5 : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev SCENIC_INTERNAL_VAR_6 : TraceFun TraceState ℚ := TraceFun.of (·.N6)
abbrev self.velocity.x : TraceFun TraceState ℚ := TraceFun.of (·.N7)
abbrev self.velocity.y : TraceFun TraceState ℚ := TraceFun.of (·.N8)
abbrev self.velocity.z : TraceFun TraceState ℚ := TraceFun.of (·.N9)

-- Defs
abbrev max_dist_sq : TraceFun TraceState ℚ := LLTLV[(15.0) * (15.0)]
abbrev min_dist_sq : TraceFun TraceState ℚ := LLTLV[(5.0) * (5.0)]

-- Top Level Assumptions 
abbrev A0 : TraceSet TraceState := LLTL[((0.2 : ℚ)) > ((0 : ℚ))]
abbrev A1 : TraceSet TraceState := LLTL[((3.0 : ℚ)) > ((0 : ℚ))]
abbrev A2 : TraceSet TraceState := LLTL[((0 : ℚ)) ≤ ((5.0 : ℚ))]
abbrev A3 : TraceSet TraceState := LLTL[((5.0 : ℚ)) ≤ ((15.0 : ℚ))]

abbrev assumptions : TraceSet TraceState := LLTL[A0 ∧ A1 ∧ A2 ∧ A3]

-- Internal Assumptions 
abbrev IA0 : TraceSet TraceState := LLTL[((0.2 : ℚ)) > ((0 : ℚ))]
abbrev IA1 : TraceSet TraceState := LLTL[((3.0 : ℚ)) > ((0 : ℚ))]
abbrev IA2 : TraceSet TraceState := LLTL[((0 : ℚ)) ≤ ((5.0 : ℚ))]
abbrev IA3 : TraceSet TraceState := LLTL[((5.0 : ℚ)) ≤ ((15.0 : ℚ))]

abbrev i_assumptions : TraceSet TraceState := LLTL[IA0 ∧ IA1 ∧ IA2 ∧ IA3]

-- Internal Guarantees 
abbrev IG0 : TraceSet TraceState := LLTL[𝐆 (((((←min_dist_sq)) ≤ ((←SCENIC_INTERNAL_VAR_0))) ∧ (((←SCENIC_INTERNAL_VAR_0)) ≤ ((←max_dist_sq)))) → ((((←SCENIC_INTERNAL_VAR_4)) = ((0 : ℚ))) ∧ (((←SCENIC_INTERNAL_VAR_5)) = ((0 : ℚ))) ∧ (((←SCENIC_INTERNAL_VAR_6)) = ((0 : ℚ)))))]
abbrev IG1 : TraceSet TraceState := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_0)) < ((←min_dist_sq))) → ((((←SCENIC_INTERNAL_VAR_4)) = ((((-((0.2 : ℚ))) * ((←SCENIC_INTERNAL_VAR_1))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←SCENIC_INTERNAL_VAR_5)) = ((((-((0.2 : ℚ))) * ((←SCENIC_INTERNAL_VAR_2))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←SCENIC_INTERNAL_VAR_6)) = ((((-((0.2 : ℚ))) * ((←SCENIC_INTERNAL_VAR_3))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]
abbrev IG2 : TraceSet TraceState := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_0)) > ((←max_dist_sq))) → ((((←SCENIC_INTERNAL_VAR_4)) = (((((0.2 : ℚ)) * ((←SCENIC_INTERNAL_VAR_1))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←SCENIC_INTERNAL_VAR_5)) = (((((0.2 : ℚ)) * ((←SCENIC_INTERNAL_VAR_2))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←SCENIC_INTERNAL_VAR_6)) = (((((0.2 : ℚ)) * ((←SCENIC_INTERNAL_VAR_3))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]
abbrev IG3 : TraceSet TraceState := LLTL[𝐆 (((𝐗 ((←self.velocity.x))) = ((←SCENIC_INTERNAL_VAR_4))) ∧ ((𝐗 ((←self.velocity.y))) = ((←SCENIC_INTERNAL_VAR_5))) ∧ ((𝐗 ((←self.velocity.z))) = ((←SCENIC_INTERNAL_VAR_6))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2 ∧ IG3]

-- Top Level Guarantees 
abbrev G0 : TraceSet TraceState := LLTL[𝐆 (((((←min_dist_sq)) ≤ ((←SCENIC_INTERNAL_VAR_0))) ∧ (((←SCENIC_INTERNAL_VAR_0)) ≤ ((←max_dist_sq)))) → (((𝐗 ((←self.velocity.x))) = ((0 : ℚ))) ∧ ((𝐗 ((←self.velocity.y))) = ((0 : ℚ))) ∧ ((𝐗 ((←self.velocity.z))) = ((0 : ℚ)))))]
abbrev G1 : TraceSet TraceState := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_0)) < ((←min_dist_sq))) → (((𝐗 ((←self.velocity.x))) = ((((-((0.2 : ℚ))) * ((←SCENIC_INTERNAL_VAR_1))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ ((𝐗 ((←self.velocity.y))) = ((((-((0.2 : ℚ))) * ((←SCENIC_INTERNAL_VAR_2))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ ((𝐗 ((←self.velocity.z))) = ((((-((0.2 : ℚ))) * ((←SCENIC_INTERNAL_VAR_3))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]
abbrev G2 : TraceSet TraceState := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_0)) > ((←max_dist_sq))) → (((𝐗 ((←self.velocity.x))) = (((((0.2 : ℚ)) * ((←SCENIC_INTERNAL_VAR_1))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ ((𝐗 ((←self.velocity.y))) = (((((0.2 : ℚ)) * ((←SCENIC_INTERNAL_VAR_2))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ ((𝐗 ((←self.velocity.z))) = (((((0.2 : ℚ)) * ((←SCENIC_INTERNAL_VAR_3))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1 ∧ G2]

