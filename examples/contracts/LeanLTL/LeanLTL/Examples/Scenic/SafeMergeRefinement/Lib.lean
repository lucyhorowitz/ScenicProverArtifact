import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace SafeMergeRefinement

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
abbrev SCENIC_INTERNAL_VAR_7 : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev self.frontGap : TraceFun TraceState ℚ := TraceFun.of (·.N6)
abbrev self.mergeProgress : TraceFun TraceState ℚ := TraceFun.of (·.N7)
abbrev self.rearClosing : TraceFun TraceState ℚ := TraceFun.of (·.N8)
abbrev self.rearGap : TraceFun TraceState ℚ := TraceFun.of (·.N9)

-- Defs
abbrev required_rear := LLTLV[(8) + ((2) * ((0.0) ⊔ (SCENIC_INTERNAL_VAR_1)))]

-- Top Level Assumptions

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Assumptions

abbrev i_assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Guarantees
abbrev IG0 := LLTL[𝐆 (((((←self.rearGap)) - (0.5)) ≤ ((←SCENIC_INTERNAL_VAR_0))) ∧ (((←SCENIC_INTERNAL_VAR_0)) ≤ (((←self.rearGap)) + (0.5))))]
abbrev IG1 := LLTL[𝐆 (((((←self.rearClosing)) - (2.0)) ≤ ((←SCENIC_INTERNAL_VAR_1))) ∧ (((←SCENIC_INTERNAL_VAR_1)) ≤ (((←self.rearClosing)) + (2.0))))]
abbrev IG2 := LLTL[𝐆 (((((←self.frontGap)) - (1.5)) ≤ ((←SCENIC_INTERNAL_VAR_2))) ∧ (((←SCENIC_INTERNAL_VAR_2)) ≤ (((←self.frontGap)) + (1.5))))]
abbrev IG3 := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_4)) = ((←self.mergeProgress)))]
abbrev IG4 := LLTL[𝐆 (((((←SCENIC_INTERNAL_VAR_2)) > (10)) ∧ (((←SCENIC_INTERNAL_VAR_0)) > ((←required_rear)))) → (((←SCENIC_INTERNAL_VAR_3)) = (1.0)))]
abbrev IG5 := LLTL[𝐆 ((¬((((←SCENIC_INTERNAL_VAR_2)) > (10)) ∧ (((←SCENIC_INTERNAL_VAR_0)) > ((←required_rear))))) → (((←SCENIC_INTERNAL_VAR_3)) = (0.0)))]
abbrev IG6 := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_7)) = (0.0)) ∨ (((←SCENIC_INTERNAL_VAR_7)) = (1.0)))]
abbrev IG7 := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_7)) = (1.0)) → ((((←SCENIC_INTERNAL_VAR_3)) ≥ (1.0)) ∨ (((←SCENIC_INTERNAL_VAR_4)) ≥ (0.6))))]
abbrev IG8 := LLTL[𝐆 (((((←SCENIC_INTERNAL_VAR_3)) < (1.0)) ∧ (((←SCENIC_INTERNAL_VAR_4)) < (0.6))) → (((←SCENIC_INTERNAL_VAR_7)) = (0.0)))]
abbrev IG9 := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_7)) = (0.0)) → ((𝐗 ((←self.mergeProgress))) ≤ (((←self.mergeProgress)) + (0.02))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2 ∧ IG3 ∧ IG4 ∧ IG5 ∧ IG6 ∧ IG7 ∧ IG8 ∧ IG9]

-- Top Level Guarantees
abbrev G0 := LLTL[𝐆 ((((𝐗 ((←self.mergeProgress))) > (((←self.mergeProgress)) + (0.02))) ∧ (((←self.mergeProgress)) < (0.6))) → ((((←self.frontGap)) > ((10) - (1.5))) ∧ (((←self.rearGap)) > ((8) - (0.5)))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0]

