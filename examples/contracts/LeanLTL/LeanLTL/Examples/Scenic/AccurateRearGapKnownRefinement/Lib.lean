import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace AccurateRearGapKnownRefinement

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
abbrev params__visibility__ : TraceFun TraceState ℚ := TraceFun.of (·.N6)
abbrev params__weather__ : TraceFun TraceState ℚ := TraceFun.of (·.N7)
abbrev self.rearClosing : TraceFun TraceState ℚ := TraceFun.of (·.N8)
abbrev self.rearGap : TraceFun TraceState ℚ := TraceFun.of (·.N9)

-- Defs

-- Top Level Assumptions
abbrev A0 := LLTL[(((←params__visibility__)) = (0)) ∧ (((←params__weather__)) ≤ (1))]

abbrev assumptions : TraceSet TraceState := LLTL[A0]

-- Internal Assumptions
abbrev IA0 := LLTL[((←params__visibility__)) = (0)]
abbrev IA1 := LLTL[((←params__weather__)) ≤ (1)]

abbrev i_assumptions : TraceSet TraceState := LLTL[IA0 ∧ IA1]

-- Internal Guarantees
abbrev IG0 := LLTL[𝐆 (((((←self.rearGap)) - (0.5)) ≤ ((←SCENIC_INTERNAL_VAR_0))) ∧ (((←SCENIC_INTERNAL_VAR_0)) ≤ (((←self.rearGap)) + (0.5))))]
abbrev IG1 := LLTL[𝐆 (((((←self.rearClosing)) - (0.5)) ≤ ((←SCENIC_INTERNAL_VAR_1))) ∧ (((←SCENIC_INTERNAL_VAR_1)) ≤ (((←self.rearClosing)) + (0.5))))]
abbrev IG2 := LLTL[𝐆 (((((←self.rearGap)) - (0.5)) ≤ ((←SCENIC_INTERNAL_VAR_2))) ∧ (((←SCENIC_INTERNAL_VAR_2)) ≤ (((←self.rearGap)) + (0.5))))]
abbrev IG3 := LLTL[𝐆 (((((←self.rearClosing)) - (0.5)) ≤ ((←SCENIC_INTERNAL_VAR_3))) ∧ (((←SCENIC_INTERNAL_VAR_3)) ≤ (((←self.rearClosing)) + (0.5))))]
abbrev IG4 := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_4)) = (((←SCENIC_INTERNAL_VAR_0)) ⊓ ((←SCENIC_INTERNAL_VAR_2))))]
abbrev IG5 := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_5)) = (((←SCENIC_INTERNAL_VAR_1)) ⊔ ((←SCENIC_INTERNAL_VAR_3))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2 ∧ IG3 ∧ IG4 ∧ IG5]

-- Top Level Guarantees
abbrev G0 := LLTL[𝐆 (((((←self.rearGap)) - (0.5)) ≤ ((←SCENIC_INTERNAL_VAR_4))) ∧ (((←SCENIC_INTERNAL_VAR_4)) ≤ (((←self.rearGap)) + (0.5))))]
abbrev G1 := LLTL[𝐆 (((((←self.rearClosing)) - (0.5)) ≤ ((←SCENIC_INTERNAL_VAR_5))) ∧ (((←SCENIC_INTERNAL_VAR_5)) ≤ (((←self.rearClosing)) + (0.5))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1]

