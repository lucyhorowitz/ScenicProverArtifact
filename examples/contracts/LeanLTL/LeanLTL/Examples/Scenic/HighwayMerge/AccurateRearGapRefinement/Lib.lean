import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace AccurateRearGapRefinement

structure TraceState where
  -- Props
  -- Numbers
  N0: ℚ
  N1: ℚ
  N2: ℚ
  N3: ℚ
  N4: ℚ
  N5: ℚ
deriving Inhabited

-- Prop Signals

-- Numerical Signals
abbrev params__visibility__ : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev params__weather__ : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev rear_closing : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev rear_gap : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev self.rearClosing : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev self.rearGap : TraceFun TraceState ℚ := TraceFun.of (·.N5)

-- Defs

-- Top Level Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Assumptions 
abbrev IA0 := LLTL[((((←params__visibility__)) = (0)) ∧ (((←params__weather__)) ≤ (1))) ∨ (¬((((←params__visibility__)) = (0)) ∧ (((←params__weather__)) ≤ (1))))]

abbrev i_assumptions : TraceSet TraceState := LLTL[IA0]

-- Internal Guarantees 
abbrev IG0 := LLTL[((((←params__visibility__)) = (0)) ∧ (((←params__weather__)) ≤ (1))) → ((𝐆 (((((←self.rearGap)) - (1.5)) ≤ ((←rear_gap))) ∧ (((←rear_gap)) ≤ (((←self.rearGap)) + (1.5))))) ∧ (𝐆 (((((←self.rearClosing)) - (2.0)) ≤ ((←rear_closing))) ∧ (((←rear_closing)) ≤ (((←self.rearClosing)) + (2.0))))))]
abbrev IG1 := LLTL[((¬((((←params__visibility__)) = (0)) ∧ (((←params__weather__)) ≤ (1)))) ∧ (¬((((←params__visibility__)) = (0)) ∧ (((←params__weather__)) ≤ (1))))) → ((𝐆 (((((←self.rearGap)) - (1.5)) ≤ ((←rear_gap))) ∧ (((←rear_gap)) ≤ (((←self.rearGap)) + (1.5))))) ∧ (𝐆 (((((←self.rearClosing)) - (2.0)) ≤ ((←rear_closing))) ∧ (((←rear_closing)) ≤ (((←self.rearClosing)) + (2.0))))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1]

-- Top Level Guarantees 
abbrev G0 := LLTL[𝐆 (((((←self.rearGap)) - (1.5)) ≤ ((←rear_gap))) ∧ (((←rear_gap)) ≤ (((←self.rearGap)) + (1.5))))]
abbrev G1 := LLTL[𝐆 (((((←self.rearClosing)) - (2.0)) ≤ ((←rear_closing))) ∧ (((←rear_closing)) ≤ (((←self.rearClosing)) + (2.0))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1]

