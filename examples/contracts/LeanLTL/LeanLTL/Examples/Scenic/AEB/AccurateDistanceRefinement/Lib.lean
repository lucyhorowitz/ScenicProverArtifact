import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace AccurateDistanceRefinement

structure TraceState where
  -- Props
  -- Numbers
  N0: ℚ
  N1: ℚ
  N2: ℚ
  N3: ℚ
deriving Inhabited

-- Prop Signals

-- Numerical Signals
abbrev dist : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev lead_distances_lead_car_ : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev params__lead_car_width__ : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev params__weather__ : TraceFun TraceState ℚ := TraceFun.of (·.N3)

-- Defs
abbrev lead_dist := LLTLV[(lead_distances_lead_car_)]
abbrev behind_car := LLTLV[((lead_dist)) ≤ (1000)]

-- Top Level Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Assumptions 
abbrev IA0 := LLTL[(((((←params__weather__)) = (0)) ∨ (((←params__weather__)) = (1))) ∧ (((←params__lead_car_width__)) ≥ (1.8))) ∨ (¬(((((←params__weather__)) = (0)) ∨ (((←params__weather__)) = (1))) ∧ (((←params__lead_car_width__)) ≥ (1.8))))]

abbrev i_assumptions : TraceSet TraceState := LLTL[IA0]

-- Internal Guarantees 
abbrev IG0 := LLTL[(((((←params__weather__)) = (0)) ∨ (((←params__weather__)) = (1))) ∧ (((←params__lead_car_width__)) ≥ (1.8))) → (𝐆 (((←behind_car)) → (((((←lead_dist)) - (0.1)) ≤ ((←dist))) ∧ (((←dist)) ≤ (((←lead_dist)) + (0.1))))))]
abbrev IG1 := LLTL[((¬(((((←params__weather__)) = (0)) ∨ (((←params__weather__)) = (1))) ∧ (((←params__lead_car_width__)) ≥ (1.8)))) ∧ (¬(((((←params__weather__)) = (0)) ∨ (((←params__weather__)) = (1))) ∧ (((←params__lead_car_width__)) ≥ (1.8))))) → (𝐆 (((←behind_car)) → (((((←lead_dist)) - (0.1)) ≤ ((←dist))) ∧ (((←dist)) ≤ (((←lead_dist)) + (0.1))))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1]

-- Top Level Guarantees 
abbrev G0 := LLTL[𝐆 (((←behind_car)) → (((((←lead_dist)) - (0.1)) ≤ ((←dist))) ∧ (((←dist)) ≤ (((←lead_dist)) + (0.1)))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0]

