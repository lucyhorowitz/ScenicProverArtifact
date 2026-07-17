import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace SquaredDistanceSystemAccuracyRefinement

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
abbrev self.leadPos.x : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev self.leadPos.y : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev self.leadPos.z : TraceFun TraceState ℚ := TraceFun.of (·.N6)
abbrev self.position.x : TraceFun TraceState ℚ := TraceFun.of (·.N7)
abbrev self.position.y : TraceFun TraceState ℚ := TraceFun.of (·.N8)
abbrev self.position.z : TraceFun TraceState ℚ := TraceFun.of (·.N9)

-- Defs

-- Top Level Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Assumptions 

abbrev i_assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Guarantees 
abbrev IG0 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_0)) = (((←self.leadPos.x)) - ((←self.position.x))))]
abbrev IG1 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_1)) = (((←self.leadPos.y)) - ((←self.position.y))))]
abbrev IG2 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_2)) = (((←self.leadPos.z)) - ((←self.position.z))))]
abbrev IG3 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_3)) = (((((←SCENIC_INTERNAL_VAR_0)) * ((←SCENIC_INTERNAL_VAR_0))) + (((←SCENIC_INTERNAL_VAR_1)) * ((←SCENIC_INTERNAL_VAR_1)))) + (((←SCENIC_INTERNAL_VAR_2)) * ((←SCENIC_INTERNAL_VAR_2)))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2 ∧ IG3]

-- Top Level Guarantees 
abbrev G0 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_0)) = (((←self.leadPos.x)) - ((←self.position.x))))]
abbrev G1 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_1)) = (((←self.leadPos.y)) - ((←self.position.y))))]
abbrev G2 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_2)) = (((←self.leadPos.z)) - ((←self.position.z))))]
abbrev G3 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_3)) = (((((←SCENIC_INTERNAL_VAR_0)) * ((←SCENIC_INTERNAL_VAR_0))) + (((←SCENIC_INTERNAL_VAR_1)) * ((←SCENIC_INTERNAL_VAR_1)))) + (((←SCENIC_INTERNAL_VAR_2)) * ((←SCENIC_INTERNAL_VAR_2)))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1 ∧ G2 ∧ G3]

