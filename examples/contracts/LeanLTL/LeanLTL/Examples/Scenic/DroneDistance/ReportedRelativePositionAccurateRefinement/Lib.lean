import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace ReportedRelativePositionAccurateRefinement

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
  N13: ℚ
  N14: ℚ
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
abbrev SCENIC_INTERNAL_VAR_7 : TraceFun TraceState ℚ := TraceFun.of (·.N7)
abbrev SCENIC_INTERNAL_VAR_8 : TraceFun TraceState ℚ := TraceFun.of (·.N8)
abbrev self.leadPos.x : TraceFun TraceState ℚ := TraceFun.of (·.N9)
abbrev self.leadPos.y : TraceFun TraceState ℚ := TraceFun.of (·.N10)
abbrev self.leadPos.z : TraceFun TraceState ℚ := TraceFun.of (·.N11)
abbrev self.position.x : TraceFun TraceState ℚ := TraceFun.of (·.N12)
abbrev self.position.y : TraceFun TraceState ℚ := TraceFun.of (·.N13)
abbrev self.position.z : TraceFun TraceState ℚ := TraceFun.of (·.N14)

-- Defs

-- Top Level Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Assumptions 

abbrev i_assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Guarantees 
abbrev IG0 : TraceSet TraceState := LLTL[𝐆 ((((←self.position.x)) = ((←SCENIC_INTERNAL_VAR_3))) ∧ (((←self.position.y)) = ((←SCENIC_INTERNAL_VAR_4))) ∧ (((←self.position.z)) = ((←SCENIC_INTERNAL_VAR_5))))]
abbrev IG1 : TraceSet TraceState := LLTL[𝐆 ((((←self.leadPos.x)) = ((←SCENIC_INTERNAL_VAR_6))) ∧ (((←self.leadPos.y)) = ((←SCENIC_INTERNAL_VAR_7))) ∧ (((←self.leadPos.z)) = ((←SCENIC_INTERNAL_VAR_8))))]
abbrev IG2 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_0)) = (((←SCENIC_INTERNAL_VAR_6)) - ((←SCENIC_INTERNAL_VAR_3))))]
abbrev IG3 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_1)) = (((←SCENIC_INTERNAL_VAR_7)) - ((←SCENIC_INTERNAL_VAR_4))))]
abbrev IG4 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_2)) = (((←SCENIC_INTERNAL_VAR_8)) - ((←SCENIC_INTERNAL_VAR_5))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2 ∧ IG3 ∧ IG4]

-- Top Level Guarantees 
abbrev G0 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_0)) = (((←self.leadPos.x)) - ((←self.position.x))))]
abbrev G1 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_1)) = (((←self.leadPos.y)) - ((←self.position.y))))]
abbrev G2 : TraceSet TraceState := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_2)) = (((←self.leadPos.z)) - ((←self.position.z))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1 ∧ G2]

