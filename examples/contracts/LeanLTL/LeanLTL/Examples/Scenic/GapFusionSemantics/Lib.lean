import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace GapFusionSemantics

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

structure FuncOutput where
  N5: ℚ
  N4: ℚ
deriving Inhabited

def ComponentFunc (t: TraceState) : FuncOutput :=
  let radar_rear_gap := t.N3;
  let lidar_rear_gap := t.N1;
  let radar_rear_closing := t.N2;
  let lidar_rear_closing := t.N0;

  let fused_gap := (radar_rear_gap) ⊓ (lidar_rear_gap);
  let fused_closing := (radar_rear_closing) ⊔ (lidar_rear_closing);
  {N5 := (fused_gap), N4 := (fused_closing)}

def CF : TraceFun TraceState FuncOutput := TraceFun.of ComponentFunc
def CF_N5 : TraceFun TraceState ℚ := TraceFun.map (·.N5) CF 
def CF_N4 : TraceFun TraceState ℚ := TraceFun.map (·.N4) CF 

-- Prop Signals

-- Numerical Signals
abbrev lidar_rear_closing : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev lidar_rear_gap : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev radar_rear_closing : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev radar_rear_gap : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev rear_closing : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev rear_gap : TraceFun TraceState ℚ := TraceFun.of (·.N5)

-- Defs

-- Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Function Properties 
abbrev F0 := LLTL[𝐆 ((←rear_gap) = (←CF_N5))]
abbrev F1 := LLTL[𝐆 ((←rear_closing) = (←CF_N4))]

abbrev fprops : TraceSet TraceState := LLTL[F0 ∧ F1]

-- Guarantees 
abbrev G0 := LLTL[𝐆 (((←rear_gap)) = (((←radar_rear_gap)) ⊓ ((←lidar_rear_gap))))]
abbrev G1 := LLTL[𝐆 (((←rear_closing)) = (((←radar_rear_closing)) ⊔ ((←lidar_rear_closing))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1]

