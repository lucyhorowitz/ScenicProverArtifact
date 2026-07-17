import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace ReportedRelativePositionComputerSemantics

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
deriving Inhabited

structure FuncOutput where
  N3: ℚ
  N4: ℚ
  N5: ℚ
deriving Inhabited

def ComponentFunc (t: TraceState) : FuncOutput :=
  let own_x := t.N0;
  let own_y := t.N1;
  let own_z := t.N2;
  let reported_x := t.N6;
  let reported_y := t.N7;
  let reported_z := t.N8;

  let x := (reported_x) - (own_x);
  let y := (reported_y) - (own_y);
  let z := (reported_z) - (own_z);
  {N3 := (x), N4 := (y), N5 := (z)}

def CF : TraceFun TraceState FuncOutput := TraceFun.of ComponentFunc
def CF_N3 : TraceFun TraceState ℚ := TraceFun.map (·.N3) CF 
def CF_N4 : TraceFun TraceState ℚ := TraceFun.map (·.N4) CF 
def CF_N5 : TraceFun TraceState ℚ := TraceFun.map (·.N5) CF 

-- Prop Signals

-- Numerical Signals
abbrev own_x : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev own_y : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev own_z : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev rel_x : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev rel_y : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev rel_z : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev reported_x : TraceFun TraceState ℚ := TraceFun.of (·.N6)
abbrev reported_y : TraceFun TraceState ℚ := TraceFun.of (·.N7)
abbrev reported_z : TraceFun TraceState ℚ := TraceFun.of (·.N8)

-- Defs

-- Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Function Properties 
abbrev F0 : TraceSet TraceState := LLTL[𝐆 ((←rel_x) = (←CF_N3))]
abbrev F1 : TraceSet TraceState := LLTL[𝐆 ((←rel_y) = (←CF_N4))]
abbrev F2 : TraceSet TraceState := LLTL[𝐆 ((←rel_z) = (←CF_N5))]

abbrev fprops : TraceSet TraceState := LLTL[F0 ∧ F1 ∧ F2]

-- Guarantees 
abbrev G0 : TraceSet TraceState := LLTL[𝐆 (((←rel_x)) = (((←reported_x)) - ((←own_x))))]
abbrev G1 : TraceSet TraceState := LLTL[𝐆 (((←rel_y)) = (((←reported_y)) - ((←own_y))))]
abbrev G2 : TraceSet TraceState := LLTL[𝐆 (((←rel_z)) = (((←reported_z)) - ((←own_z))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1 ∧ G2]

