import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace SquaredMagnitudeComputerSemantics

structure TraceState where
  -- Props
  -- Numbers
  N0: ℚ
  N1: ℚ
  N2: ℚ
  N3: ℚ
deriving Inhabited

structure FuncOutput where
  N0: ℚ
deriving Inhabited

def ComponentFunc (t: TraceState) : FuncOutput :=
  let rel_x := t.N1;
  let rel_y := t.N2;
  let rel_z := t.N3;

  let dist_sq := (((rel_x) * (rel_x)) + ((rel_y) * (rel_y))) + ((rel_z) * (rel_z));
  {N0 := (dist_sq)}

def CF : TraceFun TraceState FuncOutput := TraceFun.of ComponentFunc
def CF_N0 : TraceFun TraceState ℚ := TraceFun.map (·.N0) CF 

-- Prop Signals

-- Numerical Signals
abbrev dist_sq : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev rel_x : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev rel_y : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev rel_z : TraceFun TraceState ℚ := TraceFun.of (·.N3)

-- Defs

-- Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Function Properties 
abbrev F0 : TraceSet TraceState := LLTL[𝐆 ((←dist_sq) = (←CF_N0))]

abbrev fprops : TraceSet TraceState := LLTL[F0]

-- Guarantees 
abbrev G0 : TraceSet TraceState := LLTL[𝐆 (((←dist_sq)) = (((((←rel_x)) * ((←rel_x))) + (((←rel_y)) * ((←rel_y)))) + (((←rel_z)) * ((←rel_z)))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0]

