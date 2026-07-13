import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace ReportedSquaredDistanceComputerSemantics

structure TraceState where
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

structure FuncOutput where
  N6: ℚ
  N3: ℚ
  N4: ℚ
  N5: ℚ
deriving Inhabited

def ComponentFunc (t: TraceState) : FuncOutput :=
  let own_x := t.N0;
  let own_y := t.N1;
  let own_z := t.N2;
  let reported_x := t.N7;
  let reported_y := t.N8;
  let reported_z := t.N9;

  let x := (reported_x) - (own_x);
  let y := (reported_y) - (own_y);
  let z := (reported_z) - (own_z);
  let reported_dist_sq := (((x) * (x)) + ((y) * (y))) + ((z) * (z));
  {N6 := (reported_dist_sq), N3 := (x), N4 := (y), N5 := (z)}

def CF : TraceFun TraceState FuncOutput := TraceFun.of ComponentFunc
def CF_N6 : TraceFun TraceState ℚ := TraceFun.map (·.N6) CF
def CF_N3 : TraceFun TraceState ℚ := TraceFun.map (·.N3) CF
def CF_N4 : TraceFun TraceState ℚ := TraceFun.map (·.N4) CF
def CF_N5 : TraceFun TraceState ℚ := TraceFun.map (·.N5) CF

abbrev own_x : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev own_y : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev own_z : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev rel_x : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev rel_y : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev rel_z : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev reported_dist_sq : TraceFun TraceState ℚ := TraceFun.of (·.N6)
abbrev reported_x : TraceFun TraceState ℚ := TraceFun.of (·.N7)
abbrev reported_y : TraceFun TraceState ℚ := TraceFun.of (·.N8)
abbrev reported_z : TraceFun TraceState ℚ := TraceFun.of (·.N9)

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

abbrev F0 := LLTL[𝐆 ((←reported_dist_sq) = (←CF_N6))]
abbrev F1 := LLTL[𝐆 ((←rel_x) = (←CF_N3))]
abbrev F2 := LLTL[𝐆 ((←rel_y) = (←CF_N4))]
abbrev F3 := LLTL[𝐆 ((←rel_z) = (←CF_N5))]

abbrev fprops : TraceSet TraceState := LLTL[F0 ∧ F1 ∧ F2 ∧ F3]

abbrev G0 := LLTL[𝐆 (((←rel_x)) = (((←reported_x)) - ((←own_x))))]
abbrev G1 := LLTL[𝐆 (((←rel_y)) = (((←reported_y)) - ((←own_y))))]
abbrev G2 := LLTL[𝐆 (((←rel_z)) = (((←reported_z)) - ((←own_z))))]
abbrev G3 := LLTL[𝐆 (((←reported_dist_sq)) = (((((←rel_x)) * ((←rel_x))) + (((←rel_y)) * ((←rel_y)))) + (((←rel_z)) * ((←rel_z)))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1 ∧ G2 ∧ G3]
