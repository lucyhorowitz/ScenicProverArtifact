import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerControllerSemantics

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
deriving Inhabited

structure FuncOutput where
  N0: ℚ
  N1: ℚ
  N2: ℚ
deriving Inhabited

def ComponentFunc (t: TraceState) : FuncOutput :=
  let dist_sq := t.N3;
  let rel_x := t.N4;
  let rel_y := t.N5;
  let rel_z := t.N6;

  if ((dist_sq) > ((15.0) * (15.0)))
  then
    let cmd_vx := (((0.2) * (rel_x)) ⊔ (-(3.0))) ⊓ (3.0);
    let cmd_vy := (((0.2) * (rel_y)) ⊔ (-(3.0))) ⊓ (3.0);
    let cmd_vz := (((0.2) * (rel_z)) ⊔ (-(3.0))) ⊓ (3.0);
    {N0 := (cmd_vx), N1 := (cmd_vy), N2 := (cmd_vz)}
  else
    if ((dist_sq) < ((5.0) * (5.0)))
    then
      let cmd_vx := (((-(0.2)) * (rel_x)) ⊔ (-(3.0))) ⊓ (3.0);
      let cmd_vy := (((-(0.2)) * (rel_y)) ⊔ (-(3.0))) ⊓ (3.0);
      let cmd_vz := (((-(0.2)) * (rel_z)) ⊔ (-(3.0))) ⊓ (3.0);
      {N0 := (cmd_vx), N1 := (cmd_vy), N2 := (cmd_vz)}
    else
      let cmd_vx := 0.0;
      let cmd_vy := 0.0;
      let cmd_vz := 0.0;
      {N0 := (cmd_vx), N1 := (cmd_vy), N2 := (cmd_vz)}

def CF : TraceFun TraceState FuncOutput := TraceFun.of ComponentFunc
def CF_N0 : TraceFun TraceState ℚ := TraceFun.map (·.N0) CF 
def CF_N1 : TraceFun TraceState ℚ := TraceFun.map (·.N1) CF 
def CF_N2 : TraceFun TraceState ℚ := TraceFun.map (·.N2) CF 

-- Prop Signals

-- Numerical Signals
abbrev cmd_vx : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev cmd_vy : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev cmd_vz : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev dist_sq : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev rel_x : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev rel_y : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev rel_z : TraceFun TraceState ℚ := TraceFun.of (·.N6)

-- Defs
abbrev max_dist_sq : TraceFun TraceState ℚ := LLTLV[(15.0) * (15.0)]
abbrev min_dist_sq : TraceFun TraceState ℚ := LLTLV[(5.0) * (5.0)]

-- Assumptions 
abbrev A0 : TraceSet TraceState := LLTL[((0.2 : ℚ)) > ((0 : ℚ))]
abbrev A1 : TraceSet TraceState := LLTL[((3.0 : ℚ)) > ((0 : ℚ))]
abbrev A2 : TraceSet TraceState := LLTL[((0 : ℚ)) ≤ ((5.0 : ℚ))]
abbrev A3 : TraceSet TraceState := LLTL[((5.0 : ℚ)) ≤ ((15.0 : ℚ))]

abbrev assumptions : TraceSet TraceState := LLTL[A0 ∧ A1 ∧ A2 ∧ A3]

-- Function Properties 
abbrev F0 : TraceSet TraceState := LLTL[𝐆 ((←cmd_vx) = (←CF_N0))]
abbrev F1 : TraceSet TraceState := LLTL[𝐆 ((←cmd_vy) = (←CF_N1))]
abbrev F2 : TraceSet TraceState := LLTL[𝐆 ((←cmd_vz) = (←CF_N2))]

abbrev fprops : TraceSet TraceState := LLTL[F0 ∧ F1 ∧ F2]

-- Guarantees 
abbrev G0 : TraceSet TraceState := LLTL[𝐆 (((((←min_dist_sq)) ≤ ((←dist_sq))) ∧ (((←dist_sq)) ≤ ((←max_dist_sq)))) → ((((←cmd_vx)) = ((0 : ℚ))) ∧ (((←cmd_vy)) = ((0 : ℚ))) ∧ (((←cmd_vz)) = ((0 : ℚ)))))]
abbrev G1 : TraceSet TraceState := LLTL[𝐆 ((((←dist_sq)) < ((←min_dist_sq))) → ((((←cmd_vx)) = ((((-((0.2 : ℚ))) * ((←rel_x))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←cmd_vy)) = ((((-((0.2 : ℚ))) * ((←rel_y))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←cmd_vz)) = ((((-((0.2 : ℚ))) * ((←rel_z))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]
abbrev G2 : TraceSet TraceState := LLTL[𝐆 ((((←dist_sq)) > ((←max_dist_sq))) → ((((←cmd_vx)) = (((((0.2 : ℚ)) * ((←rel_x))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←cmd_vy)) = (((((0.2 : ℚ)) * ((←rel_y))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ)))) ∧ (((←cmd_vz)) = (((((0.2 : ℚ)) * ((←rel_z))) ⊔ (-((3.0 : ℚ)))) ⊓ ((3.0 : ℚ))))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1 ∧ G2]

