import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace MergeGovernorSafety

structure TraceState where
  -- Props
  -- Numbers
  N0: ℚ
  N1: ℚ
  N2: ℚ
  N3: ℚ
deriving Inhabited

structure FuncOutput where
  N1: ℚ
  N0: ℚ
deriving Inhabited

def ComponentFunc (t: TraceState) : FuncOutput :=
  let merge_ok := t.N2;
  let progress := t.N3;
  let hold := t.N0;

  if ((progress) ≥ (0.6))
  then
    let hold := 0.0;
    {N1 := (1.0), N0 := (hold)}
  else
    if (((merge_ok) ≥ (1.0)) ∧ ((hold) ≤ (0.0)))
    then
      let hold := 0.0;
      {N1 := (1.0), N0 := (hold)}
    else
      if ((merge_ok) ≥ (1.0))
      then
        let hold := (0.0) ⊔ ((hold) - (1.0));
        {N1 := (0.0), N0 := (hold)}
      else
        let hold := 10.0;
        {N1 := (0.0), N0 := (hold)}


def CF : TraceFun TraceState FuncOutput := TraceFun.of ComponentFunc
def CF_N1 : TraceFun TraceState ℚ := TraceFun.map (·.N1) CF
def CF_N0 : TraceFun TraceState ℚ := TraceFun.map (·.N0) CF

-- Prop Signals

-- Numerical Signals
abbrev hold : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev merge_cmd : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev merge_ok : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev progress : TraceFun TraceState ℚ := TraceFun.of (·.N3)

-- Defs

-- Assumptions

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Function Properties
abbrev F0 := LLTL[(←hold) = (←0.0)]
abbrev F1 := LLTL[𝐆 ((←merge_cmd) = (←CF_N1))]
abbrev F2 := LLTL[𝐆 ((𝐗 (←hold) = (←CF_N0)))]

abbrev fprops : TraceSet TraceState := LLTL[F0 ∧ F1 ∧ F2]

-- Guarantees
abbrev G0 := LLTL[𝐆 ((((←merge_cmd)) = (0.0)) ∨ (((←merge_cmd)) = (1.0)))]
abbrev G1 := LLTL[𝐆 ((((←merge_cmd)) = (1.0)) → ((((←merge_ok)) ≥ (1.0)) ∨ (((←progress)) ≥ (0.6))))]
abbrev G2 := LLTL[𝐆 (((((←merge_ok)) < (1.0)) ∧ (((←progress)) < (0.6))) → (((←merge_cmd)) = (0.0)))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1 ∧ G2]

