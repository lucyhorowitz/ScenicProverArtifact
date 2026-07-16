import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace GapAcceptanceSemantics

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
deriving Inhabited

def ComponentFunc (t: TraceState) : FuncOutput :=
  let front_gap := t.N0;
  let rear_gap := t.N3;
  let rear_closing := t.N2;

  let required_rear := (8) + ((2) * ((0.0) ⊔ (rear_closing)));
  if (((front_gap) > (10)) ∧ ((rear_gap) > (required_rear)))
  then
    {N1 := (1.0)}
  else
    {N1 := (0.0)}
  

def CF : TraceFun TraceState FuncOutput := TraceFun.of ComponentFunc
def CF_N1 : TraceFun TraceState ℚ := TraceFun.map (·.N1) CF 

-- Prop Signals

-- Numerical Signals
abbrev front_gap : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev merge_ok : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev rear_closing : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev rear_gap : TraceFun TraceState ℚ := TraceFun.of (·.N3)

-- Defs
abbrev required_rear := LLTLV[(8) + ((2) * ((0.0) ⊔ ((rear_closing))))]

-- Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Function Properties 
abbrev F0 := LLTL[𝐆 ((←merge_ok) = (←CF_N1))]

abbrev fprops : TraceSet TraceState := LLTL[F0]

-- Guarantees 
abbrev G0 := LLTL[𝐆 (((((←front_gap)) > (10)) ∧ (((←rear_gap)) > ((←required_rear)))) → (((←merge_ok)) = (1.0)))]
abbrev G1 := LLTL[𝐆 ((¬((((←front_gap)) > (10)) ∧ (((←rear_gap)) > ((←required_rear))))) → (((←merge_ok)) = (0.0)))]

abbrev guarantees : TraceSet TraceState := LLTL[G0 ∧ G1]

