import LeanLTL.Examples.Scenic.DroneDistance.FollowerMovementDirectionalSafetyRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerMovementDirectionalSafetyRefinement


theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t ⟨⟨hA0, hA1, hA2, hA3, hA4⟩, ⟨hIG0, hIG1, _, _, _, _, hIG6, hIG7, hIG8, hIG9⟩⟩
  simp [push_ltl] at *
  constructor
  · intro n hn hfar
    have hctrl  := hIG0 n hn               -- far → dot_prod ≥ 0 (the control law)
    have hrelx  := hIG6 n hn               -- N1 = true rel x
    have hrely  := hIG7 n hn
    have hrelz  := hIG8 n hn
    have hdist  := hIG9 n hn               -- N0 = N1² + N2² + N3²
    have hdx := hA2 n hn
    have hdy := hA3 n hn
    have hdz := hA4 n hn
    rcases hdx with ⟨px, ⟨hlen, hpx⟩, ⟨vx, ⟨_, hvx⟩, hstepx⟩⟩
    rcases hdy with ⟨py, ⟨hlen, hpy⟩, ⟨vy, ⟨_, hvy⟩, hstepy⟩⟩
    rcases hdz with ⟨pz, ⟨hlen, hpz⟩, ⟨vz, ⟨_, hvz⟩, hstepz⟩⟩
    simp [hlen] at *
    have hN0 : 15.0 * 15.0 < (t.toFun! n).N0 := by
      rw [hdist, hrelx, hrely, hrelz]; exact hfar
    have hdot := hctrl hN0
    subst hpx hpy hpz hvx hvy hvz
    rw [hstepx, hstepy, hstepz]
    rw [hrelx, hrely, hrelz] at hdot
    nlinarith [hdot]
  · intro n hn hfar
    have hctrl := hIG1 n hn              -- far → dot_prod ≥ 0 (the control law)
    have hrelx  := hIG6 n hn               -- N1 = true rel x
    have hrely  := hIG7 n hn
    have hrelz  := hIG8 n hn
    have hdist  := hIG9 n hn               -- N0 = N1² + N2² + N3²
    have hdx := hA2 n hn
    have hdy := hA3 n hn
    have hdz := hA4 n hn
    rcases hdx with ⟨px, ⟨hlen, hpx⟩, ⟨vx, ⟨_, hvx⟩, hstepx⟩⟩
    rcases hdy with ⟨py, ⟨hlen, hpy⟩, ⟨vy, ⟨_, hvy⟩, hstepy⟩⟩
    rcases hdz with ⟨pz, ⟨hlen, hpz⟩, ⟨vz, ⟨_, hvz⟩, hstepz⟩⟩
    simp [hlen] at *
    subst hpx hpy hpz hvx hvy hvz
    rw [hstepx, hstepy, hstepz]
    have hN0 : (t.toFun! n).N0 < 5.0 * 5.0 := by
      rw [hdist, hrelx, hrely, hrelz]; exact hfar
    have hdot := hctrl hN0
    rw [hrelx, hrely, hrelz] at hdot
    nlinarith [hdot]
