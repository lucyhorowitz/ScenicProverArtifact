import LeanLTL.Examples.Scenic.DroneDistance.FollowerVelocityDirectionalSafetyRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerVelocityDirectionalSafetyRefinement

/- Every guarantee is the corresponding internal guarantee with the actuation
   law (IG6: next velocity = commanded velocity) substituted in. -/
theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t ⟨⟨hA0, hA1, hA2⟩, ⟨hIG0, hIG1, hIG2, hIG3, hIG4, hIG5, hIG6⟩⟩
  simp [push_ltl] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- G0: too far → dot_prod ≥ 0
    intro n hn hfar
    have hcmd := hIG0 n hn hfar
    obtain ⟨⟨hlen, hvx⟩, ⟨_, hvy⟩, _, hvz⟩ := hIG6 n hn
    simp [hlen, hvx, hvy, hvz]
    linarith
  · -- G1: too close → dot_prod ≤ 0
    intro n hn hnear
    have hcmd := hIG1 n hn hnear
    obtain ⟨⟨hlen, hvx⟩, ⟨_, hvy⟩, _, hvz⟩ := hIG6 n hn
    simp [hlen, hvx, hvy, hvz]
    linarith
  · -- G2: in band → next velocity = 0
    intro n hn hlo hhi
    obtain ⟨hc4, hc5, hc6⟩ := hIG2 n hn hlo hhi
    obtain ⟨⟨hlen, hvx⟩, ⟨_, hvy⟩, _, hvz⟩ := hIG6 n hn
    exact ⟨⟨hlen, by rw [hvx, hc4]⟩, ⟨hlen, by rw [hvy, hc5]⟩, hlen, by rw [hvz, hc6]⟩
  · -- G3: |next velocity.x| ≤ 3
    intro n hn
    have hbnd := hIG3 n hn
    obtain ⟨⟨hlen, hvx⟩, ⟨_, hvy⟩, _, hvz⟩ := hIG6 n hn
    simp [hlen, hvx]
    exact ⟨by linarith [hbnd.1], by linarith [hbnd.2]⟩
  · -- G4: |next velocity.y| ≤ 3
    intro n hn
    have hbnd := hIG4 n hn
    obtain ⟨⟨hlen, hvx⟩, ⟨_, hvy⟩, _, hvz⟩ := hIG6 n hn
    simp [hlen, hvy]
    exact ⟨by linarith [hbnd.1], by linarith [hbnd.2]⟩
  · -- G5: |next velocity.z| ≤ 3
    intro n hn
    have hbnd := hIG5 n hn
    obtain ⟨⟨hlen, hvx⟩, ⟨_, hvy⟩, _, hvz⟩ := hIG6 n hn
    simp [hlen, hvz]
    exact ⟨by linarith [hbnd.1], by linarith [hbnd.2]⟩
