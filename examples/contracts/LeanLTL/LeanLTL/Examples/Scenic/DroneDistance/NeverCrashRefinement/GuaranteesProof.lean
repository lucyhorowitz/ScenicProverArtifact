import LeanLTL.Examples.Scenic.DroneDistance.NeverCrashRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace NeverCrashRefinement

set_option maxHeartbeats 2000000


/-
  STRATEGY SKETCH for the never-crash invariant  G0 : 𝐆 (true_dist_sq ≥ R_sq).

  Signals (see Lib.lean): N0 = dist_sq (reported), N1/N2/N3 = rel_x/y/z (reported),
  N4/N5/N6 = leadPos, N7/N8/N9 = position, N10/N11/N12 = velocity.
  R = 5 - 0.2 = 4.8 (A47? no: R = min_dist - max_leader_step);  R_sq = R*R.

  Reduce reported → true first. IG3/IG4/IG5 give rel = leadPos - position and IG6
  gives dist_sq = rel·rel, so at every step  N0 = true_dist_sq  and the controller's
  zone tests (on N0) coincide with the invariant quantity. Establish this once as a
  𝐆 fact and rewrite N0 ↦ true_dist_sq throughout.

  Prove by induction with  `globally_induction`  (LeanLTL/TraceSet/Basic.lean:952),
  following the assembly in AEB/KeepsDistanceRefinement/GuaranteesProof.lean:667-736.
    • Base case (n = 0):  A13 gives true_dist_sq ≥ R_sq.
    • Step:  assume true_dist_sq(n) ≥ R_sq, show true_dist_sq(n+1) ≥ R_sq.

  The step is a case split on N0(n) against the band [min_dist_sq, max_dist_sq]. Let
  L = max_leader_step (A12 bounds |leader step|² ≤ L²), and use the integration law
  A9/A10/A11 to write self displacement = 0.1 · (next velocity). Next relative vector
  r' = r + leadStep - selfStep.  Three zones:

    (Band)  min_dist_sq ≤ N0 ≤ max_dist_sq:  IG0 ⇒ next velocity = 0 ⇒ selfStep = 0.
            d'² ≥ (d - L)² ≥ (min_dist - L)² = R²   (uses d ≥ min_dist ≥ L, from A5).
            No induction hypothesis needed.

    (Inner) N0 < min_dist_sq:  IG1 ⇒ next velocity = clamp(-0.5·rel); A7 (0.5·5 ≤ 3)
            keeps the clamp inactive, so selfStep = -0.1·0.5·r = -a·r, a = 0.05.
            r' = (1+a)r + leadStep ⇒ d'² ≥ ((1+a)d - L)².  A6 (0.5·R ≥ 2) with the IH
            d ≥ R gives 0.5·d ≥ 2, i.e. a·d ≥ L, so (1+a)d - L ≥ d ≥ R ⇒ d'² ≥ d² ≥ R².
            This is the MIRROR of KeepsFollowDistanceProgress's far-side argument —
            reuse `clamp_product` / `clamp_radial_progress` / `bounded_disturbance_progress`
            from KeepsFollowDistanceProgressRefinement/GuaranteesProof.lean.

    (Far)   N0 > max_dist_sq:  IG2 ⇒ next velocity = clamp(0.2·rel); each |selfStep_i|
            ≤ 0.1·3 = 0.3, and the L1 bound |selfStep| ≤ 3·0.3 with |leadStep| ≤ L and
            the band-width margin A8 (max_dist ≥ R + L + 3·M·timestep) give
            d' ≥ max_dist - L - 3·M·timestep ≥ R ⇒ d'² ≥ R².  (nlinarith over the six
            componentwise bounds; structurally like `bounded_disturbance_progress`.)

  Tie-off: the three zone lemmas combine to one-step preservation
  (true_dist_sq(n) ≥ R_sq → true_dist_sq(n+1) ≥ R_sq); feed base + step to
  `globally_induction`.  All arithmetic is over ℚ (no √), which is why R and the
  margins are stated in squared / L1 form.
-/
/-- Band-zone one-step bound: if the current true distance is ≥ min_dist (`Σaᵢ² ≥ 25`)
    and the leader step is bounded (`Σsᵢ² ≤ L²`), the next distance stays ≥ R.
    Tight — equality when the leader steps straight in and `|a| = min_dist` exactly.
    The `sq_nonneg (aᵢsⱼ - aⱼsᵢ)` hints feed Cauchy–Schwarz to `nlinarith`. -/
private lemma band_progress
    (ax ay az sx sy sz : ℚ)
    (ha : (5.0 * 5.0 : ℚ) ≤ ax * ax + ay * ay + az * az)
    (hs : sx * sx + sy * sy + sz * sz ≤ 2.0 * 0.1 * (2.0 * 0.1)) :
    (5.0 - 2.0 * 0.1) * (5.0 - 2.0 * 0.1) ≤
      (ax + sx) * (ax + sx) + (ay + sy) * (ay + sy) + (az + sz) * (az + sz) := by
  nlinarith [sq_nonneg (ax * sy - ay * sx), sq_nonneg (ax * sz - az * sx),
             sq_nonneg (ay * sz - az * sy), sq_nonneg (ax * sx + ay * sy + az * sz),
             ha, hs, sq_nonneg ax, sq_nonneg ay, sq_nonneg az, sq_nonneg sx, sq_nonneg sy, sq_nonneg sz,
             mul_nonneg (by linarith : (0:ℚ) ≤ ax*ax+ay*ay+az*az - 5.0*5.0)
                        (by linarith : (0:ℚ) ≤ 2.0*0.1*(2.0*0.1) - (sx*sx+sy*sy+sz*sz))]

/-- Inner-zone bound: the controller pulls inward with gain 0.05, so the relative
    vector scales by 1.05 before the leader disturbance.  Loose (result ≈ 4.84 ≥ R). -/
private lemma inner_progress
    (ax ay az sx sy sz : ℚ)
    (ha : (5.0 - 2.0 * 0.1) * (5.0 - 2.0 * 0.1) ≤ ax * ax + ay * ay + az * az)
    (hs : sx * sx + sy * sy + sz * sz ≤ 2.0 * 0.1 * (2.0 * 0.1)) :
    (5.0 - 2.0 * 0.1) * (5.0 - 2.0 * 0.1) ≤
      (1.05 * ax + sx) * (1.05 * ax + sx) + (1.05 * ay + sy) * (1.05 * ay + sy) +
        (1.05 * az + sz) * (1.05 * az + sz) := by
  nlinarith [sq_nonneg (ax * sy - ay * sx), sq_nonneg (ax * sz - az * sx),
             sq_nonneg (ay * sz - az * sy), sq_nonneg (ax * sx + ay * sy + az * sz),
             ha, hs, sq_nonneg ax, sq_nonneg ay, sq_nonneg az, sq_nonneg sx, sq_nonneg sy, sq_nonneg sz,
             mul_nonneg (by nlinarith : (0:ℚ) ≤ ax*ax+ay*ay+az*az - (5.0-2.0*0.1)*(5.0-2.0*0.1))
                        (by linarith : (0:ℚ) ≤ 2.0*0.1*(2.0*0.1) - (sx*sx+sy*sy+sz*sz))]

/-- Far-zone bound: distance > max_dist, controller pushes outward (velocity clamped
    to ±3, so self-displacement ≤ 0.3 per axis); leader step ≤ L.  Very loose margin. -/
private lemma far_progress
    (ax ay az lx ly lz cx cy cz : ℚ)
    (ha : (15.0 * 15.0 : ℚ) ≤ ax * ax + ay * ay + az * az)
    (hl : lx * lx + ly * ly + lz * lz ≤ 2.0 * 0.1 * (2.0 * 0.1))
    (hcx : -3.0 ≤ cx) (hcx' : cx ≤ 3.0) (hcy : -3.0 ≤ cy) (hcy' : cy ≤ 3.0)
    (hcz : -3.0 ≤ cz) (hcz' : cz ≤ 3.0) :
    (5.0 - 2.0 * 0.1) * (5.0 - 2.0 * 0.1) ≤
      (ax + lx - 0.1 * cx) * (ax + lx - 0.1 * cx) + (ay + ly - 0.1 * cy) * (ay + ly - 0.1 * cy) +
        (az + lz - 0.1 * cz) * (az + lz - 0.1 * cz) := by
  -- exact SOS-style decomposition: the disturbed distance splits into nonneg squares
  -- plus ½‖a‖² − 1.1‖l‖² − 0.11‖c‖², all of which are linearly bounded below.
  have expand :
      (ax + lx - 0.1 * cx) * (ax + lx - 0.1 * cx) + (ay + ly - 0.1 * cy) * (ay + ly - 0.1 * cy) +
        (az + lz - 0.1 * cz) * (az + lz - 0.1 * cz) =
      0.5 * ((ax + 2*(lx - 0.1*cx)) * (ax + 2*(lx - 0.1*cx)) +
             (ay + 2*(ly - 0.1*cy)) * (ay + 2*(ly - 0.1*cy)) +
             (az + 2*(lz - 0.1*cz)) * (az + 2*(lz - 0.1*cz))) +
      0.1 * ((lx + cx) * (lx + cx) + (ly + cy) * (ly + cy) + (lz + cz) * (lz + cz)) +
      0.5 * (ax*ax + ay*ay + az*az) - 1.1 * (lx*lx + ly*ly + lz*lz) -
      0.11 * (cx*cx + cy*cy + cz*cz) := by ring
  rw [expand]
  nlinarith [ha, hl, sq_nonneg (ax + 2*(lx - 0.1*cx)), sq_nonneg (ay + 2*(ly - 0.1*cy)),
             sq_nonneg (az + 2*(lz - 0.1*cz)), sq_nonneg (lx + cx), sq_nonneg (ly + cy),
             sq_nonneg (lz + cz),
             mul_nonneg (by linarith : (0:ℚ) ≤ 3 - cx) (by linarith : (0:ℚ) ≤ 3 + cx),
             mul_nonneg (by linarith : (0:ℚ) ≤ 3 - cy) (by linarith : (0:ℚ) ≤ 3 + cy),
             mul_nonneg (by linarith : (0:ℚ) ≤ 3 - cz) (by linarith : (0:ℚ) ≤ 3 + cz)]

-- Common step-goal shape for a zone lemma: given the invariant machinery at time `n`,
-- the true squared distance at `n+1` stays ≥ R².  Each zone is its own declaration so it
-- gets a fresh heartbeat budget and elaborates independently.

/-- Band zone: `min_dist_sq ≤ N0 ≤ max_dist_sq` ⟹ controller holds still (velocity 0). -/
private lemma band_zone (t : Trace TraceState) (n : ℕ) (h_n : ↑n < t.length)
    (h_1_n : ↑1 < (t.shift n h_n).length)
    (hIG0 : t ⊨ IG0) (hIG3 : t ⊨ IG3) (hIG4 : t ⊨ IG4) (hIG5 : t ⊨ IG5) (hIG6 : t ⊨ IG6)
    (hA9 : t ⊨ A9) (hA10 : t ⊨ A10) (hA11 : t ⊨ A11) (hA12 : t ⊨ A12)
    (hlo : 5.0 * 5.0 ≤ (t.toFun! n).N0) (hhi : (t.toFun! n).N0 ≤ 15.0 * 15.0) :
    (5.0 - 2.0 * 0.1) * (5.0 - 2.0 * 0.1) ≤
      ((t.toFun! (1 + n)).N4 - (t.toFun! (1 + n)).N7) * ((t.toFun! (1 + n)).N4 - (t.toFun! (1 + n)).N7) +
        ((t.toFun! (1 + n)).N5 - (t.toFun! (1 + n)).N8) * ((t.toFun! (1 + n)).N5 - (t.toFun! (1 + n)).N8) +
      ((t.toFun! (1 + n)).N6 - (t.toFun! (1 + n)).N9) * ((t.toFun! (1 + n)).N6 - (t.toFun! (1 + n)).N9) := by
  simp [push_ltl] at hIG0 hIG3 hIG4 hIG5 hIG6 hA9 hA10 hA11 hA12
  have htrue : ∀ (m : Nat), ↑m < t.length →
      (t.toFun! m).N0 =
        ((t.toFun! m).N4 - (t.toFun! m).N7) * ((t.toFun! m).N4 - (t.toFun! m).N7) +
          ((t.toFun! m).N5 - (t.toFun! m).N8) * ((t.toFun! m).N5 - (t.toFun! m).N8) +
        ((t.toFun! m).N6 - (t.toFun! m).N9) * ((t.toFun! m).N6 - (t.toFun! m).N9) := by
    intro m hm; rw [hIG6 m hm, hIG3 m hm, hIG4 m hm, hIG5 m hm]
  obtain ⟨⟨_, hvx⟩, ⟨_, hvy⟩, _, hvz⟩ := hIG0 n h_n hlo hhi
  obtain ⟨p7, ⟨_, hp7⟩, u7, ⟨_, hu7⟩, hst7⟩ := hA9 n h_n
  obtain ⟨p8, ⟨_, hp8⟩, u8, ⟨_, hu8⟩, hst8⟩ := hA10 n h_n
  obtain ⟨p9, ⟨_, hp9⟩, u9, ⟨_, hu9⟩, hst9⟩ := hA11 n h_n
  have hf7 : (t.toFun! (1 + n)).N7 = (t.toFun! n).N7 := by
    have hu : u7 = 0 := by rw [← hu7]; exact hvx
    rw [hp7, hst7, hu]; ring
  have hf8 : (t.toFun! (1 + n)).N8 = (t.toFun! n).N8 := by
    have hu : u8 = 0 := by rw [← hu8]; exact hvy
    rw [hp8, hst8, hu]; ring
  have hf9 : (t.toFun! (1 + n)).N9 = (t.toFun! n).N9 := by
    have hu : u9 = 0 := by rw [← hu9]; exact hvz
    rw [hp9, hst9, hu]; ring
  have ha : (5.0 * 5.0 : ℚ) ≤
      ((t.toFun! n).N4 - (t.toFun! n).N7) * ((t.toFun! n).N4 - (t.toFun! n).N7) +
      ((t.toFun! n).N5 - (t.toFun! n).N8) * ((t.toFun! n).N5 - (t.toFun! n).N8) +
      ((t.toFun! n).N6 - (t.toFun! n).N9) * ((t.toFun! n).N6 - (t.toFun! n).N9) := by
    rw [← htrue n h_n]; exact hlo
  have hLx : (LLTLV[𝐗 self.leadPos.x] : TraceFun TraceState ℚ) (t.shift n h_n)
      = some ((t.toFun! (1 + n)).N4) := by rw [TraceFun.shift_apply _ _ 1 h_1_n]; simp
  have hLy : (LLTLV[𝐗 self.leadPos.y] : TraceFun TraceState ℚ) (t.shift n h_n)
      = some ((t.toFun! (1 + n)).N5) := by rw [TraceFun.shift_apply _ _ 1 h_1_n]; simp
  have hLz : (LLTLV[𝐗 self.leadPos.z] : TraceFun TraceState ℚ) (t.shift n h_n)
      = some ((t.toFun! (1 + n)).N6) := by rw [TraceFun.shift_apply _ _ 1 h_1_n]; simp
  obtain ⟨Ld, hLeq, hLle⟩ := hA12 n h_n
  rw [hLx, hLy, hLz] at hLeq
  simp only [Option.some_bind, Option.some.injEq] at hLeq
  rw [hf7, hf8, hf9]
  have key := band_progress
    ((t.toFun! n).N4 - (t.toFun! n).N7) ((t.toFun! n).N5 - (t.toFun! n).N8)
    ((t.toFun! n).N6 - (t.toFun! n).N9)
    ((t.toFun! (1 + n)).N4 - (t.toFun! n).N4) ((t.toFun! (1 + n)).N5 - (t.toFun! n).N5)
    ((t.toFun! (1 + n)).N6 - (t.toFun! n).N6)
    ha (by nlinarith [hLeq, hLle])
  nlinarith [key]

/-- Inner zone: `N0 < min_dist_sq` ⟹ controller pulls inward, rel scales by 1.05. -/
private lemma inner_zone (t : Trace TraceState) (n : ℕ) (h_n : ↑n < t.length)
    (h_1_n : ↑1 < (t.shift n h_n).length)
    (hIG1 : t ⊨ IG1) (hIG3 : t ⊨ IG3) (hIG4 : t ⊨ IG4) (hIG5 : t ⊨ IG5) (hIG6 : t ⊨ IG6)
    (hA9 : t ⊨ A9) (hA10 : t ⊨ A10) (hA11 : t ⊨ A11) (hA12 : t ⊨ A12)
    (ih : (5.0 - 2.0 * 0.1) * (5.0 - 2.0 * 0.1) ≤
      ((t.toFun! n).N4 - (t.toFun! n).N7) * ((t.toFun! n).N4 - (t.toFun! n).N7) +
        ((t.toFun! n).N5 - (t.toFun! n).N8) * ((t.toFun! n).N5 - (t.toFun! n).N8) +
      ((t.toFun! n).N6 - (t.toFun! n).N9) * ((t.toFun! n).N6 - (t.toFun! n).N9))
    (hlo : (t.toFun! n).N0 < 5.0 * 5.0) :
    (5.0 - 2.0 * 0.1) * (5.0 - 2.0 * 0.1) ≤
      ((t.toFun! (1 + n)).N4 - (t.toFun! (1 + n)).N7) * ((t.toFun! (1 + n)).N4 - (t.toFun! (1 + n)).N7) +
        ((t.toFun! (1 + n)).N5 - (t.toFun! (1 + n)).N8) * ((t.toFun! (1 + n)).N5 - (t.toFun! (1 + n)).N8) +
      ((t.toFun! (1 + n)).N6 - (t.toFun! (1 + n)).N9) * ((t.toFun! (1 + n)).N6 - (t.toFun! (1 + n)).N9) := by
  simp [push_ltl] at hIG1 hIG3 hIG4 hIG5 hIG6 hA9 hA10 hA11 hA12
  obtain ⟨⟨_, hvx⟩, ⟨_, hvy⟩, _, hvz⟩ := hIG1 n h_n hlo
  obtain ⟨p7, ⟨_, hp7⟩, u7, ⟨_, hu7⟩, hst7⟩ := hA9 n h_n
  obtain ⟨p8, ⟨_, hp8⟩, u8, ⟨_, hu8⟩, hst8⟩ := hA10 n h_n
  obtain ⟨p9, ⟨_, hp9⟩, u9, ⟨_, hu9⟩, hst9⟩ := hA11 n h_n
  have e6 := hIG6 n h_n
  have hb1 : (t.toFun! n).N1 * (t.toFun! n).N1 < 25 := by
    nlinarith [hlo, e6, mul_self_nonneg (t.toFun! n).N2, mul_self_nonneg (t.toFun! n).N3]
  have hb2 : (t.toFun! n).N2 * (t.toFun! n).N2 < 25 := by
    nlinarith [hlo, e6, mul_self_nonneg (t.toFun! n).N1, mul_self_nonneg (t.toFun! n).N3]
  have hb3 : (t.toFun! n).N3 * (t.toFun! n).N3 < 25 := by
    nlinarith [hlo, e6, mul_self_nonneg (t.toFun! n).N1, mul_self_nonneg (t.toFun! n).N2]
  have hcx : (t.toFun! (1 + n)).N10 = -(0.5 * (t.toFun! n).N1) := by
    rw [hvx, sup_eq_left.mpr (by nlinarith [hb1] : (-3.0:ℚ) ≤ -(0.5 * (t.toFun! n).N1)),
        inf_eq_left.mpr (by nlinarith [hb1] : -(0.5 * (t.toFun! n).N1) ≤ (3.0:ℚ))]
  have hcy : (t.toFun! (1 + n)).N11 = -(0.5 * (t.toFun! n).N2) := by
    rw [hvy, sup_eq_left.mpr (by nlinarith [hb2] : (-3.0:ℚ) ≤ -(0.5 * (t.toFun! n).N2)),
        inf_eq_left.mpr (by nlinarith [hb2] : -(0.5 * (t.toFun! n).N2) ≤ (3.0:ℚ))]
  have hcz : (t.toFun! (1 + n)).N12 = -(0.5 * (t.toFun! n).N3) := by
    rw [hvz, sup_eq_left.mpr (by nlinarith [hb3] : (-3.0:ℚ) ≤ -(0.5 * (t.toFun! n).N3)),
        inf_eq_left.mpr (by nlinarith [hb3] : -(0.5 * (t.toFun! n).N3) ≤ (3.0:ℚ))]
  have hf7 : (t.toFun! (1 + n)).N7 = (t.toFun! n).N7 - 0.05 * (t.toFun! n).N1 := by
    rw [hp7, hst7, ← hu7, hcx]; ring
  have hf8 : (t.toFun! (1 + n)).N8 = (t.toFun! n).N8 - 0.05 * (t.toFun! n).N2 := by
    rw [hp8, hst8, ← hu8, hcy]; ring
  have hf9 : (t.toFun! (1 + n)).N9 = (t.toFun! n).N9 - 0.05 * (t.toFun! n).N3 := by
    rw [hp9, hst9, ← hu9, hcz]; ring
  have e1 := hIG3 n h_n
  have e2 := hIG4 n h_n
  have e3 := hIG5 n h_n
  have hLx : (LLTLV[𝐗 self.leadPos.x] : TraceFun TraceState ℚ) (t.shift n h_n)
      = some ((t.toFun! (1 + n)).N4) := by rw [TraceFun.shift_apply _ _ 1 h_1_n]; simp
  have hLy : (LLTLV[𝐗 self.leadPos.y] : TraceFun TraceState ℚ) (t.shift n h_n)
      = some ((t.toFun! (1 + n)).N5) := by rw [TraceFun.shift_apply _ _ 1 h_1_n]; simp
  have hLz : (LLTLV[𝐗 self.leadPos.z] : TraceFun TraceState ℚ) (t.shift n h_n)
      = some ((t.toFun! (1 + n)).N6) := by rw [TraceFun.shift_apply _ _ 1 h_1_n]; simp
  obtain ⟨Ld, hLeq, hLle⟩ := hA12 n h_n
  rw [hLx, hLy, hLz] at hLeq
  simp only [Option.some_bind, Option.some.injEq] at hLeq
  rw [hf7, hf8, hf9, e1, e2, e3]
  have key := inner_progress
    ((t.toFun! n).N4 - (t.toFun! n).N7) ((t.toFun! n).N5 - (t.toFun! n).N8)
    ((t.toFun! n).N6 - (t.toFun! n).N9)
    ((t.toFun! (1 + n)).N4 - (t.toFun! n).N4) ((t.toFun! (1 + n)).N5 - (t.toFun! n).N5)
    ((t.toFun! (1 + n)).N6 - (t.toFun! n).N6)
    ih (by nlinarith [hLeq, hLle])
  nlinarith [key]

/-- Far zone: `N0 > max_dist_sq` ⟹ controller pushes outward (clamped); huge margin. -/
private lemma far_zone (t : Trace TraceState) (n : ℕ) (h_n : ↑n < t.length)
    (h_1_n : ↑1 < (t.shift n h_n).length)
    (hIG2 : t ⊨ IG2) (hIG3 : t ⊨ IG3) (hIG4 : t ⊨ IG4) (hIG5 : t ⊨ IG5) (hIG6 : t ⊨ IG6)
    (hA9 : t ⊨ A9) (hA10 : t ⊨ A10) (hA11 : t ⊨ A11) (hA12 : t ⊨ A12)
    (hhi : 15.0 * 15.0 < (t.toFun! n).N0) :
    (5.0 - 2.0 * 0.1) * (5.0 - 2.0 * 0.1) ≤
      ((t.toFun! (1 + n)).N4 - (t.toFun! (1 + n)).N7) * ((t.toFun! (1 + n)).N4 - (t.toFun! (1 + n)).N7) +
        ((t.toFun! (1 + n)).N5 - (t.toFun! (1 + n)).N8) * ((t.toFun! (1 + n)).N5 - (t.toFun! (1 + n)).N8) +
      ((t.toFun! (1 + n)).N6 - (t.toFun! (1 + n)).N9) * ((t.toFun! (1 + n)).N6 - (t.toFun! (1 + n)).N9) := by
  simp [push_ltl] at hIG2 hIG3 hIG4 hIG5 hIG6 hA9 hA10 hA11 hA12
  have htrue : ∀ (m : Nat), ↑m < t.length →
      (t.toFun! m).N0 =
        ((t.toFun! m).N4 - (t.toFun! m).N7) * ((t.toFun! m).N4 - (t.toFun! m).N7) +
          ((t.toFun! m).N5 - (t.toFun! m).N8) * ((t.toFun! m).N5 - (t.toFun! m).N8) +
        ((t.toFun! m).N6 - (t.toFun! m).N9) * ((t.toFun! m).N6 - (t.toFun! m).N9) := by
    intro m hm; rw [hIG6 m hm, hIG3 m hm, hIG4 m hm, hIG5 m hm]
  obtain ⟨⟨_, hvx⟩, ⟨_, hvy⟩, _, hvz⟩ := hIG2 n h_n hhi
  obtain ⟨p7, ⟨_, hp7⟩, u7, ⟨_, hu7⟩, hst7⟩ := hA9 n h_n
  obtain ⟨p8, ⟨_, hp8⟩, u8, ⟨_, hu8⟩, hst8⟩ := hA10 n h_n
  obtain ⟨p9, ⟨_, hp9⟩, u9, ⟨_, hu9⟩, hst9⟩ := hA11 n h_n
  have hf7 : (t.toFun! (1 + n)).N7 = (t.toFun! n).N7 + 0.1 * (t.toFun! (1 + n)).N10 := by
    rw [hp7, hst7, ← hu7]
  have hf8 : (t.toFun! (1 + n)).N8 = (t.toFun! n).N8 + 0.1 * (t.toFun! (1 + n)).N11 := by
    rw [hp8, hst8, ← hu8]
  have hf9 : (t.toFun! (1 + n)).N9 = (t.toFun! n).N9 + 0.1 * (t.toFun! (1 + n)).N12 := by
    rw [hp9, hst9, ← hu9]
  have hcx_le : (t.toFun! (1 + n)).N10 ≤ 3.0 := by rw [hvx]; exact inf_le_right
  have hcx_ge : (-3.0:ℚ) ≤ (t.toFun! (1 + n)).N10 := by
    rw [hvx]; exact le_inf le_sup_right (by norm_num)
  have hcy_le : (t.toFun! (1 + n)).N11 ≤ 3.0 := by rw [hvy]; exact inf_le_right
  have hcy_ge : (-3.0:ℚ) ≤ (t.toFun! (1 + n)).N11 := by
    rw [hvy]; exact le_inf le_sup_right (by norm_num)
  have hcz_le : (t.toFun! (1 + n)).N12 ≤ 3.0 := by rw [hvz]; exact inf_le_right
  have hcz_ge : (-3.0:ℚ) ≤ (t.toFun! (1 + n)).N12 := by
    rw [hvz]; exact le_inf le_sup_right (by norm_num)
  have ha : (15.0 * 15.0 : ℚ) ≤
      ((t.toFun! n).N4 - (t.toFun! n).N7) * ((t.toFun! n).N4 - (t.toFun! n).N7) +
      ((t.toFun! n).N5 - (t.toFun! n).N8) * ((t.toFun! n).N5 - (t.toFun! n).N8) +
      ((t.toFun! n).N6 - (t.toFun! n).N9) * ((t.toFun! n).N6 - (t.toFun! n).N9) := by
    rw [← htrue n h_n]; linarith [hhi]
  have hLx : (LLTLV[𝐗 self.leadPos.x] : TraceFun TraceState ℚ) (t.shift n h_n)
      = some ((t.toFun! (1 + n)).N4) := by rw [TraceFun.shift_apply _ _ 1 h_1_n]; simp
  have hLy : (LLTLV[𝐗 self.leadPos.y] : TraceFun TraceState ℚ) (t.shift n h_n)
      = some ((t.toFun! (1 + n)).N5) := by rw [TraceFun.shift_apply _ _ 1 h_1_n]; simp
  have hLz : (LLTLV[𝐗 self.leadPos.z] : TraceFun TraceState ℚ) (t.shift n h_n)
      = some ((t.toFun! (1 + n)).N6) := by rw [TraceFun.shift_apply _ _ 1 h_1_n]; simp
  obtain ⟨Ld, hLeq, hLle⟩ := hA12 n h_n
  rw [hLx, hLy, hLz] at hLeq
  simp only [Option.some_bind, Option.some.injEq] at hLeq
  rw [hf7, hf8, hf9]
  have key := far_progress
    ((t.toFun! n).N4 - (t.toFun! n).N7) ((t.toFun! n).N5 - (t.toFun! n).N8)
    ((t.toFun! n).N6 - (t.toFun! n).N9)
    ((t.toFun! (1 + n)).N4 - (t.toFun! n).N4) ((t.toFun! (1 + n)).N5 - (t.toFun! n).N5)
    ((t.toFun! (1 + n)).N6 - (t.toFun! n).N6)
    ((t.toFun! (1 + n)).N10) ((t.toFun! (1 + n)).N11) ((t.toFun! (1 + n)).N12)
    ha (by nlinarith [hLeq, hLle]) hcx_ge hcx_le hcy_ge hcy_le hcz_ge hcz_le
  nlinarith [key]

theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t ⟨⟨_, _, _, _, _, _, _, _, _, hA9, hA10, hA11, hA12, hA13⟩,
           ⟨hIG0, hIG1, hIG2, hIG3, hIG4, hIG5, hIG6⟩⟩
  -- guarantees is `t ⊨ 𝐆 (true_dist_sq ≥ R_sq)`; induct with the goal still folded
  simp only [guarantees, G0]
  apply TraceSet.globally_induction t
  · -- base (n = 0): hA13
    simpa [push_ltl] using hA13
  · -- step: case-split N0 against [min_dist_sq, max_dist_sq]; dispatch to a zone lemma
    simp only [TraceSet.sat_globally_iff, TraceSet.sat_wshift_iff, TraceSet.sat_imp_iff]
    intro n h_n ih h_1_n
    simp [push_ltl] at ih ⊢
    rcases lt_or_le ((t.toFun! n).N0) (5.0 * 5.0) with hlo | hlo
    · exact inner_zone t n h_n h_1_n hIG1 hIG3 hIG4 hIG5 hIG6 hA9 hA10 hA11 hA12 ih hlo
    · rcases le_or_lt ((t.toFun! n).N0) (15.0 * 15.0) with hhi | hhi
      · exact band_zone t n h_n h_1_n hIG0 hIG3 hIG4 hIG5 hIG6 hA9 hA10 hA11 hA12 hlo hhi
      · exact far_zone t n h_n h_1_n hIG2 hIG3 hIG4 hIG5 hIG6 hA9 hA10 hA11 hA12 hhi
