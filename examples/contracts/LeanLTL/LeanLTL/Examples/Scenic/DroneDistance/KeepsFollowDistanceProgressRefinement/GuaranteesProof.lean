import LeanLTL.Examples.Scenic.DroneDistance.KeepsFollowDistanceProgressRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace KeepsFollowDistanceProgressRefinement

-- Keep a modest explicit budget because Scenic checks this through an instrumented REPL.
set_option maxHeartbeats 300000

private lemma clamp_product (x v : ℚ) (hv : v = (0.2 * x ⊔ (-3.0 : ℚ)) ⊓ 3.0) :
    v ^ 2 ≤ 9 ∧ 0 ≤ x * v ∧
      ((|x| ≤ 15 ∧ x * v = 0.2 * x ^ 2) ∨
       (15 ≤ |x| ∧ x * v = 3 * |x|)) := by
  by_cases hlo : 0.2 * x ≤ (-3.0 : ℚ)
  · have hv' : v = -3.0 := by
      rw [sup_eq_right.mpr hlo, inf_eq_left.mpr (by norm_num)] at hv
      exact hv
    rw [hv']
    have hx : x ≤ 0 := by nlinarith
    rw [abs_of_nonpos hx]
    constructor
    · norm_num
    constructor
    · nlinarith
    right
    constructor <;> nlinarith
  · by_cases hhi : 0.2 * x ≤ (3.0 : ℚ)
    · have hv' : v = 0.2 * x := by
        rw [sup_eq_left.mpr (by linarith), inf_eq_left.mpr hhi] at hv
        exact hv
      rw [hv']
      have hlower : 0 ≤ 3 + 0.2 * x := by nlinarith
      have hupper : 0 ≤ 3 - 0.2 * x := by nlinarith
      have hsq := mul_nonneg hlower hupper
      have habs : |x| ≤ 15 := (abs_le).2 (by constructor <;> nlinarith)
      constructor
      · nlinarith
      constructor
      · nlinarith [sq_nonneg x]
      left
      exact ⟨habs, by ring⟩
    · have hv' : v = 3.0 := by
        rw [sup_eq_left.mpr (by linarith), inf_eq_right.mpr (by linarith)] at hv
        exact hv
      rw [hv']
      have hx : 0 ≤ x := by nlinarith
      rw [abs_of_nonneg hx]
      constructor
      · norm_num
      constructor
      · nlinarith
      right
      constructor <;> nlinarith

private lemma clamp_radial_progress
    (x y z vx vy vz : ℚ)
    (hr : 15 ^ 2 < x ^ 2 + y ^ 2 + z ^ 2)
    (hvx : vx = (0.2 * x ⊔ (-3.0 : ℚ)) ⊓ 3.0)
    (hvy : vy = (0.2 * y ⊔ (-3.0 : ℚ)) ⊓ 3.0)
    (hvz : vz = (0.2 * z ⊔ (-3.0 : ℚ)) ⊓ 3.0) :
    0 ≤ x * vx + y * vy + z * vz ∧
    9 * (x ^ 2 + y ^ 2 + z ^ 2) ≤ (x * vx + y * vy + z * vz) ^ 2 ∧
    vx ^ 2 + vy ^ 2 + vz ^ 2 ≤ 27 := by
  obtain ⟨hvx9, hpx, hx⟩ := clamp_product x vx hvx
  obtain ⟨hvy9, hpy, hy⟩ := clamp_product y vy hvy
  obtain ⟨hvz9, hpz, hz⟩ := clamp_product z vz hvz
  have hrad : 0 ≤ (x ^ 2 + y ^ 2 + z ^ 2 - 225) * (x ^ 2 + y ^ 2 + z ^ 2) := by
    apply mul_nonneg
    · nlinarith
    · positivity
  have habxy := mul_nonneg (abs_nonneg x) (abs_nonneg y)
  have habxz := mul_nonneg (abs_nonneg x) (abs_nonneg z)
  have habyz := mul_nonneg (abs_nonneg y) (abs_nonneg z)
  constructor
  · linarith only [hpx, hpy, hpz]
  constructor
  · rcases hx with hx | hx
    · rcases hy with hy | hy
      · rcases hz with hz | hz
        · nlinarith only [hx.2, hy.2, hz.2, hrad]
        · have hm := mul_nonneg (by linarith only [hz.1] : 0 ≤ 1.2 * |z| - 9)
              (by positivity : 0 ≤ x ^ 2 + y ^ 2)
          rw [hx.2, hy.2, hz.2, ← sq_abs z]
          nlinarith only [hm, sq_nonneg (x ^ 2 + y ^ 2)]
      · rcases hz with hz | hz
        · have hm := mul_nonneg (by linarith only [hy.1] : 0 ≤ 1.2 * |y| - 9)
              (by positivity : 0 ≤ x ^ 2 + z ^ 2)
          rw [hx.2, hy.2, hz.2, ← sq_abs y]
          nlinarith only [hm, sq_nonneg (x ^ 2 + z ^ 2)]
        · have hm := mul_nonneg (by linarith only [hy.1, hz.1] : 0 ≤ 1.2 * (|y| + |z|) - 9)
              (sq_nonneg x)
          rw [hx.2, hy.2, hz.2, ← sq_abs y, ← sq_abs z]
          nlinarith only [hm, habyz, sq_nonneg (x ^ 2)]
    · rcases hy with hy | hy
      · rcases hz with hz | hz
        · have hm := mul_nonneg (by linarith only [hx.1] : 0 ≤ 1.2 * |x| - 9)
              (by positivity : 0 ≤ y ^ 2 + z ^ 2)
          rw [hx.2, hy.2, hz.2, ← sq_abs x]
          nlinarith only [hm, sq_nonneg (y ^ 2 + z ^ 2)]
        · have hm := mul_nonneg (by linarith only [hx.1, hz.1] : 0 ≤ 1.2 * (|x| + |z|) - 9)
              (sq_nonneg y)
          rw [hx.2, hy.2, hz.2, ← sq_abs x, ← sq_abs z]
          nlinarith only [hm, habxz, sq_nonneg (y ^ 2)]
      · rcases hz with hz | hz
        · have hm := mul_nonneg (by linarith only [hx.1, hy.1] : 0 ≤ 1.2 * (|x| + |y|) - 9)
              (sq_nonneg z)
          rw [hx.2, hy.2, hz.2, ← sq_abs x, ← sq_abs y]
          nlinarith only [hm, habxy, sq_nonneg (z ^ 2)]
        · rw [hx.2, hy.2, hz.2, ← sq_abs x, ← sq_abs y, ← sq_abs z]
          nlinarith only [habxy, habxz, habyz]
  · linarith only [hvx9, hvy9, hvz9]

private lemma bounded_disturbance_progress
    (r s v w d q : ℚ)
    (hr : 225 < r) (hs : 0 ≤ s) (hrs : 9 * r ≤ s ^ 2)
    (hv : v ≤ 27) (hw : w = r - 0.2 * s + 0.01 * v) (hw0 : 0 ≤ w)
    (hd : d ≤ 0.04) (hc : q ^ 2 ≤ d * w) :
    w + 2 * q + d ≤ r - 1.5 := by
  have hs45 : 45 < s := by
    by_contra hn
    have hm := mul_nonneg (by linarith : 0 ≤ 45 - s) (by linarith : 0 ≤ 45 + s)
    nlinarith
  have hq_upper : q ^ 2 ≤ 0.04 * (s ^ 2 / 9 - 0.2 * s + 0.27) := by
    have hdmul := mul_nonneg (by linarith : 0 ≤ 0.04 - d) hw0
    nlinarith [hc]
  by_contra hn
  have hqlo : 0.1 * s - 0.905 < q := by nlinarith
  have hbase : 0 < 0.1 * s - 0.905 := by linarith
  have hsqlo : (0.1 * s - 0.905) ^ 2 < q ^ 2 := by
    have hm := mul_pos (by linarith : 0 < q - (0.1 * s - 0.905))
      (by linarith : 0 < q + (0.1 * s - 0.905))
    nlinarith
  have hmono := mul_nonneg (by linarith : 0 ≤ s - 45)
    (by linarith : 0 ≤ s + 13)
  nlinarith [hq_upper, hsqlo, hmono]

theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t ⟨⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7⟩, ⟨hIG0, hIG1, hIG2, hIH3, hIG4, hIG5, hIG6⟩⟩
  simp [push_ltl] at *
  intro n hn hfar
  have hi3 := hIH3 n hn
  have hi4 := hIG4 n hn
  have hi5 := hIG5 n hn
  have hi6 := hIG6 n hn
  have hv := hIG2 n hn (by rw [hi6, hi3, hi4, hi5]; exact hfar)
  have hp4 := hA4 n hn
  have hp5 := hA5 n hn
  have hp6 := hA6 n hn
  have hl := hA7 n hn
  rcases hp4 with ⟨px, ⟨hlen, hpx⟩, vx, ⟨_, hvx⟩, hstepx⟩
  rcases hp5 with ⟨py, ⟨_, hpy⟩, vy, ⟨_, hvy⟩, hstepy⟩
  rcases hp6 with ⟨pz, ⟨_, hpz⟩, vz, ⟨_, hvz⟩, hstepz⟩
  rcases hv with ⟨⟨_, hvx'⟩, ⟨_, hvy'⟩, _, hvz'⟩
  subst px
  subst py
  subst pz
  subst vx
  subst vy
  subst vz
  simp [hlen] at hl ⊢
  clear hA0 hA1 hA2 hA3 hA4 hA5 hA6 hA7 hIG0 hIG1 hIG2 hIH3 hIG4 hIG5 hIG6 hi6
  have hrfar : 15 ^ 2 < (t.toFun! n).N1 ^ 2 + (t.toFun! n).N2 ^ 2 +
      (t.toFun! n).N3 ^ 2 := by
    rw [hi3, hi4, hi5]
    norm_num at hfar ⊢
    nlinarith [hfar]
  have hctrl :
      0 ≤ (t.toFun! n).N1 * (t.toFun! (1 + n)).N10 +
          (t.toFun! n).N2 * (t.toFun! (1 + n)).N11 +
          (t.toFun! n).N3 * (t.toFun! (1 + n)).N12 ∧
      9 * ((t.toFun! n).N1 ^ 2 + (t.toFun! n).N2 ^ 2 + (t.toFun! n).N3 ^ 2) ≤
        ((t.toFun! n).N1 * (t.toFun! (1 + n)).N10 +
          (t.toFun! n).N2 * (t.toFun! (1 + n)).N11 +
          (t.toFun! n).N3 * (t.toFun! (1 + n)).N12) ^ 2 ∧
      (t.toFun! (1 + n)).N10 ^ 2 + (t.toFun! (1 + n)).N11 ^ 2 +
          (t.toFun! (1 + n)).N12 ^ 2 ≤ 27 :=
    clamp_radial_progress _ _ _ _ _ _ hrfar hvx' hvy' hvz'
  let dx := (t.toFun! (1 + n)).N4 - (t.toFun! n).N4
  let dy := (t.toFun! (1 + n)).N5 - (t.toFun! n).N5
  let dz := (t.toFun! (1 + n)).N6 - (t.toFun! n).N6
  let wx := (t.toFun! n).N1 - 0.1 * (t.toFun! (1 + n)).N10
  let wy := (t.toFun! n).N2 - 0.1 * (t.toFun! (1 + n)).N11
  let wz := (t.toFun! n).N3 - 0.1 * (t.toFun! (1 + n)).N12
  have hc : (dx * wx + dy * wy + dz * wz) ^ 2 ≤
      (dx ^ 2 + dy ^ 2 + dz ^ 2) * (wx ^ 2 + wy ^ 2 + wz ^ 2) := by
    calc
      _ ≤ (dx * wx + dy * wy + dz * wz) ^ 2 +
          (dx * wy - dy * wx) ^ 2 + (dx * wz - dz * wx) ^ 2 +
          (dy * wz - dz * wy) ^ 2 := by
            linarith only [sq_nonneg (dx * wy - dy * wx),
              sq_nonneg (dx * wz - dz * wx), sq_nonneg (dy * wz - dz * wy)]
      _ = _ := by ring
  let r := (t.toFun! n).N1 ^ 2 + (t.toFun! n).N2 ^ 2 + (t.toFun! n).N3 ^ 2
  let s := (t.toFun! n).N1 * (t.toFun! (1 + n)).N10 +
    (t.toFun! n).N2 * (t.toFun! (1 + n)).N11 +
    (t.toFun! n).N3 * (t.toFun! (1 + n)).N12
  let v := (t.toFun! (1 + n)).N10 ^ 2 + (t.toFun! (1 + n)).N11 ^ 2 +
    (t.toFun! (1 + n)).N12 ^ 2
  let w := wx ^ 2 + wy ^ 2 + wz ^ 2
  let d := dx ^ 2 + dy ^ 2 + dz ^ 2
  let q := dx * wx + dy * wy + dz * wz
  rcases hctrl with ⟨hs, hrs, hvbound⟩
  have hr : 225 < r := by dsimp [r]; norm_num at hrfar ⊢; exact hrfar
  have hw : w = r - 0.2 * s + 0.01 * v := by
    dsimp [w, r, s, v, wx, wy, wz]
    ring
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hdbound : d ≤ 0.04 := by
    dsimp [d, dx, dy, dz]
    norm_num at hl ⊢
    simpa [pow_two] using hl
  have hc' : q ^ 2 ≤ d * w := hc
  have hpure := bounded_disturbance_progress r s v w d q hr hs hrs hvbound
    hw hw0 hdbound hc'
  dsimp [r, s, v, w, d, q, dx, dy, dz, wx, wy, wz] at hpure
  rw [hi3, hi4, hi5] at hpure
  rw [hstepx, hstepy, hstepz]
  norm_num [min_def]
  nlinarith only [hpure]
