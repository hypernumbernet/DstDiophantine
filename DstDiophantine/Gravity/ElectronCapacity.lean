import DstDiophantine.Gravity.ElectronSquare
import DstDiophantine.Gravity.Electroweak
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shell seat counts and one-center closures

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. Nothing here produces a Bohr spectrum, a
dissociation energy, or a value of `G`. The integers `2`, `8`, and `18` are
seat counts. They are not indices of equal-scale nodes, and the node radii
remain `Θ(1/n)`.

## What is proved

* Two electrons at opposite ends of a diameter about a nucleus of charge
  `Z ≥ 1` have no radial balance in the outer well. In the first repulsive
  shell there is exactly one. There the outward force is negative on the
  large-radius side of the root and positive on the small-radius side.
* At a fixed radius whose diameter lies where `γ < 0`, that separation is a
  strict maximum, and any energy that increases with separation therefore has
  a strict local maximum at the antipode.
* Eight electrons at the vertices of a cube about a nucleus of charge `Z ≥ 1`
  have exactly one radial balance in the first repulsive shell, and the
  outward force restores that radius.
* Monopole, dipole, and quadrupole modes number `1`, `3`, and `5`. Two chiral
  seats on each mode give `2`, `8`, and `18` through degrees `0`, `1`, and `2`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Matrix Finset

/-! ### Diameter balance -/

noncomputable def pairBalance (Z x : ℝ) : ℝ :=
  gammaSEqual x - (4 * Z) * gammaSEqual (x / 2)

noncomputable def pairRatio (x : ℝ) : ℝ :=
  gammaSEqual x / gammaSEqual (x / 2)

noncomputable def diameterOutward (Z x : ℝ) : ℝ :=
  -Z / gammaSEqual x + 1 / (4 * gammaSEqual (x / 2))

lemma continuous_pairBalance (Z : ℝ) : Continuous (pairBalance Z) := by
  unfold pairBalance
  exact continuous_gammaSEqual.sub
    (continuous_const.mul (continuous_gammaSEqual.comp (continuous_id.div_const 2)))

lemma pairBalance_eq_outward {Z x : ℝ}
    (hx : gammaSEqual x ≠ 0) (hh : gammaSEqual (x / 2) ≠ 0) :
    diameterOutward Z x =
      pairBalance Z x / (4 * gammaSEqual x * gammaSEqual (x / 2)) := by
  unfold diameterOutward pairBalance
  field_simp [hx, hh]
  ring

/-! ### Exponential bounds -/

lemma exp_tenth_bounds : (11 / 10 : ℝ) < exp (1 / 10) ∧ exp (1 / 10) < 111 / 100 := by
  refine exp_between (x := 1 / 10) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma exp_fifth_bounds : (122 / 100 : ℝ) < exp (1 / 5) ∧ exp (1 / 5) < 5 / 4 := by
  refine exp_between (x := 1 / 5) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma exp_third_bounds : (139 / 100 : ℝ) < exp (1 / 3) ∧ exp (1 / 3) < 141 / 100 := by
  refine exp_between (x := 1 / 3) (n := 10) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma exp_two_fifths_bounds : (149 / 100 : ℝ) < exp (2 / 5) ∧ exp (2 / 5) < 3 / 2 := by
  refine exp_between (x := 2 / 5) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma exp_two_thirds_bounds : (194 / 100 : ℝ) < exp (2 / 3) ∧ exp (2 / 3) < 196 / 100 := by
  refine exp_between (x := 2 / 3) (n := 10) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma exp_four_fifths_bounds : (222 / 100 : ℝ) < exp (4 / 5) ∧ exp (4 / 5) < 223 / 100 := by
  refine exp_between (x := 4 / 5) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma exp_one_gt_271 : (271 / 100 : ℝ) < exp 1 :=
  lt_trans (by norm_num) exp_one_gt_d9

lemma exp_two_eq_mul : exp 2 = exp 1 * exp 1 := by
  have h2 : (2 : ℝ) = 1 + 1 := by norm_num
  rw [h2, exp_add]

lemma exp_one_sq_bounds : (73 / 10 : ℝ) < exp 2 ∧ exp 2 < 74 / 10 := by
  rw [exp_two_eq_mul]
  constructor
  · nlinarith [exp_one_gt_d9, exp_pos 1]
  · nlinarith [exp_one_lt_d9, exp_pos 1]

lemma cosh_two_lt_five : cosh 2 < 5 := by
  rw [cosh_eq, exp_two_eq_mul]
  have he : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
  have he2 : exp 1 * exp 1 < 9 := by
    calc exp 1 * exp 1 < 3 * exp 1 := mul_lt_mul_of_pos_right he (exp_pos 1)
      _ < 3 * 3 := mul_lt_mul_of_pos_left he (by norm_num)
      _ = 9 := by norm_num
  have hneg : exp (-2) < 1 := by
    have hlt : exp (-2) < exp 0 := exp_lt_exp.mpr (by norm_num)
    rw [exp_zero] at hlt
    exact hlt
  linarith [he2, hneg, exp_pos 1, exp_pos (-2)]

lemma sinh_le_of_exp_le {x E : ℝ} (hE : exp x ≤ E) :
    sinh x ≤ (E - 1 / E) / 2 := by
  rw [sinh_eq]
  have hinv : 1 / E ≤ exp (-x) := by
    simpa [exp_neg] using one_div_le_one_div_of_le (exp_pos x) hE
  linarith [exp_pos x, exp_pos (-x)]

lemma cosh_ge_of_exp_bounds {x e0 E : ℝ} (he : e0 ≤ exp x) (hE : exp x ≤ E) :
    (e0 + 1 / E) / 2 ≤ cosh x := by
  rw [cosh_eq]
  have hinv : 1 / E ≤ exp (-x) := by
    simpa [exp_neg] using one_div_le_one_div_of_le (exp_pos x) hE
  linarith [exp_pos x, exp_pos (-x)]

/-! ### A rational point below the first node -/

lemma gammaSEqual_four_fifths_pos : 0 < gammaSEqual (4 / 5) := by
  have hlo : (222 / 100 : ℝ) < exp (4 / 5) := exp_four_fifths_bounds.1
  have hhi : exp (4 / 5) < 223 / 100 := exp_four_fifths_bounds.2
  have hDhi : cosHi (4 / 5) (4 / 5) - sinLo (4 / 5) (4 / 5) < 0 := by
    simp only [cosHi, sinLo]; norm_num
  have hSlo : 0 < cosLo (4 / 5) + sinLo (4 / 5) (4 / 5) := by
    simp only [cosLo, sinLo]; norm_num
  have hbounds := gamma_parts_bounds (x := 4 / 5)
      (E0 := 222 / 100) (E1 := 223 / 100)
      (dLo := cosLo (4 / 5) - sinHi (4 / 5))
      (dHi := cosHi (4 / 5) (4 / 5) - sinLo (4 / 5) (4 / 5))
      (sLo := cosLo (4 / 5) + sinLo (4 / 5) (4 / 5))
      (sHi := cosHi (4 / 5) (4 / 5) + sinHi (4 / 5))
      (by norm_num) hlo.le hhi.le
      ?_ ?_ hDhi ?_ ?_ hSlo
  · have hgl : 0 < gammaLower (223 / 100)
        (cosLo (4 / 5) - sinHi (4 / 5))
        (cosLo (4 / 5) + sinLo (4 / 5) (4 / 5)) := by
      simp only [gammaLower, cosLo, sinHi, sinLo]; norm_num
    linarith [hbounds.1]
  · have hsin := sin_mem_bounds (a := 4 / 5) (b := 4 / 5)
        (by norm_num) (by norm_num) le_rfl le_rfl
    have hcos := cos_mem_bounds (a := 4 / 5) (b := 4 / 5)
        (by norm_num) (by norm_num) le_rfl le_rfl
    linarith [hsin.2, hcos.1]
  · have hsin := sin_mem_bounds (a := 4 / 5) (b := 4 / 5)
        (by norm_num) (by norm_num) le_rfl le_rfl
    have hcos := cos_mem_bounds (a := 4 / 5) (b := 4 / 5)
        (by norm_num) (by norm_num) le_rfl le_rfl
    linarith [hsin.1, hcos.2]
  · have hsin := sin_mem_bounds (a := 4 / 5) (b := 4 / 5)
        (by norm_num) (by norm_num) le_rfl le_rfl
    have hcos := cos_mem_bounds (a := 4 / 5) (b := 4 / 5)
        (by norm_num) (by norm_num) le_rfl le_rfl
    linarith [hsin.1, hcos.1]
  · have hsin := sin_mem_bounds (a := 4 / 5) (b := 4 / 5)
        (by norm_num) (by norm_num) le_rfl le_rfl
    have hcos := cos_mem_bounds (a := 4 / 5) (b := 4 / 5)
        (by norm_num) (by norm_num) le_rfl le_rfl
    linarith [hsin.2, hcos.2]

theorem four_fifths_lt_resonanceRoot1 : 4 / 5 < resonanceRoot1 := by
  by_contra h
  have hle : resonanceRoot1 ≤ 4 / 5 := le_of_not_gt h
  have hmem : (4 / 5 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, by linarith [pi_gt_three]⟩
  have hroot : resonanceRoot1 ∈ Icc (0 : ℝ) π :=
    ⟨le_of_lt (lt_trans (by norm_num) resonanceRoot1_bounds.1), by linarith [hle, pi_gt_three]⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hgt := strictAntiOn_gammaSEqual_even 0 (by simpa using hroot) (by simpa using hmem) hlt
    rw [resonanceRoot1_gammaSEqual_zero] at hgt
    exact lt_irrefl _ (hgt.trans gammaSEqual_four_fifths_pos)
  · have hzero : gammaSEqual (4 / 5) = 0 := by
      simpa [heq] using resonanceRoot1_gammaSEqual_zero
    linarith [gammaSEqual_four_fifths_pos, hzero]

lemma gammaSEqual_eight_fifths_lt : gammaSEqual (8 / 5) < -1 := by
  have hεlo : (292 / 10000 : ℝ) ≤ 8 / 5 - π / 2 := by
    linarith [pi_lt_d6]
  have hεhi : 8 / 5 - π / 2 ≤ 293 / 10000 := by
    linarith [pi_gt_d6]
  have hexp_lo : (492 / 100 : ℝ) < exp (8 / 5) := by
    have hid : exp (8 / 5) = exp (4 / 5) * exp (4 / 5) := by
      rw [show (8 / 5 : ℝ) = 4 / 5 + 4 / 5 by norm_num, exp_add]
    nlinarith [exp_four_fifths_bounds.1, exp_pos (4 / 5)]
  have hexp_hi : exp (8 / 5) < 498 / 100 := by
    have hid : exp (8 / 5) = exp (4 / 5) * exp (4 / 5) := by
      rw [show (8 / 5 : ℝ) = 4 / 5 + 4 / 5 by norm_num, exp_add]
    nlinarith [exp_four_fifths_bounds.2, exp_pos (4 / 5)]
  have hD : -(sinLo (292 / 10000) (293 / 10000) + cosLo (293 / 10000)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (293 / 10000) + cosLo (293 / 10000) := by
    simp only [sinHi, cosLo]; norm_num
  have hbounds := gamma_after (x := 8 / 5) (ε := 8 / 5 - π / 2)
      (a := 292 / 10000) (b := 293 / 10000)
      (E0 := 492 / 100) (E1 := 498 / 100)
      (by ring) (by norm_num) (by norm_num) hεlo hεhi
      (by norm_num) hexp_lo.le hexp_hi.le hD hS
  have hgu : gammaUpper (492 / 100)
      (-(sinLo (292 / 10000) (293 / 10000) + cosLo (293 / 10000)))
      (-sinLo (292 / 10000) (293 / 10000) +
        cosHi (292 / 10000) (293 / 10000)) < -1 := by
    simp only [gammaUpper, sinLo, cosLo, cosHi]; norm_num
  linarith [hbounds.2]

theorem gammaSEqual_neg_first_shell {x : ℝ}
    (hx : x ∈ Ioo resonanceRoot1 (branchNode 1)) : gammaSEqual x < 0 := by
  rcases le_or_gt x π with hle | hgt
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · have hπ : gammaSEqual π = -cosh π := by
        simpa [Nat.cast_one, one_mul] using gammaSEqual_nat_mul_pi 1
      linarith [cosh_pos π]
    · exact gammaSEqual_neg_right_of_first_node ⟨hx.1, hlt⟩
  · have hnode := (branchNode_spec 1).1
    have hzero : gammaSEqual (branchNode 1) = 0 := (branchNode_spec 1).2
    have hup : branchNode 1 < π + π := by
      simpa [Nat.cast_one, one_mul] using hnode.2
    have hlo : π < branchNode 1 := by
      simpa [Nat.cast_one, one_mul] using hnode.1
    have hxI : x ∈ Icc π (π + π) := ⟨hgt.le, le_of_lt (lt_trans hx.2 hup)⟩
    have hnI : branchNode 1 ∈ Icc π (π + π) := ⟨hlo.le, hup.le⟩
    have hlt := strictMonoOn_gammaSEqual_odd 0 (by simpa using hxI) (by simpa using hnI) hx.2
    rwa [hzero] at hlt

theorem pairBalance_neg_outer {Z x : ℝ} (hZ : 1 ≤ Z) (hx : x ∈ Ioo 0 resonanceRoot1) :
    pairBalance Z x < 0 := by
  have hx0 : 0 ≤ x / 2 := by linarith [hx.1]
  have hhalf : x / 2 < x := by linarith [hx.1]
  have hxπ : x < π := lt_trans hx.2 (lt_trans resonanceRoot1_sharp_bounds.2
    (by linarith [pi_gt_three]))
  have hmemx : x ∈ Icc (0 : ℝ) π := ⟨hx.1.le, hxπ.le⟩
  have hmemh : x / 2 ∈ Icc (0 : ℝ) π := ⟨hx0, le_trans hhalf.le hxπ.le⟩
  have hγ : gammaSEqual x < gammaSEqual (x / 2) :=
    strictAntiOn_gammaSEqual_even 0 (by simpa using hmemh) (by simpa using hmemx) hhalf
  have hpos : 0 < gammaSEqual (x / 2) :=
    gammaSEqual_pos_of_lt_firstNode hx0 (lt_trans hhalf hx.2)
  have hxpos : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  unfold pairBalance
  nlinarith [hγ, hpos, hxpos]

lemma shellNumerator_identity (t : ℝ) :
    gammaSEqual (2 * t) * cosh t - 4 * cosh (2 * t) * cos t * gammaSEqual t =
      2 * sinh t ^ 3 * sin (2 * t) -
        cosh t * cosh (2 * t) * (2 + cos (2 * t)) := by
  unfold gammaSEqual
  rw [sin_two_mul, cos_two_mul, sinh_two_mul, cosh_two_mul]
  ring_nf

lemma sin_le_of_right_interval {u v : ℝ} (hu : π / 2 ≤ u) (hv : v ≤ π) (huv : u ≤ v) :
    sin v ≤ sin u := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · rfl
  · have hanti : StrictAntiOn sin (Icc (π / 2) π) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_sin.continuousOn ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [show deriv sin x = cos x from congrFun Real.deriv_sin x]
      exact cos_neg_of_pi_div_two_lt_of_lt hx.1 (lt_trans hx.2 (by linarith [pi_pos]))
    exact (hanti ⟨hu, le_trans huv hv⟩ ⟨le_trans hu huv, hv⟩ hlt).le

lemma cos_le_of_zero_pi {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ π) (huv : u ≤ v) :
    cos v ≤ cos u := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · rfl
  · have hanti : StrictAntiOn cos (Icc 0 π) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_cos.continuousOn ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [show deriv cos x = -sin x from (Real.hasDerivAt_cos x).deriv]
      have hsin : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
      linarith
    exact (hanti ⟨hu, le_trans huv hv⟩ ⟨le_trans hu huv, hv⟩ hlt).le

lemma numerator_neg_of_bounds {t a b SB S2 C C2 Cos : ℝ}
    (ht : a ≤ t ∧ t ≤ b) (ha : 0 ≤ a) (h2a : π / 2 ≤ 2 * a) (h2b : 2 * b ≤ π)
    (hSB : sinh b ≤ SB) (hSB0 : 0 ≤ SB) (hS2 : sin (2 * a) ≤ S2)
    (hC : C ≤ cosh a) (hC2 : C2 ≤ cosh (2 * a)) (hC20 : 0 < C2)
    (hCos : Cos ≤ cos (2 * b)) (hsum : 0 < 2 + Cos)
    (hineq : 2 * SB ^ 3 * S2 < C * C2 * (2 + Cos)) :
    2 * sinh t ^ 3 * sin (2 * t) < cosh t * cosh (2 * t) * (2 + cos (2 * t)) := by
  have ht0 : 0 ≤ t := le_trans ha ht.1
  have h2t_lo : π / 2 ≤ 2 * t := by linarith
  have h2t_hi : 2 * t ≤ π := by linarith
  have hsinh : sinh t ≤ SB := le_trans ((sinh_le_sinh).mpr ht.2) hSB
  have hsinh0 : 0 ≤ sinh t := (sinh_nonneg_iff).mpr ht0
  have hsin_a : sin (2 * t) ≤ sin (2 * a) :=
    sin_le_of_right_interval h2a h2t_hi (by linarith)
  have hsin : sin (2 * t) ≤ S2 := le_trans hsin_a hS2
  have hsin0 : 0 ≤ sin (2 * t) := sin_nonneg_of_nonneg_of_le_pi (by linarith) h2t_hi
  have hpow : sinh t ^ 3 ≤ SB ^ 3 := pow_le_pow_left₀ hsinh0 hsinh 3
  have hprod : sinh t ^ 3 * sin (2 * t) ≤ SB ^ 3 * S2 :=
    mul_le_mul hpow hsin hsin0 (by positivity)
  have hL : 2 * sinh t ^ 3 * sin (2 * t) ≤ 2 * SB ^ 3 * S2 := by linarith
  have hcosh : C ≤ cosh t := le_trans hC ((cosh_le_cosh).mpr (by
    simpa [abs_of_nonneg ha, abs_of_nonneg ht0] using ht.1))
  have h2a0 : 0 ≤ 2 * a := by linarith
  have h2t0 : 0 ≤ 2 * t := by linarith
  have hcosh2 : C2 ≤ cosh (2 * t) := le_trans hC2 ((cosh_le_cosh).mpr (by
    simpa [abs_of_nonneg h2a0, abs_of_nonneg h2t0] using (by linarith : 2 * a ≤ 2 * t)))
  have hcos : 2 + Cos ≤ 2 + cos (2 * t) := by
    have hle : cos (2 * b) ≤ cos (2 * t) :=
      cos_le_of_zero_pi (by linarith) h2b (by linarith)
    linarith
  have hR : C * C2 * (2 + Cos) ≤ cosh t * cosh (2 * t) * (2 + cos (2 * t)) := by
    have hc1 : 0 ≤ cosh t := (cosh_pos t).le
    have hc2 : 0 ≤ cosh (2 * t) := (cosh_pos (2 * t)).le
    have hmul : C * C2 ≤ cosh t * cosh (2 * t) := mul_le_mul hcosh hcosh2 hC20.le hc1
    exact mul_le_mul hmul hcos hsum.le (mul_nonneg hc1 hc2)
  linarith

lemma sin_two_four_fifths_le : sin (8 / 5) ≤ 21 / 20 := by
  have hsin := sin_mem_bounds (a := 4 / 5) (b := 4 / 5) (by norm_num) (by norm_num) le_rfl le_rfl
  have hcos := cos_mem_bounds (a := 4 / 5) (b := 4 / 5) (by norm_num) (by norm_num) le_rfl le_rfl
  have hs : 0 ≤ sin (4 / 5) :=
    sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [pi_gt_three])
  have hc : 0 ≤ cos (4 / 5) := by
    have : (4 / 5 : ℝ) < π / 2 := by linarith [pi_gt_three]
    exact (cos_pos_of_mem_Ioo ⟨by linarith, this⟩).le
  rw [show (8 / 5 : ℝ) = 2 * (4 / 5) by norm_num, sin_two_mul]
  have hhi : 0 ≤ sinHi (4 / 5) := by simp only [sinHi]; norm_num
  have hprod : sin (4 / 5) * cos (4 / 5) ≤ sinHi (4 / 5) * cosHi (4 / 5) (4 / 5) :=
    mul_le_mul hsin.2 hcos.2 hc hhi
  have hnum : 2 * (sinHi (4 / 5) * cosHi (4 / 5) (4 / 5)) ≤ 21 / 20 := by
    simp only [sinHi, cosHi]; norm_num
  linarith

lemma cos_two_ge : -1 / 2 ≤ cos 2 := by
  have hsin := (sin_mem_bounds (a := 1) (b := 1) (by norm_num) (by norm_num) le_rfl le_rfl).2
  have hs : 0 ≤ sin 1 := sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [pi_gt_three])
  have hform : cos 2 = 1 - 2 * sin 1 ^ 2 := by
    have htwo : (2 : ℝ) = 2 * 1 := by norm_num
    rw [htwo, cos_two_mul]
    have hpyth : cos 1 ^ 2 + sin 1 ^ 2 = 1 := cos_sq_add_sin_sq 1
    nlinarith [hpyth]
  have hsq : sin 1 ^ 2 ≤ sinHi 1 ^ 2 := by
    have hhi : 0 ≤ sinHi 1 := by simp only [sinHi]; norm_num
    exact pow_le_pow_left₀ hs hsin 2
  have hnum : -1 / 2 ≤ 1 - 2 * sinHi 1 ^ 2 := by
    simp only [sinHi]; norm_num
  linarith

set_option maxHeartbeats 4000000 in
-- The six chord bounds call `norm_num` on products of four-digit rationals.
lemma shell_numerator_neg {t : ℝ} (ht : t ∈ Icc (4 / 5) (π / 2)) :
    2 * sinh t ^ 3 * sin (2 * t) < cosh t * cosh (2 * t) * (2 + cos (2 * t)) := by
  have hpi : π / 2 < 8 / 5 := by linarith [pi_lt_d6]
  rcases le_or_gt t 1 with hle | hgt
  · have h2a : π / 2 ≤ 2 * (4 / 5) := by
      have : (2 : ℝ) * (4 / 5) = 8 / 5 := by norm_num
      linarith
    have hsinh1 : sinh 1 ≤ 6 / 5 := by
      have hE : exp 1 ≤ 272 / 100 := (lt_trans exp_one_lt_d9 (by norm_num)).le
      have hsinh := sinh_le_of_exp_le hE
      have hnum : (272 / 100 - 1 / (272 / 100)) / 2 ≤ 6 / 5 := by norm_num
      linarith
    have hcoshA : 5 / 4 ≤ cosh (4 / 5) := by
      have hcosh := cosh_ge_of_exp_bounds exp_four_fifths_bounds.1.le exp_four_fifths_bounds.2.le
      have hnum : 5 / 4 ≤ (222 / 100 + 1 / (223 / 100)) / 2 := by norm_num
      linarith
    have hcosh2 : 12 / 5 ≤ cosh (8 / 5) := by
      have hexp_lo : (492 / 100 : ℝ) ≤ exp (8 / 5) := by
        have hid : exp (8 / 5) = exp (4 / 5) * exp (4 / 5) := by
          rw [show (8 / 5 : ℝ) = 4 / 5 + 4 / 5 by norm_num, exp_add]
        nlinarith [exp_four_fifths_bounds.1, exp_pos (4 / 5)]
      have hexp_hi : exp (8 / 5) ≤ 498 / 100 := by
        have hid : exp (8 / 5) = exp (4 / 5) * exp (4 / 5) := by
          rw [show (8 / 5 : ℝ) = 4 / 5 + 4 / 5 by norm_num, exp_add]
        nlinarith [exp_four_fifths_bounds.2, exp_pos (4 / 5)]
      have hcosh := cosh_ge_of_exp_bounds hexp_lo hexp_hi
      have hnum : 12 / 5 ≤ (492 / 100 + 1 / (498 / 100)) / 2 := by norm_num
      linarith
    exact numerator_neg_of_bounds (a := 4 / 5) (b := 1) (SB := 6 / 5) (S2 := 21 / 20)
      (C := 5 / 4) (C2 := 12 / 5) (Cos := -1 / 2)
      ⟨ht.1, hle⟩ (by norm_num) h2a (by linarith [pi_gt_three])
      hsinh1 (by norm_num)
      (by
        have : (2 : ℝ) * (4 / 5) = 8 / 5 := by norm_num
        simpa [this] using sin_two_four_fifths_le)
      hcoshA
      (by
        have : (2 : ℝ) * (4 / 5) = 8 / 5 := by norm_num
        simpa [this] using hcosh2)
      (by norm_num)
      (by
        have : (2 : ℝ) * 1 = 2 := by norm_num
        simpa [this] using cos_two_ge)
      (by norm_num) (by norm_num)
  · rcases le_or_gt t (11 / 10) with hle2 | hgt2
    · have h2a : π / 2 ≤ 2 * 1 := by linarith [pi_gt_three]
      have hsinhB : sinh (11 / 10) ≤ 7 / 5 := by
        have hE : exp (11 / 10) ≤ 272 / 100 * (111 / 100) := by
          have hid : exp (11 / 10) = exp 1 * exp (1 / 10) := by
            rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, exp_add]
          nlinarith [exp_one_lt_d9, exp_tenth_bounds.2, exp_pos 1, exp_pos (1 / 10)]
        have hsinh := sinh_le_of_exp_le hE
        have hnum : ((272 / 100 * (111 / 100)) - 1 / (272 / 100 * (111 / 100))) / 2 ≤ 7 / 5 := by
          norm_num
        linarith
      have hsin2 : sin (2 * 1) ≤ 1 := by
        have hsin := sin_mem_bounds (a := 1) (b := 1) (by norm_num) (by norm_num) le_rfl le_rfl
        have hcos := cos_mem_bounds (a := 1) (b := 1) (by norm_num) (by norm_num) le_rfl le_rfl
        have hs : 0 ≤ sin 1 := sin_nonneg_of_nonneg_of_le_pi (by norm_num)
          (by linarith [pi_gt_three])
        have hc : 0 ≤ cos 1 := by
          have : (1 : ℝ) < π / 2 := by linarith [pi_gt_three]
          exact (cos_pos_of_mem_Ioo ⟨by linarith, this⟩).le
        have hhi : 0 ≤ sinHi 1 := by simp only [sinHi]; norm_num
        rw [sin_two_mul]
        have hprod : sin 1 * cos 1 ≤ sinHi 1 * cosHi 1 1 := mul_le_mul hsin.2 hcos.2 hc hhi
        have hnum : 2 * (sinHi 1 * cosHi 1 1) ≤ 1 := by simp only [sinHi, cosHi]; norm_num
        linarith
      have hcoshA : 3 / 2 ≤ cosh 1 := by
        have hlo : (27 / 10 : ℝ) ≤ exp 1 := le_trans (by norm_num) exp_one_gt_d9.le
        have hhi : exp 1 ≤ 272 / 100 := (lt_trans exp_one_lt_d9 (by norm_num)).le
        have hcosh := cosh_ge_of_exp_bounds hlo hhi
        have hnum : 3 / 2 ≤ (27 / 10 + 1 / (272 / 100)) / 2 := by norm_num
        linarith
      have hcosh2 : 7 / 2 ≤ cosh (2 * 1) := by
        have hlo : (73 / 10 : ℝ) ≤ exp 2 := exp_one_sq_bounds.1.le
        have hhi : exp 2 ≤ 74 / 10 := exp_one_sq_bounds.2.le
        have hcosh := cosh_ge_of_exp_bounds hlo hhi
        have hnum : (7 / 2 : ℝ) ≤ ((73 : ℝ) / 10 + 1 / ((74 : ℝ) / 10)) / 2 := by norm_num
        have : (2 : ℝ) * 1 = 2 := by norm_num
        simpa [this] using (le_trans hnum hcosh)
      have hcos : -3 / 5 ≤ cos (2 * (11 / 10)) := by
        have hεlo : (470 / 1000 : ℝ) ≤ π / 2 - 11 / 10 := by linarith [pi_gt_d6]
        have hεhi : π / 2 - 11 / 10 ≤ 471 / 1000 := by linarith [pi_lt_d6]
        have hcosb := cos_mem_bounds (a := 470 / 1000) (b := 471 / 1000)
          (by norm_num) (by norm_num) hεlo hεhi
        have hsin : sin (11 / 10) = cos (π / 2 - 11 / 10) := by
          rw [←sin_pi_div_two_sub, sub_sub_cancel]
        have hs0 : 0 ≤ sin (11 / 10) :=
          sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [pi_gt_three])
        have hhi : 0 ≤ cosHi (470 / 1000) (471 / 1000) := by simp only [cosHi]; norm_num
        have hle : sin (11 / 10) ≤ cosHi (470 / 1000) (471 / 1000) := by
          rw [hsin]; exact hcosb.2
        have hsq : sin (11 / 10) ^ 2 ≤ cosHi (470 / 1000) (471 / 1000) ^ 2 :=
          pow_le_pow_left₀ hs0 hle 2
        have hform : cos (2 * (11 / 10)) = 1 - 2 * sin (11 / 10) ^ 2 := by
          rw [cos_two_mul]
          have hpyth : cos (11 / 10) ^ 2 + sin (11 / 10) ^ 2 = 1 := cos_sq_add_sin_sq _
          nlinarith [hpyth]
        have hnum : -3 / 5 ≤ 1 - 2 * cosHi (470 / 1000) (471 / 1000) ^ 2 := by
          simp only [cosHi]; norm_num
        linarith
      exact numerator_neg_of_bounds (a := 1) (b := 11 / 10) (SB := 7 / 5) (S2 := 1)
        (C := 3 / 2) (C2 := 7 / 2) (Cos := -3 / 5)
        ⟨le_of_lt hgt, hle2⟩ (by norm_num) h2a (by linarith [pi_gt_three])
        hsinhB (by norm_num) hsin2 hcoshA hcosh2 (by norm_num) hcos (by norm_num) (by norm_num)
    · have htop : t ≤ π / 2 := ht.2
      rcases le_or_gt t (6 / 5) with hle3 | hgt3
      · have hsinhB : sinh (6 / 5) ≤ 8 / 5 := by
          have hE : exp (6 / 5) ≤ 272 / 100 * (5 / 4) := by
            have hid : exp (6 / 5) = exp 1 * exp (1 / 5) := by
              rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, exp_add]
            nlinarith [exp_one_lt_d9, exp_fifth_bounds.2, exp_pos 1, exp_pos (1 / 5)]
          have hsinh := sinh_le_of_exp_le hE
          have hnum : ((272 / 100 * (5 / 4)) - 1 / (272 / 100 * (5 / 4))) / 2 ≤ 8 / 5 := by
            norm_num
          linarith
        have hsin2 : sin (2 * (11 / 10)) ≤ 9 / 10 := by
          have heq : sin (2 * (11 / 10)) = sin (π - 2 * (11 / 10)) := by rw [sin_pi_sub]
          have hδhi : π - 2 * (11 / 10) ≤ 95 / 100 := by
            have : (2 : ℝ) * (11 / 10) = 11 / 5 := by norm_num
            linarith [pi_lt_d6]
          have hδlo : (0 : ℝ) ≤ π - 2 * (11 / 10) := by
            have : (2 : ℝ) * (11 / 10) = 11 / 5 := by norm_num
            linarith [pi_gt_three]
          have hmem := sin_mem_bounds (x := π - 2 * (11 / 10)) (a := 0) (b := 95 / 100)
            (by norm_num) (by norm_num) hδlo hδhi
          have hnum : sinHi (95 / 100) ≤ 9 / 10 := by simp only [sinHi]; norm_num
          rw [heq]
          linarith
        have hcoshA : 8 / 5 ≤ cosh (11 / 10) := by
          have hlo : (27 / 10 : ℝ) * (11 / 10) ≤ exp (11 / 10) := by
            have hid : exp (11 / 10) = exp 1 * exp (1 / 10) := by
              rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, exp_add]
            nlinarith [exp_one_gt_d9, exp_tenth_bounds.1, exp_pos 1, exp_pos (1 / 10)]
          have hhi : exp (11 / 10) ≤ 272 / 100 * (111 / 100) := by
            have hid : exp (11 / 10) = exp 1 * exp (1 / 10) := by
              rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, exp_add]
            nlinarith [exp_one_lt_d9, exp_tenth_bounds.2, exp_pos 1, exp_pos (1 / 10)]
          have hcosh := cosh_ge_of_exp_bounds hlo hhi
          have hnum : 8 / 5 ≤ ((27 / 10 * (11 / 10)) + 1 / (272 / 100 * (111 / 100))) / 2 := by
            norm_num
          linarith
        have hcosh2 : 4 ≤ cosh (2 * (11 / 10)) := by
          have hlo : ((27 / 10 : ℝ) * (11 / 10)) ^ 2 ≤ exp (11 / 5) := by
            have hid : exp (11 / 5) = exp (11 / 10) * exp (11 / 10) := by
              rw [show (11 / 5 : ℝ) = 11 / 10 + 11 / 10 by norm_num, exp_add]
            have h11 : (27 / 10 : ℝ) * (11 / 10) ≤ exp (11 / 10) := by
              have hid' : exp (11 / 10) = exp 1 * exp (1 / 10) := by
                rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, exp_add]
              nlinarith [exp_one_gt_d9, exp_tenth_bounds.1, exp_pos 1, exp_pos (1 / 10)]
            nlinarith [h11, exp_pos (11 / 10)]
          have hhi : exp (11 / 5) ≤ (272 / 100 * (111 / 100)) ^ 2 := by
            have hid : exp (11 / 5) = exp (11 / 10) * exp (11 / 10) := by
              rw [show (11 / 5 : ℝ) = 11 / 10 + 11 / 10 by norm_num, exp_add]
            have h11 : exp (11 / 10) ≤ 272 / 100 * (111 / 100) := by
              have hid' : exp (11 / 10) = exp 1 * exp (1 / 10) := by
                rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, exp_add]
              nlinarith [exp_one_lt_d9, exp_tenth_bounds.2, exp_pos 1, exp_pos (1 / 10)]
            nlinarith [h11, exp_pos (11 / 10)]
          have hcosh := cosh_ge_of_exp_bounds hlo hhi
          have hnum : (4 : ℝ) ≤
              (((27 / 10 * (11 / 10)) ^ 2 + 1 / (272 / 100 * (111 / 100)) ^ 2) / 2) := by
            norm_num
          have htarget : 4 ≤ cosh (11 / 5) := by linarith
          simpa [show (2 : ℝ) * (11 / 10) = 11 / 5 by norm_num] using htarget
        have hcos : -4 / 5 ≤ cos (2 * (6 / 5)) := by
          have hεlo : (37 / 100 : ℝ) ≤ π / 2 - 6 / 5 := by linarith [pi_gt_d6]
          have hεhi : π / 2 - 6 / 5 ≤ 371 / 1000 := by linarith [pi_lt_d6]
          have hcosb := cos_mem_bounds (a := 37 / 100) (b := 371 / 1000)
            (by norm_num) (by norm_num) hεlo hεhi
          have hsin : sin (6 / 5) = cos (π / 2 - 6 / 5) := by
            simpa using sin_pi_div_two_sub (π / 2 - 6 / 5)
          have hs0 : 0 ≤ sin (6 / 5) :=
            sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [pi_gt_three])
          have hhi0 : 0 ≤ cosHi (37 / 100) (371 / 1000) := by simp only [cosHi]; norm_num
          have hle : sin (6 / 5) ≤ cosHi (37 / 100) (371 / 1000) := by
            rw [hsin]; exact hcosb.2
          have hsq : sin (6 / 5) ^ 2 ≤ cosHi (37 / 100) (371 / 1000) ^ 2 :=
            pow_le_pow_left₀ hs0 hle 2
          have hform : cos (2 * (6 / 5)) = 1 - 2 * sin (6 / 5) ^ 2 := by
            rw [cos_two_mul]
            have hpyth : cos (6 / 5) ^ 2 + sin (6 / 5) ^ 2 = 1 := cos_sq_add_sin_sq _
            nlinarith [hpyth]
          have hnum : -4 / 5 ≤ 1 - 2 * cosHi (37 / 100) (371 / 1000) ^ 2 := by
            simp only [cosHi]; norm_num
          linarith
        exact numerator_neg_of_bounds (a := 11 / 10) (b := 6 / 5) (SB := 8 / 5) (S2 := 9 / 10)
          (C := 8 / 5) (C2 := 4) (Cos := -4 / 5)
          ⟨le_of_lt hgt2, hle3⟩ (by norm_num)
          (by linarith [pi_gt_three]) (by linarith [pi_gt_three])
          hsinhB (by norm_num) hsin2 hcoshA hcosh2 (by norm_num) hcos (by norm_num) (by norm_num)
      · rcases le_or_gt t (4 / 3) with hle4 | hgt4
        · have hsinhB : sinh (4 / 3) ≤ 9 / 5 := by
            have hE : exp (4 / 3) ≤ 272 / 100 * (141 / 100) := by
              have hid : exp (4 / 3) = exp 1 * exp (1 / 3) := by
                rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, exp_add]
              nlinarith [exp_one_lt_d9, exp_third_bounds.2, exp_pos 1, exp_pos (1 / 3)]
            have hsinh := sinh_le_of_exp_le hE
            have hnum :
                ((272 / 100 * (141 / 100)) - 1 / (272 / 100 * (141 / 100))) / 2 ≤ 9 / 5 := by
              norm_num
            linarith
          have hsin2 : sin (2 * (6 / 5)) ≤ 4 / 5 := by
            have heq : sin (2 * (6 / 5)) = sin (π - 2 * (6 / 5)) := by rw [sin_pi_sub]
            have hδhi : π - 2 * (6 / 5) ≤ 75 / 100 := by
              have : (2 : ℝ) * (6 / 5) = 12 / 5 := by norm_num
              linarith [pi_lt_d6]
            have hδlo : (0 : ℝ) ≤ π - 2 * (6 / 5) := by
              have : (2 : ℝ) * (6 / 5) = 12 / 5 := by norm_num
              linarith [pi_gt_three]
            have hmem := sin_mem_bounds (x := π - 2 * (6 / 5)) (a := 0) (b := 75 / 100)
              (by norm_num) (by norm_num) hδlo hδhi
            have hnum : sinHi (75 / 100) ≤ 4 / 5 := by simp only [sinHi]; norm_num
            rw [heq]; linarith
          have hcoshA : 9 / 5 ≤ cosh (6 / 5) := by
            have hlo : ((271 / 100) * (122 / 100) : ℝ) ≤ exp (6 / 5) := by
              have hid : exp (6 / 5) = exp 1 * exp (1 / 5) := by
                rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, exp_add]
              nlinarith [exp_one_gt_271, exp_fifth_bounds.1, exp_pos 1, exp_pos (1 / 5)]
            have hhi : exp (6 / 5) ≤ 272 / 100 * (5 / 4) := by
              have hid : exp (6 / 5) = exp 1 * exp (1 / 5) := by
                rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, exp_add]
              nlinarith [exp_one_lt_d9, exp_fifth_bounds.2, exp_pos 1, exp_pos (1 / 5)]
            have hcosh := cosh_ge_of_exp_bounds hlo hhi
            have hnum : (9 / 5 : ℝ) ≤
                (((271 / 100) * (122 / 100)) + 1 / (272 / 100 * (5 / 4))) / 2 := by norm_num
            linarith
          have hcosh2 : 11 / 2 ≤ cosh (2 * (6 / 5)) := by
            have hlo : ((271 / 100) * (122 / 100) : ℝ) ^ 2 ≤ exp (12 / 5) := by
              have hid : exp (12 / 5) = exp (6 / 5) * exp (6 / 5) := by
                rw [show (12 / 5 : ℝ) = 6 / 5 + 6 / 5 by norm_num, exp_add]
              have h65 : ((271 / 100) * (122 / 100) : ℝ) ≤ exp (6 / 5) := by
                have hid' : exp (6 / 5) = exp 1 * exp (1 / 5) := by
                  rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, exp_add]
                nlinarith [exp_one_gt_271, exp_fifth_bounds.1, exp_pos 1, exp_pos (1 / 5)]
              nlinarith [h65, exp_pos (6 / 5)]
            have hhi : exp (12 / 5) ≤ (272 / 100 * (5 / 4)) ^ 2 := by
              have hid : exp (12 / 5) = exp (6 / 5) * exp (6 / 5) := by
                rw [show (12 / 5 : ℝ) = 6 / 5 + 6 / 5 by norm_num, exp_add]
              have h65 : exp (6 / 5) ≤ 272 / 100 * (5 / 4) := by
                have hid' : exp (6 / 5) = exp 1 * exp (1 / 5) := by
                  rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, exp_add]
                nlinarith [exp_one_lt_d9, exp_fifth_bounds.2, exp_pos 1, exp_pos (1 / 5)]
              nlinarith [h65, exp_pos (6 / 5)]
            have hcosh := cosh_ge_of_exp_bounds hlo hhi
            have hnum : (11 / 2 : ℝ) ≤
                ((((271 / 100) * (122 / 100)) ^ 2 + 1 / (272 / 100 * (5 / 4)) ^ 2) / 2) := by
              norm_num
            have htarget : 11 / 2 ≤ cosh (12 / 5) := by linarith
            simpa [show (2 : ℝ) * (6 / 5) = 12 / 5 by norm_num] using htarget
          exact numerator_neg_of_bounds (a := 6 / 5) (b := 4 / 3) (SB := 9 / 5) (S2 := 4 / 5)
            (C := 9 / 5) (C2 := 11 / 2) (Cos := -1)
            ⟨le_of_lt hgt3, hle4⟩ (by norm_num)
            (by linarith [pi_gt_three]) (by linarith [pi_gt_three])
            hsinhB (by norm_num) hsin2 hcoshA hcosh2 (by norm_num)
            (neg_one_le_cos _) (by norm_num) (by norm_num)
        · rcases le_or_gt t (3 / 2) with hle5 | hgt5
          · have hsinhB : sinh (3 / 2) ≤ 11 / 5 := by
              have hE : exp (3 / 2) ≤ 272 / 100 * (165 / 100) := by
                have hid : exp (3 / 2) = exp 1 * exp (1 / 2) := by
                  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, exp_add]
                nlinarith [exp_one_lt_d9, exp_half_bounds.2, exp_pos 1, exp_pos (1 / 2)]
              have hsinh := sinh_le_of_exp_le hE
              have hnum :
                  ((272 / 100 * (165 / 100)) - 1 / (272 / 100 * (165 / 100))) / 2 ≤ 11 / 5 := by
                norm_num
              linarith
            have hsin2 : sin (2 * (4 / 3)) ≤ 1 / 2 := by
              have heq : sin (2 * (4 / 3)) = sin (π - 2 * (4 / 3)) := by rw [sin_pi_sub]
              have hδhi : π - 2 * (4 / 3) ≤ 1 / 2 := by
                have : (2 : ℝ) * (4 / 3) = 8 / 3 := by norm_num
                linarith [pi_lt_d6]
              have hδlo : (0 : ℝ) ≤ π - 2 * (4 / 3) := by
                have : (2 : ℝ) * (4 / 3) = 8 / 3 := by norm_num
                linarith [pi_gt_three]
              have hmem := sin_mem_bounds (x := π - 2 * (4 / 3)) (a := 0) (b := 1 / 2)
                (by norm_num) (by norm_num) hδlo hδhi
              have hnum : sinHi (1 / 2) ≤ 1 / 2 := by simp only [sinHi]; norm_num
              rw [heq]; linarith
            have hcoshA : (2 : ℝ) ≤ cosh (4 / 3) := by
              have hlo : ((271 / 100) * (139 / 100) : ℝ) ≤ exp (4 / 3) := by
                have hid : exp (4 / 3) = exp 1 * exp (1 / 3) := by
                  rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, exp_add]
                nlinarith [exp_one_gt_271, exp_third_bounds.1, exp_pos 1, exp_pos (1 / 3)]
              have hhi : exp (4 / 3) ≤ 272 / 100 * (141 / 100) := by
                have hid : exp (4 / 3) = exp 1 * exp (1 / 3) := by
                  rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, exp_add]
                nlinarith [exp_one_lt_d9, exp_third_bounds.2, exp_pos 1, exp_pos (1 / 3)]
              have hcosh := cosh_ge_of_exp_bounds hlo hhi
              have hnum : (2 : ℝ) ≤
                  (((271 / 100) * (139 / 100)) + 1 / (272 / 100 * (141 / 100))) / 2 := by
                norm_num
              linarith
            have hcosh2 : (7 : ℝ) ≤ cosh (2 * (4 / 3)) := by
              have hlo : ((271 / 100) * (139 / 100) : ℝ) ^ 2 ≤ exp (8 / 3) := by
                have hid : exp (8 / 3) = exp (4 / 3) * exp (4 / 3) := by
                  rw [show (8 / 3 : ℝ) = 4 / 3 + 4 / 3 by norm_num, exp_add]
                have h43 : ((271 / 100) * (139 / 100) : ℝ) ≤ exp (4 / 3) := by
                  have hid' : exp (4 / 3) = exp 1 * exp (1 / 3) := by
                    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, exp_add]
                  nlinarith [exp_one_gt_271, exp_third_bounds.1, exp_pos 1, exp_pos (1 / 3)]
                nlinarith [h43, exp_pos (4 / 3)]
              have hhi : exp (8 / 3) ≤ (272 / 100 * (141 / 100)) ^ 2 := by
                have hid : exp (8 / 3) = exp (4 / 3) * exp (4 / 3) := by
                  rw [show (8 / 3 : ℝ) = 4 / 3 + 4 / 3 by norm_num, exp_add]
                have h43 : exp (4 / 3) ≤ 272 / 100 * (141 / 100) := by
                  have hid' : exp (4 / 3) = exp 1 * exp (1 / 3) := by
                    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, exp_add]
                  nlinarith [exp_one_lt_d9, exp_third_bounds.2, exp_pos 1, exp_pos (1 / 3)]
                nlinarith [h43, exp_pos (4 / 3)]
              have hcosh := cosh_ge_of_exp_bounds hlo hhi
              have hnum : (7 : ℝ) ≤
                  ((((271 / 100) * (139 / 100)) ^ 2 +
                    1 / (272 / 100 * (141 / 100)) ^ 2) / 2) := by norm_num
              have htarget : 7 ≤ cosh (8 / 3) := by linarith
              simpa [show (2 : ℝ) * (4 / 3) = 8 / 3 by norm_num] using htarget
            exact numerator_neg_of_bounds (a := 4 / 3) (b := 3 / 2) (SB := 11 / 5) (S2 := 1 / 2)
              (C := 2) (C2 := 7) (Cos := -1)
              ⟨le_of_lt hgt4, hle5⟩ (by norm_num)
              (by linarith [pi_gt_three]) (by linarith [pi_gt_three])
              hsinhB (by norm_num) hsin2 hcoshA hcosh2 (by norm_num)
              (neg_one_le_cos _) (by norm_num) (by norm_num)
          · have hsinhB : sinh (π / 2) ≤ 5 / 2 := by
              have hle : π / 2 ≤ 8 / 5 := by linarith [pi_lt_d6]
              have hsinh85 : sinh (8 / 5) ≤ 5 / 2 := by
                have hE : exp (8 / 5) ≤ 498 / 100 := by
                  have hid : exp (8 / 5) = exp (4 / 5) * exp (4 / 5) := by
                    rw [show (8 / 5 : ℝ) = 4 / 5 + 4 / 5 by norm_num, exp_add]
                  nlinarith [exp_four_fifths_bounds.2, exp_pos (4 / 5)]
                have hsinh := sinh_le_of_exp_le hE
                have hnum : ((498 / 100) - 1 / (498 / 100)) / 2 ≤ 5 / 2 := by norm_num
                linarith
              exact le_trans ((sinh_le_sinh).mpr hle) hsinh85
            have hsin2 : sin (2 * (3 / 2)) ≤ 1 / 5 := by
              have heq : sin (2 * (3 / 2)) = sin (π - 2 * (3 / 2)) := by rw [sin_pi_sub]
              have hδhi : π - 2 * (3 / 2) ≤ 15 / 100 := by
                have : (2 : ℝ) * (3 / 2) = 3 := by norm_num
                linarith [pi_lt_d6]
              have hδlo : (0 : ℝ) ≤ π - 2 * (3 / 2) := by
                have : (2 : ℝ) * (3 / 2) = 3 := by norm_num
                linarith [pi_gt_three]
              have hmem := sin_mem_bounds (x := π - 2 * (3 / 2)) (a := 0) (b := 15 / 100)
                (by norm_num) (by norm_num) hδlo hδhi
              have hnum : sinHi (15 / 100) ≤ 1 / 5 := by simp only [sinHi]; norm_num
              rw [heq]; linarith
            have hcoshA : (2 : ℝ) ≤ cosh (3 / 2) := by
              have hlo : ((271 / 100) * (164 / 100) : ℝ) ≤ exp (3 / 2) := by
                have hid : exp (3 / 2) = exp 1 * exp (1 / 2) := by
                  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, exp_add]
                nlinarith [exp_one_gt_271, exp_half_bounds.1, exp_pos 1, exp_pos (1 / 2)]
              have hhi : exp (3 / 2) ≤ 272 / 100 * (165 / 100) := by
                have hid : exp (3 / 2) = exp 1 * exp (1 / 2) := by
                  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, exp_add]
                nlinarith [exp_one_lt_d9, exp_half_bounds.2, exp_pos 1, exp_pos (1 / 2)]
              have hcosh := cosh_ge_of_exp_bounds hlo hhi
              have hnum : (2 : ℝ) ≤
                  (((271 / 100) * (164 / 100)) + 1 / (272 / 100 * (165 / 100))) / 2 := by
                norm_num
              linarith
            have hcosh2 : (19 / 2 : ℝ) ≤ cosh (2 * (3 / 2)) := by
              have hlo : ((73 / 10 : ℝ) * (27 / 10)) ≤ exp 3 := by
                have hid : exp 3 = exp 2 * exp 1 := by
                  rw [show (3 : ℝ) = 2 + 1 by norm_num, exp_add]
                nlinarith [exp_one_sq_bounds.1, exp_one_gt_d9, exp_pos 1, exp_pos 2]
              have hhi : exp 3 ≤ (74 / 10) * (272 / 100) := by
                have hid : exp 3 = exp 2 * exp 1 := by
                  rw [show (3 : ℝ) = 2 + 1 by norm_num, exp_add]
                nlinarith [exp_one_sq_bounds.2, exp_one_lt_d9, exp_pos 1, exp_pos 2]
              have hcosh := cosh_ge_of_exp_bounds hlo hhi
              have hnum : (19 / 2 : ℝ) ≤
                  (((73 / 10) * (27 / 10) + 1 / ((74 / 10) * (272 / 100))) / 2) := by norm_num
              have htarget : 19 / 2 ≤ cosh 3 := by linarith
              simpa [show (2 : ℝ) * (3 / 2) = 3 by norm_num] using htarget
            exact numerator_neg_of_bounds (a := 3 / 2) (b := π / 2) (SB := 5 / 2) (S2 := 1 / 5)
              (C := 2) (C2 := 19 / 2) (Cos := -1)
              ⟨le_of_lt hgt5, htop⟩ (by norm_num)
              (by linarith [pi_gt_three]) (by linarith [pi_pos])
              hsinhB (by norm_num) hsin2 hcoshA hcosh2 (by norm_num)
              (neg_one_le_cos _) (by norm_num) (by norm_num)

noncomputable def ratioSlope (x : ℝ) : ℝ :=
  deriv gammaSEqual x * gammaSEqual (x / 2) -
    gammaSEqual x * (deriv gammaSEqual (x / 2) * (1 / 2))

lemma ratioSlope_two (t : ℝ) :
    ratioSlope (2 * t) =
      sin t * (gammaSEqual (2 * t) * cosh t -
        4 * cosh (2 * t) * cos t * gammaSEqual t) := by
  unfold ratioSlope
  rw [deriv_gammaSEqual, deriv_gammaSEqual, sin_two_mul]
  ring_nf

lemma ratioSlope_neg_left {x : ℝ} (hx1 : 2 * resonanceRoot1 < x) (hxπ : x ≤ π) :
    ratioSlope x < 0 := by
  have hhalf_lo : 4 / 5 < x / 2 := by
    linarith [four_fifths_lt_resonanceRoot1, hx1]
  have hhalf_hi : x / 2 ≤ π / 2 := by linarith
  have hmem : x / 2 ∈ Icc (4 / 5) (π / 2) := ⟨hhalf_lo.le, hhalf_hi⟩
  have hnum := shell_numerator_neg hmem
  have hid := shellNumerator_identity (x / 2)
  have hdouble : (2 : ℝ) * (x / 2) = x := by ring
  have hshell : gammaSEqual x * cosh (x / 2) -
      4 * cosh x * cos (x / 2) * gammaSEqual (x / 2) < 0 := by
    have hnum' := hnum
    have hid' := hid
    simp only [hdouble] at hnum' hid'
    linarith
  have hsin : 0 < sin (x / 2) :=
    sin_pos_of_pos_of_lt_pi (by linarith)
      (lt_of_le_of_lt hhalf_hi (by linarith [pi_pos]))
  have hslope := ratioSlope_two (x / 2)
  rw [hdouble] at hslope
  rw [hslope]
  nlinarith

lemma ratioSlope_neg_right {x : ℝ} (hx : x ∈ Ioo π (branchNode 1)) : ratioSlope x < 0 := by
  have hhalf_lo : π / 2 < x / 2 := by linarith [hx.1]
  have hnode : branchNode 1 < π + π := by
    simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.2
  have hhalf_hi : x / 2 < π := by linarith [hx.2, hnode]
  have hγ : gammaSEqual x < 0 := by
    refine gammaSEqual_neg_first_shell ⟨?_, hx.2⟩
    linarith [resonanceRoot1_sharp_bounds.2, pi_gt_three, hx.1]
  have hγh : gammaSEqual (x / 2) < 0 := by
    refine gammaSEqual_neg_first_shell ⟨?_, ?_⟩
    · linarith [resonanceRoot1_sharp_bounds.2, pi_gt_three, hhalf_lo]
    · have hπ : π < branchNode 1 := by
        simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1
      linarith
  have hsinx : sin x < 0 := by
    have hneg : sin x = -sin (x - π) := by
      conv_lhs => rw [show x = (x - π) + π by ring]
      rw [sin_add_pi]
    have hpos : 0 < sin (x - π) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    linarith
  have hsinh : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi (by linarith) hhalf_hi
  have hform : ratioSlope x =
      -2 * cosh x * sin x * gammaSEqual (x / 2) +
        gammaSEqual x * cosh (x / 2) * sin (x / 2) := by
    unfold ratioSlope
    rw [deriv_gammaSEqual, deriv_gammaSEqual]
    ring
  rw [hform]
  have hterm1 : -2 * cosh x * sin x * gammaSEqual (x / 2) < 0 := by
    have hprod : 0 < sin x * gammaSEqual (x / 2) := mul_pos_of_neg_of_neg hsinx hγh
    have hcoef : -2 * cosh x < 0 := by linarith [cosh_pos x]
    have : -2 * cosh x * (sin x * gammaSEqual (x / 2)) < 0 :=
      mul_neg_of_neg_of_pos hcoef hprod
    linarith
  have hterm2 : gammaSEqual x * cosh (x / 2) * sin (x / 2) < 0 := by
    have hprod : gammaSEqual x * sin (x / 2) < 0 := mul_neg_of_neg_of_pos hγ hsinh
    have hcosh : 0 < cosh (x / 2) := cosh_pos _
    have : (gammaSEqual x * sin (x / 2)) * cosh (x / 2) < 0 :=
      mul_neg_of_neg_of_pos hprod hcosh
    linarith
  linarith

lemma hasDerivAt_pairRatio {x : ℝ} (hγ : gammaSEqual (x / 2) ≠ 0) :
    HasDerivAt pairRatio (ratioSlope x / gammaSEqual (x / 2) ^ 2) x := by
  unfold pairRatio ratioSlope
  have hhalf : HasDerivAt (fun y : ℝ => y / 2) ((1 : ℝ) / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have hg2 := (hasDerivAt_gammaSEqual (x / 2)).comp x hhalf
  have hdiv := (hasDerivAt_gammaSEqual x).div hg2 hγ
  change HasDerivAt (fun y => gammaSEqual y / gammaSEqual (y / 2)) _ x at hdiv
  convert hdiv using 1
  rw [deriv_gammaSEqual, deriv_gammaSEqual]
  simp only [Function.comp_apply]

lemma halfPhase_in_firstShell {y : ℝ} (hy : y ∈ Ioo (2 * resonanceRoot1) (branchNode 1)) :
    gammaSEqual (y / 2) < 0 := by
  have hπ : π < branchNode 1 := by
    simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1
  refine gammaSEqual_neg_first_shell ⟨?_, ?_⟩
  · linarith [four_fifths_lt_resonanceRoot1, hy.1]
  · have hy0 : 0 < y := by linarith [hy.1, resonanceRoot1_bounds.1]
    have hlt : y / 2 < y := by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    exact lt_trans hlt hy.2

lemma pairRatio_strictAnti :
    StrictAntiOn pairRatio (Ioo (2 * resonanceRoot1) (branchNode 1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) ?_ ?_
  · unfold pairRatio
    refine ContinuousOn.div continuous_gammaSEqual.continuousOn
      ((continuous_gammaSEqual.comp (continuous_id.div_const 2)).continuousOn.mono
        (fun _ _ => trivial)) ?_
    intro y hy
    exact (halfPhase_in_firstShell hy).ne
  · intro y hy
    rw [interior_Ioo] at hy
    have hγ : gammaSEqual (y / 2) ≠ 0 := (halfPhase_in_firstShell hy).ne
    rw [(hasDerivAt_pairRatio hγ).deriv]
    have hden : 0 < gammaSEqual (y / 2) ^ 2 := sq_pos_of_ne_zero hγ
    rcases le_or_gt y π with hle | hgt
    · exact div_neg_of_neg_of_pos (ratioSlope_neg_left hy.1 hle) hden
    · exact div_neg_of_neg_of_pos (ratioSlope_neg_right ⟨hgt, hy.2⟩) hden

lemma exp_three_quarters_bounds : (21 / 10 : ℝ) < exp (3 / 4) ∧ exp (3 / 4) < 22 / 10 := by
  refine exp_between (x := 3 / 4) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma gamma_seven_quarters_lt : gammaSEqual (7 / 4) < -3 := by
  have hεlo : (179 / 1000 : ℝ) ≤ 7 / 4 - π / 2 := by linarith [pi_lt_d6]
  have hεhi : 7 / 4 - π / 2 ≤ 180 / 1000 := by linarith [pi_gt_d6]
  have hexp_lo : (56 / 10 : ℝ) < exp (7 / 4) := by
    have hid : exp (7 / 4) = exp 1 * exp (3 / 4) := by
      rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num, exp_add]
    nlinarith [exp_one_gt_271, exp_three_quarters_bounds.1, exp_pos 1, exp_pos (3 / 4)]
  have hexp_hi : exp (7 / 4) < 6 := by
    have hid : exp (7 / 4) = exp 1 * exp (3 / 4) := by
      rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_three_quarters_bounds.2, exp_pos 1]
  have hD : -(sinLo (179 / 1000) (180 / 1000) + cosLo (180 / 1000)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (180 / 1000) + cosLo (180 / 1000) := by
    simp only [sinHi, cosLo]; norm_num
  have hbounds := gamma_after (x := 7 / 4) (ε := 7 / 4 - π / 2)
      (a := 179 / 1000) (b := 180 / 1000) (E0 := 56 / 10) (E1 := 6)
      (by ring) (by norm_num) (by norm_num) hεlo hεhi (by norm_num)
      hexp_lo.le hexp_hi.le hD hS
  have hgu : gammaUpper (56 / 10)
      (-(sinLo (179 / 1000) (180 / 1000) + cosLo (180 / 1000)))
      (-sinLo (179 / 1000) (180 / 1000) + cosHi (179 / 1000) (180 / 1000)) < -3 := by
    simp only [gammaUpper, sinLo, cosLo, cosHi]; norm_num
  linarith [hbounds.2]

lemma gamma_seven_halves_gt : -11 < gammaSEqual (7 / 2) := by
  have hδlo : (358 / 1000 : ℝ) ≤ 7 / 2 - π := by linarith [pi_lt_d6]
  have hδhi : 7 / 2 - π ≤ 359 / 1000 := by linarith [pi_gt_d6]
  have hsin := sin_mem_bounds (a := 358 / 1000) (b := 359 / 1000)
    (by norm_num) (by norm_num) hδlo hδhi
  have hcos := cos_mem_bounds (a := 358 / 1000) (b := 359 / 1000)
    (by norm_num) (by norm_num) hδlo hδhi
  have hDlo : sinLo (358 / 1000) (359 / 1000) - cosHi (358 / 1000) (359 / 1000) ≤
      sin (7 / 2 - π) - cos (7 / 2 - π) := by linarith [hsin.1, hcos.2]
  have hShi : sin (7 / 2 - π) + cos (7 / 2 - π) ≤
      sinHi (359 / 1000) + cosHi (358 / 1000) (359 / 1000) := by linarith [hsin.2, hcos.2]
  have hid : gammaSEqual (7 / 2) =
      exp (7 / 2) / 2 * (sin (7 / 2 - π) - cos (7 / 2 - π)) -
        exp (-(7 / 2)) / 2 * (sin (7 / 2 - π) + cos (7 / 2 - π)) := by
    rw [gammaSEqual_exp]
    have hsinx : sin (7 / 2) = -sin (7 / 2 - π) := by
      conv_lhs => rw [show (7 / 2 : ℝ) = (7 / 2 - π) + π by ring]
      rw [sin_add_pi]
    have hcosx : cos (7 / 2) = -cos (7 / 2 - π) := by
      conv_lhs => rw [show (7 / 2 : ℝ) = (7 / 2 - π) + π by ring]
      rw [cos_add_pi]
    rw [hsinx, hcosx]
    ring
  have hexp_hi : exp (7 / 2) < 34 := by
    have hid' : exp (7 / 2) = exp 3 * exp (1 / 2) := by
      rw [show (7 / 2 : ℝ) = 3 + 1 / 2 by norm_num, exp_add]
    have h3 : exp 3 < 203 / 10 := by
      have hid3 : exp 3 = exp 2 * exp 1 := by
        rw [show (3 : ℝ) = 2 + 1 by norm_num, exp_add]
      have h1 : exp 1 < 272 / 100 := lt_trans exp_one_lt_d9 (by norm_num)
      nlinarith [exp_one_sq_bounds.2, h1, exp_pos 1, exp_pos 2]
    nlinarith [exp_half_bounds.2, h3, exp_pos (1 / 2), exp_pos 3]
  have hexp_lo : (32 : ℝ) < exp (7 / 2) := by
    have hid' : exp (7 / 2) = exp 3 * exp (1 / 2) := by
      rw [show (7 / 2 : ℝ) = 3 + 1 / 2 by norm_num, exp_add]
    have h3 : (197 / 10 : ℝ) < exp 3 := by
      have hid3 : exp 3 = exp 2 * exp 1 := by
        rw [show (3 : ℝ) = 2 + 1 by norm_num, exp_add]
      nlinarith [exp_one_sq_bounds.1, exp_one_gt_271, exp_pos 1, exp_pos 2]
    nlinarith [exp_half_bounds.1, h3, exp_pos (1 / 2), exp_pos 3]
  have hDneg : sinLo (358 / 1000) (359 / 1000) - cosHi (358 / 1000) (359 / 1000) < 0 := by
    simp only [sinLo, cosHi]; norm_num
  have hSpos : 0 < sinHi (359 / 1000) + cosHi (358 / 1000) (359 / 1000) := by
    simp only [sinHi, cosHi]; norm_num
  have hlow : (34 / 2) * (sinLo (358 / 1000) (359 / 1000) -
      cosHi (358 / 1000) (359 / 1000)) -
      (sinHi (359 / 1000) + cosHi (358 / 1000) (359 / 1000)) / (2 * 32) > -11 := by
    simp only [sinLo, sinHi, cosHi]; norm_num
  -- exp/2 * D ≥ (34/2) * Dlo because D ≤ Dlo < 0 and exp < 34, so exp*D > 34*Dlo
  -- (more negative times larger magnitude). And the subtracted term is at most S_hi/(2*33).
  have hDge : sinLo (358 / 1000) (359 / 1000) - cosHi (358 / 1000) (359 / 1000) ≤
      sin (7 / 2 - π) - cos (7 / 2 - π) := by
    linarith [hsin.1, hcos.2]
  set Dlo := sinLo (358 / 1000) (359 / 1000) - cosHi (358 / 1000) (359 / 1000)
  set Shi := sinHi (359 / 1000) + cosHi (358 / 1000) (359 / 1000)
  have hfirst : exp (7 / 2) / 2 * (sin (7 / 2 - π) - cos (7 / 2 - π)) ≥ (34 / 2) * Dlo := by
    have hstep : exp (7 / 2) / 2 * Dlo ≥ (34 / 2) * Dlo := by nlinarith [hexp_hi, hDneg]
    nlinarith [hDge, hstep, hexp_hi]
  have hsecond : exp (-(7 / 2)) / 2 * (sin (7 / 2 - π) + cos (7 / 2 - π)) ≤ Shi / (2 * 32) := by
    have hinv : exp (-(7 / 2)) ≤ 1 / 32 := by
      have hdiv : 1 / exp (7 / 2) ≤ 1 / 32 :=
        one_div_le_one_div_of_le (by norm_num) hexp_lo.le
      simpa [exp_neg, one_div] using hdiv
    nlinarith [hShi, hSpos, hinv, exp_pos (-(7 / 2))]
  linarith [hid, hlow, hfirst, hsecond]

lemma pairBalance_seven_halves_pos {Z : ℝ} (hZ : 1 ≤ Z) : 0 < pairBalance Z (7 / 2) := by
  have hquarter : gammaSEqual (7 / 4) < -3 := gamma_seven_quarters_lt
  have hhalf : -11 < gammaSEqual (7 / 2) := gamma_seven_halves_gt
  unfold pairBalance
  have hextra : 0 ≤ -4 * (Z - 1) * gammaSEqual (7 / 4) := by nlinarith
  nlinarith

lemma pairBalance_neg_near_outer {Z : ℝ} (hZ : 1 ≤ Z) :
    pairBalance Z (2 * (resonanceRoot1 + 1 / (64 * Z))) < 0 := by
  have hZ0 : 0 < Z := by linarith
  set h : ℝ := 1 / (64 * Z) with hh
  have hh0 : 0 < h := by positivity
  have hx1 : resonanceRoot1 < resonanceRoot1 + h := by linarith
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope gammaSEqual (deriv gammaSEqual) hx1
    continuous_gammaSEqual.continuousOn (fun y _ => by
      simpa [deriv_gammaSEqual] using hasDerivAt_gammaSEqual y)
  have hzero : gammaSEqual resonanceRoot1 = 0 := resonanceRoot1_gammaSEqual_zero
  have hval : gammaSEqual (resonanceRoot1 + h) = deriv gammaSEqual c * h := by
    have hs := hslope.symm
    rw [hzero, sub_zero] at hs
    have hsub : resonanceRoot1 + h - resonanceRoot1 = h := by ring
    rw [hsub] at hs
    field_simp [hh0.ne'] at hs
    linarith
  have hh1 : h ≤ 1 / 64 := by
    rw [hh, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hc0 : 0 ≤ c := by linarith [resonanceRoot1_bounds.1, hc.1]
  have hc2 : c < 2 := by linarith [hc.2, resonanceRoot1_sharp_bounds.2]
  have hcosh : cosh c < 5 := by
    have hle : cosh c ≤ cosh 2 := (cosh_le_cosh).mpr (by
      rw [abs_of_nonneg hc0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact le_of_lt hc2)
    linarith [hle, cosh_two_lt_five]
  have hsin0 : 0 ≤ sin c :=
    sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [hc2, pi_gt_three])
  have hmag : 2 * cosh c * sin c < 10 := by
    have hsin : sin c ≤ 1 := sin_le_one c
    have hcoef : 0 ≤ 2 * cosh c := by linarith [cosh_pos c]
    have hlin : 2 * cosh c * sin c ≤ 2 * cosh c := by
      simpa using mul_le_mul_of_nonneg_left hsin hcoef
    linarith [hcosh, hlin]
  have hsmall : -gammaSEqual (resonanceRoot1 + h) < 10 * h := by
    rw [hval, deriv_gammaSEqual]
    nlinarith [hmag, hh0]
  have hxbig : 8 / 5 < 2 * (resonanceRoot1 + h) := by
    linarith [four_fifths_lt_resonanceRoot1]
  have hxπ : 2 * (resonanceRoot1 + h) < π := by
    linarith [resonanceRoot1_sharp_bounds.2, pi_gt_three]
  have hmemL : (8 / 5 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, by linarith [pi_gt_three]⟩
  have hmemx : 2 * (resonanceRoot1 + h) ∈ Icc (0 : ℝ) π :=
    ⟨by linarith [resonanceRoot1_bounds.1], hxπ.le⟩
  have hγx : gammaSEqual (2 * (resonanceRoot1 + h)) < gammaSEqual (8 / 5) :=
    strictAntiOn_gammaSEqual_even 0 (by simpa using hmemL) (by simpa using hmemx) hxbig
  have hγlt : gammaSEqual (2 * (resonanceRoot1 + h)) < -1 := by
    linarith [hγx, gammaSEqual_eight_fifths_lt]
  unfold pairBalance
  have harg : 2 * (resonanceRoot1 + h) / 2 = resonanceRoot1 + h := by ring
  rw [harg]
  have hscale : 4 * Z * (10 * h) = 5 / 8 := by
    rw [hh]
    field_simp [hZ0.ne']
    ring
  nlinarith [hsmall, hγlt, hscale]

theorem exists_unique_diameter_shell {Z : ℝ} (hZ : 1 ≤ Z) :
    ∃! x : ℝ, x ∈ Ioo (2 * resonanceRoot1) (branchNode 1) ∧ pairBalance Z x = 0 := by
  have hZ0 : 0 < Z := by linarith
  set xL : ℝ := 2 * (resonanceRoot1 + 1 / (64 * Z))
  have hneg := pairBalance_neg_near_outer hZ
  have hpos := pairBalance_seven_halves_pos hZ
  have hxL_lo : 2 * resonanceRoot1 < xL := by
    have hh : 0 < 1 / (64 * Z) := by positivity
    dsimp [xL]; linarith
  have hxL_hi : xL < 7 / 2 := by
    have hh : 1 / (64 * Z) ≤ 1 / 64 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    dsimp [xL]
    linarith [resonanceRoot1_sharp_bounds.2]
  have h72 : (7 / 2 : ℝ) < branchNode 1 := by
    have hlo : π + π / 4 < branchNode 1 := by
      have h := node_mem_sharp_branch 1 (branchNode_spec 1).1 (branchNode_spec 1).2
      simpa [Nat.cast_one, one_mul] using h.1
    linarith [pi_gt_three]
  obtain ⟨x, hxI, hx0⟩ := intermediate_value_Ioo (le_of_lt hxL_hi)
    (continuous_pairBalance Z).continuousOn ⟨hneg, hpos⟩
  have hxmem : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1) :=
    ⟨lt_trans hxL_lo hxI.1, lt_trans hxI.2 h72⟩
  refine ⟨x, ⟨hxmem, hx0⟩, ?_⟩
  intro y hy
  have hratio (w : ℝ) (hw : w ∈ Ioo (2 * resonanceRoot1) (branchNode 1))
      (h0 : pairBalance Z w = 0) : pairRatio w = 4 * Z := by
    have hden : gammaSEqual (w / 2) ≠ 0 := (halfPhase_in_firstShell hw).ne
    have h0' : gammaSEqual w - 4 * Z * gammaSEqual (w / 2) = 0 := by
      simpa [pairBalance] using h0
    unfold pairRatio
    field_simp [hden]
    linarith
  have hxρ := hratio x hxmem hx0
  have hyρ := hratio y hy.1 hy.2
  exact (pairRatio_strictAnti.injOn hxmem hy.1 (by rw [hxρ, hyρ])).symm

theorem diameterOutward_sign {Z x : ℝ} (_hZ : 1 ≤ Z)
    (hx : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1)) :
    diameterOutward Z x < 0 ↔pairBalance Z x < 0 := by
  have hγ : gammaSEqual x < 0 := by
    refine gammaSEqual_neg_first_shell ⟨?_, hx.2⟩
    linarith [four_fifths_lt_resonanceRoot1, hx.1]
  have hγh : gammaSEqual (x / 2) < 0 := halfPhase_in_firstShell hx
  have hden : 0 < 4 * gammaSEqual x * gammaSEqual (x / 2) := by nlinarith
  rw [pairBalance_eq_outward hγ.ne hγh.ne]
  constructor
  · intro h
    simpa using (div_lt_iff₀ hden).mp h
  · intro h
    exact (div_lt_iff₀ hden).mpr (by simpa using h)

/-! ### The antipode is an angular maximum -/

noncomputable def pairSeparation (r θ : ℝ) : ℝ :=
  2 * r * sin (θ / 2)

noncomputable def likePairEnergySlope (k e γ d : ℝ) : ℝ :=
  -(k * e ^ 2) / (γ * d ^ 2)

theorem likePairEnergySlope_pos {k e γ d : ℝ}
    (hk : 0 < k) (he : e ≠ 0) (hγ : γ < 0) (hd : d ≠ 0) :
    0 < likePairEnergySlope k e γ d := by
  unfold likePairEnergySlope
  have hnum : 0 < k * e ^ 2 := mul_pos hk (sq_pos_of_ne_zero he)
  have hden : γ * d ^ 2 < 0 := mul_neg_of_neg_of_pos hγ (sq_pos_of_ne_zero hd)
  have hneg : 0 < -(k * e ^ 2 / (γ * d ^ 2)) :=
    neg_pos.mpr (div_neg_of_pos_of_neg hnum hden)
  simpa [neg_div] using hneg

theorem pairSeparation_antipode (r : ℝ) : pairSeparation r π = 2 * r := by
  unfold pairSeparation
  rw [sin_pi_div_two]
  ring

theorem pairSeparation_antipode_curvature {r : ℝ} (hr : 0 < r) :
    deriv (pairSeparation r) π = 0 ∧ deriv (deriv (pairSeparation r)) π < 0 := by
  have hhalf (θ : ℝ) : HasDerivAt (fun φ : ℝ => φ / 2) ((1 : ℝ) / 2) θ :=
    (hasDerivAt_id θ).div_const 2
  have hsin (θ : ℝ) :
      HasDerivAt (Real.sin ∘ fun φ : ℝ => φ / 2) (Real.cos (θ / 2) * ((1 : ℝ) / 2)) θ :=
    (Real.hasDerivAt_sin (θ / 2)).comp θ (hhalf θ)
  have hsep (θ : ℝ) : HasDerivAt (pairSeparation r) (r * cos (θ / 2)) θ := by
    unfold pairSeparation
    have hmul := (hsin θ).const_mul (2 * r)
    have hfun : (fun φ => (2 * r) * (Real.sin ∘ fun ψ : ℝ => ψ / 2) φ) =
        fun φ => 2 * r * sin (φ / 2) := by
      funext φ
      simp [Function.comp_apply]
    rw [← hfun]
    exact hmul.congr_deriv (by ring)
  have hzero : deriv (pairSeparation r) π = 0 := by
    rw [(hsep π).deriv, cos_pi_div_two]
    ring
  have hfun : deriv (pairSeparation r) = fun θ => r * cos (θ / 2) := by
    funext θ
    exact (hsep θ).deriv
  have hcos (θ : ℝ) :
      HasDerivAt (Real.cos ∘ fun φ : ℝ => φ / 2) (-Real.sin (θ / 2) * ((1 : ℝ) / 2)) θ :=
    (Real.hasDerivAt_cos (θ / 2)).comp θ (hhalf θ)
  have hrad (θ : ℝ) :
      HasDerivAt (fun φ => r * cos (φ / 2)) (-(r * sin (θ / 2)) * ((1 : ℝ) / 2)) θ := by
    have hmul := (hcos θ).const_mul r
    have hfun : (fun φ => r * (Real.cos ∘ fun ψ : ℝ => ψ / 2) φ) =
        fun φ => r * cos (φ / 2) := by
      funext φ
      simp [Function.comp_apply]
    rw [← hfun]
    exact hmul.congr_deriv (by ring)
  have hsecond : deriv (deriv (pairSeparation r)) π = -r / 2 := by
    rw [hfun, (hrad π).deriv, sin_pi_div_two]
    ring
  exact ⟨hzero, by linarith [hr, hsecond]⟩

/-- The product is the angular second derivative of an energy whose separation
derivative is `likePairEnergySlope`, evaluated where the separation derivative
vanishes. -/
theorem antipode_energy_curvature_neg {k e γ r : ℝ}
    (hr : 0 < r) (hk : 0 < k) (he : e ≠ 0) (hγ : γ < 0) :
    likePairEnergySlope k e γ (2 * r) *
      deriv (deriv (pairSeparation r)) π < 0 := by
  have hsep := (pairSeparation_antipode_curvature hr).2
  have hslope := likePairEnergySlope_pos (d := 2 * r) hk he hγ (by linarith)
  exact mul_neg_of_pos_of_neg hslope hsep

/-! ### Phase weight

The logarithmic slope of `γ`, weighted by its argument, is strictly decreasing
on the first repulsive shell. Every scale `c ∈ (0, 1)` therefore has a strictly
decreasing ratio `γ(x) / γ(c x)` there. The cube response is a positive
combination of three such ratios. -/

noncomputable def phaseLogNum (u : ℝ) : ℝ :=
  2 * u * cos (2 * u) - 2 * u * cosh (2 * u) - 4 * u -
    sin (2 * u) * cosh (2 * u) - sin (2 * u) -
    cos (2 * u) * sinh (2 * u) + sinh (2 * u)

lemma phaseLogNum_mul_exp (u : ℝ) :
    2 * phaseLogNum u * exp (2 * u) =
      exp (4 * u) * (-(2 * u) + 1 - (sin (2 * u) + cos (2 * u))) +
        exp (2 * u) * (4 * u * cos (2 * u) - 8 * u - 2 * sin (2 * u)) +
        (-(2 * u) + cos (2 * u) - sin (2 * u) - 1) := by
  unfold phaseLogNum
  rw [sinh_eq, cosh_eq]
  have h4 : exp (4 * u) = exp (2 * u) * exp (2 * u) := by
    rw [show (4 * u : ℝ) = 2 * u + 2 * u by ring, exp_add]
  have hcancel (t : ℝ) : exp t * exp (-t) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  rw [h4]
  ring_nf
  have hpull (a t : ℝ) : a * exp t * exp (-t) = a := by
    calc a * exp t * exp (-t) = a * (exp t * exp (-t)) := by ring
      _ = a := by rw [hcancel, mul_one]
  simp only [hcancel, hpull]
  ring_nf

lemma abs_sin_add_cos_lt {θ : ℝ} : |sin θ + cos θ| < 3 / 2 := by
  have hsq : (sin θ + cos θ) ^ 2 = 1 + sin (2 * θ) := by
    calc (sin θ + cos θ) ^ 2 = sin θ ^ 2 + cos θ ^ 2 + 2 * sin θ * cos θ := by ring
      _ = 1 + 2 * sin θ * cos θ := by rw [sin_sq_add_cos_sq]
      _ = 1 + sin (2 * θ) := by rw [← sin_two_mul]
  have hle : (sin θ + cos θ) ^ 2 ≤ 2 := by
    rw [hsq]
    linarith [sin_le_one (2 * θ)]
  have hlt : (sin θ + cos θ) ^ 2 < (3 / 2) ^ 2 := by
    nlinarith [hle]
  have habs : |sin θ + cos θ| < |(3 / 2 : ℝ)| := (sq_lt_sq).1 hlt
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at habs

lemma abs_cos_sub_sin_lt {θ : ℝ} : |cos θ - sin θ| < 3 / 2 := by
  have hsq : (cos θ - sin θ) ^ 2 = 1 - sin (2 * θ) := by
    calc (cos θ - sin θ) ^ 2 = cos θ ^ 2 + sin θ ^ 2 - 2 * sin θ * cos θ := by ring
      _ = 1 - 2 * sin θ * cos θ := by nlinarith [sin_sq_add_cos_sq θ]
      _ = 1 - sin (2 * θ) := by rw [← sin_two_mul]
  have hle : (cos θ - sin θ) ^ 2 ≤ 2 := by
    rw [hsq]
    linarith [neg_one_le_sin (2 * θ)]
  have hlt : (cos θ - sin θ) ^ 2 < (3 / 2) ^ 2 := by
    nlinarith [hle]
  have habs : |cos θ - sin θ| < |(3 / 2 : ℝ)| := (sq_lt_sq).1 hlt
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at habs

lemma exp_eight_fifths_gt_four : (4 : ℝ) < exp (8 / 5) := by
  have hid : exp (8 / 5) = exp (4 / 5) * exp (4 / 5) := by
    rw [show (8 / 5 : ℝ) = 4 / 5 + 4 / 5 by norm_num, exp_add]
  nlinarith [exp_four_fifths_bounds.1, exp_pos (4 / 5)]

lemma exp_five_halves_gt_eleven : (11 : ℝ) < exp (5 / 2) := by
  have hid : exp (5 / 2) = exp 2 * exp (1 / 2) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, exp_add]
  nlinarith [exp_one_sq_bounds.1, exp_half_bounds.1, exp_pos 2, exp_pos (1 / 2)]

lemma sin_two_phase_gt_half {u : ℝ} (hlo : 4 / 5 ≤ u) (hhi : u ≤ 5 / 4) :
    1 / 2 < sin (2 * u) := by
  have h2lo : 8 / 5 ≤ 2 * u := by linarith
  have h2hi : 2 * u ≤ 5 / 2 := by linarith
  have hsin_eq : sin (2 * u) = sin (π - 2 * u) := by rw [sin_pi_sub]
  rw [hsin_eq]
  have hbase_lo : (64 / 100 : ℝ) ≤ π - 5 / 2 := by linarith [pi_gt_d6]
  have hbase_hi : π - 5 / 2 ≤ 65 / 100 := by linarith [pi_lt_d6]
  have hsin_base : sinLo (64 / 100) (65 / 100) ≤ sin (π - 5 / 2) :=
    (sin_mem_bounds (a := 64 / 100) (b := 65 / 100) (by norm_num) (by norm_num)
      hbase_lo hbase_hi).1
  have hsin_num : 1 / 2 < sinLo (64 / 100) (65 / 100) := by
    simp only [sinLo]; norm_num
  have hmono : StrictMonoOn sin (Icc 0 (π / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_sin.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [show deriv sin x = cos x from congrFun Real.deriv_sin x]
    exact cos_pos_of_mem_Ioo ⟨by linarith [hx.1, pi_pos], hx.2⟩
  have hleft : 0 ≤ π - 5 / 2 := by linarith [hbase_lo]
  have hright : π - 2 * u ≤ π / 2 := by linarith [h2lo, pi_gt_three]
  have hleft2 : 0 ≤ π - 2 * u := by linarith [h2hi, pi_gt_three]
  have horder : π - 5 / 2 ≤ π - 2 * u := by linarith
  have hsin_le : sin (π - 5 / 2) ≤ sin (π - 2 * u) :=
    (hmono.monotoneOn ⟨hleft, by linarith [hbase_hi, pi_gt_three]⟩
      ⟨hleft2, hright⟩ horder)
  linarith

lemma phaseLogNum_neg_low {u : ℝ} (hlo : 4 / 5 ≤ u) (hhi : u ≤ 5 / 4) :
    phaseLogNum u < 0 := by
  have hsin : 1 / 2 < sin (2 * u) := sin_two_phase_gt_half hlo hhi
  have h2lo : 8 / 5 ≤ 2 * u := by linarith
  have h2hi : 2 * u ≤ 5 / 2 := by linarith
  have hcos : cos (2 * u) < 0 :=
    cos_neg_of_pi_div_two_lt_of_lt (by linarith [h2lo, pi_lt_d6])
      (lt_trans (by linarith [h2hi, pi_gt_three] : 2 * u < π) (by linarith [pi_pos]))
  suffices hmain : 2 * phaseLogNum u * exp (2 * u) < 0 by
    have heq : phaseLogNum u =
        (2 * phaseLogNum u * exp (2 * u)) / (2 * exp (2 * u)) := by field_simp
    rw [heq]
    exact div_neg_of_neg_of_pos hmain (by positivity)
  rw [phaseLogNum_mul_exp]
  set s := sin (2 * u)
  set c := cos (2 * u)
  have hs : 1 / 2 ≤ s := hsin.le
  have hc : c ≤ 0 := hcos.le
  have hc1 : -1 ≤ c := neg_one_le_cos _
  have hT1 : exp (4 * u) * (-(2 * u) + 1 - (s + c)) < 0 := by
    have hκ : -(2 * u) + 1 - (s + c) ≤ -1 / 10 := by nlinarith
    have hκ0 : -(2 * u) + 1 - (s + c) < 0 := by linarith
    exact mul_neg_of_pos_of_neg (exp_pos _) hκ0
  have hT2 : exp (2 * u) * (4 * u * c - 8 * u - 2 * s) ≤
      exp (8 / 5) * (-37 / 5) := by
    have hμ : 4 * u * c - 8 * u - 2 * s ≤ -37 / 5 := by nlinarith
    have hμ0 : 4 * u * c - 8 * u - 2 * s ≤ 0 := by linarith
    have hexp : exp (8 / 5) ≤ exp (2 * u) := exp_le_exp.mpr h2lo
    have hmul : exp (2 * u) * (4 * u * c - 8 * u - 2 * s) ≤
        exp (8 / 5) * (4 * u * c - 8 * u - 2 * s) :=
      mul_le_mul_of_nonpos_right hexp hμ0
    have hscale : exp (8 / 5) * (4 * u * c - 8 * u - 2 * s) ≤
        exp (8 / 5) * (-37 / 5) :=
      mul_le_mul_of_nonneg_left hμ (exp_pos _).le
    exact le_trans hmul hscale
  have hT3 : -(2 * u) + c - s - 1 ≤ -31 / 10 := by nlinarith
  have hsum : exp (8 / 5) * (-37 / 5) + (-31 / 10) < 0 := by
    have hexp : (4 : ℝ) < exp (8 / 5) := exp_eight_fifths_gt_four
    nlinarith
  linarith

lemma phaseLogNum_neg_mid {u : ℝ} (hlo : 5 / 4 ≤ u) (_hhi : u ≤ 7 / 4) :
    phaseLogNum u < 0 := by
  suffices hmain : 2 * phaseLogNum u * exp (2 * u) < 0 by
    have heq : phaseLogNum u =
        (2 * phaseLogNum u * exp (2 * u)) / (2 * exp (2 * u)) := by field_simp
    rw [heq]
    exact div_neg_of_neg_of_pos hmain (by positivity)
  rw [phaseLogNum_mul_exp]
  set s := sin (2 * u)
  set c := cos (2 * u)
  have hsc : -(3 / 2) < s + c := by
    have h := abs_sin_add_cos_lt (θ := 2 * u)
    rw [abs_lt] at h
    linarith
  have hcs : c - s < 3 / 2 := by
    have h := abs_cos_sub_sin_lt (θ := 2 * u)
    rw [abs_lt] at h
    linarith
  have hs : -1 ≤ s := neg_one_le_sin _
  have hc : c ≤ 1 := cos_le_one _
  have hT1 : exp (4 * u) * (-(2 * u) + 1 - (s + c)) < 0 := by
    have hκ : -(2 * u) + 1 - (s + c) < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg (exp_pos _) hκ
  have hT2 : exp (2 * u) * (4 * u * c - 8 * u - 2 * s) ≤ exp (5 / 2) * (-3) := by
    have hμ : 4 * u * c - 8 * u - 2 * s ≤ -3 := by nlinarith
    have hμ0 : 4 * u * c - 8 * u - 2 * s ≤ 0 := by linarith
    have hexp : exp (5 / 2) ≤ exp (2 * u) := exp_le_exp.mpr (by linarith)
    have hmul : exp (2 * u) * (4 * u * c - 8 * u - 2 * s) ≤
        exp (5 / 2) * (4 * u * c - 8 * u - 2 * s) :=
      mul_le_mul_of_nonpos_right hexp hμ0
    have hscale : exp (5 / 2) * (4 * u * c - 8 * u - 2 * s) ≤ exp (5 / 2) * (-3) :=
      mul_le_mul_of_nonneg_left hμ (exp_pos _).le
    exact le_trans hmul hscale
  have hT3 : -(2 * u) + c - s - 1 < -2 := by nlinarith
  have htail : exp (5 / 2) * (-3) - 2 < 0 := by
    nlinarith [exp_five_halves_gt_eleven]
  linarith

lemma phaseLogNum_neg_high {u : ℝ} (hu : 7 / 4 ≤ u) : phaseLogNum u < 0 := by
  suffices hmain : 2 * phaseLogNum u * exp (2 * u) < 0 by
    have heq : phaseLogNum u =
        (2 * phaseLogNum u * exp (2 * u)) / (2 * exp (2 * u)) := by field_simp
    rw [heq]
    exact div_neg_of_neg_of_pos hmain (by positivity)
  rw [phaseLogNum_mul_exp]
  set s := sin (2 * u)
  set c := cos (2 * u)
  have hsc : -(3 / 2) < s + c := by
    have h := abs_sin_add_cos_lt (θ := 2 * u)
    rw [abs_lt] at h
    linarith
  have hcs : c - s < 3 / 2 := by
    have h := abs_cos_sub_sin_lt (θ := 2 * u)
    rw [abs_lt] at h
    linarith
  have hs : -1 ≤ s := neg_one_le_sin _
  have hc : c ≤ 1 := cos_le_one _
  have hT1 : exp (4 * u) * (-(2 * u) + 1 - (s + c)) < 0 := by
    have hκ : -(2 * u) + 1 - (s + c) < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg (exp_pos _) hκ
  have hT2 : exp (2 * u) * (4 * u * c - 8 * u - 2 * s) < 0 := by
    have hμ : 4 * u * c - 8 * u - 2 * s < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg (exp_pos _) hμ
  have hT3 : -(2 * u) + c - s - 1 < 0 := by nlinarith
  linarith

lemma phaseLogNum_neg {u : ℝ} (hu : u ∈ Ioo resonanceRoot1 (branchNode 1)) :
    phaseLogNum u < 0 := by
  have hlo : 4 / 5 < u := lt_trans four_fifths_lt_resonanceRoot1 hu.1
  rcases lt_or_ge u (5 / 4) with hlt | hge
  · exact phaseLogNum_neg_low hlo.le hlt.le
  · rcases lt_or_ge u (7 / 4) with hlt2 | hge2
    · exact phaseLogNum_neg_mid hge hlt2.le
    · exact phaseLogNum_neg_high hge2

noncomputable def phaseWeight (y : ℝ) : ℝ :=
  2 * y * cosh y * sin y / (-gammaSEqual y)

lemma weightNumer_eq (y : ℝ) :
    2 * (2 * (cosh y * sin y + y * (sinh y * sin y + cosh y * cos y)) * (-gammaSEqual y) -
        2 * y * cosh y * sin y * (2 * cosh y * sin y)) =
      phaseLogNum y := by
  unfold phaseLogNum gammaSEqual
  rw [sin_two_mul, cos_two_mul, sinh_two_mul, cosh_two_mul]
  ring_nf
  simp only [cosh_sq y, sin_sq y]
  ring

set_option maxHeartbeats 4000000 in
-- `ring_nf` expands the phase-weight numerator before the square identities.
lemma hasDerivAt_phaseWeight {y : ℝ} (hg : gammaSEqual y ≠ 0) :
    HasDerivAt phaseWeight (phaseLogNum y / (2 * gammaSEqual y ^ 2)) y := by
  have hnum :=
    ((hasDerivAt_id y).mul ((hasDerivAt_cosh y).mul (hasDerivAt_sin y))).const_mul 2
  have hden := (hasDerivAt_gammaSEqual y).neg
  simp only [Pi.mul_apply, id] at hnum
  have hdiv := hnum.div hden (by simpa using hg)
  simp only [Pi.div_apply, Pi.neg_apply] at hdiv
  have hfun : (fun t => 2 * (t * (cosh t * sin t))) / -gammaSEqual = phaseWeight := by
    funext t
    unfold phaseWeight
    simp [Pi.div_apply, Pi.neg_apply]
    ring
  rw [hfun] at hdiv
  refine hdiv.congr_deriv ?_
  simp only [one_mul, neg_neg]
  have hsq : (-gammaSEqual y) ^ 2 = gammaSEqual y ^ 2 := by ring
  rw [hsq]
  have hW := weightNumer_eq y
  field_simp [hg] at hW ⊢
  linarith

lemma phaseWeight_strictAnti :
    StrictAntiOn phaseWeight (Ioo resonanceRoot1 (branchNode 1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) ?_ ?_
  · unfold phaseWeight
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (by continuity : Continuous fun y : ℝ => 2 * y * cosh y * sin y).continuousOn
    · exact continuous_gammaSEqual.neg.continuousOn
    · intro y hy
      simpa using (gammaSEqual_neg_first_shell hy).ne
  · intro y hy
    rw [interior_Ioo] at hy
    have hg : gammaSEqual y ≠ 0 := (gammaSEqual_neg_first_shell hy).ne
    rw [(hasDerivAt_phaseWeight hg).deriv]
    exact div_neg_of_neg_of_pos (phaseLogNum_neg hy) (by positivity)

/-! ### Scaled ratios and the cube -/

noncomputable def scaledRatio (c x : ℝ) : ℝ :=
  gammaSEqual x / gammaSEqual (c * x)

noncomputable def cubeEdge : ℝ := sqrt 3 / 2

noncomputable def cubeFace : ℝ := sqrt 6 / 4

noncomputable def cubeCoeffEdge : ℝ := 3 * sqrt 3 / 4

noncomputable def cubeCoeffFace : ℝ := 3 * sqrt 6 / 8

noncomputable def cubeCoeffBody : ℝ := 1 / 4

noncomputable def cubeResponse (x : ℝ) : ℝ :=
  cubeCoeffEdge * scaledRatio cubeEdge x +
    cubeCoeffFace * scaledRatio cubeFace x +
    cubeCoeffBody * scaledRatio (1 / 2) x

noncomputable def cubeOutward (Z x : ℝ) : ℝ :=
  -Z / gammaSEqual x +
    cubeCoeffEdge / gammaSEqual (cubeEdge * x) +
    cubeCoeffFace / gammaSEqual (cubeFace * x) +
    cubeCoeffBody / gammaSEqual (x / 2)

lemma sqrt_three_lt_twentySix_fifteenths : sqrt 3 < 26 / 15 := by
  have hsq : (sqrt 3) ^ 2 < (26 / 15) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  have habs : |sqrt 3| < |(26 / 15 : ℝ)| := (sq_lt_sq).1 hsq
  rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 26 / 15)] at habs

lemma sqrt_six_lt_five_halves : sqrt 6 < 5 / 2 := by
  have hsq : (sqrt 6) ^ 2 < (5 / 2) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  have habs : |sqrt 6| < |(5 / 2 : ℝ)| := (sq_lt_sq).1 hsq
  rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2)] at habs

lemma sqrt_three_gt_oneSevenThree : 173 / 100 < sqrt 3 := by
  have hsq : (173 / 100 : ℝ) ^ 2 < (sqrt 3) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  have habs : |(173 / 100 : ℝ)| < |sqrt 3| := (sq_lt_sq).1 hsq
  rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 173 / 100), abs_of_nonneg (sqrt_nonneg _)] at habs

lemma cubeScale_mem_Ioo : 1 / 2 < cubeFace ∧ cubeFace < cubeEdge ∧ cubeEdge < 1 := by
  unfold cubeFace cubeEdge
  refine ⟨?_, ?_, ?_⟩
  · have h6 : (2 : ℝ) < sqrt 6 := by
      have hsq : (2 : ℝ) ^ 2 < (sqrt 6) ^ 2 := by
        rw [sq_sqrt (by norm_num)]
        norm_num
      have habs : |(2 : ℝ)| < |sqrt 6| := (sq_lt_sq).1 hsq
      rwa [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sqrt_nonneg _)] at habs
    nlinarith
  · have h : sqrt 6 / 2 < sqrt 3 := by
      have hsq : (sqrt 6 / 2) ^ 2 < (sqrt 3) ^ 2 := by
        rw [div_pow, sq_sqrt (by norm_num), sq_sqrt (by norm_num)]
        norm_num
      have habs : |sqrt 6 / 2| < |sqrt 3| := (sq_lt_sq).1 hsq
      rwa [abs_of_nonneg (div_nonneg (sqrt_nonneg _) (by norm_num)),
        abs_of_nonneg (sqrt_nonneg _)] at habs
    nlinarith
  · nlinarith [sqrt_three_lt_twentySix_fifteenths]

lemma cubeCoeff_pos : 0 < cubeCoeffEdge ∧ 0 < cubeCoeffFace ∧ 0 < cubeCoeffBody := by
  unfold cubeCoeffEdge cubeCoeffFace cubeCoeffBody
  refine ⟨?_, ?_, by norm_num⟩
  · positivity
  · positivity

lemma cube_phases_in_shell {x : ℝ}
    (hx : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1)) :
    gammaSEqual x < 0 ∧ gammaSEqual (cubeEdge * x) < 0 ∧
      gammaSEqual (cubeFace * x) < 0 ∧ gammaSEqual (x / 2) < 0 := by
  have hedge : resonanceRoot1 < cubeEdge * x ∧ cubeEdge * x < branchNode 1 := by
    have hc := cubeScale_mem_Ioo
    have hx0 : 0 < x := by linarith [hx.1, resonanceRoot1_bounds.1]
    refine ⟨?_, ?_⟩
    · have hhalf : resonanceRoot1 < x / 2 := by
        rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith [hx.1]
      have hlt : x / 2 < cubeEdge * x := by nlinarith [hc.1, hc.2.1, hx0]
      exact lt_trans hhalf hlt
    · nlinarith [hc.2.2, hx.2, hx0]
  have hface : resonanceRoot1 < cubeFace * x ∧ cubeFace * x < branchNode 1 := by
    have hc := cubeScale_mem_Ioo
    have hx0 : 0 < x := by linarith [hx.1, resonanceRoot1_bounds.1]
    refine ⟨?_, ?_⟩
    · nlinarith [hc.1, hx.1, hx0]
    · nlinarith [hc.2.1, hc.2.2, hx.2, hx0]
  exact ⟨gammaSEqual_neg_first_shell ⟨by linarith [hx.1, four_fifths_lt_resonanceRoot1], hx.2⟩,
    gammaSEqual_neg_first_shell ⟨hedge.1, hedge.2⟩,
    gammaSEqual_neg_first_shell ⟨hface.1, hface.2⟩,
    halfPhase_in_firstShell hx⟩

lemma scaledRatioSlope_eq_weight {c x : ℝ} (_hc : 0 < c) (hx : 0 < x)
    (hg : gammaSEqual x ≠ 0) (hgc : gammaSEqual (c * x) ≠ 0) :
    deriv gammaSEqual x * gammaSEqual (c * x) -
        gammaSEqual x * (deriv gammaSEqual (c * x) * c) =
      gammaSEqual x * gammaSEqual (c * x) *
        (phaseWeight x - phaseWeight (c * x)) / x := by
  rw [deriv_gammaSEqual, deriv_gammaSEqual]
  unfold phaseWeight
  field_simp [hg, hgc, hx.ne']

lemma hasDerivAt_scaledRatio {c x : ℝ} (hgc : gammaSEqual (c * x) ≠ 0) :
    HasDerivAt (scaledRatio c)
      ((deriv gammaSEqual x * gammaSEqual (c * x) -
        gammaSEqual x * (deriv gammaSEqual (c * x) * c)) /
          gammaSEqual (c * x) ^ 2) x := by
  unfold scaledRatio
  have hmul : HasDerivAt (fun t => c * t) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hcomp := (hasDerivAt_gammaSEqual (c * x)).comp x hmul
  have hdiv := (hasDerivAt_gammaSEqual x).div hcomp hgc
  refine hdiv.congr_deriv ?_
  rw [deriv_gammaSEqual, deriv_gammaSEqual]
  simp only [Function.comp_apply]

lemma scaledRatio_strictAnti {c : ℝ} (hc0 : 1 / 2 ≤ c) (hc1 : c < 1) :
    StrictAntiOn (scaledRatio c) (Ioo (2 * resonanceRoot1) (branchNode 1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) ?_ ?_
  · unfold scaledRatio
    refine ContinuousOn.div continuous_gammaSEqual.continuousOn ?_ ?_
    · exact (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn
    · intro y hy
      have hy0 : 0 < y := by linarith [hy.1, resonanceRoot1_bounds.1]
      have hcy_lo : resonanceRoot1 < c * y := by
        have hhalf : resonanceRoot1 < y / 2 := by
          rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
          linarith [hy.1]
        nlinarith [hc0, hy0, hhalf]
      have hcy_hi : c * y < branchNode 1 := by nlinarith [hc1, hy.2, hy0]
      exact (gammaSEqual_neg_first_shell ⟨hcy_lo, hcy_hi⟩).ne
  · intro y hy
    rw [interior_Ioo] at hy
    have hy0 : 0 < y := by linarith [hy.1, resonanceRoot1_bounds.1]
    have hcy : c * y < y := by nlinarith [hc1, hy0]
    have hcy_lo : resonanceRoot1 < c * y := by
      have hhalf : resonanceRoot1 < y / 2 := by
        rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith [hy.1]
      nlinarith [hc0, hy0, hhalf]
    have hcy_hi : c * y < branchNode 1 := by nlinarith [hc1, hy.2, hy0]
    have hmemc : c * y ∈ Ioo resonanceRoot1 (branchNode 1) := ⟨hcy_lo, hcy_hi⟩
    have hmemy : y ∈ Ioo resonanceRoot1 (branchNode 1) :=
      ⟨by linarith [hy.1, four_fifths_lt_resonanceRoot1], hy.2⟩
    have hweight : phaseWeight y < phaseWeight (c * y) :=
      phaseWeight_strictAnti hmemc hmemy hcy
    have hgc : gammaSEqual (c * y) ≠ 0 := (gammaSEqual_neg_first_shell hmemc).ne
    have hg : gammaSEqual y ≠ 0 := (gammaSEqual_neg_first_shell hmemy).ne
    have hcpos : 0 < c := by linarith
    rw [(hasDerivAt_scaledRatio hgc).deriv, scaledRatioSlope_eq_weight hcpos hy0 hg hgc]
    have hden : 0 < gammaSEqual (c * y) ^ 2 := sq_pos_of_ne_zero hgc
    have hprod : gammaSEqual y * gammaSEqual (c * y) > 0 :=
      mul_pos_of_neg_of_neg (gammaSEqual_neg_first_shell hmemy)
        (gammaSEqual_neg_first_shell hmemc)
    have hdiff : phaseWeight y - phaseWeight (c * y) < 0 := by linarith
    have hnum : gammaSEqual y * gammaSEqual (c * y) *
        (phaseWeight y - phaseWeight (c * y)) / y < 0 := by
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hprod hdiff) hy0
    exact div_neg_of_neg_of_pos hnum hden

lemma strictAntiOn_const_mul {c : ℝ} {f : ℝ → ℝ} {s : Set ℝ}
    (hc : 0 < c) (hf : StrictAntiOn f s) : StrictAntiOn (fun x => c * f x) s := by
  intro x hx y hy hxy
  exact mul_lt_mul_of_pos_left (hf hx hy hxy) hc

lemma strictAntiOn_add {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : StrictAntiOn f s) (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x + g x) s := by
  intro x hx y hy hxy
  linarith [hf hx hy hxy, hg hx hy hxy]

lemma cubeResponse_strictAnti :
    StrictAntiOn cubeResponse (Ioo (2 * resonanceRoot1) (branchNode 1)) := by
  have hscale := cubeScale_mem_Ioo
  have hedge := scaledRatio_strictAnti (c := cubeEdge) (by nlinarith [hscale.1, hscale.2.1]) hscale.2.2
  have hface := scaledRatio_strictAnti (c := cubeFace) (by nlinarith [hscale.1]) (by nlinarith [hscale.2.1])
  have hbody := scaledRatio_strictAnti (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hcoeff := cubeCoeff_pos
  unfold cubeResponse
  exact strictAntiOn_add
    (strictAntiOn_add (strictAntiOn_const_mul hcoeff.1 hedge)
      (strictAntiOn_const_mul hcoeff.2.1 hface))
    (strictAntiOn_const_mul hcoeff.2.2 hbody)

lemma gammaSEqual_seven_halves_lt_neg_six : gammaSEqual (7 / 2) < -6 := by
  have hδlo : (358 / 1000 : ℝ) ≤ 7 / 2 - π := by linarith [pi_lt_d6]
  have hδhi : 7 / 2 - π ≤ 359 / 1000 := by linarith [pi_gt_d6]
  have hexp : (32 : ℝ) < exp (7 / 2) := by
    have hid : exp (7 / 2) = exp 3 * exp (1 / 2) := by
      rw [show (7 / 2 : ℝ) = 3 + 1 / 2 by norm_num, exp_add]
    have h3 : (197 / 10 : ℝ) < exp 3 := by
      have hid3 : exp 3 = exp 2 * exp 1 := by
        rw [show (3 : ℝ) = 2 + 1 by norm_num, exp_add]
      nlinarith [exp_one_sq_bounds.1, exp_one_gt_271, exp_pos 1, exp_pos 2]
    nlinarith [exp_half_bounds.1, h3, exp_pos (1 / 2), exp_pos 3]
  have hsin := sin_mem_bounds (a := 358 / 1000) (b := 359 / 1000)
    (by norm_num) (by norm_num) hδlo hδhi
  have hcos := cos_mem_bounds (a := 358 / 1000) (b := 359 / 1000)
    (by norm_num) (by norm_num) hδlo hδhi
  have hDhi : sin (7 / 2 - π) - cos (7 / 2 - π) ≤
      sinHi (359 / 1000) - cosLo (359 / 1000) := by linarith [hsin.2, hcos.1]
  have hDneg : sinHi (359 / 1000) - cosLo (359 / 1000) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hbound : (32 / 2) * (sinHi (359 / 1000) - cosLo (359 / 1000)) < -6 := by
    simp only [sinHi, cosLo]; norm_num
  have hid : gammaSEqual (7 / 2) =
      exp (7 / 2) / 2 * (sin (7 / 2 - π) - cos (7 / 2 - π)) -
        exp (-(7 / 2)) / 2 * (sin (7 / 2 - π) + cos (7 / 2 - π)) := by
    rw [gammaSEqual_exp]
    have hsinx : sin (7 / 2) = -sin (7 / 2 - π) := by
      conv_lhs => rw [show (7 / 2 : ℝ) = (7 / 2 - π) + π by ring]
      rw [sin_add_pi]
    have hcosx : cos (7 / 2) = -cos (7 / 2 - π) := by
      conv_lhs => rw [show (7 / 2 : ℝ) = (7 / 2 - π) + π by ring]
      rw [cos_add_pi]
    rw [hsinx, hcosx]
    ring
  have hsub : 0 < exp (-(7 / 2)) / 2 * (sin (7 / 2 - π) + cos (7 / 2 - π)) := by
    have hS : 0 < sin (7 / 2 - π) + cos (7 / 2 - π) := by
      linarith [hsin.1, hcos.1, show (0 : ℝ) < sinLo (358 / 1000) (359 / 1000) +
        cosLo (359 / 1000) by simp only [sinLo, cosLo]; norm_num]
    positivity
  have hfirst : exp (7 / 2) / 2 * (sin (7 / 2 - π) - cos (7 / 2 - π)) ≤
      (32 / 2) * (sinHi (359 / 1000) - cosLo (359 / 1000)) := by
    have hstep : exp (7 / 2) / 2 * (sinHi (359 / 1000) - cosLo (359 / 1000)) ≤
        (32 / 2) * (sinHi (359 / 1000) - cosLo (359 / 1000)) := by
      nlinarith [hexp, hDneg]
    have hcmp : exp (7 / 2) / 2 * (sin (7 / 2 - π) - cos (7 / 2 - π)) ≤
        exp (7 / 2) / 2 * (sinHi (359 / 1000) - cosLo (359 / 1000)) := by
      have hcoef : 0 < exp (7 / 2) / 2 := by positivity
      exact mul_le_mul_of_nonneg_left hDhi hcoef.le
    exact le_trans hcmp hstep
  linarith [hid, hfirst, hsub, hbound]

lemma gammaSEqual_eleven_fifths_lt : gammaSEqual (11 / 5) < -6 := by
  have hεlo : (62 / 100 : ℝ) ≤ 11 / 5 - π / 2 := by linarith [pi_lt_d6]
  have hεhi : 11 / 5 - π / 2 ≤ 64 / 100 := by linarith [pi_gt_d6]
  have hexp_lo : (89 / 10 : ℝ) < exp (11 / 5) := by
    have hid : exp (11 / 5) = exp 2 * exp (1 / 5) := by
      rw [show (11 / 5 : ℝ) = 2 + 1 / 5 by norm_num, exp_add]
    nlinarith [exp_one_sq_bounds.1, exp_fifth_bounds.1, exp_pos 2, exp_pos (1 / 5)]
  have hexp_hi : exp (11 / 5) < 93 / 10 := by
    have hid : exp (11 / 5) = exp 2 * exp (1 / 5) := by
      rw [show (11 / 5 : ℝ) = 2 + 1 / 5 by norm_num, exp_add]
    nlinarith [exp_one_sq_bounds.2, exp_fifth_bounds.2, exp_pos 2, exp_pos (1 / 5)]
  have hD : -(sinLo (62 / 100) (64 / 100) + cosLo (64 / 100)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (64 / 100) + cosLo (64 / 100) := by
    simp only [sinHi, cosLo]; norm_num
  have hbounds := gamma_after (x := 11 / 5) (ε := 11 / 5 - π / 2)
      (a := 62 / 100) (b := 64 / 100) (E0 := 89 / 10) (E1 := 93 / 10)
      (by ring) (by norm_num) (by norm_num) hεlo hεhi (by norm_num)
      hexp_lo.le hexp_hi.le hD hS
  have hgu : gammaUpper (89 / 10)
      (-(sinLo (62 / 100) (64 / 100) + cosLo (64 / 100)))
      (-sinLo (62 / 100) (64 / 100) + cosHi (62 / 100) (64 / 100)) < -6 := by
    simp only [gammaUpper, sinLo, cosLo, cosHi]; norm_num
  linarith [hbounds.2]

lemma gammaSEqual_thirtyNine_tenths_gt : -3 / 2 < gammaSEqual (39 / 10) := by
  have hδlo : (758 / 1000 : ℝ) ≤ 39 / 10 - π := by linarith [pi_lt_d6]
  have hδhi : 39 / 10 - π ≤ 760 / 1000 := by linarith [pi_gt_d6]
  have hexp_hi : exp (39 / 10) < 50 := by
    have hid : exp (39 / 10) = exp 4 / exp (1 / 10) := by
      rw [show (39 / 10 : ℝ) = 4 - 1 / 10 by norm_num, exp_sub]
    have h4 : exp 4 < (74 / 10) ^ 2 := by
      have hid4 : exp 4 = exp 2 * exp 2 := by
        rw [show (4 : ℝ) = 2 + 2 by norm_num, exp_add]
      nlinarith [exp_one_sq_bounds.2, exp_pos 2]
    have h10 : (11 / 10 : ℝ) < exp (1 / 10) := exp_tenth_bounds.1
    rw [hid]
    refine (div_lt_iff₀ (exp_pos _)).2 ?_
    nlinarith [h4, h10]
  have hexp_lo : (48 : ℝ) < exp (39 / 10) := by
    have hid : exp (39 / 10) = exp 4 / exp (1 / 10) := by
      rw [show (39 / 10 : ℝ) = 4 - 1 / 10 by norm_num, exp_sub]
    have h4 : (73 / 10) ^ 2 < exp 4 := by
      have hid4 : exp 4 = exp 2 * exp 2 := by
        rw [show (4 : ℝ) = 2 + 2 by norm_num, exp_add]
      nlinarith [exp_one_sq_bounds.1, exp_pos 2]
    have h10 : exp (1 / 10) < 111 / 100 := exp_tenth_bounds.2
    rw [hid]
    refine (lt_div_iff₀ (exp_pos _)).2 ?_
    nlinarith [h4, h10]
  have hsin := sin_mem_bounds (a := 758 / 1000) (b := 760 / 1000)
    (by norm_num) (by norm_num) hδlo hδhi
  have hcos := cos_mem_bounds (a := 758 / 1000) (b := 760 / 1000)
    (by norm_num) (by norm_num) hδlo hδhi
  have hDlo : sinLo (758 / 1000) (760 / 1000) - cosHi (758 / 1000) (760 / 1000) ≤
      sin (39 / 10 - π) - cos (39 / 10 - π) := by linarith [hsin.1, hcos.2]
  have hShi : sin (39 / 10 - π) + cos (39 / 10 - π) ≤
      sinHi (760 / 1000) + cosHi (758 / 1000) (760 / 1000) := by linarith [hsin.2, hcos.2]
  have hDneg : sinLo (758 / 1000) (760 / 1000) - cosHi (758 / 1000) (760 / 1000) < 0 := by
    simp only [sinLo, cosHi]; norm_num
  have hlow : -3 / 2 < (50 / 2) * (sinLo (758 / 1000) (760 / 1000) -
      cosHi (758 / 1000) (760 / 1000)) -
      (sinHi (760 / 1000) + cosHi (758 / 1000) (760 / 1000)) / (2 * 48) := by
    simp only [sinLo, sinHi, cosHi]; norm_num
  have hid : gammaSEqual (39 / 10) =
      exp (39 / 10) / 2 * (sin (39 / 10 - π) - cos (39 / 10 - π)) -
        exp (-(39 / 10)) / 2 * (sin (39 / 10 - π) + cos (39 / 10 - π)) := by
    rw [gammaSEqual_exp]
    have hsinx : sin (39 / 10) = -sin (39 / 10 - π) := by
      conv_lhs => rw [show (39 / 10 : ℝ) = (39 / 10 - π) + π by ring]
      rw [sin_add_pi]
    have hcosx : cos (39 / 10) = -cos (39 / 10 - π) := by
      conv_lhs => rw [show (39 / 10 : ℝ) = (39 / 10 - π) + π by ring]
      rw [cos_add_pi]
    rw [hsinx, hcosx]
    ring
  have hinv : exp (-(39 / 10)) ≤ 1 / 48 := by
    have hdiv : 1 / exp (39 / 10) ≤ 1 / 48 :=
      one_div_le_one_div_of_le (by norm_num) hexp_lo.le
    simpa [exp_neg, one_div] using hdiv
  have hDact : sin (39 / 10 - π) - cos (39 / 10 - π) < 0 := by
    have hup : sin (39 / 10 - π) - cos (39 / 10 - π) ≤
        sinHi (760 / 1000) - cosLo (760 / 1000) := by linarith [hsin.2, hcos.1]
    have hneg : sinHi (760 / 1000) - cosLo (760 / 1000) < 0 := by
      simp only [sinHi, cosLo]; norm_num
    linarith
  have hfirst : (50 / 2) * (sinLo (758 / 1000) (760 / 1000) -
      cosHi (758 / 1000) (760 / 1000)) ≤
      exp (39 / 10) / 2 * (sin (39 / 10 - π) - cos (39 / 10 - π)) := by
    have hstep : (50 / 2) * (sin (39 / 10 - π) - cos (39 / 10 - π)) ≤
        exp (39 / 10) / 2 * (sin (39 / 10 - π) - cos (39 / 10 - π)) := by
      nlinarith [hexp_hi, hDact]
    have hcmp : (50 / 2) * (sinLo (758 / 1000) (760 / 1000) -
        cosHi (758 / 1000) (760 / 1000)) ≤
        (50 / 2) * (sin (39 / 10 - π) - cos (39 / 10 - π)) := by
      nlinarith [hDlo]
    exact le_trans hcmp hstep
  have hsecond : exp (-(39 / 10)) / 2 * (sin (39 / 10 - π) + cos (39 / 10 - π)) ≤
      (sinHi (760 / 1000) + cosHi (758 / 1000) (760 / 1000)) / (2 * 48) := by
    have hS0 : 0 ≤ sin (39 / 10 - π) + cos (39 / 10 - π) := by
      have hpos : 0 < sinLo (758 / 1000) (760 / 1000) + cosLo (760 / 1000) := by
        simp only [sinLo, cosLo]; norm_num
      linarith [hsin.1, hcos.1, hpos]
    have hmul : exp (-(39 / 10)) * (sin (39 / 10 - π) + cos (39 / 10 - π)) ≤
        (1 / 48) * (sinHi (760 / 1000) + cosHi (758 / 1000) (760 / 1000)) := by
      exact mul_le_mul hinv hShi hS0 (by norm_num)
    have heq : (sinHi (760 / 1000) + cosHi (758 / 1000) (760 / 1000)) / (2 * 48) =
        ((1 / 48) * (sinHi (760 / 1000) + cosHi (758 / 1000) (760 / 1000))) / 2 := by ring
    rw [heq]
    linarith
  linarith [hid, hfirst, hsecond, hlow]

lemma continuousOn_cubeResponse :
    ContinuousOn cubeResponse (Ioo (2 * resonanceRoot1) (branchNode 1)) := by
  unfold cubeResponse scaledRatio
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.div continuous_gammaSEqual.continuousOn
      (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_
    intro x hx
    exact (cube_phases_in_shell hx).2.1.ne
  · refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.div continuous_gammaSEqual.continuousOn
      (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_
    intro x hx
    exact (cube_phases_in_shell hx).2.2.1.ne
  · refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.div continuous_gammaSEqual.continuousOn
      (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_
    intro x hx
    have hsame : x / 2 = (1 / 2) * x := by ring
    rw [← hsame]
    exact (cube_phases_in_shell hx).2.2.2.ne

lemma cubeOutward_eq_response {Z x : ℝ}
    (hx : gammaSEqual x ≠ 0) (he : gammaSEqual (cubeEdge * x) ≠ 0)
    (hf : gammaSEqual (cubeFace * x) ≠ 0) (hb : gammaSEqual (x / 2) ≠ 0) :
    cubeOutward Z x = (cubeResponse x - Z) / gammaSEqual x := by
  unfold cubeOutward cubeResponse scaledRatio
  field_simp [hx, he, hf, hb]
  ring

lemma cubeResponse_gt_near_outer {Z : ℝ} (hZ : 1 ≤ Z) :
    Z < cubeResponse (2 * (resonanceRoot1 + 1 / (40 * Z))) := by
  have hZ0 : 0 < Z := by linarith
  set h : ℝ := 1 / (40 * Z) with hh
  have hh0 : 0 < h := by positivity
  have hx1 : resonanceRoot1 < resonanceRoot1 + h := by linarith
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope gammaSEqual (deriv gammaSEqual) hx1
    continuous_gammaSEqual.continuousOn (fun y _ => by
      simpa [deriv_gammaSEqual] using hasDerivAt_gammaSEqual y)
  have hzero : gammaSEqual resonanceRoot1 = 0 := resonanceRoot1_gammaSEqual_zero
  have hval : gammaSEqual (resonanceRoot1 + h) = deriv gammaSEqual c * h := by
    have hs := hslope.symm
    rw [hzero, sub_zero] at hs
    have hsub : resonanceRoot1 + h - resonanceRoot1 = h := by ring
    rw [hsub] at hs
    field_simp [hh0.ne'] at hs
    linarith
  have hh1 : h ≤ 1 / 40 := by
    rw [hh, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hc0 : 0 ≤ c := by linarith [resonanceRoot1_bounds.1, hc.1]
  have hc2 : c < 2 := by linarith [hc.2, resonanceRoot1_sharp_bounds.2, hh1]
  have hcosh : cosh c < 5 := by
    have hle : cosh c ≤ cosh 2 := (cosh_le_cosh).mpr (by
      rw [abs_of_nonneg hc0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact le_of_lt hc2)
    linarith [hle, cosh_two_lt_five]
  have hsin0 : 0 ≤ sin c :=
    sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [hc2, pi_gt_three])
  have hmag : 2 * cosh c * sin c < 10 := by
    have hsin : sin c ≤ 1 := sin_le_one c
    have hcoef : 0 ≤ 2 * cosh c := by linarith [cosh_pos c]
    have hlin : 2 * cosh c * sin c ≤ 2 * cosh c := by
      simpa using mul_le_mul_of_nonneg_left hsin hcoef
    linarith [hcosh, hlin]
  have hsmall : -gammaSEqual (resonanceRoot1 + h) < 10 * h := by
    rw [hval, deriv_gammaSEqual]
    nlinarith [hmag, hh0]
  set x : ℝ := 2 * (resonanceRoot1 + h)
  have hxbig : 8 / 5 < x := by
    dsimp [x]; linarith [four_fifths_lt_resonanceRoot1]
  have hxπ : x < π := by
    dsimp [x]; linarith [resonanceRoot1_sharp_bounds.2, pi_gt_three, hh1]
  have hmemL : (8 / 5 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, by linarith [pi_gt_three]⟩
  have hmemx : x ∈ Icc (0 : ℝ) π :=
    ⟨by dsimp [x]; linarith [resonanceRoot1_bounds.1], hxπ.le⟩
  have hγx : gammaSEqual x < gammaSEqual (8 / 5) :=
    strictAntiOn_gammaSEqual_even 0 (by simpa using hmemL) (by simpa using hmemx) hxbig
  have hγlt : gammaSEqual x < -1 := by linarith [hγx, gammaSEqual_eight_fifths_lt]
  have harg : x / 2 = resonanceRoot1 + h := by dsimp [x]; ring
  have hhalf_gt : -(10 * h) < gammaSEqual (x / 2) := by
    rw [harg]; linarith [hsmall]
  have hhalf_lt : gammaSEqual (x / 2) < 0 := by
    rw [harg]
    exact gammaSEqual_neg_right_of_first_node ⟨lt_add_of_pos_right _ hh0,
      by linarith [resonanceRoot1_sharp_bounds.2, hh1, pi_gt_three]⟩
  have hratio : 1 / (10 * h) < gammaSEqual x / gammaSEqual (x / 2) := by
    rw [lt_div_iff_of_neg hhalf_lt]
    have hright : -1 < (1 / (10 * h)) * gammaSEqual (x / 2) := by
      have hid : (1 / (10 * h)) * (-(10 * h)) = -1 := by field_simp [hh0.ne']
      nlinarith [hhalf_gt, hid, hh0]
    linarith [hγlt]
  have hshell : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1) := by
    refine ⟨by dsimp [x]; linarith, ?_⟩
    have hnode : π < branchNode 1 := by
      simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1
    dsimp [x]; linarith [hxπ, hnode]
  have hphases := cube_phases_in_shell hshell
  have hbody : cubeCoeffBody * scaledRatio (1 / 2) x < cubeResponse x := by
    unfold cubeResponse
    have hE : 0 < cubeCoeffEdge * scaledRatio cubeEdge x := by
      unfold scaledRatio
      exact mul_pos cubeCoeff_pos.1 (div_pos_of_neg_of_neg hphases.1 hphases.2.1)
    have hF : 0 < cubeCoeffFace * scaledRatio cubeFace x := by
      unfold scaledRatio
      exact mul_pos cubeCoeff_pos.2.1 (div_pos_of_neg_of_neg hphases.1 hphases.2.2.1)
    linarith
  have hscale : cubeCoeffBody * (gammaSEqual x / gammaSEqual (x / 2)) =
      (1 / 4) * (gammaSEqual x / gammaSEqual (x / 2)) := by
    unfold cubeCoeffBody; ring
  have hquarter : Z < (1 / 4) * (gammaSEqual x / gammaSEqual (x / 2)) := by
    have hlt : (1 / 4) * (1 / (10 * h)) < (1 / 4) * (gammaSEqual x / gammaSEqual (x / 2)) := by
      exact mul_lt_mul_of_pos_left hratio (by norm_num)
    have hZeq : Z = (1 / 4) * (1 / (10 * h)) := by
      rw [hh]; field_simp; ring
    linarith
  have hsame : x / 2 = (1 / 2) * x := by ring
  have hquarter' : Z < cubeCoeffBody * scaledRatio (1 / 2) x := by
    unfold scaledRatio cubeCoeffBody
    rw [← hsame]
    linarith [hquarter]
  linarith [hquarter', hbody]

lemma cubeResponse_thirtyNine_tenths_lt : cubeResponse (39 / 10) < 1 := by
  have hnode : (39 / 10 : ℝ) < branchNode 1 := by
    have hlo : π + π / 4 < branchNode 1 := by
      have h := node_mem_sharp_branch 1 (branchNode_spec 1).1 (branchNode_spec 1).2
      simpa [Nat.cast_one, one_mul] using h.1
    linarith [pi_gt_d6, hlo]
  have hmem : (39 / 10 : ℝ) ∈ Ioo (2 * resonanceRoot1) (branchNode 1) := by
    refine ⟨by linarith [resonanceRoot1_sharp_bounds.2], hnode⟩
  have hphases := cube_phases_in_shell hmem
  have hπ : π < 7 / 2 := by linarith [pi_lt_d6]
  have hnode72 : (7 / 2 : ℝ) < branchNode 1 := by
    have hlo : π + π / 4 < branchNode 1 := by
      have h := node_mem_sharp_branch 1 (branchNode_spec 1).1 (branchNode_spec 1).2
      simpa [Nat.cast_one, one_mul] using h.1
    linarith [pi_gt_three, hlo]
  have hedge_hi : cubeEdge * (39 / 10) < 7 / 2 := by
    unfold cubeEdge
    have hsqrt : sqrt 3 < 70 / 39 := by
      have hsq : (sqrt 3) ^ 2 < (70 / 39) ^ 2 := by
        rw [sq_sqrt (by norm_num)]; norm_num
      have habs : |sqrt 3| < |(70 / 39 : ℝ)| := (sq_lt_sq).1 hsq
      rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 70 / 39)] at habs
    nlinarith [hsqrt]
  have hedge_lo : π < cubeEdge * (39 / 10) := by
    unfold cubeEdge
    have hrat : π < (173 / 100) * (39 / 20) := by nlinarith [pi_lt_d6]
    have hmul : (173 / 100) * (39 / 20) < sqrt 3 * (39 / 20) := by
      nlinarith [sqrt_three_gt_oneSevenThree]
    linarith
  have hγe : gammaSEqual (cubeEdge * (39 / 10)) < gammaSEqual (7 / 2) := by
    have hleft : cubeEdge * (39 / 10) ∈ Icc π (π + π) :=
      ⟨hedge_lo.le, by linarith [hedge_hi, pi_gt_three]⟩
    have hright : (7 / 2 : ℝ) ∈ Icc π (π + π) := ⟨hπ.le, by linarith [pi_gt_three]⟩
    exact strictMonoOn_gammaSEqual_odd 0 (by simpa using hleft) (by simpa using hright) hedge_hi
  have hγe6 : gammaSEqual (cubeEdge * (39 / 10)) < -6 := by
    linarith [hγe, gammaSEqual_seven_halves_lt_neg_six]
  have hface_lo : 11 / 5 < cubeFace * (39 / 10) := by
    unfold cubeFace
    have hsqrt : 88 / 39 < sqrt 6 := by
      have hsq : (88 / 39 : ℝ) ^ 2 < (sqrt 6) ^ 2 := by
        rw [sq_sqrt (by norm_num)]; norm_num
      have habs : |(88 / 39 : ℝ)| < |sqrt 6| := (sq_lt_sq).1 hsq
      rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 88 / 39), abs_of_nonneg (sqrt_nonneg _)] at habs
    nlinarith [hsqrt]
  have hface_hi : cubeFace * (39 / 10) < π := by
    unfold cubeFace
    nlinarith [sqrt_six_lt_five_halves, pi_gt_three]
  have hγf : gammaSEqual (cubeFace * (39 / 10)) < gammaSEqual (11 / 5) := by
    have hleft : (11 / 5 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, by linarith [pi_gt_three]⟩
    have hright : cubeFace * (39 / 10) ∈ Icc (0 : ℝ) π :=
      ⟨by nlinarith [hface_lo], hface_hi.le⟩
    exact strictAntiOn_gammaSEqual_even 0 (by simpa using hleft) (by simpa using hright) hface_lo
  have hγf6 : gammaSEqual (cubeFace * (39 / 10)) < -6 := by
    linarith [hγf, gammaSEqual_eleven_fifths_lt]
  have hhalf : (7 / 4 : ℝ) < 39 / 20 := by norm_num
  have hhalfπ : (39 / 20 : ℝ) < π := by linarith [pi_gt_three]
  have hγh : gammaSEqual (39 / 20) < gammaSEqual (7 / 4) := by
    have hleft : (7 / 4 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, by linarith [pi_gt_three]⟩
    have hright : (39 / 20 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, hhalfπ.le⟩
    exact strictAntiOn_gammaSEqual_even 0 (by simpa using hleft) (by simpa using hright) hhalf
  have hγh3 : gammaSEqual (39 / 20) < -3 := by
    linarith [hγh, gamma_seven_quarters_lt]
  have hhalf_same : gammaSEqual ((1 / 2) * (39 / 10)) = gammaSEqual (39 / 20) := by
    congr 1
    norm_num
  have hgx : -3 / 2 < gammaSEqual (39 / 10) := gammaSEqual_thirtyNine_tenths_gt
  have hgx0 : gammaSEqual (39 / 10) < 0 := hphases.1
  have hre : gammaSEqual (39 / 10) / gammaSEqual (cubeEdge * (39 / 10)) < 1 / 4 := by
    have hneg : gammaSEqual (cubeEdge * (39 / 10)) < 0 := by linarith
    rw [div_lt_iff_of_neg hneg]
    nlinarith [hγe6, hgx]
  have hrf : gammaSEqual (39 / 10) / gammaSEqual (cubeFace * (39 / 10)) < 1 / 4 := by
    have hneg : gammaSEqual (cubeFace * (39 / 10)) < 0 := by linarith
    rw [div_lt_iff_of_neg hneg]
    nlinarith [hγf6, hgx]
  have hrh : gammaSEqual (39 / 10) / gammaSEqual ((1 / 2) * (39 / 10)) < 1 / 2 := by
    rw [hhalf_same]
    have hneg : gammaSEqual (39 / 20) < 0 := by linarith
    rw [div_lt_iff_of_neg hneg]
    nlinarith [hγh3, hgx]
  have hA : cubeCoeffEdge < 13 / 10 := by
    unfold cubeCoeffEdge
    nlinarith [sqrt_three_lt_twentySix_fifteenths]
  have hB : cubeCoeffFace < 15 / 16 := by
    unfold cubeCoeffFace
    nlinarith [sqrt_six_lt_five_halves]
  have hposE : 0 < gammaSEqual (39 / 10) / gammaSEqual (cubeEdge * (39 / 10)) :=
    div_pos_of_neg_of_neg hgx0 (by linarith)
  have hposF : 0 < gammaSEqual (39 / 10) / gammaSEqual (cubeFace * (39 / 10)) :=
    div_pos_of_neg_of_neg hgx0 (by linarith)
  have hposH : 0 < gammaSEqual (39 / 10) / gammaSEqual ((1 / 2) * (39 / 10)) :=
    div_pos_of_neg_of_neg hgx0 (by rw [hhalf_same]; linarith)
  have hpe : cubeCoeffEdge * (gammaSEqual (39 / 10) / gammaSEqual (cubeEdge * (39 / 10))) <
      (13 / 10) * (1 / 4) := by
    have h1 := mul_lt_mul_of_pos_right hA hposE
    have h2 := mul_lt_mul_of_pos_left hre (by norm_num : (0 : ℝ) < 13 / 10)
    linarith
  have hpf : cubeCoeffFace * (gammaSEqual (39 / 10) / gammaSEqual (cubeFace * (39 / 10))) <
      (15 / 16) * (1 / 4) := by
    have h1 := mul_lt_mul_of_pos_right hB hposF
    have h2 := mul_lt_mul_of_pos_left hrf (by norm_num : (0 : ℝ) < 15 / 16)
    linarith
  have hph : cubeCoeffBody * (gammaSEqual (39 / 10) / gammaSEqual ((1 / 2) * (39 / 10))) <
      (1 / 4) * (1 / 2) := by
    unfold cubeCoeffBody
    have h2 := mul_lt_mul_of_pos_left hrh (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  unfold cubeResponse scaledRatio
  linarith [hpe, hpf, hph]

theorem exists_unique_cube_shell {Z : ℝ} (hZ : 1 ≤ Z) :
    ∃! x : ℝ, x ∈ Ioo (2 * resonanceRoot1) (branchNode 1) ∧ cubeOutward Z x = 0 := by
  have hZ0 : 0 < Z := by linarith
  set xL : ℝ := 2 * (resonanceRoot1 + 1 / (40 * Z))
  set xR : ℝ := 39 / 10
  have hgt : Z < cubeResponse xL := by
    simpa [xL] using cubeResponse_gt_near_outer hZ
  have hlt : cubeResponse xR < Z := by
    have h1 : cubeResponse xR < 1 := by simpa [xR] using cubeResponse_thirtyNine_tenths_lt
    linarith
  have hxL_hi : xL < xR := by
    dsimp [xL, xR]
    have hh : 1 / (40 * Z) ≤ 1 / 40 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith [resonanceRoot1_sharp_bounds.2]
  have hRmem : xR ∈ Ioo (2 * resonanceRoot1) (branchNode 1) := by
    dsimp [xR]
    refine ⟨by linarith [resonanceRoot1_sharp_bounds.2], ?_⟩
    have hlo : π + π / 4 < branchNode 1 := by
      have h := node_mem_sharp_branch 1 (branchNode_spec 1).1 (branchNode_spec 1).2
      simpa [Nat.cast_one, one_mul] using h.1
    linarith [pi_gt_d6, hlo]
  have hxL_lo : 2 * resonanceRoot1 < xL := by
    dsimp [xL]
    have : 0 < 1 / (40 * Z) := by positivity
    linarith
  have hcont : ContinuousOn (fun t => Z - cubeResponse t) (Icc xL xR) := by
    refine ContinuousOn.sub continuousOn_const ?_
    refine continuousOn_cubeResponse.mono ?_
    intro t ht
    exact ⟨lt_of_lt_of_le hxL_lo ht.1, lt_of_le_of_lt ht.2 hRmem.2⟩
  have hleft : (fun t => Z - cubeResponse t) xL < 0 := by
    simpa using sub_neg.mpr hgt
  have hright : 0 < (fun t => Z - cubeResponse t) xR := by
    simpa using sub_pos.mpr hlt
  obtain ⟨x, hxI, hx0⟩ := intermediate_value_Ioo (le_of_lt hxL_hi) hcont ⟨hleft, hright⟩
  have hxLmem : xL ∈ Ioo (2 * resonanceRoot1) (branchNode 1) := by
    refine ⟨by dsimp [xL]; linarith, ?_⟩
    have hnode : π < branchNode 1 := by
      simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1
    dsimp [xL]
    linarith [resonanceRoot1_sharp_bounds.2, pi_gt_three, hnode,
      show 1 / (40 * Z) ≤ 1 / 40 by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith]
  have hxmem : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1) :=
    ⟨lt_trans hxL_lo hxI.1, lt_trans hxI.2 hRmem.2⟩
  have hzero : cubeOutward Z x = 0 := by
    have hphases := cube_phases_in_shell hxmem
    rw [cubeOutward_eq_response hphases.1.ne hphases.2.1.ne hphases.2.2.1.ne hphases.2.2.2.ne]
    have hresp : cubeResponse x = Z := by
      have hx0' : Z - cubeResponse x = 0 := hx0
      linarith
    rw [hresp]
    field_simp [hphases.1.ne]
    ring
  refine ⟨x, ⟨hxmem, hzero⟩, ?_⟩
  intro y hy
  have hresp (w : ℝ) (hw : w ∈ Ioo (2 * resonanceRoot1) (branchNode 1))
      (h0 : cubeOutward Z w = 0) : cubeResponse w = Z := by
    have hphases := cube_phases_in_shell hw
    have heq := cubeOutward_eq_response (Z := Z) (x := w) hphases.1.ne hphases.2.1.ne
      hphases.2.2.1.ne hphases.2.2.2.ne
    rw [h0] at heq
    have : (cubeResponse w - Z) / gammaSEqual w = 0 := heq.symm
    have hden : gammaSEqual w ≠ 0 := hphases.1.ne
    field_simp [hden] at this
    linarith
  have hxR := hresp x hxmem hzero
  have hyR := hresp y hy.1 hy.2
  exact (cubeResponse_strictAnti.injOn hxmem hy.1 (by rw [hxR, hyR])).symm

theorem cubeOutward_sign {Z x : ℝ}
    (hx : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1)) :
    cubeOutward Z x < 0 ↔ Z < cubeResponse x := by
  have hphases := cube_phases_in_shell hx
  rw [cubeOutward_eq_response hphases.1.ne hphases.2.1.ne hphases.2.2.1.ne hphases.2.2.2.ne]
  have hden : gammaSEqual x < 0 := hphases.1
  constructor
  · intro h
    have : cubeResponse x - Z > 0 := by
      rw [div_lt_iff_of_neg hden] at h
      linarith
    linarith
  · intro h
    rw [div_lt_iff_of_neg hden]
    linarith

/-! ### Seats

A monopole, a dipole, and a traceless quadrupole are vector spaces of dimensions
`1`, `3`, and `5`. The two complementary chiral projectors give one seat on each
mode, so the counts through degrees `0`, `1`, and `2` are `2`, `8`, and `18`.
These integers are not indices of the equal-scale nodes. -/

theorem chiral_projectors :
    Logic.chiralityL * Logic.chiralityR = 0 ∧
      Logic.chiralityR * Logic.chiralityL = 0 ∧
      Logic.chiralityL + Logic.chiralityR = 1 :=
  ⟨chiralityL_mul_chiralityR, chiralityR_mul_chiralityL, Logic.chiralityL_add_chiralityR⟩

def quadVec : Fin 5 → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => !![1, 0, 0; 0, 0, 0; 0, 0, -1]
  | 1 => !![0, 0, 0; 0, 1, 0; 0, 0, -1]
  | 2 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 3 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 4 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]

def quadrupole : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  carrier := {M | M.transpose = M ∧ M.trace = 0}
  add_mem' := by
    intro M N hM hN
    exact ⟨by simp [hM.1, hN.1], by simp [Matrix.trace_add, hM.2, hN.2]⟩
  zero_mem' := by simp
  smul_mem' := by
    intro c M hM
    exact ⟨by simp [hM.1], by simp [Matrix.trace_smul, hM.2]⟩

lemma quadVec_mem (i : Fin 5) : quadVec i ∈ quadrupole := by
  fin_cases i <;>
    · refine ⟨?_, ?_⟩
      · ext a b
        fin_cases a <;> fin_cases b <;> rfl
      · simp [quadVec, Matrix.trace, Fin.sum_univ_three]

noncomputable def quadApply (c : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  c 0 • quadVec 0 + c 1 • quadVec 1 + c 2 • quadVec 2 + c 3 • quadVec 3 + c 4 • quadVec 4

lemma quadApply_mem (c : Fin 5 → ℝ) : quadApply c ∈ quadrupole := by
  unfold quadApply
  refine ⟨?_, ?_⟩
  · simp [Matrix.transpose_add, Matrix.transpose_smul, (quadVec_mem _).1]
  · simp [Matrix.trace_add, Matrix.trace_smul, (quadVec_mem _).2]

noncomputable def quadOf : (Fin 5 → ℝ) →ₗ[ℝ] quadrupole where
  toFun c := ⟨quadApply c, quadApply_mem c⟩
  map_add' c d := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quadApply, quadVec, add_mul] <;> ring
  map_smul' a c := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quadApply, quadVec, mul_assoc] <;> ring

lemma quadOf_surjective : Function.Surjective quadOf := by
  rintro ⟨M, hM⟩
  refine ⟨![M 0 0, M 1 1, M 0 1, M 0 2, M 1 2], ?_⟩
  apply Subtype.ext
  ext i j
  have htr : M 0 0 + M 1 1 + M 2 2 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_three] using hM.2
  have h10 : M 1 0 = M 0 1 := by
    simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hM.1 1) 0).symm
  have h20 : M 2 0 = M 0 2 := by
    simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hM.1 2) 0).symm
  have h21 : M 2 1 = M 1 2 := by
    simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hM.1 2) 1).symm
  fin_cases i <;> fin_cases j <;>
    simp [quadOf, quadApply, quadVec, htr, h10, h20, h21] <;> linarith [htr]

lemma quadOf_injective : Function.Injective quadOf := by
  intro c d h
  have hval : quadApply c = quadApply d := congrArg Subtype.val h
  have hentry (i j : Fin 3) : quadApply c i j = quadApply d i j :=
    congr_fun (congr_fun hval i) j
  ext i
  fin_cases i
  · simpa [quadApply, quadVec] using hentry 0 0
  · simpa [quadApply, quadVec] using hentry 1 1
  · simpa [quadApply, quadVec] using hentry 0 1
  · simpa [quadApply, quadVec] using hentry 0 2
  · simpa [quadApply, quadVec] using hentry 1 2

lemma quadrupole_rank : Module.finrank ℝ quadrupole = 5 := by
  let e : (Fin 5 → ℝ) ≃ₗ[ℝ] quadrupole :=
    LinearEquiv.ofBijective quadOf ⟨quadOf_injective, quadOf_surjective⟩
  rw [← e.finrank_eq]
  exact (Module.finrank_fin_fun ℝ : Module.finrank ℝ (Fin 5 → ℝ) = 5)

theorem shell_seat_counts :
    2 * Module.finrank ℝ ℝ = 2 ∧
      2 * (Module.finrank ℝ ℝ + Module.finrank ℝ (Fin 3 → ℝ)) = 8 ∧
      2 * (Module.finrank ℝ ℝ + Module.finrank ℝ (Fin 3 → ℝ) +
        Module.finrank ℝ quadrupole) = 18 := by
  have h1 : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  have h3 : Module.finrank ℝ (Fin 3 → ℝ) = 3 :=
    (Module.finrank_fin_fun ℝ : Module.finrank ℝ (Fin 3 → ℝ) = 3)
  simp [h1, h3, quadrupole_rank]

end Gravity

end DstDiophantine
