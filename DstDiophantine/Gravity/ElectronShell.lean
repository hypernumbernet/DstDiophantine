import DstDiophantine.Gravity.SI
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Electron shells via Coulombic torsional layers

## Paper boundary (do **not** claim)

Sec.~electronshells rewrites Coulomb with \(\gamma_s\) and places shells at
\(\tanh(\alpha/2)\tan(\beta/2)=1\). Characteristic length \(\ell\) is **not**
a theorem of the dual-rotor algebra. This module records algebraic identities,
an equal-scale diagnostic, and a labelled \(\ell\) envelope.

## Equal-scale diagnostic

Under \(\alpha(r)=\beta(r)=\ell/r\), the dimensionless \(x=\ell/(2r)\) satisfies
\(\tanh x\cdot\tan x=1\). Positive roots lie in branches \((n\pi,\,n\pi+\pi/2)\),
so \(r_n=\ell/(2x_n)=\Theta(1/n)\), **not** \(\Theta(n^2)\). Rydberg \(n^2\)
scaling requires separate Bohr bookkeeping \(r_n=n^2 a_0\).

No theorem asserts `dst_derives_lambda`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

/-! ### Scalar interference factor -/

noncomputable def gammaS (α β : ℝ) : ℝ :=
  cosh (α / 2) * cos (β / 2) - sinh (α / 2) * sin (β / 2)

noncomputable def gammaB (α β : ℝ) : ℝ :=
  -cosh (α / 2) * sin (β / 2) + sinh (α / 2) * cos (β / 2)

noncomputable def gammaEff (α β : ℝ) : ℝ :=
  gammaS α β ^ 2 + gammaB α β ^ 2

theorem gammaS_zero_zero : gammaS 0 0 = 1 := by
  simp [gammaS]

theorem gammaEff_nonneg (α β : ℝ) : 0 ≤ gammaEff α β := by
  unfold gammaEff; positivity

private theorem cosh_half_sq_add (φ : ℝ) :
    cosh (φ / 2) ^ 2 + sinh (φ / 2) ^ 2 = cosh φ := by
  simpa [mul_div_cancel₀ φ (by norm_num : (2 : ℝ) ≠ 0)] using
    (cosh_two_mul (φ / 2)).symm

theorem gammaEff_of_beta_zero (α : ℝ) : gammaEff α 0 = cosh α := by
  unfold gammaEff gammaS gammaB
  simp [cosh_half_sq_add]

private theorem sinh_half_two (φ : ℝ) :
    2 * sinh (φ / 2) * cosh (φ / 2) = sinh φ := by
  simpa [mul_div_cancel₀ φ (by norm_num : (2 : ℝ) ≠ 0)] using
    (sinh_two_mul (φ / 2)).symm

private theorem sin_half_two (φ : ℝ) :
    2 * sin (φ / 2) * cos (φ / 2) = sin φ := by
  simpa [mul_div_cancel₀ φ (by norm_num : (2 : ℝ) ≠ 0)] using
    (sin_two_mul (φ / 2)).symm

/-- Closed form \(\gamma_{\mathrm{eff}}=\cosh\alpha-\sinh\alpha\sin\beta\). -/
theorem gammaEff_closed (α β : ℝ) :
    gammaEff α β = cosh α - sinh α * sin β := by
  unfold gammaEff gammaS gammaB
  set c := cosh (α / 2)
  set s := sinh (α / 2)
  set C := cos (β / 2)
  set S := sin (β / 2)
  have hexpand :
      (c * C - s * S) ^ 2 + (-c * S + s * C) ^ 2 =
        (c ^ 2 + s ^ 2) * (C ^ 2 + S ^ 2) - 4 * c * s * C * S := by
    ring
  have hCS : C ^ 2 + S ^ 2 = 1 := by simp [C, S]
  have hC : c ^ 2 + s ^ 2 = cosh α := by
    simpa [c, s] using cosh_half_sq_add α
  have hS : 2 * s * c = sinh α := by
    simpa [c, s, mul_comm] using sinh_half_two α
  have hsin : 2 * S * C = sin β := by
    simpa [C, S, mul_comm] using sin_half_two β
  rw [hexpand, hCS, mul_one, hC]
  have hcross : 4 * c * s * C * S = sinh α * sin β := by
    have : 4 * c * s * C * S = (2 * s * c) * (2 * S * C) := by ring
    rw [this, hS, hsin]
  rw [hcross]

/-- \(\gamma_{\mathrm{eff}}\ge e^{-|\alpha|}>0\). In particular it never vanishes. -/
theorem gammaEff_pos (α β : ℝ) : 0 < gammaEff α β := by
  rw [gammaEff_closed]
  have habs : |sinh α * sin β| ≤ |sinh α| :=
    calc |sinh α * sin β|
        = |sinh α| * |sin β| := abs_mul _ _
      _ ≤ |sinh α| * 1 :=
        mul_le_mul_of_nonneg_left (abs_sin_le_one β) (abs_nonneg _)
      _ = |sinh α| := by simp
  have hprod : sinh α * sin β ≤ |sinh α| := (abs_le.mp habs).2
  have hid : cosh α - |sinh α| = exp (-|α|) := by
    rcases le_total 0 α with hα | hα
    · have hsinh : 0 ≤ sinh α := by
        rcases eq_or_lt_of_le hα with rfl | hα
        · simp
        · exact (sinh_pos_iff.mpr hα).le
      rw [abs_of_nonneg hα, abs_of_nonneg hsinh, cosh_sub_sinh]
    · have hsinh : sinh α ≤ 0 := by
        rcases eq_or_lt_of_le hα with rfl | hα
        · simp
        · exact sinh_nonpos_iff.mpr hα.le
      rw [abs_of_nonpos hα, abs_of_nonpos hsinh, neg_neg, sub_neg_eq_add,
        cosh_add_sinh]
  have hlower : exp (-|α|) ≤ cosh α - sinh α * sin β := by
    have : cosh α - |sinh α| ≤ cosh α - sinh α * sin β := by linarith [hprod]
    rwa [hid] at this
  exact lt_of_lt_of_le (exp_pos _) hlower

theorem gammaEff_eq_one_of_alpha_zero (β : ℝ) : gammaEff 0 β = 1 := by
  rw [gammaEff_closed]
  simp

/-- Balanced kinematics \(\alpha=\beta\) is not the special-relativistic factor \(\cosh\alpha\). -/
theorem gammaEff_balanced_ne_cosh {α : ℝ} (hα : sin α ≠ 0) (hs : sinh α ≠ 0) :
    gammaEff α α ≠ cosh α := by
  rw [gammaEff_closed]
  intro h
  have : sinh α * sin α = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hs h
  · exact hα h

private theorem tanh_half_eq_of_sinh_ne (x : ℝ) :
    tanh (x / 2) = (cosh x - 1) / sinh x := by
  have htwo : (2 : ℝ) * (x / 2) = x := by ring
  have hsinh : sinh x = 2 * sinh (x / 2) * cosh (x / 2) := by
    simpa [htwo] using sinh_two_mul (x / 2)
  have hcosh : cosh x - 1 = 2 * sinh (x / 2) ^ 2 := by
    have hid : cosh (2 * (x / 2)) = 1 + 2 * sinh (x / 2) ^ 2 := by
      rw [cosh_two_mul]
      nlinarith [cosh_sq (x / 2)]
    have := hid
    rw [htwo] at this
    linarith
  have hden : cosh (x / 2) ≠ 0 := (cosh_pos _).ne'
  rw [tanh_eq_sinh_div_cosh, hcosh, hsinh]
  field_simp [hden]

private theorem tanh_half_one_lt_half : tanh ((1 : ℝ) / 2) < 1 / 2 := by
  have hpos : exp ((1 : ℝ) / 2) ≠ 0 := (exp_pos _).ne'
  have h1 : exp ((1 : ℝ) / 2) * exp ((1 : ℝ) / 2) = exp 1 := by
    rw [← exp_add]; ring_nf
  have h2 : exp ((1 : ℝ) / 2) * exp (-((1 : ℝ) / 2)) = (1 : ℝ) := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  have hform : tanh ((1 : ℝ) / 2) = (exp 1 - 1) / (exp 1 + 1) := by
    rw [tanh_eq, ← mul_div_mul_left _ _ hpos, mul_sub, mul_add, h1, h2]
  have he : exp 1 < (3 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [hform, div_lt_iff₀ (by linarith [exp_pos (1 : ℝ)])]
  linarith [exp_pos (1 : ℝ), he]

private theorem one_lt_pi_div_two' : (1 : ℝ) < π / 2 := by
  linarith [pi_gt_three]

private theorem pi_div_six_lt_one : π / 6 < (1 : ℝ) := by
  linarith [pi_lt_four]

theorem sin_one_gt_half : (1 / 2 : ℝ) < sin 1 := by
  have hmono := strictMonoOn_sin
    ⟨le_of_lt (lt_trans (neg_lt_zero.mpr pi_div_two_pos) (div_pos pi_pos (by norm_num))),
      le_of_lt (by linarith [pi_gt_three] : π / 6 < π / 2)⟩
    ⟨le_of_lt (lt_trans (neg_lt_zero.mpr pi_div_two_pos) (by norm_num : (0 : ℝ) < 1)),
      le_of_lt one_lt_pi_div_two'⟩
    pi_div_six_lt_one
  simpa [sin_pi_div_six] using hmono

/-- Balanced kinematics is not the vacuum factor \(1\), already at \(\alpha=\beta=1\). -/
theorem gammaEff_balanced_one_ne_one : gammaEff 1 1 ≠ 1 := by
  rw [gammaEff_closed]
  intro h
  have hs : (0 : ℝ) < sinh 1 := sinh_pos_iff.mpr (by norm_num)
  have hsin : sin 1 = (cosh 1 - 1) / sinh 1 :=
    (eq_div_iff hs.ne').mpr (by linarith)
  have hth : (cosh 1 - 1) / sinh 1 = tanh ((1 : ℝ) / 2) :=
    (tanh_half_eq_of_sinh_ne 1).symm
  have : (1 / 2 : ℝ) < tanh ((1 : ℝ) / 2) := by
    linarith [sin_one_gt_half, hsin, hth]
  exact (lt_irrefl _ (this.trans tanh_half_one_lt_half))

/-- Special relativity is the unexcited dual sector \(\beta=0\), not the locus \(J=0\). -/
theorem gammaEff_sr_is_beta_zero (α : ℝ) :
    gammaEff α 0 = cosh α :=
  gammaEff_of_beta_zero α



theorem gammaS_eq_zero_iff (α β : ℝ) (hc : cos (β / 2) ≠ 0) :
    gammaS α β = 0 ↔ tanh (α / 2) * tan (β / 2) = 1 := by
  have hcosh : cosh (α / 2) ≠ 0 := (cosh_pos _).ne'
  constructor
  · intro h
    have hbal : cosh (α / 2) * cos (β / 2) = sinh (α / 2) * sin (β / 2) := by
      unfold gammaS at h; linarith
    rw [tanh_eq_sinh_div_cosh, tan_eq_sin_div_cos]
    field_simp [hcosh, hc]
    nlinarith [hbal]
  · intro h
    rw [tanh_eq_sinh_div_cosh, tan_eq_sin_div_cos] at h
    field_simp [hcosh, hc] at h
    unfold gammaS
    nlinarith

/-! ### \(Z\)-contraction -/

noncomputable def equalScaleRapidity (ℓ r : ℝ) : ℝ := ℓ / r

theorem equalScale_Z_contraction (ℓ Z r : ℝ) (hZ : Z ≠ 0) :
    equalScaleRapidity (Z * ℓ) r = equalScaleRapidity ℓ (r / Z) := by
  unfold equalScaleRapidity; field_simp [hZ]

theorem equalScale_radius_of_half (ℓ x : ℝ) (hℓ : ℓ ≠ 0) (hx : x ≠ 0) :
    equalScaleRapidity ℓ (ℓ / (2 * x)) = 2 * x := by
  unfold equalScaleRapidity; field_simp [hℓ, hx]

/-! ### Equal-scale resonance \(f(x)=\tanh x\cdot\tan x\) -/

noncomputable def resonanceProd (x : ℝ) : ℝ := tanh x * tan x

theorem resonanceProd_zero : resonanceProd 0 = 0 := by
  simp [resonanceProd]

private theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < tanh x := by
  rw [tanh_eq_sinh_div_cosh]
  exact div_pos (sinh_pos_iff.mpr hx) (cosh_pos x)

private theorem tanh_lt_tanh_of_lt {a b : ℝ} (hab : a < b) : tanh a < tanh b := by
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
  have hden_a := cosh_pos a
  have hden_b := cosh_pos b
  rw [div_lt_div_iff₀ hden_a hden_b]
  -- sinh a · cosh b < sinh b · cosh a  ⟺  0 < sinh(b-a)
  have : 0 < sinh (b - a) := sinh_pos_iff.mpr (sub_pos.mpr hab)
  rw [sinh_sub] at this
  linarith

private theorem one_lt_pi_div_two : (1 : ℝ) < π / 2 := by
  linarith [pi_gt_three]

private theorem half_lt_pi_div_four : (1 / 2 : ℝ) < π / 4 := by
  linarith [pi_gt_three]

theorem strictMonoOn_resonanceProd :
    StrictMonoOn resonanceProd (Ioo 0 (π / 2)) := by
  intro a ha b hb hab
  simp only [mem_Ioo] at ha hb
  have htan_a : 0 < tan a := tan_pos_of_pos_of_lt_pi_div_two ha.1 ha.2
  have htanh_a : 0 < tanh a := tanh_pos_of_pos ha.1
  have htanh_lt : tanh a < tanh b := tanh_lt_tanh_of_lt hab
  have htan_lt : tan a < tan b :=
    strictMonoOn_tan
      ⟨lt_trans (neg_neg_of_pos pi_div_two_pos) ha.1, ha.2⟩
      ⟨lt_trans (neg_neg_of_pos pi_div_two_pos) hb.1, hb.2⟩ hab
  exact lt_trans (mul_lt_mul_of_pos_right htanh_lt htan_a)
    (mul_lt_mul_of_pos_left htan_lt (lt_trans htanh_a htanh_lt))

theorem resonanceProd_half_lt_one : resonanceProd (1 / 2) < 1 := by
  unfold resonanceProd
  have htan : tan (1 / 2 : ℝ) < 1 := by
    have hmono := strictMonoOn_tan
      ⟨by linarith [pi_div_two_pos], by linarith [one_lt_pi_div_two]⟩
      ⟨by linarith [pi_div_two_pos], by linarith [pi_div_two_pos]⟩
      half_lt_pi_div_four
    simpa [tan_pi_div_four] using hmono
  have htanh : tanh (1 / 2 : ℝ) < 1 := tanh_lt_one _
  have htan0 : 0 < tan (1 / 2 : ℝ) :=
    tan_pos_of_pos_of_lt_pi_div_two (by norm_num)
      (lt_trans (by norm_num) one_lt_pi_div_two)
  calc tanh (1 / 2) * tan (1 / 2)
      < 1 * tan (1 / 2) := mul_lt_mul_of_pos_right htanh htan0
    _ = tan (1 / 2) := one_mul _
    _ < 1 := htan

private theorem tanh_one_gt_three_quarters : (3 / 4 : ℝ) < tanh 1 := by
  have he : (27 / 10 : ℝ) < exp 1 :=
    lt_trans (by norm_num) exp_one_gt_d9
  have he2 : (729 / 100 : ℝ) < exp 1 ^ 2 := by
    nlinarith [he, show (0 : ℝ) ≤ 27 / 10 by norm_num]
  have hform : tanh 1 = (exp 1 ^ 2 - 1) / (exp 1 ^ 2 + 1) := by
    rw [tanh_eq, exp_neg]
    have hep : exp 1 ≠ 0 := (exp_pos _).ne'
    field_simp [hep]
  rw [hform, lt_div_iff₀ (by positivity)]
  nlinarith [he2]

private theorem tan_one_gt_four_thirds : (4 / 3 : ℝ) < tan 1 := by
  have hx : |(1 : ℝ)| ≤ 1 := by norm_num
  have hsin := abs_sub_le_iff.mp (sin_bound hx)
  have hcos := abs_sub_le_iff.mp (cos_bound hx)
  have hsin_lb : (247 / 300 : ℝ) ≤ sin 1 := by
    have := hsin.1
    simp only [one_pow] at this
    linarith
  have hcos_ub : cos 1 ≤ (53 / 96 : ℝ) := by
    have := hcos.2
    simp only [one_pow] at this
    linarith
  have hcos_pos : (0 : ℝ) < cos 1 := cos_pos_of_le_one hx
  rw [tan_eq_sin_div_cos]
  have hmid : (4 / 3 : ℝ) < (247 / 300) / (53 / 96) := by norm_num
  refine hmid.trans_le ?_
  rw [div_le_div_iff₀ (by norm_num) hcos_pos]
  calc (247 / 300 : ℝ) * cos 1
      ≤ (247 / 300) * (53 / 96) :=
        mul_le_mul_of_nonneg_left hcos_ub (by norm_num)
    _ ≤ sin 1 * (53 / 96) :=
        mul_le_mul_of_nonneg_right hsin_lb (by norm_num)

theorem resonanceProd_one_gt_one : (1 : ℝ) < resonanceProd 1 := by
  unfold resonanceProd
  have htanh := tanh_one_gt_three_quarters
  have htan := tan_one_gt_four_thirds
  have htanh_pos : (0 : ℝ) < tanh 1 := lt_trans (by norm_num) htanh
  calc (1 : ℝ)
      = (3 / 4) * (4 / 3) := by norm_num
    _ < tanh 1 * (4 / 3) := mul_lt_mul_of_pos_right htanh (by norm_num)
    _ < tanh 1 * tan 1 := mul_lt_mul_of_pos_left htan htanh_pos

private theorem continuousOn_resonanceProd_half_one :
    ContinuousOn resonanceProd (Icc (1 / 2 : ℝ) 1) := by
  have htanh : Continuous tanh := by
    have h : (tanh : ℝ → ℝ) = fun x => sinh x / cosh x :=
      funext tanh_eq_sinh_div_cosh
    rw [h]
    exact continuous_sinh.div continuous_cosh fun _ => (cosh_pos _).ne'
  refine htanh.continuousOn.mul (continuousOn_tan.mono ?_)
  intro x hx
  simp only [mem_Icc] at hx
  exact (cos_pos_of_mem_Ioo
    ⟨by linarith [pi_div_two_pos], lt_of_le_of_lt hx.2 one_lt_pi_div_two⟩).ne'

theorem exists_unique_resonance_root_in_half_one :
    ∃! x : ℝ, x ∈ Ioo (1 / 2 : ℝ) 1 ∧ resonanceProd x = 1 := by
  have hivt := intermediate_value_Ioo
    (by norm_num : (1 / 2 : ℝ) ≤ 1) continuousOn_resonanceProd_half_one
  obtain ⟨x, hxIoo, hxeq⟩ :=
    hivt ⟨resonanceProd_half_lt_one, resonanceProd_one_gt_one⟩
  refine ⟨x, ⟨hxIoo, hxeq⟩, ?_⟩
  intro y ⟨hyIoo, hyeq⟩
  have mem (z : ℝ) (hz : z ∈ Ioo (1 / 2 : ℝ) 1) :
      z ∈ Ioo (0 : ℝ) (π / 2) :=
    ⟨lt_trans (by norm_num) hz.1, lt_trans hz.2 one_lt_pi_div_two⟩
  have hxmem := mem x hxIoo
  have hymem := mem y hyIoo
  rcases lt_trichotomy x y with h | h | h
  · have := strictMonoOn_resonanceProd hxmem hymem h
    rw [hxeq, hyeq] at this
    exact (lt_irrefl _ this).elim
  · exact h.symm
  · have := strictMonoOn_resonanceProd hymem hxmem h
    rw [hyeq, hxeq] at this
    exact (lt_irrefl _ this).elim

/-- First positive resonance root on the equal-scale ansatz. -/
noncomputable def resonanceRoot1 : ℝ :=
  Classical.choose (ExistsUnique.exists exists_unique_resonance_root_in_half_one)

private theorem resonanceRoot1_spec :
    resonanceRoot1 ∈ Ioo (1 / 2 : ℝ) 1 ∧ resonanceProd resonanceRoot1 = 1 :=
  Classical.choose_spec (ExistsUnique.exists exists_unique_resonance_root_in_half_one)

theorem resonanceRoot1_mem : resonanceRoot1 ∈ Ioo (1 / 2 : ℝ) 1 :=
  resonanceRoot1_spec.1

theorem resonanceRoot1_prod : resonanceProd resonanceRoot1 = 1 :=
  resonanceRoot1_spec.2

theorem resonanceRoot1_bounds :
    (1 / 2 : ℝ) < resonanceRoot1 ∧ resonanceRoot1 < 1 :=
  mem_Ioo.mp resonanceRoot1_mem

/-! ### Characteristic length \(\ell = 2 x_1 a_0\) -/

noncomputable def lambdaHyp : ℝ :=
  2 * resonanceRoot1 * (bohrRadiusApprox : ℝ)

theorem lambdaHyp_bounds :
    (bohrRadiusApprox : ℝ) < lambdaHyp ∧
      lambdaHyp < 2 * (bohrRadiusApprox : ℝ) := by
  unfold lambdaHyp
  have ha0 : (0 : ℝ) < (bohrRadiusApprox : ℝ) := by exact_mod_cast bohrRadiusApprox_pos
  have hx := resonanceRoot1_bounds
  constructor <;> nlinarith

/-! ### Equal-scale radii are \(\Theta(1/n)\) -/

def resonanceBranch (n : ℕ) : Set ℝ :=
  Ioo ((n : ℝ) * π) ((n : ℝ) * π + π / 2)

theorem equalScale_radius_O_of_one_over_n
    (ℓ : ℝ) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ resonanceBranch n) (hℓ : 0 < ℓ) :
    ℓ / (2 * x) < ℓ / (2 * (n : ℝ) * π) := by
  simp only [resonanceBranch, mem_Ioo] at hx
  have hnπ : (0 : ℝ) < (n : ℝ) * π :=
    mul_pos (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)) pi_pos
  have hxpos : (0 : ℝ) < x := lt_trans hnπ hx.1
  have : (1 : ℝ) / x < 1 / ((n : ℝ) * π) :=
    (one_div_lt_one_div hxpos hnπ).mpr hx.1
  calc ℓ / (2 * x)
      = (ℓ / 2) * (1 / x) := by ring
    _ < (ℓ / 2) * (1 / ((n : ℝ) * π)) :=
        mul_lt_mul_of_pos_left this (div_pos hℓ (by norm_num))
    _ = ℓ / (2 * (n : ℝ) * π) := by ring

/-! ### Bohr bookkeeping (separate hypothesis) -/

/-- Bohr radius stand-in \(r_n = n^2 a_0\) (separate from equal-scale roots). -/
noncomputable def bohrShellRadius (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (bohrRadiusApprox : ℝ)

/-- Rydberg-style difference from Bohr radii only (not from \(\gamma_s=0\)). -/
noncomputable def bohrEnergyDiff (n m : ℕ) : ℝ :=
  (hydrogenIonisationApprox : ℝ) *
    ((1 : ℝ) / (n : ℝ) ^ 2 - 1 / (m : ℝ) ^ 2)

theorem bohrShellRadius_pos {n : ℕ} (hn : 0 < n) :
    0 < bohrShellRadius n := by
  unfold bohrShellRadius
  exact mul_pos (pow_pos (Nat.cast_pos.mpr hn) 2)
    (by exact_mod_cast bohrRadiusApprox_pos)

end Gravity

end DstDiophantine
