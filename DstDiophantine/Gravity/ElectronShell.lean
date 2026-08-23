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
