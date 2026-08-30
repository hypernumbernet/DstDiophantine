import DstDiophantine.Gravity.TorsionalLayer
import DstDiophantine.Gravity.ElectronShell
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coulombic circular orbits and the equal-scale / Bohr mismatch

## Paper boundary (do **not** claim)

The characteristic length `ℓ`, the Bohr radius `a₀`, and the identification of
the electromagnetic channel with atomic shells are **not** theorems of the
dual-rotor algebra. This module records algebraic identities of the written
Coulombic force \(F=ke^2/(\gamma_s r^2)\) and of the equal-scale layer radii.

No theorem asserts `dst_derives_lambda` or a Rydberg \(n^2\) spectrum from
\(\gamma_s=0\).

## What is proved

* The first equal-scale node lies in \((\pi/4,\,1)\). Identifying that node
  with \(a_0\) forces \(\pi a_0/2<\lambda<2a_0\).
* Coulombic circular balance \(mv^2/r=ke^2/(\gamma_s r^2)\) yields a positive
  \(v^2\) only on attractive layers \(\gamma_s>0\). Repulsive layers give
  \(v^2<0\); a node makes the written force undefined.
* The outermost well \(0<x<x_1\) is attractive; the first inner interval
  \(x_1<x<\pi\) is repulsive. Barriers are force divergences, not clock freezes.
* Equal-scale \(r_2/r_1\in(1/6,\,4/(5\pi))\subset(0,1)\) cannot equal the Bohr
  ratio \(4\). The equal-scale tower is inward; Bohr shells are outward.
* \(Z\)-contraction is the algebraic identity \(\ell\mapsto Z\ell\) \(\iff\)
  \(r\mapsto r/Z\).
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

/-! ### First-root window and labelled characteristic length -/

/-- Combined first-root window: \(\pi/4<x_1<1\). -/
theorem firstNode_window :
    π / 4 < resonanceRoot1 ∧ resonanceRoot1 < 1 :=
  resonanceRoot1_sharp_bounds

/-- If the outermost node is placed at \(a_0\), then
\(\tfrac\pi2 a_0<\lambda<2a_0\). -/
theorem lambdaHyp_sharp_bounds :
    (π / 2) * (bohrRadiusApprox : ℝ) < lambdaHyp ∧
      lambdaHyp < 2 * (bohrRadiusApprox : ℝ) := by
  unfold lambdaHyp
  have ha0 : (0 : ℝ) < (bohrRadiusApprox : ℝ) := by exact_mod_cast bohrRadiusApprox_pos
  have hx := resonanceRoot1_sharp_bounds
  constructor
  · have : (π / 2) * (bohrRadiusApprox : ℝ) = 2 * (π / 4) * (bohrRadiusApprox : ℝ) := by
      ring
    rw [this]
    nlinarith [hx.1, ha0]
  · nlinarith [hx.2, ha0]

/-! ### Coulombic circular balance -/

/-- Written Coulombic force \(F=ke^2/(\gamma_s r^2)\). The sign of \(F\) is
the sign of \(\gamma_s\). -/
noncomputable def coulombForce (k e γs r : ℝ) : ℝ :=
  k * e ^ 2 / (γs * r ^ 2)

/-- Circular-orbit identity \(v^2=ke^2/(m\gamma_s r)\). -/
noncomputable def circularSpeedSq (k e m γs r : ℝ) : ℝ :=
  k * e ^ 2 / (m * γs * r)

theorem circularSpeedSq_eq_force_balance
    {k e m γs r : ℝ} (hm : m ≠ 0) (hr : r ≠ 0) :
    circularSpeedSq k e m γs r = coulombForce k e γs r * r / m := by
  unfold circularSpeedSq coulombForce
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp [hm, hr, hr2]

/-- Attractive layers \(\gamma_s>0\) yield a real circular speed. -/
theorem circularSpeedSq_pos
    {k e m γs r : ℝ} (hk : 0 < k) (he : e ≠ 0) (hm : 0 < m)
    (hγ : 0 < γs) (hr : 0 < r) :
    0 < circularSpeedSq k e m γs r := by
  unfold circularSpeedSq
  exact div_pos (mul_pos hk (sq_pos_of_ne_zero he))
    (mul_pos (mul_pos hm hγ) hr)

/-- Repulsive layers \(\gamma_s<0\) make the written circular \(v^2\) negative. -/
theorem circularSpeedSq_neg_of_repulsive
    {k e m γs r : ℝ} (hk : 0 < k) (he : e ≠ 0) (hm : 0 < m)
    (hγ : γs < 0) (hr : 0 < r) :
    circularSpeedSq k e m γs r < 0 := by
  unfold circularSpeedSq
  have hnum : 0 < k * e ^ 2 := mul_pos hk (sq_pos_of_ne_zero he)
  have hden : m * γs * r < 0 := by
    have : m * γs < 0 := mul_neg_of_pos_of_neg hm hγ
    exact mul_neg_of_neg_of_pos this hr
  exact div_neg_of_pos_of_neg hnum hden

/-- The written force is undefined at a torsional node. -/
theorem coulombForce_denom_zero_at_node (r γs : ℝ) (hγ : γs = 0) :
    γs * r ^ 2 = 0 := by
  simp [hγ]

theorem circularSpeedSq_coulomb_limit (k e m r : ℝ) :
    circularSpeedSq k e m 1 r = k * e ^ 2 / (m * r) := by
  unfold circularSpeedSq
  ring

/-! ### Sign of the outermost well -/

theorem gammaSEqual_pos_left_of_first_node {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    0 < gammaSEqual x := by
  obtain ⟨h0, hx1⟩ := hx
  have hxIcc : x ∈ Icc (0 : ℝ) π :=
    ⟨h0.le, le_of_lt (lt_trans hx1 (lt_trans resonanceRoot1_sharp_bounds.2
      (by linarith [pi_gt_three] : (1 : ℝ) < π)))⟩
  have hrootIcc : resonanceRoot1 ∈ Icc (0 : ℝ) π :=
    ⟨le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1),
      le_of_lt (lt_trans resonanceRoot1_sharp_bounds.2
        (by linarith [pi_gt_three] : (1 : ℝ) < π))⟩
  have hanti := strictAntiOn_gammaSEqual_even 0
  have hlt := hanti (by simpa using hxIcc) (by simpa using hrootIcc) hx1
  rw [resonanceRoot1_gammaSEqual_zero] at hlt
  exact hlt

theorem gammaSEqual_neg_right_of_first_node {x : ℝ}
    (hx : x ∈ Ioo resonanceRoot1 π) :
    gammaSEqual x < 0 := by
  obtain ⟨hx1, hπ⟩ := hx
  have hxIcc : x ∈ Icc (0 : ℝ) π :=
    ⟨le_of_lt (lt_trans (by positivity : (0 : ℝ) < π / 4)
        (lt_trans resonanceRoot1_sharp_bounds.1 hx1)), hπ.le⟩
  have hrootIcc : resonanceRoot1 ∈ Icc (0 : ℝ) π :=
    ⟨le_of_lt (lt_trans (by positivity : (0 : ℝ) < π / 4)
        resonanceRoot1_sharp_bounds.1),
      le_of_lt (lt_trans resonanceRoot1_sharp_bounds.2
        (by linarith [pi_gt_three] : (1 : ℝ) < π))⟩
  have hanti := strictAntiOn_gammaSEqual_even 0
  have hlt := hanti (by simpa using hrootIcc) (by simpa using hxIcc) hx1
  rw [resonanceRoot1_gammaSEqual_zero] at hlt
  exact hlt

/-- A Coulombic node is a force divergence, not a clock freeze. -/
theorem node_is_force_divergence_not_clock_freeze {x : ℝ}
    (h : gammaSEqual x = 0) :
    gammaS (2 * x) (2 * x) = 0 ∧ 0 < gammaEff (2 * x) (2 * x) :=
  ⟨by rw [← gammaSEqual_eq_gammaS]; exact h, gammaEff_pos _ _⟩

/-! ### Inward equal-scale tower versus outward Bohr shells -/

theorem equalScale_first_second_ratio_window
    {x₂ : ℝ} (hx₂ : x₂ ∈ Ioo (π + π / 4) (π + π / 2)) :
    resonanceRoot1 / x₂ ∈ Ioo (1 / 6 : ℝ) (4 / (5 * π)) := by
  obtain ⟨hlo, hhi⟩ := resonanceRoot1_sharp_bounds
  simp only [mem_Ioo] at hx₂ ⊢
  have hx₂pos : (0 : ℝ) < x₂ := by linarith [pi_pos]
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) hx₂pos]
    nlinarith [hlo, hx₂.2]
  · rw [div_lt_div_iff₀ hx₂pos (by positivity)]
    nlinarith [hhi, hx₂.1, pi_pos]

theorem exists_equalScale_ratio_in_sharp_window :
    ∃ x₂ : ℝ, x₂ ∈ Ioo (π + π / 4) (π + π / 2) ∧ gammaSEqual x₂ = 0 ∧
      resonanceRoot1 / x₂ ∈ Ioo (1 / 6 : ℝ) (4 / (5 * π)) := by
  obtain ⟨x₂, hx₂, hzero⟩ := exists_second_node_sharp
  exact ⟨x₂, hx₂, hzero, equalScale_first_second_ratio_window hx₂⟩

theorem equalScale_ratio_lt_one
    {x₂ : ℝ} (hx₂ : x₂ ∈ Ioo (π + π / 4) (π + π / 2)) :
    resonanceRoot1 / x₂ < 1 := by
  have h := equalScale_first_second_ratio_window hx₂
  have hπ := pi_pos
  have : (4 / (5 * π) : ℝ) < 1 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_gt_three]
  exact lt_trans h.2 this

theorem bohrShellRadius_ratio_two :
    bohrShellRadius 2 / bohrShellRadius 1 = 4 := by
  unfold bohrShellRadius
  have ha0 : (bohrRadiusApprox : ℝ) ≠ 0 :=
    (by exact_mod_cast bohrRadiusApprox_pos : (0 : ℝ) < (bohrRadiusApprox : ℝ)).ne'
  field_simp [ha0]
  norm_num

/-- Equal-scale Coulombic nodes cannot reproduce the Bohr radius ratio. -/
theorem equalScale_ratio_ne_bohr
    {x₂ : ℝ} (hx₂ : x₂ ∈ Ioo (π + π / 4) (π + π / 2)) :
    resonanceRoot1 / x₂ ≠ bohrShellRadius 2 / bohrShellRadius 1 := by
  rw [bohrShellRadius_ratio_two]
  exact ne_of_lt (lt_trans (equalScale_ratio_lt_one hx₂) (by norm_num : (1 : ℝ) < 4))

/-! ### \(Z\)-contraction -/

/-- Scaling \(\ell\mapsto\ell/Z\) contracts every equal-scale radius by \(Z\).
The substitution \(\alpha,\beta\propto Z/r\) at fixed \(\ell\) is the inverse
scaling and moves nodes *outward* by \(Z\). Observed shell shrinkage is the
labelled identification \(\ell(Z)=\ell/Z\). -/
theorem Z_contracts_layerRadius {ℓ Z x : ℝ} (hZ : Z ≠ 0) :
    layerRadius (ℓ / Z) x = layerRadius ℓ x / Z := by
  unfold layerRadius
  field_simp [hZ]

/-- Inverse: \(\ell\mapsto Z\ell\) expands every equal-scale radius by \(Z\). -/
theorem Z_expands_layerRadius {ℓ Z x : ℝ} (hZ : Z ≠ 0) :
    layerRadius (Z * ℓ) x = Z * layerRadius ℓ x := by
  unfold layerRadius
  field_simp [hZ]

theorem Z_contraction_equalScale (ℓ Z r : ℝ) (hZ : Z ≠ 0) :
    equalScaleRapidity (Z * ℓ) r = equalScaleRapidity ℓ (r / Z) :=
  equalScale_Z_contraction ℓ Z r hZ

end Gravity

end DstDiophantine
