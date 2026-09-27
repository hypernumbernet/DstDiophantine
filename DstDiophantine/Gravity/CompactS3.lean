import DstDiophantine.Gravity.SI
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false

/-!
# Compact \(S^3\) cotangent gravity (galaxy scale)

## Paper boundary (do **not** claim)

Sec.~darkmatter writes an \(S^3\) cotangent potential, enhancement
\(\eta=(x/\sin x)^2\), shape \(f(x)=x/\sin^2 x\), and the scaling
\(R=\sqrt{GM/a_0}\). The acceleration \(a_0\) and Newton \(G\) are **external**
inputs (`Gravity.SI`); this module does **not** derive them from the dual-rotor
algebra. No theorem asserts `dst_derives_a0`. The point values
\(f_0=1.10\) and \(R=27\,\mathrm{kpc}\) lie outside the windows below.

The radial force does **not** change sign at the equator: `s3Accel` stays
negative wherever the sine is nonzero. The equator is only the zero of the
potential. Do not identify it with a sign change of \(J\) or of \(\gamma_s\).

Of the \(S^3\) chart the following are theorems (not a derivation of \(a_0\)):
the cotangent potential is radially harmonic and differentiates to the Gauss
acceleration; the flux \(R^2\sin^2(r/R)\,\Phi'\) equals \(GM\); circular
\(v^2=(GM/R)\,f(r/R)\); \(f\) has a unique minimum on \((0,\pi/2)\) at the
plateau root, with \(1.35<f_0<1.41\), and on \([1,6/5]\) one has
\(f<(11/10)f_0\); \(\eta\to 1\) as \(x\to 0^+\) and is strictly increasing on
\((0,\pi)\); for \(0<r\le R\) the potential is the Newtonian germ
\(-GM/r+GMr/(3R^2)\) up to a remainder of order \(r^3/R^4\); a constant
enclosed mass reproduces the point-mass shape; the negative well ends at
\(\pi R/2\), strictly before \(r=2R\), while the acceleration remains
center-directed on \((0,\pi R)\); on the SI stand-ins the Milky-Way
compactification radius satisfies \(8\,\mathrm{kpc}<R<9\,\mathrm{kpc}\).
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

/-! ### Potentials and dimensionless shapes -/

noncomputable def cotPotential (G M R r : ℝ) : ℝ :=
  -(G * M / R) * cot (r / R)

noncomputable def s3Accel (G M R r : ℝ) : ℝ :=
  -(G * M / (R ^ 2 * sin (r / R) ^ 2))

noncomputable def enhancement (x : ℝ) : ℝ :=
  (x / sin x) ^ 2

noncomputable def rotationShape (x : ℝ) : ℝ :=
  x / sin x ^ 2

/-- Plateau probe \(h(x)=\tan x-2x\). -/
noncomputable abbrev plateauProbe : ℝ → ℝ :=
  tan - fun y => (2 : ℝ) * id y

noncomputable def compactJacobian (x : ℝ) : ℝ :=
  sin x ^ 2 / x ^ 2

theorem enhancement_mul_jacobian (x : ℝ) (hx : x ≠ 0) (hs : sin x ≠ 0) :
    enhancement x * compactJacobian x = 1 := by
  unfold enhancement compactJacobian
  field_simp [hx, hs]

theorem enhancement_eq_x_mul_rotationShape (x : ℝ) (hs : sin x ≠ 0) :
    enhancement x = x * rotationShape x := by
  unfold enhancement rotationShape
  field_simp [hs]

/-! ### Gauss / harmonic / Newton factor -/

theorem s3Accel_gauss (G M R r : ℝ) (hR : R ≠ 0) (hs : sin (r / R) ≠ 0) :
    s3Accel G M R r * (4 * π * R ^ 2 * sin (r / R) ^ 2) = -4 * π * G * M := by
  unfold s3Accel
  field_simp [hR, hs]

theorem s3Accel_sin_sq (G M R r : ℝ) (hR : R ≠ 0) (hs : sin (r / R) ≠ 0) :
    sin (r / R) ^ 2 * s3Accel G M R r = -(G * M / R ^ 2) := by
  unfold s3Accel
  field_simp [hR, hs]

private theorem cos_eq_zero_of_mem_Ioo_zero_pi {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) π) (hcos : cos x = 0) : x = π / 2 := by
  have hxIcc : x ∈ Icc (0 : ℝ) π := ⟨hx.1.le, hx.2.le⟩
  have hπ : (π / 2 : ℝ) ∈ Icc 0 π := ⟨by positivity, by linarith [pi_pos]⟩
  exact strictAntiOn_cos.injOn hxIcc hπ (hcos.trans cos_pi_div_two.symm)

theorem cotPotential_eq_zero_iff {G M R r : ℝ}
    (hG : G ≠ 0) (hM : M ≠ 0) (hR : 0 < R) (hr : 0 < r)
    (hx : r / R < π) :
    cotPotential G M R r = 0 ↔ r = π * R / 2 := by
  have hR0 : R ≠ 0 := hR.ne'
  have hxpos : (0 : ℝ) < r / R := div_pos hr hR
  have hxIoo : r / R ∈ Ioo (0 : ℝ) π := ⟨hxpos, hx⟩
  unfold cotPotential
  have hcoef : -(G * M / R) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hG hM) hR0)
  constructor
  · intro h
    have hcot : cot (r / R) = 0 := (mul_eq_zero.mp h).resolve_left hcoef
    have hs : sin (r / R) ≠ 0 := (sin_pos_of_mem_Ioo hxIoo).ne'
    have hcos : cos (r / R) = 0 := by
      rw [cot_eq_cos_div_sin, div_eq_zero_iff] at hcot
      exact hcot.resolve_right hs
    have hxeq : r / R = π / 2 := cos_eq_zero_of_mem_Ioo_zero_pi hxIoo hcos
    calc r = (r / R) * R := (div_mul_cancel₀ r hR0).symm
      _ = (π / 2) * R := by rw [hxeq]
      _ = π * R / 2 := by ring
  · intro h
    have hxeq : r / R = π / 2 := by rw [h]; field_simp [hR0]
    simp [hxeq, cot_eq_cos_div_sin, cos_pi_div_two]

theorem cotPotential_newton_factor (G M R r : ℝ) (hR : R ≠ 0) (hr : r ≠ 0) :
    cotPotential G M R r = -(G * M / r) * ((r / R) * cot (r / R)) := by
  unfold cotPotential
  field_simp [hR, hr]

theorem enhancement_gt_one {x : ℝ} (hx : 0 < x) (hxπ : x < π) :
    1 < enhancement x := by
  have hs : 0 < sin x := sin_pos_of_mem_Ioo ⟨hx, hxπ⟩
  have hlt : sin x < x := sin_lt hx
  have hratio : 1 < x / sin x := (one_lt_div hs).mpr hlt
  unfold enhancement
  nlinarith [hratio, sq_nonneg (x / sin x)]

/-! ### Critical value \(f(x)=x+1/(4x)\) when \(\tan x=2x\) -/

theorem rotationShape_of_tan_eq_two_mul {x : ℝ}
    (hs : sin x ≠ 0) (htan : tan x = 2 * x) (hx : x ≠ 0) :
    rotationShape x = x + 1 / (4 * x) := by
  have hcot : cot x = 1 / (2 * x) := by
    rw [← tan_inv_eq_cot, htan]; field_simp [hx]
  unfold rotationShape
  have : 1 + cot x ^ 2 = 1 / sin x ^ 2 := by
    rw [cot_eq_cos_div_sin]; field_simp [hs]
    rw [← sin_sq_add_cos_sq x]
  have hsin2 : sin x ^ 2 = 1 / (1 + cot x ^ 2) := by
    field_simp [hs] at this ⊢; linarith
  rw [hsin2, hcot]; field_simp [hx]; ring

/-! ### Plateau probe -/

private theorem one_lt_pi_div_two : (1 : ℝ) < π / 2 := by
  linarith [pi_gt_three]

private theorem pi_div_four_lt_one : π / 4 < (1 : ℝ) := by
  linarith [pi_lt_four]

private theorem pi_div_four_lt_pi_div_two : π / 4 < π / 2 := by
  linarith [pi_pos]

theorem plateauProbe_pi_div_four : plateauProbe (π / 4) < 0 := by
  simp [plateauProbe, Pi.sub_apply, id, tan_pi_div_four]; linarith [pi_gt_three]

private theorem hasDerivAt_plateauProbe (x : ℝ) (hx : cos x ≠ 0) :
    HasDerivAt plateauProbe (1 / cos x ^ 2 - 2 * 1) x :=
  (hasDerivAt_tan hx).sub ((hasDerivAt_id x).const_mul (2 : ℝ))

private theorem mem_Ioo_neg_pi2_pi2_of_pi4 {x : ℝ}
    (hx : x ∈ Ioo (π / 4) (π / 2)) : x ∈ Ioo (-(π / 2)) (π / 2) :=
  ⟨lt_trans (neg_lt_zero.mpr pi_div_two_pos)
      (lt_trans (div_pos pi_pos (by norm_num)) hx.1), hx.2⟩

theorem strictMonoOn_plateauProbe_pi4_pi2 :
    StrictMonoOn plateauProbe (Ioo (π / 4) (π / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
  · unfold plateauProbe
    refine ContinuousOn.sub (continuousOn_tan.mono ?_)
        ((continuous_const.mul continuous_id).continuousOn)
    intro x hx
    exact (cos_pos_of_mem_Ioo (mem_Ioo_neg_pi2_pi2_of_pi4 hx)).ne'
  · intro x hx
    have hxI : x ∈ Ioo (π / 4) (π / 2) := by
      simpa [interior_Ioo] using hx
    have hcos : (0 : ℝ) < cos x :=
      cos_pos_of_mem_Ioo (mem_Ioo_neg_pi2_pi2_of_pi4 hxI)
    have hder := (hasDerivAt_plateauProbe x hcos.ne').deriv
    rw [hder]
    have htan : (1 : ℝ) < tan x := by
      have hcmp := tan_lt_tan_of_nonneg_of_lt_pi_div_two
        (le_of_lt (div_pos pi_pos (by norm_num))) hxI.2 hxI.1
      simpa [tan_pi_div_four] using hcmp
    have heq : 1 / cos x ^ 2 - 2 * 1 = tan x ^ 2 - 1 := by
      have : 1 / cos x ^ 2 = 1 + tan x ^ 2 := by
        rw [tan_eq_sin_div_cos]; field_simp [hcos.ne']
        rw [add_comm]; exact (sin_sq_add_cos_sq x).symm
      linarith
    have : (0 : ℝ) < tan x ^ 2 - 1 := by nlinarith [htan]
    rwa [heq]

/-- \(h(57/50)<0\) via double-angle Taylor window at \(57/100\). -/
theorem plateauProbe_57_50 : plateauProbe (57 / 50 : ℝ) < 0 := by
  set y : ℝ := 57 / 100
  have hy : |y| ≤ 1 := by norm_num [y]
  have hypos : (0 : ℝ) < y := by norm_num [y]
  have hsin := abs_sub_le_iff.mp (sin_bound hy)
  have hcos := abs_sub_le_iff.mp (cos_bound hy)
  have hsin_ub : sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 100 := by
    have := hsin.2; rw [abs_of_pos hypos] at this; linarith
  have hcos_lb : 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) ≤ cos y := by
    have := hcos.1; rw [abs_of_pos hypos] at this; linarith
  have hden0 : (0 : ℝ) < 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) := by norm_num [y]
  have htan_le : tan y ≤ (y - y ^ 3 / 6 + y ^ 5 / 100) /
      (1 - y ^ 2 / 2 - y ^ 4 * (5 / 96)) := by
    rw [tan_eq_sin_div_cos]
    exact div_le_div₀ (by positivity) hsin_ub hden0 hcos_lb
  have htu : tan y < (65 / 100 : ℝ) :=
    lt_of_le_of_lt htan_le (by norm_num [y])
  have htpos : (0 : ℝ) < tan y :=
    lt_trans hypos (lt_tan hypos (lt_trans (by norm_num [y]) one_lt_pi_div_two))
  have hden : tan y ^ 2 < 1 := by nlinarith [htu, htpos.le]
  have hfull : (57 / 50 : ℝ) = 2 * y := by norm_num [y]
  unfold plateauProbe
  simp only [Pi.sub_apply, id]
  rw [hfull, tan_two_mul]
  have hquot : 2 * tan y / (1 - tan y ^ 2) <
      2 * (65 / 100) / (1 - (65 / 100) ^ 2) := by
    have hp : (0 : ℝ) < 1 - tan y ^ 2 := sub_pos.mpr hden
    have hp' : (0 : ℝ) < 1 - (65 / 100) ^ 2 := by norm_num
    rw [div_lt_div_iff₀ hp hp']
    nlinarith [htu]
  have hcmp : 2 * (65 / 100 : ℝ) / (1 - (65 / 100) ^ 2) < 57 / 25 := by
    norm_num
  linarith

/-- \(h(6/5)>0\) via double-angle Taylor window at \(3/5\). -/
theorem plateauProbe_6_5 : (0 : ℝ) < plateauProbe (6 / 5) := by
  set y : ℝ := 3 / 5
  have hy : |y| ≤ 1 := by norm_num [y]
  have hypos : (0 : ℝ) < y := by norm_num [y]
  have hsin := abs_sub_le_iff.mp (sin_bound hy)
  have hcos := abs_sub_le_iff.mp (cos_bound hy)
  have hsin_lb : y - y ^ 3 / 6 - y ^ 5 / 100 ≤ sin y := by
    have := hsin.1; rw [abs_of_pos hypos] at this; linarith
  have hcos_ub : cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by
    have := hcos.2; rw [abs_of_pos hypos] at this; linarith
  have hcos_pos : (0 : ℝ) < cos y := cos_pos_of_le_one hy
  have hden0 : (0 : ℝ) < 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by norm_num [y]
  have htan_ge : (y - y ^ 3 / 6 - y ^ 5 / 100) /
      (1 - y ^ 2 / 2 + y ^ 4 * (5 / 96)) ≤ tan y := by
    rw [tan_eq_sin_div_cos]
    -- num/den_ub ≤ sin/cos : a=num, b=den_ub, c=sin, d=cos
    exact div_le_div₀ (le_trans (by positivity) hsin_lb) hsin_lb hcos_pos hcos_ub
  have htl : (68 / 100 : ℝ) < tan y :=
    lt_of_lt_of_le (by norm_num [y]) htan_ge
  have htpos : (0 : ℝ) < tan y := lt_trans (by norm_num) htl
  have hsin_ub : sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 100 := by
    have := hsin.2; rw [abs_of_pos hypos] at this; linarith
  have hcos_lb : 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) ≤ cos y := by
    have := hcos.1; rw [abs_of_pos hypos] at this; linarith
  have hden1 : (0 : ℝ) < 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) := by norm_num [y]
  have htu : tan y < (75 / 100 : ℝ) := by
    rw [tan_eq_sin_div_cos]
    refine lt_of_le_of_lt (div_le_div₀ (by positivity) hsin_ub hden1 hcos_lb) ?_
    norm_num [y]
  have hden : tan y ^ 2 < 1 := by nlinarith [htu, htpos.le]
  have hfull : (6 / 5 : ℝ) = 2 * y := by norm_num [y]
  unfold plateauProbe
  simp only [Pi.sub_apply, id]
  rw [hfull, tan_two_mul]
  have hquot : 2 * (68 / 100 : ℝ) / (1 - (68 / 100) ^ 2) <
      2 * tan y / (1 - tan y ^ 2) := by
    have hp : (0 : ℝ) < 1 - tan y ^ 2 := sub_pos.mpr hden
    have hp' : (0 : ℝ) < 1 - (68 / 100) ^ 2 := by norm_num
    rw [div_lt_div_iff₀ hp' hp]
    nlinarith [htl]
  have hcmp : (12 / 5 : ℝ) < 2 * (68 / 100) / (1 - (68 / 100) ^ 2) := by
    norm_num
  linarith

private theorem six_fifths_lt_pi_div_two : (6 / 5 : ℝ) < π / 2 :=
  lt_trans (by norm_num : (6 / 5 : ℝ) < 3 / 2) (by linarith [pi_gt_three])

theorem exists_unique_plateauRoot :
    ∃! x : ℝ, x ∈ Ioo (57 / 50 : ℝ) (6 / 5) ∧ plateauProbe x = 0 := by
  have hlo : (57 / 50 : ℝ) ≤ 6 / 5 := by norm_num
  have hcont : ContinuousOn plateauProbe (Icc (57 / 50 : ℝ) (6 / 5)) := by
    unfold plateauProbe
    refine ContinuousOn.sub (continuousOn_tan.mono ?_)
        ((continuous_const.mul continuous_id).continuousOn)
    intro x hx
    simp only [mem_Icc] at hx
    refine (cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne'
    · exact lt_trans (neg_lt_zero.mpr pi_div_two_pos) (lt_of_lt_of_le (by norm_num) hx.1)
    · exact lt_of_le_of_lt hx.2 six_fifths_lt_pi_div_two
  obtain ⟨x, hxIoo, hxeq⟩ :=
    intermediate_value_Ioo hlo hcont ⟨plateauProbe_57_50, plateauProbe_6_5⟩
  refine ⟨x, ⟨hxIoo, hxeq⟩, ?_⟩
  intro y ⟨hyIoo, hyeq⟩
  have hx' := mem_Ioo.mp hxIoo
  have hy' := mem_Ioo.mp hyIoo
  have hxmem : x ∈ Ioo (π / 4) (π / 2) :=
    ⟨lt_trans (lt_trans pi_div_four_lt_one (by norm_num : (1 : ℝ) < 57 / 50)) hx'.1,
      lt_trans hx'.2 six_fifths_lt_pi_div_two⟩
  have hymem : y ∈ Ioo (π / 4) (π / 2) :=
    ⟨lt_trans (lt_trans pi_div_four_lt_one (by norm_num : (1 : ℝ) < 57 / 50)) hy'.1,
      lt_trans hy'.2 six_fifths_lt_pi_div_two⟩
  rcases lt_trichotomy x y with h | h | h
  · have := strictMonoOn_plateauProbe_pi4_pi2 hxmem hymem h
    rw [hxeq, hyeq] at this
    exact (lt_irrefl _ this).elim
  · exact h.symm
  · have := strictMonoOn_plateauProbe_pi4_pi2 hymem hxmem h
    rw [hyeq, hxeq] at this
    exact (lt_irrefl _ this).elim

noncomputable def plateauRoot : ℝ :=
  Classical.choose (ExistsUnique.exists exists_unique_plateauRoot)

private theorem plateauRoot_spec :
    plateauRoot ∈ Ioo (57 / 50 : ℝ) (6 / 5) ∧ plateauProbe plateauRoot = 0 :=
  Classical.choose_spec (ExistsUnique.exists exists_unique_plateauRoot)

theorem plateauRoot_bounds :
    (57 / 50 : ℝ) < plateauRoot ∧ plateauRoot < (6 / 5) :=
  mem_Ioo.mp plateauRoot_spec.1

private theorem plateauRoot_mem_Ioo_pi4_pi2 :
    plateauRoot ∈ Ioo (π / 4) (π / 2) := by
  have ⟨hlo, hhi⟩ := plateauRoot_bounds
  exact ⟨lt_trans (lt_trans pi_div_four_lt_one (by norm_num : (1 : ℝ) < 57 / 50)) hlo,
    lt_trans hhi six_fifths_lt_pi_div_two⟩

theorem plateauRoot_lt_pi_div_two : plateauRoot < π / 2 :=
  plateauRoot_mem_Ioo_pi4_pi2.2

theorem plateauRoot_tan : tan plateauRoot = 2 * plateauRoot := by
  have := plateauRoot_spec.2
  simp [plateauProbe, Pi.sub_apply, id] at this
  linarith

theorem plateauRoot_ne_zero : plateauRoot ≠ 0 := by
  linarith [plateauRoot_bounds.1]

theorem plateauRoot_sin_ne_zero : sin plateauRoot ≠ 0 := by
  have ⟨hlo, hhi⟩ := plateauRoot_bounds
  exact (sin_pos_of_mem_Ioo ⟨lt_trans (by norm_num) hlo,
    lt_trans hhi (lt_trans six_fifths_lt_pi_div_two (by linarith [pi_pos]))⟩).ne'

noncomputable def f0 : ℝ := rotationShape plateauRoot

theorem f0_eq_crit : f0 = plateauRoot + 1 / (4 * plateauRoot) := by
  unfold f0
  exact rotationShape_of_tan_eq_two_mul plateauRoot_sin_ne_zero
    plateauRoot_tan plateauRoot_ne_zero

private theorem g_mono {a b : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (hab : a ≤ b) :
    a + 1 / (4 * a) ≤ b + 1 / (4 * b) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le (by norm_num) ha
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha0 hab
  have : (0 : ℝ) ≤ (b - a) * (4 * a * b - 1) := by
    have : (1 : ℝ) ≤ 4 * a * b := by nlinarith [ha, hab]
    nlinarith
  field_simp [ha0.ne', hb0.ne']; nlinarith

theorem f0_bounds : (135 / 100 : ℝ) < f0 ∧ f0 < (141 / 100 : ℝ) := by
  rw [f0_eq_crit]
  have ⟨hlo, hhi⟩ := plateauRoot_bounds
  constructor
  · have hg : (57 / 50 : ℝ) + 1 / (4 * (57 / 50)) = (1937 / 1425 : ℝ) := by
      norm_num
    have hmono := g_mono (by norm_num) hlo.le
    calc (135 / 100 : ℝ) < 1937 / 1425 := by norm_num
      _ = 57 / 50 + 1 / (4 * (57 / 50)) := hg.symm
      _ ≤ plateauRoot + 1 / (4 * plateauRoot) := hmono
  · have hg : (6 / 5 : ℝ) + 1 / (4 * (6 / 5)) = (169 / 120 : ℝ) := by norm_num
    have hmono := g_mono (by linarith [plateauRoot_bounds.1]) hhi.le
    calc plateauRoot + 1 / (4 * plateauRoot)
        ≤ 6 / 5 + 1 / (4 * (6 / 5)) := hmono
      _ = 169 / 120 := hg
      _ < 141 / 100 := by norm_num

/-- The value `1.10` is not the minimum of `f`. -/
theorem paper_f0_1_10_false : f0 ≠ (11 / 10 : ℝ) := by
  intro h; have ⟨hlo, _⟩ := f0_bounds; rw [h] at hlo; norm_num at hlo

/-! ### Tully–Fisher -/

noncomputable def vFlatSq (G M R : ℝ) : ℝ := (G * M / R) * f0

theorem tullyFisher_of_scaling {G M R a0 : ℝ}
    (hR : R ≠ 0) (hscale : R ^ 2 = G * M / a0) (ha0 : a0 ≠ 0) :
    (vFlatSq G M R) ^ 2 = G * M * a0 * f0 ^ 2 := by
  unfold vFlatSq
  have hGM : G * M = R ^ 2 * a0 := by field_simp [ha0] at hscale ⊢; nlinarith
  rw [hGM]; field_simp [hR]

/-! ### Milky-Way \(R\) on SI stand-ins -/

def milkyWayRsqApprox : ℚ :=
  GApprox * milkyWayMassApprox / mondAccelApprox

def milkyWayRsqOverKpc2 : ℚ :=
  milkyWayRsqApprox / kiloparsecApprox ^ 2

def milkyWayRsqOverKpc2_num : ℕ :=
  GMantissa * milkyWayMassCoeff * solarMassMantissa *
    10 ^ (30 + mondAccelScale + 2 * kiloparsecScale)

def milkyWayRsqOverKpc2_den : ℕ :=
  10 ^ GScale * 10 ^ solarMassScale * mondAccelMantissa *
    kiloparsecMantissa ^ 2 * 10 ^ 38

theorem milkyWayRsqOverKpc2_eq_num_div_den :
    milkyWayRsqOverKpc2 =
      (milkyWayRsqOverKpc2_num : ℚ) / (milkyWayRsqOverKpc2_den : ℚ) := by
  unfold milkyWayRsqOverKpc2 milkyWayRsqApprox milkyWayMassApprox
  unfold solarMassApprox kiloparsecApprox GApprox mondAccelApprox
  unfold milkyWayRsqOverKpc2_num milkyWayRsqOverKpc2_den
  unfold GMantissa GScale solarMassMantissa solarMassScale
    mondAccelMantissa mondAccelScale kiloparsecMantissa kiloparsecScale
    milkyWayMassCoeff
  field_simp; ring

private theorem milkyWayRsqOverKpc2_den_pos :
    (0 : ℚ) < (milkyWayRsqOverKpc2_den : ℚ) := by
  unfold milkyWayRsqOverKpc2_den GScale solarMassScale mondAccelMantissa
    kiloparsecMantissa
  norm_num

theorem milkyWayRsqOverKpc2_bounds :
    (64 : ℚ) < milkyWayRsqOverKpc2 ∧ milkyWayRsqOverKpc2 < (81 : ℚ) := by
  rw [milkyWayRsqOverKpc2_eq_num_div_den]
  have hden := milkyWayRsqOverKpc2_den_pos
  constructor
  · rw [lt_div_iff₀ hden]; exact_mod_cast (by
      unfold milkyWayRsqOverKpc2_num milkyWayRsqOverKpc2_den
      unfold GMantissa GScale solarMassMantissa solarMassScale
        mondAccelMantissa mondAccelScale kiloparsecMantissa kiloparsecScale
        milkyWayMassCoeff
      native_decide : 64 * milkyWayRsqOverKpc2_den < milkyWayRsqOverKpc2_num)
  · rw [div_lt_iff₀ hden]; exact_mod_cast (by
      unfold milkyWayRsqOverKpc2_num milkyWayRsqOverKpc2_den
      unfold GMantissa GScale solarMassMantissa solarMassScale
        mondAccelMantissa mondAccelScale kiloparsecMantissa kiloparsecScale
        milkyWayMassCoeff
      native_decide : milkyWayRsqOverKpc2_num < 81 * milkyWayRsqOverKpc2_den)

/-- `R²` on the Milky-Way stand-in lies strictly below `(27 kpc)²`. -/
theorem paper_R_MW_27_kpc_false :
    milkyWayRsqOverKpc2 < (27 : ℚ) ^ 2 :=
  milkyWayRsqOverKpc2_bounds.2.trans (by norm_num)

/-! ### Representative \(\eta\) windows (contain paper decimals) -/

theorem enhancement_one_tenth_bounds :
    (1003 / 1000 : ℝ) < enhancement (1 / 10) ∧
      enhancement (1 / 10) < (1004 / 1000 : ℝ) := by
  have hx : |(1 / 10 : ℝ)| ≤ 1 := by norm_num
  have hxpos : (0 : ℝ) < 1 / 10 := by norm_num
  have hsin := abs_sub_le_iff.mp (sin_bound hx)
  have hsin_lb : (1 / 10 : ℝ) - (1 / 10) ^ 3 / 6 - (1 / 10) ^ 5 / 100 ≤
      sin (1 / 10) := by
    have := hsin.1; rw [abs_of_pos hxpos] at this; linarith
  have hsin_ub : sin (1 / 10) ≤
      (1 / 10 : ℝ) - (1 / 10) ^ 3 / 6 + (1 / 10) ^ 5 / 100 := by
    have := hsin.2; rw [abs_of_pos hxpos] at this; linarith
  have hspos : (0 : ℝ) < sin (1 / 10) :=
    sin_pos_of_pos_of_le_one hxpos (by norm_num)
  unfold enhancement
  constructor
  · have : (1003 : ℝ) *
        ((1 / 10) - (1 / 10) ^ 3 / 6 + (1 / 10) ^ 5 / 100) ^ 2 <
        (1 / 10) ^ 2 * 1000 := by norm_num
    rw [div_pow, lt_div_iff₀ (sq_pos_of_pos hspos)]
    nlinarith [hsin_ub]
  · have : (1 / 10 : ℝ) ^ 2 * 1000 <
        (1004 : ℝ) * ((1 / 10) - (1 / 10) ^ 3 / 6 - (1 / 10) ^ 5 / 100) ^ 2 := by
      norm_num
    rw [div_pow, div_lt_iff₀ (sq_pos_of_pos hspos)]
    nlinarith [hsin_lb]

theorem enhancement_one_bounds :
    (140 / 100 : ℝ) < enhancement 1 ∧ enhancement 1 < (148 / 100 : ℝ) := by
  have hx : |(1 : ℝ)| ≤ 1 := by norm_num
  have hsin := abs_sub_le_iff.mp (sin_bound hx)
  have hsin_lb : (247 / 300 : ℝ) ≤ sin 1 := by
    have := hsin.1; simp only [one_pow] at this; linarith
  have hsin_ub : sin 1 ≤ (253 / 300 : ℝ) := by
    have := hsin.2; simp only [one_pow] at this; linarith
  have hspos : (0 : ℝ) < sin 1 := sin_pos_of_pos_of_le_one (by norm_num) le_rfl
  unfold enhancement
  constructor
  · have : (253 / 300 : ℝ) ^ 2 * (140 / 100) < 1 := by norm_num
    rw [div_pow, one_pow, lt_div_iff₀ (sq_pos_of_pos hspos)]
    nlinarith [hsin_ub]
  · have : 1 < (247 / 300 : ℝ) ^ 2 * (148 / 100) := by norm_num
    rw [div_pow, one_pow, div_lt_iff₀ (sq_pos_of_pos hspos)]
    nlinarith [hsin_lb]

/-- Paper value \(2.26\) lies in \((9/4,\, 10/3)\). -/
theorem enhancement_three_halves_bounds :
    (9 / 4 : ℝ) < enhancement (3 / 2) ∧ enhancement (3 / 2) < (10 / 3 : ℝ) := by
  have hxπ : (3 / 2 : ℝ) < π := by linarith [pi_gt_three]
  have hspos : (0 : ℝ) < sin (3 / 2) :=
    sin_pos_of_mem_Ioo ⟨by norm_num, hxπ⟩
  have hne : (3 / 2 : ℝ) ≠ π / 2 := by
    intro h; linarith [pi_gt_three, pi_lt_four, h]
  have hsin_lt : sin (3 / 2) < 1 := by
    refine lt_of_le_of_ne (sin_le_one _) ?_
    intro heq
    have hcos0 : cos (3 / 2) = 0 := by
      have := cos_sq_add_sin_sq (3 / 2 : ℝ); nlinarith [heq]
    exact hne (cos_eq_zero_of_mem_Ioo_zero_pi ⟨by norm_num, hxπ⟩ hcos0)
  have hx : |(1 : ℝ)| ≤ 1 := by norm_num
  have hsin1 := abs_sub_le_iff.mp (sin_bound hx)
  have hsin1_lb : (247 / 300 : ℝ) ≤ sin 1 := by
    have := hsin1.1; simp only [one_pow] at this; linarith
  have hmono : sin 1 ≤ sin (3 / 2) :=
    strictMonoOn_sin.monotoneOn
      ⟨le_of_lt (lt_trans (neg_lt_zero.mpr pi_div_two_pos) (by norm_num : (0 : ℝ) < 1)),
        le_of_lt one_lt_pi_div_two⟩
      ⟨le_of_lt (lt_trans (neg_lt_zero.mpr pi_div_two_pos) (by norm_num : (0 : ℝ) < 3 / 2)),
        by linarith [pi_gt_three]⟩
      (by norm_num : (1 : ℝ) ≤ 3 / 2)
  unfold enhancement
  constructor
  · -- (3/2)^2 / sin^2 > 9/4 ↔ sin^2 < 1
    rw [div_pow, lt_div_iff₀ (sq_pos_of_pos hspos)]
    nlinarith [hsin_lt]
  · -- (3/2)^2 / sin^2 < 10/3 ↔ sin^2 > 27/40
    have : (27 / 40 : ℝ) < (247 / 300) ^ 2 := by norm_num
    rw [div_pow, div_lt_iff₀ (sq_pos_of_pos hspos)]
    nlinarith [hsin1_lb, hmono]

/-- Paper value \(4.84\) lies in \((4,\, 8)\). -/
theorem enhancement_two_bounds :
    (4 : ℝ) < enhancement 2 ∧ enhancement 2 < (8 : ℝ) := by
  have hxπ : (2 : ℝ) < π := by linarith [pi_gt_three]
  have hspos : (0 : ℝ) < sin 2 := sin_pos_of_mem_Ioo ⟨by norm_num, hxπ⟩
  have hne : (2 : ℝ) ≠ π / 2 := by
    intro h; linarith [pi_gt_three, pi_lt_four, h]
  have hsin_lt : sin 2 < 1 := by
    refine lt_of_le_of_ne (sin_le_one _) ?_
    intro heq
    have hcos0 : cos 2 = 0 := by
      have := cos_sq_add_sin_sq (2 : ℝ); nlinarith [heq]
    exact hne (cos_eq_zero_of_mem_Ioo_zero_pi ⟨by norm_num, hxπ⟩ hcos0)
  have hx : |(1 : ℝ)| ≤ 1 := by norm_num
  have hsin := abs_sub_le_iff.mp (sin_bound hx)
  have hcos := abs_sub_le_iff.mp (cos_bound hx)
  have hsin_lb : (247 / 300 : ℝ) ≤ sin 1 := by
    have := hsin.1; simp only [one_pow] at this; linarith
  have hcos_lb : (43 / 96 : ℝ) ≤ cos 1 := by
    have := hcos.1; simp only [one_pow] at this; linarith
  have hs1 : (0 : ℝ) < sin 1 := sin_pos_of_pos_of_le_one (by norm_num) le_rfl
  have hc1 : (0 : ℝ) < cos 1 := cos_pos_of_le_one hx
  have hsin2 : sin 2 = 2 * sin 1 * cos 1 := by
    have h := sin_two_mul (1 : ℝ)
    -- h : sin (2 * 1) = 2 * sin 1 * cos 1
    simpa only [mul_one] using h
  have hlb : 2 * (247 / 300 : ℝ) * (43 / 96) ≤ sin 2 := by
    rw [hsin2]; nlinarith [hsin_lb, hcos_lb]
  unfold enhancement
  constructor
  · rw [div_pow, lt_div_iff₀ (sq_pos_of_pos hspos)]
    nlinarith [hsin_lt]
  · -- 4 / sin^2 < 8 ↔ sin^2 > 1/2
    have : (1 / 2 : ℝ) < (2 * (247 / 300) * (43 / 96)) ^ 2 := by norm_num
    rw [div_pow, div_lt_iff₀ (sq_pos_of_pos hspos)]
    nlinarith [hlb]

/-! ### Potential–acceleration dictionary and circular speed -/

private theorem hasDerivAt_cot {x : ℝ} (hs : sin x ≠ 0) :
    HasDerivAt cot (-(1 / sin x ^ 2)) x := by
  have hfun : cot = fun y => cos y / sin y := by
    funext y; exact cot_eq_cos_div_sin y
  rw [hfun]
  have h := (hasDerivAt_cos x).div (hasDerivAt_sin x) hs
  have heq : ((-sin x) * sin x - cos x * cos x) / sin x ^ 2 = -(1 / sin x ^ 2) := by
    have hnum : (-sin x) * sin x - cos x * cos x = -(sin x ^ 2 + cos x ^ 2) := by ring
    rw [hnum, sin_sq_add_cos_sq, neg_div, one_div]
  rwa [heq] at h

/-- \(\Phi'(r)=-g(r)\): the written \(S^3\) acceleration is minus the radial
derivative of the cotangent potential. -/
theorem hasDerivAt_cotPotential (G M R r : ℝ) (hR : R ≠ 0)
    (hs : sin (r / R) ≠ 0) :
    HasDerivAt (cotPotential G M R) (-s3Accel G M R r) r := by
  have hinner : HasDerivAt (fun t : ℝ => t / R) (1 / R) r :=
    (hasDerivAt_id r).div_const R
  have hcomp := (hasDerivAt_cot hs).comp r hinner
  have hmul := hcomp.const_mul (-(G * M / R))
  have hf : cotPotential G M R =
      fun t => -(G * M / R) * (cot ∘ fun s : ℝ => s / R) t := by
    funext t; rfl
  have heq : -(G * M / R) * (-(1 / sin (r / R) ^ 2) * (1 / R)) =
      -s3Accel G M R r := by
    unfold s3Accel; field_simp [hR, hs]
  rw [hf]
  exact heq ▸ hmul

/-- Circular \(v^2=r\,|g|\) on the \(S^3\) chart. -/
noncomputable def s3CircularSpeedSq (G M R r : ℝ) : ℝ :=
  r * (-s3Accel G M R r)

/-- Compactness-to-shape identity: \(v^2=(GM/R)\,f(r/R)\). -/
theorem s3CircularSpeedSq_eq_shape (G M R r : ℝ) (hR : R ≠ 0)
    (hs : sin (r / R) ≠ 0) :
    s3CircularSpeedSq G M R r = (G * M / R) * rotationShape (r / R) := by
  unfold s3CircularSpeedSq s3Accel rotationShape
  field_simp [hR, hs]

theorem s3CircularSpeedSq_eq_newton_mul_enhancement (G M R r : ℝ)
    (hR : R ≠ 0) (hr : r ≠ 0) (hs : sin (r / R) ≠ 0) :
    s3CircularSpeedSq G M R r = (G * M / r) * enhancement (r / R) := by
  rw [s3CircularSpeedSq_eq_shape G M R r hR hs,
    enhancement_eq_x_mul_rotationShape (r / R) hs]
  field_simp [hR, hr]

/-! ### Unique minimum of \(f\) on \((0,\pi/2)\) -/

private theorem sin_pos_of_mem_Ioo_zero_pi2 {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (π / 2)) : 0 < sin x :=
  sin_pos_of_mem_Ioo ⟨hx.1, lt_trans hx.2 (by linarith [pi_pos])⟩

private theorem cos_pos_of_mem_Ioo_zero_pi2 {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (π / 2)) : 0 < cos x :=
  cos_pos_of_mem_Ioo ⟨lt_trans (neg_lt_zero.mpr pi_div_two_pos) hx.1, hx.2⟩

theorem hasDerivAt_rotationShape {x : ℝ} (hs : sin x ≠ 0) :
    HasDerivAt rotationShape ((sin x - 2 * x * cos x) / sin x ^ 3) x := by
  have hsin2 : HasDerivAt (fun y => sin y * sin y)
      (cos x * sin x + sin x * cos x) x :=
    (hasDerivAt_sin x).mul (hasDerivAt_sin x)
  rw [show cos x * sin x + sin x * cos x = 2 * sin x * cos x by ring] at hsin2
  rw [show (fun y => sin y * sin y) = fun y => sin y ^ 2 from
    funext fun y => (pow_two _).symm] at hsin2
  have hdiv := (hasDerivAt_id x).div hsin2 (pow_ne_zero 2 hs)
  have heq :
      ((1 : ℝ) * sin x ^ 2 - x * (2 * sin x * cos x)) / (sin x ^ 2) ^ 2 =
        (sin x - 2 * x * cos x) / sin x ^ 3 := by
    field_simp [hs]
  have hf : rotationShape = id / fun y => sin y ^ 2 := by
    funext y; simp [rotationShape, Pi.div_apply]
  rw [hf]
  exact heq ▸ hdiv

private theorem sin_sub_two_mul_x_cos {x : ℝ} (hc : cos x ≠ 0) :
    sin x - 2 * x * cos x = cos x * plateauProbe x := by
  simp [plateauProbe, Pi.sub_apply, id, tan_eq_sin_div_cos]
  field_simp [hc]

private theorem deriv_rotationShape_eq_cos_mul_probe {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (π / 2)) :
    deriv rotationShape x = cos x * plateauProbe x / sin x ^ 3 := by
  have hs := (sin_pos_of_mem_Ioo_zero_pi2 hx).ne'
  have hc := (cos_pos_of_mem_Ioo_zero_pi2 hx).ne'
  rw [(hasDerivAt_rotationShape hs).deriv, sin_sub_two_mul_x_cos hc]

theorem deriv_rotationShape_eq_zero_iff {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (π / 2)) :
    deriv rotationShape x = 0 ↔ tan x = 2 * x := by
  have hc := (cos_pos_of_mem_Ioo_zero_pi2 hx).ne'
  have hs := (sin_pos_of_mem_Ioo_zero_pi2 hx).ne'
  rw [deriv_rotationShape_eq_cos_mul_probe hx]
  have hden : sin x ^ 3 ≠ 0 := pow_ne_zero 3 hs
  constructor
  · intro h
    have hnum : cos x * plateauProbe x = 0 :=
      (div_eq_zero_iff.mp h).resolve_right hden
    have hprobe : plateauProbe x = 0 := (mul_eq_zero.mp hnum).resolve_left hc
    simp [plateauProbe, Pi.sub_apply, id] at hprobe
    linarith
  · intro htan
    have hprobe : plateauProbe x = 0 := by
      simp [plateauProbe, Pi.sub_apply, id]; linarith
    simp [hprobe]

theorem two_gt_pi_div_two : π / 2 < (2 : ℝ) := by
  linarith [pi_lt_four]

/-- The attractive patch \(r<\pi R/2\) ends strictly before \(r=2R\). -/
theorem attractive_patch_before_two :
    plateauRoot < π / 2 ∧ π / 2 < (2 : ℝ) :=
  ⟨plateauRoot_lt_pi_div_two, two_gt_pi_div_two⟩

private theorem strictAntiOn_plateauProbe_zero_pi4 :
    StrictAntiOn plateauProbe (Icc (0 : ℝ) (π / 4)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · unfold plateauProbe
    refine ContinuousOn.sub (continuousOn_tan.mono ?_)
        ((continuous_const.mul continuous_id).continuousOn)
    intro x hx
    exact (cos_pos_of_mem_Ioo ⟨lt_of_lt_of_le (neg_lt_zero.mpr pi_div_two_pos) hx.1,
      lt_of_le_of_lt hx.2 pi_div_four_lt_pi_div_two⟩).ne'
  · intro x hx
    have hxI : x ∈ Ioo (0 : ℝ) (π / 4) := by simpa [interior_Icc] using hx
    have hcos : (0 : ℝ) < cos x :=
      cos_pos_of_mem_Ioo ⟨lt_trans (neg_lt_zero.mpr pi_div_two_pos) hxI.1,
        lt_trans hxI.2 pi_div_four_lt_pi_div_two⟩
    have hder := (hasDerivAt_plateauProbe x hcos.ne').deriv
    rw [hder]
    have htan : tan x < (1 : ℝ) := by
      have hcmp := tan_lt_tan_of_nonneg_of_lt_pi_div_two
        hxI.1.le pi_div_four_lt_pi_div_two hxI.2
      simpa [tan_pi_div_four] using hcmp
    have : 1 / cos x ^ 2 = 1 + tan x ^ 2 := by
      rw [tan_eq_sin_div_cos]; field_simp [hcos.ne']
      rw [add_comm]; exact (sin_sq_add_cos_sq x).symm
    have htpos : (0 : ℝ) ≤ tan x :=
      le_of_lt (lt_trans hxI.1 (lt_tan hxI.1 (lt_trans hxI.2 pi_div_four_lt_pi_div_two)))
    nlinarith [htan, htpos]

private theorem plateauProbe_neg_of_mem_Ioo_zero_pi4 {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (π / 4)) : plateauProbe x < 0 := by
  have h0 : plateauProbe 0 = 0 := by simp [plateauProbe, tan_zero]
  have := strictAntiOn_plateauProbe_zero_pi4
    ⟨le_rfl, (div_pos pi_pos (by norm_num)).le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
  simpa [h0] using this

private theorem plateauProbe_neg_of_lt_plateauRoot {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) plateauRoot) : plateauProbe x < 0 := by
  have hx' := mem_Ioo.mp hx
  have hroot := plateauRoot_mem_Ioo_pi4_pi2
  rcases lt_trichotomy x (π / 4) with h | h | h
  · exact plateauProbe_neg_of_mem_Ioo_zero_pi4 ⟨hx'.1, h⟩
  · rw [h]; exact plateauProbe_pi_div_four
  · have hxmem : x ∈ Ioo (π / 4) (π / 2) := ⟨h, lt_trans hx'.2 hroot.2⟩
    have := strictMonoOn_plateauProbe_pi4_pi2 hxmem hroot hx'.2
    simpa [plateauRoot_spec.2] using this

private theorem plateauProbe_pos_of_gt_plateauRoot {x : ℝ}
    (hx : x ∈ Ioo plateauRoot (π / 2)) : (0 : ℝ) < plateauProbe x := by
  have hx' := mem_Ioo.mp hx
  have hroot := plateauRoot_mem_Ioo_pi4_pi2
  have hymem : x ∈ Ioo (π / 4) (π / 2) := ⟨lt_trans hroot.1 hx'.1, hx'.2⟩
  have := strictMonoOn_plateauProbe_pi4_pi2 hroot hymem hx'.1
  simpa [plateauRoot_spec.2] using this

private theorem deriv_rotationShape_neg_of_lt_root {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) plateauRoot) : deriv rotationShape x < 0 := by
  have hxπ : x ∈ Ioo (0 : ℝ) (π / 2) :=
    ⟨hx.1, lt_trans hx.2 plateauRoot_lt_pi_div_two⟩
  rw [deriv_rotationShape_eq_cos_mul_probe hxπ]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (cos_pos_of_mem_Ioo_zero_pi2 hxπ)
      (plateauProbe_neg_of_lt_plateauRoot hx))
    (pow_pos (sin_pos_of_mem_Ioo_zero_pi2 hxπ) 3)

private theorem deriv_rotationShape_pos_of_gt_root {x : ℝ}
    (hx : x ∈ Ioo plateauRoot (π / 2)) : (0 : ℝ) < deriv rotationShape x := by
  have hxπ : x ∈ Ioo (0 : ℝ) (π / 2) :=
    ⟨lt_trans (lt_trans (by norm_num) plateauRoot_bounds.1) hx.1, hx.2⟩
  rw [deriv_rotationShape_eq_cos_mul_probe hxπ]
  exact div_pos
    (mul_pos (cos_pos_of_mem_Ioo_zero_pi2 hxπ)
      (plateauProbe_pos_of_gt_plateauRoot hx))
    (pow_pos (sin_pos_of_mem_Ioo_zero_pi2 hxπ) 3)

private theorem continuousOn_rotationShape_Icc {a b : ℝ}
    (ha : 0 < a) (hb : b < π / 2) :
    ContinuousOn rotationShape (Icc a b) := by
  unfold rotationShape
  refine ContinuousOn.div continuousOn_id (continuousOn_sin.pow 2) ?_
  intro x hx
  exact pow_ne_zero 2 (sin_pos_of_mem_Ioo_zero_pi2
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩).ne'

private theorem rotationShape_gt_f0_of_lt_root {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) plateauRoot) : f0 < rotationShape x := by
  have hanti : StrictAntiOn rotationShape (Icc x plateauRoot) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuousOn_rotationShape_Icc hx.1 plateauRoot_lt_pi_div_two) ?_
    intro y hy
    have hyI : y ∈ Ioo x plateauRoot := by simpa [interior_Icc] using hy
    exact deriv_rotationShape_neg_of_lt_root ⟨lt_trans hx.1 hyI.1, hyI.2⟩
  have := hanti ⟨le_rfl, hx.2.le⟩ ⟨hx.2.le, le_rfl⟩ hx.2
  simpa [f0] using this

private theorem rotationShape_gt_f0_of_gt_root {x : ℝ}
    (hx : x ∈ Ioo plateauRoot (π / 2)) : f0 < rotationShape x := by
  have ha : (0 : ℝ) < plateauRoot := lt_trans (by norm_num) plateauRoot_bounds.1
  have hmono : StrictMonoOn rotationShape (Icc plateauRoot x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (continuousOn_rotationShape_Icc ha hx.2) ?_
    intro y hy
    have hyI : y ∈ Ioo plateauRoot x := by simpa [interior_Icc] using hy
    exact deriv_rotationShape_pos_of_gt_root ⟨hyI.1, lt_trans hyI.2 hx.2⟩
  have := hmono ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1
  simpa [f0] using this

/-- Unique minimum of the rotation-curve shape on the attractive interval. -/
theorem rotationShape_min {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (π / 2)) :
    f0 ≤ rotationShape x ∧ (rotationShape x = f0 ↔ x = plateauRoot) := by
  rcases lt_trichotomy x plateauRoot with h | h | h
  · have hgt := rotationShape_gt_f0_of_lt_root ⟨hx.1, h⟩
    exact ⟨hgt.le, ⟨fun heq => (hgt.ne heq.symm).elim, fun hxeq => (h.ne hxeq).elim⟩⟩
  · subst h; exact ⟨le_rfl, ⟨fun _ => rfl, fun _ => rfl⟩⟩
  · have hgt := rotationShape_gt_f0_of_gt_root ⟨h, hx.2⟩
    exact ⟨hgt.le, ⟨fun heq => (hgt.ne heq.symm).elim, fun hxeq => (h.ne' hxeq).elim⟩⟩

theorem rotationShape_one_bounds :
    (140 / 100 : ℝ) < rotationShape 1 ∧ rotationShape 1 < (148 / 100 : ℝ) := by
  have hs : sin (1 : ℝ) ≠ 0 := (sin_pos_of_pos_of_le_one (by norm_num) le_rfl).ne'
  simpa [enhancement_eq_x_mul_rotationShape 1 hs] using enhancement_one_bounds

/-! ### Strict increase of \(\eta\) on \((0,\pi)\) -/

private theorem hasDerivAt_sin_sub_x_cos (x : ℝ) :
    HasDerivAt (fun y => sin y - y * cos y) (x * sin x) x := by
  have hmul : HasDerivAt (fun y => y * cos y) (1 * cos x + x * (-sin x)) x :=
    (hasDerivAt_id x).mul (hasDerivAt_cos x)
  have h := (hasDerivAt_sin x).sub hmul
  have heq : cos x - (1 * cos x + x * (-sin x)) = x * sin x := by ring
  rwa [heq] at h

private theorem sin_sub_x_cos_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) π) :
    0 < sin x - x * cos x := by
  have hmono : StrictMonoOn (fun y => sin y - y * cos y) (Icc (0 : ℝ) π) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · exact (continuousOn_sin.sub (continuousOn_id.mul continuousOn_cos))
    · intro y hy
      have hyI : y ∈ Ioo (0 : ℝ) π := by simpa [interior_Icc] using hy
      have hder := (hasDerivAt_sin_sub_x_cos y).deriv
      rw [hder]
      exact mul_pos hyI.1 (sin_pos_of_mem_Ioo hyI)
  have h0 : (fun y => sin y - y * cos y) 0 = 0 := by simp
  have hxIcc : x ∈ Icc (0 : ℝ) π := ⟨hx.1.le, hx.2.le⟩
  have h00 : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, pi_pos.le⟩
  have := hmono h00 hxIcc hx.1
  simpa [h0] using this

theorem hasDerivAt_enhancement {x : ℝ} (hs : sin x ≠ 0) :
    HasDerivAt enhancement
      (2 * (x / sin x) * ((sin x - x * cos x) / sin x ^ 2)) x := by
  have hu : HasDerivAt (fun y => y / sin y)
      ((1 * sin x - x * cos x) / sin x ^ 2) x :=
    (hasDerivAt_id x).div (hasDerivAt_sin x) hs
  have hpow := hu.pow 2
  have hfun : (fun y => (y / sin y) ^ 2) = (fun y => y / sin y) ^ 2 := by
    funext y; simp [Pi.pow_apply]
  rw [← hfun] at hpow
  unfold enhancement
  simpa [pow_one] using hpow

theorem strictMonoOn_enhancement :
    StrictMonoOn enhancement (Ioo (0 : ℝ) π) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
  · unfold enhancement
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_id continuousOn_sin ?_) 2
    intro x hx
    exact (sin_pos_of_mem_Ioo hx).ne'
  · intro x hx
    have hxI : x ∈ Ioo (0 : ℝ) π := by simpa [interior_Ioo] using hx
    have hspos := sin_pos_of_mem_Ioo hxI
    have hder := (hasDerivAt_enhancement hspos.ne').deriv
    rw [hder]
    have hu : (0 : ℝ) < x / sin x := div_pos hxI.1 hspos
    have hw := sin_sub_x_cos_pos hxI
    exact mul_pos (mul_pos (by norm_num) hu) (div_pos hw (pow_pos hspos 2))

theorem enhancement_pi_div_two : enhancement (π / 2) = π ^ 2 / 4 := by
  unfold enhancement
  simp [sin_pi_div_two]
  ring

/-! ### Milky-Way geometric radii on SI stand-ins -/

private theorem mul_lt_mul_of_pos_windows {a b c d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hab : a < b) (hcd : c < d) : a * c < b * d :=
  (mul_lt_mul_of_pos_right hab hc).trans
    (mul_lt_mul_of_pos_left hcd (lt_trans ha hab))

noncomputable def milkyWayROverKpc : ℝ :=
  Real.sqrt (milkyWayRsqOverKpc2 : ℝ)

theorem milkyWayROverKpc_bounds :
    (8 : ℝ) < milkyWayROverKpc ∧ milkyWayROverKpc < (9 : ℝ) := by
  have ⟨hlo, hhi⟩ := milkyWayRsqOverKpc2_bounds
  have h64 : (64 : ℝ) < (milkyWayRsqOverKpc2 : ℝ) := mod_cast hlo
  have h81 : (milkyWayRsqOverKpc2 : ℝ) < (81 : ℝ) := mod_cast hhi
  unfold milkyWayROverKpc
  constructor
  · rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    convert h64 using 1
    norm_num
  · rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 9)]
    convert h81 using 1
    norm_num

noncomputable def milkyWayPlateauOverKpc : ℝ :=
  plateauRoot * milkyWayROverKpc

theorem milkyWayPlateauOverKpc_bounds :
    (9 : ℝ) < milkyWayPlateauOverKpc ∧ milkyWayPlateauOverKpc < (11 : ℝ) := by
  have ⟨hRlo, hRhi⟩ := milkyWayROverKpc_bounds
  have ⟨hxlo, hxhi⟩ := plateauRoot_bounds
  unfold milkyWayPlateauOverKpc
  constructor
  · have := mul_lt_mul_of_pos_windows (by norm_num : (0 : ℝ) < 57 / 50)
      (by norm_num : (0 : ℝ) < 8) hxlo hRlo
    have : (9 : ℝ) < (57 / 50) * 8 := by norm_num
    linarith
  · have := mul_lt_mul_of_pos_windows
      (lt_trans (by norm_num) plateauRoot_bounds.1) (lt_trans (by norm_num) hRlo)
      hxhi hRhi
    have : (6 / 5 : ℝ) * 9 < 11 := by norm_num
    linarith

noncomputable def milkyWayReversalOverKpc : ℝ :=
  π / 2 * milkyWayROverKpc

theorem milkyWayReversalOverKpc_bounds :
    (12 : ℝ) < milkyWayReversalOverKpc ∧ milkyWayReversalOverKpc < (15 : ℝ) := by
  have ⟨hRlo, hRhi⟩ := milkyWayROverKpc_bounds
  unfold milkyWayReversalOverKpc
  constructor
  · have := mul_lt_mul_of_pos_windows (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (0 : ℝ) < 8)
      (by linarith [pi_gt_three] : (3 / 2 : ℝ) < π / 2) hRlo
    have : (3 / 2 : ℝ) * 8 = 12 := by norm_num
    linarith
  · have hpi : π < (315 / 100 : ℝ) := by
      convert Real.pi_lt_d2 using 1
      norm_num
    have hhalf : π / 2 < (315 / 200 : ℝ) := by linarith
    have := mul_lt_mul_of_pos_windows (div_pos pi_pos (by norm_num))
      (lt_trans (by norm_num) hRlo) hhalf hRhi
    have : (315 / 200 : ℝ) * 9 < 15 := by norm_num
    linarith

theorem milkyWayPlateau_lt_reversal :
    milkyWayPlateauOverKpc < milkyWayReversalOverKpc := by
  unfold milkyWayPlateauOverKpc milkyWayReversalOverKpc
  have hRpos : (0 : ℝ) < milkyWayROverKpc :=
    lt_trans (by norm_num) milkyWayROverKpc_bounds.1
  exact mul_lt_mul_of_pos_right plateauRoot_lt_pi_div_two hRpos

/-! ### Radial harmonicity, force sign, and the edge of the well -/

open Filter
open scoped Topology

/-- Radial Laplacian `Φ'' + (2/R) cot(r/R) Φ'` on the geodesic polar chart. -/
noncomputable def radialLaplace (R : ℝ) (Φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv Φ) r + (2 / R) * cot (r / R) * deriv Φ r

/-- Geodesic-sphere flux of the cotangent potential is the enclosed mass. -/
theorem geodesicFlux_cotPotential {G M R r : ℝ} (hR : R ≠ 0) (hs : sin (r / R) ≠ 0) :
    R ^ 2 * sin (r / R) ^ 2 * deriv (cotPotential G M R) r = G * M := by
  rw [(hasDerivAt_cotPotential G M R r hR hs).deriv]
  unfold s3Accel
  field_simp [hR, hs]

private theorem hasDerivAt_sin_over (R r : ℝ) :
    HasDerivAt (fun t : ℝ => sin (t / R)) (cos (r / R) * (1 / R)) r := by
  have h := (hasDerivAt_sin (r / R)).comp r ((hasDerivAt_id r).div_const R)
  have hfun : (fun t : ℝ => sin (t / R)) =ᶠ[𝓝 r] sin ∘ fun t : ℝ => t / R := by
    refine EventuallyEq.of_eq ?_
    funext t
    rfl
  simpa using h.congr_of_eventuallyEq hfun

private theorem hasDerivAt_slopeFactor {R r : ℝ} (hs : sin (r / R) ≠ 0) :
    HasDerivAt (fun t : ℝ => (sin (t / R) ^ 2)⁻¹)
      (-2 * cos (r / R) / (R * sin (r / R) ^ 3)) r := by
  have hR : R ≠ 0 := by
    rintro rfl
    simp [sin_zero] at hs
  have hsin := hasDerivAt_sin_over R r
  have hsq : HasDerivAt (fun t : ℝ => sin (t / R) * sin (t / R))
      (cos (r / R) * (1 / R) * sin (r / R) +
        sin (r / R) * (cos (r / R) * (1 / R))) r :=
    hsin.mul hsin
  have hsq' : HasDerivAt (fun t : ℝ => sin (t / R) ^ 2)
      (2 * sin (r / R) * cos (r / R) * (1 / R)) r := by
    convert hsq using 1
    · funext t; ring
    · ring
  have hinv := hsq'.inv (pow_ne_zero 2 hs)
  have heq : -(2 * sin (r / R) * cos (r / R) * (1 / R)) / (sin (r / R) ^ 2) ^ 2 =
      -2 * cos (r / R) / (R * sin (r / R) ^ 3) := by
    field_simp [hs, hR]
  exact heq ▸ hinv

private theorem hasDerivAt_neg_s3Accel {G M R r : ℝ} (hs : sin (r / R) ≠ 0) :
    HasDerivAt (fun t : ℝ => -s3Accel G M R t)
      ((G * M) / R ^ 2 * (-2 * cos (r / R) / (R * sin (r / R) ^ 3))) r := by
  have hfun : (fun t : ℝ => -s3Accel G M R t) =
      fun t => (G * M) / R ^ 2 * (sin (t / R) ^ 2)⁻¹ := by
    funext t
    unfold s3Accel
    simp only [neg_neg, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hfun]
  exact (hasDerivAt_slopeFactor hs).const_mul ((G * M) / R ^ 2)

private theorem eventually_sin_ne {R r : ℝ} (hs : sin (r / R) ≠ 0) :
    ∀ᶠ t in 𝓝 r, sin (t / R) ≠ 0 := by
  refine ContinuousAt.eventually_ne ?_ hs
  exact continuous_sin.continuousAt.comp ((continuous_id.div_const R).continuousAt)

theorem hasDerivAt_deriv_cotPotential {G M R r : ℝ} (hR : R ≠ 0) (hs : sin (r / R) ≠ 0) :
    HasDerivAt (deriv (cotPotential G M R))
      ((G * M) / R ^ 2 * (-2 * cos (r / R) / (R * sin (r / R) ^ 3))) r := by
  refine (hasDerivAt_neg_s3Accel hs).congr_of_eventuallyEq ?_
  filter_upwards [eventually_sin_ne hs] with t ht
  exact (hasDerivAt_cotPotential G M R t hR ht).deriv

/-- Away from the origin the cotangent potential is radially harmonic. -/
theorem radialLaplace_cotPotential {G M R r : ℝ} (hR : R ≠ 0) (hs : sin (r / R) ≠ 0) :
    radialLaplace R (cotPotential G M R) r = 0 := by
  unfold radialLaplace
  rw [(hasDerivAt_deriv_cotPotential hR hs).deriv,
    (hasDerivAt_cotPotential G M R r hR hs).deriv]
  unfold s3Accel
  rw [cot_eq_cos_div_sin]
  field_simp [hR, hs]
  ring

/-- The chart acceleration points toward the mass wherever it is defined. -/
theorem s3Accel_lt_zero {G M R r : ℝ} (hG : 0 < G) (hM : 0 < M) (hR : 0 < R)
    (hs : sin (r / R) ≠ 0) : s3Accel G M R r < 0 := by
  unfold s3Accel
  refine neg_lt_zero.mpr (div_pos (mul_pos hG hM) ?_)
  exact mul_pos (pow_pos hR 2) ((sq_pos_iff).mpr hs)

/-- On the open three-sphere the force stays center-directed, equator included. -/
theorem s3Accel_lt_zero_of_mem_Ioo {G M R r : ℝ}
    (hG : 0 < G) (hM : 0 < M) (hR : 0 < R) (hr : r ∈ Ioo (0 : ℝ) (π * R)) :
    s3Accel G M R r < 0 := by
  have hx : r / R ∈ Ioo (0 : ℝ) π :=
    ⟨div_pos hr.1 hR, (div_lt_iff₀ hR).mpr hr.2⟩
  exact s3Accel_lt_zero hG hM hR (sin_pos_of_mem_Ioo hx).ne'

/-- The negative well is the open hemisphere. The equator is its edge, not a force reversal. -/
theorem cotPotential_neg_iff_lt_equator {G M R r : ℝ}
    (hG : 0 < G) (hM : 0 < M) (hR : 0 < R) (hr : 0 < r) (hπ : r < π * R) :
    cotPotential G M R r < 0 ↔ r < π * R / 2 := by
  have hx : r / R ∈ Ioo (0 : ℝ) π :=
    ⟨div_pos hr hR, (div_lt_iff₀ hR).mpr hπ⟩
  have hsin : 0 < sin (r / R) := sin_pos_of_mem_Ioo hx
  have hcoef : 0 < G * M / R := div_pos (mul_pos hG hM) hR
  unfold cotPotential
  have hsign : -(G * M / R) * cot (r / R) < 0 ↔ 0 < cot (r / R) := by
    rw [neg_mul, neg_lt_zero]
    exact mul_pos_iff_of_pos_left hcoef
  rw [hsign, cot_eq_cos_div_sin, div_pos_iff_of_pos_right hsin]
  have hcos : 0 < cos (r / R) ↔ r / R < π / 2 := by
    constructor
    · intro hpos
      by_contra hge
      push Not at hge
      rcases eq_or_lt_of_le hge with heq | hlt
      · rw [← heq, cos_pi_div_two] at hpos
        exact lt_irrefl _ hpos
      · exact (not_lt_of_gt (cos_neg_of_pi_div_two_lt_of_lt hlt (by linarith [hx.2, pi_pos]))) hpos
    · intro hlt
      exact cos_pos_of_mem_Ioo ⟨lt_trans (neg_lt_zero.mpr pi_div_two_pos) hx.1, hlt⟩
  rw [hcos]
  have hhalf : r / R < π / 2 ↔ r < π * R / 2 := by
    rw [div_lt_iff₀ hR]
    have : (π / 2) * R = π * R / 2 := by ring
    rw [this]
  exact hhalf

/-! ### Newtonian germ -/

theorem tendsto_enhancement_zero :
    Tendsto enhancement (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hopen : Ioo (0 : ℝ) π ∈ 𝓝[>] 0 := by
    rw [mem_nhdsWithin]
    refine ⟨Ioo (-1) π, isOpen_Ioo, ⟨by norm_num, pi_pos⟩, ?_⟩
    intro x hx
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi] at hx
    exact ⟨hx.2, hx.1.2⟩
  have hsinc : Tendsto sinc (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa [sinc_zero] using
      (continuous_sinc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hinv : Tendsto (fun x : ℝ => (sinc x)⁻¹ ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((hsinc.inv₀ one_ne_zero).pow 2)
  refine hinv.congr' ?_
  filter_upwards [hopen] with x hx
  have hs : sin x ≠ 0 := (sin_pos_of_mem_Ioo hx).ne'
  have hx0 : x ≠ 0 := hx.1.ne'
  rw [sinc_of_ne_zero hx0, enhancement]
  field_simp [hs, hx0]

theorem tendsto_compactJacobian_zero :
    Tendsto compactJacobian (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hopen : Ioo (0 : ℝ) π ∈ 𝓝[>] 0 := by
    rw [mem_nhdsWithin]
    refine ⟨Ioo (-1) π, isOpen_Ioo, ⟨by norm_num, pi_pos⟩, ?_⟩
    intro x hx
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi] at hx
    exact ⟨hx.2, hx.1.2⟩
  have hsinc : Tendsto sinc (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa [sinc_zero] using
      (continuous_sinc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hpow : Tendsto (fun x : ℝ => sinc x ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using hsinc.pow 2
  refine hpow.congr' ?_
  filter_upwards [hopen] with x hx
  have hx0 : x ≠ 0 := hx.1.ne'
  rw [sinc_of_ne_zero hx0, compactJacobian]
  field_simp [hx0]

/-- On \((0,1]\), \(\lvert\cot x-(1/x-x/3)\rvert\le x^3/6\). -/
theorem abs_cot_sub_newton {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |cot x - (1 / x - x / 3)| ≤ x ^ 3 / 6 := by
  have hxabs : |x| ≤ 1 := by rwa [abs_of_pos hx]
  have hsinb := abs_sub_le_iff.mp (sin_bound hxabs)
  have hcosb := abs_sub_le_iff.mp (cos_bound hxabs)
  have hs_lb : x - x ^ 3 / 6 - x ^ 5 / 100 ≤ sin x := by
    have h := hsinb.2
    rw [abs_of_pos hx] at h
    linarith
  have hs_ub : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 100 := by
    have h := hsinb.1
    rw [abs_of_pos hx] at h
    linarith
  have hc_lb : 1 - x ^ 2 / 2 - x ^ 4 * (5 / 96) ≤ cos x := by
    have h := hcosb.2
    rw [abs_of_pos hx] at h
    linarith
  have hc_ub : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96) := by
    have h := hcosb.1
    rw [abs_of_pos hx] at h
    linarith
  have hspos : 0 < sin x := sin_pos_of_pos_of_le_one hx hx1
  set a : ℝ := 1 - x ^ 2 / 3
  have ha : 0 < a := by dsimp [a]; nlinarith
  have ha_le : a ≤ 1 := by dsimp [a]; nlinarith
  set sL : ℝ := x - x ^ 3 / 6 - x ^ 5 / 100
  set sU : ℝ := x - x ^ 3 / 6 + x ^ 5 / 100
  set cL : ℝ := 1 - x ^ 2 / 2 - x ^ 4 * (5 / 96)
  set cU : ℝ := 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96)
  have hsin_ge : sL ≤ sin x := by simpa [sL] using hs_lb
  have hsin_le : sin x ≤ sU := by simpa [sU] using hs_ub
  have hcos_ge : cL ≤ cos x := by simpa [cL] using hc_lb
  have hcos_le : cos x ≤ cU := by simpa [cU] using hc_ub
  have hD_le : x * cos x - sin x * a ≤ x * cU - sL * a := by
    have h1 : x * cos x ≤ x * cU := mul_le_mul_of_nonneg_left hcos_le hx.le
    have h2 : sL * a ≤ sin x * a := mul_le_mul_of_nonneg_right hsin_ge ha.le
    linarith
  have hD_ge : x * cL - sU * a ≤ x * cos x - sin x * a := by
    have h1 : x * cL ≤ x * cos x := mul_le_mul_of_nonneg_left hcos_ge hx.le
    have h2 : sin x * a ≤ sU * a := mul_le_mul_of_nonneg_right hsin_le ha.le
    linarith
  have hhi : x * cU - sL * a =
      -x ^ 5 / 18 + (5 / 96) * x ^ 5 + (x ^ 5 / 100) * a := by
    dsimp [cU, sL, a]; ring
  have hlo : x * cL - sU * a =
      -x ^ 5 / 18 - (5 / 96) * x ^ 5 - (x ^ 5 / 100) * a := by
    dsimp [cL, sU, a]; ring
  have hposx : 0 ≤ x ^ 5 := by positivity
  have hS : |x * cos x - sin x * a| ≤ (847 / 7200) * x ^ 5 := by
    have hupper : x * cos x - sin x * a ≤ (847 / 7200) * x ^ 5 := by
      have hdrop : -x ^ 5 / 18 + (5 / 96) * x ^ 5 + (x ^ 5 / 100) * a ≤
          (5 / 96) * x ^ 5 + (1 / 100) * x ^ 5 := by
        have : (x ^ 5 / 100) * a ≤ x ^ 5 / 100 := by nlinarith [ha_le, hposx]
        nlinarith [this, hposx]
      have hsum : (5 / 96 : ℝ) + 1 / 100 ≤ 847 / 7200 := by norm_num
      calc
        x * cos x - sin x * a ≤ x * cU - sL * a := hD_le
        _ = -x ^ 5 / 18 + (5 / 96) * x ^ 5 + (x ^ 5 / 100) * a := hhi
        _ ≤ (5 / 96) * x ^ 5 + (1 / 100) * x ^ 5 := hdrop
        _ ≤ (847 / 7200) * x ^ 5 := by nlinarith [hsum, hposx]
    have hlower : -((847 / 7200) * x ^ 5) ≤ x * cos x - sin x * a := by
      have hcoef : (1 / 18 + 5 / 96 + 1 / 100 : ℝ) = 847 / 7200 := by norm_num
      have hmag : x ^ 5 / 18 + (5 / 96) * x ^ 5 + (x ^ 5 / 100) * a ≤
          (847 / 7200) * x ^ 5 := by
        have : (x ^ 5 / 100) * a ≤ x ^ 5 / 100 := by nlinarith [ha_le, hposx]
        nlinarith [this, hcoef, hposx]
      calc
        -((847 / 7200) * x ^ 5) ≤
            -(x ^ 5 / 18 + (5 / 96) * x ^ 5 + (x ^ 5 / 100) * a) := by
          linarith [hmag]
        _ = x * cL - sU * a := by rw [hlo]; ring
        _ ≤ x * cos x - sin x * a := hD_ge
    exact abs_le.mpr ⟨hlower, hupper⟩
  have hden : 0 < x * sin x := mul_pos hx hspos
  have hform : cot x - (1 / x - x / 3) =
      (x * cos x - sin x * a) / (x * sin x) := by
    rw [cot_eq_cos_div_sin]
    have : 1 / x - x / 3 = a / x := by dsimp [a]; field_simp [hx.ne']
    rw [this]
    field_simp [hspos.ne', hx.ne']
  have hsin_lb2 : x * (247 / 300) ≤ sin x := by
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.le, hx1]
    have hx4_le : x ^ 4 ≤ x ^ 2 := by
      have hfac : x ^ 4 - x ^ 2 = x ^ 2 * (x ^ 2 - 1) := by ring
      have hnonpos : x ^ 4 - x ^ 2 ≤ 0 := by
        rw [hfac]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (sub_nonpos.mpr hx2)
      linarith
    have hid : sL - x * (247 / 300) =
        x * (53 / 300 - x ^ 2 / 6 - x ^ 4 / 100) := by
      dsimp [sL]; ring
    have hdrop : 53 / 300 - x ^ 2 / 6 - x ^ 2 / 100 =
        (53 / 300) * (1 - x ^ 2) := by
      ring_nf
    have hgap : 0 ≤ 53 / 300 - x ^ 2 / 6 - x ^ 4 / 100 := by
      have hge : 53 / 300 - x ^ 2 / 6 - x ^ 2 / 100 ≤
          53 / 300 - x ^ 2 / 6 - x ^ 4 / 100 := by
        linarith only [hx4_le]
      have hnn : 0 ≤ (53 / 300) * (1 - x ^ 2) :=
        mul_nonneg (by norm_num) (sub_nonneg.mpr hx2)
      linarith only [hdrop, hge, hnn]
    have : 0 ≤ sL - x * (247 / 300) := by
      rw [hid]
      exact mul_nonneg hx.le hgap
    linarith only [this, hsin_ge]
  have hden_lb : x ^ 2 * (247 / 300) ≤ x * sin x := by
    calc
      x ^ 2 * (247 / 300) = x * (x * (247 / 300)) := by ring
      _ ≤ x * sin x := mul_le_mul_of_nonneg_left hsin_lb2 hx.le
  have hd0 : 0 < x ^ 2 * (247 / 300) := by positivity
  have hquot : |cot x - (1 / x - x / 3)| ≤
      ((847 / 7200) * x ^ 5) / (x ^ 2 * (247 / 300)) := by
    rw [hform, abs_div, abs_of_pos hden]
    have h1 : |x * cos x - sin x * a| / (x * sin x) ≤
        ((847 / 7200) * x ^ 5) / (x * sin x) :=
      div_le_div_of_nonneg_right hS (le_of_lt hden)
    have h2 : ((847 / 7200) * x ^ 5) / (x * sin x) ≤
        ((847 / 7200) * x ^ 5) / (x ^ 2 * (247 / 300)) :=
      div_le_div_of_nonneg_left (by positivity) hd0 hden_lb
    exact h1.trans h2
  have hsimp : ((847 / 7200) * x ^ 5) / (x ^ 2 * (247 / 300)) =
      (847 / 5928) * x ^ 3 := by
    field_simp [hx.ne']
    ring
  have h5928 : (847 / 5928 : ℝ) ≤ 1 / 6 := by norm_num
  calc
    |cot x - (1 / x - x / 3)| ≤
        ((847 / 7200) * x ^ 5) / (x ^ 2 * (247 / 300)) := hquot
    _ = (847 / 5928) * x ^ 3 := hsimp
    _ ≤ x ^ 3 / 6 := by
      have hmul := mul_le_mul_of_nonneg_right h5928 (pow_nonneg hx.le 3)
      have heq : (1 / 6) * x ^ 3 = x ^ 3 / 6 := by ring
      linarith only [hmul, heq]

/-- For \(0<r\le R\), the cotangent potential is the Newtonian germ up to \(O(r^3/R^4)\). -/
theorem abs_cotPotential_newton {G M R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) :
    |cotPotential G M R r + G * M / r - G * M * r / (3 * R ^ 2)|
      ≤ |G * M| * r ^ 3 / (6 * R ^ 4) := by
  have hx : 0 < r / R := div_pos hr hR
  have hx1 : r / R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa using hrR)
  have hcot := abs_cot_sub_newton hx hx1
  have hR0 : R ≠ 0 := hR.ne'
  have hid : cotPotential G M R r + G * M / r - G * M * r / (3 * R ^ 2) =
      -(G * M / R) * (cot (r / R) - (1 / (r / R) - (r / R) / 3)) := by
    unfold cotPotential
    field_simp [hR0, hr.ne']
    ring
  rw [hid, abs_mul, abs_neg]
  calc
    |G * M / R| * |cot (r / R) - (1 / (r / R) - (r / R) / 3)|
        ≤ |G * M / R| * ((r / R) ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left hcot (abs_nonneg _)
    _ = |G * M| * r ^ 3 / (6 * R ^ 4) := by
      rw [abs_div, abs_of_pos hR]
      field_simp [hR0]

/-! ### Shallow plateau and a saturated enclosed mass -/

theorem strictAntiOn_rotationShape_before :
    StrictAntiOn rotationShape (Ioo (0 : ℝ) plateauRoot) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) ?_ ?_
  · unfold rotationShape
    refine ContinuousOn.div continuousOn_id (continuousOn_sin.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (sin_pos_of_mem_Ioo_zero_pi2
      ⟨hx.1, lt_trans hx.2 plateauRoot_lt_pi_div_two⟩).ne'
  · intro x hx
    rw [interior_Ioo] at hx
    exact deriv_rotationShape_neg_of_lt_root hx

theorem strictMonoOn_rotationShape_after :
    StrictMonoOn rotationShape (Ioo plateauRoot (π / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
  · unfold rotationShape
    refine ContinuousOn.div continuousOn_id (continuousOn_sin.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (sin_pos_of_mem_Ioo_zero_pi2
      ⟨lt_trans (lt_trans (by norm_num) plateauRoot_bounds.1) hx.1, hx.2⟩).ne'
  · intro x hx
    rw [interior_Ioo] at hx
    exact deriv_rotationShape_pos_of_gt_root hx

theorem rotationShape_six_fifths_lt :
    rotationShape (6 / 5 : ℝ) < (148 / 100 : ℝ) := by
  set y : ℝ := 3 / 5
  have hy : |y| ≤ 1 := by norm_num [y]
  have hypos : (0 : ℝ) < y := by norm_num [y]
  have hsin := abs_sub_le_iff.mp (sin_bound hy)
  have hcos := abs_sub_le_iff.mp (cos_bound hy)
  have hsin_lb : y - y ^ 3 / 6 - y ^ 5 / 100 ≤ sin y := by
    have := hsin.1
    rw [abs_of_pos hypos] at this
    linarith
  have hcos_lb : 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) ≤ cos y := by
    have := hcos.1
    rw [abs_of_pos hypos] at this
    linarith
  have hs0 : (0 : ℝ) < y - y ^ 3 / 6 - y ^ 5 / 100 := by norm_num [y]
  have hc0 : (0 : ℝ) < 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) := by norm_num [y]
  have hprod : (91 / 100 : ℝ) < 2 * (y - y ^ 3 / 6 - y ^ 5 / 100) *
      (1 - y ^ 2 / 2 - y ^ 4 * (5 / 96)) := by norm_num [y]
  have hsin2 : sin (2 * y) = 2 * sin y * cos y := sin_two_mul y
  have hy2 : (6 / 5 : ℝ) = 2 * y := by norm_num [y]
  have hge : 2 * (y - y ^ 3 / 6 - y ^ 5 / 100) *
      (1 - y ^ 2 / 2 - y ^ 4 * (5 / 96)) ≤ sin (6 / 5) := by
    rw [hy2, hsin2]
    nlinarith [hsin_lb, hcos_lb, hs0, hc0]
  have hsin_gt : (91 / 100 : ℝ) < sin (6 / 5) := lt_of_lt_of_le hprod hge
  have hspos : (0 : ℝ) < sin (6 / 5) := lt_trans (by norm_num) hsin_gt
  unfold rotationShape
  rw [div_lt_iff₀ (sq_pos_of_pos hspos)]
  have hcmp : (6 / 5 : ℝ) < (148 / 100) * (91 / 100) ^ 2 := by norm_num
  have hsq : (91 / 100 : ℝ) ^ 2 < sin (6 / 5) ^ 2 := by nlinarith [hsin_gt]
  nlinarith [hcmp, hsq]

/-- On \([1,6/5]\), \(f\) stays strictly within a tenth of its minimum. -/
theorem rotationShape_lt_eleven_tenths_f0 {x : ℝ} (hx : x ∈ Icc (1 : ℝ) (6 / 5)) :
    rotationShape x < (11 / 10) * f0 := by
  have hroot_lo : (1 : ℝ) < plateauRoot :=
    lt_trans (by norm_num : (1 : ℝ) < 57 / 50) plateauRoot_bounds.1
  have hroot_hi : plateauRoot < 6 / 5 := plateauRoot_bounds.2
  have h148 : (148 / 100 : ℝ) < (11 / 10) * f0 := by
    calc
      (148 / 100 : ℝ) < (11 / 10) * (135 / 100) := by norm_num
      _ < (11 / 10) * f0 := mul_lt_mul_of_pos_left f0_bounds.1 (by norm_num)
  have hanti : StrictAntiOn rotationShape (Icc (1 : ℝ) plateauRoot) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuousOn_rotationShape_Icc (by norm_num) plateauRoot_lt_pi_div_two) ?_
    intro y hy
    have hyI : y ∈ Ioo (1 : ℝ) plateauRoot := by simpa [interior_Icc] using hy
    exact deriv_rotationShape_neg_of_lt_root ⟨lt_trans (by norm_num) hyI.1, hyI.2⟩
  have hmono : StrictMonoOn rotationShape (Icc plateauRoot (6 / 5)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (continuousOn_rotationShape_Icc (lt_trans (by norm_num) plateauRoot_bounds.1)
        six_fifths_lt_pi_div_two) ?_
    intro y hy
    have hyI : y ∈ Ioo plateauRoot (6 / 5) := by simpa [interior_Icc] using hy
    exact deriv_rotationShape_pos_of_gt_root ⟨hyI.1, lt_trans hyI.2 six_fifths_lt_pi_div_two⟩
  rcases lt_trichotomy x plateauRoot with hlt | heq | hgt
  · rcases eq_or_lt_of_le hx.1 with rfl | hx1
    · exact lt_trans rotationShape_one_bounds.2 h148
    · have hlt_shape : rotationShape x < rotationShape 1 :=
        hanti ⟨le_rfl, hroot_lo.le⟩ ⟨hx.1, hlt.le⟩ hx1
      exact lt_trans hlt_shape (lt_trans rotationShape_one_bounds.2 h148)
  · subst heq
    have hf0 : (0 : ℝ) < f0 := lt_trans (by norm_num) f0_bounds.1
    simpa [f0] using (lt_mul_of_one_lt_left hf0 (by norm_num : (1 : ℝ) < 11 / 10))
  · rcases eq_or_lt_of_le hx.2 with rfl | hxhi
    · exact lt_trans rotationShape_six_fifths_lt h148
    · exact lt_trans (hmono ⟨hgt.le, hx.2⟩ ⟨hroot_hi.le, le_rfl⟩ hxhi)
        (lt_trans rotationShape_six_fifths_lt h148)

theorem strictAntiOn_s3CircularSpeedSq {G M R : ℝ}
    (hG : 0 < G) (hM : 0 < M) (hR : 0 < R) :
    StrictAntiOn (s3CircularSpeedSq G M R) (Ioo (0 : ℝ) (plateauRoot * R)) := by
  have hpos : 0 < G * M / R := div_pos (mul_pos hG hM) hR
  have hR0 : R ≠ 0 := hR.ne'
  intro r hr s hs hrs
  have hmap : ∀ t ∈ Ioo (0 : ℝ) (plateauRoot * R), t / R ∈ Ioo (0 : ℝ) plateauRoot := by
    intro t ht
    exact ⟨div_pos ht.1 hR, (div_lt_iff₀ hR).mpr ht.2⟩
  have hsinr : sin (r / R) ≠ 0 :=
    (sin_pos_of_mem_Ioo_zero_pi2
      ⟨(hmap r hr).1, lt_trans (hmap r hr).2 plateauRoot_lt_pi_div_two⟩).ne'
  have hsins : sin (s / R) ≠ 0 :=
    (sin_pos_of_mem_Ioo_zero_pi2
      ⟨(hmap s hs).1, lt_trans (hmap s hs).2 plateauRoot_lt_pi_div_two⟩).ne'
  rw [s3CircularSpeedSq_eq_shape G M R r hR0 hsinr,
    s3CircularSpeedSq_eq_shape G M R s hR0 hsins]
  exact mul_lt_mul_of_pos_left
    (strictAntiOn_rotationShape_before (hmap r hr) (hmap s hs)
      (div_lt_div_of_pos_right hrs hR)) hpos

theorem strictMonoOn_s3CircularSpeedSq {G M R : ℝ}
    (hG : 0 < G) (hM : 0 < M) (hR : 0 < R) :
    StrictMonoOn (s3CircularSpeedSq G M R) (Ioo (plateauRoot * R) (π / 2 * R)) := by
  have hpos : 0 < G * M / R := div_pos (mul_pos hG hM) hR
  have hR0 : R ≠ 0 := hR.ne'
  intro r hr s hs hrs
  have hmap : ∀ t ∈ Ioo (plateauRoot * R) (π / 2 * R),
      t / R ∈ Ioo plateauRoot (π / 2) := by
    intro t ht
    exact ⟨(lt_div_iff₀ hR).mpr ht.1, (div_lt_iff₀ hR).mpr ht.2⟩
  have hembed : ∀ t ∈ Ioo (plateauRoot * R) (π / 2 * R),
      t / R ∈ Ioo (0 : ℝ) (π / 2) := by
    intro t ht
    exact ⟨lt_trans (lt_trans (by norm_num) plateauRoot_bounds.1) (hmap t ht).1, (hmap t ht).2⟩
  have hsinr : sin (r / R) ≠ 0 := (sin_pos_of_mem_Ioo_zero_pi2 (hembed r hr)).ne'
  have hsins : sin (s / R) ≠ 0 := (sin_pos_of_mem_Ioo_zero_pi2 (hembed s hs)).ne'
  rw [s3CircularSpeedSq_eq_shape G M R r hR0 hsinr,
    s3CircularSpeedSq_eq_shape G M R s hR0 hsins]
  exact mul_lt_mul_of_pos_left
    (strictMonoOn_rotationShape_after (hmap r hr) (hmap s hs)
      (div_lt_div_of_pos_right hrs hR)) hpos

theorem s3CircularSpeedSq_flat {G M R r : ℝ}
    (hG : 0 < G) (hM : 0 < M) (hR : 0 < R)
    (hr : r / R ∈ Icc (1 : ℝ) (6 / 5)) :
    s3CircularSpeedSq G M R r < (11 / 10) * ((G * M / R) * f0) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hxπ : r / R < π / 2 := lt_of_le_of_lt hr.2 six_fifths_lt_pi_div_two
  have hs : sin (r / R) ≠ 0 :=
    (sin_pos_of_mem_Ioo_zero_pi2 ⟨lt_of_lt_of_le (by norm_num) hr.1, hxπ⟩).ne'
  rw [s3CircularSpeedSq_eq_shape G M R r hR0 hs]
  have hpos : 0 < G * M / R := div_pos (mul_pos hG hM) hR
  calc
    (G * M / R) * rotationShape (r / R)
        < (G * M / R) * ((11 / 10) * f0) :=
      mul_lt_mul_of_pos_left (rotationShape_lt_eleven_tenths_f0 hr) hpos
    _ = (11 / 10) * ((G * M / R) * f0) := by ring

/-- Circular speed on a spherical chart, with enclosed mass `M r`. -/
noncomputable def enclosedCircularSpeedSq (G R : ℝ) (M : ℝ → ℝ) (r : ℝ) : ℝ :=
  (G * M r / R) * rotationShape (r / R)

theorem enclosedCircularSpeedSq_const {G R M0 : ℝ} {M : ℝ → ℝ} {a b : ℝ}
    (hM : ∀ r ∈ Icc a b, M r = M0) {r : ℝ} (hr : r ∈ Icc a b) :
    enclosedCircularSpeedSq G R M r = (G * M0 / R) * rotationShape (r / R) := by
  simp [enclosedCircularSpeedSq, hM r hr]

theorem enclosedCircularSpeedSq_const_eq_point {G R M0 r : ℝ} {M : ℝ → ℝ}
    (hR : R ≠ 0) (hs : sin (r / R) ≠ 0) (hM : M r = M0) :
    enclosedCircularSpeedSq G R M r = s3CircularSpeedSq G M0 R r := by
  rw [enclosedCircularSpeedSq, hM, s3CircularSpeedSq_eq_shape G M0 R r hR hs]

theorem strictAntiOn_enclosedCircularSpeedSq {G M0 R : ℝ} {M : ℝ → ℝ}
    (hG : 0 < G) (hM0 : 0 < M0) (hR : 0 < R)
    (hM : ∀ r ∈ Ioo (0 : ℝ) (plateauRoot * R), M r = M0) :
    StrictAntiOn (enclosedCircularSpeedSq G R M) (Ioo (0 : ℝ) (plateauRoot * R)) := by
  have hspeed := strictAntiOn_s3CircularSpeedSq hG hM0 hR
  intro r hr s hs hrs
  have hR0 : R ≠ 0 := hR.ne'
  have hsin : ∀ t ∈ Ioo (0 : ℝ) (plateauRoot * R), sin (t / R) ≠ 0 := by
    intro t ht
    have ht' : t / R ∈ Ioo (0 : ℝ) plateauRoot :=
      ⟨div_pos ht.1 hR, (div_lt_iff₀ hR).mpr ht.2⟩
    exact (sin_pos_of_mem_Ioo_zero_pi2
      ⟨ht'.1, lt_trans ht'.2 plateauRoot_lt_pi_div_two⟩).ne'
  rw [enclosedCircularSpeedSq_const_eq_point hR0 (hsin r hr) (hM r hr),
    enclosedCircularSpeedSq_const_eq_point hR0 (hsin s hs) (hM s hs)]
  exact hspeed hr hs hrs

theorem strictMonoOn_enclosedCircularSpeedSq {G M0 R : ℝ} {M : ℝ → ℝ}
    (hG : 0 < G) (hM0 : 0 < M0) (hR : 0 < R)
    (hM : ∀ r ∈ Ioo (plateauRoot * R) (π / 2 * R), M r = M0) :
    StrictMonoOn (enclosedCircularSpeedSq G R M)
      (Ioo (plateauRoot * R) (π / 2 * R)) := by
  have hspeed := strictMonoOn_s3CircularSpeedSq hG hM0 hR
  intro r hr s hs hrs
  have hR0 : R ≠ 0 := hR.ne'
  have hsin : ∀ t ∈ Ioo (plateauRoot * R) (π / 2 * R), sin (t / R) ≠ 0 := by
    intro t ht
    have ht' : t / R ∈ Ioo plateauRoot (π / 2) :=
      ⟨(lt_div_iff₀ hR).mpr ht.1, (div_lt_iff₀ hR).mpr ht.2⟩
    exact (sin_pos_of_mem_Ioo_zero_pi2
      ⟨lt_trans (lt_trans (by norm_num) plateauRoot_bounds.1) ht'.1, ht'.2⟩).ne'
  rw [enclosedCircularSpeedSq_const_eq_point hR0 (hsin r hr) (hM r hr),
    enclosedCircularSpeedSq_const_eq_point hR0 (hsin s hs) (hM s hs)]
  exact hspeed hr hs hrs

end Gravity

end DstDiophantine
