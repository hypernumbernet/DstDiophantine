import DstDiophantine.Gravity.SI
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Basic
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
algebra. No theorem asserts `dst_derives_a0`.

Paper claims \(f_0\approx 1.10\) and Milky-Way \(R\approx 27\,\mathrm{kpc}\) are
machine-rejected on the SI stand-ins.
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

end Gravity

end DstDiophantine
