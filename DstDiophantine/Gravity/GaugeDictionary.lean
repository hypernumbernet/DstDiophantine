import DstDiophantine.Gravity.JTDictionary
import DstDiophantine.Gravity.Coframe
import DstDiophantine.Gravity.Schwarzschild
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Amplification
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gauge-level \(J\)–\(T\) dictionary for static radial boosts

The closed dictionary of `Gravity.JTDictionary` uses only \(\sqrt{A}=e^{-\varphi}\)
and positivity of \(A\). It therefore holds for an arbitrary static radial-boost
gauge, not merely the Schwarzschild factor \(A=1-r_s/r\).

## Proved

* \(T=(4/r^2)(\cosh\varphi-1)\) whenever \(0<A\) and \(r\neq 0\).
* \(r^2 T=4(\cosh\sqrt{2J}-1)\) on that gauge, with sandwich \(4J\le r^2 T\).
* Real radial boosts cannot produce \(T<0\); repulsive layers require the
  elliptic sector.
* Chart densities satisfy \(e\cdot(4J/r^2)\le e\cdot T\), with equality only
  in the flat limit (when \(\sin\theta>0\)).

## Not claimed

* A dictionary for a general tetrad field (off-axis or with translations).
* Identification of the proposed action \(\int J\) with the TEGR integral of \(T\).
-/

namespace DstDiophantine

namespace Gravity

open Invariant Amplification Real Set Filter
open scoped Topology

/-! ### Abstract radial-boost gauge -/

/-- Rapidity of a static radial boost with time-leg factor \(A>0\). -/
noncomputable def rapidityOfA (A : ℝ) : ℝ :=
  -(1 / 2) * Real.log A

/-- Weitzenböck scalar of the diagonal coframe with time-leg \(\sqrt{A}\). -/
noncomputable def teleparallelTofA (A r : ℝ) : ℝ :=
  (2 / r ^ 2) * (1 - Real.sqrt A) ^ 2 / Real.sqrt A

/-- Pure-boost torsional parameter of the gauge. -/
noncomputable def gaugeBoostParams (A : ℝ) : Operations.TorsionParams :=
  Amplification.pureBoost (rapidityOfA A)

theorem J_gaugeBoostParams (A : ℝ) :
    J (gaugeBoostParams A) = (1 / 2) * (rapidityOfA A) ^ 2 := by
  simpa [gaugeBoostParams] using Amplification.J_pureBoost (rapidityOfA A)

theorem sqrt_eq_exp_neg_rapidity {A : ℝ} (hA : 0 < A) :
    Real.sqrt A = Real.exp (-rapidityOfA A) := by
  have hlog : (1 / 2) * Real.log A = Real.log (Real.sqrt A) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hA]
  unfold rapidityOfA
  have : -(-(1 / 2) * Real.log A) = (1 / 2) * Real.log A := by ring
  rw [this, hlog, Real.exp_log (Real.sqrt_pos.mpr hA)]

theorem rapidityOfA_eq_zero_iff {A : ℝ} (hA : 0 < A) :
    rapidityOfA A = 0 ↔ A = 1 := by
  unfold rapidityOfA
  constructor
  · intro h
    have hlog : Real.log A = 0 := by linarith
    calc A = Real.exp (Real.log A) := (Real.exp_log hA).symm
      _ = Real.exp 0 := by rw [hlog]
      _ = 1 := Real.exp_zero
  · intro h
    simp [h, Real.log_one]

/-! ### Closed form \(T=(4/r^2)(\cosh\varphi-1)\) -/

theorem teleparallelTofA_eq_cosh {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    teleparallelTofA A r =
      (4 / r ^ 2) * (cosh (rapidityOfA A) - 1) := by
  set φ := rapidityOfA A
  set s := Real.sqrt A
  have hs : s = Real.exp (-φ) := sqrt_eq_exp_neg_rapidity hA
  have hspos : 0 < s := by
    rw [hs]
    exact Real.exp_pos _
  have hsne : s ≠ 0 := hspos.ne'
  have hfrac : (1 - s) ^ 2 / s = 2 * (cosh φ - 1) := by
    have hexp : Real.exp φ = s⁻¹ := by
      rw [hs, Real.exp_neg, inv_inv]
    calc (1 - s) ^ 2 / s
        = s⁻¹ - 2 + s := by field_simp [hsne]; ring
      _ = Real.exp φ - 2 + Real.exp (-φ) := by rw [hexp, hs]
      _ = 2 * (cosh φ - 1) := by rw [Real.cosh_eq φ]; ring
  calc teleparallelTofA A r
      = (2 / r ^ 2) * (1 - s) ^ 2 / s := by
          unfold teleparallelTofA; simp [s]
    _ = (2 / r ^ 2) * ((1 - s) ^ 2 / s) := by field_simp [hsne]
    _ = (2 / r ^ 2) * (2 * (cosh φ - 1)) := by rw [hfrac]
    _ = (4 / r ^ 2) * (cosh φ - 1) := by ring

theorem teleparallelTofA_eq_sinh_half_sq {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    teleparallelTofA A r =
      (8 / r ^ 2) * sinh (rapidityOfA A / 2) ^ 2 := by
  rw [teleparallelTofA_eq_cosh hA hr, cosh_sub_one_eq_two_sinh_half_sq]
  ring

theorem r_sq_teleparallelTofA_eq {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofA A r = 4 * (cosh (rapidityOfA A) - 1) := by
  rw [teleparallelTofA_eq_cosh hA hr]
  field_simp [hr]

theorem r_sq_T_ofA_eq_four_cosh_sqrt {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofA A r =
      4 * (cosh (Real.sqrt (2 * J (gaugeBoostParams A))) - 1) := by
  have hJ : 0 ≤ J (gaugeBoostParams A) := by
    rw [J_gaugeBoostParams]
    positivity
  have hsq : Real.sqrt (2 * J (gaugeBoostParams A)) = |rapidityOfA A| := by
    rw [J_gaugeBoostParams]
    have : 2 * ((1 / 2) * rapidityOfA A ^ 2) = rapidityOfA A ^ 2 := by ring
    rw [this, Real.sqrt_sq_eq_abs]
  rw [r_sq_teleparallelTofA_eq hA hr, hsq, Real.cosh_abs]

theorem r_sq_T_ofA_eq_four_coshDefect {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofA A r =
      4 * coshDefect (J (gaugeBoostParams A)) := by
  have hJ : 0 ≤ J (gaugeBoostParams A) := by
    rw [J_gaugeBoostParams]
    positivity
  rw [r_sq_T_ofA_eq_four_cosh_sqrt hA hr, coshDefect_of_nonneg hJ]

/-! ### Positivity: real radial boosts cannot produce \(T<0\) -/

theorem teleparallelTofA_nonneg {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    0 ≤ teleparallelTofA A r := by
  have hspos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  unfold teleparallelTofA
  positivity

theorem teleparallelTofA_eq_zero_iff {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    teleparallelTofA A r = 0 ↔ A = 1 := by
  have hspos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hr2 : r ^ 2 ≠ 0 := (sq_pos_of_ne_zero hr).ne'
  constructor
  · intro h
    have hnum : (1 - Real.sqrt A) ^ 2 = 0 := by
      unfold teleparallelTofA at h
      have hsne : Real.sqrt A ≠ 0 := hspos.ne'
      field_simp [hr2, hsne] at h
      nlinarith [sq_nonneg (1 - Real.sqrt A)]
    have : Real.sqrt A = 1 := by
      have : 1 - Real.sqrt A = 0 := sq_eq_zero_iff.mp hnum
      linarith
    have hsq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA.le
    calc A = (Real.sqrt A) ^ 2 := hsq.symm
      _ = 1 := by rw [this, one_pow]
  · intro h
    simp [teleparallelTofA, h]

theorem teleparallelTofA_pos_of_ne_one {A r : ℝ}
    (hA : 0 < A) (hA1 : A ≠ 1) (hr : r ≠ 0) :
    0 < teleparallelTofA A r := by
  refine lt_of_le_of_ne (teleparallelTofA_nonneg hA hr) ?_
  intro h0
  exact hA1 ((teleparallelTofA_eq_zero_iff hA hr).mp h0.symm)

/-- A real static radial boost cannot produce a negative Weitzenböck scalar. -/
theorem teleparallelTofA_not_lt_zero {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    ¬ teleparallelTofA A r < 0 :=
  not_lt.mpr (teleparallelTofA_nonneg hA hr)

/-- Repulsive layers \(T<0\) on the admissible cone require a negative \(J\)
(elliptic sector). A real radial boost has \(J\ge 0\) and cannot supply them. -/
theorem repulsive_requires_negative_J {Jval r : ℝ} (hr : r ≠ 0)
    (hbound : |Jval| ≤ JMax) (hT : teleparallelTofJ Jval r < 0) :
    Jval < 0 := by
  have hsign := sign_T_eq_sign_J_on_cone hr hbound
  have hneg : SignType.sign (teleparallelTofJ Jval r) = -1 := sign_neg hT
  rw [hsign] at hneg
  exact sign_eq_neg_one_iff.mp hneg

/-! ### Sandwich \(4J\le r^2 T\) -/

theorem abs_le_abs_sinh (x : ℝ) : |x| ≤ |sinh x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (sinh_nonneg_iff.mpr hx)]
    rcases eq_or_lt_of_le hx with rfl | hpos
    · simp
    · exact (self_lt_sinh_iff.mpr hpos).le
  · have hx0 : 0 ≤ -x := neg_nonneg.mpr hx
    rw [abs_of_nonpos hx, abs_of_nonpos (sinh_nonpos_iff.mpr hx), ← sinh_neg]
    rcases eq_or_lt_of_le hx0 with h0 | hpos
    · have : x = 0 := neg_eq_zero.mp h0.symm
      simp [this]
    · exact (self_lt_sinh_iff.mpr hpos).le

theorem four_J_le_r_sq_T_ofA {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    4 * J (gaugeBoostParams A) ≤ r ^ 2 * teleparallelTofA A r := by
  rw [J_gaugeBoostParams, teleparallelTofA_eq_sinh_half_sq hA hr]
  set φ := rapidityOfA A
  have hne : r ^ 2 ≠ 0 := (sq_pos_of_ne_zero hr).ne'
  have hsinh : |φ / 2| ≤ |sinh (φ / 2)| := abs_le_abs_sinh (φ / 2)
  have hsq : (φ / 2) ^ 2 ≤ sinh (φ / 2) ^ 2 := by
    simpa [sq_abs] using (sq_le_sq.mpr hsinh)
  field_simp [hne]
  nlinarith [sq_nonneg φ, sq_nonneg (sinh (φ / 2))]

theorem four_J_lt_r_sq_T_ofA {A r : ℝ} (hA : 0 < A) (hA1 : A ≠ 1) (hr : r ≠ 0) :
    4 * J (gaugeBoostParams A) < r ^ 2 * teleparallelTofA A r := by
  have hφ : rapidityOfA A ≠ 0 := (rapidityOfA_eq_zero_iff hA).not.mpr hA1
  rw [J_gaugeBoostParams, teleparallelTofA_eq_sinh_half_sq hA hr]
  set φ := rapidityOfA A
  have hhalf : φ / 2 ≠ 0 := div_ne_zero hφ (by norm_num)
  have hne : r ^ 2 ≠ 0 := (sq_pos_of_ne_zero hr).ne'
  have hsinh : |φ / 2| < |sinh (φ / 2)| := by
    refine lt_of_le_of_ne (abs_le_abs_sinh (φ / 2)) ?_
    intro heq
    rcases le_total 0 (φ / 2) with hx | hx
    · have hx0 : 0 < φ / 2 := lt_of_le_of_ne hx hhalf.symm
      have hstrict : φ / 2 < sinh (φ / 2) := self_lt_sinh_iff.mpr hx0
      have h1 : |φ / 2| = φ / 2 := abs_of_nonneg hx
      have h2 : |sinh (φ / 2)| = sinh (φ / 2) :=
        abs_of_nonneg (sinh_nonneg_iff.mpr hx)
      linarith
    · have hx0 : φ / 2 < 0 := lt_of_le_of_ne hx hhalf
      have hneg : 0 < -(φ / 2) := neg_pos.mpr hx0
      have hstrict : -(φ / 2) < sinh (-(φ / 2)) := self_lt_sinh_iff.mpr hneg
      have h1 : |φ / 2| = -(φ / 2) := abs_of_nonpos hx
      have h2 : |sinh (φ / 2)| = sinh (-(φ / 2)) := by
        rw [abs_of_nonpos (sinh_nonpos_iff.mpr hx), ← sinh_neg]
      linarith
  have hsq : (φ / 2) ^ 2 < sinh (φ / 2) ^ 2 := sq_lt_sq.mpr hsinh
  field_simp [hne]
  nlinarith [sq_nonneg φ, sq_nonneg (sinh (φ / 2))]

theorem four_J_eq_r_sq_T_iff {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    4 * J (gaugeBoostParams A) = r ^ 2 * teleparallelTofA A r ↔ A = 1 := by
  constructor
  · intro heq
    by_contra hA1
    exact (four_J_lt_r_sq_T_ofA hA hA1 hr).ne heq
  · intro h
    subst h
    have h1 : 0 < (1 : ℝ) := by norm_num
    have hφ : rapidityOfA 1 = 0 := by simp [rapidityOfA, Real.log_one]
    rw [J_gaugeBoostParams, teleparallelTofA_eq_cosh h1 hr, hφ]
    simp

/-! ### Kernel inequality \(J\le\cosh\sqrt{2J}-1\) -/

theorem coshDefect_ge_self {Jval : ℝ} (hJ : 0 ≤ Jval) :
    Jval ≤ coshDefect Jval := by
  rw [coshDefect_of_nonneg hJ]
  set x := Real.sqrt (2 * Jval) with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hJeq : Jval = x ^ 2 / 2 := by
    have : x ^ 2 = 2 * Jval := by
      rw [hx, Real.sq_sqrt (by positivity : 0 ≤ 2 * Jval)]
    linarith
  have hsinh : |x / 2| ≤ |sinh (x / 2)| := abs_le_abs_sinh (x / 2)
  have hsq : (x / 2) ^ 2 ≤ sinh (x / 2) ^ 2 := by
    simpa [sq_abs] using (sq_le_sq.mpr hsinh)
  have hcosh := cosh_sub_one_eq_two_sinh_half_sq x
  rw [hJeq, hcosh]
  nlinarith [sq_nonneg x, sq_nonneg (sinh (x / 2))]

theorem coshDefect_eq_self_iff {Jval : ℝ} (hJ : 0 ≤ Jval) :
    coshDefect Jval = Jval ↔ Jval = 0 := by
  constructor
  · intro heq
    set x := Real.sqrt (2 * Jval) with hx
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hJeq : Jval = x ^ 2 / 2 := by
      have : x ^ 2 = 2 * Jval := by
        rw [hx, Real.sq_sqrt (by positivity : 0 ≤ 2 * Jval)]
      linarith
    rw [coshDefect_of_nonneg hJ, ← hx] at heq
    have hcosh := cosh_sub_one_eq_two_sinh_half_sq x
    rw [hcosh, hJeq] at heq
    rcases eq_or_lt_of_le hx0 with h0 | hpos
    · rw [← h0] at hJeq
      simpa using hJeq
    · have hhalf : 0 < x / 2 := div_pos hpos (by norm_num)
      have hsq : (x / 2) ^ 2 = sinh (x / 2) ^ 2 := by nlinarith [sq_nonneg x]
      have habs : |x / 2| = |sinh (x / 2)| :=
        (sq_eq_sq_iff_abs_eq_abs (a := x / 2) (b := sinh (x / 2))).mp hsq
      have : x / 2 < sinh (x / 2) := self_lt_sinh_iff.mpr hhalf
      rw [abs_of_nonneg hhalf.le, abs_of_nonneg (sinh_nonneg_iff.mpr hhalf.le)] at habs
      linarith
  · intro h
    simp [h, coshDefect_zero]

/-! ### Chart volume and action densities -/

/-- Diagonal legs of a static radial boost in spherical coordinates. -/
noncomputable def boostSphericalDiag (A r θ : ℝ) : Fin 4 → ℝ
  | 0 => Real.sqrt A
  | 1 => (Real.sqrt A)⁻¹
  | 2 => r
  | 3 => r * Real.sin θ

theorem coframeDet_boostSpherical {A r θ : ℝ} (hA : 0 < A) :
    coframeDet (boostSphericalDiag A r θ) = r ^ 2 * Real.sin θ := by
  have hs : Real.sqrt A ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  simp only [coframeDet, boostSphericalDiag]
  field_simp [hs]

theorem coframeDet_schwarzschild {rs r θ : ℝ} (h : IsExterior rs r) :
    coframeDet (schwarzschildDiag rs r θ) = r ^ 2 * Real.sin θ := by
  have hA := schwarzschildA_pos h
  have hs : Real.sqrt (schwarzschildA rs r) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  simp only [coframeDet, schwarzschildDiag]
  field_simp [hs]

/-- TEGR chart density \(e\,T\) on the spherical radial-boost coframe. -/
noncomputable def tegrDensity (A r θ : ℝ) : ℝ :=
  coframeDet (boostSphericalDiag A r θ) * teleparallelTofA A r

/-- Algebraic chart density \(e\cdot(4J/r^2)\). -/
noncomputable def algebraicDensity (A r θ : ℝ) : ℝ :=
  coframeDet (boostSphericalDiag A r θ) *
    (4 * J (gaugeBoostParams A) / r ^ 2)

theorem algebraicDensity_le_tegrDensity {A r θ : ℝ}
    (hA : 0 < A) (hr : r ≠ 0) (hsin : 0 ≤ Real.sin θ) :
    algebraicDensity A r θ ≤ tegrDensity A r θ := by
  unfold algebraicDensity tegrDensity
  rw [coframeDet_boostSpherical hA]
  have hJ := four_J_le_r_sq_T_ofA hA hr
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hfac : 0 ≤ r ^ 2 * Real.sin θ := mul_nonneg hr2.le hsin
  have : 4 * J (gaugeBoostParams A) / r ^ 2 ≤ teleparallelTofA A r := by
    rw [div_le_iff₀ hr2]
    linarith
  nlinarith

theorem algebraicDensity_eq_tegrDensity_iff {A r θ : ℝ}
    (hA : 0 < A) (hr : r ≠ 0) (hsin : 0 < Real.sin θ) :
    algebraicDensity A r θ = tegrDensity A r θ ↔ A = 1 := by
  constructor
  · intro heq
    unfold algebraicDensity tegrDensity at heq
    rw [coframeDet_boostSpherical hA] at heq
    have hr2 : r ^ 2 ≠ 0 := (sq_pos_of_ne_zero hr).ne'
    have hsne : Real.sin θ ≠ 0 := hsin.ne'
    have hscale : (r ^ 2 * Real.sin θ) ≠ 0 := mul_ne_zero hr2 hsne
    have hdiv : 4 * J (gaugeBoostParams A) / r ^ 2 = teleparallelTofA A r :=
      mul_left_cancel₀ hscale heq
    have hJeq : 4 * J (gaugeBoostParams A) = r ^ 2 * teleparallelTofA A r := by
      have := (div_eq_iff hr2).mp hdiv
      linarith
    exact (four_J_eq_r_sq_T_iff hA hr).mp hJeq
  · intro h
    subst h
    have h1 : 0 < (1 : ℝ) := by norm_num
    have hφ : rapidityOfA 1 = 0 := by simp [rapidityOfA, Real.log_one]
    unfold algebraicDensity tegrDensity
    rw [J_gaugeBoostParams, teleparallelTofA_eq_cosh h1 hr, hφ]
    simp

/-! ### Weak-field ratio \(r^2 T/(4J)\to 1\) as \(A\to 1\) -/

theorem r_sq_T_div_four_J_ofA {A r : ℝ} (hA : 0 < A) (hA1 : A ≠ 1) (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofA A r / (4 * J (gaugeBoostParams A)) =
      (sinh (rapidityOfA A / 2) / (rapidityOfA A / 2)) ^ 2 := by
  have hφ : rapidityOfA A ≠ 0 := (rapidityOfA_eq_zero_iff hA).not.mpr hA1
  have hhalf : rapidityOfA A / 2 ≠ 0 := div_ne_zero hφ (by norm_num)
  rw [J_gaugeBoostParams, teleparallelTofA_eq_sinh_half_sq hA hr]
  set φ := rapidityOfA A
  have hne : r ^ 2 ≠ 0 := (sq_pos_of_ne_zero hr).ne'
  field_simp [hne, hhalf]
  ring

theorem tendsto_rapidityOfA :
    Tendsto rapidityOfA (𝓝 1) (𝓝 0) := by
  have hlog : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
    simpa [Real.log_one] using
      (continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
  unfold rapidityOfA
  simpa using hlog.const_mul (-(1 / 2 : ℝ))

/-! ### Schwarzschild as a specialisation -/

theorem schwarzschildRapidity_eq_rapidityOfA (rs r : ℝ) :
    schwarzschildRapidity rs r = rapidityOfA (schwarzschildA rs r) := by
  simp [schwarzschildRapidity, rapidityOfA, schwarzschildA]

theorem schwarzschildTeleparallelT_eq_teleparallelTofA (rs r : ℝ) :
    schwarzschildTeleparallelT rs r = teleparallelTofA (schwarzschildA rs r) r :=
  rfl

theorem radialBoostParams_eq_gauge (rs r : ℝ) :
    radialBoostParams rs r = gaugeBoostParams (schwarzschildA rs r) := by
  simp [radialBoostParams, gaugeBoostParams, schwarzschildRapidity_eq_rapidityOfA]

end Gravity

end DstDiophantine
