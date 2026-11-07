import DstDiophantine.Gravity.Coframe
import DstDiophantine.Gravity.Schwarzschild
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Kerr chart

On `Σ > 0` and `Δ > 0` the orthonormal coframe
`e⁰ = √(Δ/Σ) (dt − a sin²θ dφ)`, `e¹ = √(Σ/Δ) dr`, `e² = √Σ dθ`,
`e³ = sinθ/√Σ ((r²+a²) dφ − a dt)` induces the Kerr metric. The `(t,φ)`
block has determinant `-Δ sin²θ`. Vanishing spin returns the exterior
Schwarzschild coframe of gravitational radius `2M`.

A pure boost in the `(t,φ)` plane of a diagonal frame writes no cross
term. The Kerr cross term belongs to the coframe above.

## Not claimed

* The horizon `Δ = 0`, where the classical radial leg diverges. Division
  by zero is not that leg.
* A real coframe on `Δ < 0`.
* That the Kerr coframe is a pure boost, or that `J = ½ ψ²` is derived.
* A teleparallel scalar for this coframe.
-/

namespace DstDiophantine

namespace Gravity

open Real Set

/-! ### Metric coefficients -/

/-- `Σ = r² + a² cos²θ`. -/
noncomputable def kerrSigma (a r θ : ℝ) : ℝ :=
  r ^ 2 + a ^ 2 * Real.cos θ ^ 2

/-- `Δ = r² − 2Mr + a²`. -/
noncomputable def kerrDelta (M a r : ℝ) : ℝ :=
  r ^ 2 - 2 * M * r + a ^ 2

/-- Azimuthal coefficient
`g_φφ = sin²θ ((r²+a²)Σ + 2Mra² sin²θ) / Σ`. -/
noncomputable def kerrGφφ (M a r θ : ℝ) : ℝ :=
  Real.sin θ ^ 2 *
      ((r ^ 2 + a ^ 2) * kerrSigma a r θ + 2 * M * r * a ^ 2 * Real.sin θ ^ 2) /
    kerrSigma a r θ

/-- Cross term `g_tφ = −2Mar sin²θ / Σ`. -/
noncomputable def kerrGtφ (M a r θ : ℝ) : ℝ :=
  -2 * M * a * r * Real.sin θ ^ 2 / kerrSigma a r θ

/-- Coordinate components of the Kerr metric. Indices `(t,r,θ,φ)`. -/
noncomputable def kerrMetric (M a r θ : ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 0 => -(1 - 2 * M * r / kerrSigma a r θ)
  | 1, 1 => kerrSigma a r θ / kerrDelta M a r
  | 2, 2 => kerrSigma a r θ
  | 3, 3 => kerrGφφ M a r θ
  | 0, 3 => kerrGtφ M a r θ
  | 3, 0 => kerrGtφ M a r θ
  | _, _ => 0

theorem cos_sq_eq_one_sub_sin_sq (θ : ℝ) : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [eq_sub_iff_add_eq, add_comm]
  exact h

theorem kerr_azimuth_algebra (M a r θ : ℝ) :
    (r ^ 2 + a ^ 2) ^ 2 - kerrDelta M a r * a ^ 2 * Real.sin θ ^ 2 =
      (r ^ 2 + a ^ 2) * kerrSigma a r θ +
        2 * M * r * a ^ 2 * Real.sin θ ^ 2 := by
  unfold kerrDelta kerrSigma
  rw [cos_sq_eq_one_sub_sin_sq θ]
  ring

theorem kerr_timePhi_det (M a r θ : ℝ) (hSig : kerrSigma a r θ ≠ 0) :
    -(1 - 2 * M * r / kerrSigma a r θ) * kerrGφφ M a r θ - kerrGtφ M a r θ ^ 2 =
      -kerrDelta M a r * Real.sin θ ^ 2 := by
  unfold kerrGφφ kerrGtφ kerrSigma kerrDelta at *
  rw [cos_sq_eq_one_sub_sin_sq θ] at hSig ⊢
  field_simp [hSig]
  ring

/-! ### Coframe -/

/-- Orthonormal Kerr coframe. Real on `Δ ≥ 0`, classically normalised on `Δ > 0`.
Boolean tests on `Fin.val` reduce on concrete indices. -/
noncomputable def kerrCoframe (M a r θ : ℝ) : Coframe :=
  fun b μ =>
    if b.val == 0 && μ.val == 0 then Real.sqrt (kerrDelta M a r / kerrSigma a r θ)
    else if b.val == 0 && μ.val == 3 then
      -a * Real.sin θ ^ 2 * Real.sqrt (kerrDelta M a r / kerrSigma a r θ)
    else if b.val == 1 && μ.val == 1 then Real.sqrt (kerrSigma a r θ / kerrDelta M a r)
    else if b.val == 2 && μ.val == 2 then Real.sqrt (kerrSigma a r θ)
    else if b.val == 3 && μ.val == 0 then -a * Real.sin θ / Real.sqrt (kerrSigma a r θ)
    else if b.val == 3 && μ.val == 3 then
      Real.sin θ * (r ^ 2 + a ^ 2) / Real.sqrt (kerrSigma a r θ)
    else 0

theorem kerr_e00 (M a r θ : ℝ) :
    kerrCoframe M a r θ 0 0 = Real.sqrt (kerrDelta M a r / kerrSigma a r θ) := rfl

theorem kerr_e03 (M a r θ : ℝ) :
    kerrCoframe M a r θ 0 3 =
      -a * Real.sin θ ^ 2 * Real.sqrt (kerrDelta M a r / kerrSigma a r θ) := rfl

theorem kerr_e11 (M a r θ : ℝ) :
    kerrCoframe M a r θ 1 1 = Real.sqrt (kerrSigma a r θ / kerrDelta M a r) := rfl

theorem kerr_e22 (M a r θ : ℝ) :
    kerrCoframe M a r θ 2 2 = Real.sqrt (kerrSigma a r θ) := rfl

theorem kerr_e30 (M a r θ : ℝ) :
    kerrCoframe M a r θ 3 0 = -a * Real.sin θ / Real.sqrt (kerrSigma a r θ) := rfl

theorem kerr_e33 (M a r θ : ℝ) :
    kerrCoframe M a r θ 3 3 =
      Real.sin θ * (r ^ 2 + a ^ 2) / Real.sqrt (kerrSigma a r θ) := rfl

theorem kerr_e10 (M a r θ : ℝ) : kerrCoframe M a r θ 1 0 = 0 := rfl

theorem kerr_e20 (M a r θ : ℝ) : kerrCoframe M a r θ 2 0 = 0 := rfl

theorem kerr_e01 (M a r θ : ℝ) : kerrCoframe M a r θ 0 1 = 0 := rfl

theorem kerr_e21 (M a r θ : ℝ) : kerrCoframe M a r θ 2 1 = 0 := rfl

theorem kerr_e31 (M a r θ : ℝ) : kerrCoframe M a r θ 3 1 = 0 := rfl

theorem kerr_e02 (M a r θ : ℝ) : kerrCoframe M a r θ 0 2 = 0 := rfl

theorem kerr_e12 (M a r θ : ℝ) : kerrCoframe M a r θ 1 2 = 0 := rfl

theorem kerr_e32 (M a r θ : ℝ) : kerrCoframe M a r θ 3 2 = 0 := rfl

theorem kerr_e13 (M a r θ : ℝ) : kerrCoframe M a r θ 1 3 = 0 := rfl

theorem kerr_e23 (M a r θ : ℝ) : kerrCoframe M a r θ 2 3 = 0 := rfl

private theorem sqrt_inv_of_pos {x : ℝ} (_hx : 0 < x) :
    Real.sqrt (x⁻¹) = (Real.sqrt x)⁻¹ := by
  rw [inv_eq_one_div, Real.sqrt_div (x := 1) zero_le_one x, Real.sqrt_one, one_div]

theorem induced_kerr_tt {M a r θ : ℝ} (hSig : 0 < kerrSigma a r θ)
    (hΔ : 0 ≤ kerrDelta M a r) :
    inducedMetric (kerrCoframe M a r θ) 0 0 =
      -(1 - 2 * M * r / kerrSigma a r θ) := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp only [kerr_e00, kerr_e10, kerr_e20, kerr_e30, w31]
  have hsqΔ : (Real.sqrt (kerrDelta M a r / kerrSigma a r θ)) ^ 2 =
      kerrDelta M a r / kerrSigma a r θ :=
    Real.sq_sqrt (div_nonneg hΔ hSig.le)
  have hsqSig : (Real.sqrt (kerrSigma a r θ)) ^ 2 = kerrSigma a r θ :=
    Real.sq_sqrt hSig.le
  have hc := cos_sq_eq_one_sub_sin_sq θ
  field_simp [hSig.ne', (Real.sqrt_pos.mpr hSig).ne']
  rw [hsqΔ, hsqSig]
  unfold kerrDelta kerrSigma at *
  field_simp [hSig.ne']
  nlinarith [hc]

theorem induced_kerr_rr {M a r θ : ℝ} (hSig : 0 < kerrSigma a r θ)
    (hΔ : 0 < kerrDelta M a r) :
    inducedMetric (kerrCoframe M a r θ) 1 1 =
      kerrSigma a r θ / kerrDelta M a r := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp only [kerr_e01, kerr_e11, kerr_e21, kerr_e31, w31]
  ring_nf
  exact Real.sq_sqrt (div_nonneg hSig.le hΔ.le)

theorem induced_kerr_θθ {M a r θ : ℝ} (hSig : 0 < kerrSigma a r θ) :
    inducedMetric (kerrCoframe M a r θ) 2 2 = kerrSigma a r θ := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp only [kerr_e02, kerr_e12, kerr_e22, kerr_e32, w31]
  ring_nf
  exact Real.sq_sqrt hSig.le

theorem induced_kerr_tφ {M a r θ : ℝ} (hSig : 0 < kerrSigma a r θ)
    (hΔ : 0 ≤ kerrDelta M a r) :
    inducedMetric (kerrCoframe M a r θ) 0 3 = kerrGtφ M a r θ := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp only [kerr_e00, kerr_e03, kerr_e10, kerr_e13, kerr_e20, kerr_e23, kerr_e30, kerr_e33,
    w31, kerrGtφ]
  have hsqΔ : (Real.sqrt (kerrDelta M a r / kerrSigma a r θ)) ^ 2 =
      kerrDelta M a r / kerrSigma a r θ :=
    Real.sq_sqrt (div_nonneg hΔ hSig.le)
  have hsqSig : (Real.sqrt (kerrSigma a r θ)) ^ 2 = kerrSigma a r θ :=
    Real.sq_sqrt hSig.le
  field_simp [hSig.ne', (Real.sqrt_pos.mpr hSig).ne']
  rw [hsqΔ, hsqSig]
  unfold kerrDelta
  field_simp [hSig.ne']
  ring

theorem induced_kerr_φt {M a r θ : ℝ} (hSig : 0 < kerrSigma a r θ)
    (hΔ : 0 ≤ kerrDelta M a r) :
    inducedMetric (kerrCoframe M a r θ) 3 0 = kerrGtφ M a r θ := by
  rw [← induced_kerr_tφ hSig hΔ]
  rw [inducedMetric_eq_weighted, inducedMetric_eq_weighted, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [kerr_e00, kerr_e03, kerr_e10, kerr_e13, kerr_e20, kerr_e23, kerr_e30, kerr_e33, w31]
  ring

theorem induced_kerr_φφ {M a r θ : ℝ} (hSig : 0 < kerrSigma a r θ)
    (hΔ : 0 ≤ kerrDelta M a r) :
    inducedMetric (kerrCoframe M a r θ) 3 3 = kerrGφφ M a r θ := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp only [kerr_e03, kerr_e13, kerr_e23, kerr_e33, w31, kerrGφφ]
  have hsqΔ : (Real.sqrt (kerrDelta M a r / kerrSigma a r θ)) ^ 2 =
      kerrDelta M a r / kerrSigma a r θ :=
    Real.sq_sqrt (div_nonneg hΔ hSig.le)
  have hsqSig : (Real.sqrt (kerrSigma a r θ)) ^ 2 = kerrSigma a r θ :=
    Real.sq_sqrt hSig.le
  have halg := kerr_azimuth_algebra M a r θ
  field_simp [hSig.ne', (Real.sqrt_pos.mpr hSig).ne']
  rw [hsqΔ, hsqSig]
  field_simp [hSig.ne']
  nlinarith [halg]

private theorem induced_kerr_vanish {M a r θ : ℝ} {μ ν : Fin 4}
    (h0 : w31 0 * kerrCoframe M a r θ 0 μ * kerrCoframe M a r θ 0 ν = 0)
    (h1 : w31 1 * kerrCoframe M a r θ 1 μ * kerrCoframe M a r θ 1 ν = 0)
    (h2 : w31 2 * kerrCoframe M a r θ 2 μ * kerrCoframe M a r θ 2 ν = 0)
    (h3 : w31 3 * kerrCoframe M a r θ 3 μ * kerrCoframe M a r θ 3 ν = 0) :
    inducedMetric (kerrCoframe M a r θ) μ ν = 0 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four, h0, h1, h2, h3]
  ring

theorem induced_kerr_01 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 0 1 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e00, kerr_e01]) (by simp [w31, kerr_e10, kerr_e11])
    (by simp [w31, kerr_e20, kerr_e21]) (by simp [w31, kerr_e30, kerr_e31])

theorem induced_kerr_02 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 0 2 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e00, kerr_e02]) (by simp [w31, kerr_e10, kerr_e12])
    (by simp [w31, kerr_e20, kerr_e22]) (by simp [w31, kerr_e30, kerr_e32])

theorem induced_kerr_10 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 1 0 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e00, kerr_e01]) (by simp [w31, kerr_e10, kerr_e11])
    (by simp [w31, kerr_e20, kerr_e21]) (by simp [w31, kerr_e30, kerr_e31])

theorem induced_kerr_12 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 1 2 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e01, kerr_e02]) (by simp [w31, kerr_e11, kerr_e12])
    (by simp [w31, kerr_e21, kerr_e22]) (by simp [w31, kerr_e31, kerr_e32])

theorem induced_kerr_13 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 1 3 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e01, kerr_e03]) (by simp [w31, kerr_e11, kerr_e13])
    (by simp [w31, kerr_e21, kerr_e23]) (by simp [w31, kerr_e31, kerr_e33])

theorem induced_kerr_20 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 2 0 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e02, kerr_e00]) (by simp [w31, kerr_e12, kerr_e10])
    (by simp [w31, kerr_e22, kerr_e20]) (by simp [w31, kerr_e32, kerr_e30])

theorem induced_kerr_21 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 2 1 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e02, kerr_e01]) (by simp [w31, kerr_e12, kerr_e11])
    (by simp [w31, kerr_e22, kerr_e21]) (by simp [w31, kerr_e32, kerr_e31])

theorem induced_kerr_23 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 2 3 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e02, kerr_e03]) (by simp [w31, kerr_e12, kerr_e13])
    (by simp [w31, kerr_e22, kerr_e23]) (by simp [w31, kerr_e32, kerr_e33])

theorem induced_kerr_31 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 3 1 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e03, kerr_e01]) (by simp [w31, kerr_e13, kerr_e11])
    (by simp [w31, kerr_e23, kerr_e21]) (by simp [w31, kerr_e33, kerr_e31])

theorem induced_kerr_32 (M a r θ : ℝ) : inducedMetric (kerrCoframe M a r θ) 3 2 = 0 :=
  induced_kerr_vanish (by simp [w31, kerr_e03, kerr_e02]) (by simp [w31, kerr_e13, kerr_e12])
    (by simp [w31, kerr_e23, kerr_e22]) (by simp [w31, kerr_e33, kerr_e32])

/-- The coframe induces the Kerr metric on `Σ > 0` and `Δ > 0`. -/
theorem inducedMetric_kerr {M a r θ : ℝ} (hSig : 0 < kerrSigma a r θ)
    (hΔ : 0 < kerrDelta M a r) (μ ν : Fin 4) :
    inducedMetric (kerrCoframe M a r θ) μ ν = kerrMetric M a r θ μ ν := by
  fin_cases μ <;> fin_cases ν
  · exact induced_kerr_tt hSig hΔ.le
  · simpa [kerrMetric] using induced_kerr_01 M a r θ
  · simpa [kerrMetric] using induced_kerr_02 M a r θ
  · exact induced_kerr_tφ hSig hΔ.le
  · simpa [kerrMetric] using induced_kerr_10 M a r θ
  · exact induced_kerr_rr hSig hΔ
  · simpa [kerrMetric] using induced_kerr_12 M a r θ
  · simpa [kerrMetric] using induced_kerr_13 M a r θ
  · simpa [kerrMetric] using induced_kerr_20 M a r θ
  · simpa [kerrMetric] using induced_kerr_21 M a r θ
  · exact induced_kerr_θθ hSig
  · simpa [kerrMetric] using induced_kerr_23 M a r θ
  · exact induced_kerr_φt hSig hΔ.le
  · simpa [kerrMetric] using induced_kerr_31 M a r θ
  · simpa [kerrMetric] using induced_kerr_32 M a r θ
  · exact induced_kerr_φφ hSig hΔ.le

/-! ### Spinless reduction -/

theorem kerrCoframe_zero_spin {M r θ : ℝ} (h : IsExterior (2 * M) r) :
    kerrCoframe M 0 r θ = schwarzschildCoframe (2 * M) r θ := by
  have hr : 0 < r := lt_trans h.1 h.2
  have hA : 0 < schwarzschildA (2 * M) r := schwarzschildA_pos h
  have hSig : kerrSigma 0 r θ = r ^ 2 := by simp [kerrSigma]
  have hΔ : kerrDelta M 0 r = r ^ 2 * schwarzschildA (2 * M) r := by
    unfold kerrDelta schwarzschildA
    field_simp [hr.ne']
    ring
  have hdiv : kerrDelta M 0 r / kerrSigma 0 r θ = schwarzschildA (2 * M) r := by
    rw [hSig, hΔ]
    field_simp [hr.ne']
  have hrad : kerrSigma 0 r θ / kerrDelta M 0 r = (schwarzschildA (2 * M) r)⁻¹ := by
    rw [hSig, hΔ]
    field_simp [hr.ne', hA.ne']
  have h00 : kerrCoframe M 0 r θ 0 0 = schwarzschildCoframe (2 * M) r θ 0 0 := by
    rw [kerr_e00, hdiv, schwarzschildCoframe, diagonalCoframe]
    simp [schwarzschildDiag]
  have h01 : kerrCoframe M 0 r θ 0 1 = schwarzschildCoframe (2 * M) r θ 0 1 := by
    rw [kerr_e01, schwarzschildCoframe, diagonalCoframe]
    simp
  have h02 : kerrCoframe M 0 r θ 0 2 = schwarzschildCoframe (2 * M) r θ 0 2 := by
    rw [kerr_e02, schwarzschildCoframe, diagonalCoframe]
    simp
  have h03 : kerrCoframe M 0 r θ 0 3 = schwarzschildCoframe (2 * M) r θ 0 3 := by
    rw [kerr_e03, schwarzschildCoframe, diagonalCoframe]
    simp
  have h10 : kerrCoframe M 0 r θ 1 0 = schwarzschildCoframe (2 * M) r θ 1 0 := by
    rw [kerr_e10, schwarzschildCoframe, diagonalCoframe]
    simp
  have h11 : kerrCoframe M 0 r θ 1 1 = schwarzschildCoframe (2 * M) r θ 1 1 := by
    rw [kerr_e11, hrad, sqrt_inv_of_pos hA, schwarzschildCoframe, diagonalCoframe]
    simp [schwarzschildDiag]
  have h12 : kerrCoframe M 0 r θ 1 2 = schwarzschildCoframe (2 * M) r θ 1 2 := by
    rw [kerr_e12, schwarzschildCoframe, diagonalCoframe]
    simp
  have h13 : kerrCoframe M 0 r θ 1 3 = schwarzschildCoframe (2 * M) r θ 1 3 := by
    rw [kerr_e13, schwarzschildCoframe, diagonalCoframe]
    simp
  have h20 : kerrCoframe M 0 r θ 2 0 = schwarzschildCoframe (2 * M) r θ 2 0 := by
    rw [kerr_e20, schwarzschildCoframe, diagonalCoframe]
    simp
  have h21 : kerrCoframe M 0 r θ 2 1 = schwarzschildCoframe (2 * M) r θ 2 1 := by
    rw [kerr_e21, schwarzschildCoframe, diagonalCoframe]
    simp
  have h22 : kerrCoframe M 0 r θ 2 2 = schwarzschildCoframe (2 * M) r θ 2 2 := by
    rw [kerr_e22, hSig, Real.sqrt_sq hr.le, schwarzschildCoframe, diagonalCoframe]
    simp [schwarzschildDiag]
  have h23 : kerrCoframe M 0 r θ 2 3 = schwarzschildCoframe (2 * M) r θ 2 3 := by
    rw [kerr_e23, schwarzschildCoframe, diagonalCoframe]
    simp
  have h30 : kerrCoframe M 0 r θ 3 0 = schwarzschildCoframe (2 * M) r θ 3 0 := by
    rw [kerr_e30, schwarzschildCoframe, diagonalCoframe]
    simp
  have h31 : kerrCoframe M 0 r θ 3 1 = schwarzschildCoframe (2 * M) r θ 3 1 := by
    rw [kerr_e31, schwarzschildCoframe, diagonalCoframe]
    simp
  have h32 : kerrCoframe M 0 r θ 3 2 = schwarzschildCoframe (2 * M) r θ 3 2 := by
    rw [kerr_e32, schwarzschildCoframe, diagonalCoframe]
    simp
  have h33 : kerrCoframe M 0 r θ 3 3 = schwarzschildCoframe (2 * M) r θ 3 3 := by
    rw [kerr_e33, hSig, Real.sqrt_sq hr.le, schwarzschildCoframe, diagonalCoframe]
    simp [schwarzschildDiag]
    field_simp [hr.ne']
  funext b μ
  fin_cases b <;> fin_cases μ
  · exact h00
  · exact h01
  · exact h02
  · exact h03
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h30
  · exact h31
  · exact h32
  · exact h33

/-! ### A pure boost does not write the cross term -/

/-- Diagonal frame boosted by rapidity `ψ` in the `(t,φ)` plane.
`β` is the azimuthal scale of the reference leg. `φ` is index `3`. -/
noncomputable def kerrAzimuthBoostCoframe (ψ β : ℝ) : Coframe :=
  fun b μ =>
    if b = 0 ∧ μ = 0 then Real.cosh ψ
    else if b = 0 ∧ μ = 3 then Real.sinh ψ * β
    else if b = 3 ∧ μ = 0 then Real.sinh ψ
    else if b = 3 ∧ μ = 3 then Real.cosh ψ * β
    else if b = 1 ∧ μ = 1 then 1
    else if b = 2 ∧ μ = 2 then 1
    else 0

theorem induced_kerrAzimuthBoost_tt (ψ β : ℝ) :
    inducedMetric (kerrAzimuthBoostCoframe ψ β) 0 0 = -1 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [kerrAzimuthBoostCoframe, w31]
  have h := Real.cosh_sq_sub_sinh_sq ψ
  ring_nf at h ⊢
  linarith

theorem induced_kerrAzimuthBoost_tφ (ψ β : ℝ) :
    inducedMetric (kerrAzimuthBoostCoframe ψ β) 0 3 = 0 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [kerrAzimuthBoostCoframe, w31]
  ring

theorem induced_kerrAzimuthBoost_φφ (ψ β : ℝ) :
    inducedMetric (kerrAzimuthBoostCoframe ψ β) 3 3 = β ^ 2 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [kerrAzimuthBoostCoframe, w31]
  have h := Real.cosh_sq_sub_sinh_sq ψ
  linear_combination β ^ 2 * h

theorem kerrAzimuthBoost_azimuth_pos {ψ β : ℝ} (hβ : β ≠ 0) :
    0 < inducedMetric (kerrAzimuthBoostCoframe ψ β) 3 3 := by
  rw [induced_kerrAzimuthBoost_φφ]
  exact sq_pos_of_ne_zero hβ

theorem kerr_cross_ne_azimuthBoost {M a r θ ψ β : ℝ} (hSig : 0 < kerrSigma a r θ)
    (hΔ : 0 < kerrDelta M a r) (h : M * a * r * Real.sin θ ≠ 0) :
    inducedMetric (kerrCoframe M a r θ) 0 3 ≠
      inducedMetric (kerrAzimuthBoostCoframe ψ β) 0 3 := by
  rw [induced_kerr_tφ hSig hΔ.le, induced_kerrAzimuthBoost_tφ]
  unfold kerrGtφ
  have hs : Real.sin θ ≠ 0 := by
    intro hs0
    apply h
    simp [hs0]
  have hnum : -2 * M * a * r * Real.sin θ ^ 2 ≠ 0 := by
    have h2 : (-2 : ℝ) ≠ 0 := by norm_num
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 ?_) ?_) ?_) ?_
    · intro hM
      apply h
      simp [hM]
    · intro ha
      apply h
      simp [ha]
    · intro hr
      apply h
      simp [hr]
    · exact pow_ne_zero 2 hs
  exact div_ne_zero hnum hSig.ne'

end Gravity

end DstDiophantine
