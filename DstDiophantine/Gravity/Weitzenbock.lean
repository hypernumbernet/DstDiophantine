import DstDiophantine.Gravity.Schwarzschild
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Chart Weitzenböck torsion

On a fixed chart, `T^a_μν = ∂_μ e^a_ν - ∂_ν e^a_μ`. For the exterior Schwarzschild
diagonal tetrad we record principal torsion components and prove

* closed form `T = (2/r²)(1-√A)²/√A`;
* divergence form `T = -r⁻² · formal∂_r(r² B^r)` with `B^r = 4(1-√A)/r`;
* field seed `J_field = ½ (φ')²` (see `Gravity.Identification` for the
  parameter-vs-field dictionary).
-/

namespace DstDiophantine

namespace Gravity

open Real

/-- Partial derivatives of coframe components: `partials μ a ν = ∂_μ e^a_ν`. -/
abbrev CoframePartials := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- Weitzenböck torsion `T^a_μν = ∂_μ e^a_ν - ∂_ν e^a_μ`. -/
def weitzenbockTorsion (partials : CoframePartials) (a μ ν : Fin 4) : ℝ :=
  partials μ a ν - partials ν a μ

theorem weitzenbockTorsion_antisym (partials : CoframePartials) (a μ ν : Fin 4) :
    weitzenbockTorsion partials a ν μ = -weitzenbockTorsion partials a μ ν := by
  simp [weitzenbockTorsion]

/-- `∂_r √A = (rₛ/(2 r²)) / √A`. -/
noncomputable def dSqrtA_dr (rs r : ℝ) : ℝ :=
  (rs / (2 * r ^ 2)) / Real.sqrt (schwarzschildA rs r)

/-- Radial derivative of the Schwarzschild factor: `A' = rₛ / r²`. -/
noncomputable def dA_dr (rs r : ℝ) : ℝ :=
  rs / r ^ 2

/-- Radial rapidity derivative `φ' = -½ A'/A`. -/
noncomputable def dRapidity_dr (rs r : ℝ) : ℝ :=
  -(1 / 2) * dA_dr rs r / schwarzschildA rs r

theorem dRapidity_dr_eq (rs r : ℝ) :
    dRapidity_dr rs r = -(rs / (2 * r ^ 2 * schwarzschildA rs r)) := by
  simp only [dRapidity_dr, dA_dr]
  ring

/-- Field seed on the radial-boost slice: `J_field = ½ (φ')²`. -/
noncomputable def J_field (rs r : ℝ) : ℝ :=
  (1 / 2) * (dRapidity_dr rs r) ^ 2

/-- Explicit nonzero Schwarzschild coframe partials (all others zero). -/
noncomputable def schwarzschildPartials (rs r θ : ℝ) : CoframePartials :=
  fun μ a ν =>
    if μ = 1 ∧ a = 0 ∧ ν = 0 then dSqrtA_dr rs r
    else if μ = 1 ∧ a = 1 ∧ ν = 1 then
      -(rs / (2 * r ^ 2)) /
        (schwarzschildA rs r * Real.sqrt (schwarzschildA rs r))
    else if μ = 1 ∧ a = 2 ∧ ν = 2 then 1
    else if μ = 1 ∧ a = 3 ∧ ν = 3 then Real.sin θ
    else if μ = 2 ∧ a = 3 ∧ ν = 3 then r * Real.cos θ
    else 0

theorem schwarzschild_torsion_T0_r_t (rs r θ : ℝ) :
    weitzenbockTorsion (schwarzschildPartials rs r θ) 0 1 0 = dSqrtA_dr rs r := by
  simp [weitzenbockTorsion, schwarzschildPartials]

theorem schwarzschild_torsion_T2_r_theta (rs r θ : ℝ) :
    weitzenbockTorsion (schwarzschildPartials rs r θ) 2 1 2 = 1 := by
  simp [weitzenbockTorsion, schwarzschildPartials]

theorem schwarzschild_torsion_T3_r_phi (rs r θ : ℝ) :
    weitzenbockTorsion (schwarzschildPartials rs r θ) 3 1 3 = Real.sin θ := by
  simp [weitzenbockTorsion, schwarzschildPartials]

theorem schwarzschild_torsion_T3_theta_phi (rs r θ : ℝ) :
    weitzenbockTorsion (schwarzschildPartials rs r θ) 3 2 3 = r * Real.cos θ := by
  simp [weitzenbockTorsion, schwarzschildPartials]

/-- Boost-leg identity: `∂_r √A = - φ' · √A` (since `φ' < 0` on the exterior). -/
theorem dSqrtA_dr_eq_neg_dRapidity_mul_sqrtA {rs r : ℝ} (h : IsExterior rs r) :
    dSqrtA_dr rs r = -(dRapidity_dr rs r) * Real.sqrt (schwarzschildA rs r) := by
  have hA := schwarzschildA_pos h
  have hs : Real.sqrt (schwarzschildA rs r) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  have hr0 : r ≠ 0 := (lt_trans h.1 h.2).ne'
  have hA0 : schwarzschildA rs r ≠ 0 := hA.ne'
  have hs2 : (Real.sqrt (schwarzschildA rs r)) ^ 2 = schwarzschildA rs r :=
    Real.sq_sqrt hA.le
  simp only [dSqrtA_dr, dRapidity_dr_eq, neg_neg]
  field_simp [hr0, hs, hA0]
  rw [hs2]

/-- TEGR chart scalar for exterior Schwarzschild: `(2/r²)(1-√A)²/√A`.

Closed-form evaluation of
`T = ¼ T_{ρμν}T^{ρμν} + ½ T_{ρμν}T^{νμρ} − T_ρ T^ρ` on the exterior diagonal
tetrad (TEGR chart calculus). -/
noncomputable def schwarzschildTeleparallelT (rs r : ℝ) : ℝ :=
  let A := schwarzschildA rs r
  (2 / r ^ 2) * (1 - Real.sqrt A) ^ 2 / Real.sqrt A

/-- Closed radial divergence density: `T = r⁻² · DivClosed`. -/
noncomputable def schwarzschildDivClosed (rs r : ℝ) : ℝ :=
  2 * (1 - Real.sqrt (schwarzschildA rs r)) ^ 2 / Real.sqrt (schwarzschildA rs r)

/-- Radial current with `T = - r⁻² ∂_r (r² B^r)` for `B^r = 4(1-√A)/r`. -/
noncomputable def schwarzschildDivCurrent (rs r : ℝ) : ℝ :=
  (4 / r) * (1 - Real.sqrt (schwarzschildA rs r))

/-- `r² B^r = 4 r (1-√A)`. -/
noncomputable def r2B (rs r : ℝ) : ℝ :=
  r ^ 2 * schwarzschildDivCurrent rs r

theorem r2B_eq (rs r : ℝ) :
    r2B rs r = 4 * r * (1 - Real.sqrt (schwarzschildA rs r)) := by
  simp only [r2B, schwarzschildDivCurrent]
  by_cases hr0 : r = 0
  · simp [hr0]
  · field_simp [hr0]

/-- Formal radial derivative of `r² B^r` via `A'` and `(√A)'`. -/
noncomputable def formal_d_r2B_dr (rs r : ℝ) : ℝ :=
  4 * (1 - Real.sqrt (schwarzschildA rs r)) - 4 * r * dSqrtA_dr rs r

theorem formal_d_r2B_dr_eq {rs r : ℝ} (h : IsExterior rs r) :
    formal_d_r2B_dr rs r =
      4 * (1 - Real.sqrt (schwarzschildA rs r)) -
        2 * (rs / r) / Real.sqrt (schwarzschildA rs r) := by
  have hA := schwarzschildA_pos h
  have hs : Real.sqrt (schwarzschildA rs r) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  have hr0 : r ≠ 0 := (lt_trans h.1 h.2).ne'
  simp only [formal_d_r2B_dr, dSqrtA_dr, schwarzschildA]
  field_simp [hr0, hs]
  ring

theorem schwarzschild_T_eq_divClosed {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      (1 / r ^ 2) * schwarzschildDivClosed rs r := by
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hA := schwarzschildA_pos h
  have hs : Real.sqrt (schwarzschildA rs r) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  simp only [schwarzschildTeleparallelT, schwarzschildDivClosed]
  field_simp [hrpos.ne', hs]

/-- Expanded form: `∂_r [4 r (1-√A)] = - DivClosed`. -/
theorem schwarzschildDivClosed_eq_neg_expanded {rs r : ℝ} (h : IsExterior rs r) :
    -schwarzschildDivClosed rs r =
      4 * (1 - Real.sqrt (schwarzschildA rs r)) -
        2 * (rs / r) / Real.sqrt (schwarzschildA rs r) := by
  have hA := schwarzschildA_pos h
  have hs : Real.sqrt (schwarzschildA rs r) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  have hr0 : r ≠ 0 := (lt_trans h.1 h.2).ne'
  have hrs : rs / r = 1 - schwarzschildA rs r := by
    simp only [schwarzschildA]
    field_simp [hr0]
    ring
  simp only [schwarzschildDivClosed, hrs]
  set s := Real.sqrt (schwarzschildA rs r) with hs_def
  have hs2 : s ^ 2 = schwarzschildA rs r := by
    simp [hs_def, Real.sq_sqrt hA.le]
  have hs0 : s ≠ 0 := by simpa [hs_def] using hs
  field_simp [hs0]
  nlinarith [sq_nonneg (s - 1), hs2]

theorem formal_d_r2B_dr_eq_neg_DivClosed {rs r : ℝ} (h : IsExterior rs r) :
    formal_d_r2B_dr rs r = -schwarzschildDivClosed rs r := by
  rw [formal_d_r2B_dr_eq h, ← schwarzschildDivClosed_eq_neg_expanded h]

/-- `T = - r⁻² · formal∂_r(r² B^r)` on the exterior chart. -/
theorem schwarzschild_T_eq_neg_r_inv_sq_formal_d_r2B {rs r : ℝ}
    (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      -(1 / r ^ 2) * formal_d_r2B_dr rs r := by
  rw [schwarzschild_T_eq_divClosed h, formal_d_r2B_dr_eq_neg_DivClosed h]
  ring

/-- Explicit form `J_field = rₛ² / (8 r⁴ A²)`. -/
theorem J_field_coef {rs r : ℝ} (h : IsExterior rs r) :
    J_field rs r =
      rs ^ 2 / (8 * r ^ 4 * (schwarzschildA rs r) ^ 2) := by
  have hA := schwarzschildA_pos h
  have hr0 : r ≠ 0 := (lt_trans h.1 h.2).ne'
  have hA0 : schwarzschildA rs r ≠ 0 := hA.ne'
  simp only [J_field, dRapidity_dr_eq]
  field_simp [hr0, hA0]
  ring

/-- Minkowski limit: `rₛ = 0` forces `T = 0` and `J_field = 0` (at `r > 0`). -/
theorem minkowski_T_and_J_field_zero {r : ℝ} (_hr : 0 < r) :
    schwarzschildTeleparallelT 0 r = 0 ∧ J_field 0 r = 0 := by
  have hA : schwarzschildA 0 r = 1 := by
    simp [schwarzschildA]
  refine ⟨?_, ?_⟩
  · simp [schwarzschildTeleparallelT, hA]
  · simp [J_field, dRapidity_dr, dA_dr, schwarzschildA]

end Gravity

end DstDiophantine
