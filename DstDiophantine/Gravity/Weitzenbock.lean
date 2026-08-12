import DstDiophantine.Gravity.Schwarzschild
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Chart Weitzenböck torsion

On a fixed chart, `T^a_μν = ∂_μ e^a_ν - ∂_ν e^a_μ`. For the exterior Schwarzschild
diagonal tetrad we record principal torsion components and prove the chart identity
`T = r⁻² · DivClosed` with the TEGR-normalised scalar
`T = (2/r²)(1-√A)²/√A`.

The closed density `DivClosed` is the radial divergence form of `T` (up to the
conventional sign of the radial current `B^r`).
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

/-- TEGR chart scalar for exterior Schwarzschild: `(2/r²)(1-√A)²/√A`. -/
noncomputable def schwarzschildTeleparallelT (rs r : ℝ) : ℝ :=
  let A := schwarzschildA rs r
  (2 / r ^ 2) * (1 - Real.sqrt A) ^ 2 / Real.sqrt A

/-- Closed radial divergence density associated to `T`. -/
noncomputable def schwarzschildDivClosed (rs r : ℝ) : ℝ :=
  2 * (1 - Real.sqrt (schwarzschildA rs r)) ^ 2 / Real.sqrt (schwarzschildA rs r)

/-- Radial current with `T = - r⁻² ∂_r (r² B^r)` for `B^r = 4(1-√A)/r`
(sign convention of the outgoing current). -/
noncomputable def schwarzschildDivCurrent (rs r : ℝ) : ℝ :=
  (4 / r) * (1 - Real.sqrt (schwarzschildA rs r))

theorem schwarzschild_T_eq_divClosed {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      (1 / r ^ 2) * schwarzschildDivClosed rs r := by
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hA := schwarzschildA_pos h
  have hs : Real.sqrt (schwarzschildA rs r) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  simp only [schwarzschildTeleparallelT, schwarzschildDivClosed]
  field_simp [hrpos.ne', hs]

/-- Expanded form matching `∂_r [4 r (1-√A)] = - DivClosed`. -/
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
  -- Goal becomes -2(1-s)²/s = 4(1-s) - 2(1-A)/s
  simp only [schwarzschildDivClosed, hrs]
  set s := Real.sqrt (schwarzschildA rs r) with hs_def
  have hs2 : s ^ 2 = schwarzschildA rs r := by
    simp [hs_def, Real.sq_sqrt hA.le]
  have hs0 : s ≠ 0 := by simpa [hs_def] using hs
  -- Clear denominators: multiply both sides by s
  field_simp [hs0]
  -- -2(1-s)² = 4(1-s)s - 2(1-s²)
  nlinarith [sq_nonneg (s - 1), hs2]

end Gravity

end DstDiophantine
