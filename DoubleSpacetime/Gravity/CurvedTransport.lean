import DoubleSpacetime.Gravity.KillingTransport

/-!
# The static Killing bivector in the exterior Levi-Civita connection

On the exterior frame the static boost is parallel along the observer, and an
angular leg tilts it at the rate \(\kappa\sqrt{A}/r\). This bivector is not
identified with the torsional mismatch, and the teleparallel scalar is not
claimed to be a total divergence.
-/

namespace DoubleSpacetime.Gravity.CurvedTransport

open KillingAxis KillingTransport Amplification

/-- Sign of the orthonormal frame, `diag(-1,+1,+1,+1)`. -/
def frameSign : Fin 4 → ℝ
  | 0 => -1
  | _ => 1

/-- Radial boost in the orthonormal frame: `e₀ ↦ e₁`, `e₁ ↦ e₀`. -/
def radialBoost : Fin 4 → Fin 4 → ℝ
  | 0, 1 => 1
  | 1, 0 => 1
  | _, _ => 0

/-- Static boost of rate `κ`, as a frame endomorphism. -/
def staticBoost (κ : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun a b => κ * radialBoost a b

/-- Levi-Civita coefficient `ω^a_b(e_c)` of the exterior orthonormal frame. `a` is the value slot,
`b` the argument slot, `c` the direction. -/
noncomputable def exteriorConn (rs r θ : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ
  | 0, 1, 0 => dSqrtA_dr rs r
  | 1, 0, 0 => dSqrtA_dr rs r
  | 2, 1, 2 => killingNorm rs r / r
  | 1, 2, 2 => -(killingNorm rs r / r)
  | 3, 1, 3 => killingNorm rs r / r
  | 1, 3, 3 => -(killingNorm rs r / r)
  | 3, 2, 3 => (Real.cos θ / Real.sin θ) / r
  | 2, 3, 3 => -((Real.cos θ / Real.sin θ) / r)
  | _, _, _ => 0

/-- Connection term `(∇_{e_c} Λ)^a_b` of a frame-constant endomorphism. -/
def connOnBivector (ω : Fin 4 → Fin 4 → Fin 4 → ℝ) (Λ : Fin 4 → Fin 4 → ℝ)
    (c a b : Fin 4) : ℝ :=
  ω a 0 c * Λ 0 b - Λ a 0 * ω 0 b c +
    (ω a 1 c * Λ 1 b - Λ a 1 * ω 1 b c) +
    (ω a 2 c * Λ 2 b - Λ a 2 * ω 2 b c) +
    (ω a 3 c * Λ 3 b - Λ a 3 * ω 3 b c)

/-- Covariant derivative of `ξ = ν e₀` along `e_c`. The radial leg differentiates the coefficient;
every other leg contributes only the connection. -/
noncomputable def killingCov (rs r θ : ℝ) (c a : Fin 4) : ℝ :=
  (if c = 1 ∧ a = 0 then killingRate rs r else 0) +
    exteriorConn rs r θ a 0 c * killingNorm rs r

theorem exteriorConn_radial (rs r θ : ℝ) (a b : Fin 4) :
    exteriorConn rs r θ a b 1 = 0 := by
  fin_cases a <;> fin_cases b <;> rfl

theorem exteriorConn_lowered_antisym (rs r θ : ℝ) (a b c : Fin 4) :
    frameSign a * exteriorConn rs r θ a b c +
        frameSign b * exteriorConn rs r θ b a c = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [frameSign, exteriorConn]

/-! ### The Killing vector -/

theorem killingCov_time_0 (rs r θ : ℝ) : killingCov rs r θ 0 0 = 0 := by
  have hω : exteriorConn rs r θ 0 0 0 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_time_1 {rs r : ℝ} (h : IsExterior rs r) (θ : ℝ) :
    killingCov rs r θ 0 1 = killingRate rs r := by
  have hω : exteriorConn rs r θ 1 0 0 = dSqrtA_dr rs r := rfl
  unfold killingCov
  rw [hω, ite_eq_right (by decide : ¬((0 : Fin 4) = 1 ∧ (1 : Fin 4) = 0)), zero_add,
    mul_comm]
  exact (killingRate_eq_norm_mul_deriv h).symm

theorem killingCov_time_2 (rs r θ : ℝ) : killingCov rs r θ 0 2 = 0 := by
  have hω : exteriorConn rs r θ 2 0 0 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_time_3 (rs r θ : ℝ) : killingCov rs r θ 0 3 = 0 := by
  have hω : exteriorConn rs r θ 3 0 0 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_radial_0 (rs r θ : ℝ) : killingCov rs r θ 1 0 = killingRate rs r := by
  have hω : exteriorConn rs r θ 0 0 1 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_radial_1 (rs r θ : ℝ) : killingCov rs r θ 1 1 = 0 := by
  have hω : exteriorConn rs r θ 1 0 1 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_radial_2 (rs r θ : ℝ) : killingCov rs r θ 1 2 = 0 := by
  have hω : exteriorConn rs r θ 2 0 1 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_radial_3 (rs r θ : ℝ) : killingCov rs r θ 1 3 = 0 := by
  have hω : exteriorConn rs r θ 3 0 1 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_polar_0 (rs r θ : ℝ) : killingCov rs r θ 2 0 = 0 := by
  have hω : exteriorConn rs r θ 0 0 2 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_polar_1 (rs r θ : ℝ) : killingCov rs r θ 2 1 = 0 := by
  have hω : exteriorConn rs r θ 1 0 2 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_polar_2 (rs r θ : ℝ) : killingCov rs r θ 2 2 = 0 := by
  have hω : exteriorConn rs r θ 2 0 2 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_polar_3 (rs r θ : ℝ) : killingCov rs r θ 2 3 = 0 := by
  have hω : exteriorConn rs r θ 3 0 2 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_azimuth_0 (rs r θ : ℝ) : killingCov rs r θ 3 0 = 0 := by
  have hω : exteriorConn rs r θ 0 0 3 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_azimuth_1 (rs r θ : ℝ) : killingCov rs r θ 3 1 = 0 := by
  have hω : exteriorConn rs r θ 1 0 3 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_azimuth_2 (rs r θ : ℝ) : killingCov rs r θ 3 2 = 0 := by
  have hω : exteriorConn rs r θ 2 0 3 = 0 := rfl
  simp [killingCov, hω]

theorem killingCov_azimuth_3 (rs r θ : ℝ) : killingCov rs r θ 3 3 = 0 := by
  have hω : exteriorConn rs r θ 3 0 3 = 0 := rfl
  simp [killingCov, hω]

/-! ### Proper radial change of the boost -/

theorem properRadial_killingRate {rs r : ℝ} (h : IsExterior rs r) :
    killingNorm rs r * (-(rs / r ^ 3)) =
      -2 * killingRate rs r * killingNorm rs r / r := by
  have hr : r ≠ 0 := (lt_trans h.1 h.2).ne'
  unfold killingNorm killingRate
  field_simp

theorem properRadial_killingRate_ne {rs r : ℝ} (h : IsExterior rs r) :
    killingNorm rs r * (-(rs / r ^ 3)) ≠ 0 := by
  have hν := killingNorm_pos h
  have hr : 0 < r := lt_trans h.1 h.2
  exact mul_ne_zero hν.ne' (neg_ne_zero.mpr (div_ne_zero h.1.ne' (pow_ne_zero 3 hr.ne')))

theorem conn_staticBoost_radial (rs r θ κ : ℝ) (a b : Fin 4) :
    connOnBivector (exteriorConn rs r θ) (staticBoost κ) 1 a b = 0 := by
  simp only [connOnBivector, exteriorConn_radial, zero_mul, mul_zero, sub_self, add_zero]

theorem conn_staticBoost_time_00 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 0 0 0 = 0 := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, zero_add, sub_zero]
  ring

theorem conn_staticBoost_time_11 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 0 1 1 = 0 := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, sub_zero]
  ring

theorem conn_staticBoost_time_01 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 0 0 1 = 0 := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, sub_zero]
  ring

theorem conn_staticBoost_time_10 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 0 1 0 = 0 := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, sub_zero]
  ring

theorem conn_staticBoost_time_02 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 0 0 2 = 0 := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, sub_zero]

theorem conn_staticBoost_time_20 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 0 2 0 = 0 := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, sub_zero]
  ring

theorem conn_staticBoost_time_03 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 0 0 3 = 0 := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, sub_zero]

theorem conn_staticBoost_time_30 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 0 3 0 = 0 := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, sub_zero]
  ring

theorem properRadial_killingNorm {rs r : ℝ} (h : IsExterior rs r) :
    killingNorm rs r * dSqrtA_dr rs r = killingRate rs r :=
  (killingRate_eq_norm_mul_deriv h).symm

theorem flatRate_unit_radial (κ : ℝ) :
    lorentzAct (pureBoost κ) ![0, 1, 0, 0] = ![κ, 0, 0, 0] := by
  ext μ
  fin_cases μ <;> simp [lorentzAct, pureBoost]

theorem properRadial_killingNorm_eq_flat {rs r : ℝ} (h : IsExterior rs r) :
    lorentzAct (pureBoost (killingRate rs r)) ![0, 1, 0, 0] =
      ![killingNorm rs r * dSqrtA_dr rs r, 0, 0, 0] := by
  rw [properRadial_killingNorm h, flatRate_unit_radial]

/-! ### Angular tilt -/

theorem conn_staticBoost_polar_02 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 2 0 2 =
      killingRate rs r * killingNorm rs r / r := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, zero_add, sub_zero]
  ring

theorem conn_staticBoost_polar_20 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 2 2 0 =
      killingRate rs r * killingNorm rs r / r := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, zero_add, sub_zero]
  ring

theorem conn_staticBoost_azimuth_03 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 3 0 3 =
      killingRate rs r * killingNorm rs r / r := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, zero_mul, add_zero, zero_add, sub_zero]
  ring

theorem conn_staticBoost_azimuth_30 (rs r θ : ℝ) :
    connOnBivector (exteriorConn rs r θ) (staticBoost (killingRate rs r)) 3 3 0 =
      killingRate rs r * killingNorm rs r / r := by
  dsimp [connOnBivector, exteriorConn, staticBoost, radialBoost]
  simp only [mul_zero, add_zero, zero_add, sub_zero]
  ring

theorem static_not_radial_parallel {rs r₁ r₂ : ℝ}
    (h₁ : IsExterior rs r₁) (h₂ : IsExterior rs r₂) (hne : r₁ ≠ r₂) :
    killingRate rs r₁ ≠ killingRate rs r₂ :=
  killingRate_ne_of_exterior h₁ h₂ hne

end DoubleSpacetime.Gravity.CurvedTransport
