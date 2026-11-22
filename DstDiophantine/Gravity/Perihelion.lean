import DstDiophantine.Gravity.RadialFall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Perihelion from the radial law with angular momentum

No chart through the poles is derived, the precessing ellipse is not identified as a solution of the
orbit equation, and the upper bound is not claimed when `3M(α+β) > 1/2`. The tangential tilt is not
the retarded field of a moving source, and this bivector is not the torsional mismatch.
-/

namespace DstDiophantine.Gravity.Perihelion

open Real Set Filter KillingAxis
open scoped Topology

/-! ### The orthonormal frame -/

/-- Squared Lorentz factor relative to the static observer. -/
def gammaSq (ur uφ : ℝ) : ℝ :=
  1 + ur ^ 2 + uφ ^ 2

/-- Orthonormal angular momentum `L/r`. -/
noncomputable def angularMomentum (L r : ℝ) : ℝ :=
  L / r

/-- Rate of the orthonormal radial momentum. The first term is the rapidity law; the second is the
centrifugal change along the angular leg. -/
noncomputable def radialMomentumRate (rs r ur L : ℝ) : ℝ :=
  -(gammaSq ur (angularMomentum L r)) / axisDistance rs r +
    (killingNorm rs r / r) * (angularMomentum L r) ^ 2

/-- Squared energy `E² = A γ²`. -/
noncomputable def orbitEnergySq (rs L r ur : ℝ) : ℝ :=
  killingNorm rs r ^ 2 * gammaSq ur (angularMomentum L r)

theorem gammaSq_zero_angular (ur : ℝ) : gammaSq ur 0 = 1 + ur ^ 2 := by
  simp [gammaSq]

theorem zero_angular_reduces {ℓ ψ : ℝ} :
    Real.cosh ψ * (-Real.cosh ψ / ℓ) = -(1 + (Real.sinh ψ) ^ 2) / ℓ := by
  have h := Real.cosh_sq_sub_sinh_sq ψ
  have hcosh : Real.cosh ψ ^ 2 = 1 + (Real.sinh ψ) ^ 2 := by linarith
  rw [← hcosh]
  ring

theorem radialMomentumRate_zero_angular {rs r ψ : ℝ} (h : IsExterior rs r) :
    radialMomentumRate rs r (Real.sinh ψ) 0 =
      Real.cosh ψ * (-Real.cosh ψ / axisDistance rs r) := by
  have hℓ : axisDistance rs r ≠ 0 := (axisDistance_pos h).ne'
  simp only [radialMomentumRate, angularMomentum, zero_div, gammaSq_zero_angular,
    zero_angular_reduces, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]

/-! ### The three shares -/

theorem areal_accel_parts {ν ℓ ur uφ r : ℝ} (hℓ : ℓ ≠ 0) (hr : r ≠ 0) :
    (ν / ℓ) * ur ^ 2 + ν * (-(gammaSq ur uφ) / ℓ + (ν / r) * uφ ^ 2) =
      -(ν / ℓ) - (ν / ℓ) * uφ ^ 2 + (ν ^ 2 / r) * uφ ^ 2 := by
  unfold gammaSq
  field_simp [hℓ, hr]
  ring

theorem orbit_speed_sq (ν ur uφ : ℝ) :
    (ν * ur) ^ 2 =
      ν ^ 2 * gammaSq ur uφ - ν ^ 2 * (1 + uφ ^ 2) := by
  unfold gammaSq
  ring

theorem centrifugal_deficit {rs r L : ℝ} (hr : r ≠ 0) :
    (schwarzschildA rs r - 1) * L ^ 2 / r ^ 3 = -(rs * L ^ 2) / r ^ 4 := by
  unfold schwarzschildA
  field_simp [hr]
  ring

theorem perihelion_three_shares {rs r L : ℝ} (hr : r ≠ 0) :
    (schwarzschildA rs r - 1) * L ^ 2 / r ^ 3 =
        2 * (-(killingRate rs r) * (L / r) ^ 2) ∧
      -(killingRate rs r) * (L / r) ^ 2 +
          (schwarzschildA rs r - 1) * L ^ 2 / r ^ 3 =
        -3 * killingRate rs r * L ^ 2 / r ^ 2 := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  refine ⟨?_, ?_⟩
  · unfold killingRate schwarzschildA
    field_simp [hr]
    ring
  · unfold killingRate schwarzschildA
    field_simp [hr, h2]
    ring

theorem areal_accel_newton_plus_shares {rs r L : ℝ} (hr : r ≠ 0) :
    -(killingRate rs r) + L ^ 2 / r ^ 3 +
        (-(killingRate rs r) * (L / r) ^ 2) +
        (schwarzschildA rs r - 1) * L ^ 2 / r ^ 3 =
      -(killingRate rs r) + schwarzschildA rs r * L ^ 2 / r ^ 3 -
        killingRate rs r * L ^ 2 / r ^ 2 := by
  unfold killingRate schwarzschildA
  field_simp [hr]
  ring

theorem orbit_cross_term {rs r L : ℝ} (hr : r ≠ 0) :
    schwarzschildA rs r * (1 + (L / r) ^ 2) =
      schwarzschildA rs r + L ^ 2 / r ^ 2 - rs * L ^ 2 / r ^ 3 := by
  unfold schwarzschildA
  field_simp [hr]
  ring

/-! ### Differentiation along the motion -/

theorem angularMomentum_hasDerivAt {L : ℝ} {r : ℝ → ℝ} {τ r' : ℝ}
    (hr0 : r τ ≠ 0) (hderiv : HasDerivAt r r' τ) :
    HasDerivAt (fun σ => angularMomentum L (r σ))
      (-(L * r') / (r τ) ^ 2) τ := by
  have hdiv := (hasDerivAt_const τ L).div hderiv hr0
  have hfun : (fun σ => L) / r = fun σ => angularMomentum L (r σ) := by
    ext σ
    simp [angularMomentum]
  refine (hdiv.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
  ring

theorem gammaSq_hasDerivAt {rs L : ℝ} {r ur : ℝ → ℝ} {τ : ℝ}
    (hExt : IsExterior rs (r τ))
    (hr : HasDerivAt r (killingNorm rs (r τ) * ur τ) τ)
    (hur : HasDerivAt ur (radialMomentumRate rs (r τ) (ur τ) L) τ) :
    HasDerivAt (fun σ => gammaSq (ur σ) (angularMomentum L (r σ)))
      (-(2 * ur τ * gammaSq (ur τ) (angularMomentum L (r τ))) /
        axisDistance rs (r τ)) τ := by
  have hr0 : r τ ≠ 0 := (lt_trans hExt.1 hExt.2).ne'
  have hℓ : axisDistance rs (r τ) ≠ 0 := (axisDistance_pos hExt).ne'
  set ν : ℝ := killingNorm rs (r τ)
  set ℓ : ℝ := axisDistance rs (r τ)
  set uφ : ℝ := angularMomentum L (r τ)
  set γ : ℝ := gammaSq (ur τ) uφ
  have hφ := angularMomentum_hasDerivAt (L := L) hr0 hr
  have hφsq : HasDerivAt (fun σ => (angularMomentum L (r σ)) ^ 2)
      (2 * uφ * (-(L * (ν * ur τ)) / (r τ) ^ 2)) τ := by
    have hmul := hφ.mul hφ
    have hfun : (fun σ => (angularMomentum L (r σ)) ^ 2) =
        (fun σ => angularMomentum L (r σ)) * (fun σ => angularMomentum L (r σ)) := by
      ext σ
      simp [pow_two]
    refine (hmul.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
    ring
  have hursq : HasDerivAt (fun σ => (ur σ) ^ 2)
      (2 * ur τ * radialMomentumRate rs (r τ) (ur τ) L) τ := by
    have hmul := hur.mul hur
    have hfun : (fun σ => (ur σ) ^ 2) = ur * ur := by
      ext σ
      simp [pow_two]
    refine (hmul.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
    ring
  have hsum := (hursq.const_add 1).add hφsq
  have hfun : (fun σ => 1 + (ur σ) ^ 2) + (fun σ => (angularMomentum L (r σ)) ^ 2) =
      fun σ => gammaSq (ur σ) (angularMomentum L (r σ)) := by
    ext σ
    simp [gammaSq]
  refine (hsum.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
  have huφ : uφ = L / r τ := rfl
  have hrate :
      radialMomentumRate rs (r τ) (ur τ) L =
        -γ / ℓ + (ν / r τ) * uφ ^ 2 := by
    simp [radialMomentumRate, γ, ℓ, ν, uφ, gammaSq]
  rw [hrate]
  have hcent :
      2 * ur τ * ((ν / r τ) * uφ ^ 2) +
          2 * uφ * (-(L * (ν * ur τ)) / (r τ) ^ 2) =
        0 := by
    rw [huφ]
    field_simp [hr0]
    ring
  calc
    2 * ur τ * (-γ / ℓ + (ν / r τ) * uφ ^ 2) +
        2 * uφ * (-(L * (ν * ur τ)) / (r τ) ^ 2)
      = 2 * ur τ * (-γ / ℓ) +
          (2 * ur τ * ((ν / r τ) * uφ ^ 2) +
            2 * uφ * (-(L * (ν * ur τ)) / (r τ) ^ 2)) := by ring
    _ = 2 * ur τ * (-γ / ℓ) := by rw [hcent, add_zero]
    _ = -(2 * ur τ * γ) / ℓ := by ring

theorem orbitEnergy_hasDerivAt {rs L : ℝ} {r ur : ℝ → ℝ} {τ : ℝ}
    (hExt : IsExterior rs (r τ))
    (hr : HasDerivAt r (killingNorm rs (r τ) * ur τ) τ)
    (hur : HasDerivAt ur (radialMomentumRate rs (r τ) (ur τ) L) τ) :
    HasDerivAt (fun σ => orbitEnergySq rs L (r σ) (ur σ)) 0 τ := by
  set ℓ : ℝ := axisDistance rs (r τ)
  have hℓ : ℓ ≠ 0 := (axisDistance_pos hExt).ne'
  have hνr := (hasDerivAt_killingNorm hExt).comp τ hr
  have hγ := gammaSq_hasDerivAt hExt hr hur
  have hνsq : HasDerivAt (fun σ => killingNorm rs (r σ) ^ 2)
      (2 * killingNorm rs (r τ) * (dSqrtA_dr rs (r τ) * (killingNorm rs (r τ) * ur τ))) τ := by
    have hmul := hνr.mul hνr
    have hfun : (fun σ => killingNorm rs (r σ) ^ 2) =
        (killingNorm rs ∘ r) * (killingNorm rs ∘ r) := by
      ext σ
      simp [pow_two, Function.comp]
    refine (hmul.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
    simp only [Function.comp_apply]
    ring
  have hprod := hνsq.mul hγ
  have hfun : (fun σ => orbitEnergySq rs L (r σ) (ur σ)) =ᶠ[𝓝 τ]
      (fun σ => killingNorm rs (r σ) ^ 2) *
        fun σ => gammaSq (ur σ) (angularMomentum L (r σ)) := by
    refine EventuallyEq.of_eq ?_
    ext σ
    simp [orbitEnergySq]
  refine (hprod.congr_of_eventuallyEq hfun.symm).congr_deriv ?_
  have hd : dSqrtA_dr rs (r τ) = 1 / ℓ := by
    rw [eq_div_iff hℓ, mul_comm]
    exact axisDistance_mul_dSqrtA_dr hExt
  simp only [show axisDistance rs (r τ) = ℓ from rfl]
  rw [hd]
  field_simp [hℓ]
  ring

theorem arealAccel_hasDerivAt {rs L : ℝ} {r ur : ℝ → ℝ} {τ : ℝ}
    (hExt : IsExterior rs (r τ))
    (hr : HasDerivAt r (killingNorm rs (r τ) * ur τ) τ)
    (hur : HasDerivAt ur (radialMomentumRate rs (r τ) (ur τ) L) τ) :
    HasDerivAt (fun σ => killingNorm rs (r σ) * ur σ)
      (-killingRate rs (r τ) +
        schwarzschildA rs (r τ) * L ^ 2 / (r τ) ^ 3 -
        killingRate rs (r τ) * L ^ 2 / (r τ) ^ 2) τ := by
  set ℓ : ℝ := axisDistance rs (r τ)
  set ν : ℝ := killingNorm rs (r τ)
  have hℓ : ℓ ≠ 0 := (axisDistance_pos hExt).ne'
  have hr0 : r τ ≠ 0 := (lt_trans hExt.1 hExt.2).ne'
  have hνr := (hasDerivAt_killingNorm hExt).comp τ hr
  have hprod := hνr.mul hur
  have hfun : (fun σ => killingNorm rs (r σ) * ur σ) =ᶠ[𝓝 τ]
      (killingNorm rs ∘ r) * ur := by
    refine EventuallyEq.of_eq ?_
    ext σ
    simp [Function.comp]
  refine (hprod.congr_of_eventuallyEq hfun.symm).congr_deriv ?_
  have hd : dSqrtA_dr rs (r τ) = 1 / ℓ := by
    rw [eq_div_iff hℓ, mul_comm]
    exact axisDistance_mul_dSqrtA_dr hExt
  have hνsq : ν ^ 2 = schwarzschildA rs (r τ) :=
    Real.sq_sqrt (schwarzschildA_pos hExt).le
  have hκ : ν / ℓ = killingRate rs (r τ) := by
    rw [div_eq_iff hℓ]
    exact (killingRate_mul_axisDistance hExt).symm
  rw [hd]
  have hparts :=
    areal_accel_parts (ν := ν) (ℓ := ℓ) (ur := ur τ)
      (uφ := angularMomentum L (r τ)) (r := r τ) hℓ hr0
  have hrate :
      radialMomentumRate rs (r τ) (ur τ) L =
        -(gammaSq (ur τ) (angularMomentum L (r τ))) / ℓ +
          (ν / r τ) * (angularMomentum L (r τ)) ^ 2 := by
    simp [radialMomentumRate, ν, ℓ]
  have hang : angularMomentum L (r τ) ^ 2 = L ^ 2 / (r τ) ^ 2 := by
    simp [angularMomentum, pow_two]
    ring
  have hgoal :
      (1 / ℓ) * (ν * ur τ) * ur τ +
          ν * (-(gammaSq (ur τ) (angularMomentum L (r τ))) / ℓ +
            (ν / r τ) * (angularMomentum L (r τ)) ^ 2) =
        -killingRate rs (r τ) + schwarzschildA rs (r τ) * L ^ 2 / (r τ) ^ 3 -
          killingRate rs (r τ) * L ^ 2 / (r τ) ^ 2 := by
    calc
      (1 / ℓ) * (ν * ur τ) * ur τ +
          ν * (-(gammaSq (ur τ) (angularMomentum L (r τ))) / ℓ +
            (ν / r τ) * (angularMomentum L (r τ)) ^ 2)
        = (ν / ℓ) * ur τ ^ 2 +
            ν * (-(gammaSq (ur τ) (angularMomentum L (r τ))) / ℓ +
              (ν / r τ) * (angularMomentum L (r τ)) ^ 2) := by ring
      _ = -(ν / ℓ) - (ν / ℓ) * (angularMomentum L (r τ)) ^ 2 +
            (ν ^ 2 / r τ) * (angularMomentum L (r τ)) ^ 2 := hparts
      _ = -killingRate rs (r τ) + schwarzschildA rs (r τ) * L ^ 2 / (r τ) ^ 3 -
            killingRate rs (r τ) * L ^ 2 / (r τ) ^ 2 := by
          rw [hκ, hang, hνsq]
          field_simp [hr0]
          ring
  rw [hrate]
  exact hgoal

theorem orbitEnergy_eq_on {rs L a b : ℝ} {r ur : ℝ → ℝ} (_hab : a ≤ b)
    (hExt : ∀ τ ∈ Icc a b, IsExterior rs (r τ))
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (killingNorm rs (r τ) * ur τ) τ)
    (hur : ∀ τ ∈ Icc a b,
      HasDerivAt ur (radialMomentumRate rs (r τ) (ur τ) L) τ)
    {τ₁ τ₂ : ℝ} (h₁ : τ₁ ∈ Icc a b) (h₂ : τ₂ ∈ Icc a b) :
    orbitEnergySq rs L (r τ₁) (ur τ₁) = orbitEnergySq rs L (r τ₂) (ur τ₂) := by
  let E : ℝ → ℝ := fun σ => orbitEnergySq rs L (r σ) (ur σ)
  have hE : ∀ σ ∈ Icc a b, HasDerivAt E 0 σ := fun σ hσ =>
    orbitEnergy_hasDerivAt (hExt σ hσ) (hr σ hσ) (hur σ hσ)
  have hlip :=
    Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (C := 0) (f := E) (s := Icc a b)
      (fun σ hσ => (hE σ hσ).differentiableAt)
      (fun σ hσ => by
        rw [(hE σ hσ).deriv]
        simp)
      (convex_Icc a b) h₁ h₂
  have hle : ‖E τ₂ - E τ₁‖ ≤ 0 := by simpa using hlip
  have hsub : E τ₂ - E τ₁ = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact (sub_eq_zero.mp hsub).symm

theorem orbit_first_integral {rs L a b : ℝ} {r ur : ℝ → ℝ} (hab : a ≤ b)
    (hExt : ∀ τ ∈ Icc a b, IsExterior rs (r τ))
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (killingNorm rs (r τ) * ur τ) τ)
    (hur : ∀ τ ∈ Icc a b,
      HasDerivAt ur (radialMomentumRate rs (r τ) (ur τ) L) τ)
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ Icc a b) (hτ : τ ∈ Icc a b) :
    (deriv r τ) ^ 2 =
      orbitEnergySq rs L (r τ₀) (ur τ₀) -
        schwarzschildA rs (r τ) * (1 + (L / r τ) ^ 2) := by
  have hE := orbitEnergy_eq_on hab hExt hr hur hτ h₀
  have hv := (hr τ hτ).deriv
  rw [hv]
  have hsq := orbit_speed_sq (killingNorm rs (r τ)) (ur τ) (angularMomentum L (r τ))
  have hν : killingNorm rs (r τ) ^ 2 = schwarzschildA rs (r τ) :=
    Real.sq_sqrt (schwarzschildA_pos (hExt τ hτ)).le
  have hang : (angularMomentum L (r τ)) ^ 2 = (L / r τ) ^ 2 := rfl
  calc (killingNorm rs (r τ) * ur τ) ^ 2
      = orbitEnergySq rs L (r τ) (ur τ) -
          killingNorm rs (r τ) ^ 2 * (1 + (angularMomentum L (r τ)) ^ 2) := by
        simpa [orbitEnergySq, gammaSq] using hsq
    _ = orbitEnergySq rs L (r τ₀) (ur τ₀) -
          schwarzschildA rs (r τ) * (1 + (L / r τ) ^ 2) := by
        rw [hE, hν, hang]

/-! ### The orbit equation -/

theorem binet_rearrange {u u' u'' rs L : ℝ} (hL : L ≠ 0) (hu' : u' ≠ 0)
    (h : 2 * L ^ 2 * u' * u'' =
      rs * u' * (1 + L ^ 2 * u ^ 2) - (1 - rs * u) * (2 * L ^ 2 * u * u')) :
    u'' + u = rs / (2 * L ^ 2) + (3 / 2) * rs * u ^ 2 := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hden : 2 * L ^ 2 * u' ≠ 0 := mul_ne_zero (mul_ne_zero h2 hL2) hu'
  have hdiv : u'' =
      (rs * u' * (1 + L ^ 2 * u ^ 2) - (1 - rs * u) * (2 * L ^ 2 * u * u')) /
        (2 * L ^ 2 * u') := by
    rw [eq_div_iff hden]
    linarith
  rw [hdiv]
  field_simp [h2, hL2, hu']
  ring

def binetResidual (E rs L u : ℝ) : ℝ :=
  E ^ 2 - (1 - rs * u) * (1 + L ^ 2 * u ^ 2)

theorem binet_rhs_hasDerivAt {E rs L : ℝ} {u : ℝ → ℝ} {φ u' : ℝ}
    (hu : HasDerivAt u u' φ) :
    HasDerivAt (fun ψ => binetResidual E rs L (u ψ))
      (rs * u' * (1 + L ^ 2 * (u φ) ^ 2) -
        (1 - rs * u φ) * (2 * L ^ 2 * u φ * u')) φ := by
  have hlin : HasDerivAt (fun ψ => 1 - rs * u ψ) (-(rs * u')) φ := by
    have h := hu.const_mul rs
    have hsub := h.const_sub 1
    simpa using hsub.congr_deriv (by ring)
  have hu2 : HasDerivAt (fun ψ => (u ψ) ^ 2) (2 * u φ * u') φ := by
    have hmul := hu.mul hu
    have hfun : (fun ψ => (u ψ) ^ 2) = u * u := by
      ext ψ
      simp [pow_two]
    refine (hmul.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
    ring
  have hang : HasDerivAt (fun ψ => 1 + L ^ 2 * (u ψ) ^ 2)
      (L ^ 2 * (2 * u φ * u')) φ := by
    have h := hu2.const_mul (L ^ 2)
    exact (h.const_add 1).congr_deriv (by ring)
  have hprod := hlin.mul hang
  have hneg := hprod.const_sub (E ^ 2)
  have hfun : (fun ψ => binetResidual E rs L (u ψ)) =
      (fun _ => E ^ 2) - ((fun ψ => 1 - rs * u ψ) * fun ψ => 1 + L ^ 2 * (u ψ) ^ 2) := by
    ext ψ
    simp [binetResidual]
  refine (hneg.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
  ring

theorem binet_equation {E rs L : ℝ} {u : ℝ → ℝ} {φ : ℝ}
    (hL : L ≠ 0) (hu' : deriv u φ ≠ 0)
    (hu : HasDerivAt u (deriv u φ) φ)
    (hu2 : HasDerivAt (deriv u) (deriv (deriv u) φ) φ)
    (henergy : ∀ ψ, (L * deriv u ψ) ^ 2 = binetResidual E rs L (u ψ)) :
    deriv (deriv u) φ + u φ =
      rs / (2 * L ^ 2) + (3 / 2) * rs * (u φ) ^ 2 := by
  have hleft : HasDerivAt (fun ψ => (L * deriv u ψ) ^ 2)
      (2 * (L * deriv u φ) * (L * deriv (deriv u) φ)) φ := by
    have hchain : HasDerivAt (fun ψ => L * deriv u ψ) (L * deriv (deriv u) φ) φ :=
      hu2.const_mul L
    have hmul := hchain.mul hchain
    have hfun : (fun ψ => (L * deriv u ψ) ^ 2) =
        (fun ψ => L * deriv u ψ) * fun ψ => L * deriv u ψ := by
      ext ψ
      simp [pow_two]
    refine (hmul.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
    ring
  have hright := binet_rhs_hasDerivAt (E := E) (rs := rs) (L := L) hu
  have heq : (fun ψ => (L * deriv u ψ) ^ 2) = fun ψ => binetResidual E rs L (u ψ) := by
    ext ψ
    exact henergy ψ
  have hdleft := hleft.deriv
  have hdright := hright.deriv
  rw [heq] at hdleft
  have hrel : 2 * L ^ 2 * deriv u φ * deriv (deriv u) φ =
      rs * deriv u φ * (1 + L ^ 2 * (u φ) ^ 2) -
        (1 - rs * u φ) * (2 * L ^ 2 * u φ * deriv u φ) := by
    have hcomm : 2 * (L * deriv u φ) * (L * deriv (deriv u) φ) =
        2 * L ^ 2 * deriv u φ * deriv (deriv u) φ := by ring
    rw [← hcomm, ← hdleft, hdright]
  exact binet_rearrange hL hu' hrel

/-! ### The resonant harmonic -/

/-- Precessing ellipse `u = A (1 + e cos(kφ))`. -/
noncomputable def precessingU (A e k φ : ℝ) : ℝ :=
  A * (1 + e * Real.cos (k * φ))

theorem hasDerivAt_precessing (A e k φ : ℝ) :
    HasDerivAt (precessingU A e k) (-(A * e * k) * Real.sin (k * φ)) φ := by
  have hangle0 := (hasDerivAt_id φ).const_mul k
  have hangle : HasDerivAt (fun t => k * t) k φ := by
    have hfun : (fun t => k * t) = fun y => k * id y := by
      ext t
      simp
    exact (hangle0.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by simp)
  have hcomp := (Real.hasDerivAt_cos (k * φ)).comp φ hangle
  have hcos : HasDerivAt (fun t => Real.cos (k * t)) (-(Real.sin (k * φ) * k)) φ := by
    have hfun : (fun t => Real.cos (k * t)) = Real.cos ∘ fun t => k * t := by
      ext t
      rfl
    exact (hcomp.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by ring)
  have he := hcos.const_mul e
  have hadd : HasDerivAt (fun t => 1 + e * Real.cos (k * t))
      (e * (-(Real.sin (k * φ) * k))) φ :=
    (he.const_add 1).congr_deriv (by ring)
  have hmul := hadd.const_mul A
  have hfun : precessingU A e k = fun t => A * (1 + e * Real.cos (k * t)) := by
    ext t
    rfl
  refine (hmul.congr_of_eventuallyEq (EventuallyEq.of_eq hfun.symm)).congr_deriv ?_
  ring

theorem deriv_precessing (A e k φ : ℝ) :
    deriv (precessingU A e k) φ = -(A * e * k) * Real.sin (k * φ) :=
  (hasDerivAt_precessing A e k φ).deriv

theorem hasDerivAt_precessing_velocity (A e k φ : ℝ) :
    HasDerivAt (fun t => -(A * e * k) * Real.sin (k * t))
      (-(A * e * k ^ 2) * Real.cos (k * φ)) φ := by
  have hangle : HasDerivAt (fun t : ℝ => k * t) k φ := by
    simpa [id_eq, one_mul] using (hasDerivAt_id φ).const_mul k
  have hsin := (Real.hasDerivAt_sin (k * φ)).comp φ hangle
  have hmul := hsin.const_mul (-(A * e * k))
  simpa [Function.comp, pow_two] using hmul.congr_deriv (by ring)

theorem deriv_deriv_precessing (A e k φ : ℝ) :
    deriv (deriv (precessingU A e k)) φ = -(A * e * k ^ 2) * Real.cos (k * φ) := by
  have hfun : deriv (precessingU A e k) =
      fun t => -(A * e * k) * Real.sin (k * t) := by
    ext t
    exact deriv_precessing A e k t
  rw [hfun]
  exact (hasDerivAt_precessing_velocity A e k φ).deriv

theorem resonant_coefficient {M L e k : ℝ} (hL : L ≠ 0) (he : e ≠ 0) (hM : M ≠ 0) :
    (M / L ^ 2) * e * (1 - k ^ 2) = 6 * M * (M / L ^ 2) ^ 2 * e ↔
      k ^ 2 = 1 - 6 * M ^ 2 / L ^ 2 := by
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hAe : (M / L ^ 2) * e ≠ 0 := mul_ne_zero (div_ne_zero hM hL2) he
  have h6 : 6 * M * (M / L ^ 2) = 6 * M ^ 2 / L ^ 2 := by
    field_simp [hL2]
  constructor
  · intro h
    have hfactor : 6 * M * (M / L ^ 2) ^ 2 * e =
        (M / L ^ 2) * e * (6 * M * (M / L ^ 2)) := by
      field_simp [hL2]
    rw [hfactor] at h
    have hcoeff : 1 - k ^ 2 = 6 * M * (M / L ^ 2) := mul_left_cancel₀ hAe h
    rw [h6] at hcoeff
    linarith
  · intro hk
    have h1 : 1 - k ^ 2 = 6 * M ^ 2 / L ^ 2 := by linarith
    calc (M / L ^ 2) * e * (1 - k ^ 2)
        = (M / L ^ 2) * e * (6 * M ^ 2 / L ^ 2) := by rw [h1]
      _ = (M / L ^ 2) * e * (6 * M * (M / L ^ 2)) := by rw [h6]
      _ = 6 * M * (M / L ^ 2) ^ 2 * e := by
          field_simp [hL2]

/-- The failure of the orbit equation is a constant plus a double angle. -/
theorem precessing_residual {M L e k θ : ℝ} (hL : L ≠ 0)
    (hk : k ^ 2 = 1 - 6 * M ^ 2 / L ^ 2) :
    let A := M / L ^ 2
    let u := A * (1 + e * Real.cos θ)
    let u'' := -(A * e * k ^ 2) * Real.cos θ
    u'' + u - (A + 3 * M * u ^ 2) =
      -(3 * M) * A ^ 2 * (1 + e ^ 2 * (Real.cos θ) ^ 2) := by
  dsimp
  rw [hk]
  field_simp [(pow_ne_zero 2 hL : L ^ 2 ≠ 0)]
  ring

theorem precessing_residual_at {M L e k φ : ℝ} (hL : L ≠ 0)
    (hk : k ^ 2 = 1 - 6 * M ^ 2 / L ^ 2) :
    let A := M / L ^ 2
    deriv (deriv (precessingU A e k)) φ + precessingU A e k φ -
        (A + 3 * M * (precessingU A e k φ) ^ 2) =
      -(3 * M) * A ^ 2 * (1 + e ^ 2 * (Real.cos (k * φ)) ^ 2) := by
  simpa [precessingU, deriv_deriv_precessing] using
    precessing_residual (M := M) (L := L) (e := e) (k := k) (θ := k * φ) hL hk

/-! ### One radial period of the resonant ellipse -/

theorem inv_sqrt_sub_one {x : ℝ} (hx1 : x < 1) (_hx0 : 0 ≤ x) :
    1 / Real.sqrt (1 - x) - 1 =
      x / (Real.sqrt (1 - x) * (1 + Real.sqrt (1 - x))) := by
  set s : ℝ := Real.sqrt (1 - x)
  have hs0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1.le
  have hspos : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr hx1)
  have hsq : s ^ 2 = 1 - x := Real.sq_sqrt hs0
  have hsne : s ≠ 0 := hspos.ne'
  have hone : (1 - s) * (1 + s) = x := by
    have : (1 - s) * (1 + s) = 1 - s ^ 2 := by ring
    linarith
  calc 1 / s - 1
      = (1 - s) / s := by field_simp
    _ = x / (s * (1 + s)) := by
        rw [eq_div_iff (mul_ne_zero hsne (by linarith : 1 + s ≠ 0))]
        have hden : s ≠ 0 := hsne
        field_simp [hden]
        linarith

theorem sqrt_lt_one_of_pos {x : ℝ} (_hx0 : 0 < x) (hx1 : x < 1) :
    Real.sqrt (1 - x) < 1 := by
  have hlt : Real.sqrt (1 - x) < Real.sqrt 1 :=
    Real.sqrt_lt_sqrt (sub_nonneg.mpr hx1.le) (by linarith : 1 - x < 1)
  exact lt_of_lt_of_eq hlt Real.sqrt_one

theorem one_sub_lt_sqrt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 - x < Real.sqrt (1 - x) := by
  have hs0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1.le
  have hsq : (1 - x) ^ 2 < Real.sqrt (1 - x) ^ 2 := by
    rw [Real.sq_sqrt hs0]
    nlinarith
  have habs := (sq_lt_sq).mp hsq
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - x), abs_of_nonneg (Real.sqrt_nonneg _)] at habs
  exact habs

theorem inv_sqrt_sub_one_bounds {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x / 2 < 1 / Real.sqrt (1 - x) - 1 ∧
      1 / Real.sqrt (1 - x) - 1 < (x / 2) / (1 - x) := by
  set s : ℝ := Real.sqrt (1 - x)
  have hspos : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr hx1)
  have hs1 : s < 1 := sqrt_lt_one_of_pos hx0 hx1
  have hslow : 1 - x < s := one_sub_lt_sqrt hx0 hx1
  have hsq : s ^ 2 = 1 - x := Real.sq_sqrt (sub_nonneg.mpr hx1.le)
  have hid := inv_sqrt_sub_one hx1 hx0.le
  have hden_pos : 0 < s * (1 + s) := by positivity
  have hden_lt : s * (1 + s) < 2 := by nlinarith [hsq]
  have hden_gt : 2 * (1 - x) < s * (1 + s) := by nlinarith [hsq, hslow]
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  constructor
  · rw [hid]
    exact div_lt_div_of_pos_left hx0 hden_pos hden_lt
  · rw [hid]
    have hsmall : 0 < 2 * (1 - x) := by positivity
    have hlt : x / (s * (1 + s)) < x / (2 * (1 - x)) :=
      div_lt_div_of_pos_left hx0 hsmall hden_gt
    have hrewrite : x / (2 * (1 - x)) = (x / 2) / (1 - x) := by
      field_simp [h1x.ne']
    linarith

theorem perihelion_excess_bounds {M L : ℝ}
    (hx0 : 0 < 6 * M ^ 2 / L ^ 2) (hx1 : 6 * M ^ 2 / L ^ 2 < 1) :
    let x := 6 * M ^ 2 / L ^ 2
    let k := Real.sqrt (1 - x)
    6 * Real.pi * M ^ 2 / L ^ 2 < 2 * Real.pi * (1 / k - 1) ∧
      2 * Real.pi * (1 / k - 1) <
        (6 * Real.pi * M ^ 2 / L ^ 2) / (1 - 6 * M ^ 2 / L ^ 2) := by
  dsimp
  set x : ℝ := 6 * M ^ 2 / L ^ 2
  have hb := inv_sqrt_sub_one_bounds hx0 hx1
  have hpi : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hlow := mul_lt_mul_of_pos_left hb.1 hpi
  have hhigh := mul_lt_mul_of_pos_left hb.2 hpi
  have hlowEq : 2 * Real.pi * (x / 2) = 6 * Real.pi * M ^ 2 / L ^ 2 := by
    unfold x
    ring
  have hhighEq : 2 * Real.pi * ((x / 2) / (1 - x)) =
      (6 * Real.pi * M ^ 2 / L ^ 2) / (1 - x) := by
    unfold x
    field_simp [sub_ne_zero.mpr hx1.ne]
  constructor
  · simpa [hlowEq] using hlow
  · simpa [hhighEq] using hhigh

theorem perihelion_excess_latus {M L p : ℝ} (hM : M ≠ 0) (hp : p = L ^ 2 / M)
    (hx0 : 0 < 6 * M / p) (hx1 : 6 * M / p < 1) :
    let k := Real.sqrt (1 - 6 * M / p)
    6 * Real.pi * M / p < 2 * Real.pi * (1 / k - 1) ∧
      2 * Real.pi * (1 / k - 1) < (6 * Real.pi * M / p) / (1 - 6 * M / p) := by
  have hMp : M / p = M ^ 2 / L ^ 2 := by
    have hL2 : L ^ 2 ≠ 0 := by
      intro h0
      have hp0 : p = 0 := by simp [hp, h0]
      rw [hp0] at hx0
      simp at hx0
    rw [hp]
    field_simp [hM]
  have h6 : 6 * M ^ 2 / L ^ 2 = 6 * M / p := by
    calc 6 * M ^ 2 / L ^ 2
        = 6 * (M ^ 2 / L ^ 2) := by ring
      _ = 6 * (M / p) := by rw [← hMp]
      _ = 6 * M / p := by ring
  have hx0' : 0 < 6 * M ^ 2 / L ^ 2 := by simpa [h6] using hx0
  have hx1' : 6 * M ^ 2 / L ^ 2 < 1 := by simpa [h6] using hx1
  have hcoef : 6 * Real.pi * M ^ 2 / L ^ 2 = 6 * Real.pi * M / p := by
    calc 6 * Real.pi * M ^ 2 / L ^ 2
        = Real.pi * (6 * M ^ 2 / L ^ 2) := by ring
      _ = Real.pi * (6 * M / p) := by rw [h6]
      _ = 6 * Real.pi * M / p := by ring
  have h := perihelion_excess_bounds (M := M) (L := L) hx0' hx1'
  dsimp at h ⊢
  rw [hcoef, h6] at h
  exact h

/-! ### A light-speed tilt drains; the torsional leg does not -/

theorem radial_speed_cancels {κ ur uφ : ℝ} :
    κ * ur ^ 2 - κ * gammaSq ur uφ = -κ * (1 + uφ ^ 2) := by
  unfold gammaSq
  ring

theorem transverse_remains_perihelion {rs r L : ℝ} (hr : r ≠ 0) :
    -killingRate rs r * (1 + (L / r) ^ 2) + schwarzschildA rs r * L ^ 2 / r ^ 3 =
      -killingRate rs r + L ^ 2 / r ^ 3 - 3 * killingRate rs r * L ^ 2 / r ^ 2 := by
  unfold killingRate schwarzschildA
  field_simp [hr]
  ring

theorem aberration_power {κ uφ : ℝ} : (-κ * uφ) * uφ = -κ * uφ ^ 2 := by
  ring

theorem aberration_power_neg {κ uφ : ℝ} (hκ : 0 < κ) (hφ : uφ ≠ 0) :
    (-κ * uφ) * uφ < 0 := by
  rw [aberration_power]
  have hsq : 0 < uφ ^ 2 := sq_pos_of_ne_zero hφ
  nlinarith [hκ, hsq]

theorem naiveAngular_hasDerivAt (κ L0 τ : ℝ) :
    HasDerivAt (fun σ => L0 * Real.exp (-κ * σ))
      (-κ * (L0 * Real.exp (-κ * τ))) τ := by
  have hangle0 := (hasDerivAt_id τ).const_mul (-κ)
  have hlin : HasDerivAt (fun σ => -κ * σ) (-κ) τ := by
    have hfun : (fun σ => -κ * σ) = fun y => -κ * id y := by
      ext σ
      simp
    exact (hangle0.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by simp)
  have hcomp := (Real.hasDerivAt_exp (-κ * τ)).comp τ hlin
  have hexp : HasDerivAt (fun σ => Real.exp (-κ * σ))
      (Real.exp (-κ * τ) * -κ) τ := by
    have hfun : (fun σ => Real.exp (-κ * σ)) = Real.exp ∘ fun σ => -κ * σ := by
      ext σ
      rfl
    exact (hcomp.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by ring)
  exact (hexp.const_mul L0).congr_deriv (by ring)

theorem naiveAngular_strictAnti {κ L0 τ₁ τ₂ : ℝ} (hL : 0 < L0) (hκ : 0 < κ)
    (hτ : τ₁ < τ₂) :
    L0 * Real.exp (-κ * τ₂) < L0 * Real.exp (-κ * τ₁) := by
  have hneg : -κ * τ₂ < -κ * τ₁ := by nlinarith
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hneg) hL

theorem naive_log_per_radian {κ r uφ : ℝ} (hφ : uφ ≠ 0) (hr : r ≠ 0)
    (hvir : uφ ^ 2 = κ * r) :
    ((-κ * uφ) / (uφ / r)) / uφ = -uφ := by
  have hrew : ((-κ * uφ) / (uφ / r)) / uφ = -κ * r / uφ := by
    field_simp [hφ, hr]
  have hright : -κ * r / uφ = -uφ := by
    calc -κ * r / uφ
        = -(κ * r) / uφ := by ring
      _ = -(uφ ^ 2) / uφ := by rw [← hvir]
      _ = -uφ := by field_simp [hφ]
  rw [hrew, hright]

theorem naive_log_per_revolution {κ r uφ : ℝ} (hφ : uφ ≠ 0) (hr : r ≠ 0)
    (hvir : uφ ^ 2 = κ * r) :
    2 * Real.pi * (((-κ * uφ) / (uφ / r)) / uφ) = -(2 * Real.pi * uφ) := by
  rw [naive_log_per_radian hφ hr hvir]
  ring

theorem torsional_angular_power {ν r ur uφ : ℝ} :
    uφ * (-(uφ * ν * ur) / r) = -(uφ ^ 2 * ν * ur) / r := by
  ring

theorem torsional_circular_power {ν r uφ : ℝ} :
    uφ * (-(uφ * ν * (0 : ℝ)) / r) = 0 := by
  ring

/-! ### Turning values -/

open intervalIntegral MeasureTheory

/-- Slope squared, as a cubic in the reciprocal radius. -/
noncomputable def radialSlope (M α β γ u : ℝ) : ℝ :=
  2 * M * (u - α) * (β - u) * (γ - u)

/-- The cosine parameter that runs from the larger root to the smaller one. -/
noncomputable def turningParam (α β θ : ℝ) : ℝ :=
  (α + β) / 2 + ((β - α) / 2) * Real.cos θ

/-- Integrand of the return angle, after the cosine substitution. -/
noncomputable def returnIntegrand (M α β θ : ℝ) : ℝ :=
  1 / Real.sqrt (1 - 3 * M * (α + β) - M * (β - α) * Real.cos θ)

/-- Angle from one visit of the larger turning value to the next. -/
noncomputable def radialReturn (M α β : ℝ) : ℝ :=
  2 * ∫ θ in (0 : ℝ)..Real.pi, returnIntegrand M α β θ

theorem radialSlope_eq_cubic {M α β γ u : ℝ} (hM : M ≠ 0)
    (hsum : α + β + γ = 1 / (2 * M)) :
    radialSlope M α β γ u =
      2 * M * u ^ 3 - u ^ 2 +
        2 * M * (α * β + β * γ + γ * α) * u - 2 * M * α * β * γ := by
  have hγ : γ = 1 / (2 * M) - α - β := by linarith
  rw [radialSlope, hγ]
  field_simp [hM]
  ring

theorem binetResidual_eq_radialSlope {E L M α β γ u : ℝ}
    (hM : M ≠ 0) (hL : L ≠ 0)
    (hsum : α + β + γ = 1 / (2 * M))
    (hσ : α * β + β * γ + γ * α = 1 / L ^ 2)
    (hE : E ^ 2 = 1 - 2 * M * α * β * γ * L ^ 2) :
    binetResidual E (2 * M) L u = L ^ 2 * radialSlope M α β γ u := by
  rw [radialSlope_eq_cubic hM hsum, binetResidual, hE, hσ]
  field_simp [hL]
  ring

theorem hasDerivAt_turningParam (α β θ : ℝ) :
    HasDerivAt (turningParam α β) (-(((β - α) / 2) * Real.sin θ)) θ := by
  have hcos := Real.hasDerivAt_cos θ
  have hmul := hcos.const_mul ((β - α) / 2)
  convert (hmul.const_add ((α + β) / 2)).congr_deriv ?_ using 1
  · ext t
    rfl
  · ring

theorem turningParam_product {α β θ : ℝ} :
    (turningParam α β θ - α) * (β - turningParam α β θ) =
      ((β - α) / 2) ^ 2 * (Real.sin θ) ^ 2 := by
  unfold turningParam
  have hpyth : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  rw [hpyth]
  ring

theorem turning_radicand {M α β γ θ : ℝ} (hM : M ≠ 0)
    (hsum : α + β + γ = 1 / (2 * M)) :
    2 * M * (γ - turningParam α β θ) =
      1 - 3 * M * (α + β) - M * (β - α) * Real.cos θ := by
  have hγ : γ = 1 / (2 * M) - α - β := by linarith
  rw [turningParam, hγ]
  field_simp [hM]
  ring

theorem radialSlope_param {M α β γ θ : ℝ} (hM : M ≠ 0)
    (hsum : α + β + γ = 1 / (2 * M)) :
    radialSlope M α β γ (turningParam α β θ) =
      (((β - α) / 2) * Real.sin θ) ^ 2 *
        (1 - 3 * M * (α + β) - M * (β - α) * Real.cos θ) := by
  have hprod := turningParam_product (α := α) (β := β) (θ := θ)
  have hrad := turning_radicand (M := M) (α := α) (β := β) (γ := γ) (θ := θ) hM hsum
  unfold radialSlope
  calc 2 * M * (turningParam α β θ - α) * (β - turningParam α β θ) *
        (γ - turningParam α β θ)
      = (2 * M) * ((turningParam α β θ - α) * (β - turningParam α β θ)) *
          (γ - turningParam α β θ) := by ring
    _ = (2 * M) * ((((β - α) / 2) ^ 2) * (Real.sin θ) ^ 2) *
          (γ - turningParam α β θ) := by rw [hprod]
    _ = (((β - α) / 2) * Real.sin θ) ^ 2 *
          (2 * M * (γ - turningParam α β θ)) := by ring
    _ = (((β - α) / 2) * Real.sin θ) ^ 2 *
          (1 - 3 * M * (α + β) - M * (β - α) * Real.cos θ) := by
        rw [hrad]

theorem angularLatus_gt_turning {M L α β γ : ℝ} (hM : 0 < M) (hα : 0 ≤ α)
    (hαβ : α < β) (hβγ : β < γ) (hsum : α + β + γ = 1 / (2 * M))
    (hσ : α * β + β * γ + γ * α = 1 / L ^ 2) :
    2 / (α + β) < L ^ 2 / M := by
  set s : ℝ := α + β
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hγ : γ = 1 / (2 * M) - s := by
    dsimp [s]
    linarith
  have hab : 4 * (α * β) ≤ s ^ 2 := by
    nlinarith [sq_nonneg (α - β)]
  have hform : α * β + β * γ + γ * α = α * β + s / (2 * M) - s ^ 2 := by
    rw [hγ]
    dsimp [s]
    ring
  have hlt : α * β + s / (2 * M) - s ^ 2 < s / (2 * M) := by
    have hdrop : α * β - s ^ 2 ≤ - (3 / 4) * s ^ 2 := by
      nlinarith [hab]
    have hpos : 0 < (3 / 4) * s ^ 2 := by positivity
    linarith
  have hσlt : 1 / L ^ 2 < s / (2 * M) := by
    rw [← hσ, hform]
    exact hlt
  have hposσ : 0 < 1 / L ^ 2 := by
    have hβ : 0 < β := lt_of_le_of_lt hα hαβ
    have hγp : 0 < γ := lt_trans hβ hβγ
    have hσpos : 0 < α * β + β * γ + γ * α := by
      have : 0 < β * γ := mul_pos hβ hγp
      nlinarith [mul_nonneg hα hβ.le, mul_nonneg hγp.le hα]
    simpa [hσ] using hσpos
  have hrec : 2 * M / s < L ^ 2 := by
    have h := (one_div_lt_one_div (by positivity : 0 < s / (2 * M)) hposσ).mpr hσlt
    simpa [one_div] using h
  have hmul : (2 / s) * M < L ^ 2 := by
    simpa [div_mul_eq_mul_div] using hrec
  exact (lt_div_iff₀ hM).mpr hmul

theorem turning_sum_lt_one {M α β γ : ℝ} (hM : 0 < M) (hαβ : α < β) (hβγ : β < γ)
    (hsum : α + β + γ = 1 / (2 * M)) :
    3 * M * (α + β) < 1 := by
  have hγ : γ = 1 / (2 * M) - α - β := by linarith
  have hgap : 0 < 2 * M * (γ - β) := by positivity
  have hcmp : 3 * (α + β) < 2 * (α + 2 * β) := by linarith
  have hmul : 3 * M * (α + β) < 2 * M * (α + 2 * β) := by
    nlinarith
  have hclear : 2 * M * (α + 2 * β) < 1 := by
    rw [hγ] at hgap
    have h2 : (2 : ℝ) * M ≠ 0 := by positivity
    field_simp [h2] at hgap
    linarith
  linarith

private theorem inv_sqrt_gap {t c : ℝ} (ht : 0 < t) (hc : 0 < c) :
    1 / Real.sqrt t -
        (1 / Real.sqrt c - (t - c) / (2 * c * Real.sqrt c)) =
      (Real.sqrt c - Real.sqrt t) ^ 2 *
        (2 * Real.sqrt c + Real.sqrt t) /
          (2 * Real.sqrt t * (Real.sqrt c) ^ 3) := by
  set s : ℝ := Real.sqrt t
  set r : ℝ := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.mpr ht
  have hr : 0 < r := Real.sqrt_pos.mpr hc
  have hst : s ^ 2 = t := Real.sq_sqrt ht.le
  have hrc : r ^ 2 = c := Real.sq_sqrt hc.le
  have hpoly : 2 * r ^ 3 - 3 * s * r ^ 2 + s ^ 3 = (r - s) ^ 2 * (2 * r + s) := by ring
  have hfrac : 1 / s - (1 / r - (s ^ 2 - r ^ 2) / (2 * r ^ 3)) =
      (2 * r ^ 3 - 3 * s * r ^ 2 + s ^ 3) / (2 * s * r ^ 3) := by
    field_simp [hs.ne', hr.ne']
    ring
  calc 1 / s - (1 / r - (t - c) / (2 * c * r))
      = 1 / s - (1 / r - (s ^ 2 - r ^ 2) / (2 * r ^ 2 * r)) := by
        rw [hst, hrc]
    _ = 1 / s - (1 / r - (s ^ 2 - r ^ 2) / (2 * r ^ 3)) := by
        have hden : (2 : ℝ) * r ^ 2 * r = 2 * r ^ 3 := by ring
        rw [hden]
    _ = (r - s) ^ 2 * (2 * r + s) / (2 * s * r ^ 3) := by
        rw [hfrac, hpoly]

private theorem inv_sqrt_tangent {t c : ℝ} (ht : 0 < t) (hc : 0 < c) :
    1 / Real.sqrt c - (t - c) / (2 * c * Real.sqrt c) ≤ 1 / Real.sqrt t := by
  have hgap := inv_sqrt_gap ht hc
  have hnonneg : 0 ≤ (Real.sqrt c - Real.sqrt t) ^ 2 *
      (2 * Real.sqrt c + Real.sqrt t) /
        (2 * Real.sqrt t * (Real.sqrt c) ^ 3) := by
    positivity
  linarith

private theorem integral_cos_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ = 0 := by
  simp [integral_cos, Real.sin_pi, Real.sin_zero]

private theorem integral_cos_sq_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 = Real.pi / 2 := by
  have hfun : (fun θ : ℝ => Real.cos θ ^ 2) = fun θ => (1 + Real.cos (2 * θ)) / 2 := by
    ext θ
    rw [Real.cos_sq]
    ring
  rw [hfun]
  have hsplit : (fun θ : ℝ => (1 + Real.cos (2 * θ)) / 2) =
      fun θ => (1 / 2) * (1 + Real.cos (2 * θ)) := by
    ext θ
    ring
  rw [hsplit, intervalIntegral.integral_const_mul]
  have hcont : Continuous (fun θ : ℝ => Real.cos (2 * θ)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcos : ∫ θ in (0 : ℝ)..Real.pi, Real.cos (2 * θ) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) two_ne_zero]
    simp [integral_cos, Real.sin_zero, Real.sin_two_pi]
  have hone : ∫ θ in (0 : ℝ)..Real.pi, (1 : ℝ) = Real.pi := by
    simp [intervalIntegral.integral_const]
  have hadd : ∫ θ in (0 : ℝ)..Real.pi, (1 + Real.cos (2 * θ)) =
      (∫ θ in (0 : ℝ)..Real.pi, (1 : ℝ)) + ∫ θ in (0 : ℝ)..Real.pi, Real.cos (2 * θ) :=
    intervalIntegral.integral_add intervalIntegrable_const (hcont.intervalIntegrable 0 Real.pi)
  rw [hadd, hcos, hone]
  field_simp
  ring

private theorem kRatio_antitone {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) :
    (2 + t) / (t * (1 + t) ^ 2) ≤ (2 + s) / (s * (1 + s) ^ 2) := by
  have hfac : (2 + s) * t * (1 + t) ^ 2 - (2 + t) * s * (1 + s) ^ 2 =
      (t - s) * (s ^ 2 * t + 2 * s ^ 2 + s * t ^ 2 + 4 * s * t + 4 * s +
        2 * t ^ 2 + 4 * t + 2) := by
    ring
  have hpos : 0 < s ^ 2 * t + 2 * s ^ 2 + s * t ^ 2 + 4 * s * t + 4 * s +
      2 * t ^ 2 + 4 * t + 2 := by
    positivity
  have hdiff : 0 ≤ (2 + s) * t * (1 + t) ^ 2 - (2 + t) * s * (1 + s) ^ 2 := by
    rw [hfac]
    exact mul_nonneg (sub_nonneg.mpr hst) (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

private theorem invSqrt_ratio {w : ℝ} (hw : w < 1) (hw0 : w ≠ 0) :
    (1 / Real.sqrt (1 - w) - 1 - w / 2) / w ^ 2 =
      (2 + Real.sqrt (1 - w)) /
        (2 * Real.sqrt (1 - w) * (1 + Real.sqrt (1 - w)) ^ 2) := by
  set s : ℝ := Real.sqrt (1 - w)
  have hs0 : 0 < 1 - w := sub_pos.mpr hw
  have hs : 0 < s := Real.sqrt_pos.mpr hs0
  have hsq : s ^ 2 = 1 - w := Real.sq_sqrt hs0.le
  have hw' : w = 1 - s ^ 2 := by linarith
  have hnum : 2 - 2 * s - w * s = (1 - s) ^ 2 * (2 + s) := by
    rw [hw']
    ring
  have hleft : 1 / s - 1 - w / 2 = (2 - 2 * s - w * s) / (2 * s) := by
    field_simp [hs.ne']
  rw [hleft, hnum]
  have hsne : s ≠ 1 := by
    intro hs1
    apply hw0
    rw [hw', hs1]
    ring
  have hsub : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr hsne.symm
  have hw2 : w ^ 2 = (1 - s) ^ 2 * (1 + s) ^ 2 := by
    rw [hw']
    ring
  rw [hw2]
  field_simp [hs.ne', hsub]

private theorem invSqrt_quadratic {w lam : ℝ} (_hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hw : |w| ≤ lam) :
    1 / Real.sqrt (1 - w) ≤
      1 + w / 2 +
        ((2 + Real.sqrt (1 - lam)) /
          (2 * Real.sqrt (1 - lam) * (1 + Real.sqrt (1 - lam)) ^ 2)) * w ^ 2 := by
  have hw_le : w ≤ lam := (abs_le.mp hw).2
  have hw1 : w < 1 := lt_of_le_of_lt hw_le hlam1
  have h1w : 0 < 1 - w := sub_pos.mpr hw1
  set s : ℝ := Real.sqrt (1 - lam)
  have hspos : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr hlam1)
  by_cases hw0 : w = 0
  · simp [hw0, Real.sqrt_one]
  · have hratio := invSqrt_ratio hw1 hw0
    have hsw : s ≤ Real.sqrt (1 - w) := Real.sqrt_le_sqrt (by linarith)
    have hK := kRatio_antitone hspos (Real.sqrt_pos.mpr h1w) hsw
    have hK2 : (2 + Real.sqrt (1 - w)) /
          (2 * Real.sqrt (1 - w) * (1 + Real.sqrt (1 - w)) ^ 2) ≤
        (2 + s) / (2 * s * (1 + s) ^ 2) := by
      have hdiv := div_le_div_of_nonneg_right hK (by norm_num : (0 : ℝ) ≤ 2)
      have hrew : (2 + Real.sqrt (1 - w)) /
            (2 * Real.sqrt (1 - w) * (1 + Real.sqrt (1 - w)) ^ 2) =
          ((2 + Real.sqrt (1 - w)) /
            (Real.sqrt (1 - w) * (1 + Real.sqrt (1 - w)) ^ 2)) / 2 := by
        field_simp
      have hrews : (2 + s) / (2 * s * (1 + s) ^ 2) =
          ((2 + s) / (s * (1 + s) ^ 2)) / 2 := by
        field_simp
      rw [hrew, hrews]
      exact hdiv
    have hle : (1 / Real.sqrt (1 - w) - 1 - w / 2) / w ^ 2 ≤
        (2 + s) / (2 * s * (1 + s) ^ 2) := by
      rw [hratio]
      exact hK2
    have hw2 : 0 < w ^ 2 := sq_pos_of_ne_zero hw0
    have hmul := mul_le_mul_of_nonneg_right hle hw2.le
    have hcancel : (1 / Real.sqrt (1 - w) - 1 - w / 2) / w ^ 2 * w ^ 2 =
        1 / Real.sqrt (1 - w) - 1 - w / 2 := by
      field_simp [hw0]
    linarith

private theorem sqrt_two_gt_three_div_four :
    (3 : ℝ) < 4 * Real.sqrt 2 := by
  have hsq : (3 : ℝ) ^ 2 < (4 * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have habs := (sq_lt_sq).mp hsq
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt 2)] at habs
  exact habs

private theorem thirteen_sqrt_two_gt_three :
    (3 : ℝ) < 13 * Real.sqrt 2 := by
  have hsq : (3 : ℝ) ^ 2 < (13 * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have habs := (sq_lt_sq).mp hsq
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 13 * Real.sqrt 2)] at habs
  exact habs

private theorem form_gap {z r : ℝ} (hr : r ^ 2 = 4 * z ^ 2 - 1) :
    (r + 2 * Real.sqrt 3 * z) * (1 + z) ^ 2 -
        6 * r * z * (r + Real.sqrt 3 * z) ^ 2 =
      Real.sqrt 3 * (2 * z * (-24 * z ^ 3 + z ^ 2 + 8 * z + 1)) -
        r * (42 * z ^ 3 - z ^ 2 - 8 * z - 1) := by
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination
    (-6 * r * z - 12 * Real.sqrt 3 * z ^ 2) * hr +
      (-6 * r * z ^ 3) * hs3

private theorem returnFactor_lt {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    (1 / Real.sqrt (1 - x)) *
        (1 + ((2 + Real.sqrt (1 - (x / 3) / (1 - x))) /
            (2 * Real.sqrt (1 - (x / 3) / (1 - x)) *
              (1 + Real.sqrt (1 - (x / 3) / (1 - x))) ^ 2)) *
          ((x / 3) / (1 - x)) ^ 2 / 2) <
      (2 - x) / (2 * (1 - x)) := by
  set z : ℝ := Real.sqrt (1 - x)
  have hx1' : x < 1 := lt_of_le_of_lt hx1 (by norm_num)
  have hzsq : z ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  have hz0 : 0 < z := Real.sqrt_pos.mpr (by linarith)
  have hz1 : z < 1 := by
    have : z < Real.sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by linarith : 1 - x < 1)
    simpa using this
  have hz0le : Real.sqrt 2 / 2 ≤ z := by
    have hle : 1 / 2 ≤ 1 - x := by linarith
    have hsqrt := Real.sqrt_le_sqrt hle
    have hhalf : Real.sqrt ((1 : ℝ) / 2) = Real.sqrt 2 / 2 := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) 2, Real.sqrt_one]
      rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
      rw [div_mul_eq_mul_div, one_mul]
      rw [div_eq_iff (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
      rw [← sq]
      exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm
    rw [hhalf] at hsqrt
    change Real.sqrt 2 / 2 ≤ z at hsqrt
    exact hsqrt
  have hz2 : 1 / 2 ≤ z ^ 2 := by
    have := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2) hz0le
    have hsq0 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    linarith
  set r : ℝ := Real.sqrt (4 * z ^ 2 - 1)
  have hr0 : 0 < 4 * z ^ 2 - 1 := by nlinarith
  have hrpos : 0 < r := Real.sqrt_pos.mpr hr0
  have hr2 : r ^ 2 = 4 * z ^ 2 - 1 := Real.sq_sqrt hr0.le
  have hf : -24 * z ^ 3 + z ^ 2 + 8 * z + 1 < 0 := by
    have hupper : -24 * z ^ 3 + z ^ 2 + 8 * z + 1 ≤ z ^ 2 - 4 * z + 1 := by
      nlinarith [hz2]
    have hleft : z ^ 2 - 4 * z + 1 ≤ (Real.sqrt 2 / 2) ^ 2 - 4 * (Real.sqrt 2 / 2) + 1 := by
      have hdiff : z ^ 2 - 4 * z - ((Real.sqrt 2 / 2) ^ 2 - 4 * (Real.sqrt 2 / 2)) =
          (z - Real.sqrt 2 / 2) * (z + Real.sqrt 2 / 2 - 4) := by ring
      have hnonpos : z ^ 2 - 4 * z - ((Real.sqrt 2 / 2) ^ 2 - 4 * (Real.sqrt 2 / 2)) ≤ 0 := by
        rw [hdiff]
        have h1 : 0 ≤ z - Real.sqrt 2 / 2 := by linarith
        have h2 : z + Real.sqrt 2 / 2 - 4 ≤ 0 := by
          have hzle : z ≤ 1 := hz1.le
          have hz0le' : Real.sqrt 2 / 2 ≤ 1 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
          linarith
        nlinarith
      linarith
    have hneg : (Real.sqrt 2 / 2) ^ 2 - 4 * (Real.sqrt 2 / 2) + 1 < 0 := by
      have : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      linarith [sqrt_two_gt_three_div_four]
    linarith
  have hg : 0 < 42 * z ^ 3 - z ^ 2 - 8 * z - 1 := by
    have hlower : -z ^ 2 + 13 * z - 1 ≤ 42 * z ^ 3 - z ^ 2 - 8 * z - 1 := by
      nlinarith [hz2]
    have hbase : 0 < -(Real.sqrt 2 / 2) ^ 2 + 13 * (Real.sqrt 2 / 2) - 1 := by
      have : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      linarith [thirteen_sqrt_two_gt_three]
    have hinc : -(Real.sqrt 2 / 2) ^ 2 + 13 * (Real.sqrt 2 / 2) - 1 ≤ -z ^ 2 + 13 * z - 1 := by
      have hdiff : (-z ^ 2 + 13 * z) - (-(Real.sqrt 2 / 2) ^ 2 + 13 * (Real.sqrt 2 / 2)) =
          (z - Real.sqrt 2 / 2) * (13 - (z + Real.sqrt 2 / 2)) := by ring
      have hnonneg : 0 ≤ (z - Real.sqrt 2 / 2) * (13 - (z + Real.sqrt 2 / 2)) := by
        have h1 : 0 ≤ z - Real.sqrt 2 / 2 := by linarith
        have h2 : 0 ≤ 13 - (z + Real.sqrt 2 / 2) := by
          have hzle : z ≤ 1 := hz1.le
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        nlinarith
      linarith
    linarith
  have hform : (r + 2 * Real.sqrt 3 * z) * (1 + z) ^ 2 <
      6 * r * z * (r + Real.sqrt 3 * z) ^ 2 := by
    have hgap := form_gap hr2
    have hleft : Real.sqrt 3 * (2 * z * (-24 * z ^ 3 + z ^ 2 + 8 * z + 1)) -
        r * (42 * z ^ 3 - z ^ 2 - 8 * z - 1) < 0 := by
      have hL : Real.sqrt 3 * (2 * z * (-24 * z ^ 3 + z ^ 2 + 8 * z + 1)) < 0 := by
        have : -24 * z ^ 3 + z ^ 2 + 8 * z + 1 < 0 := hf
        have : 0 < Real.sqrt 3 * (2 * z) := by positivity
        nlinarith
      have hR : 0 < r * (42 * z ^ 3 - z ^ 2 - 8 * z - 1) := by positivity
      linarith
    linarith
  set s : ℝ := r / (z * Real.sqrt 3)
  have hspos : 0 < s := by positivity
  have hsdef : r = s * z * Real.sqrt 3 := by
    dsimp [s]
    field_simp [hz0.ne', Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3) |>.ne']
  have hlameq : (1 - z ^ 2) / (3 * z ^ 2) = (x / 3) / (1 - x) := by
    rw [hzsq]
    field_simp
    ring
  have hs2 : s ^ 2 = 1 - (x / 3) / (1 - x) := by
    have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    calc s ^ 2 = r ^ 2 / (z * Real.sqrt 3) ^ 2 := by
          dsimp [s]
          exact div_pow _ _ 2
      _ = (4 * z ^ 2 - 1) / (z ^ 2 * 3) := by
          rw [hr2, mul_pow, h3]
      _ = 1 - (1 - z ^ 2) / (3 * z ^ 2) := by
          field_simp [hz0.ne']
          ring
      _ = 1 - (x / 3) / (1 - x) := by
          rw [hlameq]
  have hs_sqrt : s = Real.sqrt (1 - (x / 3) / (1 - x)) := by
    have hnonneg : 0 ≤ 1 - (x / 3) / (1 - x) := by
      rw [← hs2]
      exact sq_nonneg _
    exact ((Real.sqrt_eq_iff_eq_sq hnonneg hspos.le).mpr hs2.symm).symm
  have hcut : (2 + s) * (1 + z) ^ 2 < 18 * s * z ^ 3 * (1 + s) ^ 2 := by
    rw [hsdef] at hform
    have hL : s * z * Real.sqrt 3 + 2 * Real.sqrt 3 * z = Real.sqrt 3 * z * (s + 2) := by ring
    have hIn : s * z * Real.sqrt 3 + Real.sqrt 3 * z = Real.sqrt 3 * z * (s + 1) := by ring
    rw [hL, hIn] at hform
    have hsq : (Real.sqrt 3 * z * (s + 1)) ^ 2 = 3 * z ^ 2 * (s + 1) ^ 2 := by
      have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      calc (Real.sqrt 3 * z * (s + 1)) ^ 2
          = (Real.sqrt 3) ^ 2 * z ^ 2 * (s + 1) ^ 2 := by ring
        _ = 3 * z ^ 2 * (s + 1) ^ 2 := by rw [h3]
    rw [hsq] at hform
    have hc : 0 < Real.sqrt 3 * z := by positivity
    have hform'' : (Real.sqrt 3 * z) * ((s + 2) * (1 + z) ^ 2) <
        (Real.sqrt 3 * z) * (18 * s * z ^ 3 * (1 + s) ^ 2) := by
      convert hform using 1 <;> ring
    have hcancel := (mul_lt_mul_iff_of_pos_left hc).mp hform''
    simpa [add_comm s 2] using hcancel
  have hdiv : (2 + s) * (1 + z) ^ 2 / (9 * z ^ 3) < 2 * s * (1 + s) ^ 2 := by
    have hpos : 0 < 9 * z ^ 3 := by positivity
    have hcut' : (2 + s) * (1 + z) ^ 2 < 2 * s * (1 + s) ^ 2 * (9 * z ^ 3) := by
      convert hcut using 1
      ring
    exact (div_lt_iff₀ hpos).mpr hcut'
  have hmul : (2 + s) * (1 + z) ^ 2 * (1 - z) ^ 2 / (9 * z ^ 3) <
      2 * s * (1 + s) ^ 2 * (1 - z) ^ 2 := by
    have hne : (1 : ℝ) ≠ z := hz1.ne'
    have hpos : 0 < (1 - z) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have h := mul_lt_mul_of_pos_right hdiv hpos
    have heq : (2 + s) * (1 + z) ^ 2 * (1 - z) ^ 2 / (9 * z ^ 3) =
        ((2 + s) * (1 + z) ^ 2 / (9 * z ^ 3)) * (1 - z) ^ 2 := by
      field_simp
    exact heq.trans_lt h
  set lam : ℝ := (x / 3) / (1 - x)
  have hlampos : 0 < lam := by
    dsimp [lam]
    positivity
  have hleft : (2 + s) * lam ^ 2 * z =
      (2 + s) * (1 + z) ^ 2 * (1 - z) ^ 2 / (9 * z ^ 3) := by
    have hlam' : lam = (1 - z ^ 2) / (3 * z ^ 2) := by
      dsimp [lam]
      exact hlameq.symm
    rw [hlam']
    have hfac : (1 - z ^ 2) ^ 2 = (1 + z) ^ 2 * (1 - z) ^ 2 := by ring
    field_simp [hz0.ne']
    rw [hfac]
    ring
  have hcross : (2 + s) * lam ^ 2 * z < 2 * s * (1 + s) ^ 2 * (1 - z) ^ 2 := by
    rw [hleft]
    exact hmul
  have hextra : (2 + s) * lam ^ 2 / (4 * s * (1 + s) ^ 2) < (1 - z) ^ 2 / (2 * z) := by
    have hden : 0 < 4 * s * (1 + s) ^ 2 := by positivity
    have hden2 : 0 < 2 * z := by positivity
    rw [div_lt_div_iff₀ hden hden2]
    have h2 : (2 + s) * lam ^ 2 * (2 * z) < 4 * s * (1 + s) ^ 2 * (1 - z) ^ 2 := by
      nlinarith
    simpa [mul_assoc, mul_left_comm, mul_comm] using h2
  have hsum : 1 + (2 + s) * lam ^ 2 / (4 * s * (1 + s) ^ 2) < (2 - x) / (2 * z) := by
    have hrew : (2 - x) / (2 * z) = 1 + (1 - z) ^ 2 / (2 * z) := by
      have hx' : x = 1 - z ^ 2 := by linarith [hzsq]
      rw [hx']
      field_simp [hz0.ne']
      ring
    linarith
  have hK : (2 + Real.sqrt (1 - lam)) /
      (2 * Real.sqrt (1 - lam) * (1 + Real.sqrt (1 - lam)) ^ 2) =
      (2 + s) / (2 * s * (1 + s) ^ 2) := by
    have : Real.sqrt (1 - lam) = s := by
      have : lam = (x / 3) / (1 - x) := rfl
      rw [this, hs_sqrt]
    rw [this]
  have hscale : 0 < 1 / z := by positivity
  have hfinal := mul_lt_mul_of_pos_left hsum hscale
  have hgoalL : (1 / z) * (1 + (2 + s) * lam ^ 2 / (4 * s * (1 + s) ^ 2)) =
      (1 / Real.sqrt (1 - x)) *
        (1 + ((2 + Real.sqrt (1 - lam)) /
          (2 * Real.sqrt (1 - lam) * (1 + Real.sqrt (1 - lam)) ^ 2)) * lam ^ 2 / 2) := by
    rw [show z = Real.sqrt (1 - x) from rfl, hK]
    field_simp [hz0.ne', hspos.ne']
    ring
  have hgoalR : (1 / z) * ((2 - x) / (2 * z)) = (2 - x) / (2 * (1 - x)) := by
    have hx' : x = 1 - z ^ 2 := by linarith [hzsq]
    rw [hx']
    field_simp [hz0.ne']
    ring
  rw [hgoalL, hgoalR] at hfinal
  exact hfinal

theorem returnIntegrand_pos {M α β θ : ℝ} (hM : 0 < M) (hαβ : α < β)
    (hsum : 3 * M * (α + β) + M * (β - α) < 1) :
    0 < returnIntegrand M α β θ := by
  unfold returnIntegrand
  have hrad : 0 < 1 - 3 * M * (α + β) - M * (β - α) * Real.cos θ := by
    have hcos : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hMβ : 0 < M * (β - α) := by positivity
    have : M * (β - α) * Real.cos θ ≤ M * (β - α) := by
      nlinarith
    linarith
  positivity

theorem returnIntegrand_continuous {M α β : ℝ}
    (hrad : ∀ θ, 0 < 1 - 3 * M * (α + β) - M * (β - α) * Real.cos θ) :
    Continuous (returnIntegrand M α β) := by
  unfold returnIntegrand
  refine Continuous.div continuous_const ?_ ?_
  · refine Real.continuous_sqrt.comp ?_
    refine Continuous.sub continuous_const ?_
    exact Continuous.mul continuous_const Real.continuous_cos
  · intro θ
    exact (Real.sqrt_pos.mpr (hrad θ)).ne'

private theorem integral_affine_cos {A B : ℝ} :
    ∫ θ in (0 : ℝ)..Real.pi, (A + B * Real.cos θ) = A * Real.pi := by
  have hcont : Continuous (fun θ : ℝ => B * Real.cos θ) := by fun_prop
  rw [intervalIntegral.integral_add intervalIntegrable_const (hcont.intervalIntegrable 0 Real.pi)]
  simp [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  ring

private theorem integral_quad_cos {A B C : ℝ} :
    ∫ θ in (0 : ℝ)..Real.pi, (A + B * Real.cos θ + C * Real.cos θ ^ 2) =
      A * Real.pi + C * Real.pi / 2 := by
  have hsplit : (fun θ : ℝ => A + B * Real.cos θ + C * Real.cos θ ^ 2) =
      fun θ => (A + B * Real.cos θ) + C * Real.cos θ ^ 2 := by
    ext θ
    ring
  have h1 : Continuous (fun θ : ℝ => A + B * Real.cos θ) := by fun_prop
  have h2 : Continuous (fun θ : ℝ => C * Real.cos θ ^ 2) := by fun_prop
  rw [hsplit, intervalIntegral.integral_add (h1.intervalIntegrable 0 Real.pi)
    (h2.intervalIntegrable 0 Real.pi), integral_affine_cos]
  rw [intervalIntegral.integral_const_mul, integral_cos_sq_zero_pi]
  ring

private theorem integral_inv_sqrt_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    Real.pi / Real.sqrt a < ∫ θ in (0 : ℝ)..Real.pi, (1 / Real.sqrt (a - b * Real.cos θ)) := by
  have hrad : ∀ θ, 0 < a - b * Real.cos θ := by
    intro θ
    have : b * Real.cos θ ≤ b := by nlinarith [Real.cos_le_one θ, hb.le]
    linarith
  let tangent : ℝ → ℝ := fun θ =>
    1 / Real.sqrt a + (b / (2 * a * Real.sqrt a)) * Real.cos θ
  let full : ℝ → ℝ := fun θ => 1 / Real.sqrt (a - b * Real.cos θ)
  have hle : ∀ θ, tangent θ ≤ full θ := by
    intro θ
    have ht : 0 < a - b * Real.cos θ := hrad θ
    have htan := inv_sqrt_tangent ht ha
    have hrew : 1 / Real.sqrt a -
        ((a - b * Real.cos θ) - a) / (2 * a * Real.sqrt a) = tangent θ := by
      unfold tangent
      field_simp [ha.ne', (Real.sqrt_pos.mpr ha).ne']
      ring
    linarith
  have hlt0 : tangent 0 < full 0 := by
    have hgap := inv_sqrt_gap (by linarith : 0 < a - b) ha
    have hsne : Real.sqrt (a - b) ≠ Real.sqrt a := by
      intro hsr
      have hsq := congrArg (fun t : ℝ => t ^ 2) hsr
      rw [Real.sq_sqrt (by linarith), Real.sq_sqrt ha.le] at hsq
      linarith
    have hpos : 0 < (Real.sqrt a - Real.sqrt (a - b)) ^ 2 *
        (2 * Real.sqrt a + Real.sqrt (a - b)) /
          (2 * Real.sqrt (a - b) * (Real.sqrt a) ^ 3) := by
      have hsub : Real.sqrt a - Real.sqrt (a - b) ≠ 0 := sub_ne_zero.mpr hsne.symm
      positivity
    have hrew : 1 / Real.sqrt a - ((a - b) - a) / (2 * a * Real.sqrt a) = tangent 0 := by
      unfold tangent
      simp [Real.cos_zero]
      field_simp [ha.ne', (Real.sqrt_pos.mpr ha).ne']
      ring
    have hfull : full 0 = 1 / Real.sqrt (a - b) := by
      unfold full
      simp [Real.cos_zero]
    linarith
  have hcontT : ContinuousOn tangent (Icc (0 : ℝ) Real.pi) := by
    unfold tangent
    exact (continuous_const.add (continuous_const.mul Real.continuous_cos)).continuousOn
  have hcontF : ContinuousOn full (Icc (0 : ℝ) Real.pi) := by
    unfold full
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact Real.continuous_sqrt.comp_continuousOn
        (continuous_const.sub (continuous_const.mul Real.continuous_cos)).continuousOn
    · intro θ _
      exact (Real.sqrt_pos.mpr (hrad θ)).ne'
  have hlt := integral_lt_integral_of_continuousOn_of_le_of_exists_lt Real.pi_pos hcontT hcontF
    (fun θ _ => hle θ) ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, hlt0⟩
  have htanI : ∫ θ in (0 : ℝ)..Real.pi, tangent θ = Real.pi / Real.sqrt a := by
    unfold tangent
    have h := integral_affine_cos (A := 1 / Real.sqrt a) (B := b / (2 * a * Real.sqrt a))
    rw [h]
    field_simp [(Real.sqrt_pos.mpr ha).ne']
  linarith


theorem bound_return_gt_resonant {M α β γ : ℝ} (hM : 0 < M) (hα : 0 ≤ α) (hαβ : α < β)
    (hβγ : β < γ) (hsum : α + β + γ = 1 / (2 * M)) :
    let p := 2 / (α + β)
    2 * Real.pi / Real.sqrt (1 - 6 * M / p) < radialReturn M α β ∧
      6 * Real.pi * M / p < radialReturn M α β - 2 * Real.pi := by
  dsimp
  set p : ℝ := 2 / (α + β)
  set x : ℝ := 3 * M * (α + β)
  have hs : 0 < α + β := by linarith
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hx : x = 6 * M / p := by
    dsimp [x, p]
    field_simp [hM.ne', hs.ne']
    ring
  have hx1 : x < 1 := by
    have := turning_sum_lt_one hM hαβ hβγ hsum
    simpa [x] using this
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have ha : 0 < 1 - x := by linarith
  have hb : 0 < M * (β - α) := by positivity
  have hba : M * (β - α) < 1 - x := by
    have hγ : γ = 1 / (2 * M) - α - β := by linarith
    have hpos : 0 < 2 * M * (γ - β) := by positivity
    have heq : 1 - x - M * (β - α) = 2 * M * (γ - β) := by
      dsimp [x]
      rw [hγ]
      field_simp [hM.ne']
      ring
    linarith
  have hlow := integral_inv_sqrt_lower ha hb hba
  have hret : radialReturn M α β =
      2 * ∫ θ in (0 : ℝ)..Real.pi,
        (1 / Real.sqrt ((1 - x) - M * (β - α) * Real.cos θ)) := by
    unfold radialReturn returnIntegrand
    apply congr_arg (fun I => 2 * I)
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [x]
  have hcmp : 2 * Real.pi / Real.sqrt (1 - x) < radialReturn M α β := by
    rw [hret]
    have := mul_lt_mul_of_pos_left hlow (by norm_num : (0 : ℝ) < 2)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hx0' : 0 < 6 * M / p := by simpa [hx] using hx0
  have hx1' : 6 * M / p < 1 := by simpa [hx] using hx1
  let L : ℝ := Real.sqrt (p * M)
  have hL : L ≠ 0 := by
    dsimp [L]
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hMne : M ≠ 0 := hM.ne'
  have hpL : p = L ^ 2 / M := by
    dsimp [L]
    rw [Real.sq_sqrt (by positivity)]
    field_simp [hMne]
  have hellipse := perihelion_excess_latus (M := M) (L := L) (p := p) hMne hpL hx0' hx1'
  have hk : Real.sqrt (1 - 6 * M / p) = Real.sqrt (1 - x) := by rw [hx]
  constructor
  · simpa [hk] using hcmp
  · have hperiod : 2 * Real.pi * (1 / Real.sqrt (1 - x) - 1) <
        radialReturn M α β - 2 * Real.pi := by
      have : 2 * Real.pi / Real.sqrt (1 - x) - 2 * Real.pi <
          radialReturn M α β - 2 * Real.pi := by linarith
      have hrew : 2 * Real.pi / Real.sqrt (1 - x) - 2 * Real.pi =
          2 * Real.pi * (1 / Real.sqrt (1 - x) - 1) := by
        field_simp [(Real.sqrt_pos.mpr ha).ne']
      linarith
    have hlowE : 6 * Real.pi * M / p <
        2 * Real.pi * (1 / Real.sqrt (1 - x) - 1) := by
      simpa [hk] using hellipse.1
    exact lt_trans hlowE hperiod

theorem bound_return_gt_angular {M L α β γ : ℝ} (hM : 0 < M) (hα : 0 ≤ α)
    (hαβ : α < β) (hβγ : β < γ) (hsum : α + β + γ = 1 / (2 * M))
    (hσ : α * β + β * γ + γ * α = 1 / L ^ 2) :
    6 * Real.pi * M ^ 2 / L ^ 2 < radialReturn M α β - 2 * Real.pi := by
  have hlow := (bound_return_gt_resonant hM hα hαβ hβγ hsum).2
  set p : ℝ := 2 / (α + β)
  have hs : 0 < α + β := by linarith
  have hp : 0 < p := by
    dsimp [p]
    exact div_pos (by norm_num) hs
  have hrect : p < L ^ 2 / M := by
    simpa [p] using angularLatus_gt_turning hM hα hαβ hβγ hsum hσ
  have hden : 0 < L ^ 2 / M := lt_trans hp hrect
  have hinv : M / L ^ 2 < 1 / p := by
    have hrew : M / L ^ 2 = 1 / (L ^ 2 / M) := by field_simp [hM.ne']
    rw [hrew]
    exact (one_div_lt_one_div hden hp).mpr hrect
  have hfrac : M ^ 2 / L ^ 2 < M / p := by
    have hmul := mul_lt_mul_of_pos_left hinv hM
    convert hmul using 1
    · field_simp [hM.ne']
    · field_simp [hM.ne', hp.ne']
  have hcoef : 6 * Real.pi * (M ^ 2 / L ^ 2) < 6 * Real.pi * (M / p) :=
    mul_lt_mul_of_pos_left hfrac (by positivity : 0 < 6 * Real.pi)
  have hcoef' : 6 * Real.pi * M ^ 2 / L ^ 2 < 6 * Real.pi * M / p := by
    convert hcoef using 1 <;> ring
  exact lt_trans hcoef' hlow

private theorem integral_inv_sqrt_envelope {a b lam : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hblam : b ≤ a * lam) :
    ∫ θ in (0 : ℝ)..Real.pi, (1 / Real.sqrt (a - b * Real.cos θ)) ≤
      (Real.pi / Real.sqrt a) * (1 +
        ((2 + Real.sqrt (1 - lam)) /
          (2 * Real.sqrt (1 - lam) * (1 + Real.sqrt (1 - lam)) ^ 2)) * lam ^ 2 / 2) := by
  let K : ℝ := (2 + Real.sqrt (1 - lam)) /
    (2 * Real.sqrt (1 - lam) * (1 + Real.sqrt (1 - lam)) ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hba : b < a := by
    have hmul : a * lam < a * 1 := mul_lt_mul_of_pos_left hlam1 ha
    have : a * lam < a := by simpa using hmul
    linarith
  have hrad : ∀ θ, 0 < a - b * Real.cos θ := by
    intro θ
    have : b * Real.cos θ ≤ b := by nlinarith [Real.cos_le_one θ, hb]
    linarith
  have hpoint : ∀ θ, 1 / Real.sqrt (a - b * Real.cos θ) ≤
      (1 / Real.sqrt a) * (1 + ((b / a) * Real.cos θ) / 2 +
        K * ((b / a) * Real.cos θ) ^ 2) := by
    intro θ
    have hdiv : 0 ≤ b / a := div_nonneg hb ha.le
    have hble : b / a ≤ lam := by
      have hmul : b ≤ lam * a := by simpa [mul_comm] using hblam
      exact (div_le_iff₀ ha).mpr hmul
    have hw : |(b / a) * Real.cos θ| ≤ lam := by
      rw [abs_mul, abs_of_nonneg hdiv]
      nlinarith [Real.abs_cos_le_one θ, hble]
    have hquad := invSqrt_quadratic hlam0 hlam1 hw
    have hsplit : a - b * Real.cos θ = a * (1 - (b / a) * Real.cos θ) := by
      field_simp [ha.ne']
    have hposw : 0 < 1 - (b / a) * Real.cos θ :=
      sub_pos.mpr (lt_of_abs_lt (lt_of_le_of_lt hw hlam1))
    rw [hsplit, Real.sqrt_mul ha.le]
    have hsqrt_a : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    have hsqrt_w : 0 < Real.sqrt (1 - (b / a) * Real.cos θ) := Real.sqrt_pos.mpr hposw
    have hleft : 1 / (Real.sqrt a * Real.sqrt (1 - (b / a) * Real.cos θ)) =
        (1 / Real.sqrt a) * (1 / Real.sqrt (1 - (b / a) * Real.cos θ)) := by
      field_simp [hsqrt_a.ne', hsqrt_w.ne']
    rw [hleft]
    exact mul_le_mul_of_nonneg_left (by simpa [K] using hquad) (by positivity)
  let rhs : ℝ → ℝ := fun θ =>
    (1 / Real.sqrt a) * (1 + ((b / a) * Real.cos θ) / 2 + K * ((b / a) * Real.cos θ) ^ 2)
  have hcontL : ContinuousOn (fun θ : ℝ => 1 / Real.sqrt (a - b * Real.cos θ))
      (Icc (0 : ℝ) Real.pi) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact Real.continuous_sqrt.comp_continuousOn
        (continuous_const.sub (continuous_const.mul Real.continuous_cos)).continuousOn
    · intro θ _
      exact (Real.sqrt_pos.mpr (hrad θ)).ne'
  have hcontR : ContinuousOn rhs (Icc (0 : ℝ) Real.pi) := by
    unfold rhs
    fun_prop
  have hmono := integral_mono_on (μ := volume) Real.pi_pos.le
    (hcontL.intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le)
    (hcontR.intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le)
    (fun θ _ => hpoint θ)
  have hpoly : (fun θ : ℝ => rhs θ) = fun θ =>
      (1 / Real.sqrt a) +
        ((1 / Real.sqrt a) * ((b / a) / 2)) * Real.cos θ +
        ((1 / Real.sqrt a) * K * (b / a) ^ 2) * Real.cos θ ^ 2 := by
    ext θ
    unfold rhs
    ring
  have hright : ∫ θ in (0 : ℝ)..Real.pi, rhs θ =
      (Real.pi / Real.sqrt a) * (1 + K * (b / a) ^ 2 / 2) := by
    rw [hpoly, integral_quad_cos]
    field_simp [(Real.sqrt_pos.mpr ha).ne']
  have hsq : (b / a) ^ 2 ≤ lam ^ 2 := by
    have hble : b / a ≤ lam := by
      have hmul : b ≤ lam * a := by simpa [mul_comm] using hblam
      exact (div_le_iff₀ ha).mpr hmul
    have hnonneg : 0 ≤ b / a := div_nonneg hb ha.le
    nlinarith
  have hstep1 : ∫ θ in (0 : ℝ)..Real.pi, 1 / Real.sqrt (a - b * Real.cos θ) ≤
      (Real.pi / Real.sqrt a) * (1 + K * (b / a) ^ 2 / 2) := by
    rw [← hright]
    simpa [rhs] using hmono
  have hstep2 : (Real.pi / Real.sqrt a) * (1 + K * (b / a) ^ 2 / 2) ≤
      (Real.pi / Real.sqrt a) * (1 + K * lam ^ 2 / 2) := by
    have hpi : 0 < Real.pi / Real.sqrt a := by positivity
    exact mul_le_mul_of_nonneg_left (by nlinarith) hpi.le
  exact hstep1.trans hstep2


theorem bound_return_bounds {M α β γ : ℝ} (hM : 0 < M) (hα : 0 ≤ α) (hαβ : α < β)
    (hβγ : β < γ) (hsum : α + β + γ = 1 / (2 * M))
    (hx : 3 * M * (α + β) ≤ 1 / 2) :
    let p := 2 / (α + β)
    6 * Real.pi * M / p < radialReturn M α β - 2 * Real.pi ∧
      radialReturn M α β - 2 * Real.pi < (6 * Real.pi * M / p) / (1 - 6 * M / p) := by
  dsimp
  have hlow := (bound_return_gt_resonant hM hα hαβ hβγ hsum).2
  set p : ℝ := 2 / (α + β)
  set x : ℝ := 3 * M * (α + β)
  have hs : 0 < α + β := by linarith
  have hxeq : x = 6 * M / p := by
    dsimp [x, p]
    field_simp [hM.ne', hs.ne']
    ring
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have ha : 0 < 1 - x := by linarith
  set ecc : ℝ := M * (β - α)
  set lam : ℝ := (x / 3) / (1 - x)
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    positivity
  have hlam1 : lam < 1 := by
    dsimp [lam]
    exact (div_lt_one ha).mpr (by linarith)
  have hecc : 0 ≤ ecc := by
    dsimp [ecc]
    positivity
  have hblam : ecc ≤ (1 - x) * lam := by
    dsimp [ecc, lam, x]
    have : M * (β - α) ≤ M * (α + β) := by nlinarith [hα]
    have hx3 : x / 3 = M * (α + β) := by
      dsimp [x]
      ring
    calc M * (β - α) ≤ M * (α + β) := this
      _ = x / 3 := hx3.symm
      _ = (1 - x) * ((x / 3) / (1 - x)) := by field_simp [ha.ne']
  have henv := integral_inv_sqrt_envelope (a := 1 - x) (b := ecc) (lam := lam)
    ha hecc hlam0 hlam1 hblam
  have hhalf : ∫ θ in (0 : ℝ)..Real.pi, returnIntegrand M α β θ ≤
      (Real.pi / Real.sqrt (1 - x)) * (1 +
        ((2 + Real.sqrt (1 - lam)) /
          (2 * Real.sqrt (1 - lam) * (1 + Real.sqrt (1 - lam)) ^ 2)) * lam ^ 2 / 2) := by
    have hcongr : ∫ θ in (0 : ℝ)..Real.pi, returnIntegrand M α β θ =
        ∫ θ in (0 : ℝ)..Real.pi, 1 / Real.sqrt ((1 - x) - ecc * Real.cos θ) := by
      refine intervalIntegral.integral_congr ?_
      intro θ _
      unfold returnIntegrand
      congr 1
    rw [hcongr]
    simpa [lam] using henv
  have hfac := returnFactor_lt hx0 hx
  have hstrict : 2 * ∫ θ in (0 : ℝ)..Real.pi, returnIntegrand M α β θ <
      Real.pi * (2 - x) / (1 - x) := by
    have htwo : (0 : ℝ) < 2 := by norm_num
    have hmul := mul_lt_mul_of_pos_left hfac (mul_pos (by exact Real.pi_pos) htwo)
    have hrew : 2 * Real.pi * ((1 / Real.sqrt (1 - x)) *
        (1 + ((2 + Real.sqrt (1 - (x / 3) / (1 - x))) /
          (2 * Real.sqrt (1 - (x / 3) / (1 - x)) *
            (1 + Real.sqrt (1 - (x / 3) / (1 - x))) ^ 2)) *
          ((x / 3) / (1 - x)) ^ 2 / 2)) =
        2 * ((Real.pi / Real.sqrt (1 - x)) * (1 +
          ((2 + Real.sqrt (1 - lam)) /
            (2 * Real.sqrt (1 - lam) * (1 + Real.sqrt (1 - lam)) ^ 2)) * lam ^ 2 / 2)) := by
      dsimp [lam]
      field_simp [(Real.sqrt_pos.mpr ha).ne']
    have htarget : 2 * Real.pi * ((2 - x) / (2 * (1 - x))) = Real.pi * (2 - x) / (1 - x) := by
      field_simp [ha.ne']
    have hle : 2 * ∫ θ in (0 : ℝ)..Real.pi, returnIntegrand M α β θ ≤
        2 * ((Real.pi / Real.sqrt (1 - x)) * (1 +
          ((2 + Real.sqrt (1 - lam)) /
            (2 * Real.sqrt (1 - lam) * (1 + Real.sqrt (1 - lam)) ^ 2)) * lam ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hhalf (by norm_num)
    linarith
  have hupper : radialReturn M α β - 2 * Real.pi < (6 * Real.pi * M / p) / (1 - 6 * M / p) := by
    have hret : radialReturn M α β = 2 * ∫ θ in (0 : ℝ)..Real.pi, returnIntegrand M α β θ := rfl
    have hcap : Real.pi * (2 - x) / (1 - x) - 2 * Real.pi = Real.pi * x / (1 - x) := by
      have hne : (1 - x) ≠ 0 := ha.ne'
      calc Real.pi * (2 - x) / (1 - x) - 2 * Real.pi
          = Real.pi * ((2 - x) / (1 - x) - 2) := by ring
        _ = Real.pi * ((2 - x - 2 * (1 - x)) / (1 - x)) := by
            congr 1
            field_simp [hne]
        _ = Real.pi * (x / (1 - x)) := by
            congr 1
            have : 2 - x - 2 * (1 - x) = x := by ring
            rw [this]
        _ = Real.pi * x / (1 - x) := by ring
    have hpx : Real.pi * x / (1 - x) = (6 * Real.pi * M / p) / (1 - 6 * M / p) := by
      rw [hxeq]
      field_simp [ha.ne']
    linarith
  exact ⟨hlow, hupper⟩

end DstDiophantine.Gravity.Perihelion
