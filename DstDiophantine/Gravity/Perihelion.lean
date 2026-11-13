import DstDiophantine.Gravity.RadialFall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Perihelion from the radial law with angular momentum

The radial fall has no perihelion: every share of the advance is proportional
to `L²`. On the same static coframe the equatorial motion keeps
`L = r² dφ/dτ`, and the static observer measures
`γ² = 1 + ûr² + (L/r)²`, with `dr/dτ = √A · ûr`.

The rapidity law is the radial one with this `γ²` in place of `cosh² ψ`,
plus the centrifugal change of a constant `L` along the angular leg,
`dûr/dτ = −γ²/ℓ + (√A / r) (L/r)²`.
At `L = 0` and `ûr = sinh ψ` this is `dψ/dτ = −cosh ψ / ℓ`.

## Proved

* Differentiating `√A · ûr` cancels the radial speed and leaves
  `d²r/dτ² = −κ + L²/r³ − 3 κ L²/r²`.
* The correction splits with nothing left over: one share `−κ L²/r²` is the
  transverse speed inside `γ²`, and two shares `−2 κ L²/r²` are the deficit
  `A − 1 = −rₛ/r` in the centrifugal barrier `A L²/r³`.
* `E = √A · γ` has vanishing derivative, and
  `(dr/dτ)² = E² − A(1 + L²/r²)`.
* Wherever `du/dφ ≠ 0`, `d²u/dφ² + u = rₛ/(2L²) + (3/2) rₛ u²`.
* The precessing ellipse `u = (M/L²)(1 + e cos(kφ))` cancels the resonant
  harmonic exactly when `k² = 1 − 6 M²/L²`. The residual is a constant and a
  double angle. With `0 < 6 M²/L² < 1`, the excess of one radial period over
  `2π` lies strictly between `6π M²/L²` and that quantity divided by
  `1 − 6 M²/L²`.
* In the areal acceleration the radial piece of `γ²` cancels against itself,
  `κ ûr² − κ γ² = −κ(1 + ûφ²)`, and the transverse piece remains.
* A tangential rate `−κ ûφ` has power `−κ ûφ²`. At constant `κ > 0` an angular
  momentum `L₀ exp(−κτ)` is strictly smaller at every later time. On the
  virial circle `ûφ² = κ r` its logarithmic derivative per radian is `−ûφ`.
* The torsional angular leg changes only with the radius, and its power
  vanishes whenever the radial velocity does.

## Not claimed

* A covariant transport of the full Killing bivector along a general curve.
* That the precessing ellipse solves the orbit equation. The residual is
  stated, and it has no resonant harmonic.
* That the tangential tilt is the retarded field of a moving source. It is
  the comparison against which the torsional leg is read. No arcseconds
  per century are computed.
* An identification of this bivector with the torsional mismatch of the
  parent theory.
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

/-- Rate of the orthonormal radial momentum. The first term is the rapidity
law; the second is the centrifugal change along the angular leg. -/
noncomputable def radialMomentumRate (rs r ur L : ℝ) : ℝ :=
  -(gammaSq ur (angularMomentum L r)) / axisDistance rs r +
    (killingNorm rs r / r) * (angularMomentum L r) ^ 2

/-- Squared energy `E² = A γ²`. -/
noncomputable def orbitEnergySq (rs L r ur : ℝ) : ℝ :=
  killingNorm rs r ^ 2 * gammaSq ur (angularMomentum L r)

theorem gammaSq_zero_angular (ur : ℝ) : gammaSq ur 0 = 1 + ur ^ 2 := by
  simp [gammaSq]

/-- At vanishing angular momentum the momentum rate is `−cosh² ψ / ℓ`,
which is `cosh ψ` times the radial law `dψ/dτ = −cosh ψ / ℓ`. -/
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

/-- Algebraic acceleration produced by the redshift transport and the
momentum rate. -/
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

/-- One share from `γ²`, two shares from `A − 1`. Their sum is the perihelion
term `−3 κ L²/r²`. -/
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

/-- Newtonian pieces plus the two shares recover the areal acceleration. -/
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

/-- Redshift and the full factor `γ²` trade exactly, so `E²` is stationary. -/
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

/-- Where the two laws hold, the areal acceleration is the Newtonian
acceleration plus the perihelion term. -/
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

/-- The first integral on an interval where the two laws hold. -/
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

/-- Differentiating the first integral removes every term but the Newtonian
inhomogeneity and `3 M u²`. -/
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

/-- Matching the coefficient of `cos θ` fixes `k² = 1 − 6 M²/L²`. -/
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

/-- On the rate that cancels the resonant harmonic, the failure of the orbit
equation is a constant plus a double angle. -/
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

/-! ### The advance per revolution -/

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

/-- One radial period of the precessing ellipse exceeds `2π` by an angle
strictly between `6π M²/L²` and that quantity over `1 − 6 M²/L²`. -/
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

/-- With semi-latus rectum `p = L²/M`, the same bracket is `6π M/p`. -/
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

/-- The radial piece of `γ²` cancels in the areal acceleration, and the
transverse piece remains. -/
theorem radial_speed_cancels {κ ur uφ : ℝ} :
    κ * ur ^ 2 - κ * gammaSq ur uφ = -κ * (1 + uφ ^ 2) := by
  unfold gammaSq
  ring

/-- After that cancellation, the transverse piece and the deficit in `A`
are the perihelion term. -/
theorem transverse_remains_perihelion {rs r L : ℝ} (hr : r ≠ 0) :
    -killingRate rs r * (1 + (L / r) ^ 2) + schwarzschildA rs r * L ^ 2 / r ^ 3 =
      -killingRate rs r + L ^ 2 / r ^ 3 - 3 * killingRate rs r * L ^ 2 / r ^ 2 := by
  unfold killingRate schwarzschildA
  field_simp [hr]
  ring

/-- Power of a tangential tilt `−κ ûφ`. -/
theorem aberration_power {κ uφ : ℝ} : (-κ * uφ) * uφ = -κ * uφ ^ 2 := by
  ring

theorem aberration_power_neg {κ uφ : ℝ} (hκ : 0 < κ) (hφ : uφ ≠ 0) :
    (-κ * uφ) * uφ < 0 := by
  rw [aberration_power]
  have hsq : 0 < uφ ^ 2 := sq_pos_of_ne_zero hφ
  nlinarith [hκ, hsq]

/-- At constant boost rate the tilted angular momentum is an exponential decay. -/
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

/-- On the virial circle `ûφ² = κ r`, the tilt changes `log|ûφ|` at the rate
`−ûφ` per radian. -/
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

/-- Power of the torsional angular leg `dûφ/dτ = −ûφ (√A ûr) / r`. -/
theorem torsional_angular_power {ν r ur uφ : ℝ} :
    uφ * (-(uφ * ν * ur) / r) = -(uφ ^ 2 * ν * ur) / r := by
  ring

theorem torsional_circular_power {ν r uφ : ℝ} :
    uφ * (-(uφ * ν * (0 : ℝ)) / r) = 0 := by
  ring

end DstDiophantine.Gravity.Perihelion
