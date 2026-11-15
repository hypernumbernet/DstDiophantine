import DstDiophantine.Gravity.CurvedTransport
import DstDiophantine.Gravity.Perihelion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Motion off the equatorial leg

On the exterior orthonormal frame the geodesic acceleration of a
four-velocity is the Levi-Civita contraction already recorded in
`CurvedTransport.exteriorConn`. The radial rate is the equatorial one,
with `(L/r)²` replaced by `ûθ² + ûφ²`. The rotation `cot θ / r` within
the tangent plane of the sphere appears in the two angular rates, with
opposite signs.

That rotation cancels in the derivative of `ûθ² + ûφ²`, so
`L² = r²(ûθ² + ûφ²)` is constant wherever `sin θ ≠ 0`. It cancels
against the derivative of `sin θ` in the azimuthal component, so
`r sin θ ûφ` is constant on the same set. It does not enter the radial
rate. The areal acceleration, the constancy of `E = √A γ`, and the first
integral are therefore the equatorial ones, read with this `L²`. An
angle that advances at `L/r²` carries the same slope as the Binet
residual, and the perihelion excess depends on the motion only through
this `L²`.

The two constants confine the colatitude:
`(r sin θ ûφ)² ≤ L² sin²θ`, with equality exactly at `ûθ = 0`. Wherever
`L² ≠ 0`, `sin²θ` is at least that ratio. A nonzero azimuthal constant
therefore stays a definite distance from both poles, and `cot θ / r`
remains finite along the motion. The polar leg carries the remainder
`ûθ² = (L² − (r sin θ ûφ)² / sin²θ) / r²`. On the edge the polar
acceleration is `(cot θ / r) ûφ²`. Positive cosine raises `θ` and
negative cosine lowers it, so each edge turns back toward the equator.
The edge is an orbit only where `cot θ = 0`. On the equator,
`cos θ = 0` and `ûθ = 0` kill the polar rate and return the torsional
azimuthal leg.

A vanishing azimuthal constant is a meridian. Off the poles it forces
`ûφ = 0`, and along such a motion `φ` stays fixed. Both angular
accelerations then lose `cot θ / r`. The polar leg changes by the
equatorial torsional law, the colatitude advances at `L/r²` with
`L = r ûθ`, and the radial acceleration is the equatorial one in this
`L`. None of these rates divides by `sin θ`, so the same expressions
stay finite at `θ = 0` and `θ = π`. The coordinate that degenerates
there is the azimuthal one.

A fixed colatitude occurs in two ways. Vanishing angular momentum kills
both legs, so neither the colatitude nor the azimuth advances, and the
motion is radial. Nonzero angular momentum keeps a colatitude fixed only
on the equator: the two constants are equal, the band collapses to
`sin²θ = 1`, and the polar leg remains zero, with the azimuthal rate the
torsional leg. Off the equator that leg does not remain zero on any
interval of positive length.

## Not claimed

* An identification of this bivector with the torsional mismatch of the
  parent theory.
* A formula that writes the teleparallel scalar as a total divergence for
  an arbitrary motor.
-/

namespace DstDiophantine.Gravity.OffEquator

open Real Set Filter KillingAxis Perihelion CurvedTransport
open scoped Topology

/-! ### Frame velocity and the connection contraction -/

/-- Orthonormal components `(γ, ûr, ûθ, ûφ)`. -/
def frameVel (γ ur uθ uφ : ℝ) : Fin 4 → ℝ
  | 0 => γ
  | 1 => ur
  | 2 => uθ
  | 3 => uφ

/-- `ω^a_b(u) = Σ_c u^c ω^a_b(e_c)`. -/
def connAlong (ω : Fin 4 → Fin 4 → Fin 4 → ℝ) (u : Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  ω a b 0 * u 0 + ω a b 1 * u 1 + ω a b 2 * u 2 + ω a b 3 * u 3

/-- Geodesic acceleration `Σ_b ω^a_b(u) u^b`. The component derivative cancels it. -/
def geodesicAccel (ω : Fin 4 → Fin 4 → Fin 4 → ℝ) (u : Fin 4 → ℝ) (a : Fin 4) : ℝ :=
  connAlong ω u a 0 * u 0 + connAlong ω u a 1 * u 1 +
    connAlong ω u a 2 * u 2 + connAlong ω u a 3 * u 3

/-- Rotation `cot θ / r` within the tangent plane of the sphere. -/
noncomputable def sphereRotation (θ r : ℝ) : ℝ :=
  (Real.cos θ / Real.sin θ) / r

/-- Squared Lorentz factor with both angular legs. -/
def gammaSq3 (ur uθ uφ : ℝ) : ℝ :=
  1 + ur ^ 2 + uθ ^ 2 + uφ ^ 2

/-- Squared angular momentum on the sphere, `L² = r²(ûθ² + ûφ²)`. -/
def angularMomentumSq (r uθ uφ : ℝ) : ℝ :=
  r ^ 2 * (uθ ^ 2 + uφ ^ 2)

/-- Azimuthal component `r sin θ ûφ`. -/
noncomputable def azimuthalMomentum (r θ uφ : ℝ) : ℝ :=
  r * Real.sin θ * uφ

theorem geodesicAccel_time (rs r θ γ ur uθ uφ : ℝ) :
    geodesicAccel (exteriorConn rs r θ) (frameVel γ ur uθ uφ) 0 =
      dSqrtA_dr rs r * γ * ur := by
  dsimp [geodesicAccel, connAlong, frameVel, exteriorConn]
  simp only [zero_mul, add_zero, zero_add]

theorem geodesicAccel_radial (rs r θ γ ur uθ uφ : ℝ) :
    geodesicAccel (exteriorConn rs r θ) (frameVel γ ur uθ uφ) 1 =
      dSqrtA_dr rs r * γ ^ 2 -
        (killingNorm rs r / r) * (uθ ^ 2 + uφ ^ 2) := by
  dsimp [geodesicAccel, connAlong, frameVel, exteriorConn]
  simp only [zero_mul, add_zero, zero_add]
  ring

theorem geodesicAccel_polar (rs r θ γ ur uθ uφ : ℝ) :
    geodesicAccel (exteriorConn rs r θ) (frameVel γ ur uθ uφ) 2 =
      (killingNorm rs r / r) * uθ * ur - sphereRotation θ r * uφ ^ 2 := by
  dsimp [geodesicAccel, connAlong, frameVel, exteriorConn, sphereRotation]
  simp only [zero_mul, add_zero, zero_add]
  ring

theorem geodesicAccel_azimuth (rs r θ γ ur uθ uφ : ℝ) :
    geodesicAccel (exteriorConn rs r θ) (frameVel γ ur uθ uφ) 3 =
      (killingNorm rs r / r) * uφ * ur + sphereRotation θ r * uθ * uφ := by
  dsimp [geodesicAccel, connAlong, frameVel, exteriorConn, sphereRotation]
  simp only [zero_mul, add_zero, zero_add]
  ring

/-- Once `γ²` is the Lorentz factor, the radial geodesic rate is the
equatorial law with `ûθ² + ûφ²` in place of `(L/r)²`. -/
theorem radial_rate_normalized {rs r θ γ ur uθ uφ : ℝ} (h : IsExterior rs r)
    (hγ : γ ^ 2 = gammaSq3 ur uθ uφ) :
    -geodesicAccel (exteriorConn rs r θ) (frameVel γ ur uθ uφ) 1 =
      -(gammaSq3 ur uθ uφ) / axisDistance rs r +
        (killingNorm rs r / r) * (uθ ^ 2 + uφ ^ 2) := by
  have hℓ : axisDistance rs r ≠ 0 := (axisDistance_pos h).ne'
  rw [geodesicAccel_radial]
  have hα : dSqrtA_dr rs r = 1 / axisDistance rs r := by
    rw [eq_div_iff hℓ, mul_comm]
    exact axisDistance_mul_dSqrtA_dr h
  rw [hα, hγ]
  ring

/-- At vanishing polar velocity the radial rate is the equatorial one. -/
theorem equator_radial_rate {rs r ur L : ℝ} (h : IsExterior rs r) (θ : ℝ) :
    -geodesicAccel (exteriorConn rs r θ)
        (frameVel (Real.sqrt (gammaSq3 ur 0 (angularMomentum L r))) ur 0
          (angularMomentum L r)) 1 =
      radialMomentumRate rs r ur L := by
  have hsq : (Real.sqrt (gammaSq3 ur 0 (angularMomentum L r))) ^ 2 =
      gammaSq3 ur 0 (angularMomentum L r) := by
    apply Real.sq_sqrt
    unfold gammaSq3
    positivity
  rw [radial_rate_normalized h hsq]
  simp only [gammaSq3, radialMomentumRate, angularMomentum, gammaSq]
  ring

/-- On the equator the polar geodesic acceleration vanishes at `ûθ = 0`. -/
theorem equator_polar_accel {rs r ur uφ : ℝ} :
    geodesicAccel (exteriorConn rs r (Real.pi / 2)) (frameVel 0 ur 0 uφ) 2 = 0 := by
  rw [geodesicAccel_polar]
  simp [sphereRotation, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- On the equator the azimuthal rate is the torsional leg. -/
theorem equator_azimuth_rate {rs r γ ur uφ : ℝ} :
    -geodesicAccel (exteriorConn rs r (Real.pi / 2)) (frameVel γ ur 0 uφ) 3 =
      -((killingNorm rs r / r) * ur * uφ) := by
  rw [geodesicAccel_azimuth]
  simp [sphereRotation, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-! ### The tangent rotation cancels -/

/-- The two appearances of the tangent rotation cancel in `ûθ² + ûφ²`. -/
theorem sphere_rotation_cancels (uθ uφ c : ℝ) :
    2 * uθ * (c * uφ ^ 2) + 2 * uφ * (-(c * uθ * uφ)) = 0 := by
  ring

/-- What remains is the geodesic curvature of the sphere. -/
theorem transverse_rate (β ur uθ uφ c : ℝ) :
    2 * uθ * (-(β * ur * uθ) + c * uφ ^ 2) +
        2 * uφ * (-(β * ur * uφ) - c * uθ * uφ) =
      -2 * β * ur * (uθ ^ 2 + uφ ^ 2) := by
  ring

/-- The same rotation cancels against `d(sin θ)/dτ` in `r sin θ ûφ`. -/
theorem azimuthal_rotation_cancels {cθ s ρ uθ uφ ν ur : ℝ}
    (hs : s ≠ 0) (hρ : ρ ≠ 0) :
    (cθ * (uθ / ρ)) * uφ +
        s * (-(ν / ρ) * ur * uφ - ((cθ / s) / ρ) * uθ * uφ) =
      -((s * ν / ρ) * ur * uφ) := by
  field_simp [hs, hρ]
  ring

theorem angularMomentumSq_hasDerivAt {r uθ uφ : ℝ → ℝ} {τ ν ur c : ℝ}
    (hρ : r τ ≠ 0)
    (hr : HasDerivAt r (ν * ur) τ)
    (hθ : HasDerivAt uθ (-(ν / r τ) * ur * uθ τ + c * (uφ τ) ^ 2) τ)
    (hφ : HasDerivAt uφ (-(ν / r τ) * ur * uφ τ - c * uθ τ * uφ τ) τ) :
    HasDerivAt (fun σ => angularMomentumSq (r σ) (uθ σ) (uφ σ)) 0 τ := by
  set ρ : ℝ := r τ
  set θ' : ℝ := -(ν / ρ) * ur * uθ τ + c * (uφ τ) ^ 2
  set φ' : ℝ := -(ν / ρ) * ur * uφ τ - c * uθ τ * uφ τ
  have hθ' : HasDerivAt uθ θ' τ := by simpa [θ', ρ] using hθ
  have hφ' : HasDerivAt uφ φ' τ := by simpa [φ', ρ] using hφ
  have hθ2 : HasDerivAt (fun σ => (uθ σ) ^ 2) (2 * uθ τ * θ') τ := by
    have hmul := hθ'.mul hθ'
    have hfun : (fun σ => (uθ σ) ^ 2) = uθ * uθ := by
      ext σ
      simp [pow_two]
    refine (hmul.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
    ring
  have hφ2 : HasDerivAt (fun σ => (uφ σ) ^ 2) (2 * uφ τ * φ') τ := by
    have hmul := hφ'.mul hφ'
    have hfun : (fun σ => (uφ σ) ^ 2) = uφ * uφ := by
      ext σ
      simp [pow_two]
    refine (hmul.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
    ring
  have hT : HasDerivAt (fun σ => (uθ σ) ^ 2 + (uφ σ) ^ 2)
      (-2 * (ν / ρ) * ur * ((uθ τ) ^ 2 + (uφ τ) ^ 2)) τ := by
    have hadd := hθ2.add hφ2
    refine hadd.congr_deriv ?_
    have hrate := transverse_rate (ν / ρ) ur (uθ τ) (uφ τ) c
    simpa [θ', φ'] using hrate
  have hr2 : HasDerivAt (fun σ => (r σ) ^ 2) (2 * ρ * (ν * ur)) τ := by
    have hmul := hr.mul hr
    have hfun : (fun σ => (r σ) ^ 2) = r * r := by
      ext σ
      simp [pow_two]
    refine (hmul.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
    simp [ρ]
    ring
  have hprod := hr2.mul hT
  have hfun : (fun σ => angularMomentumSq (r σ) (uθ σ) (uφ σ)) =
      (fun σ => (r σ) ^ 2) * fun σ => (uθ σ) ^ 2 + (uφ σ) ^ 2 := by
    ext σ
    simp [angularMomentumSq]
  refine (hprod.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
  have hρ' : ρ ≠ 0 := hρ
  rw [show r τ = ρ from rfl]
  field_simp [hρ']
  ring

/-- `L²` takes the same value at any two times of an interval on which the
angular rates hold. -/
theorem angularMomentumSq_eq_on {a b : ℝ} {r uθ uφ ν ur c : ℝ → ℝ}
    (_hab : a ≤ b)
    (hρ : ∀ τ ∈ Icc a b, r τ ≠ 0)
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (ν τ * ur τ) τ)
    (hθ : ∀ τ ∈ Icc a b,
      HasDerivAt uθ (-(ν τ / r τ) * ur τ * uθ τ + c τ * (uφ τ) ^ 2) τ)
    (hφ : ∀ τ ∈ Icc a b,
      HasDerivAt uφ (-(ν τ / r τ) * ur τ * uφ τ - c τ * uθ τ * uφ τ) τ)
    {τ₁ τ₂ : ℝ} (h₁ : τ₁ ∈ Icc a b) (h₂ : τ₂ ∈ Icc a b) :
    angularMomentumSq (r τ₁) (uθ τ₁) (uφ τ₁) =
      angularMomentumSq (r τ₂) (uθ τ₂) (uφ τ₂) := by
  let L : ℝ → ℝ := fun σ => angularMomentumSq (r σ) (uθ σ) (uφ σ)
  have hL : ∀ σ ∈ Icc a b, HasDerivAt L 0 σ := fun σ hσ =>
    angularMomentumSq_hasDerivAt (hρ σ hσ) (hr σ hσ) (hθ σ hσ) (hφ σ hσ)
  have hlip :=
    Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (C := 0) (f := L) (s := Icc a b)
      (fun σ hσ => (hL σ hσ).differentiableAt)
      (fun σ hσ => by
        rw [(hL σ hσ).deriv]
        simp)
      (convex_Icc a b) h₁ h₂
  have hle : ‖L τ₂ - L τ₁‖ ≤ 0 := by simpa using hlip
  have hsub : L τ₂ - L τ₁ = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact (sub_eq_zero.mp hsub).symm

theorem azimuthalMomentum_hasDerivAt {r θ uθ uφ : ℝ → ℝ} {τ ν ur : ℝ}
    (hρ : r τ ≠ 0) (hs : Real.sin (θ τ) ≠ 0)
    (hr : HasDerivAt r (ν * ur) τ)
    (hθ : HasDerivAt θ (uθ τ / r τ) τ)
    (hφ : HasDerivAt uφ
      (-(ν / r τ) * ur * uφ τ - sphereRotation (θ τ) (r τ) * uθ τ * uφ τ) τ) :
    HasDerivAt (fun σ => azimuthalMomentum (r σ) (θ σ) (uφ σ)) 0 τ := by
  set ρ : ℝ := r τ
  set s : ℝ := Real.sin (θ τ)
  set cθ : ℝ := Real.cos (θ τ)
  have hsin : HasDerivAt (Real.sin ∘ θ) (cθ * (uθ τ / ρ)) τ := by
    simpa [cθ, ρ] using (Real.hasDerivAt_sin (θ τ)).comp τ hθ
  have hφ' : HasDerivAt uφ
      (-(ν / ρ) * ur * uφ τ - ((cθ / s) / ρ) * uθ τ * uφ τ) τ := by
    simpa [sphereRotation, ρ, s, cθ] using hφ
  have hprod := hsin.mul hφ'
  have hinner : HasDerivAt (fun σ => Real.sin (θ σ) * uφ σ)
      (-((s * ν / ρ) * ur * uφ τ)) τ := by
    have hfun : (fun σ => Real.sin (θ σ) * uφ σ) = (Real.sin ∘ θ) * uφ := by
      ext σ
      rfl
    refine (hprod.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
    have hcancel :=
      azimuthal_rotation_cancels (cθ := cθ) (s := s) (ρ := ρ) (uθ := uθ τ)
        (uφ := uφ τ) (ν := ν) (ur := ur) hs hρ
    simpa [s] using hcancel
  have houter := hr.mul hinner
  have hfun : (fun σ => azimuthalMomentum (r σ) (θ σ) (uφ σ)) =
      r * fun σ => Real.sin (θ σ) * uφ σ := by
    ext σ
    simp [azimuthalMomentum, mul_assoc]
  refine (houter.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv ?_
  rw [show r τ = ρ from rfl, show Real.sin (θ τ) = s from rfl]
  field_simp [hρ]
  ring

theorem azimuthalMomentum_eq_on {a b : ℝ} {r θ uθ uφ ν ur : ℝ → ℝ}
    (_hab : a ≤ b)
    (hρ : ∀ τ ∈ Icc a b, r τ ≠ 0)
    (hs : ∀ τ ∈ Icc a b, Real.sin (θ τ) ≠ 0)
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (ν τ * ur τ) τ)
    (hθ : ∀ τ ∈ Icc a b, HasDerivAt θ (uθ τ / r τ) τ)
    (hφ : ∀ τ ∈ Icc a b, HasDerivAt uφ
      (-(ν τ / r τ) * ur τ * uφ τ -
        sphereRotation (θ τ) (r τ) * uθ τ * uφ τ) τ)
    {τ₁ τ₂ : ℝ} (h₁ : τ₁ ∈ Icc a b) (h₂ : τ₂ ∈ Icc a b) :
    azimuthalMomentum (r τ₁) (θ τ₁) (uφ τ₁) =
      azimuthalMomentum (r τ₂) (θ τ₂) (uφ τ₂) := by
  let M : ℝ → ℝ := fun σ => azimuthalMomentum (r σ) (θ σ) (uφ σ)
  have hM : ∀ σ ∈ Icc a b, HasDerivAt M 0 σ := fun σ hσ =>
    azimuthalMomentum_hasDerivAt (hρ σ hσ) (hs σ hσ) (hr σ hσ) (hθ σ hσ) (hφ σ hσ)
  have hlip :=
    Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (C := 0) (f := M) (s := Icc a b)
      (fun σ hσ => (hM σ hσ).differentiableAt)
      (fun σ hσ => by
        rw [(hM σ hσ).deriv]
        simp)
      (convex_Icc a b) h₁ h₂
  have hle : ‖M τ₂ - M τ₁‖ ≤ 0 := by simpa using hlip
  have hsub : M τ₂ - M τ₁ = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact (sub_eq_zero.mp hsub).symm

/-! ### Areal acceleration and the first integral -/

theorem inclined_areal_parts {ν ℓ ur uθ uφ r : ℝ} (hℓ : ℓ ≠ 0) (hr : r ≠ 0) :
    (ν / ℓ) * ur ^ 2 +
        ν * (-(gammaSq3 ur uθ uφ) / ℓ + (ν / r) * (uθ ^ 2 + uφ ^ 2)) =
      -(ν / ℓ) - (ν / ℓ) * (uθ ^ 2 + uφ ^ 2) +
        (ν ^ 2 / r) * (uθ ^ 2 + uφ ^ 2) := by
  unfold gammaSq3
  field_simp [hℓ, hr]
  ring

theorem inclined_speed_sq (ν ur uθ uφ : ℝ) :
    (ν * ur) ^ 2 =
      ν ^ 2 * gammaSq3 ur uθ uφ - ν ^ 2 * (1 + uθ ^ 2 + uφ ^ 2) := by
  unfold gammaSq3
  ring

/-- Where the radial law holds, the areal acceleration is the equatorial one
in the instantaneous `L² = r²(ûθ² + ûφ²)`. -/
theorem arealAccel_hasDerivAt {rs : ℝ} {r ur uθ uφ : ℝ → ℝ} {τ : ℝ}
    (hExt : IsExterior rs (r τ))
    (hr : HasDerivAt r (killingNorm rs (r τ) * ur τ) τ)
    (hur : HasDerivAt ur
      (-(gammaSq3 (ur τ) (uθ τ) (uφ τ)) / axisDistance rs (r τ) +
        (killingNorm rs (r τ) / r τ) * ((uθ τ) ^ 2 + (uφ τ) ^ 2)) τ) :
    HasDerivAt (fun σ => killingNorm rs (r σ) * ur σ)
      (-killingRate rs (r τ) +
        schwarzschildA rs (r τ) *
          angularMomentumSq (r τ) (uθ τ) (uφ τ) / (r τ) ^ 3 -
        killingRate rs (r τ) *
          angularMomentumSq (r τ) (uθ τ) (uφ τ) / (r τ) ^ 2) τ := by
  set ℓ : ℝ := axisDistance rs (r τ)
  set ν : ℝ := killingNorm rs (r τ)
  set Lsq : ℝ := angularMomentumSq (r τ) (uθ τ) (uφ τ)
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
    inclined_areal_parts (ν := ν) (ℓ := ℓ) (ur := ur τ) (uθ := uθ τ) (uφ := uφ τ)
      (r := r τ) hℓ hr0
  have hL : (uθ τ) ^ 2 + (uφ τ) ^ 2 = Lsq / (r τ) ^ 2 := by
    have hr2 : (r τ) ^ 2 ≠ 0 := pow_ne_zero 2 hr0
    unfold Lsq angularMomentumSq
    field_simp [hr2]
  have hgoal :
      (1 / ℓ) * (ν * ur τ) * ur τ +
          ν * (-(gammaSq3 (ur τ) (uθ τ) (uφ τ)) / ℓ +
            (ν / r τ) * ((uθ τ) ^ 2 + (uφ τ) ^ 2)) =
        -killingRate rs (r τ) + schwarzschildA rs (r τ) * Lsq / (r τ) ^ 3 -
          killingRate rs (r τ) * Lsq / (r τ) ^ 2 := by
    calc
      (1 / ℓ) * (ν * ur τ) * ur τ +
          ν * (-(gammaSq3 (ur τ) (uθ τ) (uφ τ)) / ℓ +
            (ν / r τ) * ((uθ τ) ^ 2 + (uφ τ) ^ 2))
        = (ν / ℓ) * (ur τ) ^ 2 +
            ν * (-(gammaSq3 (ur τ) (uθ τ) (uφ τ)) / ℓ +
              (ν / r τ) * ((uθ τ) ^ 2 + (uφ τ) ^ 2)) := by ring
      _ = -(ν / ℓ) - (ν / ℓ) * ((uθ τ) ^ 2 + (uφ τ) ^ 2) +
            (ν ^ 2 / r τ) * ((uθ τ) ^ 2 + (uφ τ) ^ 2) := hparts
      _ = -killingRate rs (r τ) + schwarzschildA rs (r τ) * Lsq / (r τ) ^ 3 -
            killingRate rs (r τ) * Lsq / (r τ) ^ 2 := by
          rw [hκ, hL, hνsq]
          field_simp [hr0]
          ring
  exact hgoal

/-- Redshift and `γ` trade exactly, off the equator as on it. -/
theorem observerEnergy_hasDerivAt {rs : ℝ} {r γ : ℝ → ℝ} {τ ur : ℝ}
    (hExt : IsExterior rs (r τ))
    (hr : HasDerivAt r (killingNorm rs (r τ) * ur) τ)
    (hγ : HasDerivAt γ
      (-(γ τ) / axisDistance rs (r τ) * ur) τ) :
    HasDerivAt (fun σ => killingNorm rs (r σ) * γ σ) 0 τ := by
  set ℓ : ℝ := axisDistance rs (r τ)
  set ν : ℝ := killingNorm rs (r τ)
  have hℓ : ℓ ≠ 0 := (axisDistance_pos hExt).ne'
  have hνr := (hasDerivAt_killingNorm hExt).comp τ hr
  have hprod := hνr.mul hγ
  have hfun : (fun σ => killingNorm rs (r σ) * γ σ) =ᶠ[𝓝 τ]
      (killingNorm rs ∘ r) * γ := by
    refine EventuallyEq.of_eq ?_
    ext σ
    simp [Function.comp]
  refine (hprod.congr_of_eventuallyEq hfun.symm).congr_deriv ?_
  have hd : dSqrtA_dr rs (r τ) = 1 / ℓ := by
    rw [eq_div_iff hℓ, mul_comm]
    exact axisDistance_mul_dSqrtA_dr hExt
  rw [hd, show (killingNorm rs ∘ r) τ = ν from rfl]
  ring

theorem observerEnergy_eq_on {rs a b : ℝ} {r γ ur : ℝ → ℝ} (_hab : a ≤ b)
    (hExt : ∀ τ ∈ Icc a b, IsExterior rs (r τ))
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (killingNorm rs (r τ) * ur τ) τ)
    (hγ : ∀ τ ∈ Icc a b,
      HasDerivAt γ (-(γ τ) / axisDistance rs (r τ) * ur τ) τ)
    {τ₁ τ₂ : ℝ} (h₁ : τ₁ ∈ Icc a b) (h₂ : τ₂ ∈ Icc a b) :
    killingNorm rs (r τ₁) * γ τ₁ = killingNorm rs (r τ₂) * γ τ₂ := by
  let E : ℝ → ℝ := fun σ => killingNorm rs (r σ) * γ σ
  have hE : ∀ σ ∈ Icc a b, HasDerivAt E 0 σ := fun σ hσ =>
    observerEnergy_hasDerivAt (hExt σ hσ) (hr σ hσ) (hγ σ hσ)
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

/-- The first integral, with both angular legs inside `L²`. -/
theorem inclined_first_integral {rs a b : ℝ} {r ur uθ uφ γ : ℝ → ℝ} (hab : a ≤ b)
    (hExt : ∀ τ ∈ Icc a b, IsExterior rs (r τ))
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (killingNorm rs (r τ) * ur τ) τ)
    (hγ : ∀ τ ∈ Icc a b,
      HasDerivAt γ (-(γ τ) / axisDistance rs (r τ) * ur τ) τ)
    (hnorm : ∀ τ ∈ Icc a b, (γ τ) ^ 2 = gammaSq3 (ur τ) (uθ τ) (uφ τ))
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ Icc a b) (hτ : τ ∈ Icc a b) :
    (deriv r τ) ^ 2 =
      (killingNorm rs (r τ₀) * γ τ₀) ^ 2 -
        schwarzschildA rs (r τ) *
          (1 + angularMomentumSq (r τ) (uθ τ) (uφ τ) / (r τ) ^ 2) := by
  have hE := observerEnergy_eq_on hab hExt hr hγ hτ h₀
  have hv := (hr τ hτ).deriv
  rw [hv]
  have hsq := inclined_speed_sq (killingNorm rs (r τ)) (ur τ) (uθ τ) (uφ τ)
  have hν : killingNorm rs (r τ) ^ 2 = schwarzschildA rs (r τ) :=
    Real.sq_sqrt (schwarzschildA_pos (hExt τ hτ)).le
  have hr0 : r τ ≠ 0 := (lt_trans (hExt τ hτ).1 (hExt τ hτ).2).ne'
  have hL : (uθ τ) ^ 2 + (uφ τ) ^ 2 =
      angularMomentumSq (r τ) (uθ τ) (uφ τ) / (r τ) ^ 2 := by
    unfold angularMomentumSq
    field_simp [pow_ne_zero 2 hr0]
  have hL' : 1 + (uθ τ) ^ 2 + (uφ τ) ^ 2 =
      1 + angularMomentumSq (r τ) (uθ τ) (uφ τ) / (r τ) ^ 2 := by
    rw [← hL]
    ring
  calc (killingNorm rs (r τ) * ur τ) ^ 2
      = killingNorm rs (r τ) ^ 2 * gammaSq3 (ur τ) (uθ τ) (uφ τ) -
          killingNorm rs (r τ) ^ 2 * (1 + (uθ τ) ^ 2 + (uφ τ) ^ 2) := hsq
    _ = killingNorm rs (r τ) ^ 2 * (γ τ) ^ 2 -
          killingNorm rs (r τ) ^ 2 * (1 + (uθ τ) ^ 2 + (uφ τ) ^ 2) := by
        rw [← hnorm τ hτ]
    _ = (killingNorm rs (r τ₀) * γ τ₀) ^ 2 -
          schwarzschildA rs (r τ) *
            (1 + angularMomentumSq (r τ) (uθ τ) (uφ τ) / (r τ) ^ 2) := by
        have hsqγ : killingNorm rs (r τ) ^ 2 * (γ τ) ^ 2 =
            (killingNorm rs (r τ) * γ τ) ^ 2 := by ring
        rw [hsqγ, hE, hν, hL']

/-- The slope in an angle that advances at `L/r²` squares to the radial speed. -/
theorem orbital_slope {L r v : ℝ} (hL : L ≠ 0) (hr : r ≠ 0) :
    (L * ((-v / r ^ 2) / (L / r ^ 2))) ^ 2 = v ^ 2 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp [hL, hr2]

/-- That radial speed is the Binet residual of `u = 1/r`. -/
theorem speed_eq_binetResidual {E rs L r v : ℝ} (hr : r ≠ 0)
    (hv : v ^ 2 = E ^ 2 - schwarzschildA rs r * (1 + L ^ 2 / r ^ 2)) :
    v ^ 2 = binetResidual E rs L (1 / r) := by
  rw [hv, binetResidual, schwarzschildA]
  field_simp [hr]

/-- The perihelion excess reads the motion through `L²` alone, so the
inclined angle that advances at `L/r²` lies in the equatorial interval. -/
theorem excess_of_angular_square {M L p : ℝ} (hM : M ≠ 0) (hp : p = L ^ 2 / M)
    (hx0 : 0 < 6 * M / p) (hx1 : 6 * M / p < 1) :
    let k := Real.sqrt (1 - 6 * M / p)
    6 * Real.pi * M / p < 2 * Real.pi * (1 / k - 1) ∧
      2 * Real.pi * (1 / k - 1) < (6 * Real.pi * M / p) / (1 - 6 * M / p) :=
  Perihelion.perihelion_excess_latus hM hp hx0 hx1

/-! ### The colatitude band -/

theorem angularMomentumSq_nonneg (r uθ uφ : ℝ) : 0 ≤ angularMomentumSq r uθ uφ := by
  unfold angularMomentumSq
  positivity

/-- `(r sin θ ûφ)² ≤ L² sin²θ`. The difference is the polar leg. -/
theorem azimuthal_le_angular (r θ uθ uφ : ℝ) :
    azimuthalMomentum r θ uφ ^ 2 ≤
      angularMomentumSq r uθ uφ * (Real.sin θ) ^ 2 := by
  unfold azimuthalMomentum angularMomentumSq
  have hpol : 0 ≤ (r * Real.sin θ * uθ) ^ 2 := sq_nonneg _
  nlinarith [hpol]

theorem azimuthal_angular_gap (r θ uθ uφ : ℝ) :
    angularMomentumSq r uθ uφ * (Real.sin θ) ^ 2 -
        azimuthalMomentum r θ uφ ^ 2 =
      (r * Real.sin θ * uθ) ^ 2 := by
  unfold azimuthalMomentum angularMomentumSq
  ring

/-- Equality is exactly the vanishing of the polar leg, off the poles and the origin. -/
theorem azimuthal_eq_angular_iff {r θ uθ uφ : ℝ} (hr : r ≠ 0) (hs : Real.sin θ ≠ 0) :
    azimuthalMomentum r θ uφ ^ 2 =
      angularMomentumSq r uθ uφ * (Real.sin θ) ^ 2 ↔ uθ = 0 := by
  constructor
  · intro h
    have hgap := azimuthal_angular_gap r θ uθ uφ
    have hzero : (r * Real.sin θ * uθ) ^ 2 = 0 := by
      rw [← hgap, h, sub_self]
    have hfac : r * Real.sin θ ≠ 0 := mul_ne_zero hr hs
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hzero)).resolve_left hfac
  · intro hθ
    unfold azimuthalMomentum angularMomentumSq
    simp only [hθ]
    ring

/-- Wherever `L² ≠ 0`, `sin²θ` is at least the square of the ratio of the constants. -/
theorem colatitude_band (r θ uθ uφ : ℝ) (hL : angularMomentumSq r uθ uφ ≠ 0) :
    azimuthalMomentum r θ uφ ^ 2 / angularMomentumSq r uθ uφ ≤
      (Real.sin θ) ^ 2 := by
  have hpos : 0 < angularMomentumSq r uθ uφ :=
    lt_of_le_of_ne (angularMomentumSq_nonneg r uθ uφ) (Ne.symm hL)
  have hle : azimuthalMomentum r θ uφ ^ 2 ≤
      (Real.sin θ) ^ 2 * angularMomentumSq r uθ uφ := by
    simpa [mul_comm] using azimuthal_le_angular r θ uθ uφ
  exact (div_le_iff₀ hpos).mpr hle

/-- A nonzero azimuthal constant makes that lower bound positive. -/
theorem band_ratio_pos {r θ uθ uφ : ℝ}
    (hL : angularMomentumSq r uθ uφ ≠ 0) (hLz : azimuthalMomentum r θ uφ ≠ 0) :
    0 < azimuthalMomentum r θ uφ ^ 2 / angularMomentumSq r uθ uφ := by
  have hpos : 0 < angularMomentumSq r uθ uφ :=
    lt_of_le_of_ne (angularMomentumSq_nonneg r uθ uφ) (Ne.symm hL)
  exact div_pos (sq_pos_of_ne_zero hLz) hpos

/-- The polar leg is what `L²` does not put into the azimuthal constant. -/
theorem polar_leg {r θ uθ uφ : ℝ} (hr : r ≠ 0) (hs : Real.sin θ ≠ 0) :
    uθ ^ 2 =
      (angularMomentumSq r uθ uφ -
        azimuthalMomentum r θ uφ ^ 2 / (Real.sin θ) ^ 2) / r ^ 2 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hs2 : (Real.sin θ) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  unfold angularMomentumSq azimuthalMomentum
  field_simp [hr2, hs2]
  ring

/-- Along a motion that keeps both constants, the band holds at every time. -/
theorem colatitude_band_of_constants {a b : ℝ} {r θ uθ uφ ν ur : ℝ → ℝ}
    (hab : a ≤ b)
    (hρ : ∀ τ ∈ Icc a b, r τ ≠ 0)
    (hs : ∀ τ ∈ Icc a b, Real.sin (θ τ) ≠ 0)
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (ν τ * ur τ) τ)
    (hθc : ∀ τ ∈ Icc a b, HasDerivAt θ (uθ τ / r τ) τ)
    (hθ : ∀ τ ∈ Icc a b,
      HasDerivAt uθ (-(ν τ / r τ) * ur τ * uθ τ +
        sphereRotation (θ τ) (r τ) * (uφ τ) ^ 2) τ)
    (hφ : ∀ τ ∈ Icc a b, HasDerivAt uφ
      (-(ν τ / r τ) * ur τ * uφ τ -
        sphereRotation (θ τ) (r τ) * uθ τ * uφ τ) τ)
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ Icc a b) (hτ : τ ∈ Icc a b)
    (hL : angularMomentumSq (r τ₀) (uθ τ₀) (uφ τ₀) ≠ 0) :
    azimuthalMomentum (r τ₀) (θ τ₀) (uφ τ₀) ^ 2 /
        angularMomentumSq (r τ₀) (uθ τ₀) (uφ τ₀) ≤
      (Real.sin (θ τ)) ^ 2 := by
  have hLeq := angularMomentumSq_eq_on hab hρ hr hθ hφ hτ h₀
  have hMeq := azimuthalMomentum_eq_on hab hρ hs hr hθc hφ hτ h₀
  have hLτ : angularMomentumSq (r τ) (uθ τ) (uφ τ) ≠ 0 := by
    rw [hLeq]
    exact hL
  have hband := colatitude_band (r τ) (θ τ) (uθ τ) (uφ τ) hLτ
  rw [hMeq, hLeq] at hband
  exact hband

/-! ### The edge turns back toward the equator -/

theorem edge_polar_accel (rs r θ γ ur uφ : ℝ) :
    geodesicAccel (exteriorConn rs r θ) (frameVel γ ur 0 uφ) 2 =
      -(sphereRotation θ r * uφ ^ 2) := by
  rw [geodesicAccel_polar]
  ring

/-- Off the equator, with azimuthal speed, the edge is not an orbit. -/
theorem edge_polar_accel_ne {rs r θ γ ur uφ : ℝ}
    (hr : r ≠ 0) (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (hφ : uφ ≠ 0) :
    geodesicAccel (exteriorConn rs r θ) (frameVel γ ur 0 uφ) 2 ≠ 0 := by
  rw [edge_polar_accel]
  unfold sphereRotation
  have hrot : (Real.cos θ / Real.sin θ) / r ≠ 0 :=
    div_ne_zero (div_ne_zero hc hs) hr
  exact neg_ne_zero.mpr (mul_ne_zero hrot (pow_ne_zero 2 hφ))

theorem sphereRotation_mul_cos (r θ : ℝ) (hr : r ≠ 0) (hs : Real.sin θ ≠ 0) :
    sphereRotation θ r = Real.cos θ / (Real.sin θ * r) := by
  unfold sphereRotation
  field_simp [hr, hs]

/-- North of the equator the edge raises `θ`. -/
theorem northern_edge_rate {r θ uφ : ℝ}
    (hr : 0 < r) (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) (hφ : uφ ≠ 0) :
    0 < sphereRotation θ r * uφ ^ 2 := by
  rw [sphereRotation_mul_cos r θ hr.ne' hs.ne']
  exact mul_pos (div_pos hc (mul_pos hs hr)) (sq_pos_of_ne_zero hφ)

/-- South of the equator the edge lowers `θ`. -/
theorem southern_edge_rate {r θ uφ : ℝ}
    (hr : 0 < r) (hs : 0 < Real.sin θ) (hc : Real.cos θ < 0) (hφ : uφ ≠ 0) :
    sphereRotation θ r * uφ ^ 2 < 0 := by
  rw [sphereRotation_mul_cos r θ hr.ne' hs.ne']
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hc (mul_pos hs hr))
    (sq_pos_of_ne_zero hφ)

/-! ### A vanishing azimuthal constant is a meridian -/

/-- Off the poles, vanishing azimuthal momentum is a vanishing azimuthal leg. -/
theorem azimuthal_leg_of_zero {r θ uφ : ℝ} (hr : r ≠ 0) (hs : Real.sin θ ≠ 0)
    (hM : azimuthalMomentum r θ uφ = 0) : uφ = 0 := by
  unfold azimuthalMomentum at hM
  exact (mul_eq_zero.mp hM).resolve_left (mul_ne_zero hr hs)

/-- Where the azimuthal constant is zero, the leg stays zero. -/
theorem azimuthal_leg_zero_of_constant {a b : ℝ} {r θ uθ uφ ν ur : ℝ → ℝ}
    (hab : a ≤ b)
    (hρ : ∀ τ ∈ Icc a b, r τ ≠ 0)
    (hs : ∀ τ ∈ Icc a b, Real.sin (θ τ) ≠ 0)
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (ν τ * ur τ) τ)
    (hθc : ∀ τ ∈ Icc a b, HasDerivAt θ (uθ τ / r τ) τ)
    (hφ : ∀ τ ∈ Icc a b, HasDerivAt uφ
      (-(ν τ / r τ) * ur τ * uφ τ -
        sphereRotation (θ τ) (r τ) * uθ τ * uφ τ) τ)
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ Icc a b) (hτ : τ ∈ Icc a b)
    (hM : azimuthalMomentum (r τ₀) (θ τ₀) (uφ τ₀) = 0) :
    uφ τ = 0 := by
  have hEq := azimuthalMomentum_eq_on hab hρ hs hr hθc hφ hτ h₀
  exact azimuthal_leg_of_zero (hρ τ hτ) (hs τ hτ) (hEq.trans hM)

/-- The azimuthal coordinate of that leg does not advance. -/
theorem meridian_phi_const {a b : ℝ} {φ r θ uφ : ℝ → ℝ} (_hab : a ≤ b)
    (hρ : ∀ τ ∈ Icc a b, r τ ≠ 0)
    (hs : ∀ τ ∈ Icc a b, Real.sin (θ τ) ≠ 0)
    (hφ : ∀ τ ∈ Icc a b, HasDerivAt φ (uφ τ / (r τ * Real.sin (θ τ))) τ)
    (hleg : ∀ τ ∈ Icc a b, uφ τ = 0)
    {τ₁ τ₂ : ℝ} (h₁ : τ₁ ∈ Icc a b) (h₂ : τ₂ ∈ Icc a b) :
    φ τ₁ = φ τ₂ := by
  have h0 : ∀ σ ∈ Icc a b, HasDerivAt φ 0 σ := by
    intro σ hσ
    have hden : r σ * Real.sin (θ σ) ≠ 0 := mul_ne_zero (hρ σ hσ) (hs σ hσ)
    have hrate : uφ σ / (r σ * Real.sin (θ σ)) = 0 := by
      rw [hleg σ hσ]
      exact (div_eq_iff hden).mpr (by ring)
    exact (hφ σ hσ).congr_deriv hrate
  have hlip :=
    Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (C := 0) (f := φ) (s := Icc a b)
      (fun σ hσ => (h0 σ hσ).differentiableAt)
      (fun σ hσ => by
        rw [(h0 σ hσ).deriv]
        simp)
      (convex_Icc a b) h₁ h₂
  have hle : ‖φ τ₂ - φ τ₁‖ ≤ 0 := by simpa using hlip
  have hsub : φ τ₂ - φ τ₁ = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact (sub_eq_zero.mp hsub).symm

/-- Both angular accelerations lose the sphere's rotation. -/
theorem meridian_polar_accel (rs r θ γ ur uθ : ℝ) :
    geodesicAccel (exteriorConn rs r θ) (frameVel γ ur uθ 0) 2 =
      (killingNorm rs r / r) * uθ * ur := by
  rw [geodesicAccel_polar]
  ring

theorem meridian_azimuth_accel (rs r θ γ ur uθ : ℝ) :
    geodesicAccel (exteriorConn rs r θ) (frameVel γ ur uθ 0) 3 = 0 := by
  rw [geodesicAccel_azimuth]
  ring

/-- The polar leg changes by the equatorial torsional law, at every colatitude. -/
theorem meridian_polar_matches_torsional (rs r θ γ ur uθ : ℝ) :
    -geodesicAccel (exteriorConn rs r θ) (frameVel γ ur uθ 0) 2 =
      -((killingNorm rs r / r) * ur * uθ) := by
  rw [meridian_polar_accel]
  ring

theorem meridian_angularMomentumSq (r uθ : ℝ) :
    angularMomentumSq r uθ 0 = (r * uθ) ^ 2 := by
  unfold angularMomentumSq
  ring

/-- The colatitude itself advances at `L/r²`, with `L = r ûθ`. -/
theorem meridian_colatitude_rate {r uθ L : ℝ} (hr : r ≠ 0) (hL : L = r * uθ) :
    uθ / r = L / r ^ 2 := by
  rw [hL]
  field_simp [hr]

/-- The radial acceleration is the equatorial one in this `L`. -/
theorem meridian_radial_is_equatorial {rs r ur uθ : ℝ} (h : IsExterior rs r)
    (θ γ : ℝ) (hγ : γ ^ 2 = gammaSq3 ur uθ 0) :
    -geodesicAccel (exteriorConn rs r θ) (frameVel γ ur uθ 0) 1 =
      radialMomentumRate rs r ur (r * uθ) := by
  have hr : r ≠ 0 := (lt_trans h.1 h.2).ne'
  rw [radial_rate_normalized h hγ]
  unfold radialMomentumRate gammaSq angularMomentum gammaSq3
  field_simp [hr]
  ring

/-! ### A fixed colatitude is radial, or it is the equator -/

/-- Vanishing angular momentum kills both angular legs. -/
theorem angular_legs_of_zero {r uθ uφ : ℝ} (hr : r ≠ 0)
    (hL : angularMomentumSq r uθ uφ = 0) : uθ = 0 ∧ uφ = 0 := by
  unfold angularMomentumSq at hL
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hsum : uθ ^ 2 + uφ ^ 2 = 0 := (mul_eq_zero.mp hL).resolve_left hr2
  refine ⟨?_, ?_⟩
  · exact sq_eq_zero_iff.mp
      (le_antisymm (by nlinarith [sq_nonneg uφ]) (sq_nonneg uθ))
  · exact sq_eq_zero_iff.mp
      (le_antisymm (by nlinarith [sq_nonneg uθ]) (sq_nonneg uφ))

/-- A vanishing polar leg does not advance the colatitude. -/
theorem colatitude_const_of_zero_polar {a b : ℝ} {θ r uθ : ℝ → ℝ} (_hab : a ≤ b)
    (hρ : ∀ τ ∈ Icc a b, r τ ≠ 0)
    (hθ : ∀ τ ∈ Icc a b, HasDerivAt θ (uθ τ / r τ) τ)
    (hleg : ∀ τ ∈ Icc a b, uθ τ = 0)
    {τ₁ τ₂ : ℝ} (h₁ : τ₁ ∈ Icc a b) (h₂ : τ₂ ∈ Icc a b) :
    θ τ₁ = θ τ₂ := by
  have h0 : ∀ σ ∈ Icc a b, HasDerivAt θ 0 σ := by
    intro σ hσ
    have hden : r σ ≠ 0 := hρ σ hσ
    have hrate : uθ σ / r σ = 0 := by
      rw [hleg σ hσ]
      exact (div_eq_iff hden).mpr (by ring)
    exact (hθ σ hσ).congr_deriv hrate
  have hlip :=
    Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (C := 0) (f := θ) (s := Icc a b)
      (fun σ hσ => (h0 σ hσ).differentiableAt)
      (fun σ hσ => by
        rw [(h0 σ hσ).deriv]
        simp)
      (convex_Icc a b) h₁ h₂
  have hle : ‖θ τ₂ - θ τ₁‖ ≤ 0 := by simpa using hlip
  have hsub : θ τ₂ - θ τ₁ = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact (sub_eq_zero.mp hsub).symm

/-- Vanishing angular momentum is a radial line at fixed angles. -/
theorem radial_angles_fixed {a b : ℝ} {θ φ r uθ uφ ν ur : ℝ → ℝ}
    (hab : a ≤ b)
    (hρ : ∀ τ ∈ Icc a b, r τ ≠ 0)
    (hs : ∀ τ ∈ Icc a b, Real.sin (θ τ) ≠ 0)
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (ν τ * ur τ) τ)
    (hθc : ∀ τ ∈ Icc a b, HasDerivAt θ (uθ τ / r τ) τ)
    (hφc : ∀ τ ∈ Icc a b, HasDerivAt φ (uφ τ / (r τ * Real.sin (θ τ))) τ)
    (hθ : ∀ τ ∈ Icc a b,
      HasDerivAt uθ (-(ν τ / r τ) * ur τ * uθ τ +
        sphereRotation (θ τ) (r τ) * (uφ τ) ^ 2) τ)
    (hφ : ∀ τ ∈ Icc a b, HasDerivAt uφ
      (-(ν τ / r τ) * ur τ * uφ τ -
        sphereRotation (θ τ) (r τ) * uθ τ * uφ τ) τ)
    {τ₀ τ₁ τ₂ : ℝ} (h₀ : τ₀ ∈ Icc a b) (h₁ : τ₁ ∈ Icc a b) (h₂ : τ₂ ∈ Icc a b)
    (hL : angularMomentumSq (r τ₀) (uθ τ₀) (uφ τ₀) = 0) :
    θ τ₁ = θ τ₂ ∧ φ τ₁ = φ τ₂ := by
  have hlegs : ∀ τ ∈ Icc a b, uθ τ = 0 ∧ uφ τ = 0 := by
    intro τ hτ
    have hEq := angularMomentumSq_eq_on hab hρ hr hθ hφ hτ h₀
    exact angular_legs_of_zero (hρ τ hτ) (hEq.trans hL)
  refine ⟨?_, ?_⟩
  · exact colatitude_const_of_zero_polar hab hρ hθc (fun τ hτ => (hlegs τ hτ).1) h₁ h₂
  · exact meridian_phi_const hab hρ hs hφc (fun τ hτ => (hlegs τ hτ).2) h₁ h₂

/-- Where the constants agree, the band is the equator and the polar leg vanishes. -/
theorem band_collapses_to_equator {r θ uθ uφ : ℝ}
    (hr : r ≠ 0) (hs : Real.sin θ ≠ 0)
    (hL : angularMomentumSq r uθ uφ ≠ 0)
    (heq : azimuthalMomentum r θ uφ ^ 2 = angularMomentumSq r uθ uφ) :
    (Real.sin θ) ^ 2 = 1 ∧ uθ = 0 := by
  have hband := colatitude_band r θ uθ uφ hL
  rw [heq, div_self hL] at hband
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
    have h := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg (Real.cos θ)]
  have h1 : (Real.sin θ) ^ 2 = 1 := le_antisymm hsin hband
  have hleg : uθ = 0 :=
    (azimuthal_eq_angular_iff hr hs).mp (by rw [heq, h1]; ring)
  exact ⟨h1, hleg⟩

/-- A motion that meets the equator with vanishing polar leg stays there. -/
theorem equator_persists {a b : ℝ} {r θ uθ uφ ν ur : ℝ → ℝ}
    (hab : a ≤ b)
    (hρ : ∀ τ ∈ Icc a b, r τ ≠ 0)
    (hs : ∀ τ ∈ Icc a b, Real.sin (θ τ) ≠ 0)
    (hr : ∀ τ ∈ Icc a b, HasDerivAt r (ν τ * ur τ) τ)
    (hθc : ∀ τ ∈ Icc a b, HasDerivAt θ (uθ τ / r τ) τ)
    (hθ : ∀ τ ∈ Icc a b,
      HasDerivAt uθ (-(ν τ / r τ) * ur τ * uθ τ +
        sphereRotation (θ τ) (r τ) * (uφ τ) ^ 2) τ)
    (hφ : ∀ τ ∈ Icc a b, HasDerivAt uφ
      (-(ν τ / r τ) * ur τ * uφ τ -
        sphereRotation (θ τ) (r τ) * uθ τ * uφ τ) τ)
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ Icc a b) (hτ : τ ∈ Icc a b)
    (hL : angularMomentumSq (r τ₀) (uθ τ₀) (uφ τ₀) ≠ 0)
    (hpol : uθ τ₀ = 0)
    (heq : (Real.sin (θ τ₀)) ^ 2 = 1) :
    (Real.sin (θ τ)) ^ 2 = 1 ∧ uθ τ = 0 := by
  have hLeq := angularMomentumSq_eq_on hab hρ hr hθ hφ hτ h₀
  have hMeq := azimuthalMomentum_eq_on hab hρ hs hr hθc hφ hτ h₀
  have hM0 : azimuthalMomentum (r τ₀) (θ τ₀) (uφ τ₀) ^ 2 =
      angularMomentumSq (r τ₀) (uθ τ₀) (uφ τ₀) := by
    rw [(azimuthal_eq_angular_iff (hρ τ₀ h₀) (hs τ₀ h₀)).mpr hpol, heq]
    ring
  have hLτ : angularMomentumSq (r τ) (uθ τ) (uφ τ) ≠ 0 := by
    rw [hLeq]
    exact hL
  have hMτ : azimuthalMomentum (r τ) (θ τ) (uφ τ) ^ 2 =
      angularMomentumSq (r τ) (uθ τ) (uφ τ) := by
    rw [hMeq, hLeq]
    exact hM0
  exact band_collapses_to_equator (hρ τ hτ) (hs τ hτ) hLτ hMτ

/-- On that latitude the tangent rotation of the sphere is zero. -/
theorem sphereRotation_of_equator {θ r : ℝ} (hs : (Real.sin θ) ^ 2 = 1) :
    sphereRotation θ r = 0 := by
  have hcos : Real.cos θ = 0 := by
    have h := Real.sin_sq_add_cos_sq θ
    exact sq_eq_zero_iff.mp (by nlinarith)
  unfold sphereRotation
  rw [hcos, zero_div, zero_div]

/-- The azimuthal rate on that latitude is the torsional leg. -/
theorem equator_latitude_azimuth {rs r θ γ ur uφ : ℝ}
    (hs : (Real.sin θ) ^ 2 = 1) :
    -geodesicAccel (exteriorConn rs r θ) (frameVel γ ur 0 uφ) 3 =
      -((killingNorm rs r / r) * ur * uφ) := by
  rw [geodesicAccel_azimuth, sphereRotation_of_equator hs]
  ring

/-- Off the equator a vanishing polar leg does not persist. -/
theorem no_fixed_latitude_off_equator {a b : ℝ} {θ r uθ uφ ν ur : ℝ → ℝ}
    {τ₀ : ℝ} (h₀ : τ₀ ∈ Ioo a b)
    (hleg : ∀ τ ∈ Icc a b, uθ τ = 0)
    (hθ : ∀ τ ∈ Icc a b, HasDerivAt uθ
      (-(ν τ / r τ) * ur τ * uθ τ +
        sphereRotation (θ τ) (r τ) * (uφ τ) ^ 2) τ)
    (hr : r τ₀ ≠ 0) (hs : Real.sin (θ τ₀) ≠ 0)
    (hc : Real.cos (θ τ₀) ≠ 0) (hφ : uφ τ₀ ≠ 0) :
    False := by
  have hτ₀ : τ₀ ∈ Icc a b := ⟨le_of_lt h₀.1, le_of_lt h₀.2⟩
  have hzero : HasDerivAt uθ 0 τ₀ := by
    refine (hasDerivAt_const τ₀ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds h₀.1 h₀.2] with τ hτ
    exact hleg τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  have hrate : -(ν τ₀ / r τ₀) * ur τ₀ * uθ τ₀ +
      sphereRotation (θ τ₀) (r τ₀) * (uφ τ₀) ^ 2 =
      sphereRotation (θ τ₀) (r τ₀) * (uφ τ₀) ^ 2 := by
    rw [hleg τ₀ hτ₀]
    ring
  have hgeo := (hθ τ₀ hτ₀).congr_deriv hrate
  have heq : sphereRotation (θ τ₀) (r τ₀) * (uφ τ₀) ^ 2 = 0 := by
    rw [← hgeo.deriv, hzero.deriv]
  have hrot : sphereRotation (θ τ₀) (r τ₀) ≠ 0 := by
    unfold sphereRotation
    exact div_ne_zero (div_ne_zero hc hs) hr
  exact mul_ne_zero hrot (pow_ne_zero 2 hφ) heq

end DstDiophantine.Gravity.OffEquator

