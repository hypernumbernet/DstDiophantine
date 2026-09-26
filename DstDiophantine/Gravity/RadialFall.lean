import DstDiophantine.Gravity.KillingAxis
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# From the flat fall to the radial Schwarzschild motion

The flat flow fixes a law for radial rapidity, not a geodesic of the exterior.
Along the inertial line `s e₀`, with `|s| < ℓ`, the local axis distance is the
hyperbolic radius `ρ = √(ℓ² − s²)`. The rapidity `ψ` relative to the hovering
observer stationed there, positive when the motion is outward, satisfies
`sinh ψ = −s/ρ` and
`dψ/ds = − cosh ψ / ρ`.
At release, `ψ = 0` and `ρ = ℓ`, so the derivative equals the initial
acceleration `−1/ℓ` of the simultaneous separation.

On the exterior the same law is kept, with the chart distance `ℓ(r)` in place
of `ρ`, and the static coframe converts rapidity into the areal radius,
`dr/dτ = √A sinh ψ`.
Differentiating, the radial change of `√A` (whose derivative is `1/ℓ`)
contributes a `sinh² ψ` term and the rapidity law a `cosh² ψ` term. The
hyperbolic identity cancels every power of the speed:
`d²r/dτ² = −√A / ℓ = −κ = −rₛ/(2r²)`.
The combination `E = √A cosh ψ` has vanishing derivative, and on any proper-time
interval on which the two laws hold,
`(dr/dτ)² = E² − A`.
A body released from rest at radius `R` has `E² = A(R)`.

## Not claimed

* That one fixed flat jet, the straight line `s e₀` at a single `ℓ`, is itself
  a Schwarzschild geodesic.
* A covariant transport of the full Killing bivector, or a treatment of
  non-radial motion.
-/

namespace DstDiophantine.Gravity.KillingAxis

open Real Filter
open scoped Topology

/-! ### Flat flow: local radius and radial rapidity -/

/-- Hyperbolic distance from the axis to the released body at proper time `s`:
`ρ = √(ℓ² − s²)`. -/
noncomputable def releasedLocalRadius (ℓ s : ℝ) : ℝ :=
  Real.sqrt (ℓ ^ 2 - s ^ 2)

theorem releasedLocalRadius_pos {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : |s| < ℓ) :
    0 < releasedLocalRadius ℓ s := by
  have hsq : s ^ 2 < ℓ ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hℓ]
    exact hs
  exact Real.sqrt_pos.mpr (sub_pos.mpr hsq)

theorem releasedLocalRadius_sq {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : |s| < ℓ) :
    releasedLocalRadius ℓ s ^ 2 = ℓ ^ 2 - s ^ 2 := by
  have hsq : s ^ 2 < ℓ ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hℓ]
    exact hs
  exact Real.sq_sqrt (sub_nonneg.mpr hsq.le)

/-- Radial rapidity relative to the local hovering observer, positive outward.
`sinh ψ = −s/ρ`. -/
noncomputable def releasedRapidity (ℓ s : ℝ) : ℝ :=
  -Real.arsinh (s / releasedLocalRadius ℓ s)

theorem releasedRapidity_sinh {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : |s| < ℓ) :
    Real.sinh (releasedRapidity ℓ s) = -s / releasedLocalRadius ℓ s := by
  have _ := releasedLocalRadius_pos hℓ hs
  simp [releasedRapidity, sinh_neg, sinh_arsinh, neg_div]

theorem releasedRapidity_cosh {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : |s| < ℓ) :
    Real.cosh (releasedRapidity ℓ s) = ℓ / releasedLocalRadius ℓ s := by
  have hρ := releasedLocalRadius_pos hℓ hs
  rw [releasedRapidity, cosh_neg, cosh_arsinh]
  have hsum : 1 + (s / releasedLocalRadius ℓ s) ^ 2 =
      (ℓ / releasedLocalRadius ℓ s) ^ 2 := by
    field_simp [hρ.ne']
    rw [releasedLocalRadius_sq hℓ hs]
    ring
  rw [hsum, sqrt_sq (div_nonneg hℓ.le hρ.le)]

theorem releasedRapidity_zero {ℓ : ℝ} (hℓ : 0 < ℓ) : releasedRapidity ℓ 0 = 0 := by
  have hρ : releasedLocalRadius ℓ 0 = ℓ := by
    simp [releasedLocalRadius, sqrt_sq hℓ.le]
  simp [releasedRapidity, hρ, arsinh_zero]

/-- The flat radial coordinate accelerates exactly as the rapidity prescribes:
`dρ/ds = sinh ψ`. -/
theorem hasDerivAt_releasedLocalRadius {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : |s| < ℓ) :
    HasDerivAt (releasedLocalRadius ℓ) (Real.sinh (releasedRapidity ℓ s)) s := by
  have hlt : s ^ 2 < ℓ ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hℓ]
    exact hs
  have hpos : 0 < ℓ ^ 2 - s ^ 2 := sub_pos.mpr hlt
  have hmul : HasDerivAt (fun t : ℝ => t * t) (1 * s + s * 1) s :=
    (hasDerivAt_id s).mul (hasDerivAt_id s)
  have hsub : HasDerivAt (fun t => ℓ ^ 2 - t * t) (-(1 * s + s * 1)) s :=
    hmul.const_sub (ℓ ^ 2)
  have hpoly : HasDerivAt (fun t => ℓ ^ 2 - t ^ 2) (-(2 * s)) s := by
    have hfun : (fun t => ℓ ^ 2 - t ^ 2) = fun t => ℓ ^ 2 - t * t := by
      ext t
      ring
    rw [hfun]
    exact hsub.congr_deriv (by ring)
  have hsqrt := hpoly.sqrt hpos.ne'
  have hρ : HasDerivAt (releasedLocalRadius ℓ)
      ((-(2 * s)) / (2 * Real.sqrt (ℓ ^ 2 - s ^ 2))) s := by
    unfold releasedLocalRadius
    exact hsqrt
  refine hρ.congr_deriv ?_
  rw [releasedRapidity_sinh hℓ hs, releasedLocalRadius]
  field_simp [(Real.sqrt_pos.mpr hpos).ne']

/-- Flat rapidity law: `dψ/ds = − cosh ψ / ρ`. -/
theorem hasDerivAt_releasedRapidity {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : |s| < ℓ) :
    HasDerivAt (releasedRapidity ℓ)
      (-Real.cosh (releasedRapidity ℓ s) / releasedLocalRadius ℓ s) s := by
  have hρpos := releasedLocalRadius_pos hℓ hs
  have hρ := hasDerivAt_releasedLocalRadius hℓ hs
  have hdiv0 := (hasDerivAt_id s).div hρ hρpos.ne'
  have hdiv : HasDerivAt (fun t => t / releasedLocalRadius ℓ t)
      ((releasedLocalRadius ℓ s -
          s * Real.sinh (releasedRapidity ℓ s)) /
        releasedLocalRadius ℓ s ^ 2) s := by
    have hfun : (fun t => t / releasedLocalRadius ℓ t) = id / releasedLocalRadius ℓ := by
      ext t
      simp [id]
    rw [hfun]
    simpa [id_eq, one_mul] using hdiv0
  have hdiv' : HasDerivAt (fun t => t / releasedLocalRadius ℓ t)
      (ℓ ^ 2 / releasedLocalRadius ℓ s ^ 3) s := by
    refine hdiv.congr_deriv ?_
    rw [releasedRapidity_sinh hℓ hs]
    have hsq := releasedLocalRadius_sq hℓ hs
    have hne := hρpos.ne'
    calc
      (releasedLocalRadius ℓ s - s * (-s / releasedLocalRadius ℓ s)) /
          releasedLocalRadius ℓ s ^ 2
        = ((releasedLocalRadius ℓ s ^ 2 + s ^ 2) / releasedLocalRadius ℓ s) /
            releasedLocalRadius ℓ s ^ 2 := by
          congr 1
          field_simp [hne]
          ring
      _ = (releasedLocalRadius ℓ s ^ 2 + s ^ 2) /
            (releasedLocalRadius ℓ s * releasedLocalRadius ℓ s ^ 2) := by
          rw [div_div]
      _ = (releasedLocalRadius ℓ s ^ 2 + s ^ 2) / releasedLocalRadius ℓ s ^ 3 := by
          congr 1
          ring
      _ = (ℓ ^ 2 - s ^ 2 + s ^ 2) / releasedLocalRadius ℓ s ^ 3 := by
          rw [hsq]
      _ = ℓ ^ 2 / releasedLocalRadius ℓ s ^ 3 := by
          congr 1
          ring
  have harsinh :=
    (Real.hasDerivAt_arsinh (s / releasedLocalRadius ℓ s)).comp s hdiv'
  have hneg : HasDerivAt (fun t => -Real.arsinh (t / releasedLocalRadius ℓ t))
      (-((Real.sqrt (1 + (s / releasedLocalRadius ℓ s) ^ 2))⁻¹ *
        (ℓ ^ 2 / releasedLocalRadius ℓ s ^ 3))) s :=
    harsinh.neg
  have hfun : (fun t => -Real.arsinh (t / releasedLocalRadius ℓ t)) =
      releasedRapidity ℓ := rfl
  rw [hfun] at hneg
  refine hneg.congr_deriv ?_
  have hsqrt_eq : Real.sqrt (1 + (s / releasedLocalRadius ℓ s) ^ 2) =
      ℓ / releasedLocalRadius ℓ s := by
    have hsum : 1 + (s / releasedLocalRadius ℓ s) ^ 2 =
        (ℓ / releasedLocalRadius ℓ s) ^ 2 := by
      field_simp [hρpos.ne']
      rw [releasedLocalRadius_sq hℓ hs]
      ring
    rw [hsum, sqrt_sq (div_nonneg hℓ.le hρpos.le)]
  rw [hsqrt_eq, releasedRapidity_cosh hℓ hs]
  field_simp [hρpos.ne', hℓ.ne']

theorem deriv_releasedRapidity_zero {ℓ : ℝ} (hℓ : 0 < ℓ) :
    deriv (releasedRapidity ℓ) 0 = -1 / ℓ := by
  have h0 : |((0 : ℝ))| < ℓ := by simpa using hℓ
  rw [(hasDerivAt_releasedRapidity hℓ h0).deriv, releasedRapidity_cosh hℓ h0]
  have hρ : releasedLocalRadius ℓ 0 = ℓ := by
    simp [releasedLocalRadius, sqrt_sq hℓ.le]
  rw [hρ]
  field_simp [hℓ.ne']

/-- At release the rapidity law is the initial acceleration of the separation. -/
theorem deriv_releasedRapidity_zero_eq_initial {ℓ : ℝ} (hℓ : 0 < ℓ) :
    deriv (releasedRapidity ℓ) 0 =
      deriv (deriv (releasedDisplacementProper ℓ)) 0 := by
  rw [deriv_releasedRapidity_zero hℓ, released_initial_acceleration hℓ.ne']

end DstDiophantine.Gravity.KillingAxis

namespace DstDiophantine.Gravity.RadialFall

open Real Set Filter KillingAxis
open scoped Topology

/-! ### The chart: rapidity law with a changing radius -/

/-- Differentiating `√A sinh ψ` under the two laws yields the boost rate.
The `sinh²` term is the radial change of the redshift; the `cosh²` term is the
rapidity law; their difference is `1`. -/
theorem arealVelocity_hasDerivAt {rs : ℝ} {r ψ : ℝ → ℝ} {τ : ℝ}
    (hExt : IsExterior rs (r τ))
    (hr : HasDerivAt r (killingNorm rs (r τ) * Real.sinh (ψ τ)) τ)
    (hψ : HasDerivAt ψ (-Real.cosh (ψ τ) / axisDistance rs (r τ)) τ) :
    HasDerivAt (fun σ => killingNorm rs (r σ) * Real.sinh (ψ σ))
      (-killingRate rs (r τ)) τ := by
  set ℓ : ℝ := axisDistance rs (r τ)
  have hℓ : ℓ ≠ 0 := (axisDistance_pos hExt).ne'
  have hνr := (hasDerivAt_killingNorm hExt).comp τ hr
  have hsinh := (Real.hasDerivAt_sinh (ψ τ)).comp τ hψ
  have hprod := hνr.mul hsinh
  have hfun : (fun σ => killingNorm rs (r σ) * Real.sinh (ψ σ)) =ᶠ[𝓝 τ]
      (killingNorm rs ∘ r) * fun σ => Real.sinh (ψ σ) := by
    refine EventuallyEq.of_eq ?_
    ext σ
    simp [Function.comp]
  refine (hprod.congr_of_eventuallyEq hfun.symm).congr_deriv ?_
  have hνℓ : killingNorm rs (r τ) / ℓ = killingRate rs (r τ) := by
    rw [div_eq_iff hℓ]
    exact (killingRate_mul_axisDistance hExt).symm
  have hd : dSqrtA_dr rs (r τ) = 1 / ℓ := by
    rw [eq_div_iff hℓ, mul_comm]
    exact axisDistance_mul_dSqrtA_dr hExt
  have hcosh := Real.cosh_sq_sub_sinh_sq (ψ τ)
  simp only [Function.comp]
  rw [hd]
  have hstep :
      (1 / ℓ) * (killingNorm rs (r τ) * Real.sinh (ψ τ)) * Real.sinh (ψ τ) +
        killingNorm rs (r τ) *
          (Real.cosh (ψ τ) * (-Real.cosh (ψ τ) / ℓ)) =
        -(killingNorm rs (r τ) / ℓ) := by
    have hdiff : Real.sinh (ψ τ) ^ 2 - Real.cosh (ψ τ) ^ 2 = -1 := by
      linarith [hcosh]
    calc
      (1 / ℓ) * (killingNorm rs (r τ) * Real.sinh (ψ τ)) * Real.sinh (ψ τ) +
          killingNorm rs (r τ) *
            (Real.cosh (ψ τ) * (-Real.cosh (ψ τ) / ℓ))
        = (killingNorm rs (r τ) / ℓ) *
            (Real.sinh (ψ τ) ^ 2 - Real.cosh (ψ τ) ^ 2) := by ring
      _ = (killingNorm rs (r τ) / ℓ) * (-1) := by rw [hdiff]
      _ = -(killingNorm rs (r τ) / ℓ) := by ring
  rw [hstep, hνℓ]

/-- `E = √A cosh ψ` is stationary: redshift and rapidity trade exactly. -/
theorem radialEnergy_hasDerivAt {rs : ℝ} {r ψ : ℝ → ℝ} {τ : ℝ}
    (hExt : IsExterior rs (r τ))
    (hr : HasDerivAt r (killingNorm rs (r τ) * Real.sinh (ψ τ)) τ)
    (hψ : HasDerivAt ψ (-Real.cosh (ψ τ) / axisDistance rs (r τ)) τ) :
    HasDerivAt (fun σ => killingNorm rs (r σ) * Real.cosh (ψ σ)) 0 τ := by
  set ℓ : ℝ := axisDistance rs (r τ)
  have hℓ : ℓ ≠ 0 := (axisDistance_pos hExt).ne'
  have hνr := (hasDerivAt_killingNorm hExt).comp τ hr
  have hcosh := (Real.hasDerivAt_cosh (ψ τ)).comp τ hψ
  have hprod := hνr.mul hcosh
  have hfun : (fun σ => killingNorm rs (r σ) * Real.cosh (ψ σ)) =ᶠ[𝓝 τ]
      (killingNorm rs ∘ r) * fun σ => Real.cosh (ψ σ) := by
    refine EventuallyEq.of_eq ?_
    ext σ
    simp [Function.comp]
  refine (hprod.congr_of_eventuallyEq hfun.symm).congr_deriv ?_
  have hd : dSqrtA_dr rs (r τ) = 1 / ℓ := by
    rw [eq_div_iff hℓ, mul_comm]
    exact axisDistance_mul_dSqrtA_dr hExt
  simp only [Function.comp]
  rw [hd]
  field_simp [hℓ]
  ring

theorem arealVelocity_sq_eq_energy {rs r₀ ψ₀ : ℝ} (h : IsExterior rs r₀) :
    (killingNorm rs r₀ * Real.sinh ψ₀) ^ 2 =
      (killingNorm rs r₀ * Real.cosh ψ₀) ^ 2 - schwarzschildA rs r₀ := by
  have hsq : killingNorm rs r₀ ^ 2 = schwarzschildA rs r₀ :=
    Real.sq_sqrt (schwarzschildA_pos h).le
  have hid := Real.cosh_sq_sub_sinh_sq ψ₀
  have hsinh : Real.sinh ψ₀ ^ 2 = Real.cosh ψ₀ ^ 2 - 1 := by
    linarith [hid]
  calc (killingNorm rs r₀ * Real.sinh ψ₀) ^ 2
      = killingNorm rs r₀ ^ 2 * Real.sinh ψ₀ ^ 2 := by ring
    _ = killingNorm rs r₀ ^ 2 * (Real.cosh ψ₀ ^ 2 - 1) := by rw [hsinh]
    _ = killingNorm rs r₀ ^ 2 * Real.cosh ψ₀ ^ 2 - killingNorm rs r₀ ^ 2 := by ring
    _ = (killingNorm rs r₀ * Real.cosh ψ₀) ^ 2 - schwarzschildA rs r₀ := by
        rw [← hsq]
        ring

/-- On a proper-time interval the integrated energy is independent of the instant. -/
theorem radialEnergy_eq_on {rs a b : ℝ} {r ψ : ℝ → ℝ} (hab : a ≤ b)
    (hExt : ∀ τ ∈ Icc a b, IsExterior rs (r τ))
    (hr : ∀ τ ∈ Icc a b,
      HasDerivAt r (killingNorm rs (r τ) * Real.sinh (ψ τ)) τ)
    (hψ : ∀ τ ∈ Icc a b,
      HasDerivAt ψ (-Real.cosh (ψ τ) / axisDistance rs (r τ)) τ)
    {τ₁ τ₂ : ℝ} (h₁ : τ₁ ∈ Icc a b) (h₂ : τ₂ ∈ Icc a b) :
    killingNorm rs (r τ₁) * Real.cosh (ψ τ₁) =
      killingNorm rs (r τ₂) * Real.cosh (ψ τ₂) := by
  have : a ≤ b := hab
  let E : ℝ → ℝ := fun σ => killingNorm rs (r σ) * Real.cosh (ψ σ)
  have hE : ∀ σ ∈ Icc a b, HasDerivAt E 0 σ := fun σ hσ =>
    radialEnergy_hasDerivAt (hExt σ hσ) (hr σ hσ) (hψ σ hσ)
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

/-- The first integral of the rapidity law is the radial Schwarzschild fall. -/
theorem radialFall_first_integral {rs a b : ℝ} {r ψ : ℝ → ℝ} (hab : a ≤ b)
    (hExt : ∀ τ ∈ Icc a b, IsExterior rs (r τ))
    (hr : ∀ τ ∈ Icc a b,
      HasDerivAt r (killingNorm rs (r τ) * Real.sinh (ψ τ)) τ)
    (hψ : ∀ τ ∈ Icc a b,
      HasDerivAt ψ (-Real.cosh (ψ τ) / axisDistance rs (r τ)) τ)
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ Icc a b) (hτ : τ ∈ Icc a b) :
    (deriv r τ) ^ 2 =
      (killingNorm rs (r τ₀) * Real.cosh (ψ τ₀)) ^ 2 - schwarzschildA rs (r τ) := by
  have hE := radialEnergy_eq_on hab hExt hr hψ hτ h₀
  have hv := (hr τ hτ).deriv
  rw [hv]
  have hsq := arealVelocity_sq_eq_energy (ψ₀ := ψ τ) (hExt τ hτ)
  rwa [hE] at hsq

/-- Released from rest, the constant is the redshift at the point of release. -/
theorem radialFall_from_rest {rs a b : ℝ} {r ψ : ℝ → ℝ} (hab : a ≤ b)
    (hExt : ∀ τ ∈ Icc a b, IsExterior rs (r τ))
    (hr : ∀ τ ∈ Icc a b,
      HasDerivAt r (killingNorm rs (r τ) * Real.sinh (ψ τ)) τ)
    (hψ : ∀ τ ∈ Icc a b,
      HasDerivAt ψ (-Real.cosh (ψ τ) / axisDistance rs (r τ)) τ)
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ Icc a b) (hτ : τ ∈ Icc a b) (hrest : ψ τ₀ = 0) :
    (deriv r τ) ^ 2 = schwarzschildA rs (r τ₀) - schwarzschildA rs (r τ) := by
  rw [radialFall_first_integral hab hExt hr hψ h₀ hτ, hrest, Real.cosh_zero, mul_one]
  rw [show killingNorm rs (r τ₀) ^ 2 = schwarzschildA rs (r τ₀) from
    Real.sq_sqrt (schwarzschildA_pos (hExt τ₀ h₀)).le]

/-- Where the two laws hold on an open interval, the areal acceleration is `−κ`. -/
theorem radialFall_second_deriv {rs a b : ℝ} {r ψ : ℝ → ℝ} (hab : a < b)
    (hExt : ∀ τ ∈ Ioo a b, IsExterior rs (r τ))
    (hr : ∀ τ ∈ Ioo a b,
      HasDerivAt r (killingNorm rs (r τ) * Real.sinh (ψ τ)) τ)
    (hψ : ∀ τ ∈ Ioo a b,
      HasDerivAt ψ (-Real.cosh (ψ τ) / axisDistance rs (r τ)) τ)
    {τ : ℝ} (hτ : τ ∈ Ioo a b) :
    deriv (deriv r) τ = -killingRate rs (r τ) := by
  have _ : a < b := hab
  have hv := arealVelocity_hasDerivAt (hExt τ hτ) (hr τ hτ) (hψ τ hτ)
  have hEq : (fun σ => killingNorm rs (r σ) * Real.sinh (ψ σ)) =ᶠ[𝓝 τ] deriv r := by
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with σ hσ
    exact (hr σ hσ).deriv.symm
  exact (hv.congr_of_eventuallyEq hEq.symm).deriv

end DstDiophantine.Gravity.RadialFall
