import DstDiophantine.Gravity.KillingAxis
import DstDiophantine.Algebra.Amplification
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Flat transport of a Poincaré bivector along an arbitrary curve

Rewriting a fixed bivector at a displaced origin is conjugation by the
translator of that displacement. For every Poincaré bivector and every
displacement `x`, the Lorentz part is unchanged and the translational part
becomes the velocity field `λ + ω x`. Along a differentiable curve the
translational part therefore changes at the rate `ω(ẋ)`, whether or not the
curve is an orbit of the bivector. The torsional scalar `J` is constant.
The squared norm `N²` moves with the event.

On the exterior the boost rate `κ = rₛ/(2r²)` has radial derivative
`-rₛ/r³`. Static bivectors at two exterior radii are not flat transports of
one another.

## Not claimed

* Motion off the equatorial leg, or an identification of the bivector with
  the torsional mismatch of the parent theory. The Levi-Civita action on
  the static bivector is `Gravity.CurvedTransport`.
-/

namespace DstDiophantine.Gravity.KillingTransport

open PGA Generators Operations Motor Amplification Invariant LorentzLie
open Sandwich (sandwich)
open KillingAxis (sandwich_expTrans killingNormSq killingParams killingRate killingNorm
  lorentzAct commutator_omegaTorsion_minkowskiVector omegaTrans_eq_half_e4)

/-- Translator that moves the origin to `x`: events shift by `-x`. -/
def originShift (x : Vec4) : TransParams :=
  ⟨fun μ => -x μ⟩

/-- Bivector rewritten at the origin `x`: same torsion, velocity field as translation. -/
def transportedParams (p : OmegaParams) (x : Vec4) : OmegaParams where
  torsion := p.torsion
  trans := ⟨fun μ => p.trans.lambda μ + lorentzAct p.torsion x μ⟩

theorem lorentzAct_zero (t : TorsionParams) : lorentzAct t 0 = 0 := by
  ext μ
  fin_cases μ <;> simp [lorentzAct]

theorem lorentzAct_neg (t : TorsionParams) (x : Vec4) :
    lorentzAct t (-x) = -lorentzAct t x := by
  ext μ
  fin_cases μ <;> simp [lorentzAct, Pi.neg_apply] <;> ring

theorem lorentzAct_add (t : TorsionParams) (x y : Vec4) :
    lorentzAct t (x + y) = lorentzAct t x + lorentzAct t y := by
  ext μ
  fin_cases μ <;> simp [lorentzAct, Pi.add_apply] <;> ring

theorem omegaTrans_neg_lambda (q : TransParams) :
    omegaTrans ⟨fun μ => -q.lambda μ⟩ = -omegaTrans q := by
  simp only [omegaTrans, neg_div, neg_smul, Finset.sum_neg_distrib]

theorem commutator_omegaTrans_omegaTrans (p q : TransParams) :
    commutator (omegaTrans p) (omegaTrans q) = 0 := by
  rw [Generators.commutator, omegaTrans_mul, omegaTrans_mul, sub_zero]

/-- `[Ω_torsion, Ω_trans(λ)]` is the translation by the Lorentz action on `λ`. -/
theorem commutator_omegaTorsion_omegaTrans (t : TorsionParams) (q : TransParams) :
    commutator (omegaTorsion t) (omegaTrans q) =
      omegaTrans ⟨lorentzAct t q.lambda⟩ := by
  rw [omegaTrans_eq_half_e4, commutator_smul_right]
  have hcomm : omegaTorsion t * ι e4Index = ι e4Index * omegaTorsion t :=
    (KillingAxis.commute_e4_of_mem_lorentzSpan (omegaTorsion_mem_lorentzSpan t)).symm.eq
  have hbr : commutator (omegaTorsion t) (ι e4Index * minkowskiVector q.lambda) =
      ι e4Index * minkowskiVector (lorentzAct t q.lambda) := by
    rw [Generators.commutator]
    calc
      omegaTorsion t * (ι e4Index * minkowskiVector q.lambda) -
          ι e4Index * minkowskiVector q.lambda * omegaTorsion t
        = ι e4Index * (omegaTorsion t * minkowskiVector q.lambda) -
            ι e4Index * (minkowskiVector q.lambda * omegaTorsion t) := by
          rw [← mul_assoc, hcomm]
          simp [mul_assoc]
      _ = ι e4Index * (omegaTorsion t * minkowskiVector q.lambda -
            minkowskiVector q.lambda * omegaTorsion t) := by
          rw [mul_sub]
      _ = ι e4Index * minkowskiVector (lorentzAct t q.lambda) := by
          rw [← Generators.commutator, commutator_omegaTorsion_minkowskiVector]
  rw [hbr, ← omegaTrans_eq_half_e4]

/-- Moving the origin to `x` replaces the translation by the velocity field. -/
theorem sandwich_originShift (p : OmegaParams) (x : Vec4) :
    sandwich (expTrans (originShift x)) (omegaBiv p) =
      omegaBiv (transportedParams p x) := by
  rw [sandwich_expTrans, omegaBiv, commutator_add_right,
    commutator_omegaTrans_omegaTrans, add_zero]
  rw [commutator_neg, commutator_omegaTorsion_omegaTrans]
  have hfun : (originShift x).lambda = -x := by
    ext μ
    simp [originShift]
  have hact : lorentzAct p.torsion (originShift x).lambda = -lorentzAct p.torsion x := by
    rw [hfun]
    exact lorentzAct_neg p.torsion x
  rw [hact]
  have hsame : omegaTrans ⟨-lorentzAct p.torsion x⟩ =
      -omegaTrans ⟨lorentzAct p.torsion x⟩ := by
    simp only [omegaTrans, Pi.neg_apply, neg_div, neg_smul, Finset.sum_neg_distrib]
  rw [hsame, neg_neg]
  have hadd := omegaTrans_add p.trans ⟨lorentzAct p.torsion x⟩
  rw [add_assoc, hadd, omegaBiv]
  congr 1

theorem transported_torsion (p : OmegaParams) (x : Vec4) :
    (transportedParams p x).torsion = p.torsion := rfl

theorem transported_lambda (p : OmegaParams) (x : Vec4) (μ : Fin 4) :
    (transportedParams p x).trans.lambda μ =
      p.trans.lambda μ + lorentzAct p.torsion x μ := rfl

/-- The torsional scalar is invariant under the transport. -/
theorem J_transported (p : OmegaParams) (x : Vec4) :
    J (transportedParams p x).torsion = J p.torsion := rfl

/-- At the new origin the squared norm equals the old norm at `x`. -/
theorem killingNormSq_at_new_origin (p : OmegaParams) (x : Vec4) :
    killingNormSq (transportedParams p x) 0 = killingNormSq p x := by
  have hfun : (fun μ => p.trans.lambda μ + lorentzAct p.torsion x μ) =
      p.trans.lambda + lorentzAct p.torsion x := by
    ext μ
    rfl
  simp [killingNormSq, transportedParams, lorentzAct_zero, hfun, add_zero]

/-- Along the radial line the transported translation is the velocity `(ν + κ s) e₀`. -/
theorem transported_killing_radial (κ ν s : ℝ) :
    (transportedParams (killingParams κ ν) ![0, s, 0, 0]).trans.lambda =
      ![ν + κ * s, 0, 0, 0] := by
  ext μ
  fin_cases μ <;> simp [transportedParams, killingParams, lorentzAct, pureBoost]

/-- Flat transport does not change the boost rate. -/
theorem transported_killing_torsion (κ ν : ℝ) (x : Vec4) :
    (transportedParams (killingParams κ ν) x).torsion = pureBoost κ := rfl

/-! ### Derivative along an arbitrary differentiable curve -/

theorem hasDerivAt_lorentzAct (t : TorsionParams) {x : ℝ → Vec4} {v : Vec4} {τ : ℝ}
    (hx : ∀ μ, HasDerivAt (fun s => x s μ) (v μ) τ) (μ : Fin 4) :
    HasDerivAt (fun s => lorentzAct t (x s) μ) (lorentzAct t v μ) τ := by
  fin_cases μ
  · change HasDerivAt (fun s => t.alpha 0 * x s 1 + t.alpha 1 * x s 2 + t.alpha 2 * x s 3)
        (t.alpha 0 * v 1 + t.alpha 1 * v 2 + t.alpha 2 * v 3) τ
    have h := ((hx 1).const_mul (t.alpha 0)).add
      (((hx 2).const_mul (t.alpha 1)).add ((hx 3).const_mul (t.alpha 2)))
    convert h using 1
    · ext s
      simp only [Pi.add_apply]
      ring
    · ring
  · change HasDerivAt (fun s => t.alpha 0 * x s 0 - t.beta 2 * x s 2 + t.beta 1 * x s 3)
        (t.alpha 0 * v 0 - t.beta 2 * v 2 + t.beta 1 * v 3) τ
    have h := ((hx 0).const_mul (t.alpha 0)).add
      (((hx 2).const_mul (-t.beta 2)).add ((hx 3).const_mul (t.beta 1)))
    convert h using 1
    · ext s
      simp only [Pi.add_apply]
      ring
    · ring
  · change HasDerivAt (fun s => t.alpha 1 * x s 0 + t.beta 2 * x s 1 - t.beta 0 * x s 3)
        (t.alpha 1 * v 0 + t.beta 2 * v 1 - t.beta 0 * v 3) τ
    have h := ((hx 0).const_mul (t.alpha 1)).add
      (((hx 1).const_mul (t.beta 2)).add ((hx 3).const_mul (-t.beta 0)))
    convert h using 1
    · ext s
      simp only [Pi.add_apply]
      ring
    · ring
  · change HasDerivAt (fun s => t.alpha 2 * x s 0 - t.beta 1 * x s 1 + t.beta 0 * x s 2)
        (t.alpha 2 * v 0 - t.beta 1 * v 1 + t.beta 0 * v 2) τ
    have h := ((hx 0).const_mul (t.alpha 2)).add
      (((hx 1).const_mul (-t.beta 1)).add ((hx 2).const_mul (t.beta 0)))
    convert h using 1
    · ext s
      simp only [Pi.add_apply]
      ring
    · ring

/-- Along any differentiable curve, `dλ/dτ = ω(ẋ)`. The curve need not be an orbit. -/
theorem hasDerivAt_transportedLambda (p : OmegaParams) {x : ℝ → Vec4} {v : Vec4} {τ : ℝ}
    (hx : ∀ μ, HasDerivAt (fun s => x s μ) (v μ) τ) (μ : Fin 4) :
    HasDerivAt (fun s => (transportedParams p (x s)).trans.lambda μ)
      (lorentzAct p.torsion v μ) τ := by
  have hconst : HasDerivAt (fun _ : ℝ => p.trans.lambda μ) 0 τ := hasDerivAt_const τ _
  have h := hconst.add (hasDerivAt_lorentzAct p.torsion hx μ)
  convert h using 1
  · ext s
    simp [transportedParams]
  · simp

theorem transported_torsion_const (p : OmegaParams) (x y : Vec4) :
    (transportedParams p x).torsion = (transportedParams p y).torsion := rfl

/-! ### The exterior rate is not a flat transport -/

theorem hasDerivAt_killingRate (rs : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (killingRate rs) (-(rs / r ^ 3)) r := by
  have hfun : killingRate rs = fun x => (rs / 2) * (x ^ 2)⁻¹ := by
    ext x
    simp [killingRate, div_eq_mul_inv]
    ring
  rw [hfun]
  have hsq : HasDerivAt (fun x => x ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hne : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hinv := hsq.inv hne
  have h := hinv.const_mul (rs / 2)
  refine h.congr_deriv ?_
  have hr2 : (r ^ 2) ^ 2 = r ^ 4 := by ring
  rw [hr2]
  field_simp

theorem killingRate_radial_deriv_ne {rs r : ℝ} (hrs : rs ≠ 0) (hr : r ≠ 0) :
    -(rs / r ^ 3) ≠ 0 := by
  intro h
  have : rs / r ^ 3 = 0 := by linarith
  exact hrs ((div_eq_zero_iff.mp this).resolve_right (pow_ne_zero 3 hr))

theorem killingRate_ne_of_exterior {rs r₁ r₂ : ℝ}
    (h₁ : IsExterior rs r₁) (h₂ : IsExterior rs r₂) (hne : r₁ ≠ r₂) :
    killingRate rs r₁ ≠ killingRate rs r₂ := by
  intro h
  have hrs : rs ≠ 0 := h₁.1.ne'
  have hr₁ : r₁ ≠ 0 := (lt_trans h₁.1 h₁.2).ne'
  have hr₂ : r₂ ≠ 0 := (lt_trans h₂.1 h₂.2).ne'
  have hsq : r₁ ^ 2 = r₂ ^ 2 := by
    have h' : rs / (2 * r₁ ^ 2) = rs / (2 * r₂ ^ 2) := by simpa [killingRate] using h
    field_simp at h'
    linarith
  have habs : |r₁| = |r₂| := by
    rw [← sq_eq_sq_iff_abs_eq_abs]
    simpa using hsq
  have hpos₁ : 0 < r₁ := lt_trans h₁.1 h₁.2
  have hpos₂ : 0 < r₂ := lt_trans h₂.1 h₂.2
  exact hne (by linarith [abs_of_pos hpos₁, abs_of_pos hpos₂, habs])

/-- No flat displacement carries the static bivector at one exterior radius
to the static bivector at another. The torsional part would have to agree,
and flat transport does not change it. -/
theorem static_not_flat_transport {rs r₁ r₂ : ℝ}
    (h₁ : IsExterior rs r₁) (h₂ : IsExterior rs r₂) (hne : r₁ ≠ r₂) (x : Vec4) :
    (transportedParams (killingParams (killingRate rs r₁) (killingNorm rs r₁)) x).torsion ≠
      pureBoost (killingRate rs r₂) := by
  intro h
  rw [transported_killing_torsion] at h
  have hrate : killingRate rs r₁ = killingRate rs r₂ := by
    have hα := congrArg (fun t : TorsionParams => t.alpha 0) h
    simpa [pureBoost] using hα
  exact killingRate_ne_of_exterior h₁ h₂ hne hrate

end DstDiophantine.Gravity.KillingTransport
