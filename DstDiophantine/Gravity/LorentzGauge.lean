import DstDiophantine.Gravity.Coframe
import DstDiophantine.Gravity.Weitzenbock
import DstDiophantine.Gravity.JTDictionary
import DstDiophantine.Algebra.Amplification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Inertial-boost gauge: metric, torsion, and the teleparallel scalar

Boost the inertial coframe in the fixed `(t,x)` plane by a rapidity `φ`.
The partials below are the 1-jet of a profile `φ(t,x)`: `u = ∂_t φ`, `v = ∂_x φ`.

## Proved

* The induced metric is Minkowski for every `φ`. The `(t,x)` block has
  determinant `1`.
* Coordinate torsion of the jet is
  `T^t_{tx} = u`, `T^t_{xt} = -u`, `T^x_{tx} = -v`, `T^x_{xt} = v`,
  and every other component vanishes. It remembers `(u,v)` and forgets `φ`.
* The teleparallel quadratic of the parent paper,
  `T = ¼ T_{ρμν} T^{ρμν} + ½ T_{ρμν} T^{νμρ} - T_ρ T^ρ`,
  with indices moved by `η`, vanishes for every jet.
* The same algebraic value `J = ½ φ²` occurs on an exterior Schwarzschild
  coframe with `T > 0`. No pointwise map `J ↦ T` serves every tetrad.
* Two rapidities with distinct squares induce the same metric and distinct `J`.

## Not claimed

* A dictionary for a general motor (translations, or a rotor about a moving axis).
* Vanishing of `T` for an arbitrary local Lorentz transformation.
* The variational identity between `∫ e T` and the Einstein--Hilbert action.
-/

namespace DstDiophantine

namespace Gravity

open Invariant Amplification Real Finset

/-! ### Coframe and inverse frame -/

/-- Inertial coframe boosted by rapidity `φ` in the `(t,x)` plane. -/
noncomputable def inertialBoostCoframe (φ : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 0 then Real.cosh φ
    else if a = 0 ∧ μ = 1 then Real.sinh φ
    else if a = 1 ∧ μ = 0 then Real.sinh φ
    else if a = 1 ∧ μ = 1 then Real.cosh φ
    else if a = μ then 1
    else 0

/-- Inverse frame `e_a^μ` of `inertialBoostCoframe`. -/
noncomputable def inertialBoostFrame (φ : ℝ) (μ a : Fin 4) : ℝ :=
  if a = 0 ∧ μ = 0 then Real.cosh φ
  else if a = 0 ∧ μ = 1 then -Real.sinh φ
  else if a = 1 ∧ μ = 0 then -Real.sinh φ
  else if a = 1 ∧ μ = 1 then Real.cosh φ
  else if a = μ then 1
  else 0

theorem w31_sq (a : Fin 4) : w31 a ^ 2 = 1 := by
  fin_cases a <;> simp [w31]

theorem inertialBoost_blockDet (φ : ℝ) :
    inertialBoostCoframe φ 0 0 * inertialBoostCoframe φ 1 1 -
        inertialBoostCoframe φ 0 1 * inertialBoostCoframe φ 1 0 = 1 := by
  simp [inertialBoostCoframe]
  ring_nf
  exact Real.cosh_sq_sub_sinh_sq φ

/-- The boosted coframe induces the Minkowski metric, for every rapidity. -/
theorem inducedMetric_inertialBoost (φ : ℝ) (μ ν : Fin 4) :
    inducedMetric (inertialBoostCoframe φ) μ ν =
      if μ = ν then w31 μ else 0 := by
  rw [inducedMetric_eq_weighted]
  have h := Real.cosh_sq_sub_sinh_sq φ
  fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, inertialBoostCoframe, w31] <;>
    ring_nf <;> linarith

/-- Frame and coframe are dual. -/
theorem inertialBoost_dual (φ : ℝ) (μ ν : Fin 4) :
    ∑ a : Fin 4, inertialBoostCoframe φ a μ * inertialBoostFrame φ ν a =
      if μ = ν then (1 : ℝ) else 0 := by
  have h := Real.cosh_sq_sub_sinh_sq φ
  fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, inertialBoostCoframe, inertialBoostFrame] <;>
    ring_nf <;> linarith

/-! ### 1-jet and coordinate torsion -/

/-- Jet `(∂_t φ, ∂_x φ) = (u, v)` on the boosted plane; transverse derivatives vanish. -/
def derivJet (u v : ℝ) : Fin 4 → ℝ
  | 0 => u
  | 1 => v
  | _ => 0

/-- `∂_φ` of the boosted coframe. -/
noncomputable def dφCoframe (φ : ℝ) (a ν : Fin 4) : ℝ :=
  if a = 0 ∧ ν = 0 then Real.sinh φ
  else if a = 0 ∧ ν = 1 then Real.cosh φ
  else if a = 1 ∧ ν = 0 then Real.cosh φ
  else if a = 1 ∧ ν = 1 then Real.sinh φ
  else 0

/-- Partials `∂_λ e^a_ν = (∂_λ φ) · ∂_φ e^a_ν`. -/
noncomputable def inertialBoostPartials (φ u v : ℝ) : CoframePartials :=
  fun dir a ν => derivJet u v dir * dφCoframe φ a ν

/-- Boost generator on the coordinate basis: the off-diagonal `(t,x)` swap. -/
def boostGen (ρ ν : Fin 4) : ℝ :=
  if ρ = 0 ∧ ν = 1 then 1 else if ρ = 1 ∧ ν = 0 then 1 else 0

theorem frame_mul_dφ (φ : ℝ) (ρ ν : Fin 4) :
    ∑ a : Fin 4, inertialBoostFrame φ ρ a * dφCoframe φ a ν = boostGen ρ ν := by
  have h := Real.cosh_sq_sub_sinh_sq φ
  fin_cases ρ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, inertialBoostFrame, dφCoframe, boostGen] <;>
    ring_nf <;> linarith

/-- Coordinate torsion `T^ρ_{μν} = e_a^ρ T^a_{μν}`. -/
noncomputable def boostCoordTorsion (φ u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  ∑ a : Fin 4,
    inertialBoostFrame φ ρ a *
      weitzenbockTorsion (inertialBoostPartials φ u v) a μ ν

/-- Closed form: `T^ρ_{μν} = (∂_μ φ) K^ρ_ν - (∂_ν φ) K^ρ_μ`. Independent of `φ`. -/
theorem boostCoordTorsion_eq_jet (φ u v : ℝ) (ρ μ ν : Fin 4) :
    boostCoordTorsion φ u v ρ μ ν =
      derivJet u v μ * boostGen ρ ν - derivJet u v ν * boostGen ρ μ := by
  unfold boostCoordTorsion weitzenbockTorsion inertialBoostPartials
  have hlin :
      ∀ a,
        inertialBoostFrame φ ρ a *
            (derivJet u v μ * dφCoframe φ a ν - derivJet u v ν * dφCoframe φ a μ) =
          derivJet u v μ * (inertialBoostFrame φ ρ a * dφCoframe φ a ν) -
            derivJet u v ν * (inertialBoostFrame φ ρ a * dφCoframe φ a μ) := by
    intro a
    ring
  simp_rw [hlin, sum_sub_distrib]
  have hμ :
      ∑ a : Fin 4, derivJet u v μ * (inertialBoostFrame φ ρ a * dφCoframe φ a ν) =
        derivJet u v μ *
          ∑ a : Fin 4, inertialBoostFrame φ ρ a * dφCoframe φ a ν := by
    rw [← Finset.mul_sum]
  have hν :
      ∑ a : Fin 4, derivJet u v ν * (inertialBoostFrame φ ρ a * dφCoframe φ a μ) =
        derivJet u v ν *
          ∑ a : Fin 4, inertialBoostFrame φ ρ a * dφCoframe φ a μ := by
    rw [← Finset.mul_sum]
  rw [hμ, hν, frame_mul_dφ, frame_mul_dφ]

theorem boostCoordTorsion_ttx (φ u v : ℝ) :
    boostCoordTorsion φ u v 0 0 1 = u := by
  rw [boostCoordTorsion_eq_jet]
  simp [derivJet, boostGen]

theorem boostCoordTorsion_xxt (φ u v : ℝ) :
    boostCoordTorsion φ u v 1 1 0 = v := by
  rw [boostCoordTorsion_eq_jet]
  simp [derivJet, boostGen]

theorem boostCoordTorsion_ne_zero_of_time (φ u v : ℝ) (hu : u ≠ 0) :
    boostCoordTorsion φ u v 0 0 1 ≠ 0 := by
  rw [boostCoordTorsion_ttx]
  exact hu

/-! ### Teleparallel quadratic -/

/-- Upper coordinate torsion in the closed form, written without `φ`. -/
def boostTorsionUp (u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  derivJet u v μ * boostGen ρ ν - derivJet u v ν * boostGen ρ μ

theorem boostCoordTorsion_eq_up (φ u v : ℝ) (ρ μ ν : Fin 4) :
    boostCoordTorsion φ u v ρ μ ν = boostTorsionUp u v ρ μ ν := by
  rw [boostCoordTorsion_eq_jet]
  rfl

/-- `T_{ρμν} = η_{ρρ} T^ρ_{μν}`. -/
def boostTdown (u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * boostTorsionUp u v ρ μ ν

/-- `T^{ρμν}`, indices raised by `η`. -/
def boostTup (u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * w31 μ * w31 ν * boostTdown u v ρ μ ν

/-- Trace `T_ρ = T^σ_{ρσ}`. -/
def boostTrace (u v : ℝ) (ρ : Fin 4) : ℝ :=
  ∑ σ : Fin 4, boostTorsionUp u v σ ρ σ

/-- Raised trace `T^ρ = η^{ρρ} T_ρ`. -/
def boostTraceUp (u v : ℝ) (ρ : Fin 4) : ℝ :=
  w31 ρ * boostTrace u v ρ

/-- Teleparallel scalar `¼ T_{ρμν}T^{ρμν} + ½ T_{ρμν}T^{νμρ} - T_ρ T^ρ`. -/
noncomputable def boostTeleparallel (u v : ℝ) : ℝ :=
  (1 / 4) * (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      boostTdown u v ρ μ ν * boostTup u v ρ μ ν) +
    (1 / 2) * (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      boostTdown u v ρ μ ν * boostTup u v ν μ ρ) -
    ∑ ρ : Fin 4, boostTrace u v ρ * boostTraceUp u v ρ

private lemma sum4_of_high {f : Fin 4 → ℝ} (h2 : f 2 = 0) (h3 : f 3 = 0) :
    ∑ i : Fin 4, f i = f 0 + f 1 := by
  rw [Fin.sum_univ_four]
  simp [h2, h3]

private lemma up_eq_zero_of_high_ρ {u v : ℝ} {ρ μ ν : Fin 4} (h : ρ ≠ 0 ∧ ρ ≠ 1) :
    boostTorsionUp u v ρ μ ν = 0 := by
  simp only [boostTorsionUp, boostGen]
  fin_cases ρ <;> simp_all

private lemma up_eq_zero_of_high_μ {u v : ℝ} {ρ μ ν : Fin 4} (h : μ ≠ 0 ∧ μ ≠ 1) :
    boostTorsionUp u v ρ μ ν = 0 := by
  have hμ : derivJet u v μ = 0 := by
    fin_cases μ <;> simp_all [derivJet]
  have hgen : boostGen ρ μ = 0 := by
    simp only [boostGen]
    fin_cases μ <;> simp_all
  simp [boostTorsionUp, hμ, hgen]

private lemma up_eq_zero_of_high_ν {u v : ℝ} {ρ μ ν : Fin 4} (h : ν ≠ 0 ∧ ν ≠ 1) :
    boostTorsionUp u v ρ μ ν = 0 := by
  have hν : derivJet u v ν = 0 := by
    fin_cases ν <;> simp_all [derivJet]
  have hgen : boostGen ρ ν = 0 := by
    simp only [boostGen]
    fin_cases ν <;> simp_all
  simp [boostTorsionUp, hν, hgen]

private lemma squareTerm_high {u v : ℝ} {ρ μ ν : Fin 4}
    (h : (ρ ≠ 0 ∧ ρ ≠ 1) ∨ (μ ≠ 0 ∧ μ ≠ 1) ∨ (ν ≠ 0 ∧ ν ≠ 1)) :
    boostTdown u v ρ μ ν * boostTup u v ρ μ ν = 0 := by
  rcases h with hρ | hμ | hν
  · simp [boostTdown, boostTup, up_eq_zero_of_high_ρ hρ]
  · simp [boostTdown, boostTup, up_eq_zero_of_high_μ hμ]
  · simp [boostTdown, boostTup, up_eq_zero_of_high_ν hν]

private lemma crossTerm_high {u v : ℝ} {ρ μ ν : Fin 4}
    (h : (ρ ≠ 0 ∧ ρ ≠ 1) ∨ (μ ≠ 0 ∧ μ ≠ 1) ∨ (ν ≠ 0 ∧ ν ≠ 1)) :
    boostTdown u v ρ μ ν * boostTup u v ν μ ρ = 0 := by
  rcases h with hρ | hμ | hν
  · simp [boostTdown, up_eq_zero_of_high_ρ hρ]
  · have h1 : boostTorsionUp u v ρ μ ν = 0 := up_eq_zero_of_high_μ hμ
    have h2 : boostTorsionUp u v ν μ ρ = 0 := by
      simpa using up_eq_zero_of_high_μ (u := u) (v := v) (ρ := ν) (μ := μ) (ν := ρ) hμ
    simp [boostTdown, boostTup, h1, h2]
  · have h1 : boostTorsionUp u v ρ μ ν = 0 := up_eq_zero_of_high_ν hν
    have h2 : boostTorsionUp u v ν μ ρ = 0 := by
      simpa using up_eq_zero_of_high_ρ (u := u) (v := v) (ρ := ν) (μ := μ) (ν := ρ) hν
    simp [boostTdown, boostTup, h1, h2]

private lemma plane_ne (i : Fin 4) (h : i = 2 ∨ i = 3) : i ≠ 0 ∧ i ≠ 1 := by
  rcases h with rfl | rfl <;> decide

private lemma sum_square_high_μ (u v : ℝ) (ρ μ : Fin 4) (hμ : μ ≠ 0 ∧ μ ≠ 1) :
    ∑ ν : Fin 4, boostTdown u v ρ μ ν * boostTup u v ρ μ ν = 0 := by
  refine Finset.sum_eq_zero fun ν _ => ?_
  exact squareTerm_high (Or.inr (Or.inl hμ))

private lemma sum_square_high_ρ (u v : ℝ) (ρ : Fin 4) (hρ : ρ ≠ 0 ∧ ρ ≠ 1) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, boostTdown u v ρ μ ν * boostTup u v ρ μ ν = 0 := by
  refine Finset.sum_eq_zero fun μ _ => ?_
  refine Finset.sum_eq_zero fun ν _ => ?_
  exact squareTerm_high (Or.inl hρ)

theorem boost_square_contraction (u v : ℝ) :
    ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
        boostTdown u v ρ μ ν * boostTup u v ρ μ ν =
      2 * u ^ 2 - 2 * v ^ 2 := by
  rw [sum4_of_high
      (f := fun ρ => ∑ μ, ∑ ν, boostTdown u v ρ μ ν * boostTup u v ρ μ ν)
      (sum_square_high_ρ u v 2 (plane_ne 2 (Or.inl rfl)))
      (sum_square_high_ρ u v 3 (plane_ne 3 (Or.inr rfl)))]
  rw [sum4_of_high
      (f := fun μ => ∑ ν, boostTdown u v 0 μ ν * boostTup u v 0 μ ν)
      (sum_square_high_μ u v 0 2 (plane_ne 2 (Or.inl rfl)))
      (sum_square_high_μ u v 0 3 (plane_ne 3 (Or.inr rfl))),
    sum4_of_high
      (f := fun μ => ∑ ν, boostTdown u v 1 μ ν * boostTup u v 1 μ ν)
      (sum_square_high_μ u v 1 2 (plane_ne 2 (Or.inl rfl)))
      (sum_square_high_μ u v 1 3 (plane_ne 3 (Or.inr rfl)))]
  -- eight plane sums, each reduced to the two in-plane `ν`
  have hν :
      ∀ ρ μ : Fin 4,
        ∑ ν : Fin 4, boostTdown u v ρ μ ν * boostTup u v ρ μ ν =
          boostTdown u v ρ μ 0 * boostTup u v ρ μ 0 +
            boostTdown u v ρ μ 1 * boostTup u v ρ μ 1 := by
    intro ρ μ
    refine sum4_of_high ?_ ?_
    · exact squareTerm_high (Or.inr (Or.inr (plane_ne 2 (Or.inl rfl))))
    · exact squareTerm_high (Or.inr (Or.inr (plane_ne 3 (Or.inr rfl))))
  simp only [hν]
  simp [boostTdown, boostTup, boostTorsionUp, derivJet, boostGen, w31]
  ring

private lemma sum_cross_high_μ (u v : ℝ) (ρ μ : Fin 4) (hμ : μ ≠ 0 ∧ μ ≠ 1) :
    ∑ ν : Fin 4, boostTdown u v ρ μ ν * boostTup u v ν μ ρ = 0 := by
  refine Finset.sum_eq_zero fun ν _ => ?_
  exact crossTerm_high (Or.inr (Or.inl hμ))

private lemma sum_cross_high_ρ (u v : ℝ) (ρ : Fin 4) (hρ : ρ ≠ 0 ∧ ρ ≠ 1) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, boostTdown u v ρ μ ν * boostTup u v ν μ ρ = 0 := by
  refine Finset.sum_eq_zero fun μ _ => ?_
  refine Finset.sum_eq_zero fun ν _ => ?_
  exact crossTerm_high (Or.inl hρ)

theorem boost_cross_contraction (u v : ℝ) :
    ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
        boostTdown u v ρ μ ν * boostTup u v ν μ ρ =
      u ^ 2 - v ^ 2 := by
  rw [sum4_of_high
      (f := fun ρ => ∑ μ, ∑ ν, boostTdown u v ρ μ ν * boostTup u v ν μ ρ)
      (sum_cross_high_ρ u v 2 (plane_ne 2 (Or.inl rfl)))
      (sum_cross_high_ρ u v 3 (plane_ne 3 (Or.inr rfl)))]
  rw [sum4_of_high
      (f := fun μ => ∑ ν, boostTdown u v 0 μ ν * boostTup u v ν μ 0)
      (sum_cross_high_μ u v 0 2 (plane_ne 2 (Or.inl rfl)))
      (sum_cross_high_μ u v 0 3 (plane_ne 3 (Or.inr rfl))),
    sum4_of_high
      (f := fun μ => ∑ ν, boostTdown u v 1 μ ν * boostTup u v ν μ 1)
      (sum_cross_high_μ u v 1 2 (plane_ne 2 (Or.inl rfl)))
      (sum_cross_high_μ u v 1 3 (plane_ne 3 (Or.inr rfl)))]
  have hν :
      ∀ ρ μ : Fin 4,
        ∑ ν : Fin 4, boostTdown u v ρ μ ν * boostTup u v ν μ ρ =
          boostTdown u v ρ μ 0 * boostTup u v 0 μ ρ +
            boostTdown u v ρ μ 1 * boostTup u v 1 μ ρ := by
    intro ρ μ
    refine sum4_of_high ?_ ?_
    · exact crossTerm_high (Or.inr (Or.inr (plane_ne 2 (Or.inl rfl))))
    · exact crossTerm_high (Or.inr (Or.inr (plane_ne 3 (Or.inr rfl))))
  simp only [hν]
  simp [boostTdown, boostTup, boostTorsionUp, derivJet, boostGen, w31]
  ring

theorem boostTrace_zero (u v : ℝ) : boostTrace u v 0 = -v := by
  rw [boostTrace, Fin.sum_univ_four]
  simp [boostTorsionUp, derivJet, boostGen]

theorem boostTrace_one (u v : ℝ) : boostTrace u v 1 = -u := by
  rw [boostTrace, Fin.sum_univ_four]
  simp [boostTorsionUp, derivJet, boostGen]

theorem boostTrace_high {u v : ℝ} {ρ : Fin 4} (h : ρ ≠ 0 ∧ ρ ≠ 1) : boostTrace u v ρ = 0 := by
  rw [boostTrace]
  refine Finset.sum_eq_zero fun σ _ => ?_
  exact up_eq_zero_of_high_μ (u := u) (v := v) (ρ := σ) (μ := ρ) (ν := σ) h

theorem boost_trace_contraction (u v : ℝ) :
    ∑ ρ : Fin 4, boostTrace u v ρ * boostTraceUp u v ρ = u ^ 2 - v ^ 2 := by
  rw [sum4_of_high
      (f := fun ρ => boostTrace u v ρ * boostTraceUp u v ρ)
      (by rw [boostTrace_high (u := u) (v := v) (plane_ne 2 (Or.inl rfl))]; simp [boostTraceUp])
      (by rw [boostTrace_high (u := u) (v := v) (plane_ne 3 (Or.inr rfl))]; simp [boostTraceUp])]
  simp only [boostTraceUp, boostTrace_zero, boostTrace_one, w31]
  ring

/-- The teleparallel scalar of every inertial-boost jet vanishes. -/
theorem boostTeleparallel_eq_zero (u v : ℝ) : boostTeleparallel u v = 0 := by
  unfold boostTeleparallel
  rw [boost_square_contraction, boost_cross_contraction, boost_trace_contraction]
  ring

/-- Nonzero torsion is compatible with a vanishing teleparallel scalar. -/
theorem torsion_without_teleparallel (φ u v : ℝ) (hu : u ≠ 0) :
    boostCoordTorsion φ u v 0 0 1 ≠ 0 ∧ boostTeleparallel u v = 0 :=
  ⟨boostCoordTorsion_ne_zero_of_time φ u v hu, boostTeleparallel_eq_zero u v⟩

/-- Same metric, distinct mismatch, whenever the squared rapidities differ. -/
theorem inertialBoost_same_metric_distinct_J {φ ψ : ℝ} (h : φ ^ 2 ≠ ψ ^ 2) :
    (∀ μ ν,
        inducedMetric (inertialBoostCoframe φ) μ ν =
          inducedMetric (inertialBoostCoframe ψ) μ ν) ∧
      J (pureBoost φ) ≠ J (pureBoost ψ) := by
  refine ⟨fun μ ν => ?_, ?_⟩
  · rw [inducedMetric_inertialBoost, inducedMetric_inertialBoost]
  · rw [J_pureBoost, J_pureBoost]
    exact fun heq => h (by linarith)

/-- The value `J = ½ φ²` does not determine `T`: it vanishes on the inertial
boost and is positive on the exterior Schwarzschild coframe of the same rapidity. -/
theorem sameJ_inertial_T_zero_schwarzschild_T_pos {rs r : ℝ} (h : IsExterior rs r) :
    J (pureBoost (schwarzschildRapidity rs r)) = J (radialBoostParams rs r) ∧
      boostTeleparallel 0 0 = 0 ∧
      0 < schwarzschildTeleparallelT rs r := by
  refine ⟨?_, boostTeleparallel_eq_zero 0 0, schwarzschild_T_pos h⟩
  rw [J_pureBoost, J_radialBoostParams]

/-- No pointwise function of `J` reproduces `T` on every tetrad. -/
theorem no_pointwise_map_J_to_T :
    ¬ ∃ F : ℝ → ℝ,
        (∀ u v φ, boostTeleparallel u v = F ((1 / 2) * φ ^ 2)) ∧
          (∀ rs r, IsExterior rs r →
            schwarzschildTeleparallelT rs r = F (J (radialBoostParams rs r))) := by
  rintro ⟨F, hFlat, hSchw⟩
  have hExt : IsExterior (2 : ℝ) 4 := ⟨by norm_num, by norm_num⟩
  have hF : F (J (radialBoostParams 2 4)) = 0 := by
    rw [J_radialBoostParams, ← hFlat 0 0 (schwarzschildRapidity 2 4),
      boostTeleparallel_eq_zero]
  have hT := hSchw 2 4 hExt
  rw [hF] at hT
  exact (schwarzschild_T_pos hExt).ne' hT

end Gravity

end DstDiophantine
