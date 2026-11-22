import DstDiophantine.Gravity.Electroweak
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Circular polarisation in the Faraday 6-space

A circular Faraday wave is null at every phase, and its four-phase mean does
not shift \(J\). Maxwell's equations, a laboratory identification, and
helicity drive of \(J\) are not derived; axis chirality is not photon
helicity.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations RelativeRotor Invariant
open Logic
open scoped Real

/-! ### Circular and linear travelling waves -/

/-- Circularly polarised wave of helicity \(\sigma\) at phase \(\psi=kz-\omega t\) (units
\(c=1\)). -/
noncomputable def circularWave (σ E0 ψ : ℝ) : FaradayParams where
  E := fun
    | 0 => E0 * Real.cos ψ
    | 1 => σ * E0 * Real.sin ψ
    | _ => 0
  B := fun
    | 0 => -E0 * Real.sin ψ
    | 1 => σ * E0 * Real.cos ψ
    | _ => 0

/-- Linearly polarised wave along \(z\): \(E=E_0\cos\psi\,\hat x\), \(B=E_0\cos\psi\,\hat y\). -/
noncomputable def linearWave (E0 ψ : ℝ) : FaradayParams where
  E := fun
    | 0 => E0 * Real.cos ψ
    | _ => 0
  B := fun
    | 1 => E0 * Real.cos ψ
    | _ => 0

/-- Signed Poynting component along \(z\): \((E\times B)_z\). -/
def poyntingZ (p : FaradayParams) : ℝ :=
  cross p.E p.B 2

theorem circularWave_zero (σ E0 : ℝ) :
    circularWave σ E0 0 = circularSnapshot σ E0 := by
  ext a <;> fin_cases a <;>
    simp [circularWave, circularSnapshot, Real.cos_zero, Real.sin_zero]

theorem circularWave_energy {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    energySq (circularWave σ E0 ψ) = E0 ^ 2 := by
  unfold energySq circularWave
  simp only [Fin.sum_univ_three]
  calc (E0 * Real.cos ψ) ^ 2 + (σ * E0 * Real.sin ψ) ^ 2 + (0 : ℝ) ^ 2
      = E0 ^ 2 * Real.cos ψ ^ 2 + σ ^ 2 * E0 ^ 2 * Real.sin ψ ^ 2 := by ring
    _ = E0 ^ 2 * Real.cos ψ ^ 2 + E0 ^ 2 * Real.sin ψ ^ 2 := by rw [hσ, one_mul]
    _ = E0 ^ 2 * (Real.cos ψ ^ 2 + Real.sin ψ ^ 2) := by ring
    _ = E0 ^ 2 := by rw [add_comm, Real.sin_sq_add_cos_sq]; ring

theorem circularWave_magnetic {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    magneticSq (circularWave σ E0 ψ) = E0 ^ 2 := by
  unfold magneticSq circularWave
  simp only [Fin.sum_univ_three]
  calc (-E0 * Real.sin ψ) ^ 2 + (σ * E0 * Real.cos ψ) ^ 2 + (0 : ℝ) ^ 2
      = E0 ^ 2 * Real.sin ψ ^ 2 + σ ^ 2 * E0 ^ 2 * Real.cos ψ ^ 2 := by ring
    _ = E0 ^ 2 * Real.sin ψ ^ 2 + E0 ^ 2 * Real.cos ψ ^ 2 := by rw [hσ, one_mul]
    _ = E0 ^ 2 * (Real.sin ψ ^ 2 + Real.cos ψ ^ 2) := by ring
    _ = E0 ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring

theorem circularWave_energy_eq_magnetic {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    energySq (circularWave σ E0 ψ) = magneticSq (circularWave σ E0 ψ) := by
  rw [circularWave_energy hσ, circularWave_magnetic hσ]

theorem circularWave_dot {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    faradayDot (circularWave σ E0 ψ) = 0 := by
  unfold faradayDot circularWave
  simp only [Fin.sum_univ_three]
  calc (E0 * Real.cos ψ) * (-E0 * Real.sin ψ) +
        (σ * E0 * Real.sin ψ) * (σ * E0 * Real.cos ψ) + 0 * 0
      = (σ ^ 2 - 1) * E0 ^ 2 * Real.sin ψ * Real.cos ψ := by ring
    _ = 0 := by rw [hσ]; ring

theorem circularWave_J {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (circularWave σ E0 ψ)) = 0 :=
  J_eq_zero_of_energy_eq_magnetic (circularWave_energy_eq_magnetic hσ)

theorem circularWave_null {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    energySq (circularWave σ E0 ψ) = magneticSq (circularWave σ E0 ψ) ∧
      J (toTorsion (circularWave σ E0 ψ)) = 0 ∧
      faradayDot (circularWave σ E0 ψ) = 0 :=
  ⟨circularWave_energy_eq_magnetic hσ, circularWave_J hσ, circularWave_dot hσ⟩

theorem circularWave_mass {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    mass (toTorsion (circularWave σ E0 ψ)) = E0 ^ 2 := by
  rw [mass_eq_energySq_of_null (circularWave_energy_eq_magnetic hσ),
    circularWave_energy hσ]

theorem circularWave_mass_pos {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) (hE : E0 ≠ 0) :
    0 < mass (toTorsion (circularWave σ E0 ψ)) := by
  refine mass_pos_of_null (circularWave_energy_eq_magnetic hσ) ?_
  rw [circularWave_energy hσ]
  exact pow_ne_zero 2 hE

/-! ### Helicity-odd Poynting versus linear polarisation -/

theorem poyntingZ_circularWave (σ E0 ψ : ℝ) :
    poyntingZ (circularWave σ E0 ψ) = σ * E0 ^ 2 := by
  simp [poyntingZ, cross, circularWave]
  have h : Real.sin ψ ^ 2 + Real.cos ψ ^ 2 = 1 := Real.sin_sq_add_cos_sq ψ
  linear_combination σ * E0 ^ 2 * h

theorem poyntingZ_timeReverse (p : FaradayParams) :
    poyntingZ (timeReverseFaradayParams p) = -poyntingZ p := by
  simp [poyntingZ, cross, timeReverseFaradayParams]
  ring

theorem poyntingZ_dual (p : FaradayParams) :
    poyntingZ (dualFaradayParams p) = poyntingZ p := by
  simp [poyntingZ, cross, dualFaradayParams]
  ring

theorem poyntingZ_circularWave_timeReverse (σ E0 ψ : ℝ) :
    poyntingZ (timeReverseFaradayParams (circularWave σ E0 ψ)) =
      -(σ * E0 ^ 2) := by
  rw [poyntingZ_timeReverse, poyntingZ_circularWave]

theorem poyntingZ_circularWave_dual (σ E0 ψ : ℝ) :
    poyntingZ (dualFaradayParams (circularWave σ E0 ψ)) = σ * E0 ^ 2 := by
  rw [poyntingZ_dual, poyntingZ_circularWave]

theorem J_circularWave_timeReverse {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (timeReverseFaradayParams (circularWave σ E0 ψ))) = 0 := by
  rw [J_timeReverse, circularWave_J hσ]

theorem J_circularWave_dual {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (dualFaradayParams (circularWave σ E0 ψ))) = 0 := by
  rw [J_dualFaraday, circularWave_J hσ, neg_zero]

theorem linearWave_energy (E0 ψ : ℝ) :
    energySq (linearWave E0 ψ) = E0 ^ 2 * Real.cos ψ ^ 2 := by
  unfold energySq linearWave
  simp only [Fin.sum_univ_three]
  ring

theorem linearWave_magnetic (E0 ψ : ℝ) :
    magneticSq (linearWave E0 ψ) = E0 ^ 2 * Real.cos ψ ^ 2 := by
  unfold magneticSq linearWave
  simp only [Fin.sum_univ_three]
  ring

theorem linearWave_J (E0 ψ : ℝ) :
    J (toTorsion (linearWave E0 ψ)) = 0 :=
  J_eq_zero_of_energy_eq_magnetic (by rw [linearWave_energy, linearWave_magnetic])

theorem linearWave_dot (E0 ψ : ℝ) :
    faradayDot (linearWave E0 ψ) = 0 := by
  simp [faradayDot, linearWave, Fin.sum_univ_three]

theorem linearWave_mass (E0 ψ : ℝ) :
    mass (toTorsion (linearWave E0 ψ)) = E0 ^ 2 * Real.cos ψ ^ 2 := by
  rw [mass_eq_energySq_of_null (by rw [linearWave_energy, linearWave_magnetic]),
    linearWave_energy]

theorem poyntingZ_linearWave (E0 ψ : ℝ) :
    poyntingZ (linearWave E0 ψ) = E0 ^ 2 * Real.cos ψ ^ 2 := by
  simp [poyntingZ, cross, linearWave]
  ring

theorem poyntingZ_linearWave_nonneg (E0 ψ : ℝ) :
    0 ≤ poyntingZ (linearWave E0 ψ) := by
  rw [poyntingZ_linearWave]
  exact mul_nonneg (sq_nonneg E0) (sq_nonneg _)

/-! ### Four-phase means of linear Faraday coefficients -/

/-- Quadrature mean over \(\{0,\pi/2,\pi,3\pi/2\}\). -/
noncomputable def quadMean (f : ℝ → ℝ) : ℝ :=
  (f 0 + f (Real.pi / 2) + f Real.pi + f (3 * Real.pi / 2)) / 4

theorem cos_three_pi_div_two : Real.cos (3 * Real.pi / 2) = 0 := by
  have h : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  ring

theorem sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  have h : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  rw [h, Real.sin_add, Real.sin_pi, Real.cos_pi, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  ring

theorem quadMean_const (c : ℝ) : quadMean (fun _ => c) = c := by
  unfold quadMean
  ring

theorem quadMean_add (f g : ℝ → ℝ) :
    quadMean (fun ψ => f ψ + g ψ) = quadMean f + quadMean g := by
  unfold quadMean
  ring

theorem quadMean_smul (c : ℝ) (f : ℝ → ℝ) :
    quadMean (fun ψ => c * f ψ) = c * quadMean f := by
  unfold quadMean
  ring

theorem quadMean_cos : quadMean Real.cos = 0 := by
  unfold quadMean
  simp [Real.cos_zero, Real.cos_pi_div_two, Real.cos_pi, cos_three_pi_div_two]

theorem quadMean_sin : quadMean Real.sin = 0 := by
  unfold quadMean
  simp [Real.sin_zero, Real.sin_pi_div_two, Real.sin_pi, sin_three_pi_div_two]

theorem quadMean_harmonic (A B : ℝ) :
    quadMean (fun ψ => A * Real.cos ψ + B * Real.sin ψ) = 0 := by
  rw [quadMean_add, quadMean_smul, quadMean_smul, quadMean_cos, quadMean_sin]
  ring

theorem quadMean_circularWave_E (σ E0 : ℝ) (a : Fin 3) :
    quadMean (fun ψ => (circularWave σ E0 ψ).E a) = 0 := by
  fin_cases a
  · simp [circularWave, quadMean_smul, quadMean_cos]
  · simp [circularWave, quadMean_smul, quadMean_sin]
  · simp [circularWave, quadMean_const]

theorem quadMean_circularWave_B (σ E0 : ℝ) (a : Fin 3) :
    quadMean (fun ψ => (circularWave σ E0 ψ).B a) = 0 := by
  match a with
  | 0 =>
    have h : (fun ψ : ℝ => (circularWave σ E0 ψ).B 0) =
        fun ψ => (-E0) * Real.sin ψ := by
      ext
      simp [circularWave, neg_mul]
    rw [h, quadMean_smul, quadMean_sin, mul_zero]
  | 1 =>
    simp [circularWave, quadMean_smul, quadMean_cos]
  | 2 =>
    simp [circularWave, quadMean_const]

/-! ### Superposition does not shift mean \(J\) -/

theorem faradayCross_circularWave (p : FaradayParams) (σ E0 ψ : ℝ) :
    faradayCross p (circularWave σ E0 ψ) =
      E0 * ((p.E 0 - σ * p.B 1) * Real.cos ψ +
        (σ * p.E 1 + p.B 0) * Real.sin ψ) := by
  simp [faradayCross, circularWave, Fin.sum_univ_three]
  ring

theorem J_add_circularWave (p : FaradayParams) {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (p + circularWave σ E0 ψ)) =
      J (toTorsion p) +
        E0 * ((p.E 0 - σ * p.B 1) * Real.cos ψ +
          (σ * p.E 1 + p.B 0) * Real.sin ψ) := by
  rw [J_add, circularWave_J hσ, add_zero, faradayCross_circularWave]

theorem quadMean_J_add_circularWave (p : FaradayParams) {σ E0 : ℝ}
    (hσ : σ ^ 2 = 1) :
    quadMean (fun ψ => J (toTorsion (p + circularWave σ E0 ψ))) =
      J (toTorsion p) := by
  have h (ψ : ℝ) :
      J (toTorsion (p + circularWave σ E0 ψ)) =
        J (toTorsion p) +
          E0 * ((p.E 0 - σ * p.B 1) * Real.cos ψ +
            (σ * p.E 1 + p.B 0) * Real.sin ψ) :=
    J_add_circularWave p hσ
  simp_rw [h, quadMean_add, quadMean_const, quadMean_smul, quadMean_harmonic,
    mul_zero, add_zero]

/-! ### Mix cannot create \(J\) from a circular wave -/

theorem J_mix_circularWave (ω : ℝ) {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (mixFaradayParams ω (circularWave σ E0 ψ))) = 0 := by
  rw [J_mixFaraday_of_orthogonal (circularWave_dot hσ), circularWave_J hσ,
    mul_zero]

/-! ### Rest sandwich of the dual circular summand -/

theorem sandwichIncrement_rest_circularWave_dual (σ E0 ψ : ℝ) :
    sandwichIncrement (faradayDual (circularWave σ E0 ψ)) (ι 0) = 0 :=
  sandwichIncrement_rest_faradayDual _

/-! ### Axis chirality is not photon helicity -/

theorem poyntingZ_add (p q : FaradayParams) :
    poyntingZ (p + q) =
      poyntingZ p + poyntingZ q +
        (cross p.E q.B 2 + cross q.E p.B 2) := by
  simp [poyntingZ, cross, add_E, add_B]
  ring

theorem poyntingZ_cartan_add_charged (p : FaradayParams) :
    poyntingZ p =
      poyntingZ (cartanParams p) + poyntingZ (chargedParams p) := by
  have hcross := cross_z_cartan_charged p p
  calc poyntingZ p
      = poyntingZ (cartanParams p + chargedParams p) := by
          rw [cartanParams_add_chargedParams]
    _ = poyntingZ (cartanParams p) + poyntingZ (chargedParams p) +
          (cross (cartanParams p).E (chargedParams p).B 2 +
            cross (chargedParams p).E (cartanParams p).B 2) :=
          poyntingZ_add _ _
    _ = poyntingZ (cartanParams p) + poyntingZ (chargedParams p) +
          (0 + 0) := by rw [hcross.1, hcross.2]
    _ = poyntingZ (cartanParams p) + poyntingZ (chargedParams p) := by
          ring

theorem circularWave_cartan_energy {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    energySq (cartanParams (circularWave σ E0 ψ)) =
      E0 ^ 2 * Real.sin ψ ^ 2 := by
  unfold energySq cartanParams circularWave
  simp only [Fin.sum_univ_three]
  calc (0 : ℝ) ^ 2 + (σ * E0 * Real.sin ψ) ^ 2 + (0 : ℝ) ^ 2
      = σ ^ 2 * E0 ^ 2 * Real.sin ψ ^ 2 := by ring
    _ = E0 ^ 2 * Real.sin ψ ^ 2 := by rw [hσ, one_mul]

theorem circularWave_cartan_magnetic (σ E0 ψ : ℝ) :
    magneticSq (cartanParams (circularWave σ E0 ψ)) =
      E0 ^ 2 * Real.sin ψ ^ 2 := by
  unfold magneticSq cartanParams circularWave
  simp only [Fin.sum_univ_three]
  ring

theorem circularWave_cartan_energy_eq_magnetic {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    energySq (cartanParams (circularWave σ E0 ψ)) =
      magneticSq (cartanParams (circularWave σ E0 ψ)) := by
  rw [circularWave_cartan_energy hσ, circularWave_cartan_magnetic]

theorem circularWave_cartan_J {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (cartanParams (circularWave σ E0 ψ))) = 0 :=
  J_eq_zero_of_energy_eq_magnetic (circularWave_cartan_energy_eq_magnetic hσ)

theorem circularWave_cartan_dot (σ E0 ψ : ℝ) :
    faradayDot (cartanParams (circularWave σ E0 ψ)) = 0 := by
  simp [faradayDot, cartanParams, circularWave, Fin.sum_univ_three]

theorem circularWave_charged_energy (σ E0 ψ : ℝ) :
    energySq (chargedParams (circularWave σ E0 ψ)) =
      E0 ^ 2 * Real.cos ψ ^ 2 := by
  unfold energySq chargedParams circularWave
  simp only [Fin.sum_univ_three]
  ring

theorem circularWave_charged_magnetic {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    magneticSq (chargedParams (circularWave σ E0 ψ)) =
      E0 ^ 2 * Real.cos ψ ^ 2 := by
  unfold magneticSq chargedParams circularWave
  simp only [Fin.sum_univ_three]
  calc (0 : ℝ) ^ 2 + (σ * E0 * Real.cos ψ) ^ 2 + (0 : ℝ) ^ 2
      = σ ^ 2 * E0 ^ 2 * Real.cos ψ ^ 2 := by ring
    _ = E0 ^ 2 * Real.cos ψ ^ 2 := by rw [hσ, one_mul]

theorem circularWave_charged_energy_eq_magnetic {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    energySq (chargedParams (circularWave σ E0 ψ)) =
      magneticSq (chargedParams (circularWave σ E0 ψ)) := by
  rw [circularWave_charged_energy, circularWave_charged_magnetic hσ]

theorem circularWave_charged_J {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (chargedParams (circularWave σ E0 ψ))) = 0 :=
  J_eq_zero_of_energy_eq_magnetic (circularWave_charged_energy_eq_magnetic hσ)

theorem circularWave_charged_dot (σ E0 ψ : ℝ) :
    faradayDot (chargedParams (circularWave σ E0 ψ)) = 0 := by
  simp [faradayDot, chargedParams, circularWave, Fin.sum_univ_three]

theorem poyntingZ_circularWave_cartan (σ E0 ψ : ℝ) :
    poyntingZ (cartanParams (circularWave σ E0 ψ)) =
      σ * E0 ^ 2 * Real.sin ψ ^ 2 := by
  simp [poyntingZ, cross, cartanParams, circularWave]
  ring

theorem poyntingZ_circularWave_charged (σ E0 ψ : ℝ) :
    poyntingZ (chargedParams (circularWave σ E0 ψ)) =
      σ * E0 ^ 2 * Real.cos ψ ^ 2 := by
  simp [poyntingZ, cross, chargedParams, circularWave]
  ring

theorem poyntingZ_circularWave_cartan_add_charged (σ E0 ψ : ℝ) :
    poyntingZ (cartanParams (circularWave σ E0 ψ)) +
        poyntingZ (chargedParams (circularWave σ E0 ψ)) =
      poyntingZ (circularWave σ E0 ψ) :=
  (poyntingZ_cartan_add_charged (circularWave σ E0 ψ)).symm

theorem cartanParams_circularWave_zero (σ E0 : ℝ) :
    cartanParams (circularWave σ E0 0) =
      { E := fun _ => 0, B := fun _ => 0 } := by
  ext a <;> fin_cases a <;> simp [cartanParams, circularWave, Real.sin_zero]

theorem faradayCartan_circularWave_zero (σ E0 : ℝ) :
    faradayCartan (circularWave σ E0 0) = 0 := by
  simp [faradayCartan, circularWave, Real.sin_zero]

theorem chiralSandwich_circularWave_zero (σ E0 : ℝ) :
    chiralSandwich (faraday (circularWave σ E0 0)) = 0 := by
  rw [chiralSandwich_faraday, faradayCartan_circularWave_zero, mul_zero]

theorem chargedParams_circularWave_pi_div_two (σ E0 : ℝ) :
    chargedParams (circularWave σ E0 (Real.pi / 2)) =
      { E := fun _ => 0, B := fun _ => 0 } := by
  ext a <;> fin_cases a <;>
    simp [chargedParams, circularWave, Real.cos_pi_div_two]

theorem faradayCharged_circularWave_pi_div_two (σ E0 : ℝ) :
    faradayCharged (circularWave σ E0 (Real.pi / 2)) = 0 := by
  simp [faradayCharged, circularWave, Real.cos_pi_div_two]

theorem chiralSandwich_circularWave_pi_div_two (σ E0 : ℝ) :
    chiralSandwich (faraday (circularWave σ E0 (Real.pi / 2))) =
      chiralityR * faraday (circularWave σ E0 (Real.pi / 2)) := by
  rw [chiralSandwich_faraday, faraday_eq_cartan_add_charged,
    faradayCharged_circularWave_pi_div_two, add_zero]

theorem chiralSandwich_circularWave (σ E0 ψ : ℝ) :
    chiralSandwich (faraday (circularWave σ E0 ψ)) =
      chiralityR * faradayCartan (circularWave σ E0 ψ) :=
  chiralSandwich_faraday _

theorem chiralSandwichL_circularWave_charged (σ E0 ψ : ℝ) :
    chiralSandwichL (faradayCharged (circularWave σ E0 ψ)) = 0 :=
  chiralSandwichL_charged _

theorem chiralSandwichL_circularWave (σ E0 ψ : ℝ) :
    chiralSandwichL (faraday (circularWave σ E0 ψ)) =
      chiralSandwichL (faradayCartan (circularWave σ E0 ψ)) :=
  chiralSandwichL_faraday _

/-! ### Rest kick and beam-direction sandwich force -/

theorem sandwichIncrement_rest_circularWave (σ E0 ψ : ℝ) :
    sandwichIncrement (faraday (circularWave σ E0 ψ)) (ι 0) =
      (E0 * Real.cos ψ) • ι 1 + (σ * E0 * Real.sin ψ) • ι 2 := by
  rw [sandwichIncrement_rest_faraday]
  simp [circularWave]

theorem sandwichForce_circularWave_rest (σ E0 ψ : ℝ) (a : Fin 3) :
    sandwichForce (circularWave σ E0 ψ) restVelocity a =
      (circularWave σ E0 ψ).E a := by
  fin_cases a <;> simp [sandwichForce, restVelocity, cross, circularWave]

theorem quadMean_sandwichForce_circularWave_rest (σ E0 : ℝ) (a : Fin 3) :
    quadMean (fun ψ =>
      sandwichForce (circularWave σ E0 ψ) restVelocity a) = 0 := by
  simp_rw [sandwichForce_circularWave_rest]
  exact quadMean_circularWave_E σ E0 a

/-- Velocity along the propagation axis \(z\). -/
def zVelocity (vz : ℝ) : Fin 3 → ℝ
  | 2 => vz
  | _ => 0

theorem sandwichForce_circularWave_zVelocity_transverse (σ E0 ψ vz : ℝ) :
    sandwichForce (circularWave σ E0 ψ) (zVelocity vz) 2 = 0 := by
  simp [sandwichForce, circularWave, zVelocity, cross]

theorem sandwichForce_circularWave_zVelocity (σ E0 ψ vz : ℝ) :
    sandwichForce (circularWave σ E0 ψ) (zVelocity vz) 0 =
      E0 * Real.cos ψ + vz * (σ * E0 * Real.cos ψ) ∧
    sandwichForce (circularWave σ E0 ψ) (zVelocity vz) 1 =
      σ * E0 * Real.sin ψ + vz * (E0 * Real.sin ψ) ∧
    sandwichForce (circularWave σ E0 ψ) (zVelocity vz) 2 = 0 := by
  simp [sandwichForce, circularWave, zVelocity, cross]

/-! ### Uniqueness of the helicity-odd classical quadratic -/

/-- Real linear combination of the six classical Faraday quadratics. -/
def classicalQuadratic (cE2 cB2 cEB cPx cPy cPz : ℝ)
    (p : FaradayParams) : ℝ :=
  cE2 * energySq p + cB2 * magneticSq p + cEB * faradayDot p +
    cPx * cross p.E p.B 0 + cPy * cross p.E p.B 1 + cPz * poyntingZ p

theorem classicalQuadratic_circularWave {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1)
    (cE2 cB2 cEB cPx cPy cPz : ℝ) :
    classicalQuadratic cE2 cB2 cEB cPx cPy cPz (circularWave σ E0 ψ) =
      (cE2 + cB2) * E0 ^ 2 + cPz * σ * E0 ^ 2 := by
  unfold classicalQuadratic
  rw [circularWave_energy hσ, circularWave_magnetic hσ, circularWave_dot hσ,
    poyntingZ_circularWave]
  simp [cross, circularWave]
  ring

theorem classicalQuadratic_helicity_odd_even_sector
    {cE2 cB2 cEB cPx cPy cPz : ℝ}
    (h : ∀ σ E0 ψ : ℝ, σ ^ 2 = 1 →
      classicalQuadratic cE2 cB2 cEB cPx cPy cPz (circularWave (-σ) E0 ψ) =
        -classicalQuadratic cE2 cB2 cEB cPx cPy cPz (circularWave σ E0 ψ)) :
    cE2 + cB2 = 0 := by
  have hσ : (1 : ℝ) ^ 2 = 1 := by norm_num
  have h1 := classicalQuadratic_circularWave (σ := 1) (E0 := 1) (ψ := 0) hσ
    cE2 cB2 cEB cPx cPy cPz
  have hσn : ((-1 : ℝ) ^ 2 = 1) := by norm_num
  have hn := classicalQuadratic_circularWave (σ := -1) (E0 := 1) (ψ := 0) hσn
    cE2 cB2 cEB cPx cPy cPz
  have hodd := h 1 1 0 hσ
  simp [h1, hn] at hodd
  linarith

theorem classicalQuadratic_eq_smul_poyntingZ_of_helicity_odd
    {cE2 cB2 cEB cPx cPy cPz : ℝ}
    (h : ∀ σ E0 ψ : ℝ, σ ^ 2 = 1 →
      classicalQuadratic cE2 cB2 cEB cPx cPy cPz (circularWave (-σ) E0 ψ) =
        -classicalQuadratic cE2 cB2 cEB cPx cPy cPz (circularWave σ E0 ψ))
    {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    classicalQuadratic cE2 cB2 cEB cPx cPy cPz (circularWave σ E0 ψ) =
      cPz * poyntingZ (circularWave σ E0 ψ) := by
  have heven := classicalQuadratic_helicity_odd_even_sector h
  rw [classicalQuadratic_circularWave hσ, poyntingZ_circularWave, heven]
  ring

end Gravity

end DstDiophantine
