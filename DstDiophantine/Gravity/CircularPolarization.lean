import DstDiophantine.Gravity.Electroweak
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Circular polarisation in the Faraday 6-space

## Paper boundary (do **not** claim)

Maxwell's equations, a laboratory electromagnetic identification, a
path-ordered dual-rotor coupling, a resonance frequency, and helicity
drive of the particle mismatch \(J\) are **not** derived. The linear
quadrature mean of a circular Faraday field vanishes, so a dual-sector
drive proportional to a mean \(F_{\mathrm{dual}}\) is not a coefficient
identity.

## What is proved

* A \(z\)-propagating circular wave with helicity \(\sigma^2=1\) is null
  at every phase: \(J=0\), \(E\cdot B=0\), and \(M=E_0^2\) (massive if
  \(E_0\neq 0\)). The existing snapshot is the phase-zero special case.
* The signed Poynting component along the propagation axis equals
  \(\sigma E_0^2\) at every phase. Laboratory \(T\) flips that sign;
  Hodge duality preserves it. A linearly polarised wave is also null,
  but its Poynting component is \(E_0^2\cos^2\psi\ge 0\) and carries no
  helicity sign, while \(M\) oscillates.
* Each linear Faraday coefficient of the circular wave has vanishing
  four-phase mean, so \(\langle F_{\mathrm{usual}}\rangle=
  \langle F_{\mathrm{dual}}\rangle=0\).
* Linear superposition onto a background torsion shifts \(J\) by a
  first harmonic in the phase; the four-phase mean of \(J\) is the
  background value. Helicity enters only the phase of that harmonic.
* The Faraday mix cannot create \(J\) from a circular wave.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations RelativeRotor Invariant
open scoped Real

/-! ### Circular and linear travelling waves -/

/-- Circularly polarised wave of helicity \(\sigma\) at phase
\(\psi=kz-\omega t\) (units \(c=1\)). -/
noncomputable def circularWave (σ E0 ψ : ℝ) : FaradayParams where
  E := fun
    | 0 => E0 * Real.cos ψ
    | 1 => σ * E0 * Real.sin ψ
    | _ => 0
  B := fun
    | 0 => -E0 * Real.sin ψ
    | 1 => σ * E0 * Real.cos ψ
    | _ => 0

/-- Linearly polarised wave along \(z\): \(E=E_0\cos\psi\,\hat x\),
\(B=E_0\cos\psi\,\hat y\). -/
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

end Gravity

end DstDiophantine
