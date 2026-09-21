import DstDiophantine.Gravity.CircularPolarization
import DstDiophantine.Gravity.DualControl
import DstDiophantine.Gravity.DualRotorDynamics
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebraic couplings of electromagnetism to dual-only control

A dual-only increment of the dual angles is the algebraic channel.
Superposing a magnetic Faraday field and substituting
\(\theta\mapsto\theta+eA\) are two laboratory readings of that same
increment. Neither is a derivation of Maxwell, of a laboratory
protocol, or of a helicity-odd drive of \(J\).

## Paper boundary (do **not** claim)

* The identification of Faraday coefficients with a laboratory
  electromagnetic field remains a working hypothesis.
* Minimal coupling \(\theta_a\mapsto\theta_a+e A_a\) is a substitution
  in the dual rotor, not a derivation of that substitution from the
  Faraday bivector, and it is not Maxwell-gauge invariant.
* Helicity drive of \(J\), a resonance frequency, and a path-ordered
  laboratory protocol are **not** derived.

## What is proved

* Superposing Faraday coefficients is addition in the shared 6-space.
  A pure magnetic increment is dual-only and cannot raise \(J\) when
  both the existing dual angles and the increment are nonnegative.
  A pure electric increment is usual-only. Superposing a circular wave
  does not shift the four-phase mean of \(J\).
* The substitution \(\theta\mapsto\theta+eA\) is the same map:
  `coupleA p e A` equals magnetic superposition of \(eA\). It
  conserves \(J+M\) and yields
  \(J\mapsto J-e\,\beta\cdot A-(e^2/2)A^2\).
  For a circular Coulomb-gauge potential with \(\sigma^2=1\),
  \(A^2=(E_0/\omega)^2\) is constant and helicity-even; the four-phase
  mean of \(J\) drops by \((e^2/2)(E_0/\omega)^2\). A linearly
  polarised potential of the same \(E_0\) drops the mean by half that
  amount. Cycle-averaged \(\dot J\) vanishes; the shift is
  ponderomotive, not a secular drift. The two readings part company
  under a constant shift of \(A\).
* From a vanishing dual seed, a zero-mean circular \(A\) makes a dual
  angle negative, hence leaves the admissible cone. Dual-only
  realisation of \(\theta=\theta_0+e A\) on the written action requires
  the constraint pair \(v=m\delta\) and \(u=e\ddot A+m\delta\).
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-! ### Shared 6-space superposition -/

/-- Read torsion coefficients as Faraday coefficients in the shared 6-space. -/
def toFaraday (p : TorsionParams) : FaradayParams where
  E := p.alpha
  B := p.beta

@[simp] theorem toTorsion_toFaraday (p : TorsionParams) :
    toTorsion (toFaraday p) = p :=
  rfl

@[simp] theorem toFaraday_toTorsion (p : FaradayParams) :
    toFaraday (toTorsion p) = p :=
  rfl

/-- Superpose a Faraday increment onto a particle torsion configuration. -/
def superpose (p : TorsionParams) (F : FaradayParams) : TorsionParams :=
  toTorsion (toFaraday p + F)

@[simp] theorem superpose_alpha (p : TorsionParams) (F : FaradayParams)
    (a : Fin 3) :
    (superpose p F).alpha a = p.alpha a + F.E a :=
  rfl

@[simp] theorem superpose_beta (p : TorsionParams) (F : FaradayParams)
    (a : Fin 3) :
    (superpose p F).beta a = p.beta a + F.B a :=
  rfl

theorem J_superpose (p : TorsionParams) (F : FaradayParams) :
    J (superpose p F) =
      J p + J (toTorsion F) + faradayCross (toFaraday p) F := by
  simpa [superpose] using J_add (toFaraday p) F

def magneticFaraday (B : Fin 3 → ℝ) : FaradayParams where
  E := fun _ => 0
  B := B

def electricFaraday (E : Fin 3 → ℝ) : FaradayParams where
  E := E
  B := fun _ => 0

theorem superpose_magnetic_dual_only (p : TorsionParams) (B : Fin 3 → ℝ) :
    (superpose p (magneticFaraday B)).alpha = p.alpha := by
  funext a
  simp [magneticFaraday]

theorem superpose_electric_usual_only (p : TorsionParams) (E : Fin 3 → ℝ) :
    (superpose p (electricFaraday E)).beta = p.beta := by
  funext a
  simp [electricFaraday]

theorem superpose_magnetic_conserves_J_add_mass
    (p : TorsionParams) (B : Fin 3 → ℝ) :
    J (superpose p (magneticFaraday B)) +
        mass (superpose p (magneticFaraday B)) =
      J p + mass p :=
  dual_only_conserves_J_add_mass (superpose_magnetic_dual_only p B)

theorem superpose_electric_conserves_mass_sub_J
    (p : TorsionParams) (E : Fin 3 → ℝ) :
    mass (superpose p (electricFaraday E)) -
        J (superpose p (electricFaraday E)) =
      mass p - J p :=
  usual_only_conserves_mass_sub_J (superpose_electric_usual_only p E)

theorem J_magneticFaraday (B : Fin 3 → ℝ) :
    J (toTorsion (magneticFaraday B)) =
      -((1 / 2) * ∑ a : Fin 3, B a ^ 2) := by
  rw [J_faraday]
  simp [magneticFaraday, energySq, magneticSq]

theorem faradayCross_magnetic (p : TorsionParams) (B : Fin 3 → ℝ) :
    faradayCross (toFaraday p) (magneticFaraday B) =
      -∑ a : Fin 3, p.beta a * B a := by
  simp [faradayCross, toFaraday, magneticFaraday]

theorem J_superpose_magnetic (p : TorsionParams) (B : Fin 3 → ℝ) :
    J (superpose p (magneticFaraday B)) =
      J p - ∑ a : Fin 3, p.beta a * B a -
        (1 / 2) * ∑ a : Fin 3, B a ^ 2 := by
  rw [J_superpose, J_magneticFaraday, faradayCross_magnetic]
  ring

/-- Nonnegative magnetic increments cannot raise \(J\) against a
nonnegative dual seed. -/
theorem J_superpose_magnetic_le {p : TorsionParams} {B : Fin 3 → ℝ}
    (hβ : ∀ a, 0 ≤ p.beta a) (hB : ∀ a, 0 ≤ B a) :
    J (superpose p (magneticFaraday B)) ≤ J p := by
  have h1 : 0 ≤ ∑ a : Fin 3, p.beta a * B a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hβ a) (hB a)
  have h2 : 0 ≤ ∑ a : Fin 3, B a ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hJ := J_superpose_magnetic p B
  linarith

theorem isAdmissibleContinuous_superpose_magnetic
    {p : TorsionParams} {B : Fin 3 → ℝ}
    (hp : IsAdmissibleContinuous p) (hB : ∀ a, 0 ≤ B a)
    (hsum : ∀ a, p.alpha a + p.beta a + B a ≤ Real.pi / 2) :
    IsAdmissibleContinuous (superpose p (magneticFaraday B)) := by
  intro a
  have hα : 0 ≤ (superpose p (magneticFaraday B)).alpha a := by
    simpa [magneticFaraday] using (hp a).1
  have hβ : 0 ≤ (superpose p (magneticFaraday B)).beta a := by
    simpa [magneticFaraday] using add_nonneg (hp a).2.1 (hB a)
  have hs : (superpose p (magneticFaraday B)).alpha a +
      (superpose p (magneticFaraday B)).beta a ≤ Real.pi / 2 := by
    simpa [magneticFaraday, add_assoc] using hsum a
  exact ⟨hα, hβ, hs⟩

theorem not_admissible_superpose_magnetic_of_neg_beta
    {p : TorsionParams} {B : Fin 3 → ℝ} {a : Fin 3}
    (h : p.beta a + B a < 0) :
    ¬ IsAdmissibleContinuous (superpose p (magneticFaraday B)) := by
  intro hp
  exact (not_le.mpr h) (by simpa [magneticFaraday] using (hp a).2.1)

/-- Superposing a circular wave does not shift mean particle \(J\). -/
theorem quadMean_J_superpose_circular (p : TorsionParams) {σ E0 : ℝ}
    (hσ : σ ^ 2 = 1) :
    quadMean (fun ψ => J (superpose p (circularWave σ E0 ψ))) = J p := by
  simpa [superpose] using quadMean_J_add_circularWave (toFaraday p) hσ

/-! ### Dual-rotor minimal coupling \(\theta\mapsto\theta+e A\) -/

def coupleA (p : TorsionParams) (e : ℝ) (A : Fin 3 → ℝ) : TorsionParams where
  alpha := p.alpha
  beta := fun a => p.beta a + e * A a

@[simp] theorem coupleA_alpha (p : TorsionParams) (e : ℝ) (A : Fin 3 → ℝ) :
    (coupleA p e A).alpha = p.alpha :=
  rfl

@[simp] theorem coupleA_beta (p : TorsionParams) (e : ℝ) (A : Fin 3 → ℝ)
    (a : Fin 3) :
    (coupleA p e A).beta a = p.beta a + e * A a :=
  rfl

/-- The substitution \(\theta\mapsto\theta+eA\) is magnetic superposition
of the increment \(eA\). -/
theorem coupleA_eq_superpose_magnetic (p : TorsionParams) (e : ℝ)
    (A : Fin 3 → ℝ) :
    coupleA p e A = superpose p (magneticFaraday (fun a => e * A a)) := by
  refine torsionParams_ext ?_ ?_
  · funext a; simp [magneticFaraday]
  · funext a; simp [magneticFaraday]

theorem coupleA_conserves_J_add_mass (p : TorsionParams) (e : ℝ)
    (A : Fin 3 → ℝ) :
    J (coupleA p e A) + mass (coupleA p e A) = J p + mass p :=
  dual_only_conserves_J_add_mass (coupleA_alpha p e A)

def ampSq (A : Fin 3 → ℝ) : ℝ :=
  ∑ a : Fin 3, A a ^ 2

def dot3 (u v : Fin 3 → ℝ) : ℝ :=
  ∑ a : Fin 3, u a * v a

theorem J_coupleA (p : TorsionParams) (e : ℝ) (A : Fin 3 → ℝ) :
    J (coupleA p e A) =
      J p - e * dot3 p.beta A - (e ^ 2 / 2) * ampSq A := by
  rw [J_coef, J_coef]
  simp only [coupleA, dot3, ampSq, Fin.sum_univ_three]
  ring

theorem JDot_coupleA (p : TorsionParams) (e : ℝ) (A Adot : Fin 3 → ℝ) :
    JDot (coupleA p e A) ⟨fun _ => 0, fun a => e * Adot a⟩ =
      -e * dot3 p.beta Adot - e ^ 2 * dot3 A Adot := by
  unfold JDot coupleA dot3
  simp only [Fin.sum_univ_three]
  ring

/-! ### Coulomb-gauge potentials of circular and linear waves -/

/-- Coulomb-gauge potential of a \(z\)-propagating circular wave,
\(E=-\partial_t A\) under \(\dot\psi=-\omega\). -/
noncomputable def circularPotential (σ E0 ω ψ : ℝ) : Fin 3 → ℝ
  | 0 => E0 / ω * Real.sin ψ
  | 1 => -σ * (E0 / ω) * Real.cos ψ
  | _ => 0

/-- Formal \(\partial_t A\) of `circularPotential` at \(\dot\psi=-\omega\). -/
noncomputable def circularPotentialDt (σ E0 ψ : ℝ) : Fin 3 → ℝ
  | 0 => -E0 * Real.cos ψ
  | 1 => -σ * E0 * Real.sin ψ
  | _ => 0

noncomputable def linearPotential (E0 ω ψ : ℝ) : Fin 3 → ℝ
  | 0 => E0 / ω * Real.sin ψ
  | _ => 0

theorem circularPotentialDt_eq_neg_E (σ E0 ψ : ℝ) (a : Fin 3) :
    circularPotentialDt σ E0 ψ a = -(circularWave σ E0 ψ).E a := by
  fin_cases a <;> simp [circularPotentialDt, circularWave]

theorem circularPotential_ampSq {σ E0 ω ψ : ℝ} (hσ : σ ^ 2 = 1) :
    ampSq (circularPotential σ E0 ω ψ) = (E0 / ω) ^ 2 := by
  simp only [ampSq, circularPotential, Fin.sum_univ_three]
  calc (E0 / ω * Real.sin ψ) ^ 2 + (-σ * (E0 / ω) * Real.cos ψ) ^ 2 + (0 : ℝ) ^ 2
      = (E0 / ω) ^ 2 * Real.sin ψ ^ 2 +
          σ ^ 2 * (E0 / ω) ^ 2 * Real.cos ψ ^ 2 := by ring
    _ = (E0 / ω) ^ 2 * Real.sin ψ ^ 2 +
          (E0 / ω) ^ 2 * Real.cos ψ ^ 2 := by rw [hσ, one_mul]
    _ = (E0 / ω) ^ 2 * (Real.sin ψ ^ 2 + Real.cos ψ ^ 2) := by ring
    _ = (E0 / ω) ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring

theorem circular_A_dot_Adot {σ E0 ω ψ : ℝ} (hσ : σ ^ 2 = 1) :
    dot3 (circularPotential σ E0 ω ψ) (circularPotentialDt σ E0 ψ) = 0 := by
  simp only [dot3, circularPotential, circularPotentialDt, Fin.sum_univ_three]
  calc (E0 / ω * Real.sin ψ) * (-E0 * Real.cos ψ) +
        (-σ * (E0 / ω) * Real.cos ψ) * (-σ * E0 * Real.sin ψ) + 0 * 0
      = (σ ^ 2 - 1) * (E0 ^ 2 / ω) * Real.sin ψ * Real.cos ψ := by ring
    _ = 0 := by rw [hσ]; ring

theorem JDot_coupleA_circular {p : TorsionParams} {e σ E0 ω ψ : ℝ}
    (hσ : σ ^ 2 = 1) :
    JDot (coupleA p e (circularPotential σ E0 ω ψ))
        ⟨fun _ => 0, fun a => e * circularPotentialDt σ E0 ψ a⟩ =
      -e * dot3 p.beta (circularPotentialDt σ E0 ψ) := by
  rw [JDot_coupleA, circular_A_dot_Adot hσ, mul_zero, sub_zero]

theorem quadMean_dot_circularPotential (β : Fin 3 → ℝ) (σ E0 ω : ℝ) :
    quadMean (fun ψ =>
      dot3 β (circularPotential σ E0 ω ψ)) = 0 := by
  have hfun :
      (fun ψ : ℝ => dot3 β (circularPotential σ E0 ω ψ)) =
        fun ψ => (β 1 * (-σ * (E0 / ω))) * Real.cos ψ +
          (β 0 * (E0 / ω)) * Real.sin ψ := by
    ext ψ
    simp [dot3, circularPotential, Fin.sum_univ_three]
    ring
  rw [hfun, quadMean_harmonic]

/-- Helicity-even ponderomotive drop of mean \(J\) on a circular potential. -/
theorem quadMean_J_coupleA_circular (p : TorsionParams) (e E0 ω : ℝ)
    {σ : ℝ} (hσ : σ ^ 2 = 1) :
    quadMean (fun ψ => J (coupleA p e (circularPotential σ E0 ω ψ))) =
      J p - (e ^ 2 / 2) * (E0 / ω) ^ 2 := by
  have hfun :
      (fun ψ : ℝ => J (coupleA p e (circularPotential σ E0 ω ψ))) =
        fun ψ => (J p - (e ^ 2 / 2) * (E0 / ω) ^ 2) +
          -e * dot3 p.beta (circularPotential σ E0 ω ψ) := by
    ext ψ
    rw [J_coupleA, circularPotential_ampSq hσ]
    ring
  rw [hfun, quadMean_add, quadMean_const, quadMean_smul,
    quadMean_dot_circularPotential, mul_zero, add_zero]

theorem quadMean_J_coupleA_circular_helicity_even
    (p : TorsionParams) (e E0 ω σ : ℝ) (hσ : σ ^ 2 = 1) :
    quadMean (fun ψ => J (coupleA p e (circularPotential σ E0 ω ψ))) =
      quadMean (fun ψ =>
        J (coupleA p e (circularPotential (-σ) E0 ω ψ))) := by
  have hσn : (-σ) ^ 2 = 1 := by rw [neg_sq, hσ]
  rw [quadMean_J_coupleA_circular p e E0 ω hσ,
    quadMean_J_coupleA_circular p e E0 ω hσn]

theorem linearPotential_ampSq (E0 ω ψ : ℝ) :
    ampSq (linearPotential E0 ω ψ) =
      (E0 / ω) ^ 2 * Real.sin ψ ^ 2 := by
  simp [ampSq, linearPotential, Fin.sum_univ_three]
  ring

theorem quadMean_sin_sq : quadMean (fun ψ => Real.sin ψ ^ 2) = 1 / 2 := by
  unfold quadMean
  simp [Real.sin_zero, Real.sin_pi_div_two, Real.sin_pi, sin_three_pi_div_two]
  ring

theorem quadMean_linearPotential_ampSq (E0 ω : ℝ) :
    quadMean (fun ψ => ampSq (linearPotential E0 ω ψ)) =
      (1 / 2) * (E0 / ω) ^ 2 := by
  have hfun :
      (fun ψ : ℝ => ampSq (linearPotential E0 ω ψ)) =
        fun ψ => (E0 / ω) ^ 2 * Real.sin ψ ^ 2 := by
    ext ψ
    exact linearPotential_ampSq E0 ω ψ
  rw [hfun, quadMean_smul, quadMean_sin_sq]
  ring

theorem quadMean_dot_linearPotential (β : Fin 3 → ℝ) (E0 ω : ℝ) :
    quadMean (fun ψ => dot3 β (linearPotential E0 ω ψ)) = 0 := by
  have hfun :
      (fun ψ : ℝ => dot3 β (linearPotential E0 ω ψ)) =
        fun ψ => (β 0 * (E0 / ω)) * Real.sin ψ := by
    ext ψ
    simp [dot3, linearPotential, Fin.sum_univ_three]
    ring
  rw [hfun, quadMean_smul, quadMean_sin, mul_zero]

/-- Linear polarisation of the same \(E_0\) drops mean \(J\) by half the
circular amount. -/
theorem quadMean_J_coupleA_linear (p : TorsionParams) (e E0 ω : ℝ) :
    quadMean (fun ψ => J (coupleA p e (linearPotential E0 ω ψ))) =
      J p - (e ^ 2 / 4) * (E0 / ω) ^ 2 := by
  have hfun :
      (fun ψ : ℝ => J (coupleA p e (linearPotential E0 ω ψ))) =
        fun ψ => J p + -e * dot3 p.beta (linearPotential E0 ω ψ) +
          -(e ^ 2 / 2) * ampSq (linearPotential E0 ω ψ) := by
    ext ψ
    rw [J_coupleA]
    ring
  rw [hfun, quadMean_add, quadMean_add, quadMean_const, quadMean_smul,
    quadMean_dot_linearPotential, mul_zero, add_zero, quadMean_smul,
    quadMean_linearPotential_ampSq]
  ring

/-! ### Gauge non-invariance and the admissible cone -/

/-- Constant shifts of \(A\) change \(J\); both potentials have vanishing
\(\dot A\). -/
theorem exists_constant_potential_changes_J :
    ∃ p : TorsionParams, ∃ e : ℝ, ∃ A c : Fin 3 → ℝ,
      J (coupleA p e A) ≠ J (coupleA p e (fun a => A a + c a)) := by
  let p : TorsionParams := ⟨fun _ => 0, fun _ => 0⟩
  let A : Fin 3 → ℝ := fun _ => 0
  let c : Fin 3 → ℝ := fun _ => 1
  refine ⟨p, 1, A, c, ?_⟩
  have hAc : (fun a => A a + c a) = fun _ => 1 := by
    ext; simp [A, c]
  have h0 : J (coupleA p 1 A) = 0 := by
    rw [J_coupleA]
    simp [dot3, ampSq, J_coef, p, A]
  have h1 : J (coupleA p 1 fun _ => 1) = -((3 : ℝ) / 2) := by
    rw [J_coupleA]
    simp [dot3, ampSq, J_coef, p]
    ring
  rw [hAc, h0, h1]
  norm_num

theorem isAdmissibleContinuous_coupleA {p : TorsionParams} {e : ℝ}
    {A : Fin 3 → ℝ} (hp : IsAdmissibleContinuous p)
    (hβ : ∀ a, 0 ≤ p.beta a + e * A a)
    (hsum : ∀ a, p.alpha a + p.beta a + e * A a ≤ Real.pi / 2) :
    IsAdmissibleContinuous (coupleA p e A) := by
  intro a
  refine ⟨(hp a).1, hβ a, ?_⟩
  simpa [coupleA, add_assoc] using hsum a

theorem not_admissible_coupleA_of_neg_beta {p : TorsionParams} {e : ℝ}
    {A : Fin 3 → ℝ} {a : Fin 3} (h : p.beta a + e * A a < 0) :
    ¬ IsAdmissibleContinuous (coupleA p e A) := by
  intro hp
  exact (not_le.mpr h) (hp a).2.1

theorem circularPotential_neg_x {E0 ω : ℝ} :
    circularPotential 1 E0 ω (3 * Real.pi / 2) 0 = -(E0 / ω) := by
  simp [circularPotential, sin_three_pi_div_two]

/-- A zero-mean circular \(A\) on a vanishing dual seed leaves the cone. -/
theorem not_admissible_coupleA_circular_from_zeroDual
    {p : TorsionParams} {e E0 ω : ℝ} (hβ : p.beta 0 = 0)
    (he : 0 < e) (hE : 0 < E0) (hω : 0 < ω) :
    ¬ IsAdmissibleContinuous
        (coupleA p e (circularPotential 1 E0 ω (3 * Real.pi / 2))) := by
  apply not_admissible_coupleA_of_neg_beta (a := 0)
  rw [hβ, circularPotential_neg_x, zero_add]
  have hdiv : 0 < E0 / ω := div_pos hE hω
  nlinarith

/-! ### Written action: dual-only realisation of \(\theta=\theta_0+e A\) -/

/-- Holding \(\ddot\phi=0\) along \(\theta=\theta_0+e A\) uniquely requires
the constraint pair \(v=m\delta\), \(u=e\ddot A+m\delta\). -/
theorem paperBothSourcedEL_coupleA_jet (m φ θ0 e A Addot : ℝ) :
    PaperBothSourcedEL m φ (θ0 + e * A) 0 (e * Addot)
      (m * (φ - (θ0 + e * A)))
      (e * Addot + m * (φ - (θ0 + e * A))) := by
  constructor <;> ring

theorem dual_force_of_coupleA_jet {m φ θ0 e A Addot v u : ℝ}
    (h : PaperBothSourcedEL m φ (θ0 + e * A) 0 (e * Addot) v u) :
    v = m * (φ - (θ0 + e * A)) ∧
      u = e * Addot + m * (φ - (θ0 + e * A)) := by
  have hv := paperBothSourcedEL_constraint_force h rfl
  rcases h with ⟨_, hθ⟩
  refine ⟨hv, ?_⟩
  linarith

end Gravity

end DstDiophantine
