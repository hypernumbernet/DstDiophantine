import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.LorentzLie
import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Logic.Quantum.Spinor
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Baryon asymmetry and the sign of a vacuum excess

The observed yield \(\eta\) is not derived. What is fixed is the Killing
response of a chiral excess.

## What is proved

* A pure boost excess of magnitude \(\delta\) along a direction \(p\) has
  \(J = M = (\delta^2/2)\lVert p\rVert^2\). The pure rotation excess has the
  same mass and the opposite scalar. For \(\delta\neq 0\) and \(p\neq 0\),
  \(J/M = \pm 1\). Both scalars are even in \(\delta\).
* Swapping the sectors, or applying the dual map to the torsion bivector,
  exchanges the two excesses up to the sign of the rapidity and reverses \(J\).
  A second dual map multiplies every element by \(-1\).
* On one axis a balanced background of rapidity \(\varphi\), shifted by a
  boost excess \(\delta\), has \(J = \varphi\delta + \delta^2/2\) and
  \(M = \varphi^2 + \varphi\delta + \delta^2/2\). The two signs of \(\delta\)
  differ in mass by \(2\varphi\delta\). The cross term, and this mass
  difference, vanish for every \(\delta\) if and only if \(\varphi = 0\).
  Equal nonzero rapidities give \(J = 0\), \(M = \varphi^2\), and a relative
  rotor different from \(1\).
* Spatial inversion sends the pseudoscalar to its negative, negates each
  boost generator, and fixes each rotation generator. It preserves sectors:
  the image of a boost excess \(\delta\) is the boost excess \(-\delta\).
* On \(\mathbb{C}^2\) the dual rotor has determinant \(1\), so the argument
  of the determinant vanishes.

## Not claimed

No baryon current, no Sakharov identity, and no derivation of
\(\eta\sim 6\times 10^{-10}\).
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations Invariant Amplification
open RelativeRotor LorentzLie Motor
open CliffordAlgebra Logic Complex
open scoped Real

/-! ### Boost and rotation excesses -/

/-- Pure boost excess of rapidity scale `δ` along the direction `p`. -/
def boostAlong (δ : ℝ) (p : Fin 3 → ℝ) : TorsionParams where
  alpha := fun a => δ * p a
  beta := fun _ => 0

/-- Pure rotation excess of rapidity scale `δ` along the direction `p`. -/
def rotationAlong (δ : ℝ) (p : Fin 3 → ℝ) : TorsionParams where
  alpha := fun _ => 0
  beta := fun a => δ * p a

theorem dagger_boostAlong (δ : ℝ) (p : Fin 3 → ℝ) :
    daggerParams (boostAlong δ p) = rotationAlong δ p := by
  rfl

theorem J_boostAlong (δ : ℝ) (p : Fin 3 → ℝ) :
    J (boostAlong δ p) = (δ ^ 2 / 2) * ∑ a : Fin 3, p a ^ 2 := by
  rw [J_coef]
  have hsum : ∑ a : Fin 3, ((δ * p a) ^ 2 - 0 ^ 2) =
      δ ^ 2 * ∑ a : Fin 3, p a ^ 2 := by
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_pow]
    rw [← Finset.mul_sum]
  simp only [boostAlong, hsum]
  ring

theorem mass_boostAlong (δ : ℝ) (p : Fin 3 → ℝ) :
    mass (boostAlong δ p) = J (boostAlong δ p) := by
  rw [mass_coef, J_boostAlong]
  simp only [boostAlong, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, mul_pow]
  rw [← Finset.mul_sum]
  ring

theorem J_rotationAlong (δ : ℝ) (p : Fin 3 → ℝ) :
    J (rotationAlong δ p) = -J (boostAlong δ p) := by
  rw [J_coef, J_coef]
  simp only [rotationAlong, boostAlong, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    sub_zero, zero_sub, Fin.sum_univ_three]
  ring

theorem mass_rotationAlong (δ : ℝ) (p : Fin 3 → ℝ) :
    mass (rotationAlong δ p) = mass (boostAlong δ p) := by
  rw [mass_coef, mass_coef]
  simp only [rotationAlong, boostAlong, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    add_zero, zero_add, Fin.sum_univ_three]

theorem J_boostAlong_even (δ : ℝ) (p : Fin 3 → ℝ) :
    J (boostAlong (-δ) p) = J (boostAlong δ p) := by
  rw [J_boostAlong, J_boostAlong]
  ring

theorem mass_boostAlong_even (δ : ℝ) (p : Fin 3 → ℝ) :
    mass (boostAlong (-δ) p) = mass (boostAlong δ p) := by
  rw [mass_boostAlong, mass_boostAlong, J_boostAlong_even]

private theorem J_boostAlong_ne_zero {δ : ℝ} {p : Fin 3 → ℝ}
    (hδ : δ ≠ 0) (hp : ∑ a : Fin 3, p a ^ 2 ≠ 0) :
    J (boostAlong δ p) ≠ 0 := by
  rw [J_boostAlong]
  exact mul_ne_zero (div_ne_zero (pow_ne_zero 2 hδ) (by norm_num)) hp

theorem J_div_mass_boostAlong {δ : ℝ} {p : Fin 3 → ℝ}
    (hδ : δ ≠ 0) (hp : ∑ a : Fin 3, p a ^ 2 ≠ 0) :
    J (boostAlong δ p) / mass (boostAlong δ p) = 1 := by
  rw [mass_boostAlong]
  exact div_self (J_boostAlong_ne_zero hδ hp)

theorem J_div_mass_rotationAlong {δ : ℝ} {p : Fin 3 → ℝ}
    (hδ : δ ≠ 0) (hp : ∑ a : Fin 3, p a ^ 2 ≠ 0) :
    J (rotationAlong δ p) / mass (rotationAlong δ p) = -1 := by
  rw [J_rotationAlong, mass_rotationAlong, mass_boostAlong, neg_div,
    div_self (J_boostAlong_ne_zero hδ hp)]

theorem J_boostAlong_unit {δ : ℝ} {p : Fin 3 → ℝ}
    (hp : ∑ a : Fin 3, p a ^ 2 = 1) :
    J (boostAlong δ p) = δ ^ 2 / 2 ∧ mass (boostAlong δ p) = δ ^ 2 / 2 := by
  refine ⟨?_, ?_⟩
  · rw [J_boostAlong, hp]; ring
  · rw [mass_boostAlong, J_boostAlong, hp]; ring

theorem J_rotationAlong_unit {δ : ℝ} {p : Fin 3 → ℝ}
    (hp : ∑ a : Fin 3, p a ^ 2 = 1) :
    J (rotationAlong δ p) = -(δ ^ 2 / 2) ∧
      mass (rotationAlong δ p) = δ ^ 2 / 2 := by
  refine ⟨?_, ?_⟩
  · rw [J_rotationAlong, J_boostAlong, hp]; ring
  · rw [mass_rotationAlong, mass_boostAlong, J_boostAlong, hp]; ring

/-! ### One-axis balance is not the vacuum -/

theorem balanced_axis_mass (φ : ℝ) :
    J (axisParams φ φ) = 0 ∧ mass (axisParams φ φ) = φ ^ 2 := by
  refine ⟨J_axisParams_balanced φ, ?_⟩
  rw [mass_axisParams]
  ring

theorem balanced_axis_not_free_fall {φ : ℝ} (hφ : φ ≠ 0) :
    relativeRotor (axisParams φ φ) ≠ 1 := by
  intro h
  have hrot := (relativeRotor_eq_one_iff _).mp h
  have hs : Real.sinh (φ / 2) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact div_ne_zero hφ two_ne_zero
  exact balanced_axis_rotors_ne hs hrot

/-! ### Balanced background: the cross term -/

/-- Boost excess `δ` on top of a one-axis balance of rapidity `φ`. -/
def balancedBoostShift (φ δ : ℝ) : TorsionParams :=
  axisParams (φ + δ) φ

theorem balancedBoostShift_J (φ δ : ℝ) :
    J (balancedBoostShift φ δ) = φ * δ + δ ^ 2 / 2 := by
  rw [balancedBoostShift, J_axisParams]
  ring

theorem balancedBoostShift_mass (φ δ : ℝ) :
    mass (balancedBoostShift φ δ) = φ ^ 2 + φ * δ + δ ^ 2 / 2 := by
  rw [balancedBoostShift, mass_axisParams]
  ring

theorem balancedBoostShift_mass_split (φ δ : ℝ) :
    mass (balancedBoostShift φ δ) - mass (balancedBoostShift φ (-δ)) =
      2 * φ * δ := by
  rw [balancedBoostShift_mass, balancedBoostShift_mass]
  ring

/-- The vacuum quadratic law holds for every excess iff the background vanishes. -/
theorem balancedBoostShift_J_eq_quadratic_iff (φ : ℝ) :
    (∀ δ : ℝ, J (balancedBoostShift φ δ) = δ ^ 2 / 2) ↔ φ = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [balancedBoostShift_J] at h1
    linarith
  · intro hφ δ
    rw [balancedBoostShift_J, hφ]
    ring

/-- The two signs of the excess carry equal mass for every excess iff the background vanishes. -/
theorem balancedBoostShift_mass_split_iff (φ : ℝ) :
    (∀ δ : ℝ, mass (balancedBoostShift φ δ) = mass (balancedBoostShift φ (-δ))) ↔
      φ = 0 := by
  constructor
  · intro h
    have h1 := h 1
    have hs := balancedBoostShift_mass_split φ 1
    rw [h1, sub_self] at hs
    linarith
  · intro hφ δ
    rw [balancedBoostShift_mass, balancedBoostShift_mass, hφ]
    ring

/-! ### Dual conversion exchanges the vacuum excesses -/

theorem dualParams_axis_rotation (δ : ℝ) :
    dualParams (axisParams 0 δ) = axisParams δ 0 := by
  change TorsionParams.mk (axisParams 0 δ).beta (fun a => -((axisParams 0 δ).alpha a)) =
    axisParams δ 0
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a
    simp [axisParams]
  · funext a
    simp [axisParams]

theorem J_dual_axis_rotation (δ : ℝ) :
    J (dualParams (axisParams 0 δ)) = -J (axisParams 0 δ) :=
  J_dualParams (axisParams 0 δ)

theorem double_dual_negates (x : PGA) : dual (dual x) = -x :=
  dual_dual x

/-! ### Spatial inversion -/

/-- Sign of a basis vector under spatial inversion: time and the null axis stay, space flips. -/
def spatialSign (μ : Fin 5) : ℝ :=
  if μ = 0 ∨ μ = 4 then 1 else -1

@[simp] theorem spatialSign_zero : spatialSign 0 = 1 := by simp [spatialSign]
@[simp] theorem spatialSign_one : spatialSign 1 = -1 := by simp [spatialSign]
@[simp] theorem spatialSign_two : spatialSign 2 = -1 := by simp [spatialSign]
@[simp] theorem spatialSign_three : spatialSign 3 = -1 := by simp [spatialSign]
@[simp] theorem spatialSign_four : spatialSign 4 = 1 := by simp [spatialSign]

theorem spatialSign_sq (μ : Fin 5) : spatialSign μ * spatialSign μ = 1 := by
  fin_cases μ <;> simp [spatialSign]

/-- Spatial inversion on the underlying vector space. -/
noncomputable def spatialParityLM : Vec5 →ₗ[ℝ] Vec5 where
  toFun v := fun μ => spatialSign μ * v μ
  map_add' v w := by
    ext μ
    simp [mul_add]
  map_smul' c v := by
    ext μ
    simp [mul_left_comm]

theorem spatialParity_quad (v : Vec5) :
    Q311 (spatialParityLM v) = Q311 v := by
  simp only [Q311, QuadraticMap.weightedSumSquares_apply, spatialParityLM,
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hs := spatialSign_sq μ
  calc
    w311 μ * ((spatialSign μ * v μ) * (spatialSign μ * v μ))
        = w311 μ * ((spatialSign μ * spatialSign μ) * (v μ * v μ)) := by ring
    _ = w311 μ * (1 * (v μ * v μ)) := by rw [hs]
    _ = w311 μ * (v μ * v μ) := by ring

/-- Spatial inversion is a quadratic isometry of `G(3,1,1)`. -/
noncomputable def spatialParityIsometry : Q311 →qᵢ Q311 where
  toLinearMap := spatialParityLM
  map_app' := spatialParity_quad

/-- The induced algebra automorphism. -/
noncomputable def spatialParity : PGA →ₐ[ℝ] PGA :=
  CliffordAlgebra.map spatialParityIsometry

theorem spatialParity_ι (μ : Fin 5) :
    spatialParity (PGA.ι μ) = spatialSign μ • PGA.ι μ := by
  unfold spatialParity PGA.ι
  rw [CliffordAlgebra.map_apply_ι]
  have hcoe : (spatialParityIsometry : Vec5 →ₗ[ℝ] Vec5) = spatialParityLM := rfl
  have hvec : spatialParityLM (e5vec μ) = spatialSign μ • e5vec μ := by
    ext i
    simp only [spatialParityLM, LinearMap.coe_mk, AddHom.coe_mk, e5vec,
      Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases h : i = μ
    · subst h
      simp
    · simp [h]
  have happ :
      spatialParityIsometry (e5vec μ) = spatialParityLM (e5vec μ) :=
    congrArg (fun f : Vec5 →ₗ[ℝ] Vec5 => f (e5vec μ)) hcoe
  rw [happ, hvec, map_smul]

theorem spatialParity_pseudoscalar :
    spatialParity pseudoscalar = -pseudoscalar := by
  unfold pseudoscalar
  rw [map_mul, map_mul, map_mul, spatialParity_ι, spatialParity_ι, spatialParity_ι,
    spatialParity_ι, spatialSign_zero, spatialSign_one, spatialSign_two, spatialSign_three,
    one_smul]
  simp [mul_assoc]

theorem spatialParity_hyperbolic (a : Fin 3) :
    spatialParity (hyperbolic a) = -hyperbolic a := by
  fin_cases a <;>
    simp only [hyperbolic, map_mul, spatialParity_ι, spatialSign_zero, spatialSign_one,
      spatialSign_two, spatialSign_three, one_smul] <;>
    simp

theorem spatialParity_cyclic (a : Fin 3) :
    spatialParity (cyclic a) = cyclic a := by
  fin_cases a <;>
    simp only [cyclic, map_mul, spatialParity_ι, spatialSign_one, spatialSign_two,
      spatialSign_three] <;>
    simp

theorem spatialParity_boostExcess (δ : ℝ) :
    spatialParity (omegaTorsion (axisParams δ 0)) =
      omegaTorsion (axisParams (-δ) 0) := by
  rw [omegaTorsion_axisParams, omegaTorsion_axisParams, map_add, map_smul, map_smul,
    spatialParity_hyperbolic, spatialParity_cyclic]
  module

theorem spatialParity_rotationExcess (δ : ℝ) :
    spatialParity (omegaTorsion (axisParams 0 δ)) =
      omegaTorsion (axisParams 0 δ) := by
  rw [omegaTorsion_axisParams, map_add, map_smul, map_smul, spatialParity_hyperbolic,
    spatialParity_cyclic]
  module

/-! ### The dual rotor determinant carries no phase -/

theorem dualRotor_det_arg (β : DualRapidity) :
    (dualRotorMat β).det = 1 ∧ ((dualRotorMat β).det).arg = 0 := by
  have hdet : (dualRotorMat β).det = 1 := dualRotorMat_det β
  exact ⟨hdet, by rw [hdet]; exact arg_one⟩

end Gravity

end DstDiophantine
