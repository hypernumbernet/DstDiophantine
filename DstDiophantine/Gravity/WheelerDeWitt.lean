import DstDiophantine.Gravity.DualRotorDynamics
import DstDiophantine.Gravity.LorentzFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The written particle action is not a Wheeler–DeWitt constraint

The Maurer–Cartan curvature of a one-parameter rotor vanishes. That removes the curvature
factor of a connection constraint. It does not set the canonical Hamiltonian to zero.

The kinetic Hessian of the written action has determinant `-1` in the six rapidities, `-1`
on one axis, and `-1/4` in the mixed velocities. Every momentum is attained. The Jacobi
integral is that Hamiltonian, and it takes both signs on the Euler–Lagrange solutions.
The same-sign working model has kinetic determinant `+1` and is likewise unconstrained.
No wave functional of a spatial metric is constructed here.
-/

namespace DstDiophantine

namespace Gravity

/-! ### One-axis kinetic Hessian -/

noncomputable def paperKinetic (φdot θdot : ℝ) : ℝ :=
  (1 / 2) * φdot ^ 2 - (1 / 2) * θdot ^ 2

def paperKineticPhiSecond : ℝ := 1

def paperKineticThetaSecond : ℝ := -1

def paperKineticHessianDet : ℝ :=
  paperKineticPhiSecond * paperKineticThetaSecond

theorem paperLagrangian_eq_kinetic (m φ θ φdot θdot : ℝ) :
    paperLagrangian m φ θ φdot θdot =
      paperKinetic φdot θdot - (m / 2) * (φ - θ) ^ 2 := by
  unfold paperLagrangian paperKinetic
  ring

theorem paperKinetic_phi_second (φdot θdot s : ℝ) :
    paperKinetic (φdot + s) θdot - paperKinetic φdot θdot - s * φdot =
      (1 / 2) * paperKineticPhiSecond * s ^ 2 := by
  unfold paperKinetic paperKineticPhiSecond
  ring

theorem paperKinetic_theta_second (φdot θdot s : ℝ) :
    paperKinetic φdot (θdot + s) - paperKinetic φdot θdot - s * (-θdot) =
      (1 / 2) * paperKineticThetaSecond * s ^ 2 := by
  unfold paperKinetic paperKineticThetaSecond
  ring

theorem paperKinetic_cross (φdot θdot s t : ℝ) :
    paperKinetic (φdot + s) (θdot + t) - paperKinetic (φdot + s) θdot -
        paperKinetic φdot (θdot + t) + paperKinetic φdot θdot = 0 := by
  unfold paperKinetic
  ring

theorem paperKineticHessianDet_eq : paperKineticHessianDet = -1 := by
  unfold paperKineticHessianDet paperKineticPhiSecond paperKineticThetaSecond
  norm_num

/-- Sum of the three axial kinetic terms. Axes do not share a velocity. -/
noncomputable def paperKinetic3 (φdot θdot : Fin 3 → ℝ) : ℝ :=
  paperKinetic (φdot 0) (θdot 0) + paperKinetic (φdot 1) (θdot 1) +
    paperKinetic (φdot 2) (θdot 2)

theorem paperKinetic3_axes_separate (φdot θdot : Fin 3 → ℝ) (s t : ℝ) :
    paperKinetic3 (fun i => if i = 0 then φdot i + s else φdot i)
        (fun i => if i = 1 then θdot i + t else θdot i) -
      paperKinetic3 (fun i => if i = 0 then φdot i + s else φdot i) θdot -
      paperKinetic3 φdot (fun i => if i = 1 then θdot i + t else θdot i) +
      paperKinetic3 φdot θdot = 0 := by
  unfold paperKinetic3
  simp
  ring

/-- Three decoupled axes: the six-velocity determinant is the cube of the one-axis determinant. -/
def paperKineticHessianDet6 : ℝ :=
  paperKineticHessianDet * paperKineticHessianDet * paperKineticHessianDet

theorem paperKineticHessianDet6_eq : paperKineticHessianDet6 = -1 := by
  unfold paperKineticHessianDet6
  rw [paperKineticHessianDet_eq]
  norm_num

/-! ### Mixed velocities \((\dot\sigma,\dot\delta)\) -/

noncomputable def mixedKinetic (σdot δdot : ℝ) : ℝ :=
  (1 / 2) * σdot * δdot

noncomputable def mixedKineticCross : ℝ := 1 / 2

noncomputable def mixedKineticHessianDet : ℝ := -(mixedKineticCross ^ 2)

theorem mixedKinetic_sigma_linear (σdot δdot s : ℝ) :
    mixedKinetic (σdot + s) δdot - mixedKinetic σdot δdot = s * ((1 / 2) * δdot) := by
  unfold mixedKinetic
  ring

theorem mixedKinetic_delta_linear (σdot δdot t : ℝ) :
    mixedKinetic σdot (δdot + t) - mixedKinetic σdot δdot = t * ((1 / 2) * σdot) := by
  unfold mixedKinetic
  ring

theorem mixedKinetic_cross_second (σdot δdot s t : ℝ) :
    mixedKinetic (σdot + s) (δdot + t) - mixedKinetic (σdot + s) δdot -
        mixedKinetic σdot (δdot + t) + mixedKinetic σdot δdot =
      mixedKineticCross * s * t := by
  unfold mixedKinetic mixedKineticCross
  ring

theorem mixedKineticHessianDet_eq : mixedKineticHessianDet = -1 / 4 := by
  unfold mixedKineticHessianDet mixedKineticCross
  norm_num

/-! ### Legendre map and the Hamiltonian -/

noncomputable def paperHamiltonian (m φ θ pφ pθ : ℝ) : ℝ :=
  (1 / 2) * pφ ^ 2 - (1 / 2) * pθ ^ 2 + (m / 2) * (φ - θ) ^ 2

theorem paper_legendre (m φ θ pφ pθ : ℝ) :
    ∃ φdot θdot : ℝ,
      φdot = pφ ∧ θdot = -pθ ∧
        paperEnergy m φ θ φdot θdot = paperHamiltonian m φ θ pφ pθ ∧
          ∀ φdot' θdot' : ℝ, φdot' = pφ → θdot' = -pθ →
            φdot' = φdot ∧ θdot' = θdot := by
  refine ⟨pφ, -pθ, rfl, rfl, ?_, ?_⟩
  · unfold paperEnergy paperHamiltonian
    ring
  · intro φdot' θdot' hφ hθ
    exact ⟨hφ, hθ⟩

theorem paperHamiltonian_dphi (m φ θ pφ pθ s : ℝ) :
    paperHamiltonian m (φ + s) θ pφ pθ =
      paperHamiltonian m φ θ pφ pθ + s * (m * (φ - θ)) + (m / 2) * s ^ 2 := by
  unfold paperHamiltonian
  ring

theorem paperHamiltonian_dtheta (m φ θ pφ pθ s : ℝ) :
    paperHamiltonian m φ (θ + s) pφ pθ =
      paperHamiltonian m φ θ pφ pθ + s * (-(m * (φ - θ))) + (m / 2) * s ^ 2 := by
  unfold paperHamiltonian
  ring

theorem paperHamiltonian_dpphi (m φ θ pφ pθ s : ℝ) :
    paperHamiltonian m φ θ (pφ + s) pθ =
      paperHamiltonian m φ θ pφ pθ + s * pφ + (1 / 2) * s ^ 2 := by
  unfold paperHamiltonian
  ring

theorem paperHamiltonian_dptheta (m φ θ pφ pθ s : ℝ) :
    paperHamiltonian m φ θ pφ (pθ + s) =
      paperHamiltonian m φ θ pφ pθ + s * (-pθ) + (1 / 2) * (-1) * s ^ 2 := by
  unfold paperHamiltonian
  ring

/-- Hamilton's equations reproduce the written Euler–Lagrange system.
`φ̇ = ∂H/∂p_φ`, `θ̇ = ∂H/∂p_θ`, `ṗ_φ = −∂H/∂φ`, `ṗ_θ = −∂H/∂θ`,
and `θ̈` is the derivative of `θ̇ = −p_θ`. -/
theorem paperHamilton_equations_actualEL (m φ θ : ℝ) :
    PaperActualEL m φ θ (-m * (φ - θ)) (-m * (φ - θ)) :=
  (paperActualEL_eq m φ θ _ _).mpr ⟨rfl, rfl⟩

noncomputable def mixedHamiltonian (m δ pσ pδ : ℝ) : ℝ :=
  2 * pσ * pδ + (m / 2) * δ ^ 2

theorem mixed_legendre (m δ pσ pδ : ℝ) :
    ∃ σdot δdot : ℝ,
      σdot = 2 * pδ ∧ δdot = 2 * pσ ∧
        (1 / 2) * δdot = pσ ∧ (1 / 2) * σdot = pδ ∧
          mixedHamiltonian m δ pσ pδ =
            (1 / 2) * σdot * δdot + (m / 2) * δ ^ 2 := by
  refine ⟨2 * pδ, 2 * pσ, rfl, rfl, ?_, ?_, ?_⟩
  · ring
  · ring
  · unfold mixedHamiltonian
    ring

theorem mixedHamiltonian_eq_energy (m φ θ φdot θdot : ℝ) :
    mixedHamiltonian m (φ - θ) ((1 / 2) * (φdot - θdot)) ((1 / 2) * (φdot + θdot)) =
      paperEnergy m φ θ φdot θdot := by
  unfold mixedHamiltonian paperEnergy
  ring

/-! ### The integral is not a constraint on the solutions -/

theorem paperEnergy_negative_on_shell :
    PaperActualEL 1 0 0 0 0 ∧ paperEnergy 1 0 0 0 1 < 0 := by
  refine ⟨(paperActualEL_eq 1 0 0 0 0).mpr ⟨?_, ?_⟩, ?_⟩
  · norm_num
  · norm_num
  · unfold paperEnergy
    norm_num

theorem paperEnergy_positive_on_shell :
    PaperActualEL 1 1 0 (-1) (-1) ∧ 0 < paperEnergy 1 1 0 0 0 := by
  refine ⟨(paperActualEL_eq 1 1 0 (-1) (-1)).mpr ⟨?_, ?_⟩, ?_⟩
  · norm_num
  · norm_num
  · unfold paperEnergy
    norm_num

theorem paperEnergy_not_constraint_on_shell :
    ∃ m φ θ φdot θdot φddot θddot : ℝ,
      PaperActualEL m φ θ φddot θddot ∧ paperEnergy m φ θ φdot θdot ≠ 0 := by
  refine ⟨1, 0, 0, 0, 1, 0, 0, ?_, ?_⟩
  · exact paperEnergy_negative_on_shell.1
  · exact ne_of_lt paperEnergy_negative_on_shell.2

/-- Decoupled axes: one on-shell axis carries a nonzero energy and the other two are at rest. -/
theorem paperEnergy_six_not_constraint :
    PaperActualEL 1 0 0 0 0 ∧ paperEnergy 1 0 0 0 1 ≠ 0 ∧
      PaperActualEL 1 0 0 0 0 ∧ paperEnergy 1 0 0 0 0 = 0 ∧
        PaperActualEL 1 0 0 0 0 ∧ paperEnergy 1 0 0 0 0 = 0 ∧
          paperEnergy 1 0 0 0 1 + paperEnergy 1 0 0 0 0 + paperEnergy 1 0 0 0 0 ≠ 0 := by
  refine ⟨paperEnergy_negative_on_shell.1, ne_of_lt paperEnergy_negative_on_shell.2, ?_⟩
  have hrest : PaperActualEL 1 0 0 0 0 :=
    (paperActualEL_eq 1 0 0 0 0).mpr ⟨by norm_num, by norm_num⟩
  have hE : paperEnergy 1 0 0 0 0 = 0 := by
    unfold paperEnergy
    norm_num
  refine ⟨hrest, hE, hrest, hE, ?_⟩
  have hneg : paperEnergy 1 0 0 0 1 = -(1 / 2) := by
    unfold paperEnergy
    norm_num
  rw [hneg, hE]
  norm_num

/-! ### Same-sign working model -/

noncomputable def oscillatorKinetic (φdot θdot : ℝ) : ℝ :=
  (1 / 2) * φdot ^ 2 + (1 / 2) * θdot ^ 2

def oscillatorKineticHessianDet : ℝ := (1 : ℝ) * 1

theorem oscillatorLagrangian_eq_kinetic (m φ θ φdot θdot : ℝ) :
    oscillatorLagrangian m φ θ φdot θdot =
      oscillatorKinetic φdot θdot - (m / 2) * (φ - θ) ^ 2 := by
  unfold oscillatorLagrangian oscillatorKinetic
  ring

theorem oscillatorKinetic_phi_second (φdot θdot s : ℝ) :
    oscillatorKinetic (φdot + s) θdot - oscillatorKinetic φdot θdot - s * φdot =
      (1 / 2) * s ^ 2 := by
  unfold oscillatorKinetic
  ring

theorem oscillatorKinetic_theta_second (φdot θdot s : ℝ) :
    oscillatorKinetic φdot (θdot + s) - oscillatorKinetic φdot θdot - s * θdot =
      (1 / 2) * s ^ 2 := by
  unfold oscillatorKinetic
  ring

theorem oscillatorKinetic_cross (φdot θdot s t : ℝ) :
    oscillatorKinetic (φdot + s) (θdot + t) - oscillatorKinetic (φdot + s) θdot -
        oscillatorKinetic φdot (θdot + t) + oscillatorKinetic φdot θdot = 0 := by
  unfold oscillatorKinetic
  ring

theorem oscillatorKineticHessianDet_eq : oscillatorKineticHessianDet = 1 := by
  unfold oscillatorKineticHessianDet
  norm_num

noncomputable def oscillatorHamiltonian (m φ θ pφ pθ : ℝ) : ℝ :=
  (1 / 2) * pφ ^ 2 + (1 / 2) * pθ ^ 2 + (m / 2) * (φ - θ) ^ 2

theorem oscillator_legendre (m φ θ pφ pθ : ℝ) :
    ∃ φdot θdot : ℝ,
      φdot = pφ ∧ θdot = pθ ∧
        oscillatorEnergy m φ θ φdot θdot = oscillatorHamiltonian m φ θ pφ pθ := by
  refine ⟨pφ, pθ, rfl, rfl, ?_⟩
  unfold oscillatorEnergy oscillatorHamiltonian
  ring

theorem oscillatorEnergy_positive_on_shell :
    OscillatorEL 1 1 0 (-1) 1 ∧ 0 < oscillatorEnergy 1 1 0 0 0 := by
  refine ⟨(oscillatorEL_eq 1 1 0 (-1) 1).mpr ⟨?_, ?_⟩, ?_⟩
  · norm_num
  · norm_num
  · unfold oscillatorEnergy
    norm_num

theorem oscillatorEnergy_not_constraint_on_shell :
    ∃ m φ θ φdot θdot φddot θddot : ℝ,
      OscillatorEL m φ θ φddot θddot ∧ oscillatorEnergy m φ θ φdot θdot ≠ 0 := by
  refine ⟨1, 1, 0, 0, 0, -1, 1, oscillatorEnergy_positive_on_shell.1, ?_⟩
  exact ne_of_gt oscillatorEnergy_positive_on_shell.2

/-! ### Vanishing rotor curvature does not impose the constraint -/

theorem oneParam_curvature_leaves_energy_free (c : PGA) :
    (0 : PGA) + (c * c - c * c) = 0 ∧
      (∃ m φ θ φdot θdot φddot θddot : ℝ,
        PaperActualEL m φ θ φddot θddot ∧ paperEnergy m φ θ φdot θdot ≠ 0) :=
  ⟨oneParam_curvature c, paperEnergy_not_constraint_on_shell⟩

end Gravity

end DstDiophantine
