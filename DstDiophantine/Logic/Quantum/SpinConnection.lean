import DstDiophantine.Logic.Quantum.DiracCovariance
import DstDiophantine.Logic.Quantum.DiracField
import DstDiophantine.Logic.Quantum.UsualRotor
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Pure-gauge spin connection of a one-parameter boost

`¼[γ⁰, γ¹]` is the logarithmic derivative of the Dirac-matrix image of the
axis-0 boost rotor. Subtracting that term from the partial derivative cancels
the derivative which hits the rotor, so the coupled derivative is the rotor
applied to the flat derivative. A constant rotor, the same substitution with
vanishing profile derivative, sends a momentum-space solution to a solution.
The ponderomotive Hamiltonian is not used.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

def gammaComm (b c : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  diracMat b * diracMat c - diracMat c * diracMat b

/-- `¼[γ_b, γ_c]`. -/
noncomputable def spinGen (b c : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 4 : ℂ) • gammaComm b c

theorem spinGen_boost :
    spinGen 0 1 =
      blockDiag2 ((1 / 2 : ℂ) • pauli 0) ((-(1 / 2 : ℂ)) • pauli 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinGen, gammaComm, diracMat, diracMat0, diracMat1, blockDiag2, pauli, pauliX,
      Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four] <;>
    ring

noncomputable def halfR (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh (θ / 2), Real.sinh (θ / 2); Real.sinh (θ / 2), Real.cosh (θ / 2)]

noncomputable def halfInvR (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh (θ / 2), -Real.sinh (θ / 2); -Real.sinh (θ / 2), Real.cosh (θ / 2)]

noncomputable def halfDerivR (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((1 : ℝ) / 2) * Real.sinh (θ / 2), ((1 : ℝ) / 2) * Real.cosh (θ / 2);
     ((1 : ℝ) / 2) * Real.cosh (θ / 2), ((1 : ℝ) / 2) * Real.sinh (θ / 2)]

noncomputable def halfInvDerivR (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((1 : ℝ) / 2) * Real.sinh (θ / 2), -(((1 : ℝ) / 2) * Real.cosh (θ / 2));
     -(((1 : ℝ) / 2) * Real.cosh (θ / 2)), ((1 : ℝ) / 2) * Real.sinh (θ / 2)]

def embedR (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (M i j : ℂ)

private theorem cosh_half (θ : ℝ) :
    Real.cosh (θ * (1 / 2)) ^ 2 - Real.sinh (θ * (1 / 2)) ^ 2 = 1 := by
  simpa [div_eq_mul_inv] using Real.cosh_sq_sub_sinh_sq (θ / 2)

theorem halfR_mul_inv (θ : ℝ) : halfR θ * halfInvR θ = 1 := by
  have h := cosh_half θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfR, halfInvR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring_nf <;> linarith

theorem halfDerivR_mul_inv (θ : ℝ) :
    halfDerivR θ * halfInvR θ = ((1 : ℝ) / 2) • !![0, 1; 1, 0] := by
  have h := cosh_half θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfDerivR, halfInvR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    ring_nf <;> linarith

theorem halfInvDerivR_mul_half (θ : ℝ) :
    halfInvDerivR θ * halfR θ = -(((1 : ℝ) / 2) • !![0, 1; 1, 0]) := by
  have h := cosh_half θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfInvDerivR, halfR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] <;>
    ring_nf <;> linarith

theorem usual_boost_eq_half (θ : ℝ) :
    usualRotorMat (EuclideanSpace.single 0 θ) = embedR (halfR θ) := by
  rw [usualRotorMat_axis0_rodrigues]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedR, halfR, pauli, pauliX, Matrix.add_apply, Matrix.smul_apply]

private theorem conj_cosh_half (θ : ℝ) :
    starRingEnd ℂ (Complex.cosh ((θ : ℂ) / 2)) = Complex.cosh ((θ : ℂ) / 2) := by
  have harg : (θ : ℂ) / 2 = ((θ / 2 : ℝ) : ℂ) := by
    simp [div_eq_mul_inv]
  rw [harg, ← Complex.ofReal_cosh, Complex.conj_ofReal]

private theorem conj_sinh_half (θ : ℝ) :
    starRingEnd ℂ (Complex.sinh ((θ : ℂ) / 2)) = Complex.sinh ((θ : ℂ) / 2) := by
  have harg : (θ : ℂ) / 2 = ((θ / 2 : ℝ) : ℂ) := by
    simp [div_eq_mul_inv]
  rw [harg, ← Complex.ofReal_sinh, Complex.conj_ofReal]

theorem rotorLower_half (θ : ℝ) : rotorLower (embedR (halfR θ)) = embedR (halfInvR θ) := by
  rw [rotorLower, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedR, halfR, halfInvR, Matrix.conjTranspose_apply, map_neg, conj_cosh_half,
      conj_sinh_half]

theorem boost_diracMat (θ : ℝ) :
    rotorDiracMat (usualRotorMat (EuclideanSpace.single 0 θ)) =
      blockDiag2 (embedR (halfR θ)) (embedR (halfInvR θ)) := by
  rw [rotorDiracMat, usual_boost_eq_half, rotorLower_half]

/-- Block embedding of the logarithmic derivatives equals `¼[γ⁰,γ¹]`. -/
theorem boost_logDeriv (θ : ℝ) :
    blockDiag2 (embedR (halfDerivR θ * halfInvR θ))
        (embedR (halfInvDerivR θ * halfR θ)) =
      spinGen 0 1 := by
  rw [halfDerivR_mul_inv, halfInvDerivR_mul_half, spinGen_boost]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag2, embedR, pauli, pauliX, Matrix.smul_apply, Matrix.neg_apply]

theorem pureGauge_cancels (G S dS : Matrix (Fin 4) (Fin 4) ℂ) (hdS : dS = G * S)
    (rate : ℂ) (ψ dψ : DiracSpinor) :
    rate • applyDiracMat dS ψ + applyDiracMat S dψ -
        rate • applyDiracMat G (applyDiracMat S ψ) =
      applyDiracMat S dψ := by
  have hmul : applyDiracMat (G * S) ψ = applyDiracMat G (applyDiracMat S ψ) := by
    simp [applyDiracMat, Matrix.mulVec_mulVec]
  rw [hdS, hmul]
  abel

/-- After the pure-gauge subtraction, each partial of the dressed spinor is the
rotor applied to the flat partial. -/
theorem pureGauge_reduces (S dS : Matrix (Fin 4) (Fin 4) ℂ)
    (hdS : dS = spinGen 0 1 * S) (rate : ℂ) (ψ dψ : DiracSpinor)
    (dressed : DiracSpinor)
    (hchain : dressed = rate • applyDiracMat dS ψ + applyDiracMat S dψ) :
    dressed - rate • applyDiracMat (spinGen 0 1) (applyDiracMat S ψ) =
      applyDiracMat S dψ := by
  rw [hchain]
  exact pureGauge_cancels (spinGen 0 1) S dS hdS rate ψ dψ

/-- A constant axis-0 boost sends a momentum-space solution to a solution. -/
theorem constant_boost_sends_solution {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (θ : ℝ)
    (h : DiracMomentum m p Ψ) :
    DiracMomentum m (lorentzAct (usualRotorMat (EuclideanSpace.single 0 θ)) p)
      (rotorDirac (usualRotorMat (EuclideanSpace.single 0 θ)) Ψ) :=
  diracMomentum_rotorDirac (usualRotorMat_axis0_det θ) h

end Logic

end DstDiophantine
