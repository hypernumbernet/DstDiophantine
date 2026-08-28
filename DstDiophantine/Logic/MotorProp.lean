import DstDiophantine.Logic.Geometric
import DstDiophantine.Logic.Dynamics
import DstDiophantine.Algebra.Amplification

/-!
# Phase 7r L2: motor propositions

Separates the **additive** Diophantine motor (null translation) from the
**multiplicative** torsion-amplitude layer. No new arithmetic; no `Theorems`.

* Pure translation ⇒ vanishing torsion ⇒ vacuum amplitude (labels do not move).
* Live object is `motor := R·T`; not identified with `exp(Ω_biv)` when mixed.
-/

namespace DstDiophantine

namespace Logic

open Admissible Amplification Invariant Motor Operations Generators

/-- Alias of `zeroParams` for the L2 motor reading. -/
abbrev zeroTorsion : TorsionParams := zeroParams

theorem isAdmissibleContinuous_zeroTorsion :
    IsAdmissibleContinuous zeroTorsion := by
  intro a
  refine ⟨by simp only [zeroTorsion, zeroParams, le_refl],
    by simp only [zeroTorsion, zeroParams, le_refl], ?_⟩
  simp only [zeroTorsion, zeroParams, add_zero]
  exact div_nonneg (Real.pi_pos.le) (by norm_num)

/-- Vanishing torsion reduces the motor to the null translator. -/
theorem motor_of_pure_translation (p : TransParams) :
    motor ⟨zeroTorsion, p⟩ = expTrans p := by
  simp only [motor, zeroTorsion, zeroParams, rotorTorsion]
  have hω : omegaTorsion ⟨fun _ => 0, fun _ => 0⟩ = 0 := by
    simp [omegaTorsion]
  rw [hω, NormedSpace.exp_zero, one_mul]

/-- Pure-translation motors have vacuum torsion amplitude. -/
theorem pure_translation_torsion_isVacuum :
    (⟨zeroTorsion, isAdmissibleContinuous_zeroTorsion⟩ : Amplitude).IsVacuum := by
  refine (Amplitude.isVacuum_iff_mass_eq_zero _).mpr ?_
  exact (mass_eq_zero_iff zeroTorsion).mpr fun _ => by simp [zeroTorsion, zeroParams]

/-- When translation vanishes, `motor = R = exp(Ω_biv)`. -/
theorem motor_eq_exp_omegaBiv_of_zero_trans (t : TorsionParams) :
    motor ⟨t, ⟨fun _ => 0⟩⟩ = NormedSpace.exp (omegaBiv ⟨t, ⟨fun _ => 0⟩⟩) := by
  have hω : omegaTrans ⟨fun _ => 0⟩ = 0 := by
    simp [omegaTrans]
  have hT : expTrans ⟨fun _ => 0⟩ = 1 := by
    simp [expTrans, hω]
  have hB : omegaBiv ⟨t, ⟨fun _ => 0⟩⟩ = omegaTorsion t := by
    simp [omegaBiv, hω]
  simp only [motor, hT, mul_one, rotorTorsion, hB]

/-- When torsion vanishes, `motor = expTrans` and `Ω_biv = Ω_trans`
(truncated translator). Mixed `R·T` is not claimed equal to `exp(Ω_biv)`. -/
theorem motor_of_zero_torsion_eq_expTrans (p : TransParams) :
    motor ⟨zeroTorsion, p⟩ = expTrans p ∧
      omegaBiv ⟨zeroTorsion, p⟩ = omegaTrans p :=
  ⟨motor_of_pure_translation p,
    by simp [omegaBiv, zeroTorsion, zeroParams, omegaTorsion]⟩

/-- Additive vacuum and multiplicative balanced massive are distinct `T` seats. -/
theorem additive_vacuum_ne_multiplicative_balanced :
    vacuumAmplitude.IsVacuum ∧ balancedAmplitude.IsBalancedMassive ∧
      ¬ vacuumAmplitude.IsBalancedMassive ∧ ¬ balancedAmplitude.IsVacuum := by
  refine ⟨vacuumAmplitude_isVacuum, balancedAmplitude_isBalancedMassive, ?_, ?_⟩
  · intro h
    exact (not_le.mpr h.2) (le_of_eq vacuumAmplitude_isVacuum.2)
  · exact Amplitude.not_vacuum_of_balancedMassive balancedAmplitude_isBalancedMassive

end Logic

end DstDiophantine
