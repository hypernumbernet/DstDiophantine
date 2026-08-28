import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Motor
import DstDiophantine.Logic.Quantum.DualSector
import Mathlib.Tactic.Ring

/-!
# Quaternion relations among the cyclic generators

The three cyclic generators satisfy the quaternion multiplication table
\[
(\texttt{cyclic } a)^2 = -1,\qquad
\texttt{cyclic } 0\cdot\texttt{cyclic } 1 = \texttt{cyclic } 2
\]
and cyclic permutations, with opposite order giving the minus sign.

These identities are computed in `G(3,1,1)` from the vector anticommutators.
The Lean signs are authoritative if they disagree with a paper draft.
-/

namespace DstDiophantine

namespace Logic

open PGA Generators CliffordAlgebra

private theorem e2_sq' : ι 2 * ι 2 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (2 : Fin 5)

private theorem e3_sq' : ι 3 * ι 3 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (3 : Fin 5)

/-- `I J = K`. -/
theorem cyclic_zero_mul_one : cyclic 0 * cyclic 1 = cyclic 2 := by
  dsimp [cyclic]
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  have h12 : ι 1 * ι 2 = -(ι 2 * ι 1) := e_mul_anticomm (by decide)
  calc ι 3 * ι 2 * (ι 1 * ι 3)
      = ι 3 * (ι 2 * ι 1) * ι 3 := by simp [mul_assoc]
    _ = ι 3 * (-(ι 1 * ι 2)) * ι 3 := by rw [h21]
    _ = -(ι 3 * ι 1) * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = -(-(ι 1 * ι 3)) * ι 2 * ι 3 := by rw [h31]
    _ = ι 1 * ι 3 * ι 2 * ι 3 := by simp [mul_assoc]
    _ = ι 1 * (ι 3 * ι 2) * ι 3 := by simp [mul_assoc]
    _ = ι 1 * (-(ι 2 * ι 3)) * ι 3 := by rw [h32]
    _ = -(ι 1 * ι 2) * (ι 3 * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -(ι 1 * ι 2) := by simp [e3_sq']
    _ = ι 2 * ι 1 := by
        rw [h12, neg_neg]

/-- `J K = I`. -/
theorem cyclic_one_mul_two : cyclic 1 * cyclic 2 = cyclic 0 := by
  dsimp [cyclic]
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  calc ι 1 * ι 3 * (ι 2 * ι 1)
      = ι 1 * (ι 3 * ι 2) * ι 1 := by simp [mul_assoc]
    _ = ι 1 * (-(ι 2 * ι 3)) * ι 1 := by rw [h32]
    _ = -(ι 1 * ι 2) * ι 3 * ι 1 := by simp [mul_neg, mul_assoc]
    _ = -(ι 1 * ι 2) * (ι 3 * ι 1) := by simp [mul_assoc]
    _ = -(ι 1 * ι 2) * (-(ι 1 * ι 3)) := by rw [h31]
    _ = ι 1 * ι 2 * ι 1 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = ι 1 * (ι 2 * ι 1) * ι 3 := by simp [mul_assoc]
    _ = ι 1 * (-(ι 1 * ι 2)) * ι 3 := by rw [h21]
    _ = -(ι 1 * ι 1) * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = -(ι 2 * ι 3) := by simp [e1_sq]
    _ = ι 3 * ι 2 := by
        rw [h23, neg_neg]

/-- `K I = J`. -/
theorem cyclic_two_mul_zero : cyclic 2 * cyclic 0 = cyclic 1 := by
  dsimp [cyclic]
  have h13 : ι 1 * ι 3 = -(ι 3 * ι 1) := e_mul_anticomm (by decide)
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  calc ι 2 * ι 1 * (ι 3 * ι 2)
      = ι 2 * (ι 1 * ι 3) * ι 2 := by simp [mul_assoc]
    _ = ι 2 * (-(ι 3 * ι 1)) * ι 2 := by rw [h13]
    _ = -(ι 2 * ι 3) * ι 1 * ι 2 := by simp [mul_neg, mul_assoc]
    _ = -(-(ι 3 * ι 2)) * ι 1 * ι 2 := by rw [h23]
    _ = ι 3 * ι 2 * ι 1 * ι 2 := by simp [mul_assoc]
    _ = ι 3 * (ι 2 * ι 1) * ι 2 := by simp [mul_assoc]
    _ = ι 3 * (-(ι 1 * ι 2)) * ι 2 := by rw [h21]
    _ = -(ι 3 * ι 1) * (ι 2 * ι 2) := by simp [mul_neg, mul_assoc]
    _ = -(ι 3 * ι 1) := by simp [e2_sq']
    _ = ι 1 * ι 3 := by
        rw [h31, neg_neg]

/-- Opposite order: `J I = -K`. -/
theorem cyclic_one_mul_zero : cyclic 1 * cyclic 0 = -cyclic 2 := by
  have hsq : cyclic 1 * cyclic 1 = -1 := cyclic_sq 1
  -- cyclic 0 * cyclic 1 = cyclic 2, multiply left by cyclic 1:
  -- cyclic 1 * cyclic 0 * cyclic 1 = cyclic 1 * cyclic 2 = cyclic 0
  have hL : cyclic 1 * cyclic 0 * cyclic 1 = cyclic 0 := by
    calc cyclic 1 * cyclic 0 * cyclic 1
        = cyclic 1 * (cyclic 0 * cyclic 1) := by simp [mul_assoc]
      _ = cyclic 1 * cyclic 2 := by rw [cyclic_zero_mul_one]
      _ = cyclic 0 := cyclic_one_mul_two
  -- multiply right by -cyclic 1
  have : cyclic 1 * cyclic 0 * cyclic 1 * (-cyclic 1) = cyclic 0 * (-cyclic 1) := by
    rw [hL]
  -- LHS reduces by `cyclic 1 * cyclic 1 = -1`.
  have hLHS : cyclic 1 * cyclic 0 * cyclic 1 * (-cyclic 1) = cyclic 1 * cyclic 0 := by
    have : cyclic 1 * (-cyclic 1) = - (cyclic 1 * cyclic 1) := by simp [mul_neg]
    calc cyclic 1 * cyclic 0 * cyclic 1 * (-cyclic 1)
        = cyclic 1 * cyclic 0 * (cyclic 1 * (-cyclic 1)) := by simp [mul_assoc]
      _ = cyclic 1 * cyclic 0 * (-(cyclic 1 * cyclic 1)) := by rw [this]
      _ = cyclic 1 * cyclic 0 * (-(-1)) := by rw [hsq]
      _ = cyclic 1 * cyclic 0 := by simp
  have hRHS : cyclic 0 * (-cyclic 1) = -cyclic 2 := by
    calc cyclic 0 * (-cyclic 1)
        = -(cyclic 0 * cyclic 1) := by simp [mul_neg]
      _ = -cyclic 2 := by rw [cyclic_zero_mul_one]
  rw [hLHS] at this
  rw [this, hRHS]

/-- Opposite order: `K J = -I`. -/
theorem cyclic_two_mul_one : cyclic 2 * cyclic 1 = -cyclic 0 := by
  have hsq : cyclic 2 * cyclic 2 = -1 := cyclic_sq 2
  have hL : cyclic 2 * cyclic 1 * cyclic 2 = cyclic 1 := by
    calc cyclic 2 * cyclic 1 * cyclic 2
        = cyclic 2 * (cyclic 1 * cyclic 2) := by simp [mul_assoc]
      _ = cyclic 2 * cyclic 0 := by rw [cyclic_one_mul_two]
      _ = cyclic 1 := cyclic_two_mul_zero
  have hLHS : cyclic 2 * cyclic 1 * cyclic 2 * (-cyclic 2) = cyclic 2 * cyclic 1 := by
    have : cyclic 2 * (-cyclic 2) = - (cyclic 2 * cyclic 2) := by simp [mul_neg]
    calc cyclic 2 * cyclic 1 * cyclic 2 * (-cyclic 2)
        = cyclic 2 * cyclic 1 * (cyclic 2 * (-cyclic 2)) := by simp [mul_assoc]
      _ = cyclic 2 * cyclic 1 * (-(cyclic 2 * cyclic 2)) := by rw [this]
      _ = cyclic 2 * cyclic 1 * (-(-1)) := by rw [hsq]
      _ = cyclic 2 * cyclic 1 := by simp
  have hRHS : cyclic 1 * (-cyclic 2) = -cyclic 0 := by
    calc cyclic 1 * (-cyclic 2)
        = -(cyclic 1 * cyclic 2) := by simp [mul_neg]
      _ = -cyclic 0 := by rw [cyclic_one_mul_two]
  have : cyclic 2 * cyclic 1 * cyclic 2 * (-cyclic 2) = cyclic 1 * (-cyclic 2) := by
    rw [hL]
  rw [hLHS] at this
  rw [this, hRHS]

/-- Opposite order: `I K = -J`. -/
theorem cyclic_zero_mul_two : cyclic 0 * cyclic 2 = -cyclic 1 := by
  have hsq : cyclic 0 * cyclic 0 = -1 := cyclic_sq 0
  have hL : cyclic 0 * cyclic 2 * cyclic 0 = cyclic 2 := by
    calc cyclic 0 * cyclic 2 * cyclic 0
        = cyclic 0 * (cyclic 2 * cyclic 0) := by simp [mul_assoc]
      _ = cyclic 0 * cyclic 1 := by rw [cyclic_two_mul_zero]
      _ = cyclic 2 := cyclic_zero_mul_one
  have hLHS : cyclic 0 * cyclic 2 * cyclic 0 * (-cyclic 0) = cyclic 0 * cyclic 2 := by
    have : cyclic 0 * (-cyclic 0) = - (cyclic 0 * cyclic 0) := by simp [mul_neg]
    calc cyclic 0 * cyclic 2 * cyclic 0 * (-cyclic 0)
        = cyclic 0 * cyclic 2 * (cyclic 0 * (-cyclic 0)) := by simp [mul_assoc]
      _ = cyclic 0 * cyclic 2 * (-(cyclic 0 * cyclic 0)) := by rw [this]
      _ = cyclic 0 * cyclic 2 * (-(-1)) := by rw [hsq]
      _ = cyclic 0 * cyclic 2 := by simp
  have hRHS : cyclic 2 * (-cyclic 0) = -cyclic 1 := by
    calc cyclic 2 * (-cyclic 0)
        = -(cyclic 2 * cyclic 0) := by simp [mul_neg]
      _ = -cyclic 1 := by rw [cyclic_two_mul_zero]
  have : cyclic 0 * cyclic 2 * cyclic 0 * (-cyclic 0) = cyclic 2 * (-cyclic 0) := by
    rw [hL]
  rw [hLHS] at this
  rw [this, hRHS]

/-- Pure dual torsion bivector is the cyclic combination of the dual rapidity. -/
theorem omegaTorsion_ofDual (β : DualRapidity) :
    Motor.omegaTorsion (ofDual β) = ∑ a : Fin 3, (β a / 2) • cyclic a := by
  simp [Motor.omegaTorsion, ofDual]

theorem omegaTorsion_ofDual_axis0 (θ : ℝ) :
    Motor.omegaTorsion (ofDual (EuclideanSpace.single 0 θ)) = (θ / 2) • cyclic 0 := by
  rw [omegaTorsion_ofDual]
  simp [PiLp.single_apply, Fin.sum_univ_three]

end Logic

end DstDiophantine
