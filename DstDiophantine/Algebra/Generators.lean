import DstDiophantine.Algebra.PGA
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Ten bivector generators of G(3,1,1)

Hyperbolic (`iI,iJ,iK`), cyclic (`I,J,K`), and null (`N₀…N₃`) generators.

## Lie-algebra status

The six hyperbolic–cyclic generators span a candidate copy of `𝔰𝔬(3,1)`
(Lorentz), and the four null generators form an abelian translation ideal under
the geometric product (`N_μ N_ν = 0`).  Together they are the standard
**Poincaré** candidate `𝔰𝔬(3,1) ⋉ ℝ^{3,1}` inside `G(3,1,1)`.

We deliberately **do not** call the six generators `𝔰𝔬(3,1) ⊕ 𝔰𝔬(3,1)`: that
would be twelve-dimensional.  Full Lie-bracket isomorphism theorems are not
claimed here; only product squares, strong null vanishing, and a minimal
commutator API are formalised.
-/

namespace DstDiophantine

open CliffordAlgebra PGA

namespace Generators

/-- Geometric commutator `[x,y] = xy - yx`. -/
noncomputable def commutator (x y : PGA) : PGA :=
  x * y - y * x

/-- Hyperbolic boost generators `B⁺ₐ = e₀ e_{a+1}` for `a = 0,1,2`. -/
noncomputable def hyperbolic : Fin 3 → PGA
  | 0 => ι 0 * ι 1
  | 1 => ι 0 * ι 2
  | 2 => ι 0 * ι 3

/-- Cyclic rotation generators `B⁻₀ = e₃ e₂`, `B⁻₁ = e₁ e₃`, `B⁻₂ = e₂ e₁`. -/
noncomputable def cyclic : Fin 3 → PGA
  | 0 => ι 3 * ι 2
  | 1 => ι 1 * ι 3
  | 2 => ι 2 * ι 1

/-- Null translation generators `N_μ = e₄ ∧ e_μ`. -/
noncomputable def null (μ : Fin 4) : PGA :=
  ι e4Index * ι (Fin.castAdd 1 μ)

@[simp] theorem reverse_ι (μ : Fin 5) : reverse (ι μ) = ι μ := by
  simp only [PGA.ι, CliffordAlgebra.reverse_ι]

/-- Square of a simple bivector: `(eᵢ eⱼ)² = -Q(eᵢ) Q(eⱼ)`. -/
theorem ι_mul_ι_sq (i j : Fin 5) (hij : i ≠ j) :
    (ι i * ι j) * (ι i * ι j) =
      -(algebraMap ℝ PGA (Q311 (e5vec i)) * algebraMap ℝ PGA (Q311 (e5vec j))) := by
  calc (ι i * ι j) * (ι i * ι j)
      = ι i * (ι j * ι i) * ι j := by simp [mul_assoc]
    _ = ι i * (-(ι i * ι j)) * ι j := by rw [e_mul_anticomm hij.symm]
    _ = -(ι i * ι i * (ι j * ι j)) := by simp [mul_neg, mul_assoc]
    _ = -(algebraMap ℝ PGA (Q311 (e5vec i)) * algebraMap ℝ PGA (Q311 (e5vec j))) := by
        rw [e_sq i, e_sq j]

/-- Reverse of a simple bivector: `(eᵢ eⱼ)˜ = -eᵢ eⱼ` when `i ≠ j`. -/
theorem reverse_ι_mul_ι (i j : Fin 5) (hij : i ≠ j) :
    reverse (ι i * ι j) = -(ι i * ι j) := by
  rw [CliffordAlgebra.reverse.map_mul, reverse_ι, reverse_ι, e_mul_anticomm hij.symm]

private theorem hyperbolic_sq_of {i j : Fin 5} (hij : i ≠ j)
    (hi : Q311 (e5vec i) = -1) (hj : Q311 (e5vec j) = 1) :
    (ι i * ι j) * (ι i * ι j) = 1 := by
  rw [ι_mul_ι_sq i j hij, hi, hj]
  simp

private theorem cyclic_sq_of {i j : Fin 5} (hij : i ≠ j)
    (hi : Q311 (e5vec i) = 1) (hj : Q311 (e5vec j) = 1) :
    (ι i * ι j) * (ι i * ι j) = -1 := by
  rw [ι_mul_ι_sq i j hij, hi, hj]
  simp

theorem hyperbolic_sq (a : Fin 3) : hyperbolic a * hyperbolic a = 1 := by
  fin_cases a
  · exact hyperbolic_sq_of (by decide : (0 : Fin 5) ≠ 1) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])
  · exact hyperbolic_sq_of (by decide : (0 : Fin 5) ≠ 2) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])
  · exact hyperbolic_sq_of (by decide : (0 : Fin 5) ≠ 3) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])

theorem cyclic_sq (a : Fin 3) : cyclic a * cyclic a = -1 := by
  fin_cases a
  · exact cyclic_sq_of (by decide : (3 : Fin 5) ≠ 2) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])
  · exact cyclic_sq_of (by decide : (1 : Fin 5) ≠ 3) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])
  · exact cyclic_sq_of (by decide : (2 : Fin 5) ≠ 1) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])

theorem null_sq (μ : Fin 4) : null μ * null μ = 0 := by
  dsimp [null]
  calc ι e4Index * ι (Fin.castAdd 1 μ) * (ι e4Index * ι (Fin.castAdd 1 μ))
      = ι e4Index * (ι (Fin.castAdd 1 μ) * ι e4Index) * ι (Fin.castAdd 1 μ) := by simp [mul_assoc]
    _ = ι e4Index * (-(ι e4Index * ι (Fin.castAdd 1 μ))) * ι (Fin.castAdd 1 μ) := by
        rw [e4_inner_anticomm μ]
    _ = -(ι e4Index * ι e4Index * ι (Fin.castAdd 1 μ) * ι (Fin.castAdd 1 μ)) := by
        simp [mul_assoc]
    _ = 0 := by simp [e4_sq_zero]

/-- Strong null vanishing: `N_μ N_ν = 0` for all `μ, ν`. -/
theorem null_mul_null (μ ν : Fin 4) : null μ * null ν = 0 := by
  dsimp [null]
  calc ι e4Index * ι (Fin.castAdd 1 μ) * (ι e4Index * ι (Fin.castAdd 1 ν))
      = ι e4Index * (ι (Fin.castAdd 1 μ) * ι e4Index) * ι (Fin.castAdd 1 ν) := by simp [mul_assoc]
    _ = ι e4Index * (-(ι e4Index * ι (Fin.castAdd 1 μ))) * ι (Fin.castAdd 1 ν) := by
        rw [e4_inner_anticomm μ]
    _ = -(ι e4Index * ι e4Index * ι (Fin.castAdd 1 μ) * ι (Fin.castAdd 1 ν)) := by
        simp [mul_assoc]
    _ = 0 := by simp [e4_sq_zero]

theorem commutator_null_null (μ ν : Fin 4) :
    commutator (null μ) (null ν) = 0 := by
  simp [commutator, null_mul_null]

/-- Null generators form an abelian ideal under the geometric product. -/
theorem null_commute (μ ν : Fin 4) : Commute (null μ) (null ν) := by
  unfold Commute SemiconjBy
  simp [null_mul_null]

theorem null_one_ne_zero : null 1 ≠ 0 := by
  intro h
  have hcast : Fin.castAdd 1 (1 : Fin 4) = (1 : Fin 5) := by decide
  have hι : ι e4Index = 0 := by
    calc ι e4Index
        = null 1 * ι 1 := by rw [null, hcast, mul_assoc, e1_sq, mul_one]
      _ = 0 := by rw [h, zero_mul]
  exact ι_e4_ne_zero hι

theorem null_reverse (μ : Fin 4) : reverse (null μ) = -null μ := by
  dsimp [null]
  exact reverse_ι_mul_ι _ _ (e4_ne_cast μ)

theorem hyperbolic_reverse (a : Fin 3) : reverse (hyperbolic a) = -hyperbolic a := by
  fin_cases a
  · exact reverse_ι_mul_ι 0 1 (by decide)
  · exact reverse_ι_mul_ι 0 2 (by decide)
  · exact reverse_ι_mul_ι 0 3 (by decide)

theorem hyperbolic_smul_mul (x y : ℝ) :
    (x • hyperbolic 0) * (y • hyperbolic 0) = (y • hyperbolic 0) * (x • hyperbolic 0) := by
  simp only [Algebra.smul_def]
  set h : PGA := hyperbolic 0
  have hh : h * h = 1 := hyperbolic_sq 0
  set Ax : PGA := algebraMap ℝ PGA x
  set Ay : PGA := algebraMap ℝ PGA y
  have scalar_mul_comm : Ax * Ay = Ay * Ax := by rw [← map_mul, ← map_mul, mul_comm x y]
  have commute_h_Ay : h * Ay = Ay * h := (Algebra.commutes y h).symm
  calc (Ax * h) * (Ay * h)
      = Ax * (h * (Ay * h)) := mul_assoc Ax h (Ay * h)
    _ = Ax * (Ay * (h * h)) := by
        congr 1
        calc h * (Ay * h) = (h * Ay) * h := (mul_assoc h Ay h).symm
          _ = (Ay * h) * h := by rw [commute_h_Ay]
          _ = Ay * (h * h) := mul_assoc Ay h h
    _ = Ax * Ay := by rw [hh, mul_one]
    _ = Ay * Ax := scalar_mul_comm
    _ = Ay * (Ax * (h * h)) := by rw [← mul_one (Ay * Ax), ← hh, mul_assoc Ay Ax (h * h)]
    _ = Ay * ((Ax * h) * h) := by congr 1; exact (mul_assoc Ax h h).symm
    _ = (Ay * h) * (Ax * h) := by
        have inner : (Ax * h) * h = h * (Ax * h) := by rw [← mul_assoc, (Algebra.commutes x h).symm]
        rw [inner, mul_assoc Ay h (Ax * h)]

theorem cyclic_reverse (a : Fin 3) : reverse (cyclic a) = -cyclic a := by
  fin_cases a
  · exact reverse_ι_mul_ι 3 2 (by decide)
  · exact reverse_ι_mul_ι 1 3 (by decide)
  · exact reverse_ι_mul_ι 2 1 (by decide)

/-! ### Commutators of hyperbolic / cyclic generators

The paper appendix writes `[iΓ_a, Γ_b] = 0` without restricting indices.
Same-axis pairs commute; distinct axes need not.
-/

private theorem mul_hyperbolic0_cyclic0 :
    hyperbolic 0 * cyclic 0 = ι 0 * ι 1 * ι 3 * ι 2 := by
  simp [hyperbolic, cyclic, mul_assoc]

private theorem mul_cyclic0_hyperbolic0 :
    cyclic 0 * hyperbolic 0 = ι 0 * ι 1 * ι 3 * ι 2 := by
  dsimp [hyperbolic, cyclic]
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  calc (ι 3 * ι 2) * (ι 0 * ι 1)
      = ι 3 * (ι 2 * ι 0) * ι 1 := by simp [mul_assoc]
    _ = ι 3 * (-(ι 0 * ι 2)) * ι 1 := by rw [h20]
    _ = -(ι 3 * ι 0) * ι 2 * ι 1 := by simp [mul_neg, mul_assoc]
    _ = -(-(ι 0 * ι 3)) * ι 2 * ι 1 := by rw [h30]
    _ = ι 0 * ι 3 * (ι 2 * ι 1) := by simp [mul_assoc]
    _ = ι 0 * ι 3 * (-(ι 1 * ι 2)) := by rw [h21]
    _ = -(ι 0 * (ι 3 * ι 1) * ι 2) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * (-(ι 1 * ι 3)) * ι 2) := by rw [h31]
    _ = ι 0 * ι 1 * ι 3 * ι 2 := by simp [mul_neg, mul_assoc]

private theorem mul_hyperbolic1_cyclic1 :
    hyperbolic 1 * cyclic 1 = ι 0 * ι 2 * ι 1 * ι 3 := by
  simp [hyperbolic, cyclic, mul_assoc]

private theorem mul_cyclic1_hyperbolic1 :
    cyclic 1 * hyperbolic 1 = ι 0 * ι 2 * ι 1 * ι 3 := by
  dsimp [hyperbolic, cyclic]
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h12 : ι 1 * ι 2 = -(ι 2 * ι 1) := e_mul_anticomm (by decide)
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  calc (ι 1 * ι 3) * (ι 0 * ι 2)
      = ι 1 * (ι 3 * ι 0) * ι 2 := by simp [mul_assoc]
    _ = ι 1 * (-(ι 0 * ι 3)) * ι 2 := by rw [h30]
    _ = -(ι 1 * ι 0) * ι 3 * ι 2 := by simp [mul_neg, mul_assoc]
    _ = -(-(ι 0 * ι 1)) * ι 3 * ι 2 := by rw [h10]
    _ = ι 0 * ι 1 * (ι 3 * ι 2) := by simp [mul_assoc]
    _ = ι 0 * ι 1 * (-(ι 2 * ι 3)) := by rw [h32]
    _ = -(ι 0 * (ι 1 * ι 2) * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * (-(ι 2 * ι 1)) * ι 3) := by rw [h12]
    _ = ι 0 * ι 2 * ι 1 * ι 3 := by simp [mul_neg, mul_assoc]

private theorem mul_hyperbolic2_cyclic2 :
    hyperbolic 2 * cyclic 2 = ι 0 * ι 3 * ι 2 * ι 1 := by
  simp [hyperbolic, cyclic, mul_assoc]

private theorem mul_cyclic2_hyperbolic2 :
    cyclic 2 * hyperbolic 2 = ι 0 * ι 3 * ι 2 * ι 1 := by
  dsimp [hyperbolic, cyclic]
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  have h13 : ι 1 * ι 3 = -(ι 3 * ι 1) := e_mul_anticomm (by decide)
  calc (ι 2 * ι 1) * (ι 0 * ι 3)
      = ι 2 * (ι 1 * ι 0) * ι 3 := by simp [mul_assoc]
    _ = ι 2 * (-(ι 0 * ι 1)) * ι 3 := by rw [h10]
    _ = -(ι 2 * ι 0) * ι 1 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = -(-(ι 0 * ι 2)) * ι 1 * ι 3 := by rw [h20]
    _ = ι 0 * ι 2 * (ι 1 * ι 3) := by simp [mul_assoc]
    _ = ι 0 * ι 2 * (-(ι 3 * ι 1)) := by rw [h13]
    _ = -(ι 0 * (ι 2 * ι 3) * ι 1) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * (-(ι 3 * ι 2)) * ι 1) := by rw [h23]
    _ = ι 0 * ι 3 * ι 2 * ι 1 := by simp [mul_neg, mul_assoc]

/-- Same-axis boost and rotation generators commute (paper: `[iΓ_a, Γ_a] = 0`). -/
theorem commutator_hyperbolic_cyclic_same (a : Fin 3) :
    commutator (hyperbolic a) (cyclic a) = 0 := by
  fin_cases a
  · simp [commutator, mul_hyperbolic0_cyclic0, mul_cyclic0_hyperbolic0]
  · simp [commutator, mul_hyperbolic1_cyclic1, mul_cyclic1_hyperbolic1]
  · simp [commutator, mul_hyperbolic2_cyclic2, mul_cyclic2_hyperbolic2]

private theorem mul_hyperbolic0_cyclic1 :
    hyperbolic 0 * cyclic 1 = ι 0 * ι 3 := by
  dsimp [hyperbolic, cyclic]
  calc (ι 0 * ι 1) * (ι 1 * ι 3)
      = ι 0 * (ι 1 * ι 1) * ι 3 := by simp [mul_assoc]
    _ = ι 0 * ι 3 := by simp [e1_sq]

private theorem mul_cyclic1_hyperbolic0 :
    cyclic 1 * hyperbolic 0 = -(ι 0 * ι 3) := by
  dsimp [hyperbolic, cyclic]
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc (ι 1 * ι 3) * (ι 0 * ι 1)
      = ι 1 * (ι 3 * ι 0) * ι 1 := by simp [mul_assoc]
    _ = ι 1 * (-(ι 0 * ι 3)) * ι 1 := by rw [h30]
    _ = -(ι 1 * ι 0) * ι 3 * ι 1 := by simp [mul_neg, mul_assoc]
    _ = -(-(ι 0 * ι 1)) * ι 3 * ι 1 := by rw [h10]
    _ = ι 0 * ι 1 * (ι 3 * ι 1) := by simp [mul_assoc]
    _ = ι 0 * ι 1 * (-(ι 1 * ι 3)) := by
        rw [e_mul_anticomm (by decide : (3 : Fin 5) ≠ 1)]
    _ = -(ι 0 * (ι 1 * ι 1) * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * ι 3) := by simp [e1_sq]

private theorem ι0_mul_ι3_ne_zero : ι 0 * ι 3 ≠ 0 := by
  intro h
  have hι : ι 0 = 0 := by
    have e3s : ι 3 * ι 3 = (1 : PGA) := by
      simpa [Q311_e5vec, w311] using e_sq (3 : Fin 5)
    calc ι 0
        = (ι 0 * ι 3) * ι 3 := by rw [mul_assoc, e3s, mul_one]
      _ = 0 := by rw [h, zero_mul]
  have : Invertible (2 : ℝ) := ⟨2⁻¹, by norm_num, by norm_num⟩
  have h' : (CliffordAlgebra.equivExterior Q311) (ι 0) = 0 := by
    rw [hι]; exact map_zero _
  rw [show (CliffordAlgebra.equivExterior Q311) = CliffordAlgebra.changeFormEquiv
      CliffordAlgebra.changeForm.associated_neg_proof from rfl,
    CliffordAlgebra.changeFormEquiv_apply] at h'
  unfold PGA.ι at h'
  rw [CliffordAlgebra.changeForm_ι] at h'
  exact absurd (Iff.mp (ExteriorAlgebra.ι_eq_zero_iff (e5vec 0)) h')
    (by simp [e5vec, Pi.single])

/-- Off-axis counterexample: `[e₀e₁, e₁e₃] ≠ 0` (paper's unrestricted commutativity fails). -/
theorem commutator_hyperbolic0_cyclic1_ne_zero :
    commutator (hyperbolic 0) (cyclic 1) ≠ 0 := by
  intro h
  rw [commutator, mul_hyperbolic0_cyclic1, mul_cyclic1_hyperbolic0, sub_neg_eq_add] at h
  have h2 : ι 0 * ι 3 + ι 0 * ι 3 = 0 := h
  have hsmul : (2 : ℝ) • (ι 0 * ι 3) = 0 := by
    simpa [two_smul] using h2
  have : ι 0 * ι 3 = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  exact ι0_mul_ι3_ne_zero this

end Generators

end DstDiophantine
