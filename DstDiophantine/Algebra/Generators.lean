import DstDiophantine.Algebra.PGA
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.Span.Basic

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

theorem commutator_smul_left (c : ℝ) (x y : PGA) :
    commutator (c • x) y = c • commutator x y := by
  simp [commutator, smul_sub]

theorem commutator_smul_right (c : ℝ) (x y : PGA) :
    commutator x (c • y) = c • commutator x y := by
  simp [commutator, smul_sub]

theorem commutator_add_left (x₁ x₂ y : PGA) :
    commutator (x₁ + x₂) y = commutator x₁ y + commutator x₂ y := by
  simp only [commutator, add_mul, mul_add]
  abel

theorem commutator_add_right (x y₁ y₂ : PGA) :
    commutator x (y₁ + y₂) = commutator x y₁ + commutator x y₂ := by
  simp only [commutator, add_mul, mul_add]
  abel

theorem commutator_sum_left {ι : Type*} (s : Finset ι) (x : ι → PGA) (y : PGA) :
    commutator (∑ i ∈ s, x i) y = ∑ i ∈ s, commutator (x i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [commutator]
  · intro a s ha ih
    simp [Finset.sum_insert ha, commutator_add_left, ih]

theorem commutator_sum_right {ι : Type*} (x : PGA) (s : Finset ι) (y : ι → PGA) :
    commutator x (∑ i ∈ s, y i) = ∑ i ∈ s, commutator x (y i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [commutator]
  · intro a s ha ih
    simp [Finset.sum_insert ha, commutator_add_right, ih]

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

/-! ### Poincaré action: `[B^±, N_μ]` lands in the null span -/

private theorem e2_sq : ι 2 * ι 2 = (1 : PGA) := by
  simp [e_sq, Q311_e5vec, w311]

private theorem e3_sq : ι 3 * ι 3 = (1 : PGA) := by
  simp [e_sq, Q311_e5vec, w311]

private theorem mul_hyperbolic0_null0 :
    hyperbolic 0 * null 0 = null 1 := by
  dsimp [hyperbolic, null]
  have h14 : ι 1 * ι e4Index = -(ι e4Index * ι 1) := e4_inner_anticomm 1
  have h04 : ι 0 * ι e4Index = -(ι e4Index * ι 0) := e4_inner_anticomm 0
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc (ι 0 * ι 1) * (ι e4Index * ι 0)
      = ι 0 * (ι 1 * ι e4Index) * ι 0 := by simp [mul_assoc]
    _ = ι 0 * (-(ι e4Index * ι 1)) * ι 0 := by rw [h14]
    _ = -(ι 0 * ι e4Index * ι 1 * ι 0) := by simp [mul_neg, mul_assoc]
    _ = -(-(ι e4Index * ι 0) * ι 1 * ι 0) := by rw [h04]
    _ = ι e4Index * ι 0 * ι 1 * ι 0 := by simp [mul_assoc]
    _ = ι e4Index * (ι 0 * (ι 1 * ι 0)) := by simp [mul_assoc]
    _ = ι e4Index * (ι 0 * (-(ι 0 * ι 1))) := by rw [h10]
    _ = -(ι e4Index * (ι 0 * ι 0) * ι 1) := by simp [mul_neg, mul_assoc]
    _ = ι e4Index * ι 1 := by simp [e0_sq]
    _ = null 1 := by simp [null]

private theorem mul_null0_hyperbolic0 :
    null 0 * hyperbolic 0 = -null 1 := by
  dsimp [hyperbolic, null]
  calc (ι e4Index * ι 0) * (ι 0 * ι 1)
      = ι e4Index * (ι 0 * ι 0) * ι 1 := by simp [mul_assoc]
    _ = -(ι e4Index * ι 1) := by simp [e0_sq]
    _ = -null 1 := by simp [null]

private theorem mul_hyperbolic0_null1 :
    hyperbolic 0 * null 1 = null 0 := by
  dsimp [hyperbolic, null]
  have h14 : ι 1 * ι e4Index = -(ι e4Index * ι 1) := e4_inner_anticomm 1
  calc (ι 0 * ι 1) * (ι e4Index * ι 1)
      = ι 0 * (ι 1 * ι e4Index) * ι 1 := by simp [mul_assoc]
    _ = ι 0 * (-(ι e4Index * ι 1)) * ι 1 := by rw [h14]
    _ = -(ι 0 * ι e4Index * (ι 1 * ι 1)) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * ι e4Index) := by simp [e1_sq]
    _ = ι e4Index * ι 0 := (e4_mul_anticomm 0).symm
    _ = null 0 := by simp [null]

private theorem mul_null1_hyperbolic0 :
    null 1 * hyperbolic 0 = -null 0 := by
  dsimp [hyperbolic, null]
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc (ι e4Index * ι 1) * (ι 0 * ι 1)
      = ι e4Index * (ι 1 * ι 0) * ι 1 := by simp [mul_assoc]
    _ = ι e4Index * (-(ι 0 * ι 1)) * ι 1 := by rw [h10]
    _ = -(ι e4Index * ι 0 * (ι 1 * ι 1)) := by simp [mul_neg, mul_assoc]
    _ = -null 0 := by simp [null, e1_sq]

private theorem commute_simple_bivector_ι {i j μ : Fin 5}
    (_hij : i ≠ j) (hi : μ ≠ i) (hj : μ ≠ j) :
    Commute (ι i * ι j) (ι μ) := by
  unfold Commute SemiconjBy
  have hμi : ι μ * ι i = -(ι i * ι μ) := e_mul_anticomm hi
  have hjμ : ι j * ι μ = -(ι μ * ι j) := e_mul_anticomm hj.symm
  calc (ι i * ι j) * ι μ
      = ι i * (ι j * ι μ) := by rw [mul_assoc]
    _ = ι i * (-(ι μ * ι j)) := by rw [hjμ]
    _ = -(ι i * ι μ) * ι j := by simp [mul_neg, mul_assoc]
    _ = (ι μ * ι i) * ι j := by rw [← hμi]
    _ = ι μ * (ι i * ι j) := by simp [mul_assoc]

private theorem commute_hyperbolic0_ι {μ : Fin 5} (h0 : μ ≠ 0) (h1 : μ ≠ 1) :
    Commute (hyperbolic 0) (ι μ) := by
  simpa [hyperbolic] using
    commute_simple_bivector_ι (by decide : (0 : Fin 5) ≠ 1) h0 h1

private theorem commute_hyperbolic0_null_off {μ : Fin 4}
    (h0 : Fin.castAdd 1 μ ≠ 0) (h1 : Fin.castAdd 1 μ ≠ 1) :
    Commute (hyperbolic 0) (null μ) := by
  dsimp [null]
  exact (commute_hyperbolic0_ι (by decide : (e4Index : Fin 5) ≠ 0)
      (by decide : (e4Index : Fin 5) ≠ 1)).mul_right
    (commute_hyperbolic0_ι h0 h1)

private theorem mul_hyperbolic0_null2 :
    hyperbolic 0 * null 2 = null 2 * hyperbolic 0 :=
  commute_hyperbolic0_null_off (by decide) (by decide)

private theorem mul_hyperbolic0_null3 :
    hyperbolic 0 * null 3 = null 3 * hyperbolic 0 :=
  commute_hyperbolic0_null_off (by decide) (by decide)

/-- Radial boost mixes time and \(x\) translations: \([B^{+}_{0},N_{0}]=2N_{1}\). -/
theorem commutator_hyperbolic0_null0 :
    commutator (hyperbolic 0) (null 0) = (2 : ℝ) • null 1 := by
  simp only [commutator, mul_hyperbolic0_null0, mul_null0_hyperbolic0, sub_neg_eq_add, two_smul]

/-- \([B^{+}_{0},N_{1}]=2N_{0}\). -/
theorem commutator_hyperbolic0_null1 :
    commutator (hyperbolic 0) (null 1) = (2 : ℝ) • null 0 := by
  simp only [commutator, mul_hyperbolic0_null1, mul_null1_hyperbolic0, sub_neg_eq_add, two_smul]

/-- Off-plane translations are invariant: \([B^{+}_{0},N_{2}]=0\). -/
theorem commutator_hyperbolic0_null2 :
    commutator (hyperbolic 0) (null 2) = 0 := by
  simp [commutator, mul_hyperbolic0_null2, sub_self]

theorem commutator_hyperbolic0_null3 :
    commutator (hyperbolic 0) (null 3) = 0 := by
  simp [commutator, mul_hyperbolic0_null3, sub_self]

/-- Closed commutator table of the radial boost with the four null generators. -/
theorem commutator_hyperbolic0_null (μ : Fin 4) :
    commutator (hyperbolic 0) (null μ) =
      match μ with
      | 0 => (2 : ℝ) • null 1
      | 1 => (2 : ℝ) • null 0
      | 2 => 0
      | 3 => 0 := by
  match μ with
  | 0 => exact commutator_hyperbolic0_null0
  | 1 => exact commutator_hyperbolic0_null1
  | 2 => exact commutator_hyperbolic0_null2
  | 3 => exact commutator_hyperbolic0_null3

/-- Null translations form an \(\mathrm{ad}\)-invariant subspace under the radial boost. -/
theorem commutator_hyperbolic0_null_mem_span (μ : Fin 4) :
    commutator (hyperbolic 0) (null μ) ∈
      Submodule.span ℝ (Set.range (null : Fin 4 → PGA)) := by
  match μ with
  | 0 =>
    rw [commutator_hyperbolic0_null0]
    exact (Submodule.span ℝ _).smul_mem _ (Submodule.subset_span ⟨1, rfl⟩)
  | 1 =>
    rw [commutator_hyperbolic0_null1]
    exact (Submodule.span ℝ _).smul_mem _ (Submodule.subset_span ⟨0, rfl⟩)
  | 2 =>
    rw [commutator_hyperbolic0_null2]
    exact Submodule.zero_mem _
  | 3 =>
    rw [commutator_hyperbolic0_null3]
    exact Submodule.zero_mem _

/-! Cyclic/null: rotation in the \(yz\)-plane mixes \(N_{2},N_{3}\). -/

private theorem mul_cyclic0_null2 :
    cyclic 0 * null 2 = null 3 := by
  dsimp [cyclic, null]
  have h24 : ι 2 * ι e4Index = -(ι e4Index * ι 2) := e4_inner_anticomm 2
  calc (ι 3 * ι 2) * (ι e4Index * ι 2)
      = ι 3 * (ι 2 * ι e4Index) * ι 2 := by simp [mul_assoc]
    _ = ι 3 * (-(ι e4Index * ι 2)) * ι 2 := by rw [h24]
    _ = -(ι 3 * ι e4Index * (ι 2 * ι 2)) := by simp [mul_neg, mul_assoc]
    _ = -(ι 3 * ι e4Index) := by simp [e2_sq]
    _ = ι e4Index * ι 3 := (e4_mul_anticomm 3).symm
    _ = null 3 := by simp [null]

private theorem mul_null2_cyclic0 :
    null 2 * cyclic 0 = -null 3 := by
  dsimp [cyclic, null]
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  calc (ι e4Index * ι 2) * (ι 3 * ι 2)
      = ι e4Index * (ι 2 * ι 3) * ι 2 := by simp [mul_assoc]
    _ = ι e4Index * (-(ι 3 * ι 2)) * ι 2 := by rw [h23]
    _ = -(ι e4Index * ι 3 * (ι 2 * ι 2)) := by simp [mul_neg, mul_assoc]
    _ = -null 3 := by simp [null, e2_sq]

private theorem mul_cyclic0_null3 :
    cyclic 0 * null 3 = -null 2 := by
  dsimp [cyclic, null]
  have h24 : ι 2 * ι e4Index = -(ι e4Index * ι 2) := e4_inner_anticomm 2
  have h34 : ι 3 * ι e4Index = -(ι e4Index * ι 3) := e4_inner_anticomm 3
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  calc (ι 3 * ι 2) * (ι e4Index * ι 3)
      = ι 3 * (ι 2 * ι e4Index) * ι 3 := by simp [mul_assoc]
    _ = ι 3 * (-(ι e4Index * ι 2)) * ι 3 := by rw [h24]
    _ = -(ι 3 * ι e4Index) * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = -(-(ι e4Index * ι 3)) * ι 2 * ι 3 := by rw [h34]
    _ = ι e4Index * (ι 3 * (ι 2 * ι 3)) := by simp [mul_assoc]
    _ = ι e4Index * (ι 3 * (-(ι 3 * ι 2))) := by rw [h23]
    _ = -(ι e4Index * (ι 3 * ι 3) * ι 2) := by simp [mul_neg, mul_assoc]
    _ = -null 2 := by simp [null, e3_sq]

private theorem mul_null3_cyclic0 :
    null 3 * cyclic 0 = null 2 := by
  dsimp [cyclic, null]
  calc (ι e4Index * ι 3) * (ι 3 * ι 2)
      = ι e4Index * (ι 3 * ι 3) * ι 2 := by simp [mul_assoc]
    _ = null 2 := by simp [null, e3_sq]

theorem commutator_cyclic0_null2 :
    commutator (cyclic 0) (null 2) = (2 : ℝ) • null 3 := by
  simp only [commutator, mul_cyclic0_null2, mul_null2_cyclic0, sub_neg_eq_add, two_smul]

theorem commutator_cyclic0_null3 :
    commutator (cyclic 0) (null 3) = (-2 : ℝ) • null 2 := by
  simp only [commutator, mul_cyclic0_null3, mul_null3_cyclic0]
  module

private theorem commute_cyclic0_ι {μ : Fin 5} (h2 : μ ≠ 2) (h3 : μ ≠ 3) :
    Commute (cyclic 0) (ι μ) := by
  simpa [cyclic] using
    commute_simple_bivector_ι (by decide : (3 : Fin 5) ≠ 2) h3 h2

private theorem commute_cyclic0_null_off {μ : Fin 4}
    (h2 : Fin.castAdd 1 μ ≠ 2) (h3 : Fin.castAdd 1 μ ≠ 3) :
    Commute (cyclic 0) (null μ) := by
  dsimp [null]
  exact (commute_cyclic0_ι (by decide : (e4Index : Fin 5) ≠ 2)
      (by decide : (e4Index : Fin 5) ≠ 3)).mul_right
    (commute_cyclic0_ι h2 h3)

private theorem mul_cyclic0_null0 :
    cyclic 0 * null 0 = null 0 * cyclic 0 :=
  commute_cyclic0_null_off (by decide) (by decide)

private theorem mul_cyclic0_null1 :
    cyclic 0 * null 1 = null 1 * cyclic 0 :=
  commute_cyclic0_null_off (by decide) (by decide)

theorem commutator_cyclic0_null0 :
    commutator (cyclic 0) (null 0) = 0 := by
  simp [commutator, mul_cyclic0_null0, sub_self]

theorem commutator_cyclic0_null1 :
    commutator (cyclic 0) (null 1) = 0 := by
  simp [commutator, mul_cyclic0_null1, sub_self]

theorem commutator_cyclic0_null (μ : Fin 4) :
    commutator (cyclic 0) (null μ) =
      match μ with
      | 0 => 0
      | 1 => 0
      | 2 => (2 : ℝ) • null 3
      | 3 => (-2 : ℝ) • null 2 := by
  match μ with
  | 0 => exact commutator_cyclic0_null0
  | 1 => exact commutator_cyclic0_null1
  | 2 => exact commutator_cyclic0_null2
  | 3 => exact commutator_cyclic0_null3

theorem commutator_cyclic0_null_mem_span (μ : Fin 4) :
    commutator (cyclic 0) (null μ) ∈
      Submodule.span ℝ (Set.range (null : Fin 4 → PGA)) := by
  match μ with
  | 0 =>
    rw [commutator_cyclic0_null0]; exact Submodule.zero_mem _
  | 1 =>
    rw [commutator_cyclic0_null1]; exact Submodule.zero_mem _
  | 2 =>
    rw [commutator_cyclic0_null2]
    exact (Submodule.span ℝ _).smul_mem _ (Submodule.subset_span ⟨3, rfl⟩)
  | 3 =>
    rw [commutator_cyclic0_null3]
    exact (Submodule.span ℝ _).smul_mem _ (Submodule.subset_span ⟨2, rfl⟩)

/-! ### Remaining Lorentz–null brackets, as the vector action of `so(3,1)` -/

/-- Null bivector span, the translation ideal. -/
noncomputable def nullSpan : Submodule ℝ PGA :=
  Submodule.span ℝ (Set.range (null : Fin 4 → PGA))

theorem mem_nullSpan (μ : Fin 4) : null μ ∈ nullSpan :=
  Submodule.subset_span ⟨μ, rfl⟩

theorem smul_mem_nullSpan (c : ℝ) {x : PGA} (hx : x ∈ nullSpan) : c • x ∈ nullSpan :=
  nullSpan.smul_mem c hx

private theorem hyperbolic_eq (a : Fin 3) :
    hyperbolic a = ι 0 * ι (Fin.castAdd 1 a.succ) := by
  fin_cases a <;> rfl

private theorem spatial_sq (k : Fin 4) (hk : k ≠ 0) :
    ι (Fin.castAdd 1 k) * ι (Fin.castAdd 1 k) = (1 : PGA) := by
  fin_cases k
  · cases hk rfl
  · simp [e_sq, Q311_e5vec, w311]
  · simp [e_sq, Q311_e5vec, w311]
  · simp [e_sq, Q311_e5vec, w311]

private theorem castAdd_ne_e4 (k : Fin 4) : Fin.castAdd 1 k ≠ e4Index := by
  fin_cases k <;> decide

private theorem castAdd_inj {μ ν : Fin 4}
    (h : Fin.castAdd 1 μ = Fin.castAdd 1 ν) : μ = ν :=
  Fin.castAdd_injective 4 1 h

private theorem castAdd_ne_zero {k : Fin 4} (hk : k ≠ 0) : Fin.castAdd 1 k ≠ (0 : Fin 5) := by
  fin_cases k <;> first | cases hk rfl | decide

private theorem zero_ne_castAdd_succ (a : Fin 3) :
    (0 : Fin 5) ≠ Fin.castAdd 1 a.succ :=
  (castAdd_ne_zero (Fin.succ_ne_zero a)).symm

/-- Boost against a time translation: \((e_0 e_k) N_0 = N_k\). -/
private theorem mul_hyperbolic_null_time (a : Fin 3) :
    hyperbolic a * null 0 = null a.succ := by
  rw [hyperbolic_eq]
  dsimp [null]
  have hk_e4 : ι (Fin.castAdd 1 a.succ) * ι e4Index =
      -(ι e4Index * ι (Fin.castAdd 1 a.succ)) := e4_inner_anticomm a.succ
  have h0e4 : ι 0 * ι e4Index = -(ι e4Index * ι 0) := e4_inner_anticomm 0
  have hk0 : ι (Fin.castAdd 1 a.succ) * ι 0 =
      -(ι 0 * ι (Fin.castAdd 1 a.succ)) :=
    e_mul_anticomm (castAdd_ne_zero (Fin.succ_ne_zero a))
  calc (ι 0 * ι (Fin.castAdd 1 a.succ)) * (ι e4Index * ι 0)
      = ι 0 * (ι (Fin.castAdd 1 a.succ) * ι e4Index) * ι 0 := by simp [mul_assoc]
    _ = ι 0 * (-(ι e4Index * ι (Fin.castAdd 1 a.succ))) * ι 0 := by rw [hk_e4]
    _ = -(ι 0 * ι e4Index * ι (Fin.castAdd 1 a.succ) * ι 0) := by simp [mul_neg, mul_assoc]
    _ = -(-(ι e4Index * ι 0) * ι (Fin.castAdd 1 a.succ) * ι 0) := by rw [h0e4]
    _ = ι e4Index * (ι 0 * (ι (Fin.castAdd 1 a.succ) * ι 0)) := by simp [mul_assoc]
    _ = ι e4Index * (ι 0 * (-(ι 0 * ι (Fin.castAdd 1 a.succ)))) := by rw [hk0]
    _ = -(ι e4Index * (ι 0 * ι 0) * ι (Fin.castAdd 1 a.succ)) := by simp [mul_neg, mul_assoc]
    _ = ι e4Index * ι (Fin.castAdd 1 a.succ) := by simp [e0_sq]

private theorem mul_null_time_hyperbolic (a : Fin 3) :
    null 0 * hyperbolic a = -null a.succ := by
  rw [hyperbolic_eq]
  dsimp [null]
  calc (ι e4Index * ι 0) * (ι 0 * ι (Fin.castAdd 1 a.succ))
      = ι e4Index * (ι 0 * ι 0) * ι (Fin.castAdd 1 a.succ) := by simp [mul_assoc]
    _ = -(ι e4Index * ι (Fin.castAdd 1 a.succ)) := by simp [e0_sq]

/-- Boost against its spatial translation: \((e_0 e_k) N_k = N_0\). -/
private theorem mul_hyperbolic_null_space (a : Fin 3) :
    hyperbolic a * null a.succ = null 0 := by
  rw [hyperbolic_eq]
  dsimp [null]
  have hk_e4 : ι (Fin.castAdd 1 a.succ) * ι e4Index =
      -(ι e4Index * ι (Fin.castAdd 1 a.succ)) := e4_inner_anticomm a.succ
  have hsq := spatial_sq a.succ (Fin.succ_ne_zero a)
  calc (ι 0 * ι (Fin.castAdd 1 a.succ)) * (ι e4Index * ι (Fin.castAdd 1 a.succ))
      = ι 0 * (ι (Fin.castAdd 1 a.succ) * ι e4Index) * ι (Fin.castAdd 1 a.succ) := by
        simp [mul_assoc]
    _ = ι 0 * (-(ι e4Index * ι (Fin.castAdd 1 a.succ))) *
          ι (Fin.castAdd 1 a.succ) := by rw [hk_e4]
    _ = -(ι 0 * ι e4Index * (ι (Fin.castAdd 1 a.succ) * ι (Fin.castAdd 1 a.succ))) := by
        simp [mul_neg, mul_assoc]
    _ = -(ι 0 * ι e4Index) := by rw [hsq, mul_one]
    _ = ι e4Index * ι 0 := (e4_mul_anticomm 0).symm

private theorem mul_null_space_hyperbolic (a : Fin 3) :
    null a.succ * hyperbolic a = -null 0 := by
  rw [hyperbolic_eq]
  dsimp [null]
  have hk0 : ι (Fin.castAdd 1 a.succ) * ι 0 =
      -(ι 0 * ι (Fin.castAdd 1 a.succ)) :=
    e_mul_anticomm (castAdd_ne_zero (Fin.succ_ne_zero a))
  have hsq := spatial_sq a.succ (Fin.succ_ne_zero a)
  calc (ι e4Index * ι (Fin.castAdd 1 a.succ)) * (ι 0 * ι (Fin.castAdd 1 a.succ))
      = ι e4Index * (ι (Fin.castAdd 1 a.succ) * ι 0) * ι (Fin.castAdd 1 a.succ) := by
        simp [mul_assoc]
    _ = ι e4Index * (-(ι 0 * ι (Fin.castAdd 1 a.succ))) *
          ι (Fin.castAdd 1 a.succ) := by rw [hk0]
    _ = -(ι e4Index * ι 0 * (ι (Fin.castAdd 1 a.succ) * ι (Fin.castAdd 1 a.succ))) := by
        simp [mul_neg, mul_assoc]
    _ = -null 0 := by simp [null, hsq]

private theorem commute_hyperbolic_null_off (a : Fin 3) {μ : Fin 4}
    (h0 : μ ≠ 0) (hsp : μ ≠ a.succ) :
    Commute (hyperbolic a) (null μ) := by
  rw [hyperbolic_eq]
  dsimp [null]
  have hi0 : (e4Index : Fin 5) ≠ 0 := by decide
  have hik : e4Index ≠ Fin.castAdd 1 a.succ := (castAdd_ne_e4 a.succ).symm
  have hμ0 : Fin.castAdd 1 μ ≠ (0 : Fin 5) := by
    intro h
    exact h0 (castAdd_inj (h.trans (by simp)))
  have hμk : Fin.castAdd 1 μ ≠ Fin.castAdd 1 a.succ := by
    intro h
    exact hsp (castAdd_inj h)
  exact (commute_simple_bivector_ι (zero_ne_castAdd_succ a) hi0 hik).mul_right
    (commute_simple_bivector_ι (zero_ne_castAdd_succ a) hμ0 hμk)

/-- Closed commutator table of a boost with the four null generators. -/
theorem commutator_hyperbolic_null (a : Fin 3) (μ : Fin 4) :
    commutator (hyperbolic a) (null μ) =
      if μ = 0 then (2 : ℝ) • null a.succ
      else if μ = a.succ then (2 : ℝ) • null 0
      else 0 := by
  by_cases h0 : μ = 0
  · subst h0
    simp [commutator, mul_hyperbolic_null_time, mul_null_time_hyperbolic, sub_neg_eq_add, two_smul]
  · by_cases hsp : μ = a.succ
    · subst hsp
      simp [commutator, mul_hyperbolic_null_space, mul_null_space_hyperbolic, h0,
        sub_neg_eq_add, two_smul]
    · rw [commutator, (commute_hyperbolic_null_off a h0 hsp).eq, sub_self]
      simp [h0, hsp]

theorem commutator_hyperbolic_null_mem_span (a : Fin 3) (μ : Fin 4) :
    commutator (hyperbolic a) (null μ) ∈ nullSpan := by
  rw [commutator_hyperbolic_null]
  split_ifs with h0 hsp
  · exact smul_mem_nullSpan _ (mem_nullSpan _)
  · exact smul_mem_nullSpan _ (mem_nullSpan _)
  · exact nullSpan.zero_mem

/-- Plane of the cyclic generator `B⁻_a`: left and right spatial legs. -/
def cyclicLeft : Fin 3 → Fin 4
  | 0 => 3
  | 1 => 1
  | 2 => 2

def cyclicRight : Fin 3 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 1

private theorem cyclic_eq_legs (a : Fin 3) :
    cyclic a = ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicRight a)) := by
  fin_cases a <;> rfl

private theorem cyclicLeft_ne_right (a : Fin 3) : cyclicLeft a ≠ cyclicRight a := by
  fin_cases a <;> decide

private theorem cyclicLeft_ne_zero (a : Fin 3) : cyclicLeft a ≠ 0 := by
  fin_cases a <;> decide

private theorem cyclicRight_ne_zero (a : Fin 3) : cyclicRight a ≠ 0 := by
  fin_cases a <;> decide

private theorem mul_cyclic_null_right (a : Fin 3) :
    cyclic a * null (cyclicRight a) = null (cyclicLeft a) := by
  rw [cyclic_eq_legs]
  dsimp [null]
  have hj_e4 : ι (Fin.castAdd 1 (cyclicRight a)) * ι e4Index =
      -(ι e4Index * ι (Fin.castAdd 1 (cyclicRight a))) :=
    e4_inner_anticomm (cyclicRight a)
  have hsq := spatial_sq (cyclicRight a) (cyclicRight_ne_zero a)
  calc (ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicRight a))) *
          (ι e4Index * ι (Fin.castAdd 1 (cyclicRight a)))
      = ι (Fin.castAdd 1 (cyclicLeft a)) *
          (ι (Fin.castAdd 1 (cyclicRight a)) * ι e4Index) *
          ι (Fin.castAdd 1 (cyclicRight a)) := by simp [mul_assoc]
    _ = ι (Fin.castAdd 1 (cyclicLeft a)) *
          (-(ι e4Index * ι (Fin.castAdd 1 (cyclicRight a)))) *
          ι (Fin.castAdd 1 (cyclicRight a)) := by rw [hj_e4]
    _ = -(ι (Fin.castAdd 1 (cyclicLeft a)) * ι e4Index *
          (ι (Fin.castAdd 1 (cyclicRight a)) * ι (Fin.castAdd 1 (cyclicRight a)))) := by
        simp [mul_neg, mul_assoc]
    _ = -(ι (Fin.castAdd 1 (cyclicLeft a)) * ι e4Index) := by rw [hsq, mul_one]
    _ = ι e4Index * ι (Fin.castAdd 1 (cyclicLeft a)) :=
      (e4_mul_anticomm (cyclicLeft a)).symm

private theorem mul_null_right_cyclic (a : Fin 3) :
    null (cyclicRight a) * cyclic a = -null (cyclicLeft a) := by
  rw [cyclic_eq_legs]
  dsimp [null]
  have hji : ι (Fin.castAdd 1 (cyclicRight a)) * ι (Fin.castAdd 1 (cyclicLeft a)) =
      -(ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicRight a))) :=
    e_mul_anticomm (by
      intro h
      exact cyclicLeft_ne_right a (castAdd_inj h.symm))
  have hsq := spatial_sq (cyclicRight a) (cyclicRight_ne_zero a)
  calc (ι e4Index * ι (Fin.castAdd 1 (cyclicRight a))) *
          (ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicRight a)))
      = ι e4Index * (ι (Fin.castAdd 1 (cyclicRight a)) *
          ι (Fin.castAdd 1 (cyclicLeft a))) *
          ι (Fin.castAdd 1 (cyclicRight a)) := by simp [mul_assoc]
    _ = ι e4Index * (-(ι (Fin.castAdd 1 (cyclicLeft a)) *
          ι (Fin.castAdd 1 (cyclicRight a)))) *
          ι (Fin.castAdd 1 (cyclicRight a)) := by rw [hji]
    _ = -(ι e4Index * ι (Fin.castAdd 1 (cyclicLeft a)) *
          (ι (Fin.castAdd 1 (cyclicRight a)) * ι (Fin.castAdd 1 (cyclicRight a)))) := by
        simp [mul_neg, mul_assoc]
    _ = -null (cyclicLeft a) := by simp [null, hsq]

private theorem mul_cyclic_null_left (a : Fin 3) :
    cyclic a * null (cyclicLeft a) = -null (cyclicRight a) := by
  rw [cyclic_eq_legs]
  dsimp [null]
  have hj_e4 : ι (Fin.castAdd 1 (cyclicRight a)) * ι e4Index =
      -(ι e4Index * ι (Fin.castAdd 1 (cyclicRight a))) :=
    e4_inner_anticomm (cyclicRight a)
  have hi_e4 : ι (Fin.castAdd 1 (cyclicLeft a)) * ι e4Index =
      -(ι e4Index * ι (Fin.castAdd 1 (cyclicLeft a))) :=
    e4_inner_anticomm (cyclicLeft a)
  have hji : ι (Fin.castAdd 1 (cyclicRight a)) * ι (Fin.castAdd 1 (cyclicLeft a)) =
      -(ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicRight a))) :=
    e_mul_anticomm (by
      intro h
      exact cyclicLeft_ne_right a (castAdd_inj h.symm))
  have hsq := spatial_sq (cyclicLeft a) (cyclicLeft_ne_zero a)
  calc (ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicRight a))) *
          (ι e4Index * ι (Fin.castAdd 1 (cyclicLeft a)))
      = ι (Fin.castAdd 1 (cyclicLeft a)) *
          (ι (Fin.castAdd 1 (cyclicRight a)) * ι e4Index) *
          ι (Fin.castAdd 1 (cyclicLeft a)) := by simp [mul_assoc]
    _ = ι (Fin.castAdd 1 (cyclicLeft a)) *
          (-(ι e4Index * ι (Fin.castAdd 1 (cyclicRight a)))) *
          ι (Fin.castAdd 1 (cyclicLeft a)) := by rw [hj_e4]
    _ = -(ι (Fin.castAdd 1 (cyclicLeft a)) * ι e4Index) *
          ι (Fin.castAdd 1 (cyclicRight a)) *
          ι (Fin.castAdd 1 (cyclicLeft a)) := by simp [mul_neg, mul_assoc]
    _ = -(-(ι e4Index * ι (Fin.castAdd 1 (cyclicLeft a)))) *
          ι (Fin.castAdd 1 (cyclicRight a)) *
          ι (Fin.castAdd 1 (cyclicLeft a)) := by rw [hi_e4]
    _ = ι e4Index * (ι (Fin.castAdd 1 (cyclicLeft a)) *
          (ι (Fin.castAdd 1 (cyclicRight a)) * ι (Fin.castAdd 1 (cyclicLeft a)))) := by
        simp [mul_assoc]
    _ = ι e4Index * (ι (Fin.castAdd 1 (cyclicLeft a)) *
          (-(ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicRight a))))) := by
        rw [hji]
    _ = -(ι e4Index * (ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicLeft a))) *
          ι (Fin.castAdd 1 (cyclicRight a))) := by simp [mul_neg, mul_assoc]
    _ = -null (cyclicRight a) := by simp [null, hsq]

private theorem mul_null_left_cyclic (a : Fin 3) :
    null (cyclicLeft a) * cyclic a = null (cyclicRight a) := by
  rw [cyclic_eq_legs]
  dsimp [null]
  have hsq := spatial_sq (cyclicLeft a) (cyclicLeft_ne_zero a)
  calc (ι e4Index * ι (Fin.castAdd 1 (cyclicLeft a))) *
          (ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicRight a)))
      = ι e4Index * (ι (Fin.castAdd 1 (cyclicLeft a)) * ι (Fin.castAdd 1 (cyclicLeft a))) *
          ι (Fin.castAdd 1 (cyclicRight a)) := by simp [mul_assoc]
    _ = null (cyclicRight a) := by simp [null, hsq]

private theorem commute_cyclic_null_off (a : Fin 3) {μ : Fin 4}
    (hL : μ ≠ cyclicLeft a) (hR : μ ≠ cyclicRight a) :
    Commute (cyclic a) (null μ) := by
  rw [cyclic_eq_legs]
  dsimp [null]
  have hij : Fin.castAdd 1 (cyclicLeft a) ≠ Fin.castAdd 1 (cyclicRight a) := by
    intro h
    exact cyclicLeft_ne_right a (castAdd_inj h)
  have hi4 : Fin.castAdd 1 (cyclicLeft a) ≠ e4Index := castAdd_ne_e4 (cyclicLeft a)
  have hj4 : Fin.castAdd 1 (cyclicRight a) ≠ e4Index := castAdd_ne_e4 (cyclicRight a)
  have hμL : Fin.castAdd 1 μ ≠ Fin.castAdd 1 (cyclicLeft a) := by
    intro h; exact hL (castAdd_inj h)
  have hμR : Fin.castAdd 1 μ ≠ Fin.castAdd 1 (cyclicRight a) := by
    intro h; exact hR (castAdd_inj h)
  exact (commute_simple_bivector_ι hij hi4.symm hj4.symm).mul_right
    (commute_simple_bivector_ι hij hμL hμR)

/-- Closed commutator table of a cyclic generator with the four null generators. -/
theorem commutator_cyclic_null (a : Fin 3) (μ : Fin 4) :
    commutator (cyclic a) (null μ) =
      if μ = cyclicRight a then (2 : ℝ) • null (cyclicLeft a)
      else if μ = cyclicLeft a then (-2 : ℝ) • null (cyclicRight a)
      else 0 := by
  by_cases hR : μ = cyclicRight a
  · subst hR
    simp [commutator, mul_cyclic_null_right, mul_null_right_cyclic, sub_neg_eq_add, two_smul]
  · by_cases hL : μ = cyclicLeft a
    · subst hL
      simp [commutator, mul_cyclic_null_left, mul_null_left_cyclic, hR]
      module
    · rw [commutator, (commute_cyclic_null_off a hL hR).eq, sub_self]
      simp [hR, hL]

theorem commutator_cyclic_null_mem_span (a : Fin 3) (μ : Fin 4) :
    commutator (cyclic a) (null μ) ∈ nullSpan := by
  rw [commutator_cyclic_null]
  split_ifs
  · exact smul_mem_nullSpan _ (mem_nullSpan _)
  · exact smul_mem_nullSpan _ (mem_nullSpan _)
  · exact nullSpan.zero_mem

/-- Any two elements of the null span multiply to zero. -/
theorem nullSpan_mul {x y : PGA} (hx : x ∈ nullSpan) (hy : y ∈ nullSpan) : x * y = 0 := by
  refine Submodule.span_induction₂
    (s := Set.range (null : Fin 4 → PGA)) (t := Set.range (null : Fin 4 → PGA))
    (p := fun u v _ _ => u * v = 0) ?mem ?zl ?zr ?al ?ar ?sl ?sr hx hy
  · intro u v hu hv
    obtain ⟨μ, rfl⟩ := hu
    obtain ⟨ν, rfl⟩ := hv
    exact null_mul_null μ ν
  · intro; simp
  · intro; simp
  · intro _ _ _ _ _ _ hxz hyz
    simp [add_mul, hxz, hyz]
  · intro _ _ _ _ _ _ hxy hxz
    simp [mul_add, hxy, hxz]
  · intro r _ _ _ _ h
    rw [smul_mul_assoc, h, smul_zero]
  · intro r _ _ _ _ h
    rw [mul_smul_comm, h, smul_zero]

/-- Two null generators sandwich any element to zero. -/
theorem null_mul_mul_null (μ ν : Fin 4) (z : PGA) :
    null μ * z * null ν = 0 := by
  dsimp [null]
  calc ι e4Index * ι (Fin.castAdd 1 μ) * z * (ι e4Index * ι (Fin.castAdd 1 ν))
      = (ι e4Index * (ι (Fin.castAdd 1 μ) * z) * ι e4Index) *
          ι (Fin.castAdd 1 ν) := by simp [mul_assoc]
    _ = 0 := by rw [e4_mul_mul_e4, zero_mul]

/-- Null-span elements sandwich any element to zero. -/
theorem nullSpan_mul_mul {x y : PGA} (hx : x ∈ nullSpan) (hy : y ∈ nullSpan) (z : PGA) :
    x * z * y = 0 := by
  refine Submodule.span_induction₂
    (s := Set.range (null : Fin 4 → PGA)) (t := Set.range (null : Fin 4 → PGA))
    (p := fun u v _ _ => u * z * v = 0) ?mem ?zl ?zr ?al ?ar ?sl ?sr hx hy
  · intro u v hu hv
    obtain ⟨μ, rfl⟩ := hu
    obtain ⟨ν, rfl⟩ := hv
    exact null_mul_mul_null μ ν z
  · intro; simp
  · intro; simp
  · intro _ _ _ _ _ _ hxz hyz
    simp [add_mul, hxz, hyz]
  · intro _ _ _ _ _ _ hxy hxz
    simp [mul_add, hxy, hxz]
  · intro r _ _ _ _ h
    rw [smul_mul_assoc, smul_mul_assoc, h, smul_zero]
  · intro r _ _ _ _ h
    rw [mul_smul_comm, h, smul_zero]

end Generators

end DstDiophantine
