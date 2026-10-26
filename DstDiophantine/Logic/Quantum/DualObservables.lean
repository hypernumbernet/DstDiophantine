import DstDiophantine.Logic.Quantum.DualEntanglement

/-!
# Spin observables of a dual spinor

* The spin vector `r(u)_k = ⟨u, σ_k u⟩` is real, `⟨u, σ·a u⟩ = a·r(u)`, and
  `|r(u)|² = ‖u‖⁴`: a unit dual spinor is a point of the unit sphere, and the
  outcome `s = ±1` along a unit axis has probability `(1 + s a·r) / 2`.
* A dual rotor `U(β)` turns `r` by the full angle `‖β‖` about `β`; two
  `SU(2)` matrices turn every axis alike exactly when they differ by sign.
* The interference of `u` with `U(β) u` has intensity `cos² (‖β‖ / 4)` for
  every `u`: the period `4π` of the dual angle is visible.
* `[σ·a, σ·b] = 2i σ·(a × b)`, and on a unit dual spinor
  `Var(σ·a) Var(σ·b) = (a·b - ⟨σ·a⟩⟨σ·b⟩)² + ⟨σ·(a × b)⟩²`, so the Robertson
  bound holds with the covariance as the exact excess; along three
  perpendicular axes the variances sum to `2`.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

open scoped InnerProductSpace

/-! ### Expectations and the spin vector -/

/-- Expectation `⟨u, A u⟩`. -/
noncomputable def spinExp (A : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) : ℂ :=
  inner ℂ u (applyMat A u)

theorem spinExp_add (A B : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) :
    spinExp (A + B) u = spinExp A u + spinExp B u := by
  simp [spinExp, applyMat_add_mat, inner_add_right]

theorem spinExp_smul (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) :
    spinExp (c • A) u = c * spinExp A u := by
  simp [spinExp, applyMat_smul_mat, inner_smul_right]

theorem spinExp_one (u : DualSpinor) : spinExp 1 u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [spinExp, applyMat_one, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem star_spinExp (A : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) :
    star (spinExp A u) = spinExp Aᴴ u := by
  rw [spinExp, spinExp, ← applyMat_inner]
  exact inner_conj_symm (applyMat A u) u

theorem spinExp_im_of_hermitian {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = A) (u : DualSpinor) :
    (spinExp A u).im = 0 := by
  have h := star_spinExp A u
  rw [hA] at h
  exact Complex.conj_eq_iff_im.mp h

theorem spinExp_re_of_antiHermitian {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A)
    (u : DualSpinor) : (spinExp A u).re = 0 := by
  have h := congrArg Complex.re (star_spinExp A u)
  rw [hA, show -A = (-1 : ℂ) • A by simp, spinExp_smul] at h
  simp at h
  linarith

theorem pauli_conjTranspose (k : Fin 3) : (pauli k)ᴴ = pauli k := by
  fin_cases k
  · exact pauliX_isHermitian
  · exact pauliY_isHermitian
  · exact pauliZ_isHermitian

theorem cyclicRepComb_conjTranspose (n : Fin 3 → ℝ) :
    (cyclicRepComb n)ᴴ = -cyclicRepComb n := by
  unfold cyclicRepComb
  rw [Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_smul, cyclicRep_conjTranspose, smul_neg]
  simp

/-- Spin vector `r(u)_k = ⟨u, σ_k u⟩`. -/
noncomputable def spinVec (u : DualSpinor) : Fin 3 → ℝ :=
  fun k => (spinExp (pauli k) u).re

theorem spinExp_pauli (k : Fin 3) (u : DualSpinor) :
    spinExp (pauli k) u = (spinVec u k : ℂ) := by
  apply Complex.ext
  · simp [spinVec]
  · simp [spinExp_im_of_hermitian (pauli_conjTranspose k)]

/-- `⟨u, σ·a u⟩ = a·r(u)`. -/
theorem spinExp_pauliComb (a : Fin 3 → ℝ) (u : DualSpinor) :
    spinExp (pauliComb a) u = (axisDot a (spinVec u) : ℂ) := by
  simp only [pauliComb, Fin.sum_univ_three, spinExp_add, spinExp_smul, spinExp_pauli, axisDot]
  push_cast
  ring

private theorem dualSpinor_norm_sq (u : DualSpinor) :
    ‖u‖ ^ 2 = (u 0).re ^ 2 + (u 0).im ^ 2 + ((u 1).re ^ 2 + (u 1).im ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  ring

/-- `|r(u)|² = ‖u‖⁴`. -/
theorem axisDot_spinVec (u : DualSpinor) :
    axisDot (spinVec u) (spinVec u) = ‖u‖ ^ 4 := by
  rw [show ‖u‖ ^ 4 = (‖u‖ ^ 2) ^ 2 by ring, dualSpinor_norm_sq]
  simp [axisDot, spinVec, spinExp, dualSpinor_inner_eq, applyMat_apply, pauli, pauliX, pauliY,
    pauliZ, Fin.sum_univ_two]
  ring

theorem axisDot_spinVec_of_norm {u : DualSpinor} (hu : ‖u‖ = 1) :
    axisDot (spinVec u) (spinVec u) = 1 := by
  rw [axisDot_spinVec, hu, one_pow]

/-- Born weight of the outcome `s` along `a`: `⟨u, (1 + s σ·a)/2 u⟩ = (‖u‖² + s a·r) / 2`. -/
theorem spinExp_spinProj (s : ℝ) (a : Fin 3 → ℝ) (u : DualSpinor) :
    spinExp (spinProj s a) u = (((‖u‖ ^ 2 + s * axisDot a (spinVec u)) / 2 : ℝ) : ℂ) := by
  rw [spinProj, spinExp_smul, spinExp_add, spinExp_smul, spinExp_one, spinExp_pauliComb]
  push_cast
  ring

/-! ### Dual rotors turn the spin vector -/

/-- Rodrigues rotation by `θ` about the axis `n`. -/
noncomputable def axisRot (n : Fin 3 → ℝ) (θ : ℝ) (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => Real.cos θ * a k + Real.sin θ * cross3 n a k + (1 - Real.cos θ) * axisDot n a * n k

/-- A rotation about a unit axis preserves the dot product. -/
theorem axisDot_axisRot {n : Fin 3 → ℝ} (hn : axisDot n n = 1) (θ : ℝ) (a b : Fin 3 → ℝ) :
    axisDot (axisRot n θ a) (axisRot n θ b) = axisDot a b := by
  have hcs := Real.cos_sq_add_sin_sq θ
  simp only [axisDot, axisRot, cross3] at hn ⊢
  linear_combination
    (Real.sin θ ^ 2 * (a 0 * b 0 + a 1 * b 1 + a 2 * b 2) +
        (1 - Real.cos θ) ^ 2 * (n 0 * a 0 + n 1 * a 1 + n 2 * a 2) *
          (n 0 * b 0 + n 1 * b 1 + n 2 * b 2)) * hn +
      ((a 0 * b 0 + a 1 * b 1 + a 2 * b 2) -
          (n 0 * a 0 + n 1 * a 1 + n 2 * a 2) * (n 0 * b 0 + n 1 * b 1 + n 2 * b 2)) * hcs

/-- The rotation by `-θ` is the transpose of the rotation by `θ`. -/
theorem axisDot_axisRot_neg (n : Fin 3 → ℝ) (θ : ℝ) (a r : Fin 3 → ℝ) :
    axisDot (axisRot n (-θ) a) r = axisDot a (axisRot n θ r) := by
  simp only [axisDot, axisRot, cross3, Real.cos_neg, Real.sin_neg]
  ring

private theorem realSmul_eq (t : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : t • M = (t : ℂ) • M :=
  (algebraMap_smul ℂ t M).symm

/-- Conjugation of `σ·a` by `c + s Γ(n)`. -/
theorem rodrigues_conj_pauliComb (c s : ℝ) (n a : Fin 3 → ℝ) :
    (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + s • cyclicRepComb n)ᴴ * pauliComb a *
        (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + s • cyclicRepComb n) =
      pauliComb (fun k => (c ^ 2 - s ^ 2 * axisDot n n) * a k - 2 * c * s * cross3 n a k +
        2 * s ^ 2 * axisDot n a * n k) := by
  rw [realSmul_eq, realSmul_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [cyclicRepComb, cyclicRep, pauliComb, pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.conjTranspose_apply, axisDot, cross3]
     apply Complex.ext <;> simp [sq] <;> ring)

private theorem unit_axis_of_ne {β : DualRapidity} (h : β ≠ 0) :
    axisDot (fun a => β a / ‖β‖) (fun a => β a / ‖β‖) = 1 := by
  have hr : ‖β‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hnorm : ‖β‖ ^ 2 = (β 0) ^ 2 + (β 1) ^ 2 + (β 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  simp only [axisDot]
  field_simp
  linarith

/-- Heisenberg form: `U(β)ᴴ (σ·a) U(β) = σ·(R_{-‖β‖} a)` about `β / ‖β‖`. -/
theorem dualRotor_conj_pauliComb {β : DualRapidity} (h : β ≠ 0) (a : Fin 3 → ℝ) :
    (dualRotorMat β)ᴴ * pauliComb a * dualRotorMat β =
      pauliComb (axisRot (fun k => β k / ‖β‖) (-‖β‖) a) := by
  rw [dualRotorMat_rodrigues]
  simp only [h, ↓reduceIte]
  rw [rodrigues_conj_pauliComb, unit_axis_of_ne h]
  congr 1
  funext k
  set t := ‖β‖ / 2
  have e : -‖β‖ = -(2 * t) := by simp only [t]; ring
  have hc : Real.cos (-‖β‖) = 2 * Real.cos t ^ 2 - 1 := by
    rw [e, Real.cos_neg, Real.cos_two_mul]
  have hs : Real.sin (-‖β‖) = -(2 * Real.sin t * Real.cos t) := by
    rw [e, Real.sin_neg, Real.sin_two_mul]
  have hcs := Real.sin_sq_add_cos_sq t
  simp only [axisRot, hc, hs]
  linear_combination
    (-a k + 2 * axisDot (fun k => β k / ‖β‖) a * (β k / ‖β‖)) * hcs

theorem spinExp_applyMat (A M : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) :
    spinExp A (applyMat M u) = spinExp (Mᴴ * A * M) u := by
  rw [spinExp, spinExp, ← applyMat_mul, applyMat_inner_mul, Matrix.mul_assoc]

/-- The dual rotor `U(β)` turns the spin vector by the full angle `‖β‖` about `β`. -/
theorem spinVec_dualRotor {β : DualRapidity} (h : β ≠ 0) (u : DualSpinor) :
    spinVec (applyMat (dualRotorMat β) u) =
      axisRot (fun k => β k / ‖β‖) ‖β‖ (spinVec u) := by
  have key : ∀ a : Fin 3 → ℝ, axisDot a (spinVec (applyMat (dualRotorMat β) u)) =
      axisDot a (axisRot (fun k => β k / ‖β‖) ‖β‖ (spinVec u)) := by
    intro a
    have e := spinExp_pauliComb a (applyMat (dualRotorMat β) u)
    rw [spinExp_applyMat, dualRotor_conj_pauliComb h, spinExp_pauliComb,
      axisDot_axisRot_neg] at e
    exact_mod_cast e.symm
  funext k
  have := key (fun j => if j = k then 1 else 0)
  fin_cases k <;> simpa [axisDot] using this

/-- Two `SU(2)` matrices that conjugate every Pauli matrix alike differ by sign. -/
theorem eq_or_eq_neg_of_conj_pauli {U V : Matrix (Fin 2) (Fin 2) ℂ} (hU : Uᴴ * U = 1)
    (hV : Vᴴ * V = 1) (hdU : U.det = 1) (hdV : V.det = 1)
    (h : ∀ k, Uᴴ * pauli k * U = Vᴴ * pauli k * V) : U = V ∨ U = -V := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  set W := V * Uᴴ with hWdef
  have hW : ∀ k, W * pauli k = pauli k * W := by
    intro k
    calc W * pauli k = V * (Uᴴ * pauli k * U) * Uᴴ := by
          simp only [W, Matrix.mul_assoc, hU', Matrix.mul_one]
      _ = V * (Vᴴ * pauli k * V) * Uᴴ := by rw [h k]
      _ = pauli k * W := by simp only [W, ← Matrix.mul_assoc, hV', Matrix.one_mul]
  have hx := hW 0
  have hz := hW 2
  have e01 := congrFun (congrFun hz 0) 1
  have e10 := congrFun (congrFun hz 1) 0
  have e00 := congrFun (congrFun hx 0) 1
  simp [pauli, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at e01 e10 e00
  have w01 : W 0 1 = 0 := by linear_combination -e01 / 2
  have w10 : W 1 0 = 0 := by linear_combination e10 / 2
  have hdet : W.det = 1 := by
    rw [hWdef, Matrix.det_mul, Matrix.det_conjTranspose, hdU, hdV]
    simp
  rw [Matrix.det_fin_two, w01, w10, ← e00] at hdet
  have hsq : (W 0 0 - 1) * (W 0 0 + 1) = 0 := by linear_combination hdet
  have hWs : ∀ c : ℂ, W 0 0 = c → W = c • 1 := by
    intro c hc
    ext i j
    fin_cases i <;> fin_cases j <;> simp [w01, w10, ← e00, hc]
  rcases mul_eq_zero.mp hsq with h1 | h1
  · left
    have hW1 : W = 1 := by rw [hWs 1 (by linear_combination h1), one_smul]
    calc U = (V * Uᴴ) * U := by rw [← hWdef, hW1, Matrix.one_mul]
      _ = V := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  · right
    have hW1 : W = -1 := by rw [hWs (-1) (by linear_combination h1)]; simp
    calc U = -((V * Uᴴ) * U) := by rw [← hWdef, hW1]; simp
      _ = -V := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]

/-- Two dual rotors turn every spin vector alike exactly when they differ by sign. -/
theorem dualRotor_conj_pauli_eq_iff (β γ : DualRapidity) :
    (∀ k, (dualRotorMat β)ᴴ * pauli k * dualRotorMat β =
        (dualRotorMat γ)ᴴ * pauli k * dualRotorMat γ) ↔
      dualRotorMat β = dualRotorMat γ ∨ dualRotorMat β = -dualRotorMat γ := by
  refine ⟨eq_or_eq_neg_of_conj_pauli (dualRotorMat_unitary β) (dualRotorMat_unitary γ)
    (dualRotorMat_det β) (dualRotorMat_det γ), ?_⟩
  rintro (h | h) k <;> simp [h]

/-! ### The `4π` period in interference -/

/-- `Re ⟨u, U(β) u⟩ = cos (‖β‖ / 2) ‖u‖²` for every dual spinor. -/
theorem spinExp_dualRotor_re (β : DualRapidity) (u : DualSpinor) :
    (spinExp (dualRotorMat β) u).re = Real.cos (‖β‖ / 2) * ‖u‖ ^ 2 := by
  rw [dualRotorMat_rodrigues]
  split_ifs with h
  · rw [add_zero, realSmul_eq, spinExp_smul, spinExp_one, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  · rw [realSmul_eq, realSmul_eq, spinExp_add, spinExp_smul, spinExp_smul, spinExp_one,
      Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.re_ofReal_mul,
      spinExp_re_of_antiHermitian (cyclicRepComb_conjTranspose (fun a => β a / ‖β‖)) u,
      mul_zero, add_zero]

theorem norm_applyMat_dualRotor_sq (β : DualRapidity) (u : DualSpinor) :
    ‖applyMat (dualRotorMat β) u‖ ^ 2 = ‖u‖ ^ 2 := by
  have h1 : inner ℂ (applyMat (dualRotorMat β) u) (applyMat (dualRotorMat β) u) =
      inner ℂ u u := by
    rw [applyMat_inner_mul, dualRotorMat_unitary, applyMat_one]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  exact_mod_cast h1

/-- Interference of `u` with `U(β) u`: `‖u + U(β) u‖² = 4 cos² (‖β‖ / 4) ‖u‖²`. -/
theorem norm_add_dualRotor_sq (β : DualRapidity) (u : DualSpinor) :
    ‖u + applyMat (dualRotorMat β) u‖ ^ 2 = 4 * Real.cos (‖β‖ / 4) ^ 2 * ‖u‖ ^ 2 := by
  rw [@norm_add_sq ℂ, norm_applyMat_dualRotor_sq]
  have hre : RCLike.re (inner ℂ u (applyMat (dualRotorMat β) u)) =
      Real.cos (‖β‖ / 2) * ‖u‖ ^ 2 := spinExp_dualRotor_re β u
  rw [hre]
  have hc := Real.cos_two_mul (‖β‖ / 4)
  rw [show 2 * (‖β‖ / 4) = ‖β‖ / 2 by ring] at hc
  rw [hc]
  ring

/-! ### Uncertainty -/

/-- `{σ·a, σ·b} = 2 a·b`. -/
theorem pauliComb_anticomm (a b : Fin 3 → ℝ) :
    pauliComb a * pauliComb b + pauliComb b * pauliComb a =
      ((2 * axisDot a b : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [pauliComb, pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_three, axisDot]
     try (apply Complex.ext <;> simp <;> ring))

/-- `[σ·a, σ·b] = 2i σ·(a × b)`. -/
theorem pauliComb_comm (a b : Fin 3 → ℝ) :
    pauliComb a * pauliComb b - pauliComb b * pauliComb a =
      (2 * I) • pauliComb (cross3 a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [pauliComb, pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_three, cross3]
     apply Complex.ext <;> simp <;> ring)

theorem spinExp_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) :
    spinExp (A - B) u = spinExp A u - spinExp B u := by
  rw [sub_eq_add_neg, spinExp_add, show -B = (-1 : ℂ) • B by simp, spinExp_smul]
  ring

/-- `⟨u, [σ·a, σ·b] u⟩ = 2i (a × b)·r(u)`. -/
theorem spinExp_pauliComb_comm (a b : Fin 3 → ℝ) (u : DualSpinor) :
    spinExp (pauliComb a * pauliComb b - pauliComb b * pauliComb a) u =
      2 * I * (axisDot (cross3 a b) (spinVec u) : ℂ) := by
  rw [pauliComb_comm, spinExp_smul, spinExp_pauliComb]

/-- Variance of `σ·a`. -/
noncomputable def spinVar (a : Fin 3 → ℝ) (u : DualSpinor) : ℝ :=
  (spinExp (pauliComb a * pauliComb a) u).re - axisDot a (spinVec u) ^ 2

theorem spinVar_eq (a : Fin 3 → ℝ) (u : DualSpinor) :
    spinVar a u = axisDot a a * ‖u‖ ^ 2 - axisDot a (spinVec u) ^ 2 := by
  rw [spinVar, pauliComb, pauli_dot_sq, spinExp_smul, spinExp_one]
  congr 1
  rw [show ((a 0 : ℂ) ^ 2 + (a 1 : ℂ) ^ 2 + (a 2 : ℂ) ^ 2) = ((axisDot a a : ℝ) : ℂ) by
    simp only [axisDot]; push_cast; ring]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

private theorem gram_cross (a b r : Fin 3 → ℝ) :
    axisDot (cross3 a b) r ^ 2 =
      axisDot a a * axisDot b b * axisDot r r + 2 * axisDot a b * axisDot a r * axisDot b r -
        axisDot a a * axisDot b r ^ 2 - axisDot b b * axisDot a r ^ 2 -
          axisDot r r * axisDot a b ^ 2 := by
  simp only [axisDot, cross3]
  ring

private theorem lagrange_cross (a b : Fin 3 → ℝ) :
    axisDot (cross3 a b) (cross3 a b) = axisDot a a * axisDot b b - axisDot a b ^ 2 := by
  simp only [axisDot, cross3]
  ring

/-- On a unit dual spinor the Robertson–Schrödinger relation is an equality:
`Var(σ·a) Var(σ·b) = (a·b - ⟨σ·a⟩⟨σ·b⟩)² + ⟨σ·(a × b)⟩²`. -/
theorem spinVar_mul_spinVar {u : DualSpinor} (hu : ‖u‖ = 1) (a b : Fin 3 → ℝ) :
    spinVar a u * spinVar b u =
      (axisDot a b - axisDot a (spinVec u) * axisDot b (spinVec u)) ^ 2 +
        axisDot (cross3 a b) (spinVec u) ^ 2 := by
  have hr := axisDot_spinVec_of_norm hu
  rw [spinVar_eq, spinVar_eq, hu, one_pow, mul_one, mul_one]
  linear_combination (axisDot a b ^ 2 - axisDot a a * axisDot b b) * hr -
    gram_cross a b (spinVec u)

/-- Robertson bound: `|⟨[σ·a, σ·b]⟩|² / 4 ≤ Var(σ·a) Var(σ·b)`. -/
theorem robertson_spin {u : DualSpinor} (hu : ‖u‖ = 1) (a b : Fin 3 → ℝ) :
    ‖spinExp (pauliComb a * pauliComb b - pauliComb b * pauliComb a) u‖ ^ 2 / 4 ≤
      spinVar a u * spinVar b u := by
  rw [spinExp_pauliComb_comm, spinVar_mul_spinVar hu, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, mul_one, mul_pow, sq_abs]
  nlinarith [sq_nonneg (axisDot a b - axisDot a (spinVec u) * axisDot b (spinVec u))]

/-- Along three perpendicular unit axes the spin variances of a unit dual spinor
sum to `2`. -/
theorem spinVar_add_add {u : DualSpinor} (hu : ‖u‖ = 1) {a b : Fin 3 → ℝ}
    (ha : axisDot a a = 1) (hb : axisDot b b = 1) (hab : axisDot a b = 0) :
    spinVar a u + spinVar b u + spinVar (cross3 a b) u = 2 := by
  have hr := axisDot_spinVec_of_norm hu
  rw [spinVar_eq, spinVar_eq, spinVar_eq, hu, one_pow, mul_one, mul_one, mul_one]
  set x := axisDot a (spinVec u)
  set y := axisDot b (spinVec u)
  linear_combination lagrange_cross a b - gram_cross a b (spinVec u) + (1 + y ^ 2) * ha +
    (1 + x ^ 2) * hb + (axisDot (spinVec u) (spinVec u) * axisDot a b - axisDot a b -
      2 * x * y) * hab - axisDot a a * axisDot b b * hr

/-- A dual spinor sharp along `a` has variance `1` along every perpendicular unit axis. -/
theorem spinVar_eq_one_of_sharp {u : DualSpinor} (hu : ‖u‖ = 1) {a b : Fin 3 → ℝ}
    (ha : axisDot a a = 1) (hb : axisDot b b = 1) (hab : axisDot a b = 0)
    (hsharp : spinVar a u = 0) : spinVar b u = 1 := by
  have h := spinVar_mul_spinVar hu a b
  have hsum := spinVar_add_add hu ha hb hab
  have hvb := spinVar_eq b u
  have hvc := spinVar_eq (cross3 a b) u
  have hva := spinVar_eq a u
  rw [hu, one_pow, mul_one] at hvb hvc hva
  rw [hsharp] at h hsum
  rw [hab, zero_sub] at h
  nlinarith [sq_nonneg (axisDot (cross3 a b) (spinVec u)), sq_nonneg (axisDot b (spinVec u)),
    sq_nonneg (axisDot a (spinVec u) * axisDot b (spinVec u)), lagrange_cross a b]

end Logic

end DstDiophantine
