import DstDiophantine.Logic.Quantum.DiracConjugation

/-!
# Two dual spinors: the singlet, correlations, and the CHSH bound

A joint state of two dual spinors is a vector of `ℂ² ⊗ ℂ²`, stored as the
`2 × 2` array `Ψ i j` of amplitudes of `e_i ⊗ e_j`. Local operators act by
`A ⊗ B : Ψ ↦ A Ψ Bᵀ`.

* `det Ψ` is unchanged by every pair of total rotors and vanishes exactly on
  product states `u ⊗ v`; `2 ‖det Ψ‖ ≤ ‖Ψ‖²`, with equality for the singlet.
  Local dual rotors preserve both `det Ψ` and `‖Ψ‖²`.
* The states fixed by every common dual rotor form the line of the singlet
  `ε = e₀ ⊗ e₁ - e₁ ⊗ e₀`, which every common total rotor also fixes.
* `J u ⊗ u - u ⊗ J u = ‖u‖² ε`, and the singlet overlap of `u ⊗ v` is
  `-⟨J u, v⟩`.
* In the singlet `⟨σ·a ⊗ σ·b⟩ = -a·b`, each one-particle mean vanishes, and
  the outcomes `(s, t)` along `a` and `b` occur with weight `(1 - s t a·b) / 4`.
* No signalling: a unitary on one particle, or the choice of a two-outcome
  measurement there, leaves every expectation of the other unchanged.
* CHSH: outcomes fixed by local variables under any finite distribution give
  `|S| ≤ 2`; the singlet reaches `|S| = 2√2`, its maximum over unit axes.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

/-! ### Joint states and local operators -/

/-- Joint state of two dual spinors: `Ψ i j` is the amplitude of `e_i ⊗ e_j`. -/
abbrev PairState := Matrix (Fin 2) (Fin 2) ℂ

/-- Product state `u ⊗ v`. -/
def pairTensor (u v : DualSpinor) : PairState :=
  Matrix.of fun i j => u i * v j

@[simp] theorem pairTensor_apply (u v : DualSpinor) (i j : Fin 2) :
    pairTensor u v i j = u i * v j := rfl

/-- Local operator `A ⊗ B`, acting by `Ψ ↦ A Ψ Bᵀ`. -/
def pairAct (A B : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) : PairState :=
  A * Ψ * Bᵀ

/-- Inner product of `ℂ² ⊗ ℂ²`. -/
def pairInner (Ψ Φ : PairState) : ℂ :=
  ∑ i, ∑ j, star (Ψ i j) * Φ i j

/-- Squared norm of a joint state. -/
noncomputable def pairNormSq (Ψ : PairState) : ℝ :=
  ∑ i, ∑ j, ‖Ψ i j‖ ^ 2

/-- Singlet `e₀ ⊗ e₁ - e₁ ⊗ e₀`. -/
def singlet : PairState :=
  !![0, 1; -1, 0]

theorem pairAct_tensor (A B : Matrix (Fin 2) (Fin 2) ℂ) (u v : DualSpinor) :
    pairAct A B (pairTensor u v) = pairTensor (applyMat A u) (applyMat B v) := by
  ext i j
  simp only [pairAct, Matrix.mul_apply, Matrix.transpose_apply, pairTensor_apply,
    applyMat_apply, Fin.sum_univ_two]
  ring

theorem pairAct_pairAct (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) :
    pairAct A B (pairAct C D Ψ) = pairAct (A * C) (B * D) Ψ := by
  simp only [pairAct, Matrix.transpose_mul, Matrix.mul_assoc]

theorem pairAct_one_one (Ψ : PairState) : pairAct 1 1 Ψ = Ψ := by
  simp [pairAct]

theorem pairAct_sub_left (A B C : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) :
    pairAct (A - B) C Ψ = pairAct A C Ψ - pairAct B C Ψ := by
  simp [pairAct, Matrix.sub_mul]

theorem pairInner_sub_right (Ψ Φ Χ : PairState) :
    pairInner Ψ (Φ - Χ) = pairInner Ψ Φ - pairInner Ψ Χ := by
  simp only [pairInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pairInner_eq_trace (Ψ Φ : PairState) : pairInner Ψ Φ = (Ψᴴ * Φ).trace := by
  simp only [pairInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two]
  ring

theorem pairInner_self (Ψ : PairState) : pairInner Ψ Ψ = (pairNormSq Ψ : ℂ) := by
  simp only [pairInner, pairNormSq, Fin.sum_univ_two, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.star_def, Complex.conj_mul']

/-- Local unitaries preserve the inner product. -/
theorem pairInner_pairAct_unitary {U V : Matrix (Fin 2) (Fin 2) ℂ} (hU : Uᴴ * U = 1)
    (hV : Vᴴ * V = 1) (Ψ Φ : PairState) :
    pairInner (pairAct U V Ψ) (pairAct U V Φ) = pairInner Ψ Φ := by
  rw [pairInner_eq_trace, pairInner_eq_trace, pairAct, pairAct]
  have hVT : Vᵀ * Vᵀᴴ = 1 := by
    have e : Vᵀᴴ = Vᴴᵀ := rfl
    rw [e, ← Matrix.transpose_mul, hV, Matrix.transpose_one]
  have h : (U * Ψ * Vᵀ)ᴴ * (U * Φ * Vᵀ) = Vᵀᴴ * (Ψᴴ * Φ * Vᵀ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  rw [h, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hVT, Matrix.mul_one]

theorem pairNormSq_pairAct_unitary {U V : Matrix (Fin 2) (Fin 2) ℂ} (hU : Uᴴ * U = 1)
    (hV : Vᴴ * V = 1) (Ψ : PairState) :
    pairNormSq (pairAct U V Ψ) = pairNormSq Ψ := by
  have h := pairInner_pairAct_unitary hU hV Ψ Ψ
  rw [pairInner_self, pairInner_self] at h
  exact_mod_cast h

/-! ### The antisymmetric invariant -/

theorem det_pairAct (A B : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) :
    (pairAct A B Ψ).det = A.det * Ψ.det * B.det := by
  simp [pairAct, Matrix.det_mul, Matrix.det_transpose]

/-- Total rotors on the two particles, each of determinant one, leave `det Ψ`
unchanged. -/
theorem det_pairAct_of_det_one {M N : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1)
    (hN : N.det = 1) (Ψ : PairState) : (pairAct M N Ψ).det = Ψ.det := by
  rw [det_pairAct, hM, hN, one_mul, mul_one]

/-- Independent dual rotors on the two particles preserve `det Ψ` and `‖Ψ‖²`. -/
theorem det_pairAct_dualRotor (β γ : DualRapidity) (Ψ : PairState) :
    (pairAct (dualRotorMat β) (dualRotorMat γ) Ψ).det = Ψ.det :=
  det_pairAct_of_det_one (dualRotorMat_det β) (dualRotorMat_det γ) Ψ

theorem pairNormSq_pairAct_dualRotor (β γ : DualRapidity) (Ψ : PairState) :
    pairNormSq (pairAct (dualRotorMat β) (dualRotorMat γ) Ψ) = pairNormSq Ψ :=
  pairNormSq_pairAct_unitary (dualRotorMat_unitary β) (dualRotorMat_unitary γ) Ψ

theorem det_pairTensor (u v : DualSpinor) : (pairTensor u v).det = 0 := by
  rw [Matrix.det_fin_two]
  simp only [pairTensor_apply]
  ring

/-- A joint state is a product of two dual spinors exactly when `det Ψ = 0`. -/
theorem exists_pairTensor_iff_det (Ψ : PairState) :
    (∃ u v : DualSpinor, Ψ = pairTensor u v) ↔ Ψ.det = 0 := by
  refine ⟨fun ⟨u, v, h⟩ => h ▸ det_pairTensor u v, fun h => ?_⟩
  rw [Matrix.det_fin_two] at h
  by_cases h00 : Ψ 0 0 = 0
  · by_cases h01 : Ψ 0 1 = 0
    · refine ⟨WithLp.toLp 2 ![0, 1], WithLp.toLp 2 ![Ψ 1 0, Ψ 1 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01]
    · have h10 : Ψ 1 0 = 0 := by
        have h' : Ψ 0 1 * Ψ 1 0 = 0 := by
          rw [h00, zero_mul, zero_sub, neg_eq_zero] at h
          exact h
        exact (mul_eq_zero.mp h').resolve_left h01
      refine ⟨WithLp.toLp 2 ![1, Ψ 1 1 / Ψ 0 1], WithLp.toLp 2 ![0, Ψ 0 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h10, h01]
  · refine ⟨WithLp.toLp 2 ![1, Ψ 1 0 / Ψ 0 0], WithLp.toLp 2 ![Ψ 0 0, Ψ 0 1], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00]
    field_simp
    linear_combination h

/-- `2 ‖det Ψ‖ ≤ ‖Ψ‖²`. -/
theorem two_norm_det_le (Ψ : PairState) : 2 * ‖Ψ.det‖ ≤ pairNormSq Ψ := by
  rw [Matrix.det_fin_two]
  have h1 := norm_sub_le (Ψ 0 0 * Ψ 1 1) (Ψ 0 1 * Ψ 1 0)
  rw [norm_mul, norm_mul] at h1
  simp only [pairNormSq, Fin.sum_univ_two]
  nlinarith [sq_nonneg (‖Ψ 0 0‖ - ‖Ψ 1 1‖), sq_nonneg (‖Ψ 0 1‖ - ‖Ψ 1 0‖)]

/-! ### The singlet -/

theorem det_singlet : singlet.det = 1 := by
  simp [singlet, Matrix.det_fin_two]

theorem pairNormSq_singlet : pairNormSq singlet = 2 := by
  simp [pairNormSq, singlet, Fin.sum_univ_two]
  norm_num

/-- The singlet attains `2 ‖det Ψ‖ = ‖Ψ‖²`. -/
theorem two_norm_det_singlet : 2 * ‖singlet.det‖ = pairNormSq singlet := by
  rw [det_singlet, pairNormSq_singlet, norm_one, mul_one]

theorem singlet_ne_pairTensor (u v : DualSpinor) : singlet ≠ pairTensor u v := by
  intro h
  have h2 := det_pairTensor u v
  rw [← h, det_singlet] at h2
  exact one_ne_zero h2

/-- `M ⊗ M` multiplies the singlet by `det M`. -/
theorem pairAct_singlet (M : Matrix (Fin 2) (Fin 2) ℂ) :
    pairAct M M singlet = M.det • singlet := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairAct, singlet, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

/-- Every common total rotor fixes the singlet. -/
theorem pairAct_singlet_of_det_one {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) :
    pairAct M M singlet = singlet := by
  rw [pairAct_singlet, hM, one_smul]

theorem pairAct_dualRotor_singlet (β : DualRapidity) :
    pairAct (dualRotorMat β) (dualRotorMat β) singlet = singlet :=
  pairAct_singlet_of_det_one (dualRotorMat_det β)

private def halfTurnZ : Matrix (Fin 2) (Fin 2) ℂ := !![-I, 0; 0, I]

private def halfTurnY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

private theorem exists_dualRotor_halfTurnZ : ∃ β : DualRapidity, dualRotorMat β = halfTurnZ := by
  refine dualRotor_surj ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [halfTurnZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · simp [halfTurnZ, Matrix.det_fin_two]

private theorem exists_dualRotor_halfTurnY : ∃ β : DualRapidity, dualRotorMat β = halfTurnY := by
  refine dualRotor_surj ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [halfTurnY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · simp [halfTurnY, Matrix.det_fin_two]

/-- The joint states fixed by every common dual rotor form the line of the
singlet. -/
theorem eq_smul_singlet_of_dualRotor_fixed {Ψ : PairState}
    (h : ∀ β : DualRapidity, pairAct (dualRotorMat β) (dualRotorMat β) Ψ = Ψ) :
    Ψ = Ψ 0 1 • singlet := by
  obtain ⟨βz, hz⟩ := exists_dualRotor_halfTurnZ
  obtain ⟨βy, hy⟩ := exists_dualRotor_halfTurnY
  have hZ := h βz
  have hY := h βy
  rw [hz] at hZ
  rw [hy] at hY
  have e00 := congrFun (congrFun hZ 0) 0
  have e11 := congrFun (congrFun hZ 1) 1
  have e10 := congrFun (congrFun hY 1) 0
  simp only [pairAct, halfTurnZ, halfTurnY, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e11 e10
  ring_nf at e00 e11 e10
  simp only [I_sq] at e00 e11 e10
  ext i j
  fin_cases i <;> fin_cases j <;> simp [singlet]
  · linear_combination -e00 / 2
  · linear_combination -e10
  · linear_combination -e11 / 2

/-- The singlet pairs a dual spinor with its quaternionic partner:
`J u ⊗ u - u ⊗ J u = ‖u‖² ε`. -/
theorem quatJ_pair_eq_singlet (u : DualSpinor) :
    pairTensor (quatJ u) u - pairTensor u (quatJ u) = inner ℂ u u • singlet := by
  rw [dualSpinor_inner_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singlet, Fin.sum_univ_two] <;> ring

theorem quatJ_pair_eq_singlet_of_norm {u : DualSpinor} (hu : ‖u‖ = 1) :
    pairTensor (quatJ u) u - pairTensor u (quatJ u) = singlet := by
  rw [quatJ_pair_eq_singlet, inner_self_eq_norm_sq_to_K, hu]
  simp

/-- The singlet overlap of a product state `u ⊗ v` is `-⟨J u, v⟩`. -/
theorem pairInner_singlet_tensor (u v : DualSpinor) :
    pairInner singlet (pairTensor u v) = -inner ℂ (quatJ u) v := by
  simp [pairInner, singlet, dualSpinor_inner_eq, Fin.sum_univ_two]

/-- Parallel spins have no singlet component. -/
theorem pairInner_singlet_tensor_parallel (c : ℂ) (u : DualSpinor) :
    pairInner singlet (pairTensor u (c • u)) = 0 := by
  rw [pairInner_singlet_tensor, inner_smul_right]
  have h : inner ℂ (quatJ u) u = 0 := by
    rw [← inner_conj_symm, inner_self_quatJ, map_zero]
  rw [h, mul_zero, neg_zero]

/-- The spin-reversed partner `J u` has singlet overlap `-‖u‖²`. -/
theorem pairInner_singlet_tensor_quatJ (u : DualSpinor) :
    pairInner singlet (pairTensor u (quatJ u)) = -inner ℂ u u := by
  rw [pairInner_singlet_tensor, inner_quatJ_quatJ]

/-! ### Spin correlations in the singlet -/

/-- Euclidean dot product of two axes. -/
def axisDot (a b : Fin 3 → ℝ) : ℝ :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2

theorem pairInner_singlet_singlet : pairInner singlet singlet = 2 := by
  rw [pairInner_self, pairNormSq_singlet]
  norm_num

/-- `⟨ε| σ·a ⊗ σ·b |ε⟩ = -2 a·b`. -/
theorem pairInner_singlet_pauli (a b : Fin 3 → ℝ) :
    pairInner singlet (pairAct (pauliComb a) (pauliComb b) singlet) =
      -2 * (axisDot a b : ℂ) := by
  simp [pairInner, pairAct, singlet, pauliComb, pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_three, axisDot]
  ring_nf
  simp only [I_sq]
  ring

/-- Each one-particle spin mean vanishes in the singlet. -/
theorem pairInner_singlet_pauli_left (a : Fin 3 → ℝ) :
    pairInner singlet (pairAct (pauliComb a) 1 singlet) = 0 := by
  simp [pairInner, pairAct, singlet, pauliComb, pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_three]

theorem pairInner_singlet_pauli_right (b : Fin 3 → ℝ) :
    pairInner singlet (pairAct 1 (pauliComb b) singlet) = 0 := by
  simp [pairInner, pairAct, singlet, pauliComb, pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_three]

/-- Spin projector `(1 + s σ·a) / 2`. -/
noncomputable def spinProj (s : ℝ) (a : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (s : ℂ) • pauliComb a)

theorem spinProj_add_neg (a : Fin 3 → ℝ) : spinProj 1 a + spinProj (-1) a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinProj] <;> ring

/-- Along a unit axis the spin projector is idempotent. -/
theorem spinProj_mul_self {a : Fin 3 → ℝ} (ha : axisDot a a = 1) {s : ℝ} (hs : s ^ 2 = 1) :
    spinProj s a * spinProj s a = spinProj s a := by
  have hsq := pauli_dot_sq a
  have ha' : ((a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2 : ℂ) = 1 := by
    have : (a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2 = 1 := by rw [← ha, axisDot]; ring
    exact_mod_cast this
  have hP : pauliComb a * pauliComb a = 1 := by
    rw [pauliComb, hsq, ha', one_smul]
  have hs' : (s : ℂ) * s = 1 := by
    have : s * s = 1 := by rw [← hs]; ring
    exact_mod_cast this
  simp only [spinProj, smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hP, hs']
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- In the singlet the outcomes `s, t = ±1` along `a` and `b` have joint weight
`(1 - s t a·b) / 2` against the norm `2`. -/
theorem pairInner_singlet_spinProj (s t : ℝ) (a b : Fin 3 → ℝ) :
    pairInner singlet (pairAct (spinProj s a) (spinProj t b) singlet) =
      ((1 - s * t * axisDot a b) / 2 : ℝ) := by
  simp [pairInner, pairAct, singlet, spinProj, pauliComb, pauli, pauliX, pauliY, pauliZ,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, axisDot]
  ring_nf
  simp only [I_sq]
  ring

/-- Probability of opposite outcomes along axes at angle `θ`: `cos² (θ / 2)`. -/
theorem singlet_opposite_prob {a b : Fin 3 → ℝ} {θ : ℝ} (hθ : axisDot a b = Real.cos θ) :
    ((pairInner singlet (pairAct (spinProj 1 a) (spinProj (-1) b) singlet) +
        pairInner singlet (pairAct (spinProj (-1) a) (spinProj 1 b) singlet)) /
        pairInner singlet singlet).re = Real.cos (θ / 2) ^ 2 := by
  have hc : Real.cos (θ / 2) ^ 2 = 1 / 2 + Real.cos θ / 2 := by
    rw [Real.cos_sq, show 2 * (θ / 2) = θ by ring]
  rw [pairInner_singlet_spinProj, pairInner_singlet_spinProj, pairInner_singlet_singlet, hθ, hc,
    ← Complex.ofReal_add, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div,
    Complex.ofReal_re]
  ring

/-! ### No signalling -/

/-- A unitary on the first particle leaves every expectation of the second
unchanged. -/
theorem pairInner_local_unitary {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : Uᴴ * U = 1)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) :
    pairInner (pairAct U 1 Ψ) (pairAct 1 B (pairAct U 1 Ψ)) = pairInner Ψ (pairAct 1 B Ψ) := by
  have h : pairAct 1 B (pairAct U 1 Ψ) = pairAct U 1 (pairAct 1 B Ψ) := by
    rw [pairAct_pairAct, pairAct_pairAct, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
      Matrix.one_mul]
  rw [h, pairInner_pairAct_unitary hU (by simp)]

/-- A local dual rotor on the first particle leaves every expectation of the
second unchanged. -/
theorem pairInner_local_dualRotor (β : DualRapidity) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (Ψ : PairState) :
    pairInner (pairAct (dualRotorMat β) 1 Ψ) (pairAct 1 B (pairAct (dualRotorMat β) 1 Ψ)) =
      pairInner Ψ (pairAct 1 B Ψ) :=
  pairInner_local_unitary (dualRotorMat_unitary β) B Ψ

/-- Summing over the outcomes of a two-outcome measurement on the first particle
returns the expectation of the second alone, whatever the first measurement. -/
theorem pairInner_marginal (P B : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) :
    pairInner Ψ (pairAct P B Ψ) + pairInner Ψ (pairAct (1 - P) B Ψ) =
      pairInner Ψ (pairAct 1 B Ψ) := by
  rw [pairAct_sub_left, pairInner_sub_right]
  ring

theorem pairInner_marginal_spin (a : Fin 3 → ℝ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (Ψ : PairState) :
    pairInner Ψ (pairAct (spinProj 1 a) B Ψ) + pairInner Ψ (pairAct (spinProj (-1) a) B Ψ) =
      pairInner Ψ (pairAct 1 B Ψ) := by
  rw [← pairInner_marginal (spinProj 1 a) B Ψ, ← spinProj_add_neg a, add_sub_cancel_left]

/-! ### The CHSH combination -/

/-- CHSH combination of a correlation function. -/
def chsh (E : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) (a a' b b' : Fin 3 → ℝ) : ℝ :=
  E a b + E a b' + E a' b - E a' b'

private theorem chsh_pointwise {A A' B B' : ℝ} (hA : |A| ≤ 1) (hA' : |A'| ≤ 1) (hB : |B| ≤ 1)
    (hB' : |B'| ≤ 1) : |A * B + A * B' + A' * B - A' * B'| ≤ 2 := by
  have e : A * B + A * B' + A' * B - A' * B' = A * (B + B') + A' * (B - B') := by ring
  rw [e]
  have h1 : |A * (B + B')| ≤ |B + B'| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hA
  have h2 : |A' * (B - B')| ≤ |B - B'| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hA'
  have h3 : |B + B'| + |B - B'| ≤ 2 := by
    have := abs_le.mp hB
    have := abs_le.mp hB'
    rcases abs_cases (B + B') with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
      rcases abs_cases (B - B') with ⟨h5, _⟩ | ⟨h5, _⟩ <;> linarith
  calc |A * (B + B') + A' * (B - B')| ≤ |A * (B + B')| + |A' * (B - B')| := abs_add_le _ _
    _ ≤ 2 := by linarith

/-- Outcomes in `[-1, 1]` fixed by a local variable `i`, averaged over any finite
distribution `w`, keep the CHSH combination within `2`. -/
theorem chsh_local_bound {ι : Type*} (s : Finset ι) (w A A' B B' : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i, |A i| ≤ 1) (hA' : ∀ i, |A' i| ≤ 1) (hB : ∀ i, |B i| ≤ 1)
    (hB' : ∀ i, |B' i| ≤ 1) :
    |∑ i ∈ s, w i * (A i * B i + A i * B' i + A' i * B i - A' i * B' i)| ≤ 2 := by
  calc |∑ i ∈ s, w i * (A i * B i + A i * B' i + A' i * B i - A' i * B' i)|
      ≤ ∑ i ∈ s, |w i * (A i * B i + A i * B' i + A' i * B i - A' i * B' i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i * 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul, abs_of_nonneg (hw i hi)]
        exact mul_le_mul_of_nonneg_left (chsh_pointwise (hA i) (hA' i) (hB i) (hB' i)) (hw i hi)
    _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Normalized singlet correlation of spin measurements along `a` and `b`. -/
noncomputable def singletCorr (a b : Fin 3 → ℝ) : ℝ :=
  (pairInner singlet (pairAct (pauliComb a) (pauliComb b) singlet) /
    pairInner singlet singlet).re

theorem singletCorr_eq (a b : Fin 3 → ℝ) : singletCorr a b = -axisDot a b := by
  rw [singletCorr, pairInner_singlet_pauli, pairInner_singlet_singlet,
    show (-2 * (axisDot a b : ℂ)) / 2 = ((-axisDot a b : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

/-- With `a ⊥ a'` and `b, b'` bisecting them, the singlet gives `S = -2√2`. -/
theorem singletCorr_chsh :
    chsh singletCorr ![0, 0, 1] ![1, 0, 0]
      ![1 / Real.sqrt 2, 0, 1 / Real.sqrt 2] ![-(1 / Real.sqrt 2), 0, 1 / Real.sqrt 2] =
      -(2 * Real.sqrt 2) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [chsh, singletCorr_eq, axisDot]
  simp
  field_simp
  nlinarith [h2]

private theorem axisDot_sq_le (a x : Fin 3 → ℝ) :
    axisDot a x ^ 2 ≤ axisDot a a * axisDot x x := by
  simp only [axisDot]
  nlinarith [sq_nonneg (a 0 * x 1 - a 1 * x 0), sq_nonneg (a 0 * x 2 - a 2 * x 0),
    sq_nonneg (a 1 * x 2 - a 2 * x 1)]

/-- Along unit axes the singlet CHSH combination does not exceed `2√2`. -/
theorem singletCorr_chsh_le {a a' b b' : Fin 3 → ℝ} (ha : axisDot a a = 1)
    (ha' : axisDot a' a' = 1) (hb : axisDot b b = 1) (hb' : axisDot b' b' = 1) :
    |chsh singletCorr a a' b b'| ≤ 2 * Real.sqrt 2 := by
  set X := axisDot a (b + b')
  set Y := axisDot a' (b - b')
  have hS : chsh singletCorr a a' b b' = -(X + Y) := by
    simp only [chsh, singletCorr_eq, X, Y, axisDot, Pi.add_apply, Pi.sub_apply]
    ring
  have hX : X ^ 2 ≤ axisDot (b + b') (b + b') := by
    have := axisDot_sq_le a (b + b')
    rwa [ha, one_mul] at this
  have hY : Y ^ 2 ≤ axisDot (b - b') (b - b') := by
    have := axisDot_sq_le a' (b - b')
    rwa [ha', one_mul] at this
  have hsum : axisDot (b + b') (b + b') + axisDot (b - b') (b - b') = 4 := by
    have e : axisDot (b + b') (b + b') + axisDot (b - b') (b - b') =
        2 * axisDot b b + 2 * axisDot b' b' := by
      simp only [axisDot, Pi.add_apply, Pi.sub_apply]
      ring
    rw [e, hb, hb']
    norm_num
  have h8 : (X + Y) ^ 2 ≤ 8 := by nlinarith [sq_nonneg (X - Y)]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [hS, abs_neg]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (X + Y + 2 * Real.sqrt 2),
    sq_nonneg (X + Y - 2 * Real.sqrt 2)]

end Logic

end DstDiophantine
