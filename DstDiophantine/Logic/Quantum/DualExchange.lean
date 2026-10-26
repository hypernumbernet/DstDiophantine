import DstDiophantine.Logic.Quantum.DualObservables

/-!
# Two dual spinors: partial spin vectors and exchange

* The spin vectors `r_A`, `r_B` of the two particles of a joint state satisfy
  `|r_A|² + 4 ‖det Ψ‖² = |r_B|² + 4 ‖det Ψ‖² = ‖Ψ‖⁴`: on a unit state each
  particle has polarization `√(1 - C²)` with `C = 2 ‖det Ψ‖`.
* Exchange `Ψ ↦ Ψᵀ` commutes with every common rotor. The antisymmetric
  states are the multiples of the singlet, and
  `u ⊗ v - v ⊗ u = -⟨J u, v⟩ ε` vanishes exactly when `v ∥ u` (exclusion).
* `Σ σ_k ⊗ σ_k = 2 P - 1` and `Σ Γ_k ⊗ Γ_k = 1 - 2 P` with `P` the exchange;
  the total spin squared is `S² = 1 + P`: `2` on symmetric states, `0` on the
  singlet.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

open scoped InnerProductSpace

/-! ### Pauli entries and local actions -/

@[simp] theorem pauliY_apply_00 : pauliY 0 0 = 0 := rfl
@[simp] theorem pauliY_apply_01 : pauliY 0 1 = -I := rfl
@[simp] theorem pauliY_apply_10 : pauliY 1 0 = I := rfl
@[simp] theorem pauliY_apply_11 : pauliY 1 1 = 0 := rfl

@[simp] theorem pauliZ_apply_00 : pauliZ 0 0 = 1 := rfl
@[simp] theorem pauliZ_apply_01 : pauliZ 0 1 = 0 := rfl
@[simp] theorem pauliZ_apply_10 : pauliZ 1 0 = 0 := rfl
@[simp] theorem pauliZ_apply_11 : pauliZ 1 1 = -1 := rfl

theorem pairAct_one_right (A : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) :
    pairAct A 1 Ψ = A * Ψ := by
  simp [pairAct]

theorem pairAct_one_left (B : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) :
    pairAct 1 B Ψ = Ψ * Bᵀ := by
  simp [pairAct]

theorem pairAct_mul_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) (i j : Fin 2) :
    (A * Ψ) i j = A i 0 * Ψ 0 j + A i 1 * Ψ 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pairAct_mul_right_apply (Ψ : PairState) (B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (Ψ * Bᵀ) i j = Ψ i 0 * B j 0 + Ψ i 1 * B j 1 := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

theorem pairInner_star (Ψ Φ : PairState) : star (pairInner Ψ Φ) = pairInner Φ Ψ := by
  simp only [pairInner, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem pairInner_left_hermitian {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = A)
    (Ψ : PairState) : (pairInner Ψ (pairAct A 1 Ψ)).im = 0 := by
  have h : star (pairInner Ψ (pairAct A 1 Ψ)) = pairInner Ψ (pairAct A 1 Ψ) := by
    rw [pairInner_star, pairAct_one_right, pairInner_eq_trace, pairInner_eq_trace]
    have hT : (A * Ψ)ᴴ * Ψ = Ψᴴ * (A * Ψ) := by
      simp only [Matrix.conjTranspose_mul, hA, Matrix.mul_assoc]
    rw [hT]
  exact Complex.conj_eq_iff_im.mp h

theorem pairInner_right_hermitian {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : Bᴴ = B)
    (Ψ : PairState) : (pairInner Ψ (pairAct 1 B Ψ)).im = 0 := by
  have h : star (pairInner Ψ (pairAct 1 B Ψ)) = pairInner Ψ (pairAct 1 B Ψ) := by
    rw [pairInner_star, pairAct_one_left, pairInner_eq_trace, pairInner_eq_trace]
    have hBT : Bᵀᴴ = Bᵀ := by
      calc Bᵀᴴ = Bᴴᵀ := rfl
        _ = Bᵀ := by rw [hB]
    have hT : ((Ψ * Bᵀ)ᴴ * Ψ).trace = (Ψᴴ * (Ψ * Bᵀ)).trace := by
      simp only [Matrix.conjTranspose_mul, hBT, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    exact hT
  exact Complex.conj_eq_iff_im.mp h

/-- Spin vector of the first particle: `⟨Ψ, (σ_k ⊗ 1) Ψ⟩`. -/
noncomputable def leftSpinVec (Ψ : PairState) : Fin 3 → ℝ :=
  fun k => (pairInner Ψ (pairAct (pauli k) 1 Ψ)).re

/-- Spin vector of the second particle: `⟨Ψ, (1 ⊗ σ_k) Ψ⟩`. -/
noncomputable def rightSpinVec (Ψ : PairState) : Fin 3 → ℝ :=
  fun k => (pairInner Ψ (pairAct 1 (pauli k) Ψ)).re

theorem pairInner_left_pauli_im (Ψ : PairState) (k : Fin 3) :
    (pairInner Ψ (pairAct (pauli k) 1 Ψ)).im = 0 :=
  pairInner_left_hermitian (pauli_conjTranspose k) Ψ

theorem pairInner_right_pauli_im (Ψ : PairState) (k : Fin 3) :
    (pairInner Ψ (pairAct 1 (pauli k) Ψ)).im = 0 :=
  pairInner_right_hermitian (pauli_conjTranspose k) Ψ

private theorem pairInner_sum (Ψ Φ : PairState) :
    pairInner Ψ Φ =
      star (Ψ 0 0) * Φ 0 0 + star (Ψ 0 1) * Φ 0 1 +
        star (Ψ 1 0) * Φ 1 0 + star (Ψ 1 1) * Φ 1 1 := by
  simp only [pairInner, Fin.sum_univ_two]
  abel

private theorem pairAct_pauli_one (Ψ : PairState) (j : Fin 2) :
    pairAct pauliX 1 Ψ 0 j = Ψ 1 j ∧
      pairAct pauliX 1 Ψ 1 j = Ψ 0 j ∧
        pairAct pauliY 1 Ψ 0 j = -I * Ψ 1 j ∧
          pairAct pauliY 1 Ψ 1 j = I * Ψ 0 j ∧
            pairAct pauliZ 1 Ψ 0 j = Ψ 0 j ∧
              pairAct pauliZ 1 Ψ 1 j = -Ψ 1 j := by
  simp [pairAct_one_right, pairAct_mul_apply]

private theorem pairAct_one_pauli (Ψ : PairState) (i : Fin 2) :
    pairAct 1 pauliX Ψ i 0 = Ψ i 1 ∧
      pairAct 1 pauliX Ψ i 1 = Ψ i 0 ∧
        pairAct 1 pauliY Ψ i 0 = -I * Ψ i 1 ∧
          pairAct 1 pauliY Ψ i 1 = I * Ψ i 0 ∧
            pairAct 1 pauliZ Ψ i 0 = Ψ i 0 ∧
              pairAct 1 pauliZ Ψ i 1 = -Ψ i 1 := by
  simp [pairAct_one_left, pairAct_mul_right_apply, mul_comm I]

private theorem leftSpinVec_comp (Ψ : PairState) :
    leftSpinVec Ψ 0 =
      (star (Ψ 0 0) * Ψ 1 0 + star (Ψ 0 1) * Ψ 1 1 +
        star (Ψ 1 0) * Ψ 0 0 + star (Ψ 1 1) * Ψ 0 1).re ∧
    leftSpinVec Ψ 1 =
      (star (Ψ 0 0) * (-I * Ψ 1 0) + star (Ψ 0 1) * (-I * Ψ 1 1) +
        star (Ψ 1 0) * (I * Ψ 0 0) + star (Ψ 1 1) * (I * Ψ 0 1)).re ∧
    leftSpinVec Ψ 2 =
      (star (Ψ 0 0) * Ψ 0 0 + star (Ψ 0 1) * Ψ 0 1 +
        star (Ψ 1 0) * (-Ψ 1 0) + star (Ψ 1 1) * (-Ψ 1 1)).re := by
  have h0 := pairAct_pauli_one Ψ 0
  have h1 := pairAct_pauli_one Ψ 1
  refine ⟨?_, ?_, ?_⟩
  · simp only [leftSpinVec, pauli, pairInner_sum, h0, h1]
  · simp only [leftSpinVec, pauli, pairInner_sum, h0, h1]
  · simp only [leftSpinVec, pauli, pairInner_sum, h0, h1]

private theorem rightSpinVec_comp (Ψ : PairState) :
    rightSpinVec Ψ 0 =
      (star (Ψ 0 0) * Ψ 0 1 + star (Ψ 0 1) * Ψ 0 0 +
        star (Ψ 1 0) * Ψ 1 1 + star (Ψ 1 1) * Ψ 1 0).re ∧
    rightSpinVec Ψ 1 =
      (star (Ψ 0 0) * (-I * Ψ 0 1) + star (Ψ 0 1) * (I * Ψ 0 0) +
        star (Ψ 1 0) * (-I * Ψ 1 1) + star (Ψ 1 1) * (I * Ψ 1 0)).re ∧
    rightSpinVec Ψ 2 =
      (star (Ψ 0 0) * Ψ 0 0 + star (Ψ 0 1) * (-Ψ 0 1) +
        star (Ψ 1 0) * Ψ 1 0 + star (Ψ 1 1) * (-Ψ 1 1)).re := by
  have h0 := pairAct_one_pauli Ψ 0
  have h1 := pairAct_one_pauli Ψ 1
  refine ⟨?_, ?_, ?_⟩
  · simp only [rightSpinVec, pauli, pairInner_sum, h0, h1]
  · simp only [rightSpinVec, pauli, pairInner_sum, h0, h1]
  · simp only [rightSpinVec, pauli, pairInner_sum, h0, h1]

/-- `|r_A|² + 4 ‖det Ψ‖² = ‖Ψ‖⁴`. -/
theorem axisDot_leftSpinVec (Ψ : PairState) :
    axisDot (leftSpinVec Ψ) (leftSpinVec Ψ) + 4 * ‖Ψ.det‖ ^ 2 = pairNormSq Ψ ^ 2 := by
  obtain ⟨hx, hy, hz⟩ := leftSpinVec_comp Ψ
  have hdet : Ψ.det = Ψ 0 0 * Ψ 1 1 - Ψ 0 1 * Ψ 1 0 := Matrix.det_fin_two Ψ
  have hnorm : pairNormSq Ψ =
      ‖Ψ 0 0‖ ^ 2 + ‖Ψ 0 1‖ ^ 2 + ‖Ψ 1 0‖ ^ 2 + ‖Ψ 1 1‖ ^ 2 := by
    simp [pairNormSq, Fin.sum_univ_two]
    abel
  have nsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [axisDot, hx, hy, hz, hdet, hnorm, nsq, nsq, nsq, nsq, nsq]
  simp only [star_def, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- `|r_B|² + 4 ‖det Ψ‖² = ‖Ψ‖⁴`. -/
theorem axisDot_rightSpinVec (Ψ : PairState) :
    axisDot (rightSpinVec Ψ) (rightSpinVec Ψ) + 4 * ‖Ψ.det‖ ^ 2 = pairNormSq Ψ ^ 2 := by
  obtain ⟨hx, hy, hz⟩ := rightSpinVec_comp Ψ
  have hdet : Ψ.det = Ψ 0 0 * Ψ 1 1 - Ψ 0 1 * Ψ 1 0 := Matrix.det_fin_two Ψ
  have hnorm : pairNormSq Ψ =
      ‖Ψ 0 0‖ ^ 2 + ‖Ψ 0 1‖ ^ 2 + ‖Ψ 1 0‖ ^ 2 + ‖Ψ 1 1‖ ^ 2 := by
    simp [pairNormSq, Fin.sum_univ_two]
    abel
  have nsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [axisDot, hx, hy, hz, hdet, hnorm, nsq, nsq, nsq, nsq, nsq]
  simp only [star_def, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- On a unit joint state both particles have polarization `√(1 - (2 ‖det Ψ‖)²)`. -/
theorem axisDot_spinVec_pair_of_norm {Ψ : PairState} (hΨ : pairNormSq Ψ = 1) :
    axisDot (leftSpinVec Ψ) (leftSpinVec Ψ) = 1 - (2 * ‖Ψ.det‖) ^ 2 ∧
      axisDot (rightSpinVec Ψ) (rightSpinVec Ψ) = 1 - (2 * ‖Ψ.det‖) ^ 2 := by
  have hl := axisDot_leftSpinVec Ψ
  have hr := axisDot_rightSpinVec Ψ
  rw [hΨ] at hl hr
  constructor <;> linarith

theorem pairInner_tensor (u v u' v' : DualSpinor) :
    pairInner (pairTensor u v) (pairTensor u' v') = inner ℂ u u' * inner ℂ v v' := by
  simp only [pairInner, pairTensor_apply, dualSpinor_inner_eq, Fin.sum_univ_two, star_mul]
  ring

/-- A product state leaves each particle with the spin vector of its own factor. -/
theorem leftSpinVec_tensor (u v : DualSpinor) :
    leftSpinVec (pairTensor u v) = fun k => ‖v‖ ^ 2 * spinVec u k := by
  funext k
  have hact : pairAct (pauli k) 1 (pairTensor u v) =
      pairTensor (applyMat (pauli k) u) v := by
    rw [pairAct_tensor, applyMat_one]
  have him : (inner ℂ u (applyMat (pauli k) u)).im = 0 :=
    spinExp_im_of_hermitian (pauli_conjTranspose k) u
  have hvre : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    change ((‖v‖ : ℂ) ^ 2).re = ‖v‖ ^ 2
    simp [pow_two]
  have hvim : (inner ℂ v v).im = 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    change ((‖v‖ : ℂ) ^ 2).im = 0
    simp [pow_two]
  rw [leftSpinVec, hact, pairInner_tensor, spinVec, spinExp, Complex.mul_re, him, hvre, hvim]
  ring

private theorem pauliComb_axis (k : Fin 3) :
    pauliComb (fun j => if j = k then (1 : ℝ) else 0) = pauli k := by
  ext i j
  simp only [pauliComb, Fin.sum_univ_three]
  fin_cases k <;> simp

/-- Neither particle of the singlet has a spin direction. -/
theorem leftSpinVec_singlet : leftSpinVec singlet = 0 := by
  funext k
  have h := pairInner_singlet_pauli_left (fun j => if j = k then 1 else 0)
  rw [pauliComb_axis] at h
  simp [leftSpinVec, h]

theorem rightSpinVec_singlet : rightSpinVec singlet = 0 := by
  funext k
  have h := pairInner_singlet_pauli_right (fun j => if j = k then 1 else 0)
  rw [pauliComb_axis] at h
  simp [rightSpinVec, h]

/-! ### Exchange -/

/-- Exchange of the two particles: `Ψ ↦ Ψᵀ`. -/
def pairSwap (Ψ : PairState) : PairState := Ψᵀ

theorem pairSwap_pairSwap (Ψ : PairState) : pairSwap (pairSwap Ψ) = Ψ := by
  simp [pairSwap]

theorem pairSwap_tensor (u v : DualSpinor) : pairSwap (pairTensor u v) = pairTensor v u := by
  ext i j
  simp [pairSwap, mul_comm]

/-- Exchange intertwines `M ⊗ N` with `N ⊗ M`; it commutes with every common rotor. -/
theorem pairAct_pairSwap (M N : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) :
    pairAct M N (pairSwap Ψ) = pairSwap (pairAct N M Ψ) := by
  simp [pairAct, pairSwap, Matrix.transpose_mul, Matrix.mul_assoc]

theorem pairSwap_singlet : pairSwap singlet = -singlet := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairSwap, singlet]

/-- The antisymmetric joint states are the multiples of the singlet. -/
theorem pairSwap_eq_neg_iff (Ψ : PairState) : pairSwap Ψ = -Ψ ↔ Ψ = Ψ 0 1 • singlet := by
  constructor
  · intro h
    have e00 := congrFun (congrFun h 0) 0
    have e11 := congrFun (congrFun h 1) 1
    have e10 := congrFun (congrFun h 1) 0
    simp only [pairSwap, Matrix.transpose_apply, Matrix.neg_apply] at e00 e11 e10
    have h00 : Ψ 0 0 = 0 := by linear_combination e00 / 2
    have h11 : Ψ 1 1 = 0 := by linear_combination e11 / 2
    ext i j
    fin_cases i <;> fin_cases j
    · simp [singlet, h00]
    · simp [singlet]
    · simp [singlet]
      linear_combination e10
    · simp [singlet, h11]
  · intro h
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairSwap, singlet]

/-- Every joint state is a symmetric state plus a multiple of the singlet. -/
theorem pair_eq_symm_add_singlet (Ψ : PairState) :
    Ψ = (1 / 2 : ℂ) • (Ψ + pairSwap Ψ) + ((Ψ 0 1 - Ψ 1 0) / 2) • singlet ∧
      pairSwap ((1 / 2 : ℂ) • (Ψ + pairSwap Ψ)) = (1 / 2 : ℂ) • (Ψ + pairSwap Ψ) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pairSwap, singlet] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pairSwap] <;> ring

/-- Antisymmetrized product: `u ⊗ v - v ⊗ u = -⟨J u, v⟩ ε`. -/
theorem pairTensor_sub_swap (u v : DualSpinor) :
    pairTensor u v - pairTensor v u = (-inner ℂ (quatJ u) v) • singlet := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singlet, dualSpinor_inner_eq, Fin.sum_univ_two] <;> ring

/-- Exclusion: two dual spinors have a nonzero antisymmetrized product exactly
when they are not parallel. -/
theorem pairTensor_sub_swap_eq_zero_iff {u : DualSpinor} (hu : u ≠ 0) (v : DualSpinor) :
    pairTensor u v - pairTensor v u = 0 ↔ ∃ c : ℂ, v = c • u := by
  rw [pairTensor_sub_swap, smul_eq_zero, neg_eq_zero]
  have hs : singlet ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 1
    simp [singlet] at this
  simp only [hs, or_false]
  have hJ : inner ℂ (quatJ u) v = u 1 * v 0 - u 0 * v 1 := by
    simp [dualSpinor_inner_eq, Fin.sum_univ_two]
    ring
  rw [hJ]
  constructor
  · intro h
    by_cases h0 : u 0 = 0
    · have h1 : u 1 ≠ 0 := by
        intro h1
        apply hu
        ext i
        fin_cases i <;> simp [h0, h1]
      refine ⟨v 1 / u 1, ?_⟩
      ext i
      fin_cases i
      · have : u 1 * v 0 = 0 := by rw [h0, zero_mul, sub_zero] at h; exact h
        simp [h0, (mul_eq_zero.mp this).resolve_left h1]
      · simp
        field_simp
    · refine ⟨v 0 / u 0, ?_⟩
      ext i
      fin_cases i
      · simp
        field_simp
      · simp
        field_simp
        linear_combination -h
  · rintro ⟨c, rfl⟩
    simp
    ring

private theorem pairAct_double_apply (A B : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState)
    (i j : Fin 2) :
    pairAct A B Ψ i j =
      A i 0 * Ψ 0 0 * B j 0 + A i 0 * Ψ 0 1 * B j 1 +
        A i 1 * Ψ 1 0 * B j 0 + A i 1 * Ψ 1 1 * B j 1 := by
  simp [pairAct, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  ring

/-- Dirac exchange identity: `Σ σ_k ⊗ σ_k = 2 P - 1`. -/
theorem sum_pairAct_pauli (Ψ : PairState) :
    ∑ k, pairAct (pauli k) (pauli k) Ψ = (2 : ℂ) • pairSwap Ψ - Ψ := by
  ext i j
  have hx := pairAct_double_apply pauliX pauliX Ψ i j
  have hy := pairAct_double_apply pauliY pauliY Ψ i j
  have hz := pairAct_double_apply pauliZ pauliZ Ψ i j
  simp only [Fin.sum_univ_three, pauli, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    pairSwap, Matrix.transpose_apply, hx, hy, hz]
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> simp only [I_sq] <;> ring

/-- In dual generators: `Σ Γ_k ⊗ Γ_k = 1 - 2 P`. -/
theorem sum_pairAct_cyclicRep (Ψ : PairState) :
    ∑ k, pairAct (cyclicRep k) (cyclicRep k) Ψ = Ψ - (2 : ℂ) • pairSwap Ψ := by
  have h : ∀ k, pairAct (cyclicRep k) (cyclicRep k) Ψ = -pairAct (pauli k) (pauli k) Ψ := by
    intro k
    simp only [pairAct, cyclicRep, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    rw [show -I * -I = (-1 : ℂ) by rw [neg_mul_neg, I_mul_I], neg_one_smul]
  simp only [h, Finset.sum_neg_distrib, sum_pairAct_pauli, neg_sub]

/-- Total spin component `σ_k ⊗ 1 + 1 ⊗ σ_k` (twice the spin). -/
def pairSpin (k : Fin 3) (Ψ : PairState) : PairState :=
  pairAct (pauli k) 1 Ψ + pairAct 1 (pauli k) Ψ

private theorem pairSpin_add (k : Fin 3) (X Y : PairState) :
    pairSpin k (X + Y) = pairSpin k X + pairSpin k Y := by
  simp [pairSpin, pairAct, Matrix.mul_add, Matrix.add_mul]
  abel

private theorem pairSpin_sq (k : Fin 3) (Ψ : PairState) :
    pairSpin k (pairSpin k Ψ) =
      (2 : ℂ) • Ψ + (2 : ℂ) • pairAct (pauli k) (pauli k) Ψ := by
  have hkk : pauli k * pauli k = 1 := pauli_sq k
  have hAA : pairAct (pauli k) 1 (pairAct (pauli k) 1 Ψ) = Ψ := by
    rw [pairAct_pairAct, hkk, one_mul, pairAct_one_one]
  have hBB : pairAct 1 (pauli k) (pairAct 1 (pauli k) Ψ) = Ψ := by
    rw [pairAct_pairAct, one_mul, hkk, pairAct_one_one]
  have hAB : pairAct (pauli k) 1 (pairAct 1 (pauli k) Ψ) = pairAct (pauli k) (pauli k) Ψ := by
    rw [pairAct_pairAct, mul_one, one_mul]
  have hBA : pairAct 1 (pauli k) (pairAct (pauli k) 1 Ψ) = pairAct (pauli k) (pauli k) Ψ := by
    rw [pairAct_pairAct, one_mul, mul_one]
  calc pairSpin k (pairSpin k Ψ)
      = pairSpin k (pairAct (pauli k) 1 Ψ + pairAct 1 (pauli k) Ψ) := rfl
    _ = pairSpin k (pairAct (pauli k) 1 Ψ) + pairSpin k (pairAct 1 (pauli k) Ψ) :=
        pairSpin_add k _ _
    _ = (pairAct (pauli k) 1 (pairAct (pauli k) 1 Ψ) +
          pairAct 1 (pauli k) (pairAct (pauli k) 1 Ψ)) +
        (pairAct (pauli k) 1 (pairAct 1 (pauli k) Ψ) +
          pairAct 1 (pauli k) (pairAct 1 (pauli k) Ψ)) := rfl
    _ = (Ψ + pairAct (pauli k) (pauli k) Ψ) + (pairAct (pauli k) (pauli k) Ψ + Ψ) := by
        rw [hAA, hBA, hAB, hBB]
    _ = (2 : ℂ) • Ψ + (2 : ℂ) • pairAct (pauli k) (pauli k) Ψ := by
        simp [two_smul]
        abel

/-- `Σ (σ_k ⊗ 1 + 1 ⊗ σ_k)² = 4 (1 + P)`, so `S² = 1 + P`. -/
theorem sum_pairSpin_sq (Ψ : PairState) :
    ∑ k, pairSpin k (pairSpin k Ψ) = (4 : ℂ) • (Ψ + pairSwap Ψ) := by
  simp only [pairSpin_sq]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.smul_sum, sum_pairAct_pauli]
  simp [two_smul]
  module

/-- `S² = 2` on symmetric states (spin one) and `0` on the singlet (spin zero). -/
theorem sum_pairSpin_sq_of_symm {Ψ : PairState} (h : pairSwap Ψ = Ψ) :
    ∑ k, pairSpin k (pairSpin k Ψ) = (8 : ℂ) • Ψ := by
  rw [sum_pairSpin_sq, h, ← two_smul ℂ Ψ, smul_smul]
  norm_num

theorem sum_pairSpin_sq_singlet : ∑ k, pairSpin k (pairSpin k singlet) = 0 := by
  rw [sum_pairSpin_sq, pairSwap_singlet, add_neg_cancel, smul_zero]

end Logic

end DstDiophantine
