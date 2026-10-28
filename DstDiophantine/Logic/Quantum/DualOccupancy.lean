import DstDiophantine.Logic.Quantum.DualExchange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Occupancy of one dual-spinor ray

* `J` reverses the spin vector: `r(Ju) = -r(u)`.
* For `u ≠ 0` the orthogonal complement of the ray of `u` is the ray of `Ju`.
  Any third dual spinor orthogonal to both is zero.
* Two dual spinors on the ray of `u` carry the same spin vector. Their joint
  state is symmetric, and the total-spin square acts on it by `8`, the value
  on every symmetric state. The singlet, of total-spin square `0`, is the
  joint state of the ray with its reverse. A repeated ray of a nonzero dual
  spinor is not a scalar multiple of that singlet.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex Module Submodule

open scoped InnerProductSpace

theorem inner_self_ne_zero {u : DualSpinor} (hu : u ≠ 0) : inner ℂ u u ≠ 0 := by
  intro h
  rw [inner_self_eq_norm_sq_to_K] at h
  have : (‖u‖ : ℂ) = 0 := by
    simpa using (sq_eq_zero_iff.mp h)
  exact hu (norm_eq_zero.mp (by exact_mod_cast this))

theorem not_smul_quatJ {u : DualSpinor} (hu : u ≠ 0) (c : ℂ) : c • u ≠ quatJ u := by
  intro h
  have hinner : c * inner ℂ u u = 0 := by
    have h' := congrArg (fun w => inner ℂ u w) h
    rw [inner_smul_right, inner_self_quatJ] at h'
    exact h'
  rcases mul_eq_zero.mp hinner with hc | hn
  · rw [hc, zero_smul] at h
    have hnorm : ‖quatJ u‖ = 0 := by simp [h]
    rw [norm_quatJ] at hnorm
    exact hu (norm_eq_zero.mp hnorm)
  · exact inner_self_ne_zero hu hn

theorem linearIndependent_quatJ {u : DualSpinor} (hu : u ≠ 0) :
    LinearIndependent ℂ ![quatJ u, u] := by
  rw [linearIndependent_fin2]
  refine ⟨?_, not_smul_quatJ hu⟩
  simpa using hu

/-- A dual spinor and its quaternionic partner span the whole space. -/
theorem span_quatJ_eq_top {u : DualSpinor} (hu : u ≠ 0) :
    Submodule.span ℂ (Set.range ![quatJ u, u]) = ⊤ := by
  have hdim : finrank ℂ (Submodule.span ℂ (Set.range ![quatJ u, u])) = 2 := by
    rw [finrank_span_eq_card (linearIndependent_quatJ hu)]
    simp
  have htop : finrank ℂ (⊤ : Submodule ℂ DualSpinor) = 2 := by
    rw [finrank_top, dualSpinor_finrank]
  exact eq_of_le_of_finrank_eq le_top (hdim.trans htop.symm)

/-- The orthogonal complement of the ray of `u` is the ray of `Ju`. -/
theorem inner_eq_zero_iff_smul_quatJ {u : DualSpinor} (hu : u ≠ 0) (v : DualSpinor) :
    inner ℂ u v = 0 ↔ ∃ c : ℂ, v = c • quatJ u := by
  constructor
  · intro h
    have hv : v ∈ Submodule.span ℂ (Set.range ![quatJ u, u]) := by
      rw [span_quatJ_eq_top hu]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hv
    have hsum : v = c 0 • quatJ u + c 1 • u := by
      rw [← hc, Fin.sum_univ_two]
      simp
    have hinner : inner ℂ u v = c 1 * inner ℂ u u := by
      rw [hsum, inner_add_right, inner_smul_right, inner_smul_right, inner_self_quatJ,
        mul_zero, zero_add]
    rw [h] at hinner
    have ha : c 1 = 0 := (mul_eq_zero.mp hinner.symm).resolve_right (inner_self_ne_zero hu)
    refine ⟨c 0, ?_⟩
    rw [hsum, ha, zero_smul, add_zero]
  · rintro ⟨c, rfl⟩
    rw [inner_smul_right, inner_self_quatJ, mul_zero]

/-- No third dual spinor is orthogonal to both members of the pair `(u, Ju)`. -/
theorem eq_zero_of_orthogonal_pair {u v w : DualSpinor} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : inner ℂ u v = 0) (huw : inner ℂ u w = 0) (hvw : inner ℂ v w = 0) :
    w = 0 := by
  obtain ⟨c, hc⟩ := (inner_eq_zero_iff_smul_quatJ hu v).1 huv
  obtain ⟨d, hd⟩ := (inner_eq_zero_iff_smul_quatJ hu w).1 huw
  have hc0 : c ≠ 0 := by
    intro h0
    apply hv
    rw [hc, h0, zero_smul]
  have hinner : star c * d * inner ℂ (quatJ u) (quatJ u) = 0 := by
    have h := hvw
    rw [hc, hd, inner_smul_left, inner_smul_right] at h
    simpa [mul_assoc] using h
  rw [inner_quatJ_quatJ, inner_self_eq_norm_sq_to_K] at hinner
  have hn : (‖u‖ : ℂ) ^ 2 ≠ 0 := by
    intro h0
    exact inner_self_ne_zero hu (by rw [inner_self_eq_norm_sq_to_K]; exact h0)
  have hcd : star c * d = 0 := by
    have hmul := mul_eq_zero.mp hinner
    exact hmul.resolve_right hn
  have hd0 : d = 0 := by
    have hstar : star c ≠ 0 := by
      intro h
      exact hc0 (star_eq_zero.mp h)
    exact (mul_eq_zero.mp hcd).resolve_left hstar
  rw [hd, hd0, zero_smul]

private theorem pauli_eq_pauliComb (k : Fin 3) :
    pauliComb (fun j => if j = k then (1 : ℝ) else 0) = pauli k := by
  ext i j
  simp only [pauliComb, Fin.sum_univ_three]
  fin_cases k <;> simp

theorem applyMat_pauli_quatJ (k : Fin 3) (u : DualSpinor) :
    applyMat (pauli k) (quatJ u) = -quatJ (applyMat (pauli k) u) := by
  have h := quatJ_pauliComb (fun j => if j = k then (1 : ℝ) else 0) u
  rw [pauli_eq_pauliComb] at h
  exact neg_eq_iff_eq_neg.mp h.symm

/-- `⟨Ju, σ_k Ju⟩ = -⟨u, σ_k u⟩`. -/
theorem spinExp_quatJ_pauli (k : Fin 3) (u : DualSpinor) :
    spinExp (pauli k) (quatJ u) = -spinExp (pauli k) u := by
  have hJ : inner ℂ (quatJ u) (applyMat (pauli k) (quatJ u)) =
      -inner ℂ (applyMat (pauli k) u) u := by
    rw [applyMat_pauli_quatJ, inner_neg_right, inner_quatJ_quatJ]
  have hswap : inner ℂ (applyMat (pauli k) u) u =
      star (inner ℂ u (applyMat (pauli k) u)) :=
    (inner_conj_symm (applyMat (pauli k) u) u).symm
  have hreal : star (inner ℂ u (applyMat (pauli k) u)) =
      inner ℂ u (applyMat (pauli k) u) :=
    Complex.conj_eq_iff_im.mpr
      (by simpa [spinExp] using spinExp_im_of_hermitian (pauli_conjTranspose k) u)
  rw [spinExp, spinExp, hJ, hswap, hreal]

/-- The quaternionic partner reverses the spin vector. -/
theorem spinVec_quatJ (u : DualSpinor) : spinVec (quatJ u) = fun k => -spinVec u k := by
  funext k
  have h := spinExp_quatJ_pauli k u
  rw [spinVec, spinVec, h]
  simp

/-- The second particle of a product carries the spin vector of its own factor. -/
theorem rightSpinVec_tensor (u v : DualSpinor) :
    rightSpinVec (pairTensor u v) = fun k => ‖u‖ ^ 2 * spinVec v k := by
  funext k
  have hact : pairAct 1 (pauli k) (pairTensor u v) =
      pairTensor u (applyMat (pauli k) v) := by
    rw [pairAct_tensor, applyMat_one]
  have him : (inner ℂ v (applyMat (pauli k) v)).im = 0 :=
    spinExp_im_of_hermitian (pauli_conjTranspose k) v
  have hure : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    change ((‖u‖ : ℂ) ^ 2).re = ‖u‖ ^ 2
    simp [pow_two]
  have huim : (inner ℂ u u).im = 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    change ((‖u‖ : ℂ) ^ 2).im = 0
    simp [pow_two]
  rw [rightSpinVec, hact, pairInner_tensor, spinVec, spinExp, Complex.mul_re, him, hure, huim]
  ring

/-- Two dual spinors on one ray carry the same spin vector. -/
theorem spinVec_pair_parallel (u : DualSpinor) :
    leftSpinVec (pairTensor u u) = (fun k => ‖u‖ ^ 2 * spinVec u k) ∧
      rightSpinVec (pairTensor u u) = (fun k => ‖u‖ ^ 2 * spinVec u k) := by
  exact ⟨leftSpinVec_tensor u u, rightSpinVec_tensor u u⟩

/-- The joint state of a repeated ray is symmetric, so the total-spin square
acts on it by `8`. -/
theorem sum_pairSpin_sq_parallel (u : DualSpinor) :
    ∑ k, pairSpin k (pairSpin k (pairTensor u u)) = (8 : ℂ) • pairTensor u u :=
  sum_pairSpin_sq_of_symm (by rw [pairSwap_tensor])

theorem pairSwap_smul (c : ℂ) (Ψ : PairState) :
    pairSwap (c • Ψ) = c • pairSwap Ψ := by
  simp [pairSwap, Matrix.transpose_smul]

/-- The singlet line carries total-spin square zero. -/
theorem sum_pairSpin_sq_smul_singlet (c : ℂ) :
    ∑ k, pairSpin k (pairSpin k (c • singlet)) = 0 := by
  rw [sum_pairSpin_sq, pairSwap_smul, pairSwap_singlet, smul_neg, add_neg_cancel, smul_zero]

theorem pairTensor_self_ne_zero {u : DualSpinor} (hu : u ≠ 0) :
    pairTensor u u ≠ 0 := by
  intro h
  apply hu
  ext i
  have hii : u i * u i = 0 := by
    have := congr_fun (congr_fun h i) i
    simpa [pairTensor_apply] using this
  exact (mul_eq_zero.mp hii).elim id id

/-- A repeated ray of a nonzero dual spinor is not on the singlet line. -/
theorem repeated_ray_not_smul_singlet {u : DualSpinor} (hu : u ≠ 0) (c : ℂ) :
    pairTensor u u ≠ c • singlet := by
  intro h
  have hline : (8 : ℂ) • pairTensor u u = 0 := by
    rw [← sum_pairSpin_sq_parallel u, h]
    exact sum_pairSpin_sq_smul_singlet c
  have hzero : pairTensor u u = 0 := by
    ext i j
    have hentry := congr_fun (congr_fun hline i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hentry
    exact (mul_eq_zero.mp hentry).resolve_left (by norm_num)
  exact pairTensor_self_ne_zero hu hzero

end Logic

end DstDiophantine
