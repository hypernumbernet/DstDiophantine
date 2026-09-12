import DstDiophantine.Logic.Quantum.Spinor
import DstDiophantine.Logic.Quantum.DualSector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Usual-sector matrix rotor

The usual generators are represented by Pauli matrices \(\sigma_a\), which
square to \(+1\). The matrix rotor is therefore
\(V(\alpha)=\exp(\alpha\cdot\sigma/2)\). Each such matrix is Hermitian of
determinant \(1\), and is not unitary for a nonzero boost. Mixed usual/dual
exponentials are not identified with an \(\mathrm{SL}(2,\mathbb{C})\) product.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex NormedSpace

open scoped Matrix

noncomputable local instance :
    NormedRing (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.linftyOpNormedRing

noncomputable local instance :
    NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.linftyOpNormedAlgebra

noncomputable local instance :
    NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ (Matrix (Fin 2) (Fin 2) ℂ)

noncomputable local instance :
    NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Matrix (Fin 2) (Fin 2) ℂ)

/-- Usual rotor as a matrix: \(\exp(\sum(\alpha_a/2)\sigma_a)=\exp(\alpha\cdot\sigma/2)\). -/
noncomputable def usualRotorMat (α : UsualRapidity) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp (∑ a : Fin 3, (α a / 2 : ℂ) • pauli a)

/-- Generator of the usual rotor. -/
noncomputable def usualRotorGen (α : UsualRapidity) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ a : Fin 3, (α a / 2 : ℂ) • pauli a

theorem usualRotorMat_eq_exp_gen (α : UsualRapidity) :
    usualRotorMat α = NormedSpace.exp (usualRotorGen α) :=
  rfl

noncomputable def axis0UsualGen (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (θ / 2 : ℂ) • pauli 0

theorem usualRotorMat_axis0 (θ : ℝ) :
    usualRotorMat (EuclideanSpace.single 0 θ) = NormedSpace.exp (axis0UsualGen θ) := by
  unfold usualRotorMat axis0UsualGen
  congr 1
  simp [PiLp.single_apply, Fin.sum_univ_three]

theorem axis0UsualGen_eq_real_smul (θ : ℝ) :
    axis0UsualGen θ = (θ / 2 : ℝ) • pauli 0 := by
  unfold axis0UsualGen
  have h : (θ / 2 : ℂ) = ↑(θ / 2) := by simp [Complex.ofReal_div]
  rw [h]
  rfl

theorem pauli_isHermitian (a : Fin 3) : (pauli a).IsHermitian := by
  fin_cases a
  · exact pauliX_isHermitian
  · exact pauliY_isHermitian
  · exact pauliZ_isHermitian

theorem usualRotorGen_conjTranspose (α : UsualRapidity) :
    (usualRotorGen α).conjTranspose = usualRotorGen α := by
  unfold usualRotorGen
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hr : star (α a / 2 : ℂ) = (α a / 2 : ℂ) := by simp
  rw [Matrix.conjTranspose_smul, pauli_isHermitian a, hr]

/-- Usual rotor matrix is Hermitian. -/
theorem usualRotorMat_isHermitian (α : UsualRapidity) :
    (usualRotorMat α).IsHermitian := by
  rw [usualRotorMat_eq_exp_gen]
  change (NormedSpace.exp (usualRotorGen α)).conjTranspose =
    NormedSpace.exp (usualRotorGen α)
  rw [(Matrix.exp_conjTranspose (usualRotorGen α)).symm,
    usualRotorGen_conjTranspose]

private theorem hasDerivAt_exp_neg_smul_mat
    (x : Matrix (Fin 2) (Fin 2) ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => NormedSpace.exp ((-v) • x))
      (NormedSpace.exp ((-u) • x) * (-x)) u := by
  have h : HasDerivAt (fun v : ℝ => NormedSpace.exp (v • (-x)))
      (NormedSpace.exp (u • (-x)) * (-x)) u :=
    hasDerivAt_exp_smul_const (-x) u
  have hfun : (fun v : ℝ => NormedSpace.exp ((-v) • x)) =
      fun v : ℝ => NormedSpace.exp (v • (-x)) :=
    funext fun v => by rw [neg_smul, smul_neg]
  simpa [hfun, neg_smul, smul_neg] using h

private theorem exp_smul_mul_exp_neg_smul_mat
    (x : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    NormedSpace.exp (t • x) * NormedSpace.exp ((-t) • x) = 1 := by
  have hneg : (-t) • x = -(t • x) := neg_smul t x
  rw [hneg]
  have hc : Commute (t • x) (-(t • x)) := Commute.neg_right (Commute.refl _)
  have h := (NormedSpace.exp_add_of_commute hc).symm
  rw [add_neg_cancel, NormedSpace.exp_zero] at h
  exact h

/-- Hyperbolic closed form on `M₂(ℂ)`: `x² = 1 ⇒ exp(t • x) = cosh t + sinh t • x`. -/
theorem exp_mat_of_sq_one {x : Matrix (Fin 2) (Fin 2) ℂ}
    (hx : x * x = 1) (t : ℝ) :
    NormedSpace.exp (t • x) =
      Real.cosh t • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.sinh t • x := by
  let R : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun u => Real.cosh u • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.sinh u • x
  let f : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun u => NormedSpace.exp ((-u) • x) * R u
  have hRx (u : ℝ) : x * R u = Real.sinh u • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Real.cosh u • x := by
    simp only [R, mul_add]
    have h1 : x * (Real.cosh u • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = Real.cosh u • x := by
      rw [mul_smul_comm, mul_one]
    have h2 : x * (Real.sinh u • x) = Real.sinh u • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [mul_smul_comm, hx]
    rw [h1, h2, add_comm]
  have hR' (u : ℝ) :
      HasDerivAt R (Real.sinh u • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Real.cosh u • x) u :=
    ((Real.hasDerivAt_cosh u).smul_const (1 : Matrix (Fin 2) (Fin 2) ℂ)).add
      ((Real.hasDerivAt_sinh u).smul_const x)
  have hf' (u : ℝ) : HasDerivAt f 0 u := by
    have hexp := hasDerivAt_exp_neg_smul_mat x u
    have hmul :
        HasDerivAt ((fun v => NormedSpace.exp ((-v) • x)) * R)
          (NormedSpace.exp ((-u) • x) * (-x) * R u +
            NormedSpace.exp ((-u) • x) *
              (Real.sinh u • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.cosh u • x)) u :=
      hexp.mul (hR' u)
    have hzero :
        NormedSpace.exp ((-u) • x) * (-x) * R u +
          NormedSpace.exp ((-u) • x) *
            (Real.sinh u • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.cosh u • x) = 0 := by
      calc
        NormedSpace.exp ((-u) • x) * (-x) * R u +
              NormedSpace.exp ((-u) • x) *
                (Real.sinh u • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.cosh u • x)
            = NormedSpace.exp ((-u) • x) * ((-x) * R u) +
                NormedSpace.exp ((-u) • x) * (x * R u) := by
              rw [mul_assoc, hRx]
        _ = NormedSpace.exp ((-u) • x) * ((-x) * R u + x * R u) := by
              rw [← mul_add]
        _ = NormedSpace.exp ((-u) • x) * (-(x * R u) + x * R u) := by
              rw [neg_mul]
        _ = NormedSpace.exp ((-u) • x) * 0 := by
              rw [neg_add_cancel]
        _ = 0 := mul_zero _
    convert hmul using 2
    · rfl
    · exact hzero.symm
  have hf0 : f 0 = 1 := by
    simp only [f, R, neg_zero, zero_smul, NormedSpace.exp_zero, Real.cosh_zero,
      Real.sinh_zero, one_smul, zero_smul, add_zero, mul_one]
  have hdiff : Differentiable ℝ f := fun u => (hf' u).differentiableAt
  have hderiv : ∀ u, deriv f u = 0 := fun u => (hf' u).deriv
  have hf_one : ∀ u, f u = 1 := fun u =>
    (is_const_of_deriv_eq_zero hdiff hderiv u 0).trans hf0
  have : NormedSpace.exp ((-t) • x) * R t = 1 := hf_one t
  calc
    NormedSpace.exp (t • x) = NormedSpace.exp (t • x) * 1 := (mul_one _).symm
    _ = NormedSpace.exp (t • x) * (NormedSpace.exp ((-t) • x) * R t) := by rw [this]
    _ = (NormedSpace.exp (t • x) * NormedSpace.exp ((-t) • x)) * R t := by rw [mul_assoc]
    _ = 1 * R t := by rw [exp_smul_mul_exp_neg_smul_mat]
    _ = R t := one_mul _

/-- Axis-0 usual rotor: \(\cosh(\theta/2)\,I+\sinh(\theta/2)\,\sigma_x\). -/
theorem usualRotorMat_axis0_rodrigues (θ : ℝ) :
    usualRotorMat (EuclideanSpace.single 0 θ) =
      Real.cosh (θ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Real.sinh (θ / 2) • pauli 0 := by
  rw [usualRotorMat_axis0, axis0UsualGen_eq_real_smul]
  exact exp_mat_of_sq_one (pauli_sq 0) (θ / 2)

private theorem usualRotorMat_axis0_entries (θ : ℝ) :
    usualRotorMat (EuclideanSpace.single 0 θ) =
      !![↑(Real.cosh (θ / 2)), ↑(Real.sinh (θ / 2));
         ↑(Real.sinh (θ / 2)), ↑(Real.cosh (θ / 2))] := by
  rw [usualRotorMat_axis0_rodrigues]
  unfold pauli pauliX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply]

/-- Axis-0 usual rotor has determinant `1`. -/
theorem usualRotorMat_axis0_det (θ : ℝ) :
    (usualRotorMat (EuclideanSpace.single 0 θ)).det = 1 := by
  rw [usualRotorMat_axis0_entries, Matrix.det_fin_two]
  have h : (Real.cosh (θ / 2)) ^ 2 - (Real.sinh (θ / 2)) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (θ / 2)
  have hC : (↑(Real.cosh (θ / 2)) : ℂ) * ↑(Real.cosh (θ / 2)) -
      ↑(Real.sinh (θ / 2)) * ↑(Real.sinh (θ / 2)) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    rw [← pow_two, ← pow_two, h]
    simp
  exact hC

/-- A nonzero usual boost is not unitary. -/
theorem usualRotorMat_axis0_not_unitary :
    (usualRotorMat (EuclideanSpace.single 0 (2 : ℝ))).conjTranspose *
      usualRotorMat (EuclideanSpace.single 0 (2 : ℝ)) ≠ 1 := by
  intro h
  have hHerm : (usualRotorMat (EuclideanSpace.single 0 (2 : ℝ))).conjTranspose =
      usualRotorMat (EuclideanSpace.single 0 (2 : ℝ)) :=
    usualRotorMat_isHermitian _
  have hM := usualRotorMat_axis0_entries (2 : ℝ)
  have h01 : ((usualRotorMat (EuclideanSpace.single 0 (2 : ℝ))).conjTranspose *
      usualRotorMat (EuclideanSpace.single 0 (2 : ℝ))) 0 1 = 0 := by
    rw [h]; simp
  have hentry :
      ((usualRotorMat (EuclideanSpace.single 0 (2 : ℝ))).conjTranspose *
        usualRotorMat (EuclideanSpace.single 0 (2 : ℝ))) 0 1 =
        (↑(Real.cosh 1) : ℂ) * ↑(Real.sinh 1) +
          ↑(Real.sinh 1) * ↑(Real.cosh 1) := by
    rw [hHerm, hM]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hs : Real.sinh (1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by norm_num : (0 : ℝ) < 1))
  have hc : Real.cosh (1 : ℝ) ≠ 0 := ne_of_gt (Real.cosh_pos 1)
  have h2cs : (↑(Real.cosh 1) : ℂ) * ↑(Real.sinh 1) +
      ↑(Real.sinh 1) * ↑(Real.cosh 1) ≠ 0 := by
    intro hz
    have hz' : (2 : ℂ) * (↑(Real.cosh 1) : ℂ) * ↑(Real.sinh 1) = 0 := by
      convert hz using 1; ring
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    rw [mul_eq_zero] at hz'
    rcases hz' with hL | hS
    · rw [mul_eq_zero] at hL
      rcases hL with h2' | hC
      · exact h2 h2'
      · exact hc (Complex.ofReal_eq_zero.mp hC)
    · exact hs (Complex.ofReal_eq_zero.mp hS)
  exact h2cs (hentry ▸ h01)

/-- Pauli combination \(\vec n\cdot\vec\sigma\). -/
noncomputable def pauliComb (n : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ a : Fin 3, (n a : ℂ) • pauli a

private theorem usualRapidity_norm_sq (α : UsualRapidity) :
    ‖α‖ ^ 2 = (α 0) ^ 2 + (α 1) ^ 2 + (α 2) ^ 2 := by
  have h1 := (real_inner_self_eq_norm_sq (F := UsualRapidity) α).symm
  have h2 : inner ℝ α α = (α 0) ^ 2 + (α 1) ^ 2 + (α 2) ^ 2 := by
    simp [inner, Fin.sum_univ_three, sq]
  exact h1.trans h2

private theorem usualRotorGen_of_unit {α : UsualRapidity} (h : α ≠ 0) :
    usualRotorGen α =
      (‖α‖ / 2 : ℝ) • pauliComb (fun a => α a / ‖α‖) := by
  have hr : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr h
  unfold usualRotorGen pauliComb
  simp only [Fin.sum_univ_three, smul_add]
  have hterm (v : ℝ) (G : Matrix (Fin 2) (Fin 2) ℂ) :
      (v / 2 : ℂ) • G = (‖α‖ / 2 : ℝ) • ((v / ‖α‖ : ℂ) • G) := by
    ext i j
    simp [Matrix.smul_apply]
    field_simp [hr]
  have hcast (v : ℝ) : (v / ‖α‖ : ℂ) = ((v / ‖α‖ : ℝ) : ℂ) := by
    simp [Complex.ofReal_div]
  rw [hterm (α 0), hterm (α 1), hterm (α 2), hcast (α 0), hcast (α 1), hcast (α 2)]

private theorem pauliComb_unit_sq {α : UsualRapidity} (h : α ≠ 0) :
    pauliComb (fun a => α a / ‖α‖) * pauliComb (fun a => α a / ‖α‖) = 1 := by
  have hr : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hn : ((α 0 / ‖α‖) ^ 2 + (α 1 / ‖α‖) ^ 2 + (α 2 / ‖α‖) ^ 2 : ℝ) = 1 := by
    have hdiv :
        (α 0 / ‖α‖) ^ 2 + (α 1 / ‖α‖) ^ 2 + (α 2 / ‖α‖) ^ 2 =
          ((α 0) ^ 2 + (α 1) ^ 2 + (α 2) ^ 2) / ‖α‖ ^ 2 := by
      field_simp [hr]
    rw [hdiv, ← usualRapidity_norm_sq, div_self (pow_ne_zero 2 hr)]
  have hsq := pauli_dot_sq (fun a => α a / ‖α‖)
  have hnC : ((α 0 / ‖α‖) ^ 2 + (α 1 / ‖α‖) ^ 2 + (α 2 / ‖α‖) ^ 2 : ℂ) = 1 :=
    mod_cast hn
  simpa [pauliComb, hnC, one_smul] using hsq

/-- Usual rotor matrix is the hyperbolic Rodrigues formula along \(\alpha\). -/
theorem usualRotorMat_rodrigues (α : UsualRapidity) :
    usualRotorMat α =
      Real.cosh (‖α‖ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (if h : α = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ)
          else Real.sinh (‖α‖ / 2) • pauliComb (fun a => α a / ‖α‖)) := by
  by_cases h : α = 0
  · subst h
    simp [usualRotorMat, Real.cosh_zero]
  · rw [usualRotorMat_eq_exp_gen, usualRotorGen_of_unit h]
    simp only [h, ↓reduceDIte]
    exact exp_mat_of_sq_one (pauliComb_unit_sq h) (‖α‖ / 2)

/-- Three-axis usual rotor has determinant `1`. -/
theorem usualRotorMat_det (α : UsualRapidity) :
    (usualRotorMat α).det = 1 := by
  by_cases hr : α = 0
  · subst hr
    have hgen : usualRotorGen 0 = 0 := by
      unfold usualRotorGen
      simp
    rw [usualRotorMat_eq_exp_gen, hgen, NormedSpace.exp_zero, Matrix.det_one]
  · set r := ‖(α : EuclideanSpace ℝ (Fin 3))‖
    have hrpos : 0 < r := norm_pos_iff.mpr hr
    set n : Fin 3 → ℝ := fun a => α a / r
    have hn : (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 = 1 := by
      have hnorm : r ^ 2 = (α 0) ^ 2 + (α 1) ^ 2 + (α 2) ^ 2 := usualRapidity_norm_sq α
      have hr0 : r ≠ 0 := hrpos.ne'
      unfold n
      have hdiv :
          (α 0 / r) ^ 2 + (α 1 / r) ^ 2 + (α 2 / r) ^ 2 =
            ((α 0) ^ 2 + (α 1) ^ 2 + (α 2) ^ 2) / r ^ 2 := by
        field_simp [hr0]
      rw [hdiv, ← hnorm, div_self (pow_ne_zero 2 hr0)]
    rw [usualRotorMat_rodrigues]
    simp only [hr, ↓reduceDIte]
    set U := pauliComb (fun a => α a / ‖α‖)
    have hUsq : U * U = 1 := pauliComb_unit_sq hr
    set c := Real.cosh (‖α‖ / 2)
    set s := Real.sinh (‖α‖ / 2)
    have hRℂ (t : ℝ) (m : Matrix (Fin 2) (Fin 2) ℂ) :
        t • m = (t : ℂ) • m := (algebraMap_smul ℂ t m).symm
    rw [hRℂ c, hRℂ s]
    have h11 : U 1 1 = -U 0 0 := by
      have hU :
          U = (n 0 : ℂ) • pauli 0 + (n 1 : ℂ) • pauli 1 + (n 2 : ℂ) • pauli 2 := by
        simp [U, n, pauliComb, Fin.sum_univ_three, r]
      have h0 : pauli 0 0 0 = 0 ∧ pauli 0 1 1 = 0 := by
        unfold pauli pauliX; simp
      have h1 : pauli 1 0 0 = 0 ∧ pauli 1 1 1 = 0 := by
        unfold pauli pauliY; simp
      have h2 : pauli 2 0 0 = 1 ∧ pauli 2 1 1 = -1 := by
        unfold pauli pauliZ; simp
      simp [hU, Matrix.add_apply, Matrix.smul_apply, h0, h1, h2]
    have hUU00 : (U * U) 0 0 = U 0 0 * U 0 0 + U 0 1 * U 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hpq : U 0 0 * U 0 0 + U 0 1 * U 1 0 = 1 := by
      have : (U * U) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [hUsq]
      simpa [Matrix.one_apply] using hUU00.symm.trans this
    have hcs : (c : ℂ) * c - (s : ℂ) * s = 1 := by
      have h : c ^ 2 - s ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq (‖α‖ / 2)
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
      rw [← pow_two, ← pow_two, h]
      simp
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    rw [h11]
    calc ((c : ℂ) * 1 + s * U 0 0) * ((c : ℂ) * 1 + s * (-U 0 0)) -
          ((c : ℂ) * 0 + s * U 0 1) * ((c : ℂ) * 0 + s * U 1 0)
        = ((c : ℂ) + s * U 0 0) * (c + -(s * U 0 0)) - (s * U 0 1) * (s * U 1 0) := by
          simp
        _ = ((c : ℂ) + s * U 0 0) * (c - s * U 0 0) - s * s * (U 0 1 * U 1 0) := by
          rw [sub_eq_add_neg]; ring
        _ = c * c - s * s * (U 0 0 * U 0 0 + U 0 1 * U 1 0) := by ring
        _ = c * c - s * s * 1 := by rw [hpq]
        _ = c * c - s * s := by ring
        _ = 1 := hcs

end Logic

end DstDiophantine
