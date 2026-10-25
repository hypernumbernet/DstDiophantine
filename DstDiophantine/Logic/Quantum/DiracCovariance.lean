import DstDiophantine.Logic.Quantum.DiracEquation
import DstDiophantine.Logic.Quantum.UsualRotor
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Covariance of the momentum-space Dirac equation under the total rotor

A total rotor is represented on the upper Weyl block by a `2×2` complex
matrix `M` of determinant `1`, and on the lower block by `(M†)⁻¹`, which is
`(adj M)†` at unit determinant. The four-momentum is carried by the
Hermitian matrix `p₀ I + p·σ`, whose determinant is `-Q(p)`. Conjugation
`X ↦ M X M†` preserves Hermiticity and determinant, so it defines a real
Lorentz action `Λ_M` on four-momenta.

The two Weyl blocks intertwine the slash at `p` with the slash at `Λ_M p`.
Every momentum-space Dirac solution of mass `m` at `p` is therefore sent to
a solution of the same mass at `Λ_M p`. The mass bilinear is invariant, and
the Clifford contraction of the current with a four-vector is invariant
when both are transformed.

The rest momentum is fixed by `Λ_M` exactly when `M` is unitary. Usual
rotors act on the lower block by their inverse, dual rotors act identically
on both blocks and fix the rest momentum.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

open scoped InnerProductSpace

/-! ### The momentum matrix -/

/-- Four-momentum read off a `2×2` Hermitian matrix `p₀ I + p·σ`. -/
noncomputable def hermVec (X : Matrix (Fin 2) (Fin 2) ℂ) : Vec4 :=
  ![((X 0 0).re + (X 1 1).re) / 2, (X 1 0).re, (X 1 0).im,
    ((X 0 0).re - (X 1 1).re) / 2]

theorem pauliSlash_entries (p : Vec4) :
    pauliSlash p =
      !![((p 0 + p 3 : ℝ) : ℂ), (p 1 : ℂ) - I * (p 2 : ℂ);
         (p 1 : ℂ) + I * (p 2 : ℂ), ((p 0 - p 3 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliSlash, pauliX, pauliY, pauliZ, Matrix.add_apply, Matrix.smul_apply] <;>
    ring

theorem hermVec_pauliSlash (p : Vec4) : hermVec (pauliSlash p) = p := by
  rw [pauliSlash_entries]
  ext μ
  fin_cases μ <;> simp [hermVec]

theorem pauliSlash_injective : Function.Injective pauliSlash := by
  intro p q h
  rw [← hermVec_pauliSlash p, ← hermVec_pauliSlash q, h]

theorem pauliSlash_hermVec {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) :
    pauliSlash (hermVec X) = X := by
  have h00 : star (X 0 0) = X 0 0 := by
    simpa using congrFun (congrFun hX 0) 0
  have h11 : star (X 1 1) = X 1 1 := by
    simpa using congrFun (congrFun hX 1) 1
  have h01 : star (X 1 0) = X 0 1 := by
    simpa using congrFun (congrFun hX 0) 1
  have h00im : (X 0 0).im = 0 := by
    have := congrArg Complex.im h00
    simp at this
    linarith
  have h11im : (X 1 1).im = 0 := by
    have := congrArg Complex.im h11
    simp at this
    linarith
  rw [pauliSlash_entries]
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [hermVec, h00im]
    ring
  · apply Complex.ext <;> simp [hermVec, ← h01]
  · apply Complex.ext <;> simp [hermVec]
  · apply Complex.ext <;> simp [hermVec, h11im]
    ring

theorem pauliSlash_hermitian (p : Vec4) : (pauliSlash p)ᴴ = pauliSlash p := by
  rw [pauliSlash_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  ring

/-- `det(p₀ I + p·σ) = -Q(p)`. -/
theorem pauliSlash_det (p : Vec4) :
    (pauliSlash p).det = -(minkowskiQ p : ℂ) := by
  rw [pauliSlash_entries, Matrix.det_fin_two_of, minkowskiQ_eq]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The chiral partner is minus the adjugate of the momentum matrix. -/
theorem pauliSlashBar_eq_neg_adjugate (p : Vec4) :
    pauliSlashBar p = -(pauliSlash p).adjugate := by
  rw [Matrix.adjugate_fin_two, pauliSlash_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliSlashBar, pauliX, pauliY, pauliZ, Matrix.add_apply, Matrix.smul_apply] <;>
    ring

/-! ### Lorentz action of a total rotor -/

/-- Lower-block partner `(adj M)†`, equal to `(M†)⁻¹` at unit determinant. -/
noncomputable def rotorLower (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  M.adjugateᴴ

/-- Four-momentum transformed by `X ↦ M X M†`. -/
noncomputable def lorentzAct (M : Matrix (Fin 2) (Fin 2) ℂ) (p : Vec4) : Vec4 :=
  hermVec (M * pauliSlash p * Mᴴ)

theorem pauliSlash_lorentzAct (M : Matrix (Fin 2) (Fin 2) ℂ) (p : Vec4) :
    pauliSlash (lorentzAct M p) = M * pauliSlash p * Mᴴ := by
  apply pauliSlash_hermVec
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    pauliSlash_hermitian, Matrix.mul_assoc]

/-- `pauliSlash` as a real linear map. -/
noncomputable def pauliSlashLM : Vec4 →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := pauliSlash
  map_add' := pauliSlash_add
  map_smul' r p := by
    rw [pauliSlash_smul, RingHom.id_apply, ← Complex.coe_smul]

/-- The Lorentz action of a total rotor is linear in the momentum. -/
theorem lorentzAct_eq_sum (M : Matrix (Fin 2) (Fin 2) ℂ) (p : Vec4) :
    lorentzAct M p = ∑ ν : Fin 4, p ν • lorentzAct M (Pi.single ν 1) := by
  apply pauliSlash_injective
  have hp : p = ∑ ν : Fin 4, p ν • (Pi.single ν 1 : Vec4) := by
    ext μ
    simp [Finset.sum_apply, Pi.single_apply]
  change pauliSlashLM (lorentzAct M p) =
    pauliSlashLM (∑ ν : Fin 4, p ν • lorentzAct M (Pi.single ν 1))
  rw [map_sum]
  simp only [map_smul]
  change pauliSlash (lorentzAct M p) = ∑ ν : Fin 4, p ν • pauliSlash (lorentzAct M _)
  simp only [pauliSlash_lorentzAct]
  conv_lhs => rw [hp]
  change M * pauliSlashLM (∑ ν : Fin 4, p ν • (Pi.single ν 1 : Vec4)) * Mᴴ = _
  rw [map_sum]
  simp only [map_smul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- A unit-determinant rotor preserves the Minkowski quadratic. -/
theorem minkowskiQ_lorentzAct {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) (p : Vec4) :
    minkowskiQ (lorentzAct M p) = minkowskiQ p := by
  have h := congrArg Matrix.det (pauliSlash_lorentzAct M p)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hM, pauliSlash_det,
    pauliSlash_det] at h
  simp only [star_one, one_mul, mul_one, neg_inj] at h
  exact_mod_cast h

private theorem conjTranspose_mul_rotorLower {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.det = 1) : Mᴴ * rotorLower M = 1 := by
  unfold rotorLower
  rw [← Matrix.conjTranspose_mul, Matrix.adjugate_mul, hM, one_smul,
    Matrix.conjTranspose_one]

private theorem rotorLower_conjTranspose_mul {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.det = 1) : (rotorLower M)ᴴ * M = 1 := by
  unfold rotorLower
  rw [Matrix.conjTranspose_conjTranspose, Matrix.adjugate_mul, hM, one_smul]

/-- Upper intertwiner: `slash(Λp)` on the lower block. -/
theorem pauliSlash_lorentzAct_intertwine {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1)
    (p : Vec4) :
    pauliSlash (lorentzAct M p) * rotorLower M = M * pauliSlash p := by
  rw [pauliSlash_lorentzAct, Matrix.mul_assoc, conjTranspose_mul_rotorLower hM,
    Matrix.mul_one]

/-- Lower intertwiner: the chiral partner on the upper block. -/
theorem pauliSlashBar_lorentzAct_intertwine {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1)
    (p : Vec4) :
    pauliSlashBar (lorentzAct M p) * M = rotorLower M * pauliSlashBar p := by
  rw [pauliSlashBar_eq_neg_adjugate, pauliSlashBar_eq_neg_adjugate, pauliSlash_lorentzAct,
    Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, ← Matrix.adjugate_conjTranspose]
  unfold rotorLower
  rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.adjugate_mul, hM, one_smul, Matrix.mul_one]

/-! ### Action on Dirac spinors -/

/-- Total rotor on `ℂ⁴`: `M` on the upper Weyl block, `(adj M)†` on the lower. -/
noncomputable def rotorDirac (M : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : DiracSpinor) : DiracSpinor :=
  weylUpper (applyMat M (diracUpper Ψ)) + weylLower (applyMat (rotorLower M) (diracLower Ψ))

/-- Matrix of the total rotor on `ℂ⁴`. -/
noncomputable def rotorDiracMat (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  blockDiag2 M (rotorLower M)

theorem rotorDirac_eq_mat (M : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : DiracSpinor) :
    rotorDirac M Ψ = applyDiracMat (rotorDiracMat M) Ψ := by
  ext i
  fin_cases i <;>
    simp [rotorDirac, applyDiracMat, rotorDiracMat, blockDiag2, weylUpper, weylLower,
      applyMat, diracUpper, diracLower, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_two]

theorem rotorDirac_weyl (M : Matrix (Fin 2) (Fin 2) ℂ) (u l : DualSpinor) :
    rotorDirac M (weylUpper u + weylLower l) =
      weylUpper (applyMat M u) + weylLower (applyMat (rotorLower M) l) := by
  unfold rotorDirac
  rw [diracUpper_add, diracLower_add, diracUpper_weylUpper, diracUpper_weylLower,
    diracLower_weylUpper, diracLower_weylLower, add_zero, zero_add]

theorem rotorDirac_smul (M : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (Ψ : DiracSpinor) :
    rotorDirac M (c • Ψ) = c • rotorDirac M Ψ := by
  nth_rw 1 [← weyl_decompose Ψ]
  rw [smul_add, ← weylUpper_smul, ← weylLower_smul, rotorDirac_weyl, applyMat_smul,
    applyMat_smul, weylUpper_smul, weylLower_smul, ← smul_add]
  rfl

/-- The total rotor intertwines the slash at `p` with the slash at `Λ_M p`. -/
theorem slash_rotorDirac {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) (p : Vec4)
    (Ψ : DiracSpinor) :
    applyDiracMat (slashMat (lorentzAct M p)) (rotorDirac M Ψ) =
      rotorDirac M (applyDiracMat (slashMat p) Ψ) := by
  rw [slash_weyl_decompose (lorentzAct M p), slash_weyl_decompose p, rotorDirac_weyl]
  unfold rotorDirac
  rw [diracUpper_add, diracLower_add, diracUpper_weylUpper, diracUpper_weylLower,
    diracLower_weylUpper, diracLower_weylLower, add_zero, zero_add,
    ← applyMat_mul, ← applyMat_mul, ← applyMat_mul, ← applyMat_mul,
    pauliSlash_lorentzAct_intertwine hM, pauliSlashBar_lorentzAct_intertwine hM]

/-- Covariance: a solution of mass `m` at `p` goes to a solution of mass `m`
at `Λ_M p`. -/
theorem diracMomentum_rotorDirac {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1)
    {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (h : DiracMomentum m p Ψ) :
    DiracMomentum m (lorentzAct M p) (rotorDirac M Ψ) := by
  unfold DiracMomentum at h ⊢
  rw [slash_rotorDirac hM, h, rotorDirac_smul]

/-- The mass bilinear is invariant under every unit-determinant total rotor. -/
theorem diracScalar_rotorDirac {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1)
    (Ψ Φ : DiracSpinor) :
    diracScalar (rotorDirac M Ψ) (rotorDirac M Φ) = diracScalar Ψ Φ := by
  rw [← weyl_decompose Ψ, ← weyl_decompose Φ, rotorDirac_weyl, rotorDirac_weyl,
    diracScalar_weyl, diracScalar_weyl, applyMat_inner_mul, applyMat_inner_mul,
    conjTranspose_mul_rotorLower hM, rotorLower_conjTranspose_mul hM, applyMat_one,
    applyMat_one]

/-! ### Current covariance -/

/-- Clifford contraction `∑ q_μ j^μ` of the Dirac current with a four-vector. -/
noncomputable def currentContract (q : Vec4) (Ψ Φ : DiracSpinor) : ℂ :=
  ∑ μ : Fin 4, (q μ : ℂ) * diracCurrent μ Ψ Φ

private theorem diracScalar_add_right (Ψ Φ Χ : DiracSpinor) :
    diracScalar Ψ (Φ + Χ) = diracScalar Ψ Φ + diracScalar Ψ Χ := by
  unfold diracScalar
  rw [applyDiracMat_add, inner_add_right]

private theorem diracScalar_smul_right (Ψ Φ : DiracSpinor) (c : ℂ) :
    diracScalar Ψ (c • Φ) = c * diracScalar Ψ Φ := by
  unfold diracScalar
  rw [applyDiracMat_smul, inner_smul_right]

theorem currentContract_eq (q : Vec4) (Ψ Φ : DiracSpinor) :
    currentContract q Ψ Φ = diracScalar Ψ (applyDiracMat (slashMat q) Φ) := by
  unfold currentContract
  simp only [diracCurrent_eq_scalar, slashMat, Fin.sum_univ_four, applyDiracMat_add_mat,
    applyDiracMat_smul_mat, diracScalar_add_right, diracScalar_smul_right]

/-- Current covariance: contracting the transformed current with the
transformed vector gives the original contraction. -/
theorem currentContract_rotorDirac {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1)
    (q : Vec4) (Ψ Φ : DiracSpinor) :
    currentContract (lorentzAct M q) (rotorDirac M Ψ) (rotorDirac M Φ) =
      currentContract q Ψ Φ := by
  rw [currentContract_eq, currentContract_eq, slash_rotorDirac hM,
    diracScalar_rotorDirac hM]

/-! ### Rest momentum and its stabilizer -/

theorem lorentzAct_rest (M : Matrix (Fin 2) (Fin 2) ℂ) (m : ℝ) :
    pauliSlash (lorentzAct M (restMomentum m)) = (m : ℂ) • (M * Mᴴ) := by
  rw [pauliSlash_lorentzAct, pauliSlash_rest, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul]

/-- A total rotor fixes the rest momentum exactly when it is unitary. -/
theorem lorentzAct_rest_iff {M : Matrix (Fin 2) (Fin 2) ℂ} {m : ℝ} (hm : m ≠ 0) :
    lorentzAct M (restMomentum m) = restMomentum m ↔ M * Mᴴ = 1 := by
  have hmC : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm
  constructor
  · intro h
    have h2 := congrArg pauliSlash h
    rw [lorentzAct_rest, pauliSlash_rest] at h2
    have h3 : (m : ℂ) • (M * Mᴴ) = (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := h2
    exact smul_right_injective _ hmC h3
  · intro h
    apply pauliSlash_injective
    rw [lorentzAct_rest, pauliSlash_rest, h]

/-- Dual rotors fix the rest momentum. -/
theorem lorentzAct_dualRotor_rest (β : DualRapidity) (m : ℝ) :
    lorentzAct (dualRotorMat β) (restMomentum m) = restMomentum m := by
  apply pauliSlash_injective
  rw [lorentzAct_rest, pauliSlash_rest,
    mul_eq_one_comm.mp (dualRotorMat_unitary β)]

/-- On a dual rotor the lower partner is the rotor itself. -/
theorem rotorLower_dualRotor (β : DualRapidity) :
    rotorLower (dualRotorMat β) = dualRotorMat β := by
  have hU := dualRotorMat_unitary β
  have hdet := dualRotorMat_det β
  have h1 : (dualRotorMat β)ᴴ * rotorLower (dualRotorMat β) = 1 :=
    conjTranspose_mul_rotorLower hdet
  calc rotorLower (dualRotorMat β)
      = (dualRotorMat β * (dualRotorMat β)ᴴ) * rotorLower (dualRotorMat β) := by
        rw [mul_eq_one_comm.mp hU, Matrix.one_mul]
    _ = dualRotorMat β := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

/-- On a usual rotor the lower partner is the inverse rotor. -/
theorem rotorLower_usualRotor (α : UsualRapidity) :
    rotorLower (usualRotorMat α) * usualRotorMat α = 1 := by
  have hH : (usualRotorMat α)ᴴ = usualRotorMat α := usualRotorMat_isHermitian α
  unfold rotorLower
  rw [Matrix.adjugate_conjTranspose, hH, Matrix.adjugate_mul, usualRotorMat_det, one_smul]

theorem lorentzAct_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) (p : Vec4) :
    lorentzAct (M * N) p = lorentzAct M (lorentzAct N p) := by
  apply pauliSlash_injective
  rw [pauliSlash_lorentzAct, pauliSlash_lorentzAct, pauliSlash_lorentzAct,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem pauliSlash_trace (p : Vec4) : (pauliSlash p).trace = 2 * (p 0 : ℂ) := by
  rw [pauliSlash_entries, Matrix.trace_fin_two]
  simp
  ring

/-! ### Positive square root and polar factorization -/

private theorem cayley_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;>
    ring

private theorem det_add_one_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (A + 1).det = A.det + A.trace + 1 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

private theorem trace_im_of_herm {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = A) :
    A.trace.im = 0 := by
  have h00 : star (A 0 0) = A 0 0 := by simpa using congrFun (congrFun hA 0) 0
  have h11 : star (A 1 1) = A 1 1 := by simpa using congrFun (congrFun hA 1) 1
  have i0 := congrArg Complex.im h00
  have i1 := congrArg Complex.im h11
  simp at i0 i1
  rw [Matrix.trace_fin_two, Complex.add_im]
  linarith

private theorem trace_eq_re_of_herm {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = A) :
    A.trace = (A.trace.re : ℂ) := by
  apply Complex.ext <;> simp [trace_im_of_herm hA]

/-- Positive square root `(A + 1)/√(tr A + 2)` of a unit-determinant
Hermitian `2×2` matrix. -/
noncomputable def posSqrt (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((Real.sqrt (A.trace.re + 2))⁻¹ : ℝ) : ℂ) • (A + 1)

section PosSqrt

variable {A : Matrix (Fin 2) (Fin 2) ℂ}

private theorem add_one_mul_self (hA : Aᴴ = A) (hdet : A.det = 1) :
    (A + 1) * (A + 1) = ((A.trace.re + 2 : ℝ) : ℂ) • A := by
  have hc := cayley_two A
  rw [hdet, trace_eq_re_of_herm hA] at hc
  have hexp : (A + 1) * (A + 1) = A * A + (2 : ℂ) • A + 1 := by
    rw [add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, two_smul]
    abel
  rw [hexp, hc]
  push_cast
  module

theorem posSqrt_mul_self (hA : Aᴴ = A) (hdet : A.det = 1) (htr : 0 < A.trace.re + 2) :
    posSqrt A * posSqrt A = A := by
  unfold posSqrt
  set s := Real.sqrt (A.trace.re + 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr htr
  have hs2 : s ^ 2 = A.trace.re + 2 := Real.sq_sqrt htr.le
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_one_mul_self hA hdet, smul_smul]
  have hcoef : ((s⁻¹ : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) * ((A.trace.re + 2 : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, ← ofReal_mul, ← hs2]
    have : s⁻¹ * s⁻¹ * s ^ 2 = 1 := by field_simp
    rw [this, ofReal_one]
  rw [hcoef, one_smul]

theorem posSqrt_hermitian (hA : Aᴴ = A) : (posSqrt A)ᴴ = posSqrt A := by
  unfold posSqrt
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hA,
    Complex.star_def, Complex.conj_ofReal]

theorem posSqrt_det (hA : Aᴴ = A) (hdet : A.det = 1) (htr : 0 < A.trace.re + 2) :
    (posSqrt A).det = 1 := by
  unfold posSqrt
  set s := Real.sqrt (A.trace.re + 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr htr
  have hs2 : s ^ 2 = A.trace.re + 2 := Real.sq_sqrt htr.le
  rw [Matrix.det_smul, det_add_one_two, hdet, trace_eq_re_of_herm hA]
  simp only [Fintype.card_fin]
  have : ((s⁻¹ : ℝ) : ℂ) ^ 2 * (1 + (A.trace.re : ℂ) + 1) =
      ((s⁻¹ ^ 2 * (A.trace.re + 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, ← hs2]
  have h1 : s⁻¹ ^ 2 * s ^ 2 = 1 := by field_simp
  rw [h1, ofReal_one]

theorem posSqrt_trace_pos (hA : Aᴴ = A) (htr : 0 < A.trace.re + 2) :
    0 < (posSqrt A).trace.re := by
  unfold posSqrt
  have htrace : A.trace = (A.trace.re : ℂ) := trace_eq_re_of_herm hA
  set t := A.trace.re with ht
  have hspos : 0 < Real.sqrt (t + 2) := Real.sqrt_pos.mpr htr
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, htrace]
  simp only [Fintype.card_fin, smul_eq_mul]
  have : (((Real.sqrt (t + 2))⁻¹ : ℝ) : ℂ) * ((t : ℂ) + ((2 : ℕ) : ℂ)) =
      (((Real.sqrt (t + 2))⁻¹ * (t + 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, ofReal_re]
  exact mul_pos (inv_pos.mpr hspos) htr

end PosSqrt

/-- A unit-determinant Hermitian matrix of positive trace is determined by
its square. -/
theorem herm_sqrt_unique {H₁ H₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (h₁ : H₁ᴴ = H₁) (h₂ : H₂ᴴ = H₂) (d₁ : H₁.det = 1) (d₂ : H₂.det = 1)
    (t₁ : 0 < H₁.trace.re) (t₂ : 0 < H₂.trace.re) (h : H₁ * H₁ = H₂ * H₂) :
    H₁ = H₂ := by
  obtain ⟨r₁, hr₁⟩ : ∃ r : ℝ, H₁.trace = r := ⟨_, trace_eq_re_of_herm h₁⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r : ℝ, H₂.trace = r := ⟨_, trace_eq_re_of_herm h₂⟩
  rw [hr₁, ofReal_re] at t₁
  rw [hr₂, ofReal_re] at t₂
  have c₁ := cayley_two H₁
  have c₂ := cayley_two H₂
  rw [d₁, hr₁, one_smul] at c₁
  rw [d₂, hr₂, one_smul] at c₂
  have htr₁ : (H₁ * H₁).trace = (r₁ : ℂ) * r₁ - 2 := by
    rw [c₁, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, hr₁]
    simp only [Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  have htr₂ : (H₂ * H₂).trace = (r₂ : ℂ) * r₂ - 2 := by
    rw [c₂, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, hr₂]
    simp only [Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  have hsq : r₁ * r₁ = r₂ * r₂ := by
    have hC : (r₁ : ℂ) * r₁ = r₂ * r₂ := by
      have := htr₁.symm.trans ((congrArg Matrix.trace h).trans htr₂)
      linear_combination this
    exact_mod_cast hC
  have hr : r₁ = r₂ := by nlinarith
  have hsm : (r₁ : ℂ) • H₁ = (r₁ : ℂ) • H₂ := by
    have e₁ : (r₁ : ℂ) • H₁ = H₁ * H₁ + 1 := by rw [c₁, sub_add_cancel]
    have e₂ : (r₂ : ℂ) • H₂ = H₂ * H₂ + 1 := by rw [c₂, sub_add_cancel]
    rw [e₁, h, ← e₂, hr]
  have hne : (r₁ : ℂ) ≠ 0 := ofReal_ne_zero.mpr t₁.ne'
  exact smul_right_injective _ hne hsm

private theorem mul_conjTranspose_herm (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (M * Mᴴ)ᴴ = M * Mᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

private theorem mul_conjTranspose_trace_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ (M * Mᴴ).trace.re := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Complex.add_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (M 0 0).re, sq_nonneg (M 0 0).im, sq_nonneg (M 0 1).re,
    sq_nonneg (M 0 1).im, sq_nonneg (M 1 0).re, sq_nonneg (M 1 0).im,
    sq_nonneg (M 1 1).re, sq_nonneg (M 1 1).im]

/-- Polar factorization: every unit-determinant `2×2` matrix is a positive
Hermitian factor of determinant `1` times a unitary factor of determinant `1`. -/
theorem polar_factor {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) :
    ∃ H U : Matrix (Fin 2) (Fin 2) ℂ,
      Hᴴ = H ∧ H.det = 1 ∧ 0 < H.trace.re ∧ U * Uᴴ = 1 ∧ U.det = 1 ∧ M = H * U := by
  set A := M * Mᴴ with hAdef
  have hA : Aᴴ = A := mul_conjTranspose_herm M
  have hdetA : A.det = 1 := by
    rw [hAdef, Matrix.det_mul, Matrix.det_conjTranspose, hM, star_one, mul_one]
  have htrA : 0 < A.trace.re + 2 := by
    have := mul_conjTranspose_trace_nonneg M
    linarith
  set H := posSqrt A
  have hH : Hᴴ = H := posSqrt_hermitian hA
  have hHdet : H.det = 1 := posSqrt_det hA hdetA htrA
  have hHH : H * H = A := posSqrt_mul_self hA hdetA htrA
  have hl : H.adjugate * H = 1 := by rw [Matrix.adjugate_mul, hHdet, one_smul]
  have hr : H * H.adjugate = 1 := by rw [Matrix.mul_adjugate, hHdet, one_smul]
  have hadj : H.adjugateᴴ = H.adjugate := by rw [Matrix.adjugate_conjTranspose, hH]
  refine ⟨H, H.adjugate * M, hH, hHdet, posSqrt_trace_pos hA htrA, ?_, ?_, ?_⟩
  · calc H.adjugate * M * (H.adjugate * M)ᴴ
        = H.adjugate * A * H.adjugateᴴ := by
          rw [Matrix.conjTranspose_mul, hAdef]
          simp only [Matrix.mul_assoc]
      _ = (H.adjugate * H) * (H * H.adjugate) := by
          rw [hadj, ← hHH]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hl, hr, Matrix.one_mul]
  · rw [Matrix.det_mul, Matrix.det_adjugate, hHdet, hM]
    simp
  · rw [← Matrix.mul_assoc, hr, Matrix.one_mul]

/-- The polar factors are unique. -/
theorem polar_unique {H₁ H₂ U₁ U₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (h₁ : H₁ᴴ = H₁) (h₂ : H₂ᴴ = H₂) (d₁ : H₁.det = 1) (d₂ : H₂.det = 1)
    (t₁ : 0 < H₁.trace.re) (t₂ : 0 < H₂.trace.re)
    (u₁ : U₁ * U₁ᴴ = 1) (u₂ : U₂ * U₂ᴴ = 1) (h : H₁ * U₁ = H₂ * U₂) :
    H₁ = H₂ ∧ U₁ = U₂ := by
  have hsq : H₁ * H₁ = H₂ * H₂ := by
    have e₁ : (H₁ * U₁) * (H₁ * U₁)ᴴ = H₁ * H₁ := by
      rw [Matrix.conjTranspose_mul, h₁, Matrix.mul_assoc, ← Matrix.mul_assoc U₁, u₁,
        Matrix.one_mul]
    have e₂ : (H₂ * U₂) * (H₂ * U₂)ᴴ = H₂ * H₂ := by
      rw [Matrix.conjTranspose_mul, h₂, Matrix.mul_assoc, ← Matrix.mul_assoc U₂, u₂,
        Matrix.one_mul]
    rw [← e₁, ← e₂, h]
  have hH := herm_sqrt_unique h₁ h₂ d₁ d₂ t₁ t₂ hsq
  refine ⟨hH, ?_⟩
  have hl : H₁.adjugate * H₁ = 1 := by rw [Matrix.adjugate_mul, d₁, one_smul]
  calc U₁ = H₁.adjugate * (H₁ * U₁) := by rw [← Matrix.mul_assoc, hl, Matrix.one_mul]
    _ = H₁.adjugate * (H₂ * U₂) := by rw [h]
    _ = U₂ := by rw [← hH, ← Matrix.mul_assoc, hl, Matrix.one_mul]

/-! ### Usual and dual rotors exhaust the polar factors -/

private theorem euclid_norm_scaled (w : Fin 3 → ℝ) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (hw : r ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) :
    ‖(WithLp.toLp 2 (fun i => a / r * w i) : EuclideanSpace ℝ (Fin 3))‖ = a := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
  have h : (a / r * w 0) ^ 2 + (a / r * w 1) ^ 2 + (a / r * w 2) ^ 2 = a ^ 2 := by
    have e : (a / r * w 0) ^ 2 + (a / r * w 1) ^ 2 + (a / r * w 2) ^ 2 =
        (a / r) ^ 2 * (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) := by ring
    rw [e, ← hw]
    field_simp
  rw [h, Real.sqrt_sq ha]

/-- Every positive Hermitian matrix of determinant `1` is a usual rotor. -/
theorem usualRotor_surj {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : Hᴴ = H) (hdet : H.det = 1)
    (htr : 0 < H.trace.re) : ∃ α : UsualRapidity, usualRotorMat α = H := by
  set v := hermVec H with hv
  have hHv : pauliSlash v = H := pauliSlash_hermVec hH
  have hQ : minkowskiQ v = -1 := by
    have h := pauliSlash_det v
    rw [hHv, hdet] at h
    have : ((minkowskiQ v : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast this
  have hv0 : 0 < v 0 := by
    have h := pauliSlash_trace v
    rw [hHv] at h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [minkowskiQ_eq] at hQ
  set r := Real.sqrt (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) with hr
  have hr2 : r ^ 2 = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := Real.sq_sqrt (by positivity)
  have hv0sq : v 0 = Real.sqrt (1 + r ^ 2) := by
    rw [hr2]
    have : 1 + (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) = v 0 ^ 2 := by linarith
    rw [this, Real.sqrt_sq hv0.le]
  rcases (Real.sqrt_nonneg (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2)).lt_or_eq with hrpos | hr0
  · set a := 2 * Real.arsinh r
    have hapos : 0 < a := by
      have : 0 < Real.arsinh r := Real.arsinh_pos_iff.mpr hrpos
      positivity
    set w : Fin 3 → ℝ := ![v 1, v 2, v 3]
    set α : UsualRapidity := WithLp.toLp 2 (fun i => a / r * w i)
    have hnorm : ‖α‖ = a :=
      euclid_norm_scaled w hrpos hapos.le (by simp [w, hr2])
    have hα0 : α ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnorm
      linarith
    refine ⟨α, ?_⟩
    rw [usualRotorMat_rodrigues]
    simp only [hα0, ↓reduceIte]
    rw [hnorm, ← hHv, pauliSlash_entries]
    have hc : Real.cosh (a / 2) = v 0 := by
      rw [show a / 2 = Real.arsinh r by ring, Real.cosh_arsinh, hv0sq]
    have hs : Real.sinh (a / 2) = r := by
      rw [show a / 2 = Real.arsinh r by ring, Real.sinh_arsinh]
    rw [hc, hs]
    have hane : a ≠ 0 := hapos.ne'
    have hrne : r ≠ 0 := hrpos.ne'
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [α, w, pauliComb, pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_three,
        Matrix.add_apply, Matrix.smul_apply] <;> field_simp
    ring
  · have hr00 : r = 0 := by rw [hr]; exact hr0.symm
    have hsum : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 0 := by
      rw [← hr2, hr00]
      ring
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
    have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
    have h3 : v 3 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
    have h0 : v 0 = 1 := by nlinarith
    refine ⟨0, ?_⟩
    rw [usualRotorMat_zero, ← hHv, pauliSlash_entries, h0, h1, h2, h3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private theorem unitary_conjTranspose_eq_adjugate {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U * Uᴴ = 1) (hdet : U.det = 1) : Uᴴ = U.adjugate := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  calc Uᴴ = Uᴴ * (U * U.adjugate) := by
        rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.mul_one]
    _ = U.adjugate := by rw [← Matrix.mul_assoc, hU', Matrix.one_mul]

/-- Every unitary matrix of determinant `1` is a dual rotor. -/
theorem dualRotor_surj {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U * Uᴴ = 1) (hdet : U.det = 1) :
    ∃ β : DualRapidity, dualRotorMat β = U := by
  have hadj := unitary_conjTranspose_eq_adjugate hU hdet
  rw [Matrix.adjugate_fin_two] at hadj
  have e11 : U 1 1 = star (U 0 0) := by
    simpa using (congrFun (congrFun hadj 0) 0).symm
  have e01 : U 0 1 = -star (U 1 0) := by
    have h : (starRingEnd ℂ) (U 1 0) = -U 0 1 := by
      simpa using congrFun (congrFun hadj 0) 1
    rw [Complex.star_def, h, neg_neg]
  set x0 := (U 0 0).re
  set x3 := -(U 0 0).im
  set x1 := -(U 1 0).im
  set x2 := (U 1 0).re
  have hnorm : x0 ^ 2 + (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) = 1 := by
    have h := hdet
    rw [Matrix.det_fin_two, e11, e01] at h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re] at hre
    simp only [x0, x1, x2, x3]
    nlinarith [hre]
  have hU_eq : U = !![(x0 : ℂ) - I * x3, -(x2 : ℂ) - I * x1;
      (x2 : ℂ) - I * x1, (x0 : ℂ) + I * x3] := by
    ext i j
    fin_cases i <;> fin_cases j
    · apply Complex.ext <;> simp [x0, x3]
    · apply Complex.ext <;> simp [e01, x1, x2]
    · apply Complex.ext <;> simp [x1, x2]
    · apply Complex.ext <;> simp [e11, x0, x3]
  set r := Real.sqrt (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) with hr
  have hr2 : r ^ 2 = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 := Real.sq_sqrt (by positivity)
  have hx0lo : -1 ≤ x0 := by nlinarith [sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]
  have hx0hi : x0 ≤ 1 := by nlinarith [sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]
  rcases (Real.sqrt_nonneg (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)).lt_or_eq with hrpos | hr0
  · set θ := 2 * Real.arccos x0
    have hsin : Real.sin (θ / 2) = r := by
      rw [show θ / 2 = Real.arccos x0 by ring, Real.sin_arccos, hr]
      congr 1
      linarith
    have hcos : Real.cos (θ / 2) = x0 := by
      rw [show θ / 2 = Real.arccos x0 by ring, Real.cos_arccos hx0lo hx0hi]
    have hθpos : 0 < θ := by
      have h0 : 0 ≤ Real.arccos x0 := Real.arccos_nonneg x0
      rcases h0.lt_or_eq with h | h
      · positivity
      · exfalso
        have : Real.sin (θ / 2) = 0 := by
          rw [show θ / 2 = Real.arccos x0 by ring, ← h, Real.sin_zero]
        rw [hsin] at this
        linarith
    set w : Fin 3 → ℝ := ![x1, x2, x3]
    set β : DualRapidity := WithLp.toLp 2 (fun i => θ / r * w i)
    have hnorm' : ‖β‖ = θ :=
      euclid_norm_scaled w hrpos hθpos.le (by simp [w, hr2])
    have hβ0 : β ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnorm'
      linarith
    refine ⟨β, ?_⟩
    rw [dualRotorMat_rodrigues]
    simp only [hβ0, ↓reduceIte]
    rw [hnorm', hcos, hsin, hU_eq]
    have hθne : θ ≠ 0 := hθpos.ne'
    have hrne : r ≠ 0 := hrpos.ne'
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [β, w, cyclicRepComb, cyclicRep, pauli, pauliX, pauliY, pauliZ,
        Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply] <;> field_simp
  · have hr00 : r = 0 := by rw [hr]; exact hr0.symm
    have hsum : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 0 := by
      rw [← hr2, hr00]
      ring
    have h1 : x1 = 0 := by nlinarith [sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]
    have h2 : x2 = 0 := by nlinarith [sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]
    have h3 : x3 = 0 := by nlinarith [sq_nonneg x1, sq_nonneg x2, sq_nonneg x3]
    have hx0sq : x0 ^ 2 = 1 := by nlinarith
    have hfac : (x0 - 1) * (x0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with hp | hn
    · have hp' : x0 = 1 := by linarith
      refine ⟨0, ?_⟩
      rw [dualRotorMat_zero, hU_eq, hp', h1, h2, h3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · have hn' : x0 = -1 := by linarith
      refine ⟨EuclideanSpace.single 0 (2 * Real.pi), ?_⟩
      rw [dualRotorMat_axis0_rodrigues, show 2 * Real.pi / 2 = Real.pi by ring,
        Real.cos_pi, Real.sin_pi, hU_eq, hn', h1, h2, h3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

/-- Total-rotor factorization: every unit-determinant matrix is a usual rotor
followed by a dual rotor. -/
theorem totalRotor_factor {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) :
    ∃ (α : UsualRapidity) (β : DualRapidity), M = usualRotorMat α * dualRotorMat β := by
  obtain ⟨H, U, hH, hHdet, hHtr, hU, hUdet, rfl⟩ := polar_factor hM
  obtain ⟨α, rfl⟩ := usualRotor_surj hH hHdet hHtr
  obtain ⟨β, rfl⟩ := dualRotor_surj hU hUdet
  exact ⟨α, β, rfl⟩

theorem usualRotorMat_trace_pos (α : UsualRapidity) : 0 < (usualRotorMat α).trace.re := by
  have hpos : 0 < Real.cosh (‖α‖ / 2) := Real.cosh_pos _
  have h2 : (((2 : ℕ) : ℂ)).re = 2 := by norm_num
  have key : (usualRotorMat α).trace = (Real.cosh (‖α‖ / 2) : ℂ) * ((2 : ℕ) : ℂ) := by
    rw [usualRotorMat_rodrigues]
    split_ifs <;>
      simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
        pauliComb_trace, smul_zero, add_zero, Fintype.card_fin, Complex.real_smul]
  rw [key, Complex.re_ofReal_mul, h2]
  positivity

/-- The usual and dual factors of a total rotor are unique. -/
theorem totalRotor_factor_unique {α₁ α₂ : UsualRapidity} {β₁ β₂ : DualRapidity}
    (h : usualRotorMat α₁ * dualRotorMat β₁ = usualRotorMat α₂ * dualRotorMat β₂) :
    usualRotorMat α₁ = usualRotorMat α₂ ∧ dualRotorMat β₁ = dualRotorMat β₂ :=
  polar_unique (usualRotorMat_isHermitian α₁) (usualRotorMat_isHermitian α₂)
    (usualRotorMat_det α₁) (usualRotorMat_det α₂)
    (usualRotorMat_trace_pos α₁) (usualRotorMat_trace_pos α₂)
    (mul_eq_one_comm.mp (dualRotorMat_unitary β₁))
    (mul_eq_one_comm.mp (dualRotorMat_unitary β₂)) h

/-- The stabilizer of the rest momentum is exactly the dual rotors. -/
theorem lorentzAct_rest_iff_dualRotor {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1)
    {m : ℝ} (hm : m ≠ 0) :
    lorentzAct M (restMomentum m) = restMomentum m ↔ ∃ β : DualRapidity, M = dualRotorMat β := by
  rw [lorentzAct_rest_iff hm]
  constructor
  · intro hU
    obtain ⟨β, hβ⟩ := dualRotor_surj hU hM
    exact ⟨β, hβ.symm⟩
  · rintro ⟨β, rfl⟩
    exact mul_eq_one_comm.mp (dualRotorMat_unitary β)

/-! ### Momentum is carried by the usual factor -/

/-- The dual factor does not move the rest momentum. -/
theorem lorentzAct_factor_rest (α : UsualRapidity) (β : DualRapidity) (m : ℝ) :
    lorentzAct (usualRotorMat α * dualRotorMat β) (restMomentum m) =
      lorentzAct (usualRotorMat α) (restMomentum m) := by
  rw [lorentzAct_mul, lorentzAct_dualRotor_rest]

/-- Every forward on-shell momentum is reached from rest by a usual rotor. -/
theorem exists_usualRotor_momentum {m : ℝ} (hm : 0 < m) {p : Vec4}
    (hQ : minkowskiQ p = -m ^ 2) (hp : 0 < p 0) :
    ∃ α : UsualRapidity, lorentzAct (usualRotorMat α) (restMomentum m) = p := by
  set A := ((m⁻¹ : ℝ) : ℂ) • pauliSlash p with hAdef
  have hA : Aᴴ = A := by
    rw [hAdef, Matrix.conjTranspose_smul, pauliSlash_hermitian, Complex.star_def,
      Complex.conj_ofReal]
  have hdetA : A.det = 1 := by
    have hmC : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
    rw [hAdef, Matrix.det_smul, pauliSlash_det, hQ]
    simp only [Fintype.card_fin]
    push_cast
    field_simp
  have htrA : 0 < A.trace.re + 2 := by
    rw [hAdef, Matrix.trace_smul, pauliSlash_trace]
    simp only [smul_eq_mul]
    have : (((m⁻¹ : ℝ) : ℂ) * (2 * (p 0 : ℂ))).re = m⁻¹ * (2 * p 0) := by
      rw [← ofReal_ofNat, ← ofReal_mul, ← ofReal_mul, ofReal_re]
    rw [this]
    have : 0 < m⁻¹ * (2 * p 0) := by positivity
    linarith
  set H := posSqrt A
  obtain ⟨α, hα⟩ := usualRotor_surj (posSqrt_hermitian hA) (posSqrt_det hA hdetA htrA)
    (posSqrt_trace_pos hA htrA)
  refine ⟨α, ?_⟩
  apply pauliSlash_injective
  rw [lorentzAct_rest, hα, posSqrt_hermitian hA, posSqrt_mul_self hA hdetA htrA, hAdef,
    smul_smul, ← ofReal_mul, mul_inv_cancel₀ hm.ne', ofReal_one, one_smul]

/-- The usual rotor that carries the rest momentum to a given momentum is unique. -/
theorem usualRotor_momentum_unique {m : ℝ} (hm : m ≠ 0) {α₁ α₂ : UsualRapidity}
    (h : lorentzAct (usualRotorMat α₁) (restMomentum m) =
      lorentzAct (usualRotorMat α₂) (restMomentum m)) :
    usualRotorMat α₁ = usualRotorMat α₂ := by
  have h2 := congrArg pauliSlash h
  rw [lorentzAct_rest, lorentzAct_rest, usualRotorMat_isHermitian α₁,
    usualRotorMat_isHermitian α₂] at h2
  have hmC : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm
  have hsq := smul_right_injective _ hmC h2
  exact herm_sqrt_unique (usualRotorMat_isHermitian α₁) (usualRotorMat_isHermitian α₂)
    (usualRotorMat_det α₁) (usualRotorMat_det α₂)
    (usualRotorMat_trace_pos α₁) (usualRotorMat_trace_pos α₂) hsq

/-! ### Non-collinear usual rotors leave a dual rotation -/

/-- Usual rotors along perpendicular axes do not commute. -/
theorem usualRotor_perp_not_comm {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    usualRotorMat (EuclideanSpace.single 0 a) * usualRotorMat (EuclideanSpace.single 2 b) ≠
      usualRotorMat (EuclideanSpace.single 2 b) * usualRotorMat (EuclideanSpace.single 0 a) := by
  have hsa : Real.sinh (a / 2) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    intro h0
    exact ha (by linarith)
  have hsb : Real.sinh (b / 2) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    intro h0
    exact hb (by linarith)
  rw [usualRotorMat_axis0_rodrigues, usualRotorMat_axis2_rodrigues]
  set ca := Real.cosh (a / 2)
  set sa := Real.sinh (a / 2)
  set cb := Real.cosh (b / 2)
  set sb := Real.sinh (b / 2)
  have hX : (ca • (1 : Matrix (Fin 2) (Fin 2) ℂ) + sa • pauli 0) =
      !![(ca : ℂ), (sa : ℂ); (sa : ℂ), (ca : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli, pauliX, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  have hZ : (cb • (1 : Matrix (Fin 2) (Fin 2) ℂ) + sb • pauli 2) =
      !![(cb : ℂ) + sb, 0; 0, (cb : ℂ) - sb] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli, pauliZ, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
        sub_eq_add_neg]
  rw [hX, hZ, Matrix.mul_fin_two, Matrix.mul_fin_two]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h01
  have hprod : ((sa * sb : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination (-1 / 2 : ℂ) * h01
  have hprod' : sa * sb = 0 := by exact_mod_cast hprod
  rcases mul_eq_zero.mp hprod' with h0 | h0
  · exact hsa h0
  · exact hsb h0

/-- Thomas–Wigner rotation: the product of usual rotors along perpendicular
axes is a usual rotor followed by a nontrivial dual rotor. -/
theorem usualRotor_perp_dual_factor {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (α : UsualRapidity) (β : DualRapidity)
    (h : usualRotorMat (EuclideanSpace.single 0 a) * usualRotorMat (EuclideanSpace.single 2 b) =
      usualRotorMat α * dualRotorMat β) :
    dualRotorMat β ≠ 1 := by
  intro hβ
  rw [hβ, Matrix.mul_one] at h
  apply usualRotor_perp_not_comm ha hb
  have hH := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_mul, usualRotorMat_isHermitian, usualRotorMat_isHermitian,
    usualRotorMat_isHermitian] at hH
  rw [h, ← hH]

/-! ### Axis of the Thomas–Wigner rotation -/

/-- Entrywise complex conjugate of a `2×2` matrix. -/
def matConj (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := M.map star

private theorem matConj_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    matConj (M * N) = matConj M * matConj N := by
  ext i j
  simp [matConj, Matrix.mul_apply, Fin.sum_univ_two]

private theorem matConj_conjTranspose (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (matConj M)ᴴ = matConj Mᴴ := by
  ext i j
  simp [matConj, Matrix.conjTranspose_apply]

private theorem matConj_one : matConj (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matConj]

private theorem matConj_det (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (matConj M).det = star M.det := by
  simp [matConj, Matrix.det_fin_two]

private theorem matConj_trace (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (matConj M).trace = star M.trace := by
  simp [matConj, Matrix.trace_fin_two]

/-- The unitary polar factor of a real matrix is real. -/
theorem polar_real {M H U : Matrix (Fin 2) (Fin 2) ℂ} (hM : matConj M = M)
    (hH : Hᴴ = H) (hHdet : H.det = 1) (hHtr : 0 < H.trace.re) (hU : U * Uᴴ = 1)
    (h : M = H * U) : matConj U = U := by
  refine (polar_unique (H₁ := matConj H) (H₂ := H) ?_ hH ?_ hHdet ?_ hHtr ?_ hU ?_).2
  · rw [matConj_conjTranspose, hH]
  · rw [matConj_det, hHdet, star_one]
  · rw [matConj_trace, Complex.star_def, Complex.conj_re]
    exact hHtr
  · rw [matConj_conjTranspose, ← matConj_mul, hU, matConj_one]
  · rw [← matConj_mul, ← h, hM]

/-- A real unitary matrix of determinant `1` is a dual rotor about axis `1`. -/
theorem real_unitary_axis1 {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U * Uᴴ = 1)
    (hdet : U.det = 1) (hr : matConj U = U) :
    ∃ φ : ℝ, U = dualRotorMat (EuclideanSpace.single 1 φ) := by
  have hadj := unitary_conjTranspose_eq_adjugate hU hdet
  rw [Matrix.adjugate_fin_two] at hadj
  have e11 : U 1 1 = star (U 0 0) := by
    simpa using (congrFun (congrFun hadj 0) 0).symm
  have e01 : U 0 1 = -star (U 1 0) := by
    have h : (starRingEnd ℂ) (U 1 0) = -U 0 1 := by
      simpa using congrFun (congrFun hadj 0) 1
    rw [Complex.star_def, h, neg_neg]
  have hreal : ∀ i j, (U i j).im = 0 := by
    intro i j
    have h := congrArg Complex.im (congrFun (congrFun hr i) j)
    simp [matConj] at h
    linarith
  set c := (U 0 0).re
  set s := (U 1 0).re
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have h := hdet
    rw [Matrix.det_fin_two, e11, e01] at h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re] at hre
    have h00 := hreal 0 0
    have h10 := hreal 1 0
    simp only [c, s]
    nlinarith [hre]
  have hU_eq : U = !![(c : ℂ), -(s : ℂ); (s : ℂ), (c : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j
    · apply Complex.ext <;> simp [c, hreal 0 0]
    · apply Complex.ext <;> simp [e01, s, hreal 1 0]
    · apply Complex.ext <;> simp [s, hreal 1 0]
    · apply Complex.ext <;> simp [e11, c, hreal 0 0]
  set z : ℂ := (c : ℂ) + (s : ℂ) * I
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_add_mul_I, hcs, Real.sqrt_one]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz
    exact zero_ne_one hz
  have hcos : Real.cos (Complex.arg z) = c := by
    rw [Complex.cos_arg hz0, hz, div_one]
    simp [z]
  have hsin : Real.sin (Complex.arg z) = s := by
    rw [Complex.sin_arg, hz, div_one]
    simp [z]
  refine ⟨2 * Complex.arg z, ?_⟩
  rw [dualRotorMat_axis1_rodrigues, show 2 * Complex.arg z / 2 = Complex.arg z by ring,
    hcos, hsin, hU_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicRep, pauli, pauliY, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]

private theorem matConj_real_comb (r s : ℝ) {k : Fin 3} (hk : k ≠ 1) :
    matConj (r • (1 : Matrix (Fin 2) (Fin 2) ℂ) + s • pauli k) =
      r • (1 : Matrix (Fin 2) (Fin 2) ℂ) + s • pauli k := by
  fin_cases k
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matConj, pauli, pauliX, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  · exact absurd rfl hk
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matConj, pauli, pauliZ, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]

/-- Thomas–Wigner rotation about the perpendicular axis: usual rotors along
axes `0` and `2` compose to a usual rotor followed by a nontrivial dual rotor
about axis `1`. -/
theorem usualRotor_perp_wigner {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ (α : UsualRapidity) (φ : ℝ),
      usualRotorMat (EuclideanSpace.single 0 a) * usualRotorMat (EuclideanSpace.single 2 b) =
        usualRotorMat α * dualRotorMat (EuclideanSpace.single 1 φ) ∧
      dualRotorMat (EuclideanSpace.single 1 φ) ≠ 1 := by
  set M := usualRotorMat (EuclideanSpace.single 0 a) *
    usualRotorMat (EuclideanSpace.single 2 b) with hMdef
  have hM : M.det = 1 := by
    rw [hMdef, Matrix.det_mul, usualRotorMat_det, usualRotorMat_det, mul_one]
  have hMr : matConj M = M := by
    rw [hMdef, matConj_mul, usualRotorMat_axis0_rodrigues, usualRotorMat_axis2_rodrigues,
      matConj_real_comb _ _ (by decide), matConj_real_comb _ _ (by decide)]
  obtain ⟨H, U, hH, hHdet, hHtr, hU, hUdet, hMHU⟩ := polar_factor hM
  have hUr := polar_real hMr hH hHdet hHtr hU hMHU
  obtain ⟨φ, rfl⟩ := real_unitary_axis1 hU hUdet hUr
  obtain ⟨α, rfl⟩ := usualRotor_surj hH hHdet hHtr
  exact ⟨α, φ, hMHU, usualRotor_perp_dual_factor ha hb _ _ hMHU⟩

end Logic

end DstDiophantine
