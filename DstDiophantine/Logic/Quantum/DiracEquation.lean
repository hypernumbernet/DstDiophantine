import DstDiophantine.Logic.Quantum.DiracSpinor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

/-!
# Momentum-space Dirac equation from the Clifford square

The Minkowski quadratic is already a square in `Cl(3,1)`:
`γ(p)² = Q(p)`. On the Dirac module `ℂ⁴` the same identity is
`slash(p)² = Q(p) I`. A spinor eigenvector `slash(p) Ψ = i m Ψ`
therefore sits on the mass shell `Q(p) = -m²`.

This is the first-order factor of Klein–Gordon. It is not a PDE on
spacetime, not a derivation of `m` from torsion, and not covariance
under the full rotor group.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex Cl31

/-! ### Minkowski quadratic and the Clifford slash -/

/-- Minkowski quadratic `Q(p) = -p₀² + p₁² + p₂² + p₃²`. -/
def minkowskiQ (p : Vec4) : ℝ :=
  ∑ μ : Fin 4, minkowskiEta μ μ * p μ * p μ

theorem minkowskiQ_eq (p : Vec4) :
    minkowskiQ p = -(p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 + (p 3) ^ 2 := by
  simp [minkowskiQ, minkowskiEta, w31, Fin.sum_univ_four, sq]

/-- Rest-frame four-momentum `(m, 0, 0, 0)`. -/
def restMomentum (m : ℝ) : Vec4 :=
  Pi.single 0 m

theorem minkowskiQ_rest (m : ℝ) : minkowskiQ (restMomentum m) = -m ^ 2 := by
  simp [minkowskiQ_eq, restMomentum, Pi.single_eq_same, Pi.single_eq_of_ne]

/-- Algebraic slash `γ(p) = ∑ p_μ γ^μ` in `Cl(3,1)`. -/
noncomputable def slashCl (p : Vec4) : Cl31 :=
  ∑ μ : Fin 4, p μ • diracGamma μ

private theorem smul_mul_smul_cl (c d : ℝ) (u v : Cl31) :
    (c • u) * (d • v) = (c * d) • (u * v) := by
  rw [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm d c]

private theorem smul_algebraMap_cl (r s : ℝ) :
    r • algebraMap ℝ Cl31 s = algebraMap ℝ Cl31 (r * s) := by
  rw [Algebra.algebraMap_eq_smul_one, smul_smul, ← Algebra.algebraMap_eq_smul_one]

private theorem slashCl_expand (p : Vec4) :
    slashCl p =
      p 0 • diracGamma 0 + p 1 • diracGamma 1 +
        p 2 • diracGamma 2 + p 3 • diracGamma 3 := by
  simp [slashCl, Fin.sum_univ_four]

private theorem slashCl_sq_expand (p : Vec4) :
    slashCl p * slashCl p =
      (p 0 * p 0) • (diracGamma 0 * diracGamma 0) +
        (p 1 * p 1) • (diracGamma 1 * diracGamma 1) +
          (p 2 * p 2) • (diracGamma 2 * diracGamma 2) +
            (p 3 * p 3) • (diracGamma 3 * diracGamma 3) +
              (p 0 * p 1) • (diracGamma 0 * diracGamma 1) +
                (p 1 * p 0) • (diracGamma 1 * diracGamma 0) +
                  (p 0 * p 2) • (diracGamma 0 * diracGamma 2) +
                    (p 2 * p 0) • (diracGamma 2 * diracGamma 0) +
                      (p 0 * p 3) • (diracGamma 0 * diracGamma 3) +
                        (p 3 * p 0) • (diracGamma 3 * diracGamma 0) +
                          (p 1 * p 2) • (diracGamma 1 * diracGamma 2) +
                            (p 2 * p 1) • (diracGamma 2 * diracGamma 1) +
                              (p 1 * p 3) • (diracGamma 1 * diracGamma 3) +
                                (p 3 * p 1) • (diracGamma 3 * diracGamma 1) +
                                  (p 2 * p 3) • (diracGamma 2 * diracGamma 3) +
                                    (p 3 * p 2) • (diracGamma 3 * diracGamma 2) := by
  simp only [slashCl_expand, mul_add, add_mul, smul_mul_smul_cl]
  abel

private theorem slashCl_cross {μ ν : Fin 4} (h : μ ≠ ν) (p : Vec4) :
    (p μ * p ν) • (diracGamma μ * diracGamma ν) +
      (p ν * p μ) • (diracGamma ν * diracGamma μ) = 0 := by
  have hη : minkowskiEta μ ν = 0 := minkowskiEta_off h
  have hcliff := diracGamma_clifford μ ν
  have hcomm : p ν * p μ = p μ * p ν := mul_comm _ _
  have : diracGamma μ * diracGamma ν + diracGamma ν * diracGamma μ = 0 := by
    simpa [hη, map_zero] using hcliff
  have hswap : diracGamma ν * diracGamma μ = -(diracGamma μ * diracGamma ν) :=
    eq_neg_of_add_eq_zero_right this
  rw [hswap, smul_neg, hcomm]
  abel

private theorem slashCl_diag (p : Vec4) :
    (p 0 * p 0) • (diracGamma 0 * diracGamma 0) +
      (p 1 * p 1) • (diracGamma 1 * diracGamma 1) +
        (p 2 * p 2) • (diracGamma 2 * diracGamma 2) +
          (p 3 * p 3) • (diracGamma 3 * diracGamma 3) =
      algebraMap ℝ Cl31 (minkowskiQ p) := by
  simp only [diracGamma_sq, smul_algebraMap_cl]
  simp only [minkowskiQ, minkowskiEta_diag, Fin.sum_univ_four, w31, sq]
  simp [map_add, map_neg, map_mul]

/-- `γ(p)² = Q(p)` in `Cl(3,1)`. -/
theorem slashCl_sq (p : Vec4) :
    slashCl p * slashCl p = algebraMap ℝ Cl31 (minkowskiQ p) := by
  have h01 := slashCl_cross (by decide : (0 : Fin 4) ≠ 1) p
  have h02 := slashCl_cross (by decide : (0 : Fin 4) ≠ 2) p
  have h03 := slashCl_cross (by decide : (0 : Fin 4) ≠ 3) p
  have h12 := slashCl_cross (by decide : (1 : Fin 4) ≠ 2) p
  have h13 := slashCl_cross (by decide : (1 : Fin 4) ≠ 3) p
  have h23 := slashCl_cross (by decide : (2 : Fin 4) ≠ 3) p
  have hdiag := slashCl_diag p
  have hsum' :
      slashCl p * slashCl p =
        ((p 0 * p 0) • (diracGamma 0 * diracGamma 0) +
          (p 1 * p 1) • (diracGamma 1 * diracGamma 1) +
          (p 2 * p 2) • (diracGamma 2 * diracGamma 2) +
          (p 3 * p 3) • (diracGamma 3 * diracGamma 3)) +
        ((p 0 * p 1) • (diracGamma 0 * diracGamma 1) +
          (p 1 * p 0) • (diracGamma 1 * diracGamma 0)) +
        ((p 0 * p 2) • (diracGamma 0 * diracGamma 2) +
          (p 2 * p 0) • (diracGamma 2 * diracGamma 0)) +
        ((p 0 * p 3) • (diracGamma 0 * diracGamma 3) +
          (p 3 * p 0) • (diracGamma 3 * diracGamma 0)) +
        ((p 1 * p 2) • (diracGamma 1 * diracGamma 2) +
          (p 2 * p 1) • (diracGamma 2 * diracGamma 1)) +
        ((p 1 * p 3) • (diracGamma 1 * diracGamma 3) +
          (p 3 * p 1) • (diracGamma 3 * diracGamma 1)) +
        ((p 2 * p 3) • (diracGamma 2 * diracGamma 3) +
          (p 3 * p 2) • (diracGamma 3 * diracGamma 2)) := by
    rw [slashCl_sq_expand]
    abel
  rw [hsum', h01, h02, h03, h12, h13, h23]
  simp only [add_zero]
  exact hdiag

/-! ### Matrix slash on `ℂ⁴` -/

/-- Matrix slash `∑ p_μ γ^μ`. -/
def slashMat (p : Vec4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ μ : Fin 4, (p μ : ℂ) • diracMat μ

private theorem smul_mul_smul_mat (c d : ℂ) (u v : Matrix (Fin 4) (Fin 4) ℂ) :
    (c • u) * (d • v) = (c * d) • (u * v) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem slashMat_expand (p : Vec4) :
    slashMat p =
      (p 0 : ℂ) • diracMat0 + (p 1 : ℂ) • diracMat1 +
        (p 2 : ℂ) • diracMat2 + (p 3 : ℂ) • diracMat3 := by
  simp [slashMat, diracMat, Fin.sum_univ_four]

private theorem slashMat_sq_expand (p : Vec4) :
    slashMat p * slashMat p =
      ((p 0 : ℂ) * p 0) • (diracMat0 * diracMat0) +
        ((p 1 : ℂ) * p 1) • (diracMat1 * diracMat1) +
          ((p 2 : ℂ) * p 2) • (diracMat2 * diracMat2) +
            ((p 3 : ℂ) * p 3) • (diracMat3 * diracMat3) +
              ((p 0 : ℂ) * p 1) • (diracMat0 * diracMat1) +
                ((p 1 : ℂ) * p 0) • (diracMat1 * diracMat0) +
                  ((p 0 : ℂ) * p 2) • (diracMat0 * diracMat2) +
                    ((p 2 : ℂ) * p 0) • (diracMat2 * diracMat0) +
                      ((p 0 : ℂ) * p 3) • (diracMat0 * diracMat3) +
                        ((p 3 : ℂ) * p 0) • (diracMat3 * diracMat0) +
                          ((p 1 : ℂ) * p 2) • (diracMat1 * diracMat2) +
                            ((p 2 : ℂ) * p 1) • (diracMat2 * diracMat1) +
                              ((p 1 : ℂ) * p 3) • (diracMat1 * diracMat3) +
                                ((p 3 : ℂ) * p 1) • (diracMat3 * diracMat1) +
                                  ((p 2 : ℂ) * p 3) • (diracMat2 * diracMat3) +
                                    ((p 3 : ℂ) * p 2) • (diracMat3 * diracMat2) := by
  simp only [slashMat_expand, mul_add, add_mul, smul_mul_smul_mat]
  abel

private theorem slashMat_cross {μ ν : Fin 4} (hμν : μ ≠ ν)
    (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : diracMat μ = A) (hB : diracMat ν = B) (p : Vec4) :
    ((p μ : ℂ) * p ν) • (A * B) + ((p ν : ℂ) * p μ) • (B * A) = 0 := by
  have hcliff : diracMat μ * diracMat ν + diracMat ν * diracMat μ = 0 := by
    simpa [minkowskiEta_off hμν] using diracMat_clifford μ ν
  rw [hA, hB] at hcliff
  have hswap : B * A = -(A * B) := eq_neg_of_add_eq_zero_right hcliff
  have hcomm : (p ν : ℂ) * p μ = (p μ : ℂ) * p ν := by ring
  rw [hswap, smul_neg, hcomm]
  abel

private theorem slashMat_diag (p : Vec4) :
    ((p 0 : ℂ) * p 0) • (diracMat0 * diracMat0) +
      ((p 1 : ℂ) * p 1) • (diracMat1 * diracMat1) +
        ((p 2 : ℂ) * p 2) • (diracMat2 * diracMat2) +
          ((p 3 : ℂ) * p 3) • (diracMat3 * diracMat3) =
      (minkowskiQ p : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [diracMat0_sq, diracMat1_sq, diracMat2_sq, diracMat3_sq, minkowskiQ_eq]
  simp [smul_neg, add_smul, sq]

/-- Matrix Clifford square `slash(p)² = Q(p) I`. -/
theorem slashMat_sq (p : Vec4) :
    slashMat p * slashMat p = (minkowskiQ p : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h01 := slashMat_cross (by decide : (0 : Fin 4) ≠ 1) diracMat0 diracMat1
    (by simp [diracMat]) (by simp [diracMat]) p
  have h02 := slashMat_cross (by decide : (0 : Fin 4) ≠ 2) diracMat0 diracMat2
    (by simp [diracMat]) (by simp [diracMat]) p
  have h03 := slashMat_cross (by decide : (0 : Fin 4) ≠ 3) diracMat0 diracMat3
    (by simp [diracMat]) (by simp [diracMat]) p
  have h12 := slashMat_cross (by decide : (1 : Fin 4) ≠ 2) diracMat1 diracMat2
    (by simp [diracMat]) (by simp [diracMat]) p
  have h13 := slashMat_cross (by decide : (1 : Fin 4) ≠ 3) diracMat1 diracMat3
    (by simp [diracMat]) (by simp [diracMat]) p
  have h23 := slashMat_cross (by decide : (2 : Fin 4) ≠ 3) diracMat2 diracMat3
    (by simp [diracMat]) (by simp [diracMat]) p
  have hdiag := slashMat_diag p
  have hsum' :
      slashMat p * slashMat p =
        (((p 0 : ℂ) * p 0) • (diracMat0 * diracMat0) +
          ((p 1 : ℂ) * p 1) • (diracMat1 * diracMat1) +
          ((p 2 : ℂ) * p 2) • (diracMat2 * diracMat2) +
          ((p 3 : ℂ) * p 3) • (diracMat3 * diracMat3)) +
        (((p 0 : ℂ) * p 1) • (diracMat0 * diracMat1) +
          ((p 1 : ℂ) * p 0) • (diracMat1 * diracMat0)) +
        (((p 0 : ℂ) * p 2) • (diracMat0 * diracMat2) +
          ((p 2 : ℂ) * p 0) • (diracMat2 * diracMat0)) +
        (((p 0 : ℂ) * p 3) • (diracMat0 * diracMat3) +
          ((p 3 : ℂ) * p 0) • (diracMat3 * diracMat0)) +
        (((p 1 : ℂ) * p 2) • (diracMat1 * diracMat2) +
          ((p 2 : ℂ) * p 1) • (diracMat2 * diracMat1)) +
        (((p 1 : ℂ) * p 3) • (diracMat1 * diracMat3) +
          ((p 3 : ℂ) * p 1) • (diracMat3 * diracMat1)) +
        (((p 2 : ℂ) * p 3) • (diracMat2 * diracMat3) +
          ((p 3 : ℂ) * p 2) • (diracMat3 * diracMat2)) := by
    rw [slashMat_sq_expand]
    abel
  rw [hsum', h01, h02, h03, h12, h13, h23]
  simp only [add_zero]
  exact hdiag

/-- First-order factorization of the Klein–Gordon symbol. -/
theorem slashMat_factor (p : Vec4) (m : ℝ) :
    (slashMat p - (I * (m : ℂ)) • 1) * (slashMat p + (I * (m : ℂ)) • 1) =
      slashMat p * slashMat p + ((m : ℂ) ^ 2) • 1 := by
  set cI : ℂ := I * (m : ℂ)
  have hcI : cI * cI = -((m : ℂ) ^ 2) := by
    simp only [cI]
    rw [mul_mul_mul_comm]
    simp [I_mul_I]
    ring
  have hL (A : Matrix (Fin 4) (Fin 4) ℂ) :
      (cI • (1 : Matrix (Fin 4) (Fin 4) ℂ)) * A = cI • A := by
    simp [Matrix.smul_mul, Matrix.one_mul]
  have hR (A : Matrix (Fin 4) (Fin 4) ℂ) :
      A * (cI • (1 : Matrix (Fin 4) (Fin 4) ℂ)) = cI • A := by
    simp [Matrix.mul_smul, Matrix.mul_one]
  have hsq : (cI • (1 : Matrix (Fin 4) (Fin 4) ℂ)) * (cI • 1) = (cI * cI) • 1 := by
    simp [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  calc (slashMat p - cI • 1) * (slashMat p + cI • 1)
      = slashMat p * slashMat p + slashMat p * (cI • 1) -
          (cI • 1) * slashMat p - (cI • 1) * (cI • 1) := by
        simp [sub_eq_add_neg, mul_add, add_mul, neg_mul]
    _ = slashMat p * slashMat p + cI • slashMat p - cI • slashMat p -
          (cI * cI) • 1 := by
        rw [hR, hL, hsq]
    _ = slashMat p * slashMat p - (cI * cI) • 1 := by
        simp
    _ = slashMat p * slashMat p + ((m : ℂ) ^ 2) • 1 := by
        rw [hcI, sub_eq_add_neg, neg_smul, neg_neg]

/-! ### Linearity of the Dirac action -/

theorem applyDiracMat_add (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ Φ : DiracSpinor) :
    applyDiracMat M (Ψ + Φ) = applyDiracMat M Ψ + applyDiracMat M Φ := by
  simp [applyDiracMat, Matrix.mulVec_add]

theorem applyDiracMat_smul (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat M (c • Ψ) = c • applyDiracMat M Ψ := by
  simp [applyDiracMat, Matrix.mulVec_smul]

theorem applyDiracMat_smul_mat (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (c • M) Ψ = c • applyDiracMat M Ψ := by
  simp [applyDiracMat, Matrix.smul_mulVec]

theorem applyDiracMat_add_mat (A B : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (A + B) Ψ = applyDiracMat A Ψ + applyDiracMat B Ψ := by
  simp [applyDiracMat, Matrix.add_mulVec]

theorem applyDiracMat_neg (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (-M) Ψ = -applyDiracMat M Ψ := by
  simpa using applyDiracMat_smul_mat (-1) M Ψ

theorem applyDiracMat_mul (A B : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (A * B) Ψ = applyDiracMat A (applyDiracMat B Ψ) := by
  simp [applyDiracMat, Matrix.mulVec_mulVec]

theorem applyDiracMat_one (Ψ : DiracSpinor) :
    applyDiracMat (1 : Matrix (Fin 4) (Fin 4) ℂ) Ψ = Ψ := by
  simp [applyDiracMat, Matrix.one_mulVec]

theorem applyDiracMat_smul_one (c : ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) Ψ = c • Ψ := by
  rw [applyDiracMat_smul_mat, applyDiracMat_one]

/-! ### Momentum-space Dirac equation -/

/-- Momentum-space Dirac equation `(γ^μ p_μ - i m) Ψ = 0`. -/
def DiracMomentum (m : ℝ) (p : Vec4) (Ψ : DiracSpinor) : Prop :=
  applyDiracMat (slashMat p) Ψ = (I * (m : ℂ)) • Ψ

/-- A nonzero Dirac eigenspinor lies on the mass shell `Q(p) = -m²`. -/
theorem diracMomentum_implies_mass_shell {m : ℝ} {p : Vec4} {Ψ : DiracSpinor}
    (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) :
    minkowskiQ p = -m ^ 2 := by
  have hI : I * (m : ℂ) * (I * (m : ℂ)) = -((m : ℂ) ^ 2) := by
    rw [mul_mul_mul_comm]
    simp [I_mul_I]
    ring
  have hsq :
      applyDiracMat (slashMat p * slashMat p) Ψ = -((m : ℂ) ^ 2) • Ψ := by
    rw [applyDiracMat_mul, h, applyDiracMat_smul, h, smul_smul, hI]
  rw [slashMat_sq, applyDiracMat_smul_one] at hsq
  have hsub : ((minkowskiQ p : ℂ) + (m : ℂ) ^ 2) • Ψ = 0 := by
    rw [add_smul, hsq]
    simp [neg_smul]
  have hc : (minkowskiQ p : ℂ) + (m : ℂ) ^ 2 = 0 :=
    (smul_eq_zero.mp hsub).resolve_right hΨ
  have hR : minkowskiQ p + m ^ 2 = 0 := by
    rw [← ofReal_inj (z := minkowskiQ p + m ^ 2) (w := 0)]
    simpa [ofReal_add, ofReal_pow] using hc
  linarith

/-! ### Weyl blocks of the slash -/

/-- Spatial Pauli combination plus the time component: `p₀ I + p · σ`. -/
def pauliSlash (p : Vec4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (p 0 : ℂ) • 1 + (p 1 : ℂ) • pauliX + (p 2 : ℂ) • pauliY + (p 3 : ℂ) • pauliZ

/-- Chiral partner `-p₀ I + p · σ`. -/
def pauliSlashBar (p : Vec4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-(p 0 : ℂ)) • 1 + (p 1 : ℂ) • pauliX + (p 2 : ℂ) • pauliY + (p 3 : ℂ) • pauliZ

def diracUpper (Ψ : DiracSpinor) : DualSpinor :=
  WithLp.toLp 2 ![WithLp.ofLp Ψ 0, WithLp.ofLp Ψ 1]

def diracLower (Ψ : DiracSpinor) : DualSpinor :=
  WithLp.toLp 2 ![WithLp.ofLp Ψ 2, WithLp.ofLp Ψ 3]

theorem weyl_decompose' (Ψ : DiracSpinor) :
    weylUpper (diracUpper Ψ) + weylLower (diracLower Ψ) = Ψ :=
  weyl_decompose Ψ

theorem weylUpper_add (ψ φ : DualSpinor) :
    weylUpper (ψ + φ) = weylUpper ψ + weylUpper φ := by
  ext i; fin_cases i <;> simp [weylUpper, PiLp.add_apply]

theorem weylLower_add (ψ φ : DualSpinor) :
    weylLower (ψ + φ) = weylLower ψ + weylLower φ := by
  ext i; fin_cases i <;> simp [weylLower, PiLp.add_apply]

theorem weylUpper_smul (c : ℂ) (ψ : DualSpinor) :
    weylUpper (c • ψ) = c • weylUpper ψ := by
  ext i; fin_cases i <;> simp [weylUpper, PiLp.smul_apply]

theorem weylLower_smul (c : ℂ) (ψ : DualSpinor) :
    weylLower (c • ψ) = c • weylLower ψ := by
  ext i; fin_cases i <;> simp [weylLower, PiLp.smul_apply]

theorem weylUpper_neg (ψ : DualSpinor) :
    weylUpper (-ψ) = -weylUpper ψ := by
  simpa using weylUpper_smul (-1) ψ

theorem weylLower_neg (ψ : DualSpinor) :
    weylLower (-ψ) = -weylLower ψ := by
  simpa using weylLower_smul (-1) ψ

theorem weylUpper_zero : weylUpper (0 : DualSpinor) = 0 := by
  simpa using weylUpper_smul 0 (0 : DualSpinor)

theorem weylLower_zero : weylLower (0 : DualSpinor) = 0 := by
  simpa using weylLower_smul 0 (0 : DualSpinor)

theorem weyl_pair_injective {u l u' l' : DualSpinor}
    (h : weylUpper u + weylLower l = weylUpper u' + weylLower l') :
    u = u' ∧ l = l' := by
  have hvec :
      WithLp.toLp 2 ![WithLp.ofLp u 0, WithLp.ofLp u 1,
        WithLp.ofLp l 0, WithLp.ofLp l 1] =
      WithLp.toLp 2 ![WithLp.ofLp u' 0, WithLp.ofLp u' 1,
        WithLp.ofLp l' 0, WithLp.ofLp l' 1] := by
    simpa [weylUpper_add_lower] using h
  have hf := WithLp.toLp_injective (p := 2) hvec
  constructor
  · ext i
    fin_cases i
    · simpa using congrFun hf 0
    · simpa using congrFun hf 1
  · ext i
    fin_cases i
    · simpa using congrFun hf 2
    · simpa using congrFun hf 3

private theorem apply_diracMat0_weylUpper (ψ : DualSpinor) :
    applyDiracMat diracMat0 (weylUpper ψ) = weylLower (-ψ) := by
  ext i
  fin_cases i <;>
    simp [applyDiracMat, weylUpper, weylLower, diracMat0, Matrix.mulVec,
      Fin.sum_univ_four, PiLp.neg_apply, vecHead, vecTail]

private theorem apply_diracMat1_weylUpper (ψ : DualSpinor) :
    applyDiracMat diracMat1 (weylUpper ψ) = weylLower (applyMat pauliX ψ) := by
  ext i
  fin_cases i <;>
    simp [applyDiracMat, applyMat, weylUpper, weylLower, diracMat1, pauliX,
      Matrix.mulVec, Fin.sum_univ_four, Fin.sum_univ_two, vecHead, vecTail]

private theorem apply_diracMat2_weylUpper (ψ : DualSpinor) :
    applyDiracMat diracMat2 (weylUpper ψ) = weylLower (applyMat pauliY ψ) := by
  ext i
  fin_cases i <;>
    (simp [applyDiracMat, applyMat, weylUpper, weylLower, diracMat2, pauliY,
      Matrix.mulVec, Fin.sum_univ_four, Fin.sum_univ_two, vecHead, vecTail] <;>
      ring)

private theorem apply_diracMat3_weylUpper (ψ : DualSpinor) :
    applyDiracMat diracMat3 (weylUpper ψ) = weylLower (applyMat pauliZ ψ) := by
  ext i
  fin_cases i <;>
    simp [applyDiracMat, applyMat, weylUpper, weylLower, diracMat3, pauliZ,
      Matrix.mulVec, Fin.sum_univ_four, Fin.sum_univ_two, vecHead, vecTail]

private theorem apply_diracMat0_weylLower (ψ : DualSpinor) :
    applyDiracMat diracMat0 (weylLower ψ) = weylUpper ψ := by
  ext i
  fin_cases i <;>
    simp [applyDiracMat, weylUpper, weylLower, diracMat0, Matrix.mulVec,
      Fin.sum_univ_four, vecHead, vecTail]

private theorem apply_diracMat1_weylLower (ψ : DualSpinor) :
    applyDiracMat diracMat1 (weylLower ψ) = weylUpper (applyMat pauliX ψ) := by
  ext i
  fin_cases i <;>
    simp [applyDiracMat, applyMat, weylUpper, weylLower, diracMat1, pauliX,
      Matrix.mulVec, Fin.sum_univ_four, Fin.sum_univ_two, vecHead, vecTail]

private theorem apply_diracMat2_weylLower (ψ : DualSpinor) :
    applyDiracMat diracMat2 (weylLower ψ) = weylUpper (applyMat pauliY ψ) := by
  ext i
  fin_cases i <;>
    (simp [applyDiracMat, applyMat, weylUpper, weylLower, diracMat2, pauliY,
      Matrix.mulVec, Fin.sum_univ_four, Fin.sum_univ_two, vecHead, vecTail] <;>
      ring)

private theorem apply_diracMat3_weylLower (ψ : DualSpinor) :
    applyDiracMat diracMat3 (weylLower ψ) = weylUpper (applyMat pauliZ ψ) := by
  ext i
  fin_cases i <;>
    simp [applyDiracMat, applyMat, weylUpper, weylLower, diracMat3, pauliZ,
      Matrix.mulVec, Fin.sum_univ_four, Fin.sum_univ_two, vecHead, vecTail]

theorem applyMat_add (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ φ : DualSpinor) :
    applyMat M (ψ + φ) = applyMat M ψ + applyMat M φ := by
  simp [applyMat, Matrix.mulVec_add]

theorem applyMat_smul (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor) :
    applyMat M (c • ψ) = c • applyMat M ψ := by
  simp [applyMat, Matrix.mulVec_smul]

theorem applyMat_add_mat (A B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor) :
    applyMat (A + B) ψ = applyMat A ψ + applyMat B ψ := by
  simp [applyMat, Matrix.add_mulVec]

theorem applyMat_smul_mat (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor) :
    applyMat (c • M) ψ = c • applyMat M ψ := by
  simp [applyMat, Matrix.smul_mulVec]

theorem applyMat_one (ψ : DualSpinor) :
    applyMat (1 : Matrix (Fin 2) (Fin 2) ℂ) ψ = ψ := by
  simp [applyMat, Matrix.one_mulVec]

private theorem apply_pauliSlashBar_eq (p : Vec4) (ψ : DualSpinor) :
    applyMat (pauliSlashBar p) ψ =
      (-(p 0 : ℂ)) • ψ + (p 1 : ℂ) • applyMat pauliX ψ +
        (p 2 : ℂ) • applyMat pauliY ψ + (p 3 : ℂ) • applyMat pauliZ ψ := by
  simp only [pauliSlashBar, applyMat_add_mat, applyMat_smul_mat, applyMat_one]

private theorem apply_pauliSlash_eq (p : Vec4) (ψ : DualSpinor) :
    applyMat (pauliSlash p) ψ =
      (p 0 : ℂ) • ψ + (p 1 : ℂ) • applyMat pauliX ψ +
        (p 2 : ℂ) • applyMat pauliY ψ + (p 3 : ℂ) • applyMat pauliZ ψ := by
  simp only [pauliSlash, applyMat_add_mat, applyMat_smul_mat, applyMat_one]

/-- Slash sends the upper Weyl block into the lower block. -/
theorem slash_weylUpper (p : Vec4) (ψ : DualSpinor) :
    applyDiracMat (slashMat p) (weylUpper ψ) =
      weylLower (applyMat (pauliSlashBar p) ψ) := by
  have hL :
      applyDiracMat (slashMat p) (weylUpper ψ) =
        (p 0 : ℂ) • weylLower (-ψ) +
          (p 1 : ℂ) • weylLower (applyMat pauliX ψ) +
            (p 2 : ℂ) • weylLower (applyMat pauliY ψ) +
              (p 3 : ℂ) • weylLower (applyMat pauliZ ψ) := by
    rw [slashMat_expand]
    simp only [applyDiracMat_add_mat, applyDiracMat_smul_mat,
      apply_diracMat0_weylUpper, apply_diracMat1_weylUpper,
      apply_diracMat2_weylUpper, apply_diracMat3_weylUpper]
  have h0 : (p 0 : ℂ) • weylLower (-ψ) = weylLower ((-(p 0 : ℂ)) • ψ) := by
    rw [weylLower_neg, smul_neg, ← weylLower_smul, ← weylLower_neg, neg_smul]
  rw [hL, apply_pauliSlashBar_eq, h0]
  simp only [weylLower_add, weylLower_smul]

/-- Slash sends the lower Weyl block into the upper block. -/
theorem slash_weylLower (p : Vec4) (ψ : DualSpinor) :
    applyDiracMat (slashMat p) (weylLower ψ) =
      weylUpper (applyMat (pauliSlash p) ψ) := by
  rw [slashMat_expand]
  simp only [applyDiracMat_add_mat, applyDiracMat_smul_mat,
    apply_diracMat0_weylLower, apply_diracMat1_weylLower,
    apply_diracMat2_weylLower, apply_diracMat3_weylLower]
  rw [apply_pauliSlash_eq]
  simp only [weylUpper_add, weylUpper_smul]

theorem slash_weyl_decompose (p : Vec4) (Ψ : DiracSpinor) :
    applyDiracMat (slashMat p) Ψ =
      weylUpper (applyMat (pauliSlash p) (diracLower Ψ)) +
        weylLower (applyMat (pauliSlashBar p) (diracUpper Ψ)) := by
  nth_rw 1 [← weyl_decompose' Ψ]
  rw [applyDiracMat_add, slash_weylUpper, slash_weylLower]
  abel

/-- Massless Dirac decouples into two independent Weyl equations. -/
theorem dirac_massless_decouple {p : Vec4} {Ψ : DiracSpinor}
    (h : DiracMomentum 0 p Ψ) :
    applyMat (pauliSlash p) (diracLower Ψ) = 0 ∧
      applyMat (pauliSlashBar p) (diracUpper Ψ) = 0 := by
  have h0 : applyDiracMat (slashMat p) Ψ = 0 := by
    simpa [DiracMomentum] using h
  have heq :
      weylUpper (applyMat (pauliSlash p) (diracLower Ψ)) +
        weylLower (applyMat (pauliSlashBar p) (diracUpper Ψ)) =
      weylUpper 0 + weylLower 0 := by
    rw [← slash_weyl_decompose, h0, weylUpper_zero, weylLower_zero, add_zero]
  exact weyl_pair_injective heq

/-- A mass term mixes the two Weyl blocks. -/
theorem dirac_massive_mix {m : ℝ} {p : Vec4} {Ψ : DiracSpinor}
    (h : DiracMomentum m p Ψ) :
    applyMat (pauliSlash p) (diracLower Ψ) = (I * (m : ℂ)) • diracUpper Ψ ∧
      applyMat (pauliSlashBar p) (diracUpper Ψ) = (I * (m : ℂ)) • diracLower Ψ := by
  have hrhs :
      (I * (m : ℂ)) • Ψ =
        weylUpper ((I * (m : ℂ)) • diracUpper Ψ) +
          weylLower ((I * (m : ℂ)) • diracLower Ψ) := by
    nth_rw 1 [← weyl_decompose' Ψ]
    rw [smul_add, weylUpper_smul, weylLower_smul]
  have heq :
      weylUpper (applyMat (pauliSlash p) (diracLower Ψ)) +
          weylLower (applyMat (pauliSlashBar p) (diracUpper Ψ)) =
        weylUpper ((I * (m : ℂ)) • diracUpper Ψ) +
          weylLower ((I * (m : ℂ)) • diracLower Ψ) := by
    rw [← slash_weyl_decompose, h, hrhs]
  exact weyl_pair_injective heq

/-! ### Rest-frame solutions -/

/-- Rest-frame particle spinor: lower Weyl block is `i` times the upper. -/
def restParticleSpinor (u : DualSpinor) : DiracSpinor :=
  weylUpper u + weylLower (I • u)

/-- Rest-frame antiparticle spinor: lower Weyl block is `-i` times the upper. -/
def restAntiparticleSpinor (u : DualSpinor) : DiracSpinor :=
  weylUpper u + weylLower (-I • u)

theorem restParticleSpinor_ne_zero :
    restParticleSpinor (EuclideanSpace.single 0 (1 : ℂ)) ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : DiracSpinor => WithLp.ofLp v 0) h
  simp [restParticleSpinor, weylUpper, weylLower, EuclideanSpace.single,
    PiLp.add_apply] at h0

theorem restAntiparticleSpinor_ne_zero :
    restAntiparticleSpinor (EuclideanSpace.single 0 (1 : ℂ)) ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : DiracSpinor => WithLp.ofLp v 0) h
  simp [restAntiparticleSpinor, weylUpper, weylLower, EuclideanSpace.single,
    PiLp.add_apply] at h0

private theorem pauliSlash_rest (m : ℝ) :
    pauliSlash (restMomentum m) = (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [pauliSlash, restMomentum, Pi.single_eq_same, Pi.single_eq_of_ne]

private theorem pauliSlashBar_rest (m : ℝ) :
    pauliSlashBar (restMomentum m) =
      (-(m : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [pauliSlashBar, restMomentum, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem restParticle_dirac (m : ℝ) (u : DualSpinor) :
    DiracMomentum m (restMomentum m) (restParticleSpinor u) := by
  unfold DiracMomentum restParticleSpinor
  have hsl : applyMat (pauliSlash (restMomentum m)) (I • u) = (m : ℂ) • (I • u) := by
    rw [pauliSlash_rest, applyMat_smul_mat, applyMat_one]
  have hbar : applyMat (pauliSlashBar (restMomentum m)) u = (-(m : ℂ)) • u := by
    rw [pauliSlashBar_rest, applyMat_smul_mat, applyMat_one]
  have h1 : (m : ℂ) • weylUpper (I • u) = (I * (m : ℂ)) • weylUpper u := by
    rw [← weylUpper_smul, smul_smul, mul_comm, weylUpper_smul]
  have h2 : (-(m : ℂ)) • weylLower u = (I * (m : ℂ)) • weylLower (I • u) := by
    have : I * (m : ℂ) * I = -(m : ℂ) := by
      rw [mul_right_comm, I_mul_I, neg_one_mul]
    calc (-(m : ℂ)) • weylLower u
        = weylLower ((-(m : ℂ)) • u) := (weylLower_smul _ _).symm
      _ = weylLower ((I * (m : ℂ) * I) • u) := by rw [this]
      _ = weylLower ((I * (m : ℂ)) • I • u) := by rw [smul_smul]
      _ = (I * (m : ℂ)) • weylLower (I • u) := weylLower_smul _ _
  rw [applyDiracMat_add, slash_weylUpper, slash_weylLower, hsl, hbar]
  rw [weylLower_smul, weylUpper_smul, h1, h2, smul_add, add_comm]

theorem restAntiparticle_dirac_neg (m : ℝ) (u : DualSpinor) :
    DiracMomentum (-m) (restMomentum m) (restAntiparticleSpinor u) := by
  unfold DiracMomentum restAntiparticleSpinor
  have hsl : applyMat (pauliSlash (restMomentum m)) (-I • u) = (m : ℂ) • (-I • u) := by
    rw [pauliSlash_rest, applyMat_smul_mat, applyMat_one]
  have hbar : applyMat (pauliSlashBar (restMomentum m)) u = (-(m : ℂ)) • u := by
    rw [pauliSlashBar_rest, applyMat_smul_mat, applyMat_one]
  have h1 : (m : ℂ) • weylUpper (-I • u) = (I * ((-m : ℝ) : ℂ)) • weylUpper u := by
    have : (m : ℂ) * (-I) = I * ((-m : ℝ) : ℂ) := by
      simp [ofReal_neg, mul_comm]
    rw [← weylUpper_smul, smul_smul, this, weylUpper_smul]
  have h2 : (-(m : ℂ)) • weylLower u = (I * ((-m : ℝ) : ℂ)) • weylLower (-I • u) := by
    have : I * ((-m : ℝ) : ℂ) * (-I) = -(m : ℂ) := by
      simp [ofReal_neg]
      rw [mul_right_comm, I_mul_I, neg_one_mul]
    calc (-(m : ℂ)) • weylLower u
        = weylLower ((-(m : ℂ)) • u) := (weylLower_smul _ _).symm
      _ = weylLower ((I * ((-m : ℝ) : ℂ) * (-I)) • u) := by rw [this]
      _ = weylLower ((I * ((-m : ℝ) : ℂ)) • (-I) • u) := by rw [smul_smul]
      _ = (I * ((-m : ℝ) : ℂ)) • weylLower (-I • u) := weylLower_smul _ _
  rw [applyDiracMat_add, slash_weylUpper, slash_weylLower, hsl, hbar]
  rw [weylLower_smul, weylUpper_smul, h1, h2, smul_add, add_comm]

/-- Massive rest-frame particle solutions exist and are nonzero. -/
theorem exists_rest_particle (m : ℝ) :
    ∃ Ψ : DiracSpinor, Ψ ≠ 0 ∧ DiracMomentum m (restMomentum m) Ψ :=
  ⟨restParticleSpinor (EuclideanSpace.single 0 (1 : ℂ)),
    restParticleSpinor_ne_zero, restParticle_dirac m _⟩

theorem slashMat_anticomm_gamma5 (p : Vec4) :
    slashMat p * diracMat5 + diracMat5 * slashMat p = 0 := by
  simp only [slashMat]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have h := diracMat5_anticomm μ
  calc ((p μ : ℂ) • diracMat μ) * diracMat5 + diracMat5 * ((p μ : ℂ) • diracMat μ)
      = (p μ : ℂ) • (diracMat μ * diracMat5) +
          (p μ : ℂ) • (diracMat5 * diracMat μ) := by
        simp [Matrix.smul_mul, Matrix.mul_smul]
    _ = (p μ : ℂ) • (diracMat μ * diracMat5 + diracMat5 * diracMat μ) := by
        rw [smul_add]
    _ = (p μ : ℂ) • (diracMat5 * diracMat μ + diracMat μ * diracMat5) := by
        rw [add_comm]
    _ = (p μ : ℂ) • 0 := by rw [h]
    _ = 0 := by simp

/-- Chirality `γ⁵` sends a mass-`m` solution to a mass-`(-m)` solution. -/
theorem diracMat5_flips_mass {m : ℝ} {p : Vec4} {Ψ : DiracSpinor}
    (h : DiracMomentum m p Ψ) :
    DiracMomentum (-m) p (applyDiracMat diracMat5 Ψ) := by
  have hcomm : slashMat p * diracMat5 = -(diracMat5 * slashMat p) :=
    eq_neg_of_add_eq_zero_left (slashMat_anticomm_gamma5 p)
  unfold DiracMomentum
  calc applyDiracMat (slashMat p) (applyDiracMat diracMat5 Ψ)
      = applyDiracMat (slashMat p * diracMat5) Ψ :=
        (applyDiracMat_mul _ _ _).symm
    _ = applyDiracMat (-(diracMat5 * slashMat p)) Ψ := by rw [hcomm]
    _ = -applyDiracMat (diracMat5 * slashMat p) Ψ := applyDiracMat_neg _ _
    _ = -applyDiracMat diracMat5 (applyDiracMat (slashMat p) Ψ) := by
        rw [applyDiracMat_mul]
    _ = -applyDiracMat diracMat5 ((I * (m : ℂ)) • Ψ) := by rw [h]
    _ = -((I * (m : ℂ)) • applyDiracMat diracMat5 Ψ) := by
        rw [applyDiracMat_smul]
    _ = (I * ((-m : ℝ) : ℂ)) • applyDiracMat diracMat5 Ψ := by
        simp [neg_smul, ofReal_neg]

end Logic

end DstDiophantine
