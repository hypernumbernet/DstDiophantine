import DstDiophantine.Logic.Quantum.DiracSpinor
import DstDiophantine.Logic.Quantum.DeBroglie
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Momentum-space Dirac equation from the Clifford square

The Minkowski quadratic is already a square in `Cl(3,1)`:
`γ(p)² = Q(p)`. On the Dirac module `ℂ⁴` the same identity is
`slash(p)² = Q(p) I`. A spinor eigenvector `slash(p) Ψ = i m Ψ`
therefore sits on the mass shell `Q(p) = -m²`.

A rest-frame particle solution is assembled from a dual spinor `u`.
On any mass shell `Q(p)=-m²` with `m≠0` the same Weyl parameter
determines a solution whose rest-frame specialisation is `(u,iu)`.
A longitudinal boost of that rest pair is the on-shell Weyl
construction after the chiral hyperbolic Rodrigues factor along the
boost axis. Dual rotation about that axis commutes with the factor;
a perpendicular dual rotation need not. The `ℂ⁴` overlap of two
rest-frame solutions is twice the dual-rotor amplitude. The same
boost multiplies that overlap by `cosh α`, for every dual rotation.
The factor equals `1` only at vanishing rapidity.

The mass bilinear is the Hermitian form `Ψ†(-iγ⁰)Φ`. On every pair of
rest-frame solutions it equals the Euclidean overlap, and a longitudinal
boost leaves it unchanged. In this representation `(-iγ⁰)γ⁰ = i`, so the
time component of the Dirac current is `i` times the Euclidean overlap.
Along the boosted rest pair the current is
`i Ψ̄Φ (cosh α, 0, 0, −sinh α)`, its Clifford contraction with the
boosted momentum is `i m Ψ̄Φ`, and `(j⁰, −j³)` is parallel to that
momentum.

The eigenrays of `σ_z` label spin along that momentum. `V(α)` multiplies
the eigenvalue `+1` by `e^{α/2}` on the upper block and by `e^{-α/2}` on
the lower, and both blocks stay in that ray; the opposite ray exchanges
the two factors. The mass bilinear and every current component between
the two rays vanish. A dual rotation about the boost axis multiplies each
ray by a phase. A dual rotation of angle `π` about a perpendicular axis
exchanges the rays.

This is the first-order factor of Klein–Gordon. It is not a PDE on
spacetime, not a derivation of `m` from torsion, and not covariance
under the full rotor group.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex Cl31 InnerProductSpace

open scoped InnerProductSpace

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

theorem diracUpper_weylUpper (u : DualSpinor) :
    diracUpper (weylUpper u) = u := by
  ext i
  fin_cases i <;> simp [diracUpper, weylUpper]

theorem diracLower_weylLower (l : DualSpinor) :
    diracLower (weylLower l) = l := by
  ext i
  fin_cases i <;> simp [diracLower, weylLower]

theorem diracUpper_weylLower (l : DualSpinor) :
    diracUpper (weylLower l) = 0 := by
  ext i
  fin_cases i <;> simp [diracUpper, weylLower]

theorem diracLower_weylUpper (u : DualSpinor) :
    diracLower (weylUpper u) = 0 := by
  ext i
  fin_cases i <;> simp [diracLower, weylUpper]

theorem diracUpper_add (Ψ Φ : DiracSpinor) :
    diracUpper (Ψ + Φ) = diracUpper Ψ + diracUpper Φ := by
  ext i
  fin_cases i <;> simp [diracUpper, PiLp.add_apply]

theorem diracLower_add (Ψ Φ : DiracSpinor) :
    diracLower (Ψ + Φ) = diracLower Ψ + diracLower Φ := by
  ext i
  fin_cases i <;> simp [diracLower, PiLp.add_apply]

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

theorem applyMat_neg (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor) :
    applyMat (-M) ψ = -applyMat M ψ := by
  simpa using applyMat_smul_mat (-1) M ψ

theorem applyMat_one (ψ : DualSpinor) :
    applyMat (1 : Matrix (Fin 2) (Fin 2) ℂ) ψ = ψ := by
  simp [applyMat, Matrix.one_mulVec]

theorem applyMat_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor) :
    applyMat (A * B) ψ = applyMat A (applyMat B ψ) := by
  simp [applyMat, Matrix.mulVec_mulVec]

private theorem applyMat_basis (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    WithLp.ofLp (applyMat A (EuclideanSpace.single j (1 : ℂ))) i = A i j := by
  simp [applyMat, EuclideanSpace.single]

private theorem applyMat_eq_of_forall {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ ψ, applyMat A ψ = applyMat B ψ) : A = B := by
  ext i j
  have hij := congrArg (fun v : DualSpinor => WithLp.ofLp v i)
    (h (EuclideanSpace.single j (1 : ℂ)))
  simpa [applyMat_basis] using hij

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

/-- Chiral slashes multiply to the Minkowski quadratic. -/
theorem pauliSlash_mul_pauliSlashBar (p : Vec4) :
    pauliSlash p * pauliSlashBar p = (minkowskiQ p : ℂ) • 1 := by
  refine applyMat_eq_of_forall fun ψ => ?_
  rw [applyMat_smul_mat, applyMat_one]
  have hsq :
      applyDiracMat (slashMat p * slashMat p) (weylUpper ψ) =
        weylUpper (applyMat (pauliSlash p * pauliSlashBar p) ψ) := by
    rw [applyDiracMat_mul, slash_weylUpper, slash_weylLower, applyMat_mul]
  have hQ :
      applyDiracMat (slashMat p * slashMat p) (weylUpper ψ) =
        weylUpper ((minkowskiQ p : ℂ) • ψ) := by
    rw [slashMat_sq, applyDiracMat_smul_one, weylUpper_smul]
  exact weylUpper_injective (hsq.symm.trans hQ)

theorem pauliSlashBar_mul_pauliSlash (p : Vec4) :
    pauliSlashBar p * pauliSlash p = (minkowskiQ p : ℂ) • 1 := by
  refine applyMat_eq_of_forall fun ψ => ?_
  rw [applyMat_smul_mat, applyMat_one]
  have hsq :
      applyDiracMat (slashMat p * slashMat p) (weylLower ψ) =
        weylLower (applyMat (pauliSlashBar p * pauliSlash p) ψ) := by
    rw [applyDiracMat_mul, slash_weylLower, slash_weylUpper, applyMat_mul]
  have hQ :
      applyDiracMat (slashMat p * slashMat p) (weylLower ψ) =
        weylLower ((minkowskiQ p : ℂ) • ψ) := by
    rw [slashMat_sq, applyDiracMat_smul_one, weylLower_smul]
  exact weylLower_injective (hsq.symm.trans hQ)

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

theorem pauliSlash_rest (m : ℝ) :
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

/-! ### On-shell solutions from a Weyl parameter -/

/-- On-shell particle spinor: the lower Weyl block is fixed by the chiral slash.
At rest this is the pair \((u,iu)\). -/
noncomputable def onShellParticleSpinor (m : ℝ) (p : Vec4) (u : DualSpinor) :
    DiracSpinor :=
  weylUpper u + weylLower (-(I / (m : ℂ)) • applyMat (pauliSlashBar p) u)

theorem onShellParticleSpinor_rest {m : ℝ} (hm : m ≠ 0) (u : DualSpinor) :
    onShellParticleSpinor m (restMomentum m) u = restParticleSpinor u := by
  have hmC : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm
  have hscale : -(I / (m : ℂ)) * (-(m : ℂ)) = I := by
    field_simp [hmC]
  unfold onShellParticleSpinor restParticleSpinor
  have hbar : applyMat (pauliSlashBar (restMomentum m)) u = (-(m : ℂ)) • u := by
    rw [pauliSlashBar_rest, applyMat_smul_mat, applyMat_one]
  rw [hbar, smul_smul, hscale]

theorem onShellParticleSpinor_ne_zero {m : ℝ} {p : Vec4} {u : DualSpinor}
    (hu : u ≠ 0) : onShellParticleSpinor m p u ≠ 0 := by
  intro h
  have h0 : weylUpper u + weylLower (-(I / (m : ℂ)) • applyMat (pauliSlashBar p) u) =
      weylUpper 0 + weylLower 0 := by
    simpa [onShellParticleSpinor, weylUpper_zero, weylLower_zero] using h
  exact hu (weyl_pair_injective h0).1

private theorem dualSpinor_single_ne_zero :
    EuclideanSpace.single (0 : Fin 2) (1 : ℂ) ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : DualSpinor => WithLp.ofLp v 0) h
  simp [EuclideanSpace.single] at h0

/-- Any dual spinor determines a massive Dirac solution on the mass shell. -/
theorem onShellParticle_dirac {m : ℝ} {p : Vec4} (hm : m ≠ 0)
    (hQ : minkowskiQ p = -m ^ 2) (u : DualSpinor) :
    DiracMomentum m p (onShellParticleSpinor m p u) := by
  have hmC : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm
  set l : DualSpinor := -(I / (m : ℂ)) • applyMat (pauliSlashBar p) u
  have hscale : I * (m : ℂ) * (-(I / (m : ℂ))) = 1 := by
    field_simp [hmC]
    simp [sq, I_mul_I]
  have hbar : applyMat (pauliSlashBar p) u = (I * (m : ℂ)) • l := by
    have : (I * (m : ℂ)) • l =
        (I * (m : ℂ) * (-(I / (m : ℂ)))) • applyMat (pauliSlashBar p) u := by
      dsimp [l]; rw [smul_smul]
    rw [this, hscale, one_smul]
  have hsl : applyMat (pauliSlash p) l = (I * (m : ℂ)) • u := by
    have hprod :
        applyMat (pauliSlash p) (applyMat (pauliSlashBar p) u) =
          (minkowskiQ p : ℂ) • u := by
      rw [← applyMat_mul, pauliSlash_mul_pauliSlashBar, applyMat_smul_mat,
        applyMat_one]
    have hQ' : (minkowskiQ p : ℂ) = -((m : ℂ) ^ 2) := by
      rw [hQ, ofReal_neg, ofReal_pow]
    have hcoeff : -(I / (m : ℂ)) * (-((m : ℂ) ^ 2)) = I * (m : ℂ) := by
      field_simp [hmC]
    calc applyMat (pauliSlash p) l
        = -(I / (m : ℂ)) • applyMat (pauliSlash p) (applyMat (pauliSlashBar p) u) := by
          dsimp [l]; rw [applyMat_smul]
      _ = -(I / (m : ℂ)) • ((minkowskiQ p : ℂ) • u) := by rw [hprod]
      _ = (-(I / (m : ℂ)) * (minkowskiQ p : ℂ)) • u := by rw [smul_smul]
      _ = (I * (m : ℂ)) • u := by rw [hQ', hcoeff]
  unfold DiracMomentum onShellParticleSpinor
  rw [applyDiracMat_add, slash_weylUpper, slash_weylLower]
  have h1 : weylUpper (applyMat (pauliSlash p) l) =
      (I * (m : ℂ)) • weylUpper u := by
    rw [hsl, weylUpper_smul]
  have h2 : weylLower (applyMat (pauliSlashBar p) u) =
      (I * (m : ℂ)) • weylLower l := by
    rw [hbar, weylLower_smul]
  rw [h1, h2, smul_add, add_comm]

/-- Massive on-shell particle solutions exist for every four-momentum on the shell. -/
theorem exists_onShell_particle {m : ℝ} {p : Vec4} (hm : m ≠ 0)
    (hQ : minkowskiQ p = -m ^ 2) :
    ∃ Ψ : DiracSpinor, Ψ ≠ 0 ∧ DiracMomentum m p Ψ :=
  ⟨onShellParticleSpinor m p (EuclideanSpace.single 0 (1 : ℂ)),
    onShellParticleSpinor_ne_zero dualSpinor_single_ne_zero,
    onShellParticle_dirac hm hQ _⟩

/-- Longitudinal boost of the rest momentum: \((m\cosh\alpha,0,0,m\sinh\alpha)\). -/
noncomputable def boostZMomentum (m α : ℝ) : Vec4 :=
  Pi.single (0 : Fin 4) (m * Real.cosh α) + Pi.single (3 : Fin 4) (m * Real.sinh α)

private theorem boostZMomentum_zero (m α : ℝ) :
    boostZMomentum m α 0 = m * Real.cosh α := by
  simp [boostZMomentum, Pi.single_eq_same, Pi.single_eq_of_ne]

private theorem boostZMomentum_one (m α : ℝ) : boostZMomentum m α 1 = 0 := by
  simp [boostZMomentum, Pi.single_eq_of_ne]

private theorem boostZMomentum_two (m α : ℝ) : boostZMomentum m α 2 = 0 := by
  simp [boostZMomentum, Pi.single_eq_of_ne]

private theorem boostZMomentum_three (m α : ℝ) :
    boostZMomentum m α 3 = m * Real.sinh α := by
  simp [boostZMomentum, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem minkowskiQ_boostZ (m α : ℝ) :
    minkowskiQ (boostZMomentum m α) = -m ^ 2 := by
  have hid : Real.cosh α ^ 2 - Real.sinh α ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq α
  calc minkowskiQ (boostZMomentum m α)
      = -(m * Real.cosh α) ^ 2 + (m * Real.sinh α) ^ 2 := by
        rw [minkowskiQ_eq, boostZMomentum_zero, boostZMomentum_one,
          boostZMomentum_two, boostZMomentum_three]; ring
    _ = -m ^ 2 * (Real.cosh α ^ 2 - Real.sinh α ^ 2) := by ring
    _ = -m ^ 2 := by rw [hid]; ring

/-! ### Chiral boost along \(z\) and internal dual rotation -/

/-- Hyperbolic Rodrigues factor along \(\sigma_z\):
\(\cosh(\alpha/2)\,I+\sinh(\alpha/2)\,\sigma_z\). -/
noncomputable def chiralBoostZ (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cosh (α / 2) : ℂ) • 1 + (Real.sinh (α / 2) : ℂ) • pauliZ

private theorem chiralBoostZ_eq (α : ℝ) :
    chiralBoostZ α =
      !![↑(Real.exp (α / 2)), 0; 0, ↑(Real.exp (-(α / 2)))] := by
  unfold chiralBoostZ pauliZ
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.add_apply, Matrix.smul_apply, Complex.cosh_add_sinh,
      ofReal_div, ofReal_exp]
  · simp [Matrix.add_apply, Matrix.smul_apply]
  · simp [Matrix.add_apply, Matrix.smul_apply]
  · simp [Matrix.add_apply, Matrix.smul_apply]
    simpa [sub_eq_add_neg] using Complex.cosh_sub_sinh (↑α / 2 : ℂ)

/-- Same-axis chiral boosts compose by adding rapidities. -/
private theorem chiralBoostZ_add (α β : ℝ) :
    chiralBoostZ (α + β) = chiralBoostZ α * chiralBoostZ β := by
  rw [chiralBoostZ_eq, chiralBoostZ_eq, chiralBoostZ_eq]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← Complex.exp_add]; congr 1; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← Complex.exp_add]; congr 1; ring

private theorem pauliSlashBar_boostZ (m α : ℝ) :
    pauliSlashBar (boostZMomentum m α) =
      (-((m * Real.cosh α : ℝ) : ℂ)) • 1 +
        ((m * Real.sinh α : ℝ) : ℂ) • pauliZ := by
  simp [pauliSlashBar, boostZMomentum_zero, boostZMomentum_one,
    boostZMomentum_two, boostZMomentum_three]

/-- Weyl-block action of a longitudinal Dirac boost: the upper block
by \(V(\alpha)\) and the lower by \(V(-\alpha)\). -/
noncomputable def applyDiracBoostZ (α : ℝ) (Ψ : DiracSpinor) : DiracSpinor :=
  weylUpper (applyMat (chiralBoostZ α) (diracUpper Ψ)) +
    weylLower (applyMat (chiralBoostZ (-α)) (diracLower Ψ))

private theorem applyDiracBoostZ_weyl (α : ℝ) (u l : DualSpinor) :
    applyDiracBoostZ α (weylUpper u + weylLower l) =
      weylUpper (applyMat (chiralBoostZ α) u) +
        weylLower (applyMat (chiralBoostZ (-α)) l) := by
  unfold applyDiracBoostZ
  rw [diracUpper_add, diracLower_add, diracUpper_weylUpper, diracUpper_weylLower,
    diracLower_weylUpper, diracLower_weylLower, add_zero, zero_add]

private theorem onShell_boostZ_lower {m α : ℝ} (hm : m ≠ 0) (u : DualSpinor) :
    -(I / (m : ℂ)) • applyMat (pauliSlashBar (boostZMomentum m α)) u =
      I • applyMat (chiralBoostZ (-(2 * α))) u := by
  have hmC : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm
  have hV : chiralBoostZ (-(2 * α)) =
      (Real.cosh α : ℂ) • 1 - (Real.sinh α : ℂ) • pauliZ := by
    have hdiv : -(2 * α) / 2 = -α := by ring
    unfold chiralBoostZ
    rw [hdiv, Real.cosh_neg, Real.sinh_neg, ofReal_neg, neg_smul, sub_eq_add_neg]
  have hbar :
      applyMat (pauliSlashBar (boostZMomentum m α)) u =
        (-((m * Real.cosh α : ℝ) : ℂ)) • u +
          ((m * Real.sinh α : ℝ) : ℂ) • applyMat pauliZ u := by
    rw [pauliSlashBar_boostZ, applyMat_add_mat, applyMat_smul_mat, applyMat_one,
      applyMat_smul_mat]
  have hcosh : ((m * Real.cosh α : ℝ) : ℂ) = (m : ℂ) * Real.cosh α := ofReal_mul _ _
  have hsinh : ((m * Real.sinh α : ℝ) : ℂ) = (m : ℂ) * Real.sinh α := ofReal_mul _ _
  have hc : -(I / (m : ℂ)) * -((m : ℂ) * Real.cosh α) = I * Real.cosh α := by
    field_simp [hmC]
  have hs : -(I / (m : ℂ)) * ((m : ℂ) * Real.sinh α) = -(I * Real.sinh α) := by
    field_simp [hmC]
  have hR :
      applyMat (chiralBoostZ (-(2 * α))) u =
        (Real.cosh α : ℂ) • u - (Real.sinh α : ℂ) • applyMat pauliZ u := by
    rw [hV, sub_eq_add_neg, applyMat_add_mat, applyMat_smul_mat, applyMat_one,
      applyMat_neg, applyMat_smul_mat, sub_eq_add_neg]
  rw [hbar, smul_add, hcosh, hsinh, smul_smul, smul_smul, hc, hs, hR,
    smul_sub, smul_smul, smul_smul, mul_comm (I : ℂ), mul_comm (I : ℂ),
    sub_eq_add_neg, neg_smul]

/-- The on-shell Weyl construction at a longitudinal boost of rest
momentum is the Dirac-boosted rest pair, after a chiral factor on the
Weyl parameter. -/
theorem applyDiracBoostZ_rest {m α : ℝ} (hm : m ≠ 0) (u : DualSpinor) :
    applyDiracBoostZ α (restParticleSpinor u) =
      onShellParticleSpinor m (boostZMomentum m α)
        (applyMat (chiralBoostZ α) u) := by
  unfold restParticleSpinor onShellParticleSpinor
  rw [applyDiracBoostZ_weyl, onShell_boostZ_lower hm, applyMat_smul]
  have hcomp :
      applyMat (chiralBoostZ (-(2 * α))) (applyMat (chiralBoostZ α) u) =
        applyMat (chiralBoostZ (-α)) u := by
    rw [← applyMat_mul, ← chiralBoostZ_add]
    have : -(2 * α) + α = -α := by ring
    rw [this]
  rw [hcomp]

/-- Dual rotation about the boost axis commutes with the chiral factor. -/
theorem chiralBoostZ_comm_dualRotor_axis2 (α θ : ℝ) :
    chiralBoostZ α * dualRotorMat (EuclideanSpace.single 2 θ) =
      dualRotorMat (EuclideanSpace.single 2 θ) * chiralBoostZ α := by
  have hR :
      dualRotorMat (EuclideanSpace.single 2 θ) =
        !![↑(Real.cos (θ / 2)) - I * ↑(Real.sin (θ / 2)), 0;
           0, ↑(Real.cos (θ / 2)) + I * ↑(Real.sin (θ / 2))] := by
    rw [dualRotorMat_axis2_rodrigues, cyclicRep_two_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply] <;> ring
  rw [chiralBoostZ_eq, hR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Dual rotation about a perpendicular axis need not commute with the
chiral boost factor. -/
theorem chiralBoostZ_not_comm_dualRotor_axis0 :
    chiralBoostZ 2 * dualRotorMat (EuclideanSpace.single 0 Real.pi) ≠
      dualRotorMat (EuclideanSpace.single 0 Real.pi) * chiralBoostZ 2 := by
  have hR : dualRotorMat (EuclideanSpace.single 0 Real.pi) = cyclicRep 0 := by
    rw [dualRotorMat_axis0_rodrigues, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  rw [hR, cyclicRep_zero_eq, chiralBoostZ_eq]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hexp : Complex.exp 1 = Complex.exp (-1) :=
    mul_right_cancel₀ I_ne_zero (h01.trans (mul_comm _ _))
  have hre : Real.exp (1 : ℝ) = Real.exp (-(1 : ℝ)) := by
    apply ofReal_injective
    simpa [ofReal_exp] using hexp
  have : (1 : ℝ) = -1 := Real.exp_injective hre
  linarith

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

/-! ### Dual-rotor amplitude as rest-frame Dirac overlap -/

private theorem dirac_inner_sum (χ ψ : DiracSpinor) :
    inner ℂ χ ψ = ∑ i : Fin 4, star (χ i) * ψ i := by
  simp [inner, Fin.sum_univ_four]
  ring

private theorem dual_inner_sum (χ ψ : DualSpinor) :
    inner ℂ χ ψ = ∑ i : Fin 2, star (χ i) * ψ i := by
  simp [inner, Fin.sum_univ_two]
  ring

/-- Weyl blocks are orthogonal in \(\mathbb{C}^4\). -/
theorem weylUpper_inner_lower (ψ φ : DualSpinor) :
    inner ℂ (weylUpper ψ) (weylLower φ) = 0 := by
  rw [dirac_inner_sum]
  simp [weylUpper, weylLower, Fin.sum_univ_four]

theorem weylLower_inner_upper (ψ φ : DualSpinor) :
    inner ℂ (weylLower ψ) (weylUpper φ) = 0 := by
  rw [dirac_inner_sum]
  simp [weylUpper, weylLower, Fin.sum_univ_four]

theorem weylUpper_inner_upper (ψ χ : DualSpinor) :
    inner ℂ (weylUpper ψ) (weylUpper χ) = inner ℂ ψ χ := by
  rw [dirac_inner_sum, dual_inner_sum]
  simp [weylUpper, Fin.sum_univ_four, Fin.sum_univ_two]

theorem weylLower_inner_lower (ψ χ : DualSpinor) :
    inner ℂ (weylLower ψ) (weylLower χ) = inner ℂ ψ χ := by
  rw [dirac_inner_sum, dual_inner_sum]
  simp [weylLower, Fin.sum_univ_four, Fin.sum_univ_two]

private theorem inner_I_smul (u v : DualSpinor) :
    inner ℂ (I • u) (I • v) = inner ℂ u v := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
  have : (starRingEnd ℂ) I * I = 1 := by
    have hstar : (starRingEnd ℂ) I = -I := conj_I
    rw [hstar, neg_mul, I_mul_I]
    simp
  rw [this, one_mul]

/-- Rest-frame particle overlap is twice the dual-spinor pairing. -/
theorem restParticle_inner (u v : DualSpinor) :
    inner ℂ (restParticleSpinor u) (restParticleSpinor v) = 2 * inner ℂ u v := by
  unfold restParticleSpinor
  rw [inner_add_left, inner_add_right, inner_add_right,
    weylUpper_inner_upper, weylUpper_inner_lower, weylLower_inner_upper,
    weylLower_inner_lower, inner_I_smul]
  ring

/-- The \(\mathbb{C}^4\) overlap of rest-frame solutions that differ by a dual
rotation is twice the dual-rotor amplitude. Dual rotation of the Weyl
parameter stays on the rest-frame mass shell by `restParticle_dirac`. -/
theorem restParticle_dualRotor_overlap (β : DualRapidity) (u : DualSpinor) :
    inner ℂ (restParticleSpinor u)
        (restParticleSpinor (applyMat (dualRotorMat β) u)) =
      2 * dualRotorAmplitude β u := by
  rw [restParticle_inner, dualRotorAmplitude]

/-! ### Boosted Euclidean overlap -/

private theorem applyMat_coord (A : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor)
    (i : Fin 2) :
    applyMat A ψ i = ∑ j : Fin 2, A i j * ψ j := by
  simp [applyMat, Matrix.mulVec, dotProduct]

private theorem applyMat_inner (A : Matrix (Fin 2) (Fin 2) ℂ) (χ ψ : DualSpinor) :
    inner ℂ (applyMat A χ) ψ = inner ℂ χ (applyMat A.conjTranspose ψ) := by
  simp only [dual_inner_sum, applyMat_coord, Fin.sum_univ_two]
  simp only [star_add, star_mul', Matrix.conjTranspose_apply]
  ring

private theorem applyMat_inner_mul (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (χ ψ : DualSpinor) :
    inner ℂ (applyMat A χ) (applyMat B ψ) =
      inner ℂ χ (applyMat (A.conjTranspose * B) ψ) := by
  rw [applyMat_inner, applyMat_mul]

private theorem ofReal_star (t : ℝ) : star (t : ℂ) = (t : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

private theorem chiralBoostZ_hermitian (α : ℝ) :
    (chiralBoostZ α).conjTranspose = chiralBoostZ α := by
  unfold chiralBoostZ
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, pauliZ_isHermitian, ofReal_star, ofReal_star]

private theorem chiralBoostZ_double (α : ℝ) :
    chiralBoostZ α * chiralBoostZ α = chiralBoostZ (2 * α) := by
  have h : α + α = 2 * α := by ring
  rw [← h, chiralBoostZ_add]

private theorem cosh_eq_one_iff (α : ℝ) : Real.cosh α = 1 ↔ α = 0 := by
  constructor
  · intro h
    have hexp : Real.exp α + Real.exp (-α) = 2 := by
      rw [Real.cosh_eq] at h
      linarith
    have hneg : Real.exp (-α) * Real.exp α = 1 := by
      rw [← Real.exp_add]
      simp
    have hpoly : Real.exp α ^ 2 + 1 = 2 * Real.exp α := by
      calc Real.exp α ^ 2 + 1
          = Real.exp α ^ 2 + Real.exp (-α) * Real.exp α := by rw [hneg]
        _ = Real.exp α * (Real.exp α + Real.exp (-α)) := by ring
        _ = Real.exp α * 2 := by rw [hexp]
        _ = 2 * Real.exp α := by ring
    have hsq : (Real.exp α - 1) ^ 2 = 0 := by
      have : (Real.exp α - 1) ^ 2 = Real.exp α ^ 2 - 2 * Real.exp α + 1 := by ring
      linarith
    have hexp1 : Real.exp α = 1 := by
      have : Real.exp α - 1 = 0 := sq_eq_zero_iff.mp hsq
      linarith
    exact Real.exp_injective (by simpa [Real.exp_zero] using hexp1)
  · intro h
    simp [h]

/-- The two chiral grams along a longitudinal boost sum to a scalar. -/
private theorem chiralBoostZ_gram (α : ℝ) :
    chiralBoostZ (2 * α) + chiralBoostZ (-(2 * α)) =
      (2 * Real.cosh α : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hdiv : (2 * α) / 2 = α := by ring
  have hdivn : (-(2 * α)) / 2 = -α := by ring
  ext i j
  fin_cases i <;> fin_cases j
  · have hgoal :
        Complex.exp (α : ℂ) + (Complex.cosh (α : ℂ) + -Complex.sinh (α : ℂ)) =
          2 * Complex.cosh (α : ℂ) := by
      rw [(Complex.cosh_add_sinh (α : ℂ)).symm]
      ring
    simpa [chiralBoostZ, hdiv, hdivn, pauliZ, Real.cosh_neg, Real.sinh_neg,
      Matrix.add_apply, Matrix.smul_apply, ofReal_neg] using hgoal
  · simp [chiralBoostZ, hdiv, hdivn, pauliZ, Real.cosh_neg, Real.sinh_neg,
      Matrix.add_apply, Matrix.smul_apply, ofReal_neg]
  · simp [chiralBoostZ, hdiv, hdivn, pauliZ, Real.cosh_neg, Real.sinh_neg,
      Matrix.add_apply, Matrix.smul_apply, ofReal_neg]
  · have hgoal :
        Complex.cosh (α : ℂ) + -Complex.sinh (α : ℂ) + Complex.exp (α : ℂ) =
          2 * Complex.cosh (α : ℂ) := by
      rw [(Complex.cosh_add_sinh (α : ℂ)).symm]
      ring
    simpa [chiralBoostZ, hdiv, hdivn, pauliZ, Real.cosh_neg, Real.sinh_neg,
      Matrix.add_apply, Matrix.smul_apply, ofReal_neg] using hgoal

private theorem boosted_blocks (α : ℝ) (u : DualSpinor) :
    applyDiracBoostZ α (restParticleSpinor u) =
      weylUpper (applyMat (chiralBoostZ α) u) +
        weylLower (I • applyMat (chiralBoostZ (-α)) u) := by
  unfold restParticleSpinor
  rw [applyDiracBoostZ_weyl, applyMat_smul]

/-- A longitudinal boost of rapidity `α` multiplies the rest-frame
`ℂ⁴` overlap by `cosh α`, for every dual rotation. -/
theorem boostedRest_dualRotor_overlap (α : ℝ) (β : DualRapidity) (u : DualSpinor) :
    inner ℂ
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α
          (restParticleSpinor (applyMat (dualRotorMat β) u))) =
      (2 * Real.cosh α : ℂ) * dualRotorAmplitude β u := by
  have hpos : chiralBoostZ α * chiralBoostZ α = chiralBoostZ (2 * α) :=
    chiralBoostZ_double α
  have hneg : chiralBoostZ (-α) * chiralBoostZ (-α) = chiralBoostZ (-(2 * α)) := by
    rw [chiralBoostZ_double]
    congr 1
    ring
  rw [boosted_blocks, boosted_blocks]
  rw [inner_add_left, inner_add_right, inner_add_right,
    weylUpper_inner_upper, weylUpper_inner_lower, weylLower_inner_upper,
    weylLower_inner_lower, inner_I_smul]
  rw [applyMat_inner_mul, applyMat_inner_mul, chiralBoostZ_hermitian,
    chiralBoostZ_hermitian, hpos, hneg]
  simp only [add_zero, zero_add]
  rw [← inner_add_right, ← applyMat_add_mat, chiralBoostZ_gram,
    applyMat_smul_mat, applyMat_one, inner_smul_right, dualRotorAmplitude]

/-- The boosted overlap is the rest-frame overlap multiplied by `cosh α`. -/
theorem boostedRest_overlap_factor (α : ℝ) (β : DualRapidity) (u : DualSpinor) :
    inner ℂ
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α
          (restParticleSpinor (applyMat (dualRotorMat β) u))) =
      (Real.cosh α : ℂ) *
        inner ℂ (restParticleSpinor u)
          (restParticleSpinor (applyMat (dualRotorMat β) u)) := by
  rw [boostedRest_dualRotor_overlap, restParticle_dualRotor_overlap]
  ring

private theorem dualRotorAmplitude_zero (u : DualSpinor) :
    dualRotorAmplitude 0 u = inner ℂ u u := by
  unfold dualRotorAmplitude
  have hR : dualRotorMat (0 : DualRapidity) = 1 := by
    rw [dualRotorMat_rodrigues]
    simp
  rw [hR, applyMat_one]

private theorem spinUp_inner_self : inner ℂ spinUp spinUp = 1 := by
  rw [dual_inner_sum]
  simp [spinUp]

/-- The boosted overlap agrees with the rest-frame overlap for every dual
rotation if and only if the boost rapidity vanishes. -/
theorem boostedRest_overlap_eq_rest_iff (α : ℝ) :
    (∀ (β : DualRapidity) (u : DualSpinor),
      inner ℂ
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α
            (restParticleSpinor (applyMat (dualRotorMat β) u))) =
        inner ℂ (restParticleSpinor u)
          (restParticleSpinor (applyMat (dualRotorMat β) u))) ↔
      α = 0 := by
  constructor
  · intro h
    have hamp := h (0 : DualRapidity) spinUp
    rw [boostedRest_overlap_factor, restParticle_dualRotor_overlap,
      dualRotorAmplitude_zero, spinUp_inner_self] at hamp
    have hcoshC : (Real.cosh α : ℂ) = 1 := by
      have h2 : (Real.cosh α : ℂ) * 2 = 2 := by simpa using hamp
      have hne : (2 : ℂ) ≠ 0 := by norm_num
      exact mul_right_cancel₀ hne (by simpa [mul_comm] using h2)
    exact (cosh_eq_one_iff α).mp (ofReal_injective hcoshC)
  · intro hα
    subst hα
    intro β u
    rw [boostedRest_overlap_factor, Real.cosh_zero]
    simp

/-! ### Mass bilinear and Dirac current

`(-iγ⁰)` is Hermitian. On a rest pair it reproduces the Euclidean overlap.
A longitudinal boost leaves that bilinear fixed and turns the Euclidean
growth `cosh α` into the time component of the current. -/

/-- Dirac adjoint matrix \(-i\gamma^0\) in the Weyl representation. -/
noncomputable def diracAdjointMat : Matrix (Fin 4) (Fin 4) ℂ :=
  -I • diracMat0

theorem diracAdjointMat_mul_gamma0 :
    diracAdjointMat * diracMat0 = I • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  unfold diracAdjointMat
  rw [Matrix.smul_mul, diracMat0_sq, smul_neg, neg_smul, neg_neg]

/-- Mass bilinear \(\bar\Psi\Phi=\Psi^\dagger(-i\gamma^0)\Phi\). -/
noncomputable def diracScalar (Ψ Φ : DiracSpinor) : ℂ :=
  inner ℂ Ψ (applyDiracMat diracAdjointMat Φ)

/-- Dirac current \(j^\mu=\Psi^\dagger(-i\gamma^0)\gamma^\mu\Phi\). -/
noncomputable def diracCurrent (μ : Fin 4) (Ψ Φ : DiracSpinor) : ℂ :=
  inner ℂ Ψ (applyDiracMat (diracAdjointMat * diracMat μ) Φ)

theorem diracCurrent_eq_scalar (μ : Fin 4) (Ψ Φ : DiracSpinor) :
    diracCurrent μ Ψ Φ = diracScalar Ψ (applyDiracMat (diracMat μ) Φ) := by
  unfold diracCurrent diracScalar
  rw [applyDiracMat_mul]

/-- \((-i\gamma^0)\gamma^0=i\), so the time component is \(i\) times the
Euclidean overlap, for every pair of Dirac spinors. -/
theorem diracCurrent_zero (Ψ Φ : DiracSpinor) :
    diracCurrent 0 Ψ Φ = I * inner ℂ Ψ Φ := by
  have hmul : diracAdjointMat * diracMat 0 = I • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    simpa [diracMat] using diracAdjointMat_mul_gamma0
  unfold diracCurrent
  rw [hmul, applyDiracMat_smul_one, inner_smul_right]

private theorem diracAdjoint_weyl (u l : DualSpinor) :
    applyDiracMat diracAdjointMat (weylUpper u + weylLower l) =
      weylUpper (-I • l) + weylLower (I • u) := by
  have h0 :
      applyDiracMat diracMat0 (weylUpper u + weylLower l) =
        weylUpper l + weylLower (-u) := by
    rw [applyDiracMat_add, apply_diracMat0_weylUpper, apply_diracMat0_weylLower,
      add_comm]
  have hneg : (-I) • (-u) = I • u := by
    rw [smul_neg, neg_smul, neg_neg]
  unfold diracAdjointMat
  rw [applyDiracMat_smul_mat, h0, smul_add, ← weylUpper_smul, ← weylLower_smul, hneg]

private theorem adjointCoeff (z : ℂ) :
    -I * (I * z) + I * (-I * z) = 2 * z := by
  calc -I * (I * z) + I * (-I * z)
      = (-(I * I) + -(I * I)) * z := by ring
    _ = (1 + 1) * z := by rw [I_mul_I]; ring
    _ = 2 * z := by ring

theorem diracScalar_weyl (u l v m : DualSpinor) :
    diracScalar (weylUpper u + weylLower l) (weylUpper v + weylLower m) =
      (-I) * inner ℂ u m + I * inner ℂ l v := by
  unfold diracScalar
  rw [diracAdjoint_weyl, inner_add_left, inner_add_right, inner_add_right,
    weylUpper_inner_upper, weylUpper_inner_lower, weylLower_inner_upper,
    weylLower_inner_lower, inner_smul_right, inner_smul_right]
  ring

/-- At rest the mass bilinear is the Euclidean overlap, twice the
dual-spinor pairing. -/
theorem restParticle_diracScalar (u v : DualSpinor) :
    diracScalar (restParticleSpinor u) (restParticleSpinor v) =
      2 * inner ℂ u v := by
  unfold restParticleSpinor
  rw [diracScalar_weyl, inner_smul_right, inner_smul_left, conj_I]
  exact adjointCoeff _

theorem restParticle_diracScalar_eq_inner (u v : DualSpinor) :
    diracScalar (restParticleSpinor u) (restParticleSpinor v) =
      inner ℂ (restParticleSpinor u) (restParticleSpinor v) := by
  rw [restParticle_diracScalar, restParticle_inner]

private theorem chiralBoostZ_zero : chiralBoostZ 0 = 1 := by
  unfold chiralBoostZ
  simp [Real.cosh_zero, Real.sinh_zero]

private theorem chiralBoostZ_inv (α : ℝ) :
    chiralBoostZ α * chiralBoostZ (-α) = 1 := by
  have h := chiralBoostZ_add α (-α)
  simpa [add_neg_cancel, chiralBoostZ_zero] using h.symm

private theorem chiralBoostZ_inv' (α : ℝ) :
    chiralBoostZ (-α) * chiralBoostZ α = 1 := by
  have h := chiralBoostZ_add (-α) α
  simpa [neg_add_cancel, chiralBoostZ_zero] using h.symm

private theorem exp_half_prod (α : ℝ) :
    Complex.exp (↑α / 2) * Complex.exp (-(↑α / 2)) = 1 := by
  rw [← Complex.exp_add]
  ring_nf
  simp

private theorem exp_half_prod' (α : ℝ) :
    Complex.exp (-(↑α / 2)) * Complex.exp (↑α / 2) = 1 := by
  rw [mul_comm, exp_half_prod]

private theorem exp_double (α : ℝ) :
    Complex.exp (↑α / 2) * Complex.exp (↑α / 2) = Complex.exp α := by
  rw [← Complex.exp_add]
  ring_nf

private theorem exp_double_neg (α : ℝ) :
    Complex.exp (-(↑α / 2)) * Complex.exp (-(↑α / 2)) = Complex.exp (-α) := by
  rw [← Complex.exp_add]
  ring_nf

private theorem sinh_sub_cosh_complex (α : ℝ) :
    (Real.sinh α : ℂ) - Real.cosh α = -Complex.exp (-α) := by
  have hsub : Real.cosh α - Real.sinh α = Real.exp (-α) := by
    have h := Real.cosh_add_sinh (-α)
    rw [Real.cosh_neg, Real.sinh_neg, ← sub_eq_add_neg] at h
    exact h
  have hneg : (Real.sinh α - Real.cosh α : ℝ) = -(Real.cosh α - Real.sinh α) := by
    ring
  rw [← Complex.ofReal_sub, hneg, hsub, Complex.ofReal_neg, Complex.ofReal_exp,
    Complex.ofReal_neg]

private theorem chiralBoostZ_conj_pauliX (α : ℝ) :
    chiralBoostZ α * pauliX * chiralBoostZ α = pauliX := by
  rw [chiralBoostZ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, exp_half_prod, exp_half_prod']

private theorem chiralBoostZ_conj_pauliY (α : ℝ) :
    chiralBoostZ α * pauliY * chiralBoostZ α = pauliY := by
  rw [chiralBoostZ_eq]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]
    calc Complex.exp (↑α / 2) * I * Complex.exp (-(↑α / 2))
        = (Complex.exp (↑α / 2) * Complex.exp (-(↑α / 2))) * I := by ring
      _ = I := by rw [exp_half_prod]; simp
  · simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]
    calc Complex.exp (-(↑α / 2)) * I * Complex.exp (↑α / 2)
        = (Complex.exp (-(↑α / 2)) * Complex.exp (↑α / 2)) * I := by ring
      _ = I := by rw [exp_half_prod']; simp
  · simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

private theorem chiralBoostZ_conj_pauliZ (α : ℝ) :
    chiralBoostZ α * pauliZ * chiralBoostZ α =
      (Real.sinh α : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (Real.cosh α : ℂ) • pauliZ := by
  rw [chiralBoostZ_eq]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [pauliZ, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_two, exp_double]
  · simp [pauliZ, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_two]
  · simp [pauliZ, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_two]
  · simp [pauliZ, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_two, exp_double_neg]
    rw [← sub_eq_add_neg, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
      sinh_sub_cosh_complex]

private theorem expectation_sandwich (A σ : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.conjTranspose = A) (u v : DualSpinor) :
    inner ℂ (applyMat A u) (applyMat σ (applyMat A v)) =
      inner ℂ u (applyMat (A * σ * A) v) := by
  rw [← applyMat_mul, applyMat_inner_mul, hA, mul_assoc]

private theorem spatial_current_weyl
    (σ : Matrix (Fin 2) (Fin 2) ℂ) (γ : Matrix (Fin 4) (Fin 4) ℂ)
    (hkU : ∀ ψ, applyDiracMat γ (weylUpper ψ) = weylLower (applyMat σ ψ))
    (hkL : ∀ ψ, applyDiracMat γ (weylLower ψ) = weylUpper (applyMat σ ψ))
    (U L U' L' : DualSpinor) :
    diracScalar (weylUpper U + weylLower L)
        (applyDiracMat γ (weylUpper U' + weylLower L')) =
      (-I) * inner ℂ U (applyMat σ U') + I * inner ℂ L (applyMat σ L') := by
  rw [applyDiracMat_add, hkU, hkL,
    add_comm (weylLower (applyMat σ U')) (weylUpper (applyMat σ L')),
    diracScalar_weyl]

private theorem boosted_pauli_current
    (σ : Matrix (Fin 2) (Fin 2) ℂ) (γ : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4)
    (hμ : diracMat μ = γ)
    (hkU : ∀ ψ, applyDiracMat γ (weylUpper ψ) = weylLower (applyMat σ ψ))
    (hkL : ∀ ψ, applyDiracMat γ (weylLower ψ) = weylUpper (applyMat σ ψ))
    (α : ℝ) (u v : DualSpinor) :
    diracCurrent μ
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α (restParticleSpinor v)) =
      (-I) * inner ℂ (applyMat (chiralBoostZ α) u)
          (applyMat σ (applyMat (chiralBoostZ α) v)) +
        I * inner ℂ (applyMat (chiralBoostZ (-α)) u)
          (applyMat σ (applyMat (chiralBoostZ (-α)) v)) := by
  rw [boosted_blocks, boosted_blocks, diracCurrent_eq_scalar, hμ,
    spatial_current_weyl σ γ hkU hkL]
  simp only [applyMat_smul, inner_I_smul]

/-- The Euclidean overlap of two boosted rest solutions is `cosh α` times
twice the dual-spinor pairing. -/
theorem boostedRest_inner (α : ℝ) (u v : DualSpinor) :
    inner ℂ
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α (restParticleSpinor v)) =
      (2 * Real.cosh α : ℂ) * inner ℂ u v := by
  have hpos : chiralBoostZ α * chiralBoostZ α = chiralBoostZ (2 * α) :=
    chiralBoostZ_double α
  have hneg : chiralBoostZ (-α) * chiralBoostZ (-α) = chiralBoostZ (-(2 * α)) := by
    rw [chiralBoostZ_double]
    congr 1
    ring
  rw [boosted_blocks, boosted_blocks]
  rw [inner_add_left, inner_add_right, inner_add_right,
    weylUpper_inner_upper, weylUpper_inner_lower, weylLower_inner_upper,
    weylLower_inner_lower, inner_I_smul]
  rw [applyMat_inner_mul, applyMat_inner_mul, chiralBoostZ_hermitian,
    chiralBoostZ_hermitian, hpos, hneg]
  simp only [add_zero, zero_add]
  rw [← inner_add_right, ← applyMat_add_mat, chiralBoostZ_gram,
    applyMat_smul_mat, applyMat_one, inner_smul_right]

/-- A longitudinal boost leaves the mass bilinear unchanged. -/
theorem boostedRest_diracScalar (α : ℝ) (u v : DualSpinor) :
    diracScalar
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α (restParticleSpinor v)) =
      2 * inner ℂ u v := by
  rw [boosted_blocks, boosted_blocks, diracScalar_weyl, inner_smul_right,
    inner_smul_left, conj_I]
  have hU : inner ℂ (applyMat (chiralBoostZ α) u)
      (applyMat (chiralBoostZ (-α)) v) = inner ℂ u v := by
    rw [applyMat_inner_mul, chiralBoostZ_hermitian, chiralBoostZ_inv, applyMat_one]
  have hL : inner ℂ (applyMat (chiralBoostZ (-α)) u)
      (applyMat (chiralBoostZ α) v) = inner ℂ u v := by
    rw [applyMat_inner_mul, chiralBoostZ_hermitian, chiralBoostZ_inv', applyMat_one]
  rw [hU, hL]
  exact adjointCoeff _

theorem boostedRest_diracScalar_dualRotor (α : ℝ) (β : DualRapidity) (u : DualSpinor) :
    diracScalar
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α
          (restParticleSpinor (applyMat (dualRotorMat β) u))) =
      2 * dualRotorAmplitude β u := by
  rw [boostedRest_diracScalar, dualRotorAmplitude]

/-- The mass bilinear and the Euclidean overlap of the boosted rest pair
agree for every dual spinors if and only if the rapidity vanishes. -/
theorem boostedRest_scalar_eq_inner_iff (α : ℝ) :
    (∀ u v : DualSpinor,
      diracScalar
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α (restParticleSpinor v)) =
        inner ℂ
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α (restParticleSpinor v))) ↔
      α = 0 := by
  constructor
  · intro h
    have hspin := h spinUp spinUp
    rw [boostedRest_diracScalar, boostedRest_inner, spinUp_inner_self] at hspin
    have hcoshC : (Real.cosh α : ℂ) = 1 := by
      have hmul : (2 : ℂ) * (Real.cosh α : ℂ) = (2 : ℂ) * 1 := by
        simpa [mul_one] using hspin.symm
      exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hmul
    exact (cosh_eq_one_iff α).mp (ofReal_injective hcoshC)
  · intro hα
    subst hα
    intro u v
    rw [boostedRest_diracScalar, boostedRest_inner, Real.cosh_zero]
    simp

theorem boostedRest_current_zero (α : ℝ) (u v : DualSpinor) :
    diracCurrent 0
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α (restParticleSpinor v)) =
      (I * Real.cosh α) *
        diracScalar
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α (restParticleSpinor v)) := by
  rw [diracCurrent_zero, boostedRest_inner, boostedRest_diracScalar]
  ring

private theorem boosted_pauli_cancel
    (σ : Matrix (Fin 2) (Fin 2) ℂ) (γ : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4)
    (hμ : diracMat μ = γ)
    (hkU : ∀ ψ, applyDiracMat γ (weylUpper ψ) = weylLower (applyMat σ ψ))
    (hkL : ∀ ψ, applyDiracMat γ (weylLower ψ) = weylUpper (applyMat σ ψ))
    (hσ : ∀ β : ℝ, chiralBoostZ β * σ * chiralBoostZ β = σ)
    (α : ℝ) (u v : DualSpinor) :
    diracCurrent μ
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α (restParticleSpinor v)) = 0 := by
  rw [boosted_pauli_current σ γ μ hμ hkU hkL]
  rw [expectation_sandwich _ _ (chiralBoostZ_hermitian α), hσ,
    expectation_sandwich _ _ (chiralBoostZ_hermitian (-α)), hσ]
  ring

theorem boostedRest_current_one (α : ℝ) (u v : DualSpinor) :
    diracCurrent 1
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α (restParticleSpinor v)) = 0 := by
  exact boosted_pauli_cancel pauliX diracMat1 1 rfl
    (fun ψ => apply_diracMat1_weylUpper ψ)
    (fun ψ => apply_diracMat1_weylLower ψ)
    chiralBoostZ_conj_pauliX α u v

theorem boostedRest_current_two (α : ℝ) (u v : DualSpinor) :
    diracCurrent 2
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α (restParticleSpinor v)) = 0 := by
  exact boosted_pauli_cancel pauliY diracMat2 2 rfl
    (fun ψ => apply_diracMat2_weylUpper ψ)
    (fun ψ => apply_diracMat2_weylLower ψ)
    chiralBoostZ_conj_pauliY α u v

private theorem pauliZ_expectation (β : ℝ) (u v : DualSpinor) :
    inner ℂ u (applyMat
        ((Real.sinh β : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (Real.cosh β : ℂ) • pauliZ) v) =
      (Real.sinh β : ℂ) * inner ℂ u v +
        (Real.cosh β : ℂ) * inner ℂ u (applyMat pauliZ v) := by
  rw [applyMat_add_mat, applyMat_smul_mat, applyMat_one, applyMat_smul_mat,
    inner_add_right, inner_smul_right, inner_smul_right]

theorem boostedRest_current_three (α : ℝ) (u v : DualSpinor) :
    diracCurrent 3
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α (restParticleSpinor v)) =
      (-I * Real.sinh α) *
        diracScalar
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α (restParticleSpinor v)) := by
  have hpos := chiralBoostZ_conj_pauliZ α
  have hneg : chiralBoostZ (-α) * pauliZ * chiralBoostZ (-α) =
      (-Real.sinh α : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (Real.cosh α : ℂ) • pauliZ := by
    rw [chiralBoostZ_conj_pauliZ (-α), Real.sinh_neg, Real.cosh_neg, ofReal_neg]
  have hnegMat :
      (-Real.sinh α : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (Real.cosh α : ℂ) • pauliZ =
      (Real.sinh (-α) : ℂ) • 1 + (Real.cosh (-α) : ℂ) • pauliZ := by
    rw [Real.sinh_neg, Real.cosh_neg, ofReal_neg]
  rw [boosted_pauli_current pauliZ diracMat3 3 rfl
      (fun ψ => apply_diracMat3_weylUpper ψ)
      (fun ψ => apply_diracMat3_weylLower ψ),
    expectation_sandwich _ _ (chiralBoostZ_hermitian α), hpos,
    expectation_sandwich _ _ (chiralBoostZ_hermitian (-α)), hneg, hnegMat,
    pauliZ_expectation α, pauliZ_expectation (-α), Real.sinh_neg, Real.cosh_neg,
    ofReal_neg, boostedRest_diracScalar]
  ring

/-- Clifford contraction of the current with the boosted momentum. -/
theorem boostedRest_current_contract (m α : ℝ) (u v : DualSpinor) :
    (boostZMomentum m α 0 : ℂ) *
        diracCurrent 0
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α (restParticleSpinor v)) +
      (boostZMomentum m α 1 : ℂ) *
        diracCurrent 1
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α (restParticleSpinor v)) +
      (boostZMomentum m α 2 : ℂ) *
        diracCurrent 2
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α (restParticleSpinor v)) +
      (boostZMomentum m α 3 : ℂ) *
        diracCurrent 3
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α (restParticleSpinor v)) =
      I * (m : ℂ) *
        diracScalar
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α (restParticleSpinor v)) := by
  rw [boostZMomentum_zero, boostZMomentum_one, boostZMomentum_two,
    boostZMomentum_three, boostedRest_current_zero, boostedRest_current_one,
    boostedRest_current_two, boostedRest_current_three]
  have hcosh : ((m * Real.cosh α : ℝ) : ℂ) = (m : ℂ) * Real.cosh α := ofReal_mul _ _
  have hsinh : ((m * Real.sinh α : ℝ) : ℂ) = (m : ℂ) * Real.sinh α := ofReal_mul _ _
  have hid : (Real.cosh α : ℂ) ^ 2 = (Real.sinh α : ℂ) ^ 2 + 1 := by
    have hsub : (Real.cosh α : ℂ) ^ 2 - (Real.sinh α : ℂ) ^ 2 = 1 := by
      rw [← ofReal_pow, ← ofReal_pow, ← ofReal_sub, Real.cosh_sq_sub_sinh_sq,
        ofReal_one]
    linear_combination hsub
  rw [hcosh, hsinh]
  ring_nf
  rw [hid]
  ring

/-- \((j^0,-j^3)\) tracks the boosted momentum, up to the factor \(i\)
fixed by the adjoint. Dividing by \(m\) needs \(m\neq 0\). -/
theorem boostedRest_current_parallel (m α : ℝ) (u v : DualSpinor) :
    let Ψ := applyDiracBoostZ α (restParticleSpinor u)
    let Φ := applyDiracBoostZ α (restParticleSpinor v)
    (m : ℂ) * diracCurrent 0 Ψ Φ =
        I * diracScalar Ψ Φ * (boostZMomentum m α 0 : ℂ) ∧
      (m : ℂ) * (-diracCurrent 3 Ψ Φ) =
        I * diracScalar Ψ Φ * (boostZMomentum m α 3 : ℂ) := by
  dsimp
  rw [boostedRest_current_zero, boostedRest_current_three, boostZMomentum_zero,
    boostZMomentum_three]
  have hcosh : ((m * Real.cosh α : ℝ) : ℂ) = (m : ℂ) * Real.cosh α := ofReal_mul _ _
  have hsinh : ((m * Real.sinh α : ℝ) : ℂ) = (m : ℂ) * Real.sinh α := ofReal_mul _ _
  rw [hcosh, hsinh]
  constructor <;> ring

/-! ### Spin along the longitudinal momentum

`σ_z` eigenrays are labels of the free solution. The chiral factor is
diagonal in that basis, so a longitudinal boost preserves each ray and a
same-axis dual rotation only multiplies it by a phase. A perpendicular
dual rotation of angle `π` exchanges the rays. Opposite rays are
orthogonal in the invariant mass bilinear, and the Dirac current between
them vanishes. -/

private theorem spinUp_inner_spinDown : inner ℂ spinUp spinDown = 0 := by
  rw [dual_inner_sum]
  simp [spinUp, spinDown]

private theorem pauliZ_spinUp : applyMat pauliZ spinUp = spinUp := by
  ext i
  fin_cases i <;>
    simp [applyMat, pauliZ, spinUp, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem pauliZ_spinDown : applyMat pauliZ spinDown = -spinDown := by
  ext i
  fin_cases i <;>
    simp [applyMat, pauliZ, spinDown, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem chiralBoostZ_on_spinUp (α : ℝ) :
    applyMat (chiralBoostZ α) spinUp = (Real.exp (α / 2) : ℂ) • spinUp := by
  unfold chiralBoostZ
  rw [applyMat_add_mat, applyMat_smul_mat, applyMat_one, applyMat_smul_mat,
    pauliZ_spinUp, ← add_smul]
  have h : (Real.cosh (α / 2) : ℂ) + (Real.sinh (α / 2) : ℂ) =
      (Real.exp (α / 2) : ℂ) := by
    rw [← ofReal_add, Real.cosh_add_sinh, ofReal_exp]
  rw [h]

private theorem chiralBoostZ_on_spinDown (α : ℝ) :
    applyMat (chiralBoostZ α) spinDown =
      (Real.exp (-(α / 2)) : ℂ) • spinDown := by
  unfold chiralBoostZ
  rw [applyMat_add_mat, applyMat_smul_mat, applyMat_one, applyMat_smul_mat,
    pauliZ_spinDown, smul_neg]
  have hsub : (Real.cosh (α / 2) : ℂ) - (Real.sinh (α / 2) : ℂ) =
      (Real.exp (-(α / 2)) : ℂ) := by
    have h : Real.cosh (α / 2) - Real.sinh (α / 2) = Real.exp (-(α / 2)) := by
      have hexp := Real.cosh_add_sinh (-(α / 2))
      rw [Real.cosh_neg, Real.sinh_neg, ← sub_eq_add_neg] at hexp
      exact hexp
    rw [← ofReal_sub, h, ofReal_exp]
  rw [← sub_eq_add_neg, ← sub_smul, hsub]

private theorem boosted_spin_upper (α : ℝ) (u : DualSpinor) :
    diracUpper (applyDiracBoostZ α (restParticleSpinor u)) =
      applyMat (chiralBoostZ α) u := by
  rw [boosted_blocks, diracUpper_add, diracUpper_weylUpper, diracUpper_weylLower,
    add_zero]

private theorem boosted_spin_lower (α : ℝ) (u : DualSpinor) :
    diracLower (applyDiracBoostZ α (restParticleSpinor u)) =
      I • applyMat (chiralBoostZ (-α)) u := by
  rw [boosted_blocks, diracLower_add, diracLower_weylUpper, diracLower_weylLower,
    zero_add]

/-- Upper block of the boosted eigenvalue \(+1\): the factor \(e^{\alpha/2}\). -/
theorem boostedRest_spinUp_upper (α : ℝ) :
    diracUpper (applyDiracBoostZ α (restParticleSpinor spinUp)) =
      (Real.exp (α / 2) : ℂ) • spinUp := by
  rw [boosted_spin_upper, chiralBoostZ_on_spinUp]

/-- Lower block of the boosted eigenvalue \(+1\): the factor \(e^{-\alpha/2}\). -/
theorem boostedRest_spinUp_lower (α : ℝ) :
    diracLower (applyDiracBoostZ α (restParticleSpinor spinUp)) =
      I • (Real.exp (-(α / 2)) : ℂ) • spinUp := by
  rw [boosted_spin_lower, chiralBoostZ_on_spinUp]
  have harg : (-α) / 2 = -(α / 2) := by ring
  rw [harg]

/-- Upper block of the boosted eigenvalue \(-1\): the factor \(e^{-\alpha/2}\). -/
theorem boostedRest_spinDown_upper (α : ℝ) :
    diracUpper (applyDiracBoostZ α (restParticleSpinor spinDown)) =
      (Real.exp (-(α / 2)) : ℂ) • spinDown :=
  by rw [boosted_spin_upper, chiralBoostZ_on_spinDown]

/-- Lower block of the boosted eigenvalue \(-1\): the factor \(e^{\alpha/2}\). -/
theorem boostedRest_spinDown_lower (α : ℝ) :
    diracLower (applyDiracBoostZ α (restParticleSpinor spinDown)) =
      I • (Real.exp (α / 2) : ℂ) • spinDown := by
  rw [boosted_spin_lower, chiralBoostZ_on_spinDown]
  have harg : -(-α / 2) = α / 2 := by ring
  rw [harg]

private theorem exp_half_phase (θ : ℝ) :
    (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * -I =
      Complex.exp ((-↑(θ / 2)) * I) := by
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

private theorem exp_half_phase_down (θ : ℝ) :
    (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * I =
      Complex.exp (↑(θ / 2) * I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem real_smul_complex_mat (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    r • A = (r : ℂ) • A :=
  (algebraMap_smul ℂ r A).symm

private theorem cyclicRep_two_spinUp : applyMat (cyclicRep 2) spinUp = -I • spinUp := by
  rw [cyclicRep_two_eq]
  ext i
  fin_cases i <;>
    simp [applyMat, spinUp, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem cyclicRep_two_spinDown : applyMat (cyclicRep 2) spinDown = I • spinDown := by
  rw [cyclicRep_two_eq]
  ext i
  fin_cases i <;>
    simp [applyMat, spinDown, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Dual rotation about the boost axis multiplies the eigenvalue \(+1\) by a phase. -/
theorem dualRotor_axis2_spinUp (θ : ℝ) :
    applyMat (dualRotorMat (EuclideanSpace.single 2 θ)) spinUp =
      Complex.exp ((-↑(θ / 2)) * I) • spinUp := by
  rw [dualRotorMat_axis2_rodrigues, real_smul_complex_mat, real_smul_complex_mat,
    applyMat_add_mat, applyMat_smul_mat, applyMat_one, applyMat_smul_mat,
    cyclicRep_two_spinUp, smul_smul, ← add_smul, exp_half_phase]

/-- Dual rotation about the boost axis multiplies the eigenvalue \(-1\) by the opposite phase. -/
theorem dualRotor_axis2_spinDown (θ : ℝ) :
    applyMat (dualRotorMat (EuclideanSpace.single 2 θ)) spinDown =
      Complex.exp (↑(θ / 2) * I) • spinDown := by
  rw [dualRotorMat_axis2_rodrigues, real_smul_complex_mat, real_smul_complex_mat,
    applyMat_add_mat, applyMat_smul_mat, applyMat_one, applyMat_smul_mat,
    cyclicRep_two_spinDown, smul_smul, ← add_smul, exp_half_phase_down]

/-- A dual rotation of angle \(\pi\) about a perpendicular axis exchanges the two rays. -/
theorem dualRotor_axis0_pi_exchange :
    applyMat (dualRotorMat (EuclideanSpace.single 0 Real.pi)) spinUp =
        -I • spinDown ∧
      applyMat (dualRotorMat (EuclideanSpace.single 0 Real.pi)) spinDown =
        -I • spinUp := by
  rw [dualRotorMat_axis0_rodrigues, Real.cos_pi_div_two, Real.sin_pi_div_two,
    cyclicRep_zero_eq]
  constructor
  · ext i
    fin_cases i <;>
      simp [applyMat, spinUp, spinDown, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.add_apply, Matrix.smul_apply]
  · ext i
    fin_cases i <;>
      simp [applyMat, spinUp, spinDown, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.add_apply, Matrix.smul_apply]

/-- After a same-axis dual rotation, the boosted upper block stays in the ray of eigenvalue \(+1\). -/
theorem boostedRest_axis2_spinUp_upper (α θ : ℝ) :
    diracUpper (applyDiracBoostZ α
        (restParticleSpinor
          (applyMat (dualRotorMat (EuclideanSpace.single 2 θ)) spinUp))) =
      (Complex.exp ((-↑(θ / 2)) * I) * (Real.exp (α / 2) : ℂ)) • spinUp := by
  rw [boosted_spin_upper, dualRotor_axis2_spinUp, applyMat_smul, chiralBoostZ_on_spinUp,
    smul_smul]

/-- After a perpendicular dual rotation of angle \(\pi\), the boosted upper block lies in the opposite ray. -/
theorem boostedRest_axis0_pi_spinUp_upper (α : ℝ) :
    diracUpper (applyDiracBoostZ α
        (restParticleSpinor
          (applyMat (dualRotorMat (EuclideanSpace.single 0 Real.pi)) spinUp))) =
      (-I * (Real.exp (-(α / 2)) : ℂ)) • spinDown := by
  rw [boosted_spin_upper, dualRotor_axis0_pi_exchange.1, applyMat_smul,
    chiralBoostZ_on_spinDown, smul_smul]

/-- Opposite spin rays have vanishing invariant mass bilinear at every longitudinal rapidity. -/
theorem boostedRest_oppositeSpin_scalar (α : ℝ) :
    diracScalar
        (applyDiracBoostZ α (restParticleSpinor spinUp))
        (applyDiracBoostZ α (restParticleSpinor spinDown)) = 0 := by
  rw [boostedRest_diracScalar, spinUp_inner_spinDown, mul_zero]

/-- Opposite spin rays carry no Dirac current into each other. -/
theorem boostedRest_oppositeSpin_current (α : ℝ) (μ : Fin 4) :
    diracCurrent μ
        (applyDiracBoostZ α (restParticleSpinor spinUp))
        (applyDiracBoostZ α (restParticleSpinor spinDown)) = 0 := by
  fin_cases μ
  · change diracCurrent 0
        (applyDiracBoostZ α (restParticleSpinor spinUp))
        (applyDiracBoostZ α (restParticleSpinor spinDown)) = 0
    rw [boostedRest_current_zero, boostedRest_oppositeSpin_scalar, mul_zero]
  · change diracCurrent 1
        (applyDiracBoostZ α (restParticleSpinor spinUp))
        (applyDiracBoostZ α (restParticleSpinor spinDown)) = 0
    exact boostedRest_current_one α spinUp spinDown
  · change diracCurrent 2
        (applyDiracBoostZ α (restParticleSpinor spinUp))
        (applyDiracBoostZ α (restParticleSpinor spinDown)) = 0
    exact boostedRest_current_two α spinUp spinDown
  · change diracCurrent 3
        (applyDiracBoostZ α (restParticleSpinor spinUp))
        (applyDiracBoostZ α (restParticleSpinor spinDown)) = 0
    rw [boostedRest_current_three, boostedRest_oppositeSpin_scalar, mul_zero]

end Logic

end DstDiophantine
