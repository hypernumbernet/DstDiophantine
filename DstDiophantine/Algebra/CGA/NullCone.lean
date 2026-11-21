import DstDiophantine.Algebra.CGA.QuadraticForm
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Null pair for 1D CGA

Null infinity and the origin are grade-1 vectors in `Cl(2,1)`.
-/

namespace DstDiophantine

namespace CGA

open CliffordAlgebra

/-- 1D conformal geometric algebra Cl(2,1). -/
abbrev CGA1 := CliffordAlgebra Q21

namespace CGA1

/-- Index of e₋ (Q = -1). -/
def eMinusIndex : Fin 3 := 0

/-- Index of the Euclidean line basis e (Q = +1). -/
def eIndex : Fin 3 := 1

/-- Index of e₊ (Q = +1). -/
def ePlusIndex : Fin 3 := 2

noncomputable def ι (μ : Fin 3) : CGA1 :=
  CliffordAlgebra.ι Q21 (e3vec μ)

theorem e_sq (μ : Fin 3) : ι μ * ι μ = algebraMap ℝ CGA1 (Q21 (e3vec μ)) :=
  ι_sq_scalar (Q := Q21) (e3vec μ)

theorem eMinus_sq : ι eMinusIndex * ι eMinusIndex = algebraMap ℝ CGA1 (-1 : ℝ) := by
  simp [e_sq, Q21_e3vec, w21, eMinusIndex]

theorem e_sq_one : ι eIndex * ι eIndex = (1 : CGA1) := by
  simp [e_sq, Q21_e3vec, w21, eIndex]

theorem ePlus_sq : ι ePlusIndex * ι ePlusIndex = (1 : CGA1) := by
  simp [e_sq, Q21_e3vec, w21, ePlusIndex]

theorem e_anticomm {i j : Fin 3} (hij : i ≠ j) :
    ι i * ι j + ι j * ι i = 0 :=
  ι_mul_ι_add_swap_of_isOrtho (Q := Q21) (Q21_isOrtho_basis i j hij)

/-- Euclidean line generator (grade 1). -/
noncomputable def eLine : CGA1 := ι eIndex

/-- Underlying vector for null infinity: (1, 0, -1). -/
def nInfVec : Vec3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => -1

/-- Underlying vector for null origin: (1/2, 0, 1/2). -/
noncomputable def n0Vec : Vec3
  | ⟨0, _⟩ => 1 / 2
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1 / 2

/-- Euclidean line vector: (0, 1, 0). -/
def eLineVec : Vec3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

theorem Q21_nInfVec : Q21 nInfVec = 0 := by
  simp only [Q21, QuadraticMap.weightedSumSquares_apply, nInfVec, w21]
  rw [Fin.sum_univ_three]
  norm_num

theorem Q21_n0Vec : Q21 n0Vec = 0 := by
  simp only [Q21, QuadraticMap.weightedSumSquares_apply, n0Vec, w21]
  rw [Fin.sum_univ_three]
  norm_num

/-- Null infinity ∞. -/
noncomputable def nInf : CGA1 :=
  CliffordAlgebra.ι Q21 nInfVec

/-- Null origin ₀. -/
noncomputable def n0 : CGA1 :=
  CliffordAlgebra.ι Q21 n0Vec

theorem nInf_sq : nInf * nInf = 0 := by
  unfold nInf
  rw [ι_sq_scalar (Q := Q21) nInfVec, Q21_nInfVec, map_zero]

theorem n0_sq : n0 * n0 = 0 := by
  unfold n0
  rw [ι_sq_scalar (Q := Q21) n0Vec, Q21_n0Vec, map_zero]

/-- Conformal point `X(x) = n₀ + x e + (1/2) x² n∞`. -/
noncomputable def pointVec (x : ℝ) : Vec3 :=
  fun i =>
    match i with
    | ⟨0, _⟩ => 1 / 2 + (1 / 2) * x ^ 2
    | ⟨1, _⟩ => x
    | ⟨2, _⟩ => 1 / 2 - (1 / 2) * x ^ 2

theorem pointVec_eq (x : ℝ) :
    pointVec x = n0Vec + x • eLineVec + ((1 / 2) * x ^ 2) • nInfVec := by
  funext i
  fin_cases i
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply]
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply]
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply]; try ring

theorem Q21_pointVec (x : ℝ) : Q21 (pointVec x) = 0 := by
  simp only [Q21, QuadraticMap.weightedSumSquares_apply, pointVec, w21]
  rw [Fin.sum_univ_three]
  ring

/-- Grade-1 conformal point embedding. -/
noncomputable def point (x : ℝ) : CGA1 :=
  CliffordAlgebra.ι Q21 (pointVec x)

theorem point_sq (x : ℝ) : point x * point x = 0 := by
  unfold point
  rw [ι_sq_scalar (Q := Q21) (pointVec x), Q21_pointVec x, map_zero]

theorem pointVec_smul_weights (c x : ℝ) :
    pointVec (c * x) =
      n0Vec + c • (x • eLineVec) + (c ^ 2) • ((1 / 2 * x ^ 2) • nInfVec) := by
  funext i
  fin_cases i
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply, smul_smul]; try ring
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply, smul_smul]
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply, smul_smul]; try ring

theorem pointVec_mul (m n : ℤ) :
    pointVec ((m * n : ℤ) : ℝ) =
      n0Vec + ((m : ℝ) * (n : ℝ)) • eLineVec
        + (1 / 2 * ((m : ℝ) * (n : ℝ)) ^ 2) • nInfVec := by
  rw [Int.cast_mul, pointVec_eq]

theorem point_mul (m n : ℤ) :
    point ((m * n : ℤ) : ℝ) =
      CliffordAlgebra.ι Q21
        (n0Vec + ((m : ℝ) * (n : ℝ)) • eLineVec
          + (1 / 2 * ((m : ℝ) * (n : ℝ)) ^ 2) • nInfVec) := by
  unfold point
  rw [pointVec_mul]

/-! ### Polar pairing and injectivity -/

/-- Symmetric bilinear form polarising `Q21`: `B(u,v) = -u₀v₀ + u₁v₁ + u₂v₂`. -/
noncomputable def bilin21 (u v : Vec3) : ℝ :=
  (Q21 (u + v) - Q21 u - Q21 v) / 2

theorem bilin21_eq (u v : Vec3) :
    bilin21 u v = -(u 0) * (v 0) + (u 1) * (v 1) + (u 2) * (v 2) := by
  simp only [bilin21, Q21, QuadraticMap.weightedSumSquares_apply, w21, Pi.add_apply]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  ring

theorem bilin21_pointVec_nInf (x : ℝ) : bilin21 (pointVec x) nInfVec = -1 := by
  simp only [bilin21_eq, pointVec, nInfVec]
  ring

theorem bilin21_pointVec_n0 (x : ℝ) : bilin21 (pointVec x) n0Vec = -(x ^ 2) / 2 := by
  simp only [bilin21_eq, pointVec, n0Vec]
  ring

theorem pointVec_eLine (x : ℝ) : pointVec x eIndex = x := by
  simp [pointVec, eIndex]

theorem pointVec_injective : Function.Injective pointVec := by
  intro x y h
  have := congr_fun h eIndex
  simpa [pointVec_eLine] using this

theorem pointVec_dilation_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective fun δ : ℝ => pointVec (Real.exp δ * a) := by
  intro δ₁ δ₂ h
  have hxy : Real.exp δ₁ * a = Real.exp δ₂ * a := by
    simpa [pointVec_eLine] using congr_fun h eIndex
  have : Real.exp δ₁ = Real.exp δ₂ :=
    mul_right_cancel₀ (ne_of_gt ha) hxy
  exact Real.exp_injective this

/-- Not `2π`-periodic on null-cone seeds, unlike a rapidity torus. -/
theorem pointVec_dilation_not_two_pi_periodic {a : ℝ} (ha : 0 < a) (δ : ℝ) :
    pointVec (Real.exp (δ + 2 * Real.pi) * a) ≠
      pointVec (Real.exp δ * a) := by
  intro h
  have hinj := pointVec_dilation_injective ha h
  have : δ + 2 * Real.pi = δ := hinj
  linarith [Real.pi_pos]

theorem pointVec_exp_nat_mul (a δ : ℝ) (k : ℕ) :
    pointVec (Real.exp ((k : ℝ) * δ) * a) =
      pointVec (Real.exp δ ^ k * a) :=
  congrArg (fun t => pointVec (t * a)) (Real.exp_nat_mul δ k)

/-! ### Point–point pairing and scale-invariant dilation mismatch -/

theorem bilin21_pointVec_pointVec (x y : ℝ) :
    bilin21 (pointVec x) (pointVec y) = -((x - y) ^ 2) / 2 := by
  simp only [bilin21_eq, pointVec]
  ring

/-- Scale-invariant mismatch `(e^δ - 1)²`, independent of the positive seed. -/
noncomputable def cgaDilationMismatch (δ : ℝ) : ℝ :=
  (Real.exp δ - 1) ^ 2

theorem bilin21_pointVec_dilation (a δ : ℝ) (ha : 0 < a) :
    bilin21 (pointVec a) (pointVec (Real.exp δ * a)) =
      -(a ^ 2) * cgaDilationMismatch δ / 2 := by
  have h := bilin21_pointVec_pointVec a (Real.exp δ * a)
  have hdiff : a - Real.exp δ * a = a * (1 - Real.exp δ) := by ring
  rw [h, hdiff]
  unfold cgaDilationMismatch
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp [ha0]
  ring

theorem cgaDilationMismatch_eq_of_pos (a δ : ℝ) (ha : 0 < a) :
    cgaDilationMismatch δ =
      -2 * bilin21 (pointVec a) (pointVec (Real.exp δ * a)) / a ^ 2 := by
  have h := bilin21_pointVec_dilation a δ ha
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ha)
  unfold cgaDilationMismatch at h ⊢
  field_simp [ha2] at h ⊢
  linarith [h]

theorem cgaDilationMismatch_pos_of_ne_zero {δ : ℝ} (hδ : δ ≠ 0) :
    0 < cgaDilationMismatch δ := by
  unfold cgaDilationMismatch
  have : Real.exp δ ≠ 1 := by
    intro heq
    have : δ = 0 := Real.exp_injective (heq.trans (Real.exp_zero).symm)
    exact hδ this
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr this)

theorem cgaDilationMismatch_balanced (m : ℕ) (hm : 0 < m) :
    cgaDilationMismatch (Real.log 2 / (m : ℝ)) =
      ((2 : ℝ) ^ ((1 : ℝ) / m) - 1) ^ 2 := by
  unfold cgaDilationMismatch
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have hlog : Real.log 2 / (m : ℝ) = Real.log (2 ^ ((1 : ℝ) / m)) := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    rw [Real.log_rpow h2]
    field_simp [hm0]
  rw [hlog, Real.exp_log (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]

theorem cgaDilationMismatch_balanced_pos (m : ℕ) (hm : 0 < m) :
    0 < cgaDilationMismatch (Real.log 2 / (m : ℝ)) := by
  rw [cgaDilationMismatch_balanced m hm]
  have hpow : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / m) :=
    Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2)
      (div_pos (by norm_num : (0 : ℝ) < 1) (Nat.cast_pos.mpr hm))
  exact sq_pos_of_pos (sub_pos.mpr hpow)

/-! ### Integer dilation group on the null cone -/

/-- Multiplicative dilation of a null-cone coordinate by scale `c`. -/
noncomputable def cgaDilation (c x : ℝ) : Vec3 :=
  pointVec (c * x)

theorem cgaDilation_eq (c x : ℝ) :
    cgaDilation c x = pointVec (c * x) :=
  rfl

theorem cgaDilation_smul_weights (c x : ℝ) :
    cgaDilation c x =
      n0Vec + c • (x • eLineVec) + (c ^ 2) • ((1 / 2 * x ^ 2) • nInfVec) :=
  pointVec_smul_weights c x

theorem cgaDilation_scale_unique {α γ : ℝ} (hα : 0 < α) (_hγ : 0 < γ) :
    cgaDilation (γ / α) α = pointVec γ := by
  unfold cgaDilation
  have : (γ / α) * α = γ := div_mul_cancel₀ γ (ne_of_gt hα)
  rw [this]

theorem cgaDilation_scale_of_eq {α γ c : ℝ} (hα : 0 < α)
    (heq : cgaDilation c α = pointVec γ) : c = γ / α := by
  have hxy : c * α = γ := by
    simpa [cgaDilation, pointVec_eLine] using congr_fun heq eIndex
  exact (eq_div_iff (ne_of_gt hα)).mpr hxy

end CGA1

end CGA

end DstDiophantine
