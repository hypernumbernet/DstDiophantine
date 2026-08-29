import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.PGA.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Motors, Ω decomposition, and null exponential truncation

The translational exponential truncates at first order because the null sector is
strongly nilpotent (`N_μ N_ν = 0`). Torsion rotors use the Banach-algebra exponential.

## What is proved vs. paper narrative

* **Proved here:** the *definitional* factorisation `motor p := rotorTorsion *
  expTrans`, together with `rotor_unitary`, `expTrans_unitary`, and
  `motor_unitary` for that product.
* **Proved here:** closed forms `exp(t • x)` when `x * x = ±1`, and the
  left-inverse ⇒ right-inverse lemma for unitary motors (`m * reverse m = 1`).
* **Proved here:** the Banach exponential truncates, `exp(Ω_trans) = 1 + Ω_trans`,
  translators multiply by adding coefficients, and `exp(Ω_biv) = RT` whenever
  torsion and translation commute.
* **Not identified in general:** `motor p` with `exp(omegaBiv p)` when
  `[Ω_torsion, Ω_trans] ≠ 0`.  A closed motor product law for mixed
  torsion-plus-translation parameters is likewise not claimed.
* Sandwich metric preservation for the full degenerate quadratic form is likewise
  not claimed.
-/

namespace DstDiophantine

open CliffordAlgebra PGA Generators Operations NormedSpace

namespace Motor

structure TransParams where
  lambda : Fin 4 → ℝ

structure OmegaParams where
  torsion : TorsionParams
  trans : TransParams

/-- Torsion part `Ω_torsion = ∑ (αₐ/2) B⁺ₐ + (βₐ/2) B⁻ₐ`. -/
noncomputable def omegaTorsion (p : TorsionParams) : PGA :=
  ∑ a : Fin 3, ((p.alpha a / 2) • hyperbolic a + (p.beta a / 2) • cyclic a)

/-- Translational part `Ω_trans = ∑ (λ^μ/2) N_μ`. -/
noncomputable def omegaTrans (p : TransParams) : PGA :=
  ∑ μ : Fin 4, (p.lambda μ / 2) • null μ

/-- Full five-dimensional bivector generator `Ω_biv⁽⁵⁾`. -/
noncomputable def omegaBiv (p : OmegaParams) : PGA :=
  omegaTorsion p.torsion + omegaTrans p.trans

theorem omegaTorsion_reverse (p : TorsionParams) :
    reverse (omegaTorsion p) = -omegaTorsion p := by
  simp only [omegaTorsion, map_sum, map_smul, map_add, hyperbolic_reverse, cyclic_reverse]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext a
  simp [neg_add_rev, add_comm]

/-- Helper for the deferred `reverse_exp_of_reverse_neg` proof. -/
theorem reverse_pow (x : PGA) (n : ℕ) : reverse (x ^ n) = (reverse x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, CliffordAlgebra.reverse.map_mul, ih, pow_succ (reverse x)]
    exact (Commute.pow_right (Commute.refl (reverse x)) n).eq

theorem reverse_pow_of_reverse_neg (x : PGA) (hx : reverse x = -x) (n : ℕ) :
    reverse (x ^ n) = (-x) ^ n := by
  rw [reverse_pow, hx]

theorem omegaTrans_sq (p : TransParams) : omegaTrans p * omegaTrans p = 0 := by
  simp [omegaTrans, Finset.sum_mul_sum, null_mul_null]

theorem omegaTrans_mul (p q : TransParams) : omegaTrans p * omegaTrans q = 0 := by
  simp [omegaTrans, Finset.sum_mul_sum, null_mul_null]

theorem omegaTrans_add (p q : TransParams) :
    omegaTrans p + omegaTrans q = omegaTrans ⟨fun μ => p.lambda μ + q.lambda μ⟩ := by
  simp only [omegaTrans, Finset.sum_add_distrib, add_smul, add_div]

/-- First-order null exponential: `exp(Ω_trans) = 1 + Ω_trans`. -/
noncomputable def expTrans (p : TransParams) : PGA :=
  1 + omegaTrans p

theorem expTrans_eq (p : TransParams) :
    expTrans p = 1 + omegaTrans p := rfl

/-- Torsion rotor `R = exp(Ω_torsion)`. -/
noncomputable def rotorTorsion (p : TorsionParams) : PGA :=
  exp (omegaTorsion p)

/-- `reverse(exp x) = exp(-x)` when `reverse x = -x`. -/
theorem reverse_exp_of_reverse_neg {x : PGA} (hx : reverse x = -x) :
    reverse (exp x) = exp (-x) := by
  set revOp := CliffordAlgebra.reverseOp (Q := Q311)
  have hcont : Continuous revOp := revOp.toLinearMap.continuous_of_finiteDimensional
  calc
    reverse (exp x) = (revOp (exp x)).unop :=
      (CliffordAlgebra.unop_reverseOp (Q := Q311) (exp x)).symm
    _ = (exp (revOp x)).unop := by rw [map_exp revOp hcont]
    _ = (exp (MulOpposite.op (reverse x))).unop := by rw [CliffordAlgebra.op_reverse (Q := Q311)]
    _ = (exp (MulOpposite.op (-x))).unop := by rw [hx]
    _ = exp (-x) := by rw [← MulOpposite.unop_op (exp (-x)), ← exp_op (-x)]

/-! ### Left inverse implies right inverse for unitary motors -/

/-- If `m * reverse m = 1`, then also `reverse m * m = 1`
(finite-dimensional: left-invertible ⇒ right-invertible). -/
theorem reverse_mul_of_mul_reverse {m : PGA} (h : m * reverse m = 1) :
    reverse m * m = 1 := by
  have hsurj : Function.Surjective (LinearMap.mulLeft ℝ m) := by
    intro y
    refine ⟨reverse m * y, ?_⟩
    simp [LinearMap.mulLeft_apply, ← mul_assoc, h]
  have hinj : Function.Injective (LinearMap.mulLeft ℝ m) :=
    (LinearMap.injective_iff_surjective (f := LinearMap.mulLeft ℝ m)).2 hsurj
  have : LinearMap.mulLeft ℝ m (reverse m * m) = LinearMap.mulLeft ℝ m 1 := by
    simp [LinearMap.mulLeft_apply, ← mul_assoc, h]
  exact hinj this

/-! ### Closed-form exponentials for generators with `x² = ±1` -/

private theorem hasDerivAt_exp_neg_smul (x : PGA) (u : ℝ) :
    HasDerivAt (fun v : ℝ => exp ((-v) • x)) (exp ((-u) • x) * (-x)) u := by
  have h : HasDerivAt (fun v : ℝ => exp (v • (-x))) (exp (u • (-x)) * (-x)) u :=
    hasDerivAt_exp_smul_const (-x) u
  have hfun : (fun v : ℝ => exp ((-v) • x)) = fun v : ℝ => exp (v • (-x)) :=
    funext fun v => by rw [neg_smul, smul_neg]
  simpa [hfun, neg_smul, smul_neg] using h

private theorem exp_smul_mul_exp_neg_smul (x : PGA) (t : ℝ) :
    exp (t • x) * exp ((-t) • x) = 1 := by
  have hc : Commute (t • x) ((-t) • x) :=
    ((Commute.refl x).smul_left t).smul_right (-t)
  rw [← exp_add_of_commute hc, ← add_smul, add_neg_cancel, zero_smul, exp_zero]

/-- Hyperbolic closed form: `x² = 1 ⇒ exp(t • x) = cosh t + sinh t • x`. -/
theorem exp_of_sq_one {x : PGA} (hx : x * x = 1) (t : ℝ) :
    exp (t • x) = Real.cosh t • (1 : PGA) + Real.sinh t • x := by
  let R : ℝ → PGA := fun u => Real.cosh u • (1 : PGA) + Real.sinh u • x
  let f : ℝ → PGA := fun u => exp ((-u) • x) * R u
  have hRx (u : ℝ) : x * R u = Real.sinh u • (1 : PGA) + Real.cosh u • x := by
    simp only [R, mul_add]
    have h1 : x * (Real.cosh u • (1 : PGA)) = Real.cosh u • x := by
      rw [mul_smul_comm, mul_one]
    have h2 : x * (Real.sinh u • x) = Real.sinh u • (1 : PGA) := by
      rw [mul_smul_comm, hx]
    rw [h1, h2, add_comm]
  have hR' (u : ℝ) :
      HasDerivAt R (Real.sinh u • (1 : PGA) + Real.cosh u • x) u := by
    exact ((Real.hasDerivAt_cosh u).smul_const (1 : PGA)).add
      ((Real.hasDerivAt_sinh u).smul_const x)
  have hf' (u : ℝ) : HasDerivAt f 0 u := by
    have hexp := hasDerivAt_exp_neg_smul x u
    have hmul :
        HasDerivAt ((fun v => exp ((-v) • x)) * R)
          (exp ((-u) • x) * (-x) * R u +
            exp ((-u) • x) * (Real.sinh u • (1 : PGA) + Real.cosh u • x)) u :=
      hexp.mul (hR' u)
    have hzero :
        exp ((-u) • x) * (-x) * R u +
          exp ((-u) • x) * (Real.sinh u • (1 : PGA) + Real.cosh u • x) = 0 := by
      calc
        exp ((-u) • x) * (-x) * R u +
              exp ((-u) • x) * (Real.sinh u • (1 : PGA) + Real.cosh u • x)
            = exp ((-u) • x) * ((-x) * R u) + exp ((-u) • x) * (x * R u) := by
              rw [mul_assoc, hRx]
        _ = exp ((-u) • x) * ((-x) * R u + x * R u) := by
              rw [← mul_add]
        _ = exp ((-u) • x) * (-(x * R u) + x * R u) := by
              rw [neg_mul]
        _ = exp ((-u) • x) * 0 := by
              rw [neg_add_cancel]
        _ = 0 := mul_zero _
    convert hmul using 2
    · rfl
    · exact hzero.symm
  have hf0 : f 0 = 1 := by
    simp only [f, R, neg_zero, zero_smul, exp_zero, Real.cosh_zero, Real.sinh_zero,
      one_smul, zero_smul, add_zero, mul_one]
  have hdiff : Differentiable ℝ f := fun u => (hf' u).differentiableAt
  have hderiv : ∀ u, deriv f u = 0 := fun u => (hf' u).deriv
  have hf_one : ∀ u, f u = 1 := fun u =>
    (is_const_of_deriv_eq_zero hdiff hderiv u 0).trans hf0
  have : exp ((-t) • x) * R t = 1 := hf_one t
  calc
    exp (t • x) = exp (t • x) * 1 := (mul_one _).symm
    _ = exp (t • x) * (exp ((-t) • x) * R t) := by rw [this]
    _ = (exp (t • x) * exp ((-t) • x)) * R t := by rw [mul_assoc]
    _ = 1 * R t := by rw [exp_smul_mul_exp_neg_smul]
    _ = R t := one_mul _

/-- Circular closed form: `x² = -1 ⇒ exp(t • x) = cos t + sin t • x`. -/
theorem exp_of_sq_neg_one {x : PGA} (hx : x * x = -1) (t : ℝ) :
    exp (t • x) = Real.cos t • (1 : PGA) + Real.sin t • x := by
  let R : ℝ → PGA := fun u => Real.cos u • (1 : PGA) + Real.sin u • x
  let f : ℝ → PGA := fun u => exp ((-u) • x) * R u
  have hRx (u : ℝ) : x * R u = (-Real.sin u) • (1 : PGA) + Real.cos u • x := by
    simp only [R, mul_add]
    have h1 : x * (Real.cos u • (1 : PGA)) = Real.cos u • x := by
      rw [mul_smul_comm, mul_one]
    have h2 : x * (Real.sin u • x) = (-Real.sin u) • (1 : PGA) := by
      rw [mul_smul_comm, hx, smul_neg, neg_smul]
    rw [h1, h2, add_comm]
  have hR' (u : ℝ) :
      HasDerivAt R ((-Real.sin u) • (1 : PGA) + Real.cos u • x) u :=
    ((Real.hasDerivAt_cos u).smul_const (1 : PGA)).add
      ((Real.hasDerivAt_sin u).smul_const x)
  have hf' (u : ℝ) : HasDerivAt f 0 u := by
    have hexp := hasDerivAt_exp_neg_smul x u
    have hmul :
        HasDerivAt ((fun v => exp ((-v) • x)) * R)
          (exp ((-u) • x) * (-x) * R u +
            exp ((-u) • x) * ((-Real.sin u) • (1 : PGA) + Real.cos u • x)) u :=
      hexp.mul (hR' u)
    have hzero :
        exp ((-u) • x) * (-x) * R u +
          exp ((-u) • x) * ((-Real.sin u) • (1 : PGA) + Real.cos u • x) = 0 := by
      calc
        exp ((-u) • x) * (-x) * R u +
              exp ((-u) • x) * ((-Real.sin u) • (1 : PGA) + Real.cos u • x)
            = exp ((-u) • x) * ((-x) * R u) + exp ((-u) • x) * (x * R u) := by
              rw [mul_assoc, hRx]
        _ = exp ((-u) • x) * ((-x) * R u + x * R u) := by
              rw [← mul_add]
        _ = exp ((-u) • x) * (-(x * R u) + x * R u) := by
              rw [neg_mul]
        _ = exp ((-u) • x) * 0 := by
              rw [neg_add_cancel]
        _ = 0 := mul_zero _
    convert hmul using 2
    · rfl
    · exact hzero.symm
  have hf0 : f 0 = 1 := by
    simp only [f, R, neg_zero, zero_smul, exp_zero, Real.cos_zero, Real.sin_zero,
      one_smul, zero_smul, add_zero, mul_one]
  have hdiff : Differentiable ℝ f := fun u => (hf' u).differentiableAt
  have hderiv : ∀ u, deriv f u = 0 := fun u => (hf' u).deriv
  have hf_one : ∀ u, f u = 1 := fun u =>
    (is_const_of_deriv_eq_zero hdiff hderiv u 0).trans hf0
  have : exp ((-t) • x) * R t = 1 := hf_one t
  calc
    exp (t • x) = exp (t • x) * 1 := (mul_one _).symm
    _ = exp (t • x) * (exp ((-t) • x) * R t) := by rw [this]
    _ = (exp (t • x) * exp ((-t) • x)) * R t := by rw [mul_assoc]
    _ = 1 * R t := by rw [exp_smul_mul_exp_neg_smul]
    _ = R t := one_mul _

theorem rotor_unitary (p : TorsionParams) :
    rotorTorsion p * reverse (rotorTorsion p) = 1 := by
  dsimp [rotorTorsion]
  rw [reverse_exp_of_reverse_neg (omegaTorsion_reverse p)]
  rw [← exp_add_of_commute (Commute.neg_right (Commute.refl (omegaTorsion p)))]
  simp

/-- Motor split `M := R · T` at the **definition** level (not `exp(Ω_biv)`). -/
noncomputable def motor (p : OmegaParams) : PGA :=
  rotorTorsion p.torsion * expTrans p.trans

/-- Null translator is unitary: `(1+Ω_trans)(1+Ω_trans)˜ = 1`. -/
theorem expTrans_unitary (p : TransParams) :
    expTrans p * reverse (expTrans p) = 1 := by
  have hrev : reverse (omegaTrans p) = -omegaTrans p := by
    simp only [omegaTrans, map_sum, map_smul, null_reverse]
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext μ
    rw [smul_neg]
  simp [expTrans, CliffordAlgebra.reverse.map_add, CliffordAlgebra.reverse.map_one, hrev,
    mul_add, add_mul, omegaTrans_sq, mul_neg]

theorem motor_unitary (p : OmegaParams) :
    motor p * reverse (motor p) = 1 := by
  simp only [motor, CliffordAlgebra.reverse.map_mul]
  calc
    rotorTorsion p.torsion * expTrans p.trans *
        (reverse (expTrans p.trans) * reverse (rotorTorsion p.torsion))
        = rotorTorsion p.torsion * (expTrans p.trans * reverse (expTrans p.trans)) *
            reverse (rotorTorsion p.torsion) := by
              rw [← mul_assoc, mul_assoc (rotorTorsion p.torsion) (expTrans p.trans)
                (reverse (expTrans p.trans))]
    _ = rotorTorsion p.torsion * reverse (rotorTorsion p.torsion) := by
              rw [expTrans_unitary, mul_one]
    _ = 1 := rotor_unitary p.torsion

theorem motor_factorization (p : OmegaParams) :
    motor p = rotorTorsion p.torsion * expTrans p.trans := rfl

/-! ### Null exponential is the Banach exponential -/

theorem omegaTrans_smul_mul (p : TransParams) (t u : ℝ) :
    (t • omegaTrans p) * (u • omegaTrans p) = 0 := by
  rw [mul_smul_comm, smul_mul_assoc, omegaTrans_sq, smul_zero, smul_zero]

/-- First-order truncation: \(\exp(t\,\Omega_{\mathrm{trans}})=1+t\,\Omega_{\mathrm{trans}}\). -/
theorem exp_smul_omegaTrans (p : TransParams) (t : ℝ) :
    exp (t • omegaTrans p) = (1 : PGA) + t • omegaTrans p := by
  set Ω := omegaTrans p
  have hsq : Ω * Ω = 0 := omegaTrans_sq p
  let R : ℝ → PGA := fun u => (1 : PGA) + u • Ω
  let f : ℝ → PGA := fun u => exp ((-u) • Ω) * R u
  have hRΩ (u : ℝ) : Ω * R u = Ω := by
    simp only [R, mul_add, mul_one]
    rw [mul_smul_comm, hsq, smul_zero, add_zero]
  have hR' (u : ℝ) : HasDerivAt R Ω u := by
    have hconst : HasDerivAt (fun _ : ℝ => (1 : PGA)) 0 u := hasDerivAt_const u (1 : PGA)
    have hid : HasDerivAt (fun v : ℝ => v • Ω) Ω u := by
      simpa using (hasDerivAt_id u).smul_const Ω
    have hsum : R = (fun _ : ℝ => (1 : PGA)) + fun v => v • Ω := rfl
    rw [hsum]
    have hadd := hconst.add hid
    simpa using hadd
  have hf' (u : ℝ) : HasDerivAt f 0 u := by
    have hexp := hasDerivAt_exp_neg_smul Ω u
    have hmul :
        HasDerivAt ((fun v => exp ((-v) • Ω)) * R)
          (exp ((-u) • Ω) * (-Ω) * R u + exp ((-u) • Ω) * Ω) u :=
      hexp.mul (hR' u)
    have hzero :
        exp ((-u) • Ω) * (-Ω) * R u + exp ((-u) • Ω) * Ω = 0 := by
      calc
        exp ((-u) • Ω) * (-Ω) * R u + exp ((-u) • Ω) * Ω
            = exp ((-u) • Ω) * ((-Ω) * R u) + exp ((-u) • Ω) * Ω := by
              rw [mul_assoc]
        _ = exp ((-u) • Ω) * ((-Ω) * R u + Ω) := by rw [← mul_add]
        _ = exp ((-u) • Ω) * (-(Ω * R u) + Ω) := by rw [neg_mul]
        _ = exp ((-u) • Ω) * (-Ω + Ω) := by rw [hRΩ]
        _ = exp ((-u) • Ω) * 0 := by rw [neg_add_cancel]
        _ = 0 := mul_zero _
    convert hmul using 2
    · rfl
    · exact hzero.symm
  have hf0 : f 0 = 1 := by
    simp only [f, R, neg_zero, zero_smul, exp_zero, zero_smul, add_zero, mul_one]
  have hdiff : Differentiable ℝ f := fun u => (hf' u).differentiableAt
  have hderiv : ∀ u, deriv f u = 0 := fun u => (hf' u).deriv
  have hf_one : ∀ u, f u = 1 := fun u =>
    (is_const_of_deriv_eq_zero hdiff hderiv u 0).trans hf0
  have : exp ((-t) • Ω) * R t = 1 := hf_one t
  calc
    exp (t • Ω) = exp (t • Ω) * 1 := (mul_one _).symm
    _ = exp (t • Ω) * (exp ((-t) • Ω) * R t) := by rw [this]
    _ = (exp (t • Ω) * exp ((-t) • Ω)) * R t := by rw [mul_assoc]
    _ = 1 * R t := by rw [exp_smul_mul_exp_neg_smul]
    _ = R t := one_mul _

/-- The Banach exponential of a null generator truncates at first order. -/
theorem exp_omegaTrans (p : TransParams) :
    exp (omegaTrans p) = expTrans p := by
  simpa [expTrans, one_smul] using exp_smul_omegaTrans p 1

/-- Translators form an abelian group: coefficients add. -/
theorem expTrans_mul (p q : TransParams) :
    expTrans p * expTrans q =
      expTrans ⟨fun μ => p.lambda μ + q.lambda μ⟩ := by
  simp only [expTrans, mul_add, add_mul, mul_one, one_mul, omegaTrans_mul, add_zero]
  rw [add_assoc, omegaTrans_add]

/-- When torsion and translation commute, \(\exp(\Omega_{\mathrm{biv}})=RT\). -/
theorem exp_omegaBiv_eq_motor_of_commute (p : OmegaParams)
    (h : Commute (omegaTorsion p.torsion) (omegaTrans p.trans)) :
    exp (omegaBiv p) = motor p := by
  rw [omegaBiv, motor, rotorTorsion, exp_add_of_commute h, exp_omegaTrans]

end Motor

end DstDiophantine
