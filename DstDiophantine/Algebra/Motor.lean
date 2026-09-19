import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.PGA.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.IteratedFDeriv
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
* **Proved here:** the full torsion–null commutator table lands in the null span;
  `[Ω_trans,[Ω_torsion,Ω_trans]]=0`; Baker–Campbell–Hausdorff jets of `RT` versus
  the truncated BCH exponential agree through order three, with the first
  correction `½[Ω_torsion,Ω_trans]`; and `exp(Ω_biv) ≠ RT` in general (radial
  boost against time translation).
* **Proved in `DstDiophantine.Algebra.MotorGroup`:** the group-level consequences:
  every torsion rotor normalises the translators (`R T R˜ = T'`), motors multiply in
  semidirect form `(R_p T_p)(R_q T_q) = (R_p R_q) T'`, and `exp(Ω_biv)` is itself a
  motor `R · T_dressed` with the *same* torsion rotor and a dressed translation
  (which differs from `Ω_trans` in general, consistent with `exists_omegaBiv_ne_motor`).
* Not claimed: a fully closed parametrised product law on `OmegaParams` (this would
  need surjectivity of `exp` from `lorentzSpan` onto the rotor group).
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

/-! ### Null ideal and low-order BCH -/

theorem omegaTrans_mem_nullSpan (p : TransParams) :
    omegaTrans p ∈ nullSpan := by
  simp only [omegaTrans]
  refine Submodule.sum_mem _ fun μ _ => ?_
  exact smul_mem_nullSpan _ (mem_nullSpan μ)

theorem commutator_hyperbolic_omegaTrans_mem_span (a : Fin 3) (p : TransParams) :
    Generators.commutator (hyperbolic a) (omegaTrans p) ∈ nullSpan := by
  simp only [omegaTrans, commutator_sum_right]
  refine Submodule.sum_mem _ fun μ _ => ?_
  rw [commutator_smul_right]
  exact smul_mem_nullSpan _ (commutator_hyperbolic_null_mem_span a μ)

theorem commutator_cyclic_omegaTrans_mem_span (a : Fin 3) (p : TransParams) :
    Generators.commutator (cyclic a) (omegaTrans p) ∈ nullSpan := by
  simp only [omegaTrans, commutator_sum_right]
  refine Submodule.sum_mem _ fun μ _ => ?_
  rw [commutator_smul_right]
  exact smul_mem_nullSpan _ (commutator_cyclic_null_mem_span a μ)

/-- The mismatch commutator remains translational. -/
theorem commutator_omegaTorsion_omegaTrans_mem_span (t : TorsionParams) (p : TransParams) :
    Generators.commutator (omegaTorsion t) (omegaTrans p) ∈ nullSpan := by
  simp only [omegaTorsion, commutator_sum_left]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [commutator_add_left, commutator_smul_left, commutator_smul_left]
  exact add_mem (smul_mem_nullSpan _ (commutator_hyperbolic_omegaTrans_mem_span a p))
    (smul_mem_nullSpan _ (commutator_cyclic_omegaTrans_mem_span a p))

/-- Nested `[Ω_trans,[Ω_torsion,Ω_trans]]` vanishes: the null sector is abelian. -/
theorem commutator_omegaTrans_commutator_torsion_trans
    (t : TorsionParams) (p : TransParams) :
    Generators.commutator (omegaTrans p)
      (Generators.commutator (omegaTorsion t) (omegaTrans p)) = 0 := by
  set C := Generators.commutator (omegaTorsion t) (omegaTrans p)
  have hx := omegaTrans_mem_nullSpan p
  have hy : C ∈ nullSpan := commutator_omegaTorsion_omegaTrans_mem_span t p
  dsimp [Generators.commutator]
  rw [nullSpan_mul hx hy, nullSpan_mul hy hx, sub_zero]

theorem commutator_omegaTorsion_commutator_mem_span
    (t : TorsionParams) (p : TransParams) :
    Generators.commutator (omegaTorsion t)
      (Generators.commutator (omegaTorsion t) (omegaTrans p)) ∈ nullSpan := by
  have hy := commutator_omegaTorsion_omegaTrans_mem_span t p
  refine Submodule.span_induction
    (p := fun z _ => Generators.commutator (omegaTorsion t) z ∈ nullSpan)
    ?mem ?zero ?add ?smul hy
  · intro z hz
    obtain ⟨μ, rfl⟩ := hz
    simp only [omegaTorsion, commutator_sum_left]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [commutator_add_left, commutator_smul_left, commutator_smul_left]
    exact add_mem (smul_mem_nullSpan _ (commutator_hyperbolic_null_mem_span a μ))
      (smul_mem_nullSpan _ (commutator_cyclic_null_mem_span a μ))
  · simp [Generators.commutator]
  · intro x y _ _ hx hy
    simpa [commutator_add_right] using add_mem hx hy
  · intro c x _ hx
    simpa [commutator_smul_right] using smul_mem_nullSpan c hx

theorem omegaTrans_mul_mul (p : TransParams) (z : PGA) :
    omegaTrans p * z * omegaTrans p = 0 :=
  nullSpan_mul_mul (omegaTrans_mem_nullSpan p) (omegaTrans_mem_nullSpan p) z

private theorem hasFDerivAt_exp_zero_pga :
    HasFDerivAt (exp : PGA → PGA) (1 : PGA →L[ℝ] PGA) 0 :=
  hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := PGA)

private theorem hasDerivAt_one_add_smul (y : PGA) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (1 : PGA) + u • y) y t := by
  have h : HasDerivAt (fun u : ℝ => u • y) y t := by
    simpa using (hasDerivAt_id t).smul_const y
  exact h.const_add (1 : PGA)

private theorem smul_invTwo_add (z : PGA) :
    (2⁻¹ : ℝ) • z + z = (3 / 2 : ℝ) • z := by
  calc
    (2⁻¹ : ℝ) • z + z = (2⁻¹ : ℝ) • z + (1 : ℝ) • z := by rw [one_smul]
    _ = ((2⁻¹ : ℝ) + 1) • z := (add_smul _ _ _).symm
    _ = (3 / 2 : ℝ) • z := by congr 1; norm_num

private theorem three_smul_eq (z : PGA) : (3 : ℝ) • z = z + z + z := by
  rw [show (3 : ℝ) = (2 : ℝ) + 1 by norm_num, add_smul, two_smul, one_smul]

noncomputable def motorPath (p : OmegaParams) (t : ℝ) : PGA :=
  exp (t • omegaTorsion p.torsion) * exp (t • omegaTrans p.trans)

private theorem motorPath_eq (p : OmegaParams) (t : ℝ) :
    motorPath p t =
      exp (t • omegaTorsion p.torsion) * ((1 : PGA) + t • omegaTrans p.trans) := by
  simp [motorPath, exp_smul_omegaTrans]

private theorem hasDerivAt_motorPath (p : OmegaParams) (t : ℝ) :
    HasDerivAt (motorPath p)
      (exp (t • omegaTorsion p.torsion) *
        (omegaTorsion p.torsion * ((1 : PGA) + t • omegaTrans p.trans) +
          omegaTrans p.trans)) t := by
  have hL := hasDerivAt_exp_smul_const (omegaTorsion p.torsion) t
  have hR := hasDerivAt_one_add_smul (omegaTrans p.trans) t
  have hfun : motorPath p = (fun u => exp (u • omegaTorsion p.torsion)) *
      (fun u => (1 : PGA) + u • omegaTrans p.trans) := by
    ext u
    exact motorPath_eq p u
  rw [hfun]
  exact (hL.mul hR).congr_deriv (by simp [mul_add, mul_assoc])

private theorem motorPath_zero (p : OmegaParams) : motorPath p 0 = 1 := by
  simp [motorPath, zero_smul, exp_zero]

private theorem deriv_motorPath_zero (p : OmegaParams) :
    deriv (motorPath p) 0 = omegaBiv p := by
  have h := (hasDerivAt_motorPath p 0).deriv
  simp [omegaBiv, h, zero_smul, exp_zero]

private theorem hasDerivAt_deriv_motorPath (p : OmegaParams) (t : ℝ) :
    HasDerivAt (deriv (motorPath p))
      (exp (t • omegaTorsion p.torsion) *
        (omegaTorsion p.torsion * omegaTorsion p.torsion *
            ((1 : PGA) + t • omegaTrans p.trans) +
          (2 : ℝ) • (omegaTorsion p.torsion * omegaTrans p.trans))) t := by
  have hfun : deriv (motorPath p) = fun u =>
      exp (u • omegaTorsion p.torsion) *
        (omegaTorsion p.torsion * ((1 : PGA) + u • omegaTrans p.trans) +
          omegaTrans p.trans) := by
    ext u
    exact (hasDerivAt_motorPath p u).deriv
  have hL := hasDerivAt_exp_smul_const (omegaTorsion p.torsion) t
  have hlin : HasDerivAt
      (fun u : ℝ => omegaTorsion p.torsion * ((1 : PGA) + u • omegaTrans p.trans) +
        omegaTrans p.trans)
      (omegaTorsion p.torsion * omegaTrans p.trans) t := by
    have hadd := hasDerivAt_one_add_smul (omegaTrans p.trans) t
    have hmul := hadd.const_mul (omegaTorsion p.torsion)
    exact (hmul.add_const (omegaTrans p.trans)).congr_deriv (by simp)
  have hprod := hL.mul hlin
  -- product rule: exp' * lin + exp * lin' = exp * X * lin + exp * (X Y)
  have : exp (t • omegaTorsion p.torsion) * omegaTorsion p.torsion *
        (omegaTorsion p.torsion * ((1 : PGA) + t • omegaTrans p.trans) +
          omegaTrans p.trans) +
      exp (t • omegaTorsion p.torsion) * (omegaTorsion p.torsion * omegaTrans p.trans) =
      exp (t • omegaTorsion p.torsion) *
        (omegaTorsion p.torsion * omegaTorsion p.torsion *
            ((1 : PGA) + t • omegaTrans p.trans) +
          (2 : ℝ) • (omegaTorsion p.torsion * omegaTrans p.trans)) := by
    simp [mul_add, two_smul, mul_assoc]
    abel
  rw [hfun]
  exact hprod.congr_deriv this

private theorem iteratedDeriv_two_motorPath_zero (p : OmegaParams) :
    iteratedDeriv 2 (motorPath p) 0 =
      omegaTorsion p.torsion * omegaTorsion p.torsion +
        (2 : ℝ) • (omegaTorsion p.torsion * omegaTrans p.trans) := by
  have h := (hasDerivAt_deriv_motorPath p 0).deriv
  simp [iteratedDeriv_succ, iteratedDeriv_zero, h, zero_smul, exp_zero]

noncomputable def bch2Arg (p : OmegaParams) (t : ℝ) : PGA :=
  t • omegaBiv p + (t ^ 2 / 2) •
    Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)

noncomputable def bch2Path (p : OmegaParams) (t : ℝ) : PGA :=
  exp (bch2Arg p t)

noncomputable def bch3Arg (p : OmegaParams) (t : ℝ) : PGA :=
  t • omegaBiv p +
    (t ^ 2 / 2) • Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) +
    (t ^ 3 / 12) • Generators.commutator (omegaTorsion p.torsion)
      (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans))

noncomputable def bch3Path (p : OmegaParams) (t : ℝ) : PGA :=
  exp (bch3Arg p t)

private theorem hasDerivAt_pow_two_div (t : ℝ) :
    HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t :=
  ((hasDerivAt_pow 2 t).div_const (2 : ℝ)).congr_deriv (by simp [pow_one])

private theorem hasDerivAt_pow_three_div_twelve (t : ℝ) :
    HasDerivAt (fun u : ℝ => u ^ 3 / 12) (t ^ 2 / 4) t :=
  ((hasDerivAt_pow 3 t).div_const (12 : ℝ)).congr_deriv (by simp [pow_two]; ring)

private theorem hasDerivAt_pow_two_div_four (t : ℝ) :
    HasDerivAt (fun u : ℝ => u ^ 2 / 4) (t / 2) t :=
  ((hasDerivAt_pow 2 t).div_const (4 : ℝ)).congr_deriv (by simp [pow_one]; ring)

private theorem hasDerivAt_bch2Arg (p : OmegaParams) (t : ℝ) :
    HasDerivAt (bch2Arg p)
      (omegaBiv p + t • Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)) t := by
  have h1 : HasDerivAt (fun u : ℝ => u • omegaBiv p) (omegaBiv p) t := by
    simpa using (hasDerivAt_id t).smul_const (omegaBiv p)
  have h2 := (hasDerivAt_pow_two_div t).smul_const
    (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans))
  have hfun : bch2Arg p =
      (fun u : ℝ => u • omegaBiv p) + fun u =>
        (u ^ 2 / 2) • Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) := rfl
  rw [hfun]
  simpa using h1.add h2

private theorem bch2Arg_zero (p : OmegaParams) : bch2Arg p 0 = 0 := by
  simp [bch2Arg]

private theorem deriv_bch2Arg_zero (p : OmegaParams) :
    deriv (bch2Arg p) 0 = omegaBiv p := by
  simpa using (hasDerivAt_bch2Arg p 0).deriv

private theorem iteratedDeriv_two_bch2Arg (p : OmegaParams) :
    iteratedDeriv 2 (bch2Arg p) 0 =
      Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) := by
  have hfun : deriv (bch2Arg p) = fun t =>
      omegaBiv p + t • Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) := by
    ext t
    exact (hasDerivAt_bch2Arg p t).deriv
  have h2 : HasDerivAt (fun t : ℝ =>
      omegaBiv p + t • Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans))
      (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)) 0 := by
    have hC : HasDerivAt (fun t : ℝ =>
        t • Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans))
        (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const
        (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans))
    exact hC.const_add (omegaBiv p)
  simp [iteratedDeriv_succ, hfun, h2.deriv]

private theorem contDiff_bch2Arg (p : OmegaParams) : ContDiff ℝ ⊤ (bch2Arg p) := by
  unfold bch2Arg
  fun_prop

private theorem iteratedFDeriv_two_exp_diag (A : PGA) :
    iteratedFDeriv ℝ 2 (exp : PGA → PGA) 0 (fun _ => A) = A * A := by
  have h := (exp_hasFPowerSeriesOnBall (𝕂 := ℝ) (𝔸 := PGA)).factorial_smul A 2
  have hser : expSeries ℝ PGA 2 (fun _ => A) = (2⁻¹ : ℝ) • (A * A) := by
    simp [expSeries_apply_eq, pow_two, Nat.factorial]
  rw [← h, hser, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num [Nat.factorial]

private theorem iteratedFDeriv_three_exp_diag (A : PGA) :
    iteratedFDeriv ℝ 3 (exp : PGA → PGA) 0 (fun _ => A) = A * A * A := by
  have h := (exp_hasFPowerSeriesOnBall (𝕂 := ℝ) (𝔸 := PGA)).factorial_smul A 3
  have hser : expSeries ℝ PGA 3 (fun _ => A) = (6⁻¹ : ℝ) • (A * A * A) := by
    rw [expSeries_apply_eq]
    simp [Nat.factorial, pow_three, mul_assoc]
  rw [← h, hser, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num [Nat.factorial]

private theorem perm_fin_two_eq (σ : Equiv.Perm (Fin 2)) :
    σ = 1 ∨ σ = Equiv.swap (0 : Fin 2) 1 := by
  have hset : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap (0 : Fin 2) 1} := by
    decide
  have hσ : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 2))) := Finset.mem_univ _
  rw [hset, Finset.mem_insert, Finset.mem_singleton] at hσ
  exact hσ

private theorem expSeries_two_apply (x y : PGA) :
    expSeries ℝ PGA 2 ![x, y] = (2⁻¹ : ℝ) • (x * y) := by
  simp [expSeries, ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]

private theorem iteratedFDeriv_two_exp (v w : PGA) :
    iteratedFDeriv ℝ 2 (exp : PGA → PGA) 0 ![v, w] =
      (2⁻¹ : ℝ) • (v * w + w * v) := by
  have hps := exp_hasFPowerSeriesOnBall (𝕂 := ℝ) (𝔸 := PGA)
  rw [hps.iteratedFDeriv_eq_sum_of_completeSpace (v := ![v, w])]
  have hset : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap (0 : Fin 2) 1} := by
    ext σ
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    exact perm_fin_two_eq σ
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have := congrArg (fun σ : Equiv.Perm (Fin 2) => σ 0) h
    simp at this
  rw [hset, Finset.sum_pair hne]
  have hterm (σ : Equiv.Perm (Fin 2)) :
      expSeries ℝ PGA 2 (fun i => (![v, w] : Fin 2 → PGA) (σ i)) =
        (2⁻¹ : ℝ) • ((![v, w] : Fin 2 → PGA) (σ 0) * (![v, w] : Fin 2 → PGA) (σ 1)) := by
    simp [expSeries, ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [hterm 1, hterm (Equiv.swap (0 : Fin 2) 1)]
  simp [Equiv.swap_apply_left, Equiv.swap_apply_right, smul_add]

private theorem deriv_bch2Path_zero (p : OmegaParams) :
    deriv (bch2Path p) 0 = omegaBiv p := by
  have hu := hasDerivAt_bch2Arg p 0
  have hexp : HasFDerivAt (exp : PGA → PGA) (1 : PGA →L[ℝ] PGA) (bch2Arg p 0) := by
    rw [bch2Arg_zero]; exact hasFDerivAt_exp_zero_pga
  have hcomp := hexp.comp_hasDerivAt (x := 0) hu
  have hφ : bch2Path p = (exp : PGA → PGA) ∘ bch2Arg p := rfl
  rw [hφ, hcomp.deriv, one_apply_eq_self]
  simp

private theorem iteratedDeriv_two_bch2Path_zero (p : OmegaParams) :
    iteratedDeriv 2 (bch2Path p) 0 =
      omegaBiv p * omegaBiv p +
        Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) := by
  set A := omegaBiv p
  set C := Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)
  have hg : ContDiffAt ℝ 2 (exp : PGA → PGA) (bch2Arg p 0) :=
    (exp_analytic (𝕂 := ℝ) (bch2Arg p 0)).contDiffAt
  have hf : ContDiffAt ℝ 2 (bch2Arg p) 0 :=
    (contDiff_bch2Arg p).contDiffAt.of_le le_top
  have hcomp := iteratedDeriv_vcomp_two (g := (exp : PGA → PGA)) (f := bch2Arg p) hg hf
  have hpath : bch2Path p = (exp : PGA → PGA) ∘ bch2Arg p := rfl
  rw [hpath, hcomp, bch2Arg_zero, deriv_bch2Arg_zero, iteratedDeriv_two_bch2Arg]
  have hid : fderiv ℝ (exp : PGA → PGA) 0 C = C := by
    rw [hasFDerivAt_exp_zero_pga.fderiv]
    simp
  rw [hid, iteratedFDeriv_two_exp_diag]

/-- The product `RT` and the second-order BCH exponential share a 2-jet at vanishing scale. -/
theorem motor_bch2_jet (p : OmegaParams) :
    motorPath p 0 = bch2Path p 0 ∧
      deriv (motorPath p) 0 = deriv (bch2Path p) 0 ∧
      iteratedDeriv 2 (motorPath p) 0 = iteratedDeriv 2 (bch2Path p) 0 := by
  have hY : omegaTrans p.trans * omegaTrans p.trans = 0 := omegaTrans_sq p.trans
  have hA : omegaBiv p * omegaBiv p +
      Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) =
        omegaTorsion p.torsion * omegaTorsion p.torsion +
          (2 : ℝ) • (omegaTorsion p.torsion * omegaTrans p.trans) := by
    simp [omegaBiv, Generators.commutator, mul_add, add_mul, hY, two_smul]
    abel
  refine ⟨?_, ?_, ?_⟩
  · simp [motorPath_zero, bch2Path, bch2Arg_zero, exp_zero]
  · rw [deriv_motorPath_zero, deriv_bch2Path_zero]
  · rw [iteratedDeriv_two_motorPath_zero, iteratedDeriv_two_bch2Path_zero, hA]

private theorem iteratedDeriv_two_motorPath_eq (p : OmegaParams) (t : ℝ) :
    iteratedDeriv 2 (motorPath p) t =
      exp (t • omegaTorsion p.torsion) *
        (omegaTorsion p.torsion * omegaTorsion p.torsion *
            ((1 : PGA) + t • omegaTrans p.trans) +
          (2 : ℝ) • (omegaTorsion p.torsion * omegaTrans p.trans)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, (hasDerivAt_deriv_motorPath p t).deriv]

private theorem hasDerivAt_iteratedDeriv_two_motorPath (p : OmegaParams) (t : ℝ) :
    HasDerivAt (iteratedDeriv 2 (motorPath p))
      (exp (t • omegaTorsion p.torsion) *
        (omegaTorsion p.torsion * omegaTorsion p.torsion * omegaTorsion p.torsion *
            ((1 : PGA) + t • omegaTrans p.trans) +
          (3 : ℝ) • (omegaTorsion p.torsion * omegaTorsion p.torsion *
            omegaTrans p.trans))) t := by
  set X := omegaTorsion p.torsion
  set Y := omegaTrans p.trans
  have hfun : iteratedDeriv 2 (motorPath p) = fun u =>
      exp (u • X) * (X * X * ((1 : PGA) + u • Y) + (2 : ℝ) • (X * Y)) := by
    ext u
    simpa [X, Y] using iteratedDeriv_two_motorPath_eq p u
  have hL := hasDerivAt_exp_smul_const X t
  have hR : HasDerivAt
      (fun u : ℝ => X * X * ((1 : PGA) + u • Y) + (2 : ℝ) • (X * Y))
      (X * X * Y) t := by
    have hadd := hasDerivAt_one_add_smul Y t
    have hmul := hadd.const_mul (X * X)
    exact (hmul.add_const ((2 : ℝ) • (X * Y))).congr_deriv (by simp [mul_assoc])
  have hprod := hL.mul hR
  have : exp (t • X) * X * (X * X * ((1 : PGA) + t • Y) + (2 : ℝ) • (X * Y)) +
      exp (t • X) * (X * X * Y) =
      exp (t • X) * (X * X * X * ((1 : PGA) + t • Y) +
        (3 : ℝ) • (X * X * Y)) := by
    simp [mul_add, two_smul, three_smul_eq, mul_assoc]
    abel
  rw [hfun]
  exact hprod.congr_deriv this

private theorem iteratedDeriv_three_motorPath_zero (p : OmegaParams) :
    iteratedDeriv 3 (motorPath p) 0 =
      omegaTorsion p.torsion * omegaTorsion p.torsion * omegaTorsion p.torsion +
        (3 : ℝ) • (omegaTorsion p.torsion * omegaTorsion p.torsion *
          omegaTrans p.trans) := by
  have h := (hasDerivAt_iteratedDeriv_two_motorPath p 0).deriv
  rw [iteratedDeriv_succ, h]
  simp [zero_smul, exp_zero]

private theorem hasDerivAt_bch3Arg (p : OmegaParams) (t : ℝ) :
    HasDerivAt (bch3Arg p)
      (omegaBiv p +
        t • Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) +
        (t ^ 2 / 4) • Generators.commutator (omegaTorsion p.torsion)
          (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans))) t := by
  have h1 : HasDerivAt (fun u : ℝ => u • omegaBiv p) (omegaBiv p) t := by
    simpa using (hasDerivAt_id t).smul_const (omegaBiv p)
  have h2 := (hasDerivAt_pow_two_div t).smul_const
    (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans))
  have h3 := (hasDerivAt_pow_three_div_twelve t).smul_const
    (Generators.commutator (omegaTorsion p.torsion)
      (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)))
  have hfun : bch3Arg p =
      ((fun u : ℝ => u • omegaBiv p) + fun u =>
        (u ^ 2 / 2) • Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)) +
        fun u =>
          (u ^ 3 / 12) • Generators.commutator (omegaTorsion p.torsion)
            (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)) := rfl
  rw [hfun]
  simpa using (h1.add h2).add h3

private theorem bch3Arg_zero (p : OmegaParams) : bch3Arg p 0 = 0 := by
  simp [bch3Arg]

private theorem deriv_bch3Arg_zero (p : OmegaParams) :
    deriv (bch3Arg p) 0 = omegaBiv p := by
  simpa using (hasDerivAt_bch3Arg p 0).deriv

private theorem iteratedDeriv_two_bch3Arg (p : OmegaParams) :
    iteratedDeriv 2 (bch3Arg p) 0 =
      Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) := by
  set C := Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)
  set K := Generators.commutator (omegaTorsion p.torsion) C
  have hfun : deriv (bch3Arg p) = fun t =>
      omegaBiv p + t • C + (t ^ 2 / 4) • K := by
    ext t
    simpa [C, K] using (hasDerivAt_bch3Arg p t).deriv
  have h2 : HasDerivAt (fun t : ℝ => omegaBiv p + t • C + (t ^ 2 / 4) • K)
      (C + (0 / 2) • K) 0 := by
    have hC : HasDerivAt (fun t : ℝ => t • C) C 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const C
    have hK := (hasDerivAt_pow_two_div_four 0).smul_const K
    have hsum : HasDerivAt (fun t : ℝ => t • C + (t ^ 2 / 4) • K) (C + (0 / 2) • K) 0 := by
      have hfg : (fun t : ℝ => t • C + (t ^ 2 / 4) • K) =
          (fun t : ℝ => t • C) + fun t => (t ^ 2 / 4) • K := rfl
      rw [hfg]
      simpa using hC.add hK
    have hfun' : (fun t : ℝ => omegaBiv p + t • C + (t ^ 2 / 4) • K) =
        fun t => omegaBiv p + (t • C + (t ^ 2 / 4) • K) :=
        funext fun t => add_assoc _ _ _
    rw [hfun']
    exact hsum.const_add (omegaBiv p)
  simp [iteratedDeriv_succ, hfun, h2.deriv]

private theorem iteratedDeriv_three_bch3Arg (p : OmegaParams) :
    iteratedDeriv 3 (bch3Arg p) 0 =
      (2⁻¹ : ℝ) • Generators.commutator (omegaTorsion p.torsion)
        (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)) := by
  set C := Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)
  set K := Generators.commutator (omegaTorsion p.torsion) C
  have hfun : iteratedDeriv 2 (bch3Arg p) = fun t => C + (t / 2) • K := by
    ext t
    have hder : deriv (bch3Arg p) = fun u =>
        omegaBiv p + u • C + (u ^ 2 / 4) • K := by
      ext u
      simpa [C, K] using (hasDerivAt_bch3Arg p u).deriv
    have h2 : HasDerivAt (fun u : ℝ => omegaBiv p + u • C + (u ^ 2 / 4) • K)
        (C + (t / 2) • K) t := by
      have hC : HasDerivAt (fun u : ℝ => u • C) C t := by
        simpa using (hasDerivAt_id t).smul_const C
      have hK := (hasDerivAt_pow_two_div_four t).smul_const K
      have hsum : HasDerivAt (fun u : ℝ => u • C + (u ^ 2 / 4) • K) (C + (t / 2) • K) t := by
        have hfg : (fun u : ℝ => u • C + (u ^ 2 / 4) • K) =
            (fun u : ℝ => u • C) + fun u => (u ^ 2 / 4) • K := rfl
        rw [hfg]
        simpa using hC.add hK
      have hfun' : (fun u : ℝ => omegaBiv p + u • C + (u ^ 2 / 4) • K) =
          fun u => omegaBiv p + (u • C + (u ^ 2 / 4) • K) :=
        funext fun u => add_assoc _ _ _
      rw [hfun']
      exact hsum.const_add (omegaBiv p)
    rw [iteratedDeriv_succ, iteratedDeriv_one, hder, h2.deriv]
  have h3 : HasDerivAt (fun t : ℝ => C + (t / 2) • K) ((2⁻¹ : ℝ) • K) 0 := by
    have hd : HasDerivAt (fun t : ℝ => (t / 2) • K) ((2⁻¹ : ℝ) • K) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).smul_const K
    exact hd.const_add C
  rw [iteratedDeriv_succ, hfun, h3.deriv]

private theorem contDiff_bch3Arg (p : OmegaParams) : ContDiff ℝ ⊤ (bch3Arg p) := by
  unfold bch3Arg
  fun_prop

private theorem bch3_bracket_algebra (X Y : PGA) (hY : Y * Y = 0)
    (hYXY : Y * X * Y = 0) :
    let A := X + Y
    let C := X * Y - Y * X
    let K := X * C - C * X
    A * A * A + (3 / 2 : ℝ) • (A * C + C * A) + (2⁻¹ : ℝ) • K =
      X * X * X + (3 : ℝ) • (X * X * Y) := by
  intro A C K
  have hsq : A * A = X * X + X * Y + Y * X := by
    simp [A, mul_add, add_mul, hY]
    abel
  have hA3 : A * A * A = X * X * X + X * X * Y + X * Y * X + Y * X * X := by
    nth_rw 1 [hsq]
    simp [A, mul_add, add_mul, hY, hYXY, mul_assoc]
    abel
  have hAC1 : A * C = X * X * Y - X * Y * X := by
    have h1 : (X + Y) * (X * Y) = X * X * Y := by
      rw [add_mul, ← mul_assoc Y, hYXY, add_zero]
      simp [mul_assoc]
    have h2 : (X + Y) * (Y * X) = X * Y * X := by
      rw [add_mul, ← mul_assoc Y, hY, zero_mul, add_zero]
      simp [mul_assoc]
    simp [A, C, mul_sub, h1, h2]
  have hCA1 : C * A = X * Y * X - Y * X * X := by
    have h1 : (X * Y) * (X + Y) = X * Y * X := by
      rw [mul_add]
      have : X * Y * Y = 0 := by simp [mul_assoc, hY]
      rw [this, add_zero]
    have h2 : (Y * X) * (X + Y) = Y * X * X := by
      rw [mul_add, hYXY, add_zero]
    simp [A, C, sub_mul, h1, h2]
  have hAC : A * C + C * A = X * X * Y - Y * X * X := by
    rw [hAC1, hCA1]
    abel
  have hK : K = X * X * Y - (2 : ℝ) • (X * Y * X) + Y * X * X := by
    simp [K, C, mul_sub, sub_mul, two_smul, mul_assoc]
    abel
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  apply smul_right_injective (M := PGA) h2
  have h21 : (2 : ℝ) * (3 / 2) = 3 := by norm_num
  simp [smul_add, smul_smul, h21, one_smul, hA3, hAC, hK, two_smul, three_smul_eq,
    smul_sub]
  abel

private theorem iteratedDeriv_three_bch3Path_zero (p : OmegaParams) :
    iteratedDeriv 3 (bch3Path p) 0 =
      omegaTorsion p.torsion * omegaTorsion p.torsion * omegaTorsion p.torsion +
        (3 : ℝ) • (omegaTorsion p.torsion * omegaTorsion p.torsion *
          omegaTrans p.trans) := by
  set X := omegaTorsion p.torsion
  set Y := omegaTrans p.trans
  set A := omegaBiv p
  set C := Generators.commutator X Y
  set K := Generators.commutator X C
  have hg : ContDiffAt ℝ 3 (exp : PGA → PGA) (bch3Arg p 0) :=
    (exp_analytic (𝕂 := ℝ) (bch3Arg p 0)).contDiffAt
  have hf : ContDiffAt ℝ 3 (bch3Arg p) 0 :=
    (contDiff_bch3Arg p).contDiffAt.of_le le_top
  have hcomp := iteratedDeriv_vcomp_three (g := (exp : PGA → PGA)) (f := bch3Arg p) hg hf
  have hpath : bch3Path p = (exp : PGA → PGA) ∘ bch3Arg p := rfl
  rw [hpath, hcomp, bch3Arg_zero, deriv_bch3Arg_zero, iteratedDeriv_two_bch3Arg,
    iteratedDeriv_three_bch3Arg]
  have hid : fderiv ℝ (exp : PGA → PGA) 0 ((2⁻¹ : ℝ) • K) = (2⁻¹ : ℝ) • K := by
    rw [hasFDerivAt_exp_zero_pga.fderiv]
    simp
  have hA : A = X + Y := rfl
  have hCdef : C = X * Y - Y * X := rfl
  have hKdef : K = X * C - C * X := rfl
  rw [hid, iteratedFDeriv_three_exp_diag, iteratedFDeriv_two_exp C A,
    iteratedFDeriv_two_exp A C]
  have hY : Y * Y = 0 := omegaTrans_sq p.trans
  have hYXY : Y * X * Y = 0 := omegaTrans_mul_mul p.trans X
  have hAlg := bch3_bracket_algebra X Y hY hYXY
  have hsym : C * A + A * C = A * C + C * A := add_comm _ _
  have hscale : (2 : ℝ) • ((2⁻¹ : ℝ) • (A * C + C * A)) = A * C + C * A := by
    rw [smul_smul]; norm_num
  calc
    A * A * A + (2⁻¹ : ℝ) • (C * A + A * C) +
        (2 : ℝ) • ((2⁻¹ : ℝ) • (A * C + C * A)) + (2⁻¹ : ℝ) • K
        = A * A * A + (2⁻¹ : ℝ) • (A * C + C * A) + (A * C + C * A) + (2⁻¹ : ℝ) • K := by
          rw [hsym, hscale]
    _ = A * A * A + (3 / 2 : ℝ) • (A * C + C * A) + (2⁻¹ : ℝ) • K := by
          rw [add_assoc (A * A * A), smul_invTwo_add]
    _ = X * X * X + (3 : ℝ) • (X * X * Y) := by
          simpa [hA, hCdef, hKdef] using hAlg

/-- The product `RT` and the third-order BCH exponential share a 3-jet at vanishing scale. -/
theorem motor_bch3_jet (p : OmegaParams) :
    motorPath p 0 = bch3Path p 0 ∧
      deriv (motorPath p) 0 = deriv (bch3Path p) 0 ∧
      iteratedDeriv 2 (motorPath p) 0 = iteratedDeriv 2 (bch3Path p) 0 ∧
      iteratedDeriv 3 (motorPath p) 0 = iteratedDeriv 3 (bch3Path p) 0 := by
  have hg : ContDiffAt ℝ 2 (exp : PGA → PGA) (bch3Arg p 0) :=
    (exp_analytic (𝕂 := ℝ) (bch3Arg p 0)).contDiffAt
  have hf : ContDiffAt ℝ 2 (bch3Arg p) 0 :=
    (contDiff_bch3Arg p).contDiffAt.of_le le_top
  have h2 := iteratedDeriv_vcomp_two (g := (exp : PGA → PGA)) (f := bch3Arg p) hg hf
  have hpath : bch3Path p = (exp : PGA → PGA) ∘ bch3Arg p := rfl
  have hY : omegaTrans p.trans * omegaTrans p.trans = 0 := omegaTrans_sq p.trans
  have hA : omegaBiv p * omegaBiv p +
      Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) =
        omegaTorsion p.torsion * omegaTorsion p.torsion +
          (2 : ℝ) • (omegaTorsion p.torsion * omegaTrans p.trans) := by
    simp [omegaBiv, Generators.commutator, mul_add, add_mul, hY, two_smul]
    abel
  have hder : deriv (bch3Path p) 0 = omegaBiv p := by
    have hu := hasDerivAt_bch3Arg p 0
    have hexp : HasFDerivAt (exp : PGA → PGA) (1 : PGA →L[ℝ] PGA) (bch3Arg p 0) := by
      rw [bch3Arg_zero]; exact hasFDerivAt_exp_zero_pga
    have hcomp := hexp.comp_hasDerivAt (x := 0) hu
    have hφ : bch3Path p = (exp : PGA → PGA) ∘ bch3Arg p := rfl
    rw [hφ, hcomp.deriv, one_apply_eq_self]
    simp
  have h2eq : iteratedDeriv 2 (bch3Path p) 0 =
      omegaBiv p * omegaBiv p +
        Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) := by
    rw [hpath, h2, bch3Arg_zero, deriv_bch3Arg_zero, iteratedDeriv_two_bch3Arg]
    have hid : fderiv ℝ (exp : PGA → PGA) 0
        (Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans)) =
        Generators.commutator (omegaTorsion p.torsion) (omegaTrans p.trans) := by
      rw [hasFDerivAt_exp_zero_pga.fderiv]
      simp
    rw [hid, iteratedFDeriv_two_exp_diag]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [motorPath_zero, bch3Path, bch3Arg_zero, exp_zero]
  · rw [deriv_motorPath_zero, hder]
  · rw [iteratedDeriv_two_motorPath_zero, h2eq, hA]
  · rw [iteratedDeriv_three_motorPath_zero, iteratedDeriv_three_bch3Path_zero]

private theorem hasDerivAt_exp_smul_sq (A : PGA) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • A) * A) (exp (t • A) * A * A) t :=
  (hasDerivAt_exp_smul_const A t).mul_const A

private theorem iteratedDeriv_two_exp_smul_zero (A : PGA) :
    iteratedDeriv 2 (fun t : ℝ => exp (t • A)) 0 = A * A := by
  have h1 : deriv (fun t : ℝ => exp (t • A)) = fun t => exp (t • A) * A := by
    ext t
    exact (hasDerivAt_exp_smul_const A t).deriv
  have h2 := (hasDerivAt_exp_smul_sq A 0).deriv
  simp [iteratedDeriv_succ, h1, h2, zero_smul, exp_zero]

private def scaledParams (p : OmegaParams) (t : ℝ) : OmegaParams :=
  ⟨⟨fun a => t * p.torsion.alpha a, fun a => t * p.torsion.beta a⟩,
    ⟨fun μ => t * p.trans.lambda μ⟩⟩

private theorem omegaTorsion_scaled (p : TorsionParams) (t : ℝ) :
    omegaTorsion ⟨fun a => t * p.alpha a, fun a => t * p.beta a⟩ = t • omegaTorsion p := by
  simp only [omegaTorsion, Finset.smul_sum, smul_add, smul_smul, mul_div_assoc]

private theorem omegaTrans_scaled (p : TransParams) (t : ℝ) :
    omegaTrans ⟨fun μ => t * p.lambda μ⟩ = t • omegaTrans p := by
  simp only [omegaTrans, Finset.smul_sum, smul_smul, mul_div_assoc]

private theorem motor_scaled (p : OmegaParams) (t : ℝ) :
    motor (scaledParams p t) = motorPath p t := by
  simp [motor, motorPath, rotorTorsion, expTrans, scaledParams,
    omegaTorsion_scaled, omegaTrans_scaled, exp_smul_omegaTrans]

private theorem omegaBiv_scaled (p : OmegaParams) (t : ℝ) :
    omegaBiv (scaledParams p t) = t • omegaBiv p := by
  simp [omegaBiv, scaledParams, omegaTorsion_scaled, omegaTrans_scaled, smul_add]

/-- Mixed torsion-plus-translation motors are not the Banach exponential of `Ω_biv`. -/
theorem exists_omegaBiv_ne_motor :
    ∃ p : OmegaParams, exp (omegaBiv p) ≠ motor p := by
  let t0 : TorsionParams := ⟨fun a => if a = 0 then (2 : ℝ) else 0, fun _ => 0⟩
  let q0 : TransParams := ⟨fun μ => if μ = 0 then (2 : ℝ) else 0⟩
  let p0 : OmegaParams := ⟨t0, q0⟩
  have hX : omegaTorsion t0 = hyperbolic 0 := by
    simp only [omegaTorsion]
    rw [Fin.sum_univ_three]
    simp [t0]
  have hY : omegaTrans q0 = null 0 := by
    simp only [omegaTrans]
    rw [Fin.sum_univ_four]
    simp [q0]
  have hC : Generators.commutator (omegaTorsion t0) (omegaTrans q0) = (2 : ℝ) • null 1 := by
    rw [hX, hY, commutator_hyperbolic_null]
    simp
  have hCne : Generators.commutator (omegaTorsion t0) (omegaTrans q0) ≠ 0 := by
    rw [hC]
    intro h
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact null_one_ne_zero ((smul_eq_zero.mp h).resolve_left h2)
  let f := motorPath p0
  let g := fun t : ℝ => exp (t • omegaBiv p0)
  have hf2 := iteratedDeriv_two_motorPath_zero p0
  have hg2 := iteratedDeriv_two_exp_smul_zero (omegaBiv p0)
  have hneq : iteratedDeriv 2 f 0 ≠ iteratedDeriv 2 g 0 := by
    intro h
    set X := omegaTorsion t0
    set Y := omegaTrans q0
    have hYsq : Y * Y = 0 := omegaTrans_sq q0
    have hf2' : iteratedDeriv 2 f 0 = X * X + (2 : ℝ) • (X * Y) := by
      simpa [f, X, Y] using hf2
    have hg2' : iteratedDeriv 2 g 0 = (X + Y) * (X + Y) := by
      simpa [g, omegaBiv, X, Y] using hg2
    have hexpand : (X + Y) * (X + Y) = X * X + X * Y + Y * X := by
      simp [mul_add, add_mul, hYsq]
      abel
    have hEq : X * X + (2 : ℝ) • (X * Y) = X * X + (X * Y + Y * X) := by
      rw [← hf2', h, hg2', hexpand, add_assoc]
    have h' : (2 : ℝ) • (X * Y) = X * Y + Y * X := add_left_cancel hEq
    have hcomm : X * Y = Y * X := by
      have : X * Y + X * Y = X * Y + Y * X := by
        simpa [two_smul] using h'
      exact add_left_cancel this
    exact hCne (by simp [Generators.commutator, hcomm])
  have : ∃ t : ℝ, f t ≠ g t := by
    by_contra h
    push Not at h
    exact hneq <| congrArg (fun φ : ℝ → PGA => iteratedDeriv 2 φ 0) (funext h)
  obtain ⟨t, ht⟩ := this
  refine ⟨scaledParams p0 t, ?_⟩
  intro h
  have hmot : motor (scaledParams p0 t) = f t := motor_scaled p0 t
  have hexp : exp (omegaBiv (scaledParams p0 t)) = g t := by
    simp [g, omegaBiv_scaled]
  exact ht (by rw [← hmot, ← hexp, h])

end Motor

end DstDiophantine
