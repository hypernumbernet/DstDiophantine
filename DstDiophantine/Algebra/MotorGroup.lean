import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Algebra.LorentzLie
import DstDiophantine.Algebra.UnitGroup
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Group-level structure of torsion rotors and null translators

`DstDiophantine.Algebra.LorentzLie` proves the Lie-algebra statement: the ten
generators span `𝔰𝔬(3,1) ⋉ ℝ^{3,1}` with the null span as an abelian ideal.  This
module lifts that statement to the exponentiated objects actually used by the
motor construction.

## Main results

* `exp_apply_mem_of_forall_mem`, `exp_smul_mul_mul_exp_neg_smul`, `sandwich_exp_mem`:
  conjugation by `exp Ω` is `exp(ad Ω)`; hence every `ad Ω`-invariant subspace is
  invariant under the sandwich `exp Ω · exp(-Ω)`.
* `sandwich_rotorTorsion_mem_nullSpan`, `exists_sandwich_rotorTorsion_expTrans`:
  a torsion rotor conjugates a null translator to a null translator
  (`R T R˜ = T'`), for **every** torsion rotor, not only for the pure radial boost of
  `Sandwich.sandwich_pureBoost_expTrans`.
* `exists_sandwich_rotorTorsion_rotorTorsion`: torsion rotors conjugate torsion
  rotors to torsion rotors (`R exp(Ω) R˜ = exp(R Ω R˜)`).
* `exists_motor_mul`, `exists_motor_pow`: the motor product law in semidirect form,
  `(R_p T_p)(R_q T_q) = (R_p R_q) T'` with `T'` an explicit translator, and its
  iterate `(RT)^n = R^n T_n`: only the torsion rotor amplifies under powers.
* `exists_exp_add_eq_exp_mul_one_add`, `exists_exp_omegaBiv_eq_rotorTorsion_mul_expTrans`:
  the Banach exponential of the full bivector `Ω_torsion + Ω_trans` is itself a
  motor `R · T_dressed` with the *same* rotor and a dressed translation
  `Z = ∫₀¹ exp(-sΩ_torsion) Ω_trans exp(sΩ_torsion) ds`; by
  `Motor.exists_omegaBiv_ne_motor` the dressed translation differs from
  `Ω_trans` in general (`exists_dressed_translation_ne`).
* `smul_mul_smul_comm_of_commute`, `cyclic_smul_mul`, `hyperbolic_smul_cyclic_smul_same`:
  scalar multiples of commuting generators commute on every axis.

## Not claimed

That the product of two torsion rotors is again `exp` of a torsion bivector
(surjectivity of `exp` onto the rotor group), and hence a fully closed
parametrised product law on `OmegaParams`.
-/

namespace DstDiophantine

open CliffordAlgebra PGA Generators Operations Motor Sandwich LorentzLie UnitGroup NormedSpace

namespace MotorGroup

/-! ### Generic Banach-algebra helpers -/

section Generic

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasDerivAt_exp_neg_smul (x : 𝔸) (u : ℝ) :
    HasDerivAt (fun v : ℝ => exp ((-v) • x)) (exp ((-u) • x) * (-x)) u := by
  have h : HasDerivAt (fun v : ℝ => exp (v • (-x))) (exp (u • (-x)) * (-x)) u :=
    hasDerivAt_exp_smul_const (-x) u
  have hfun : (fun v : ℝ => exp ((-v) • x)) = fun v : ℝ => exp (v • (-x)) :=
    funext fun v => by rw [neg_smul, smul_neg]
  simpa [hfun, neg_smul, smul_neg] using h

theorem exp_smul_mul_exp_neg_smul (x : 𝔸) (t : ℝ) :
    exp (t • x) * exp ((-t) • x) = 1 := by
  have hc : Commute (t • x) ((-t) • x) :=
    ((Commute.refl x).smul_left t).smul_right (-t)
  have hball : ∀ y : 𝔸, y ∈ Metric.eball (0 : 𝔸) (expSeries ℝ 𝔸).radius := fun y =>
    (expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _
  rw [← exp_add_of_commute_of_mem_ball hc (hball _) (hball _), ← add_smul, add_neg_cancel,
    zero_smul, exp_zero]

end Generic

/-! ### Scalar multiples of commuting generators commute on every axis -/

theorem smul_mul_smul_comm_of_commute {u v : PGA} (h : Commute u v) (x y : ℝ) :
    (x • u) * (y • v) = (y • v) * (x • u) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul,
    mul_comm x y, h.eq]

theorem cyclic_smul_mul (a : Fin 3) (x y : ℝ) :
    (x • cyclic a) * (y • cyclic a) = (y • cyclic a) * (x • cyclic a) :=
  smul_mul_smul_comm_of_commute (Commute.refl _) x y

theorem hyperbolic_smul_cyclic_smul_same (a : Fin 3) (x y : ℝ) :
    (x • hyperbolic a) * (y • cyclic a) = (y • cyclic a) * (x • hyperbolic a) :=
  smul_mul_smul_comm_of_commute (sub_eq_zero.mp (commutator_hyperbolic_cyclic_same a)) x y

/-! ### `ad Ω` as a continuous linear map and `exp(ad Ω)` -/

/-- `ad Ω = [Ω, ·]` as a continuous linear map on the finite-dimensional algebra. -/
noncomputable def adL (Ω : PGA) : PGA →L[ℝ] PGA :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ Ω - LinearMap.mulRight ℝ Ω)

@[simp] theorem adL_apply (Ω x : PGA) : adL Ω x = commutator Ω x := by
  simp [adL, Generators.commutator]

/-- The exponential of an operator preserving a subspace preserves that subspace. -/
theorem exp_apply_mem_of_forall_mem {W : Submodule ℝ PGA} (L : PGA →L[ℝ] PGA)
    (hL : ∀ y ∈ W, L y ∈ W) {x : PGA} (hx : x ∈ W) : exp L x ∈ W := by
  have hclosed : IsClosed (W : Set PGA) := W.closed_of_finiteDimensional
  have hpow : ∀ n : ℕ, (L ^ n) x ∈ W := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ']
      exact hL _ ih
  have hsum : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • L ^ n)) (exp L) := by
    rw [exp_eq_tsum ℝ]
    exact (expSeries_summable' (𝕂 := ℝ) L).hasSum
  have hsum' := (ContinuousLinearMap.apply ℝ PGA x).hasSum hsum
  refine hclosed.mem_of_tendsto hsum'.tendsto_sum_nat (Filter.Eventually.of_forall fun n => ?_)
  refine W.sum_mem fun i _ => ?_
  simp only [ContinuousLinearMap.apply_apply]
  exact W.smul_mem _ (hpow i)

/-- Conjugation by `exp(tΩ)` is the exponential of `t · ad Ω`. -/
theorem exp_smul_mul_mul_exp_neg_smul (Ω x : PGA) (t : ℝ) :
    exp (t • Ω) * x * exp ((-t) • Ω) = exp (t • adL Ω) x := by
  set A := adL Ω
  let f : ℝ → PGA := fun u => exp (u • Ω) * x * exp ((-u) • Ω)
  let E : ℝ → (PGA →L[ℝ] PGA) := fun u => exp ((-u) • A)
  have hcomm (u : ℝ) : Ω * exp (u • Ω) = exp (u • Ω) * Ω :=
    (((Commute.refl Ω).smul_right u).exp_right).eq
  have hf' (u : ℝ) : HasDerivAt f (A (f u)) u := by
    have h1 : HasDerivAt (fun v : ℝ => exp (v • Ω) * x) (exp (u • Ω) * Ω * x) u :=
      (hasDerivAt_exp_smul_const Ω u).mul_const x
    have h2 := hasDerivAt_exp_neg_smul Ω u
    refine (h1.mul h2).congr_deriv ?_
    simp only [A, adL_apply, Generators.commutator, f, mul_neg, ← sub_eq_add_neg, mul_assoc]
    congr 1
    rw [← mul_assoc, ← hcomm, mul_assoc]
  have hE' (u : ℝ) : HasDerivAt E (exp ((-u) • A) * (-A)) u := hasDerivAt_exp_neg_smul A u
  let h : ℝ → PGA := fun u => E u (f u)
  have hh' (u : ℝ) : HasDerivAt h 0 u := by
    refine ((hE' u).clm_apply (hf' u)).congr_deriv ?_
    change (exp ((-u) • A) * -A) (f u) + exp ((-u) • A) (A (f u)) = 0
    have hm : (exp ((-u) • A) * -A) (f u) = -(exp ((-u) • A) (A (f u))) := by
      change exp ((-u) • A) ((-A) (f u)) = _
      rw [neg_apply, map_neg]
    rw [hm]
    exact neg_add_cancel _
  have hconst : ∀ u, h u = h 0 := fun u =>
    is_const_of_deriv_eq_zero (fun u => (hh' u).differentiableAt) (fun u => (hh' u).deriv) u 0
  have h0 : h 0 = x := by
    change exp ((-(0 : ℝ)) • A) (exp ((0 : ℝ) • Ω) * x * exp ((-(0 : ℝ)) • Ω)) = x
    have hA0 : ((0 : ℝ) • A) = 0 := zero_smul ℝ A
    have hΩ0 : ((0 : ℝ) • Ω) = 0 := zero_smul ℝ Ω
    simp only [neg_zero, hA0, hΩ0, exp_zero, one_mul, mul_one, one_apply_eq_self]
  have ht : exp ((-t) • A) (f t) = x := (hconst t).trans h0
  have hinv : exp (t • A) * exp ((-t) • A) = 1 := exp_smul_mul_exp_neg_smul A t
  change f t = exp (t • A) x
  calc f t = (exp (t • A) * exp ((-t) • A)) (f t) := by
        rw [hinv, one_apply_eq_self]
    _ = exp (t • A) (exp ((-t) • A) (f t)) := rfl
    _ = exp (t • A) x := by rw [ht]

/-- An `ad Ω`-invariant subspace is invariant under conjugation by `exp Ω`. -/
theorem exp_mul_mul_exp_neg_mem {W : Submodule ℝ PGA} {Ω : PGA}
    (hW : ∀ y ∈ W, commutator Ω y ∈ W) {x : PGA} (hx : x ∈ W) :
    exp Ω * x * exp (-Ω) ∈ W := by
  have h := exp_smul_mul_mul_exp_neg_smul Ω x 1
  simp only [one_smul, neg_one_smul] at h
  rw [h]
  exact exp_apply_mem_of_forall_mem (adL Ω) (fun y hy => by rw [adL_apply]; exact hW y hy) hx

/-- Sandwich version: for a reverse-odd generator `Ω`, `exp Ω · W · (exp Ω)˜ ⊆ W`
whenever `[Ω, W] ⊆ W`. -/
theorem sandwich_exp_mem {W : Submodule ℝ PGA} {Ω : PGA} (hΩ : reverse Ω = -Ω)
    (hW : ∀ y ∈ W, commutator Ω y ∈ W) {x : PGA} (hx : x ∈ W) :
    sandwich (exp Ω) x ∈ W := by
  rw [sandwich, reverse_exp_of_reverse_neg hΩ]
  exact exp_mul_mul_exp_neg_mem hW hx

/-! ### Torsion rotors act on the null, Lorentz and Poincaré spans -/

theorem sandwich_rotorTorsion_mem_nullSpan (t : TorsionParams) {x : PGA}
    (hx : x ∈ nullSpan) : sandwich (rotorTorsion t) x ∈ nullSpan :=
  sandwich_exp_mem (omegaTorsion_reverse t)
    (fun _ hy => commutator_lorentz_null_mem_nullSpan (omegaTorsion_mem_lorentzSpan t) hy) hx

theorem sandwich_rotorTorsion_mem_lorentzSpan (t : TorsionParams) {x : PGA}
    (hx : x ∈ lorentzSpan) : sandwich (rotorTorsion t) x ∈ lorentzSpan :=
  sandwich_exp_mem (omegaTorsion_reverse t)
    (fun _ hy => commutator_mem_lorentzSpan (omegaTorsion_mem_lorentzSpan t) hy) hx

theorem sandwich_rotorTorsion_mem_poincareSpan (t : TorsionParams) {x : PGA}
    (hx : x ∈ poincareSpan) : sandwich (rotorTorsion t) x ∈ poincareSpan :=
  sandwich_exp_mem (omegaTorsion_reverse t)
    (fun _ hy => commutator_mem_poincareSpan
      (lorentzSpan_le_poincareSpan (omegaTorsion_mem_lorentzSpan t)) hy) hx

/-! ### Parametrising the spans -/

theorem exists_omegaTrans_eq_of_mem_nullSpan {x : PGA} (hx : x ∈ nullSpan) :
    ∃ q : TransParams, x = omegaTrans q := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  refine ⟨⟨fun μ => 2 * c μ⟩, ?_⟩
  have h2 : ∀ r : ℝ, 2 * r / 2 = r := fun r => by ring
  simp only [omegaTrans, h2]
  exact hc.symm

theorem exists_omegaTorsion_eq_of_mem_lorentzSpan {x : PGA} (hx : x ∈ lorentzSpan) :
    ∃ s : TorsionParams, x = omegaTorsion s := by
  rw [lorentzSpan, Submodule.span_union] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hu
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  refine ⟨⟨fun a => 2 * c a, fun a => 2 * d a⟩, ?_⟩
  have h2 : ∀ r : ℝ, 2 * r / 2 = r := fun r => by ring
  simp only [omegaTorsion, h2, Finset.sum_add_distrib]
  rw [hc, hd]

/-! ### Translators are normalised by torsion rotors -/

theorem sandwich_rotorTorsion_one (t : TorsionParams) : sandwich (rotorTorsion t) 1 = 1 := by
  simp [sandwich, rotor_unitary]

theorem exists_sandwich_rotorTorsion_omegaTrans (t : TorsionParams) (p : TransParams) :
    ∃ q : TransParams, sandwich (rotorTorsion t) (omegaTrans p) = omegaTrans q :=
  exists_omegaTrans_eq_of_mem_nullSpan
    (sandwich_rotorTorsion_mem_nullSpan t (omegaTrans_mem_nullSpan p))

/-- Every torsion rotor conjugates a null translator to a null translator. -/
theorem exists_sandwich_rotorTorsion_expTrans (t : TorsionParams) (p : TransParams) :
    ∃ q : TransParams, sandwich (rotorTorsion t) (expTrans p) = expTrans q := by
  obtain ⟨q, hq⟩ := exists_sandwich_rotorTorsion_omegaTrans t p
  exact ⟨q, by rw [expTrans, sandwich_add, sandwich_rotorTorsion_one, hq]; rfl⟩

/-! ### Unitary sandwiches are algebra automorphisms; rotors conjugate rotors to rotors -/

/-- A unitary sandwich `m · m˜` as an `ℝ`-algebra homomorphism. -/
noncomputable def sandwichAlgHom {m : PGA} (hm : m * reverse m = 1) : PGA →ₐ[ℝ] PGA where
  toFun := sandwich m
  map_one' := by simp [sandwich, hm]
  map_mul' := sandwich_mul hm
  map_zero' := by simp [sandwich]
  map_add' := sandwich_add m
  commutes' := fun r => by
    simp only [sandwich]
    rw [← Algebra.commutes r m, mul_assoc, hm, mul_one]

theorem sandwichAlgHom_apply {m : PGA} (hm : m * reverse m = 1) (x : PGA) :
    sandwichAlgHom hm x = sandwich m x := rfl

/-- A unitary sandwich commutes with the Banach exponential. -/
theorem sandwich_exp {m : PGA} (hm : m * reverse m = 1) (x : PGA) :
    sandwich m (exp x) = exp (sandwich m x) := by
  have hcont : Continuous (sandwichAlgHom hm) :=
    (sandwichAlgHom hm).toLinearMap.continuous_of_finiteDimensional
  exact map_exp (sandwichAlgHom hm) hcont x

/-- Torsion rotors conjugate torsion rotors to torsion rotors. -/
theorem exists_sandwich_rotorTorsion_rotorTorsion (t s : TorsionParams) :
    ∃ s' : TorsionParams, sandwich (rotorTorsion t) (rotorTorsion s) = rotorTorsion s' := by
  obtain ⟨s', hs'⟩ := exists_omegaTorsion_eq_of_mem_lorentzSpan
    (sandwich_rotorTorsion_mem_lorentzSpan t (omegaTorsion_mem_lorentzSpan s))
  refine ⟨s', ?_⟩
  have h := sandwich_exp (rotor_unitary t) (omegaTorsion s)
  rw [hs'] at h
  exact h

/-! ### Motor product law in semidirect form -/

theorem reverse_rotorTorsion (t : TorsionParams) :
    reverse (rotorTorsion t) = rotorTorsion (negTorsionParams t) := by
  rw [rotorTorsion, reverse_exp_of_reverse_neg (omegaTorsion_reverse t), ← omegaTorsion_neg]
  rfl

/-- `(R_p T_p)(R_q T_q) = (R_p R_q) T'` with `T'` a translator: the translators form a
normal abelian subgroup normalised by the torsion rotors. -/
theorem exists_motor_mul (p q : OmegaParams) :
    ∃ r : TransParams,
      motor p * motor q = rotorTorsion p.torsion * rotorTorsion q.torsion * expTrans r := by
  obtain ⟨r₁, hr₁⟩ := exists_sandwich_rotorTorsion_expTrans (negTorsionParams q.torsion) p.trans
  refine ⟨⟨fun μ => r₁.lambda μ + q.trans.lambda μ⟩, ?_⟩
  have hunit : rotorTorsion q.torsion * reverse (rotorTorsion q.torsion) = 1 :=
    rotor_unitary q.torsion
  have hrev : reverse (rotorTorsion (negTorsionParams q.torsion)) = rotorTorsion q.torsion := by
    rw [← reverse_rotorTorsion, reverse_reverse]
  have hsand : reverse (rotorTorsion q.torsion) * expTrans p.trans * rotorTorsion q.torsion =
      expTrans r₁ := by
    rw [← hr₁, sandwich, reverse_rotorTorsion, hrev]
  calc motor p * motor q
      = rotorTorsion p.torsion * expTrans p.trans *
          (rotorTorsion q.torsion * expTrans q.trans) := rfl
    _ = rotorTorsion p.torsion * rotorTorsion q.torsion *
          (reverse (rotorTorsion q.torsion) * expTrans p.trans * rotorTorsion q.torsion) *
          expTrans q.trans := by
        rw [show rotorTorsion p.torsion * rotorTorsion q.torsion *
            (reverse (rotorTorsion q.torsion) * expTrans p.trans * rotorTorsion q.torsion) *
            expTrans q.trans =
            rotorTorsion p.torsion * (rotorTorsion q.torsion * reverse (rotorTorsion q.torsion)) *
              expTrans p.trans * (rotorTorsion q.torsion * expTrans q.trans) by
          simp only [mul_assoc], hunit, mul_one]
    _ = rotorTorsion p.torsion * rotorTorsion q.torsion * expTrans r₁ * expTrans q.trans := by
        rw [hsand]
    _ = rotorTorsion p.torsion * rotorTorsion q.torsion *
          expTrans ⟨fun μ => r₁.lambda μ + q.trans.lambda μ⟩ := by
        rw [mul_assoc, expTrans_mul]

/-- A translator can be moved through a torsion rotor: `T R = R T'`. -/
theorem exists_expTrans_mul_rotorTorsion (r : TransParams) (t : TorsionParams) :
    ∃ r' : TransParams, expTrans r * rotorTorsion t = rotorTorsion t * expTrans r' := by
  obtain ⟨r', hr'⟩ := exists_sandwich_rotorTorsion_expTrans (negTorsionParams t) r
  refine ⟨r', ?_⟩
  have hrev : reverse (rotorTorsion (negTorsionParams t)) = rotorTorsion t := by
    rw [← reverse_rotorTorsion, reverse_reverse]
  have hsand : reverse (rotorTorsion t) * expTrans r * rotorTorsion t = expTrans r' := by
    rw [← hr', sandwich, reverse_rotorTorsion, hrev]
  calc expTrans r * rotorTorsion t
      = rotorTorsion t * (reverse (rotorTorsion t) * expTrans r * rotorTorsion t) := by
        rw [← mul_assoc, ← mul_assoc, rotor_unitary, one_mul]
    _ = rotorTorsion t * expTrans r' := by rw [hsand]

theorem expTrans_zero : expTrans ⟨fun _ => 0⟩ = 1 := by
  simp [expTrans, omegaTrans]

/-- Powers of a mixed motor: `(RT)^n = R^n T_n` with `T_n` a translator, so the torsion
rotor is the only factor that amplifies. -/
theorem exists_motor_pow (p : OmegaParams) (n : ℕ) :
    ∃ r : TransParams, motor p ^ n = rotorTorsion p.torsion ^ n * expTrans r := by
  induction n with
  | zero => exact ⟨⟨fun _ => 0⟩, by simp [expTrans_zero]⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := exists_expTrans_mul_rotorTorsion r p.torsion
    refine ⟨⟨fun μ => r'.lambda μ + p.trans.lambda μ⟩, ?_⟩
    rw [pow_succ, hr, pow_succ, motor]
    calc rotorTorsion p.torsion ^ n * expTrans r * (rotorTorsion p.torsion * expTrans p.trans)
        = rotorTorsion p.torsion ^ n * (expTrans r * rotorTorsion p.torsion) *
            expTrans p.trans := by simp only [mul_assoc]
      _ = rotorTorsion p.torsion ^ n * (rotorTorsion p.torsion * expTrans r') *
            expTrans p.trans := by rw [hr']
      _ = rotorTorsion p.torsion ^ n * rotorTorsion p.torsion *
            expTrans ⟨fun μ => r'.lambda μ + p.trans.lambda μ⟩ := by
          rw [← expTrans_mul]; simp only [mul_assoc]

/-! ### `exp(Ω_torsion + Ω_trans)` is a motor with a dressed translation -/

/-- Time-dependent conjugate `exp(-sX) Y exp(sX)`. -/
noncomputable def conjPath (X Y : PGA) (s : ℝ) : PGA :=
  exp ((-s) • X) * Y * exp (s • X)

/-- Dressed translation `Z(t) = ∫₀ᵗ exp(-sX) Y exp(sX) ds`. -/
noncomputable def nullDress (X Y : PGA) (t : ℝ) : PGA :=
  ∫ s in (0 : ℝ)..t, conjPath X Y s

theorem continuous_conjPath (X Y : PGA) : Continuous (conjPath X Y) := by
  unfold conjPath
  have h1 : Continuous fun s : ℝ => exp ((-s) • X) :=
    exp_continuous.comp (continuous_neg.smul continuous_const)
  have h2 : Continuous fun s : ℝ => exp (s • X) :=
    exp_continuous.comp (continuous_id.smul continuous_const)
  exact (h1.mul continuous_const).mul h2

theorem conjPath_mem {W : Submodule ℝ PGA} {X Y : PGA} (hY : Y ∈ W)
    (hX : ∀ y ∈ W, commutator X y ∈ W) (s : ℝ) : conjPath X Y s ∈ W := by
  have h := exp_smul_mul_mul_exp_neg_smul X Y (-s)
  rw [neg_neg] at h
  unfold conjPath
  rw [h]
  refine exp_apply_mem_of_forall_mem _ (fun y hy => ?_) hY
  change (-s) • adL X y ∈ W
  rw [adL_apply]
  exact W.smul_mem _ (hX y hy)

theorem nullDress_mem {W : Submodule ℝ PGA} {X Y : PGA} (hY : Y ∈ W)
    (hX : ∀ y ∈ W, commutator X y ∈ W) (t : ℝ) : nullDress X Y t ∈ W := by
  refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp fun φ hφ => ?_
  rw [Submodule.mem_dualAnnihilator] at hφ
  have hcont := continuous_conjPath X Y
  have hint := (LinearMap.toContinuousLinearMap φ).intervalIntegral_comp_comm
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
  have hz : ∀ s, φ (conjPath X Y s) = 0 := fun s => hφ _ (conjPath_mem hY hX s)
  simp only [LinearMap.coe_toContinuousLinearMap', hz, intervalIntegral.integral_zero] at hint
  exact hint.symm

theorem hasDerivAt_nullDress (X Y : PGA) (t : ℝ) :
    HasDerivAt (nullDress X Y) (conjPath X Y t) t := by
  have hcont := continuous_conjPath X Y
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

/-- If `Y` lies in the null ideal and `ad X` preserves it, then
`exp(X + Y) = exp X · (1 + Z)` with `Z` again in the null ideal. -/
theorem exists_exp_add_eq_exp_mul_one_add {X Y : PGA} (hY : Y ∈ nullSpan)
    (hX : ∀ y ∈ nullSpan, commutator X y ∈ nullSpan) :
    ∃ Z ∈ nullSpan, exp (X + Y) = exp X * (1 + Z) := by
  set Z := nullDress X Y with hZdef
  let F : ℝ → PGA := fun t => exp (t • X) * (1 + Z t)
  let G : ℝ → PGA := fun t => exp ((-t) • (X + Y)) * F t
  have hcomm (t : ℝ) : X * exp (t • X) = exp (t • X) * X :=
    (((Commute.refl X).smul_right t).exp_right).eq
  have hF' (t : ℝ) : HasDerivAt F
      (exp (t • X) * X * (1 + Z t) + exp (t • X) * conjPath X Y t) t :=
    (hasDerivAt_exp_smul_const X t).mul ((hasDerivAt_nullDress X Y t).const_add 1)
  have hG' (t : ℝ) : HasDerivAt G 0 t := by
    refine ((hasDerivAt_exp_neg_smul (X + Y) t).mul (hF' t)).congr_deriv ?_
    have hYZ : Y * exp (t • X) * Z t = 0 := nullSpan_mul_mul hY (nullDress_mem hY hX t) _
    have heY : exp (t • X) * conjPath X Y t = Y * exp (t • X) := by
      simp only [conjPath]
      rw [← mul_assoc, ← mul_assoc, exp_smul_mul_exp_neg_smul, one_mul]
    have hA : X * (exp (t • X) * (1 + Z t)) = exp (t • X) * X * (1 + Z t) := by
      rw [← mul_assoc, hcomm]
    have hB : Y * (exp (t • X) * (1 + Z t)) = Y * exp (t • X) := by
      rw [mul_add, mul_one, mul_add, ← mul_assoc, hYZ, add_zero]
    calc exp ((-t) • (X + Y)) * -(X + Y) * F t +
          exp ((-t) • (X + Y)) * (exp (t • X) * X * (1 + Z t) + exp (t • X) * conjPath X Y t)
        = exp ((-t) • (X + Y)) * (-(X + Y) * (exp (t • X) * (1 + Z t)) +
            (exp (t • X) * X * (1 + Z t) + exp (t • X) * conjPath X Y t)) := by
          simp only [F, mul_add, mul_assoc]
      _ = exp ((-t) • (X + Y)) * 0 := by
          congr 1
          rw [heY, neg_mul, add_mul, hA, hB, neg_add_cancel]
      _ = 0 := mul_zero _
  have hGconst : ∀ t, G t = G 0 := fun t =>
    is_const_of_deriv_eq_zero (fun u => (hG' u).differentiableAt) (fun u => (hG' u).deriv) t 0
  have hZ0 : Z 0 = 0 := intervalIntegral.integral_same
  have hG0 : G 0 = 1 := by simp [G, F, hZ0, exp_zero]
  have hG1 : exp ((-1 : ℝ) • (X + Y)) * (exp ((1 : ℝ) • X) * (1 + Z 1)) = 1 :=
    (hGconst 1).trans hG0
  rw [one_smul] at hG1
  refine ⟨Z 1, nullDress_mem hY hX 1, ?_⟩
  calc exp (X + Y) = exp (X + Y) * (exp ((-1 : ℝ) • (X + Y)) * (exp X * (1 + Z 1))) := by
        rw [hG1, mul_one]
    _ = (exp ((1 : ℝ) • (X + Y)) * exp ((-1 : ℝ) • (X + Y))) * (exp X * (1 + Z 1)) := by
        rw [one_smul, mul_assoc]
    _ = exp X * (1 + Z 1) := by rw [exp_smul_mul_exp_neg_smul, one_mul]

/-- The Banach exponential of the full bivector `Ω_biv = Ω_torsion + Ω_trans` is a motor
with the same torsion rotor and a dressed translation. -/
theorem exists_exp_omegaBiv_eq_rotorTorsion_mul_expTrans (p : OmegaParams) :
    ∃ q : TransParams, exp (omegaBiv p) = rotorTorsion p.torsion * expTrans q := by
  obtain ⟨Z, hZ, hexp⟩ := exists_exp_add_eq_exp_mul_one_add (omegaTrans_mem_nullSpan p.trans)
    (fun _ hy => commutator_lorentz_null_mem_nullSpan (omegaTorsion_mem_lorentzSpan p.torsion) hy)
  obtain ⟨q, rfl⟩ := exists_omegaTrans_eq_of_mem_nullSpan hZ
  exact ⟨q, hexp⟩

/-- The dressed translation differs from `Ω_trans` in general: `exp(Ω_biv)` is a motor,
but not the motor `RT` of the same parameters. -/
theorem exists_dressed_translation_ne :
    ∃ (p : OmegaParams) (q : TransParams),
      exp (omegaBiv p) = rotorTorsion p.torsion * expTrans q ∧ q ≠ p.trans := by
  obtain ⟨p, hp⟩ := exists_omegaBiv_ne_motor
  obtain ⟨q, hq⟩ := exists_exp_omegaBiv_eq_rotorTorsion_mul_expTrans p
  refine ⟨p, q, hq, fun h => hp ?_⟩
  rw [hq, h]
  rfl

/-- `exp(Ω_biv)` is unitary. -/
theorem exp_omegaBiv_unitary (p : OmegaParams) :
    exp (omegaBiv p) * reverse (exp (omegaBiv p)) = 1 := by
  have hrev : reverse (omegaBiv p) = -omegaBiv p := by
    have h1 : reverse (omegaTrans p.trans) = -omegaTrans p.trans := by
      simp only [omegaTrans, map_sum, map_smul, null_reverse]
      rw [← Finset.sum_neg_distrib]
      congr 1
      ext μ
      rw [smul_neg]
    rw [omegaBiv, map_add, omegaTorsion_reverse, h1, neg_add]
  rw [reverse_exp_of_reverse_neg hrev,
    ← exp_add_of_commute (Commute.neg_right (Commute.refl (omegaBiv p)))]
  simp

end MotorGroup

end DstDiophantine
