import DstDiophantine.Gravity.ClassicalSchwarzschild
import DstDiophantine.Algebra.MotorGroup
import DstDiophantine.Algebra.BivectorBasis

/-!
# The direction of gravity: the axis of the static Killing bivector

At an event, a Killing field `ξ` is determined by its value and by the
antisymmetric derivative `∇ξ`: a translation and a Lorentz generator, that is,
an element of the Poincaré algebra. In `G(3,1,1)` that element is a bivector.
For the static field `∂_t` of a radial-boost chart it is
`K = (κ/2) B⁺ + (ν/2) N₀`, with `ν` the Killing norm and `κ` its proper radial
derivative.

## Proved

* Translator conjugation is exact at first order, `T x T˜ = x + [Ω_trans, x]`;
  a translator moves the hyperplane `e_μ` to `e_μ + w_μ λ^μ e₄`, and
  `[Ω_torsion, x] = ω x` is the Lorentz action on vectors.
* `K` is the conjugate of the pure boost `(κ/2) B⁺` by the radial translator of
  length `ℓ = ν/κ`, and that radial displacement is unique; `K` is the meet of the
  time hyperplane with the displaced radial hyperplane; `K² = κ²/4`. For `ν > 0`
  the axis lies on the side `-sign κ`, and `κ` has the sign of the mass.
* Events `P(x) = (1 + e₄ x) i`: the velocity of a general `Ω_biv` at `P(x)` is
  `e₄ (λ + ω x) i`. For `K` it is `(ν + κ s) e₀` along the radial line,
  vanishing only at `s = -ν/κ`.
* `exp(τK) = T R(κτ) T˜` fixes every event of the axis; the orbit of the origin
  is the hyperbola at constant interval `ℓ` from the axis, bending away from it.
* The squared Killing norm `N² = -(λ + ω x)²` satisfies the exact
  second-difference identity `□N² = 8J`. Hyperbolic model: `N²` grows away from
  the axis; elliptic model: it shrinks.
* In that flat flow the inertial frame of release, seen from the hovering
  observer, is `exp(-τ K)`, still a boost about the same axis. A body released
  from rest travels on `s e₀`. At observer proper time `σ` its simultaneous
  separation is `ℓ (sech(σ/ℓ) - 1)` along the outward normal: nonpositive,
  with vanishing first derivative at release and second derivative `-1/ℓ`.
  The same line meets the light cone of the axis, where `N = 0`, at proper
  time `ℓ`, and the separation tends to `-ℓ`.
* Exterior Schwarzschild: `ν = √A`, `κ = ½A' = √A ∂_r√A = rₛ/(2r²)`,
  `r²κ = rₛ/2`, `ℓ = ν/κ > 0` inward with `ℓ · ∂_r√A = 1`,
  `∂_r√A = T⁰_{rt} = -√A φ'`; `ℓ` increases strictly, tends to `0` at the
  horizon (where `K` becomes the pure boost of rate `1/(2rₛ)`) and to `∞` far
  away (where `K` becomes the pure time translation); `J(κ) = A² J_field`.

## Not claimed

* That the double-spacetime mismatch `Ω` itself is a Killing bivector.
* A covariant Killing transport on a general manifold, or a dictionary for a
  general motor field.
* That the straight line of the flat flow is a Schwarzschild geodesic. The
  fall law is the Killing jet at one event.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations Motor Amplification LorentzLie MotorGroup
open Sandwich (sandwich sandwich_add sandwich_smul sandwich_comp sandwich_mul)
open CliffordAlgebra (reverse)
open NormedSpace Set Filter
open scoped Topology

namespace KillingAxis

/-! ### Translator conjugation -/

theorem reverse_omegaTrans (p : TransParams) : reverse (omegaTrans p) = -omegaTrans p := by
  simp only [omegaTrans, map_sum, map_smul, null_reverse]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext μ
  rw [smul_neg]

/-- Reversed translation parameters. -/
def negTrans (p : TransParams) : TransParams := ⟨fun μ => -p.lambda μ⟩

theorem omegaTrans_negTrans (p : TransParams) : omegaTrans (negTrans p) = -omegaTrans p := by
  simp only [omegaTrans, negTrans, neg_div, neg_smul, Finset.sum_neg_distrib]

theorem reverse_expTrans (p : TransParams) : reverse (expTrans p) = expTrans (negTrans p) := by
  rw [expTrans, expTrans, map_add, CliffordAlgebra.reverse.map_one, reverse_omegaTrans,
    omegaTrans_negTrans]

/-- A translator conjugates exactly at first order: `T x T˜ = x + [Ω_trans, x]`. -/
theorem sandwich_expTrans (p : TransParams) (x : PGA) :
    sandwich (expTrans p) x = x + commutator (omegaTrans p) x := by
  have h := omegaTrans_mul_mul p x
  rw [Sandwich.sandwich, reverse_expTrans, expTrans, expTrans, omegaTrans_negTrans,
    Generators.commutator]
  simp only [add_mul, mul_add, one_mul, mul_one, mul_neg, h]
  abel

/-- `Ω_trans = ½ e₄ λ`. -/
theorem omegaTrans_eq_half_e4 (p : TransParams) :
    omegaTrans p = (1 / 2 : ℝ) • (ι e4Index * minkowskiVector p.lambda) := by
  rw [minkowskiVector_eq_sum, Finset.mul_sum, Finset.smul_sum]
  simp only [omegaTrans, null, mul_smul_comm, smul_smul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  ring

/-! ### Vectors: hyperplane shifts and the Lorentz action -/

private theorem castAdd_zero : (Fin.castAdd 1 (0 : Fin 4) : Fin 5) = 0 := rfl
private theorem castAdd_one : (Fin.castAdd 1 (1 : Fin 4) : Fin 5) = 1 := rfl
private theorem castAdd_two : (Fin.castAdd 1 (2 : Fin 4) : Fin 5) = 2 := rfl
private theorem castAdd_three : (Fin.castAdd 1 (3 : Fin 4) : Fin 5) = 3 := rfl

private theorem extend4_zero (x : Fin 4 → ℝ) : extend4 x 0 = x 0 := rfl
private theorem extend4_one (x : Fin 4 → ℝ) : extend4 x 1 = x 1 := rfl
private theorem extend4_two (x : Fin 4 → ℝ) : extend4 x 2 = x 2 := rfl
private theorem extend4_three (x : Fin 4 → ℝ) : extend4 x 3 = x 3 := rfl

private theorem null_zero_eq : null 0 = ι e4Index * ι 0 := by simp [null]
private theorem null_one_eq : null 1 = ι e4Index * ι 1 := by simp [null]

theorem minkowskiVector_vec (a b c d : ℝ) :
    minkowskiVector ![a, b, c, d] = a • ι 0 + b • ι 1 + c • ι 2 + d • ι 3 := by
  rw [minkowskiVector_eq_sum, Fin.sum_univ_four, castAdd_zero, castAdd_one, castAdd_two,
    castAdd_three]
  simp

theorem minkowskiVector_add (x y : Fin 4 → ℝ) :
    minkowskiVector (x + y) = minkowskiVector x + minkowskiVector y := by
  simp only [minkowskiVector_eq_sum, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem polar_Q311_e5vec_extend4 (j : Fin 5) (x : Fin 4 → ℝ) :
    QuadraticMap.polar Q311 (e5vec j) (extend4 x) = 2 * w311 j * extend4 x j := by
  fin_cases j <;>
    simp [QuadraticMap.polar, Q311, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_five,
      e5vec, Pi.single_apply, extend4, w311] <;> ring

/-- `[e₄ v, e_μ] = polar(v, e_μ) e₄`. -/
theorem commutator_e4_vec_ι (v : Fin 4 → ℝ) (μ : Fin 5) :
    commutator (ι e4Index * minkowskiVector v) (ι μ) =
      QuadraticMap.polar Q311 (extend4 v) (e5vec μ) • ι e4Index := by
  have hswap : minkowskiVector v * ι μ + ι μ * minkowskiVector v =
      algebraMap ℝ PGA (QuadraticMap.polar Q311 (extend4 v) (e5vec μ)) :=
    CliffordAlgebra.ι_mul_ι_add_swap _ _
  have hμ : ι μ * ι e4Index = -(ι e4Index * ι μ) := by
    rw [show ι e4Index * ι μ = -(ι μ * ι e4Index) from e4_mul_ι_vec (e5vec μ), neg_neg]
  rw [Generators.commutator, ← mul_assoc (ι μ), hμ, neg_mul, sub_neg_eq_add, mul_assoc,
    mul_assoc, ← mul_add, hswap, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

/-- A translator moves the hyperplane `e_μ` by the Minkowski pairing:
`T e_μ T˜ = e_μ + w_μ λ^μ e₄`. -/
theorem sandwich_expTrans_ι (p : TransParams) (μ : Fin 4) :
    sandwich (expTrans p) (ι (Fin.castAdd 1 μ)) =
      ι (Fin.castAdd 1 μ) + (w31 μ * p.lambda μ) • ι e4Index := by
  have hw : w311 (Fin.castAdd 1 μ) = w31 μ := by fin_cases μ <;> rfl
  rw [sandwich_expTrans, omegaTrans_eq_half_e4, commutator_smul_left, commutator_e4_vec_ι,
    QuadraticMap.polar_comm, polar_Q311_e5vec_extend4, extend4_apply, hw, smul_smul]
  module

/-- `[a b, m] = polar(b,m) a - polar(a,m) b` for any three vectors. -/
theorem commutator_ι_mul_ι_ι (a b m : Vec5) :
    commutator (CliffordAlgebra.ι Q311 a * CliffordAlgebra.ι Q311 b)
        (CliffordAlgebra.ι Q311 m) =
      QuadraticMap.polar Q311 b m • CliffordAlgebra.ι Q311 a -
        QuadraticMap.polar Q311 a m • CliffordAlgebra.ι Q311 b := by
  have h1 := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q311) b m
  have h2 := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q311) a m
  set A := CliffordAlgebra.ι Q311 a
  set B := CliffordAlgebra.ι Q311 b
  set M := CliffordAlgebra.ι Q311 m
  have key : A * B * M - M * (A * B) = A * (B * M + M * B) - (A * M + M * A) * B := by
    noncomm_ring
  rw [Generators.commutator, key, h1, h2, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, one_mul]

/-- Lorentz action `ω x` of `Ω_torsion` on Minkowski coordinates. -/
def lorentzAct (t : TorsionParams) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![t.alpha 0 * x 1 + t.alpha 1 * x 2 + t.alpha 2 * x 3,
    t.alpha 0 * x 0 - t.beta 2 * x 2 + t.beta 1 * x 3,
    t.alpha 1 * x 0 + t.beta 2 * x 1 - t.beta 0 * x 3,
    t.alpha 2 * x 0 - t.beta 1 * x 1 + t.beta 0 * x 2]

/-- `[Ω_torsion, x] = ω x`. -/
theorem commutator_omegaTorsion_minkowskiVector (t : TorsionParams) (x : Fin 4 → ℝ) :
    commutator (omegaTorsion t) (minkowskiVector x) = minkowskiVector (lorentzAct t x) := by
  have hgen : ∀ i j : Fin 5, commutator (ι i * ι j) (minkowskiVector x) =
      (2 * w311 j * extend4 x j) • ι i - (2 * w311 i * extend4 x i) • ι j := by
    intro i j
    rw [← polar_Q311_e5vec_extend4, ← polar_Q311_e5vec_extend4]
    exact commutator_ι_mul_ι_ι _ _ _
  have hB0 : hyperbolic 0 = ι 0 * ι 1 := rfl
  have hB1 : hyperbolic 1 = ι 0 * ι 2 := rfl
  have hB2 : hyperbolic 2 = ι 0 * ι 3 := rfl
  have hC0 : cyclic 0 = ι 3 * ι 2 := rfl
  have hC1 : cyclic 1 = ι 1 * ι 3 := rfl
  have hC2 : cyclic 2 = ι 2 * ι 1 := rfl
  rw [omegaTorsion, Fin.sum_univ_three, lorentzAct, minkowskiVector_vec]
  simp only [commutator_add_left, commutator_smul_left, hB0, hB1, hB2, hC0, hC1, hC2, hgen,
    extend4_zero, extend4_one, extend4_two, extend4_three]
  simp only [w311]
  module

/-! ### The static Killing bivector and its displaced axis -/

/-- `K = (κ/2) B⁺ + (ν/2) N₀`: boost rate `κ`, time translation `ν`. -/
noncomputable def killingBivector (κ ν : ℝ) : PGA :=
  (κ / 2) • hyperbolic 0 + (ν / 2) • null 0

/-- Radial translation parameter `λ = -ℓ e₁`. -/
def radialShift (ℓ : ℝ) : TransParams := ⟨![0, -ℓ, 0, 0]⟩

theorem commutator_omegaTrans_hyperbolic0 (p : TransParams) :
    commutator (omegaTrans p) (hyperbolic 0) =
      -(p.lambda 1 • null 0 + p.lambda 0 • null 1) := by
  rw [omegaTrans, Fin.sum_univ_four]
  simp only [commutator_add_left, commutator_smul_left]
  rw [Generators.commutator_neg (null 0), Generators.commutator_neg (null 1),
    Generators.commutator_neg (null 2), Generators.commutator_neg (null 3),
    commutator_hyperbolic0_null0, commutator_hyperbolic0_null1,
    commutator_hyperbolic0_null2, commutator_hyperbolic0_null3]
  module

/-- The static Killing bivector is a pure boost about an axis displaced by `ℓ`. -/
theorem sandwich_radialShift_boost (κ ℓ : ℝ) :
    sandwich (expTrans (radialShift ℓ)) ((κ / 2) • hyperbolic 0) =
      killingBivector κ (κ * ℓ) := by
  rw [sandwich_expTrans, commutator_smul_right, commutator_omegaTrans_hyperbolic0,
    killingBivector]
  simp only [radialShift, Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero,
    neg_smul, neg_neg]
  module

/-- The radial displacement that turns the pure boost into `K` is unique:
no time component, radial component `-ν/κ`; translations along the axis are free. -/
theorem sandwich_expTrans_boost_eq_killing_iff {κ ν : ℝ} (hκ : κ ≠ 0) (p : TransParams) :
    sandwich (expTrans p) ((κ / 2) • hyperbolic 0) = killingBivector κ ν ↔
      p.lambda 0 = 0 ∧ p.lambda 1 = -(ν / κ) := by
  rw [sandwich_expTrans, commutator_smul_right, commutator_omegaTrans_hyperbolic0,
    killingBivector]
  constructor
  · intro h
    have h' := add_left_cancel h
    have hsum : ∑ μ : Fin 4,
        (![-(κ / 2) * p.lambda 1 - ν / 2, -(κ / 2) * p.lambda 0, 0, 0] μ) • null μ = 0 := by
      rw [← sub_eq_zero] at h'
      rw [← h', Fin.sum_univ_four]
      simp
      module
    have hli := Fintype.linearIndependent_iff.mp BivectorBasis.linearIndependent_null _ hsum
    have h0 := hli 0
    have h1 := hli 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨?_, ?_⟩
    · have : κ / 2 ≠ 0 := div_ne_zero hκ two_ne_zero
      have h1' : (κ / 2) * p.lambda 0 = 0 := by linarith
      exact (mul_eq_zero.mp h1').resolve_left this
    · field_simp
      linarith
  · rintro ⟨h0, h1⟩
    congr 1
    rw [h0, h1, zero_smul, add_zero, smul_neg, smul_smul, ← neg_smul]
    congr 1
    rw [mul_neg, neg_neg, div_mul_div_comm, mul_comm κ ν, mul_div_mul_right _ _ hκ]

/-- A positive time translation puts the axis on the side `-sign(κ)`. -/
theorem axis_neg_iff {κ ν : ℝ} (hν : 0 < ν) : -(ν / κ) < 0 ↔ 0 < κ := by
  rw [neg_lt_zero, div_pos_iff_of_pos_left hν]

/-- `K` is the meet of the time hyperplane with the displaced radial hyperplane. -/
theorem killingBivector_eq_meet (κ ℓ : ℝ) :
    killingBivector κ (κ * ℓ) =
      (κ / 2) • (sandwich (expTrans (radialShift ℓ)) (ι 0) *
        sandwich (expTrans (radialShift ℓ)) (ι 1)) := by
  have h0 : sandwich (expTrans (radialShift ℓ)) (ι 0) = ι 0 := by
    simpa [castAdd_zero, radialShift] using sandwich_expTrans_ι (radialShift ℓ) 0
  have h1 : sandwich (expTrans (radialShift ℓ)) (ι 1) = ι 1 + (-ℓ) • ι e4Index := by
    simpa [castAdd_one, radialShift, w31] using sandwich_expTrans_ι (radialShift ℓ) 1
  rw [h0, h1, killingBivector, mul_add, mul_smul_comm,
    e_mul_anticomm (by decide : (0 : Fin 5) ≠ e4Index), null_zero_eq]
  have hB : hyperbolic 0 = ι 0 * ι 1 := rfl
  rw [hB]
  module

private theorem null0_mul_hyperbolic0 : null 0 * hyperbolic 0 = -null 1 := by
  have hB : hyperbolic 0 = ι 0 * ι 1 := rfl
  rw [null_zero_eq, null_one_eq, hB]
  calc ι e4Index * ι 0 * (ι 0 * ι 1) = ι e4Index * (ι 0 * ι 0) * ι 1 := by
        simp only [mul_assoc]
    _ = -(ι e4Index * ι 1) := by rw [e0_sq]; simp

private theorem hyperbolic0_mul_null0 : hyperbolic 0 * null 0 = null 1 := by
  have h := commutator_hyperbolic0_null0
  rw [Generators.commutator, null0_mul_hyperbolic0, sub_neg_eq_add] at h
  have : hyperbolic 0 * null 0 = (2 : ℝ) • null 1 - null 1 := eq_sub_of_add_eq h
  rw [this, two_smul, add_sub_cancel_right]

/-- `K² = κ²/4`: the translation part does not enter the invariant. -/
theorem killingBivector_sq (κ ν : ℝ) :
    killingBivector κ ν * killingBivector κ ν = algebraMap ℝ PGA (κ ^ 2 / 4) := by
  simp only [killingBivector, add_mul, mul_add, smul_mul_smul_comm, hyperbolic_sq,
    hyperbolic0_mul_null0, null0_mul_hyperbolic0, null_sq, smul_zero, add_zero,
    Algebra.algebraMap_eq_smul_one]
  module

/-! ### Events and the velocity field of a Poincaré bivector -/

/-- Event with Minkowski coordinates `x`: `P(x) = (1 + e₄ x) i`. -/
noncomputable def event (x : Fin 4 → ℝ) : PGA :=
  (1 + ι e4Index * minkowskiVector x) * pseudoscalar

private theorem commute_e4_bivector {i j : Fin 5} (hi : i ≠ e4Index) (hj : j ≠ e4Index) :
    Commute (ι e4Index) (ι i * ι j) := by
  unfold Commute SemiconjBy
  have hi' : ι e4Index * ι i = -(ι i * ι e4Index) := e_mul_anticomm hi.symm
  have hj' : ι e4Index * ι j = -(ι j * ι e4Index) := e_mul_anticomm hj.symm
  calc ι e4Index * (ι i * ι j) = (ι e4Index * ι i) * ι j := by rw [mul_assoc]
    _ = -(ι i * ι e4Index) * ι j := by rw [hi']
    _ = -(ι i * (ι e4Index * ι j)) := by simp [mul_assoc]
    _ = -(ι i * (-(ι j * ι e4Index))) := by rw [hj']
    _ = ι i * ι j * ι e4Index := by simp [mul_assoc]

/-- The null vector commutes with the whole Lorentz sector. -/
theorem commute_e4_of_mem_lorentzSpan {x : PGA} (hx : x ∈ lorentzSpan) :
    Commute (ι e4Index) x := by
  refine Submodule.span_induction (p := fun y _ => Commute (ι e4Index) y) ?_ ?_ ?_ ?_ hx
  · rintro y (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · fin_cases a
      · exact commute_e4_bivector (i := 0) (j := 1) (by decide) (by decide)
      · exact commute_e4_bivector (i := 0) (j := 2) (by decide) (by decide)
      · exact commute_e4_bivector (i := 0) (j := 3) (by decide) (by decide)
    · fin_cases a
      · exact commute_e4_bivector (i := 3) (j := 2) (by decide) (by decide)
      · exact commute_e4_bivector (i := 1) (j := 3) (by decide) (by decide)
      · exact commute_e4_bivector (i := 2) (j := 1) (by decide) (by decide)
  · exact Commute.zero_right _
  · intro y z _ _ hy hz
    exact hy.add_right hz
  · intro r y _ hy
    exact hy.smul_right r

theorem commutator_lorentz_e4_mul {L : PGA} (hL : L ∈ lorentzSpan) (X : PGA) :
    commutator L (ι e4Index * X * pseudoscalar) =
      ι e4Index * commutator L X * pseudoscalar := by
  have hLe : L * ι e4Index = ι e4Index * L := (commute_e4_of_mem_lorentzSpan hL).eq.symm
  have hLi : pseudoscalar * L = L * pseudoscalar :=
    (commute_pseudoscalar_of_mem_lorentzSpan hL).eq
  simp only [Generators.commutator, mul_sub, sub_mul]
  rw [show L * (ι e4Index * X * pseudoscalar) = ι e4Index * (L * X) * pseudoscalar by
        rw [← mul_assoc, ← mul_assoc, hLe, mul_assoc (ι e4Index) L X],
      show ι e4Index * X * pseudoscalar * L = ι e4Index * (X * L) * pseudoscalar by
        rw [mul_assoc (ι e4Index * X), hLi, ← mul_assoc, mul_assoc (ι e4Index) X L]]

theorem commutator_e4_vec_pseudoscalar (v : Fin 4 → ℝ) :
    commutator (ι e4Index * minkowskiVector v) pseudoscalar =
      (2 : ℝ) • (ι e4Index * minkowskiVector v * pseudoscalar) := by
  have hvi : pseudoscalar * minkowskiVector v = -(minkowskiVector v * pseudoscalar) := by
    rw [minkowskiVector_anticomm_pseudoscalar, neg_neg]
  have hie : pseudoscalar * ι e4Index = ι e4Index * pseudoscalar :=
    e4_commute_pseudoscalar.symm
  have h : pseudoscalar * (ι e4Index * minkowskiVector v) =
      -(ι e4Index * minkowskiVector v * pseudoscalar) := by
    rw [← mul_assoc, hie, mul_assoc, hvi, mul_neg, ← mul_assoc]
  rw [Generators.commutator, h, sub_neg_eq_add, two_smul]

theorem commutator_e4_mul_e4_mul (v X : PGA) :
    commutator (ι e4Index * v) (ι e4Index * X * pseudoscalar) = 0 := by
  have h1 : ι e4Index * v * (ι e4Index * X * pseudoscalar) = 0 := by
    rw [show ι e4Index * v * (ι e4Index * X * pseudoscalar) =
        ι e4Index * v * ι e4Index * X * pseudoscalar by simp only [mul_assoc],
      e4_mul_mul_e4, zero_mul, zero_mul]
  have h2 : ι e4Index * X * pseudoscalar * (ι e4Index * v) = 0 := by
    rw [show ι e4Index * X * pseudoscalar * (ι e4Index * v) =
        ι e4Index * X * (pseudoscalar * ι e4Index) * v by simp only [mul_assoc],
      ← e4_commute_pseudoscalar,
      show ι e4Index * X * (ι e4Index * pseudoscalar) * v =
        ι e4Index * X * ι e4Index * pseudoscalar * v by simp only [mul_assoc],
      e4_mul_mul_e4, zero_mul, zero_mul]
  rw [Generators.commutator, h1, h2, sub_zero]

/-- Velocity field of a Poincaré bivector: `[Ω_biv, P(x)] = e₄ (λ + [Ω_torsion, x]) i`. -/
theorem commutator_omegaBiv_event (p : OmegaParams) (x : Fin 4 → ℝ) :
    commutator (omegaBiv p) (event x) =
      ι e4Index * (minkowskiVector p.trans.lambda +
        commutator (omegaTorsion p.torsion) (minkowskiVector x)) * pseudoscalar := by
  have hL := omegaTorsion_mem_lorentzSpan p.torsion
  have hLi : commutator (omegaTorsion p.torsion) pseudoscalar = 0 := by
    rw [Generators.commutator, (commute_pseudoscalar_of_mem_lorentzSpan hL).eq, sub_self]
  rw [omegaBiv, omegaTrans_eq_half_e4, event, add_mul, one_mul, commutator_add_left,
    commutator_add_right, commutator_add_right, hLi, commutator_lorentz_e4_mul hL,
    commutator_smul_left, commutator_smul_left, commutator_e4_vec_pseudoscalar,
    commutator_e4_mul_e4_mul]
  simp only [mul_add, add_mul, smul_zero, add_zero, zero_add, smul_smul]
  module

/-- A translator moves events by its parameter: `T(λ) P(x) T(λ)˜ = P(x + λ)`. -/
theorem sandwich_expTrans_event (p : TransParams) (x : Fin 4 → ℝ) :
    sandwich (expTrans p) (event x) = event (x + p.lambda) := by
  rw [sandwich_expTrans, omegaTrans_eq_half_e4]
  have hev : event x = pseudoscalar + ι e4Index * minkowskiVector x * pseudoscalar := by
    rw [event, add_mul, one_mul]
  rw [hev, commutator_smul_left, commutator_add_right, commutator_e4_vec_pseudoscalar,
    commutator_e4_mul_e4_mul, event, minkowskiVector_add]
  simp only [add_zero, smul_smul, mul_add, add_mul, one_mul]
  module

/-- `K` as a Poincaré bivector with parameters: boost rate `κ`, time translation `ν`. -/
def killingParams (κ ν : ℝ) : OmegaParams := ⟨pureBoost κ, ⟨![ν, 0, 0, 0]⟩⟩

theorem omegaBiv_killingParams (κ ν : ℝ) :
    omegaBiv (killingParams κ ν) = killingBivector κ ν := by
  rw [omegaBiv, killingParams, omegaTorsion_pureBoost, killingBivector, omegaTrans,
    Fin.sum_univ_four]
  simp

theorem e4_e0_pseudoscalar_ne_zero : ι e4Index * ι 0 * pseudoscalar ≠ 0 := by
  intro h
  have h1 : dual (null 0) = 0 := by
    rw [dual, null_zero_eq, h]
  have h2 : dual (dual (null 0)) = -null 0 := dual_dual (null 0)
  rw [h1, show dual (0 : PGA) = 0 by simp [dual]] at h2
  exact null_ne_zero 0 (neg_eq_zero.mp h2.symm)

/-- Along the radial line the velocity of `K` is `(ν + κ s) e₀`. -/
theorem commutator_killing_event_radial (κ ν s : ℝ) :
    commutator (killingBivector κ ν) (event ![0, s, 0, 0]) =
      (ν + κ * s) • (ι e4Index * ι 0 * pseudoscalar) := by
  have hv : (killingParams κ ν).trans.lambda +
      lorentzAct (killingParams κ ν).torsion ![0, s, 0, 0] = ![ν + κ * s, 0, 0, 0] := by
    funext μ
    fin_cases μ <;> simp [killingParams, lorentzAct, pureBoost]
  rw [← omegaBiv_killingParams, commutator_omegaBiv_event,
    commutator_omegaTorsion_minkowskiVector, ← minkowskiVector_add, hv, minkowskiVector_vec]
  simp only [zero_smul, add_zero, mul_smul_comm, smul_mul_assoc]

/-- The velocity of `K` vanishes on the radial line exactly at `s = -ν/κ`. -/
theorem killing_velocity_eq_zero_iff (κ ν s : ℝ) :
    commutator (killingBivector κ ν) (event ![0, s, 0, 0]) = 0 ↔ ν + κ * s = 0 := by
  rw [commutator_killing_event_radial, smul_eq_zero]
  simp [e4_e0_pseudoscalar_ne_zero]

/-! ### Finite motion: the hovering hyperbola -/

theorem commute_pseudoscalar_rotorTorsion (t : TorsionParams) :
    Commute pseudoscalar (rotorTorsion t) := by
  rw [rotorTorsion]
  exact (commute_pseudoscalar_of_mem_lorentzSpan (omegaTorsion_mem_lorentzSpan t)).exp_right

theorem sandwich_pureBoost_minkowskiVector (φ : ℝ) (y : Fin 4 → ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (minkowskiVector y) =
      minkowskiVector (Sandwich.boostConjLambda φ y) := by
  rw [minkowskiVector_eq_sum, minkowskiVector_eq_sum, Fin.sum_univ_four, Fin.sum_univ_four,
    castAdd_zero, castAdd_one, castAdd_two, castAdd_three]
  simp only [sandwich_add, sandwich_smul, Sandwich.sandwich_pureBoost_ι0,
    Sandwich.sandwich_pureBoost_ι1, Sandwich.sandwich_pureBoost_ι2,
    Sandwich.sandwich_pureBoost_ι3, Sandwich.boostConjLambda]
  module

/-- A pure radial boost moves events by its Lorentz action. -/
theorem sandwich_pureBoost_event (φ : ℝ) (y : Fin 4 → ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (event y) =
      event (Sandwich.boostConjLambda φ y) := by
  have hm := rotor_unitary (pureBoost φ)
  have hi : sandwich (rotorTorsion (pureBoost φ)) pseudoscalar = pseudoscalar := by
    rw [Sandwich.sandwich, ← (commute_pseudoscalar_rotorTorsion _).eq, mul_assoc, hm, mul_one]
  have h1 : sandwich (rotorTorsion (pureBoost φ)) 1 = 1 := by
    simp [Sandwich.sandwich, hm]
  rw [event, event, sandwich_mul hm, sandwich_add, h1, sandwich_mul hm,
    Sandwich.sandwich_pureBoost_ι4, sandwich_pureBoost_minkowskiVector, hi]

/-- `exp(τK) = T R(κτ) T˜`: the static motion is a boost about the displaced axis. -/
theorem exp_smul_killingBivector (κ ℓ τ : ℝ) :
    exp (τ • killingBivector κ (κ * ℓ)) =
      sandwich (expTrans (radialShift ℓ)) (rotorTorsion (pureBoost (τ * κ))) := by
  rw [← sandwich_radialShift_boost, ← sandwich_smul,
    ← MotorGroup.sandwich_exp (expTrans_unitary _), rotorTorsion_pureBoost, smul_smul,
    show τ * (κ / 2) = τ * κ / 2 by ring]

theorem sandwich_exp_killingBivector (κ ℓ τ : ℝ) (y : Fin 4 → ℝ) :
    sandwich (exp (τ • killingBivector κ (κ * ℓ))) (event y) =
      event (Sandwich.boostConjLambda (τ * κ) (y + (negTrans (radialShift ℓ)).lambda) +
        (radialShift ℓ).lambda) := by
  rw [exp_smul_killingBivector,
    show sandwich (expTrans (radialShift ℓ)) (rotorTorsion (pureBoost (τ * κ))) =
      expTrans (radialShift ℓ) * rotorTorsion (pureBoost (τ * κ)) *
        reverse (expTrans (radialShift ℓ)) from rfl,
    sandwich_comp, sandwich_comp, reverse_expTrans, sandwich_expTrans_event,
    sandwich_pureBoost_event, sandwich_expTrans_event]

/-- Orbit of the observer's event under `exp(τK)`. -/
noncomputable def hoverWorldline (κ ℓ τ : ℝ) : Fin 4 → ℝ :=
  ![ℓ * Real.sinh (τ * κ), ℓ * (Real.cosh (τ * κ) - 1), 0, 0]

/-- The observer at the origin moves on `ℓ (sinh κτ, cosh κτ - 1, 0, 0)`. -/
theorem sandwich_exp_killing_event_zero (κ ℓ τ : ℝ) :
    sandwich (exp (τ • killingBivector κ (κ * ℓ))) (event 0) =
      event (hoverWorldline κ ℓ τ) := by
  rw [sandwich_exp_killingBivector]
  congr 1
  funext μ
  fin_cases μ
  all_goals simp [Sandwich.boostConjLambda, negTrans, radialShift, hoverWorldline]
  all_goals ring

/-- Every event of the axis `{t = 0, x = -ℓ}` is fixed by `exp(τK)`. -/
theorem sandwich_exp_killing_event_axis (κ ℓ τ y z : ℝ) :
    sandwich (exp (τ • killingBivector κ (κ * ℓ))) (event ![0, -ℓ, y, z]) =
      event ![0, -ℓ, y, z] := by
  rw [sandwich_exp_killingBivector]
  congr 1
  funext μ
  fin_cases μ <;> simp [Sandwich.boostConjLambda, negTrans, radialShift, Matrix.vecHead,
    Matrix.vecTail]

/-- The hovering orbit keeps the constant interval `ℓ²` from the axis event `-ℓ e₁`. -/
theorem hoverWorldline_interval (κ ℓ τ : ℝ) :
    Q31 (hoverWorldline κ ℓ τ - (radialShift ℓ).lambda) = ℓ ^ 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (τ * κ)
  rw [Q31_eq_minkowskiDot]
  simp only [minkowskiDot, hoverWorldline, radialShift, Pi.sub_apply]
  simp
  linear_combination ℓ ^ 2 * h

/-- The orbit bends away from the axis: its radial coordinate never becomes negative. -/
theorem hoverWorldline_radial_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (κ τ : ℝ) :
    0 ≤ hoverWorldline κ ℓ τ 1 := by
  simp only [hoverWorldline, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact mul_nonneg hℓ (sub_nonneg.mpr (Real.one_le_cosh _))

/-! ### The Killing norm and the sign of `J` -/

/-- Squared Killing norm of the velocity field: `N²(x) = -(λ + ω x)²`. -/
noncomputable def killingNormSq (p : OmegaParams) (x : Fin 4 → ℝ) : ℝ :=
  -Q31 (p.trans.lambda + lorentzAct p.torsion x)

/-- The velocity `λ + [Ω_torsion, x]` of `P(x)` squares to `-N²(x)`. -/
theorem killingVelocity_sq (p : OmegaParams) (x : Fin 4 → ℝ) :
    (minkowskiVector p.trans.lambda + commutator (omegaTorsion p.torsion) (minkowskiVector x)) *
      (minkowskiVector p.trans.lambda +
        commutator (omegaTorsion p.torsion) (minkowskiVector x)) =
      algebraMap ℝ PGA (-killingNormSq p x) := by
  rw [commutator_omegaTorsion_minkowskiVector, ← minkowskiVector_add, minkowskiVector_sq,
    killingNormSq, neg_neg]

/-- Exact second differences: the d'Alembertian of `N²` is `8J`, at every event,
for every step, whatever the translation part. -/
theorem killingNormSq_dAlembertian (p : OmegaParams) (x : Fin 4 → ℝ) (h : ℝ) :
    ∑ μ : Fin 4, w31 μ * (killingNormSq p (x + h • e4vec μ) +
        killingNormSq p (x - h • e4vec μ) - 2 * killingNormSq p x) =
      8 * Invariant.J p.torsion * h ^ 2 := by
  rw [Invariant.J_coef]
  simp [killingNormSq, Q31_eq_minkowskiDot, minkowskiDot, lorentzAct, Fin.sum_univ_four,
    Fin.sum_univ_three, e4vec, w31, Pi.single_apply]
  ring

/-- Hyperbolic model: along the radial line `N² = (ν + κ s)²`, growing away from the axis. -/
theorem killingNormSq_killingParams_radial (κ ν s : ℝ) :
    killingNormSq (killingParams κ ν) ![0, s, 0, 0] = (ν + κ * s) ^ 2 := by
  simp [killingNormSq, killingParams, Q31_eq_minkowskiDot, minkowskiDot, lorentzAct, pureBoost]
  ring

/-- Elliptic model: rotation `ω` in the `(y,z)` plane with time translation `ν` along its axis. -/
def rotationParams (ω ν : ℝ) : OmegaParams := ⟨⟨fun _ => 0, ![ω, 0, 0]⟩, ⟨![ν, 0, 0, 0]⟩⟩

theorem omegaTorsion_rotationParams (ω ν : ℝ) :
    omegaTorsion (rotationParams ω ν).torsion = (ω / 2) • cyclic 0 := by
  simp [omegaTorsion, rotationParams, Fin.sum_univ_three]

/-- Elliptic model: `N² = ν² - ω² y²`, shrinking away from the axis. -/
theorem killingNormSq_rotationParams (ω ν y : ℝ) :
    killingNormSq (rotationParams ω ν) ![0, 0, y, 0] = ν ^ 2 - ω ^ 2 * y ^ 2 := by
  simp [killingNormSq, rotationParams, Q31_eq_minkowskiDot, minkowskiDot, lorentzAct]
  ring

theorem J_rotationParams (ω ν : ℝ) :
    Invariant.J (rotationParams ω ν).torsion = -(1 / 2) * ω ^ 2 := by
  rw [Invariant.J_coef]
  simp [rotationParams, Fin.sum_univ_three]

/-! ### Free fall in the flat flow -/

/-- Minkowski product `⟨x,y⟩ = -x⁰y⁰ + xⁱyⁱ`. -/
def minkowskiProd (x y : Fin 4 → ℝ) : ℝ :=
  -x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

theorem minkowskiProd_smul_left (c : ℝ) (x y : Fin 4 → ℝ) :
    minkowskiProd (c • x) y = c * minkowskiProd x y := by
  simp only [minkowskiProd, Pi.smul_apply, smul_eq_mul]
  ring

/-- Inertial worldline of a body released from rest at the origin: `s e₀`. -/
def releasedWorldline (s : ℝ) : Fin 4 → ℝ := ![s, 0, 0, 0]

theorem releasedWorldline_eq_smul (s : ℝ) : releasedWorldline s = s • e4vec 0 := by
  ext μ
  fin_cases μ <;> simp [releasedWorldline, e4vec]

theorem Q31_time_unit : Q31 (e4vec 0) = -1 := by
  simp [Q31_eq_minkowskiDot, minkowskiDot, e4vec]

/-- Unit 4-velocity of the hovering observer at flow parameter `τ`. -/
noncomputable def hoverVelocity (κ τ : ℝ) : Fin 4 → ℝ :=
  ![Real.cosh (τ * κ), Real.sinh (τ * κ), 0, 0]

/-- Unit spacelike normal, orthogonal to `hoverVelocity`. At `τ = 0` it is `+e₁`. -/
noncomputable def hoverOutward (κ τ : ℝ) : Fin 4 → ℝ :=
  ![Real.sinh (τ * κ), Real.cosh (τ * κ), 0, 0]

theorem hoverOutward_zero (κ : ℝ) : hoverOutward κ 0 = e4vec 1 := by
  ext μ
  fin_cases μ <;> simp [hoverOutward, e4vec, Real.sinh_zero, Real.cosh_zero]

theorem Q31_hoverVelocity (κ τ : ℝ) : Q31 (hoverVelocity κ τ) = -1 := by
  rw [Q31_eq_minkowskiDot]
  have h := Real.cosh_sq_sub_sinh_sq (τ * κ)
  simp [minkowskiDot, hoverVelocity]
  linear_combination -h

theorem Q31_hoverOutward (κ τ : ℝ) : Q31 (hoverOutward κ τ) = 1 := by
  rw [Q31_eq_minkowskiDot]
  have h := Real.cosh_sq_sub_sinh_sq (τ * κ)
  simp [minkowskiDot, hoverOutward]
  linear_combination h

theorem minkowskiProd_hoverVelocity_outward (κ τ : ℝ) :
    minkowskiProd (hoverVelocity κ τ) (hoverOutward κ τ) = 0 := by
  simp [minkowskiProd, hoverVelocity, hoverOutward]
  ring

theorem hasDerivAt_hoverTime (κ ℓ τ : ℝ) :
    HasDerivAt (fun t => hoverWorldline κ ℓ t 0) (ℓ * κ * Real.cosh (τ * κ)) τ := by
  have hmul := (hasDerivAt_id τ).mul_const κ
  simp only [id_eq, one_mul] at hmul
  have hsinh := ((Real.hasDerivAt_sinh (τ * κ)).comp τ hmul).const_mul ℓ
  simp only [Function.comp] at hsinh
  have hfun : (fun t => ℓ * Real.sinh (t * κ)) = fun t => hoverWorldline κ ℓ t 0 := by
    ext t
    simp [hoverWorldline]
  rw [← hfun]
  exact hsinh.congr_deriv (by ring)

theorem hasDerivAt_hoverRadial (κ ℓ τ : ℝ) :
    HasDerivAt (fun t => hoverWorldline κ ℓ t 1) (ℓ * κ * Real.sinh (τ * κ)) τ := by
  have hmul := (hasDerivAt_id τ).mul_const κ
  simp only [id_eq, one_mul] at hmul
  have hcosh := (((Real.hasDerivAt_cosh (τ * κ)).comp τ hmul).sub_const 1).const_mul ℓ
  simp only [Function.comp] at hcosh
  have hfun : (fun t => ℓ * (Real.cosh (t * κ) - 1)) = fun t => hoverWorldline κ ℓ t 1 := by
    ext t
    simp [hoverWorldline]
  rw [← hfun]
  exact hcosh.congr_deriv (by ring)

/-- The tangent `(d/dτ) X` has interval `-(ℓ κ)²`, so proper time runs at rate `|ℓ κ|`. -/
theorem hoverTangent_interval (κ ℓ τ : ℝ) :
    Q31 ((ℓ * κ) • hoverVelocity κ τ) = -(ℓ * κ) ^ 2 := by
  rw [Q31_eq_minkowskiDot]
  have h := Real.cosh_sq_sub_sinh_sq (τ * κ)
  simp [minkowskiDot, Pi.smul_apply, smul_eq_mul, hoverVelocity]
  linear_combination -(ℓ * κ) ^ 2 * h

/-- Proper-time reparametrization: rapidity `κτ` becomes `σ/ℓ` when `σ = ℓ κ τ`. -/
theorem hoverWorldline_proper {κ ℓ σ : ℝ} (hℓ : ℓ ≠ 0) (hκ : κ ≠ 0) :
    hoverWorldline κ ℓ (σ / (ℓ * κ)) =
      ![ℓ * Real.sinh (σ / ℓ), ℓ * (Real.cosh (σ / ℓ) - 1), 0, 0] := by
  ext μ
  fin_cases μ
  · simp only [hoverWorldline]
    rw [show (σ / (ℓ * κ)) * κ = σ / ℓ by field_simp]
  · simp only [hoverWorldline]
    rw [show (σ / (ℓ * κ)) * κ = σ / ℓ by field_simp]
  · simp [hoverWorldline]
  · simp [hoverWorldline]

/-- Seen from the hovering observer, the inertial frame of release is the inverse motor:
a boost of rapidity `-κτ` about the same axis. -/
theorem exp_neg_killing_eq_displacedBoost (κ ℓ τ : ℝ) :
    exp ((-τ) • killingBivector κ (κ * ℓ)) =
      sandwich (expTrans (radialShift ℓ)) (rotorTorsion (pureBoost (-(τ * κ)))) := by
  rw [show -(τ * κ) = (-τ) * κ by ring]
  exact exp_smul_killingBivector κ ℓ (-τ)

/-- Proper time on the inertial line at which the event is simultaneous with
the observer at flow parameter `τ`. -/
noncomputable def releasedSimulTime (ℓ κ τ : ℝ) : ℝ :=
  ℓ * Real.tanh (τ * κ)

/-- Signed separation along `hoverOutward`: `ℓ (sech(κτ) - 1)`. -/
noncomputable def releasedDisplacement (ℓ κ τ : ℝ) : ℝ :=
  ℓ * ((Real.cosh (τ * κ))⁻¹ - 1)

/-- The same separation in observer proper time `σ`, with rapidity `σ/ℓ`. -/
noncomputable def releasedDisplacementProper (ℓ σ : ℝ) : ℝ :=
  ℓ * ((Real.cosh (σ / ℓ))⁻¹ - 1)

theorem released_simultaneous_prod (ℓ κ τ s : ℝ) :
    minkowskiProd (releasedWorldline s - hoverWorldline κ ℓ τ) (hoverVelocity κ τ) =
      ℓ * Real.sinh (τ * κ) - s * Real.cosh (τ * κ) := by
  simp [minkowskiProd, releasedWorldline, hoverWorldline, hoverVelocity, Pi.sub_apply]
  ring

theorem released_simultaneous_iff (ℓ κ τ s : ℝ) :
    minkowskiProd (releasedWorldline s - hoverWorldline κ ℓ τ) (hoverVelocity κ τ) = 0 ↔
      s = releasedSimulTime ℓ κ τ := by
  have hc : Real.cosh (τ * κ) ≠ 0 := (Real.cosh_pos _).ne'
  rw [released_simultaneous_prod, releasedSimulTime, Real.tanh_eq_sinh_div_cosh]
  constructor
  · intro h
    have hs : s * Real.cosh (τ * κ) = ℓ * Real.sinh (τ * κ) := by linarith
    apply mul_left_cancel₀ hc
    field_simp at hs ⊢
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- The simultaneous separation is the signed multiple of the outward normal. -/
theorem released_separation_eq_displacement (ℓ κ τ : ℝ) :
    releasedWorldline (releasedSimulTime ℓ κ τ) - hoverWorldline κ ℓ τ =
      releasedDisplacement ℓ κ τ • hoverOutward κ τ := by
  ext μ
  fin_cases μ
  · simp [releasedWorldline, releasedSimulTime, hoverWorldline, releasedDisplacement,
      hoverOutward, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos _).ne']
  · simp [releasedWorldline, releasedSimulTime, hoverWorldline, releasedDisplacement,
      hoverOutward, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos _).ne']
    ring
  · simp [releasedWorldline, hoverWorldline, releasedDisplacement, hoverOutward, Pi.sub_apply,
      Pi.smul_apply]
  · simp [releasedWorldline, hoverWorldline, releasedDisplacement, hoverOutward, Pi.sub_apply,
      Pi.smul_apply]

theorem releasedDisplacement_eq_proper {ℓ κ τ : ℝ} (hℓ : ℓ ≠ 0) :
    releasedDisplacement ℓ κ τ = releasedDisplacementProper ℓ (ℓ * κ * τ) := by
  simp only [releasedDisplacement, releasedDisplacementProper]
  congr 1
  rw [show (ℓ * κ * τ) / ℓ = τ * κ by field_simp]

theorem releasedDisplacementProper_zero (ℓ : ℝ) : releasedDisplacementProper ℓ 0 = 0 := by
  simp [releasedDisplacementProper, Real.cosh_zero, zero_div]

theorem releasedDisplacementProper_nonpos {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (σ : ℝ) :
    releasedDisplacementProper ℓ σ ≤ 0 := by
  have hp := Real.cosh_pos (σ / ℓ)
  have hinv : (Real.cosh (σ / ℓ))⁻¹ ≤ 1 := (inv_le_one₀ hp).2 (Real.one_le_cosh _)
  exact mul_nonpos_of_nonneg_of_nonpos hℓ (sub_nonpos.mpr hinv)

theorem releasedDisplacementProper_lt_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {σ : ℝ} (hσ : σ ≠ 0) :
    releasedDisplacementProper ℓ σ < 0 := by
  have hcosh : 1 < Real.cosh (σ / ℓ) :=
    Real.one_lt_cosh.2 (div_ne_zero hσ hℓ.ne')
  have hinv : (Real.cosh (σ / ℓ))⁻¹ < 1 :=
    (inv_lt_one₀ (Real.cosh_pos _)).2 hcosh
  exact mul_neg_of_pos_of_neg hℓ (sub_lt_zero.mpr hinv)

theorem hasDerivAt_releasedDisplacementProper {ℓ : ℝ} (hℓ : ℓ ≠ 0) (σ : ℝ) :
    HasDerivAt (releasedDisplacementProper ℓ)
      (-Real.sinh (σ / ℓ) / Real.cosh (σ / ℓ) ^ 2) σ := by
  have harg := (hasDerivAt_id σ).div_const ℓ
  simp only [id_eq] at harg
  have hcosh := (Real.hasDerivAt_cosh (σ / ℓ)).comp σ harg
  have hinv := hcosh.inv (Real.cosh_pos _).ne'
  have hmul := (hinv.sub_const (1 : ℝ)).const_mul ℓ
  unfold releasedDisplacementProper
  exact hmul.congr_deriv <| by
    simp only [Function.comp]
    field_simp [hℓ]

theorem deriv_releasedDisplacementProper {ℓ : ℝ} (hℓ : ℓ ≠ 0) (σ : ℝ) :
    deriv (releasedDisplacementProper ℓ) σ =
      -Real.sinh (σ / ℓ) / Real.cosh (σ / ℓ) ^ 2 :=
  (hasDerivAt_releasedDisplacementProper hℓ σ).deriv

theorem deriv_releasedDisplacementProper_zero {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    deriv (releasedDisplacementProper ℓ) 0 = 0 := by
  rw [deriv_releasedDisplacementProper hℓ]
  simp [Real.sinh_zero, Real.cosh_zero]

theorem hasDerivAt_releasedSpeed_zero {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    HasDerivAt (fun σ : ℝ => -Real.sinh (σ / ℓ) / Real.cosh (σ / ℓ) ^ 2) (-1 / ℓ) 0 := by
  have harg := (hasDerivAt_id 0).div_const ℓ
  simp only [id_eq] at harg
  have hsinh := ((Real.hasDerivAt_sinh (0 / ℓ)).comp 0 harg).neg
  have hcosh := (Real.hasDerivAt_cosh (0 / ℓ)).comp 0 harg
  have hden := hcosh.pow 2
  have hpos : ((Real.cosh ∘ fun x => x / ℓ) ^ 2) 0 ≠ 0 := by
    simp [Function.comp, Real.cosh_zero]
  have hdiv := hsinh.div hden hpos
  exact hdiv.congr_deriv <| by
    simp [Real.sinh_zero, Real.cosh_zero, zero_div]
    field_simp [hℓ]

/-- Initial acceleration toward the negative outward normal: `ξ''(0) = -1/ℓ`. -/
theorem released_initial_acceleration {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    deriv (deriv (releasedDisplacementProper ℓ)) 0 = -1 / ℓ := by
  have hfun : deriv (releasedDisplacementProper ℓ) =
      fun σ => -Real.sinh (σ / ℓ) / Real.cosh (σ / ℓ) ^ 2 := by
    ext σ
    exact deriv_releasedDisplacementProper hℓ σ
  rw [hfun]
  exact (hasDerivAt_releasedSpeed_zero hℓ).deriv

/-- As the observer's proper time tends to infinity, the simultaneous separation
approaches `-ℓ`: the body approaches the axis on the observer's simultaneity. -/
theorem tendsto_releasedDisplacementProper_atTop {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (releasedDisplacementProper ℓ) atTop (𝓝 (-ℓ)) := by
  have hdiv : Tendsto (fun σ : ℝ => σ / ℓ) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hℓ).2 tendsto_id
  have hexp : Tendsto (fun σ => Real.exp (σ / ℓ) / 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2
      (Real.tendsto_exp_atTop.comp hdiv)
  have hle : ∀ σ, Real.exp (σ / ℓ) / 2 ≤ Real.cosh (σ / ℓ) := by
    intro σ
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(σ / ℓ))]
  have hcosh : Tendsto (fun σ => Real.cosh (σ / ℓ)) atTop atTop :=
    tendsto_atTop_mono hle hexp
  have hinv : Tendsto (fun σ => (Real.cosh (σ / ℓ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcosh
  have hmul := ((hinv.sub_const 1).const_mul ℓ)
  unfold releasedDisplacementProper
  simpa [sub_eq_add_neg] using hmul

theorem released_axis_interval (ℓ s : ℝ) :
    Q31 (releasedWorldline s - (radialShift ℓ).lambda) = ℓ ^ 2 - s ^ 2 := by
  rw [Q31_eq_minkowskiDot]
  simp only [minkowskiDot, releasedWorldline, radialShift, Pi.sub_apply]
  simp
  ring

/-- The inertial line meets the light cone of the axis event at proper time `±ℓ`. -/
theorem released_lightcone_iff (ℓ s : ℝ) :
    Q31 (releasedWorldline s - (radialShift ℓ).lambda) = 0 ↔ s = ℓ ∨ s = -ℓ := by
  rw [released_axis_interval]
  constructor
  · intro h
    have hs : s ^ 2 = ℓ ^ 2 := by linarith
    exact (sq_eq_sq_iff_eq_or_eq_neg).1 hs
  · rintro (rfl | rfl) <;> ring

/-- That meeting point lies on the Killing horizon `N = 0`. -/
theorem released_on_killingHorizon (κ ℓ : ℝ) :
    killingNormSq (killingParams κ (κ * ℓ)) (releasedWorldline ℓ) = 0 := by
  simp [killingNormSq, killingParams, releasedWorldline, lorentzAct, pureBoost,
    Q31_eq_minkowskiDot, minkowskiDot]

/-! ### Exterior Schwarzschild -/

/-- Killing norm of `∂_t`: `ν = √A`. -/
noncomputable def killingNorm (rs r : ℝ) : ℝ :=
  Real.sqrt (schwarzschildA rs r)

/-- Boost rate of the static Killing bivector: `κ = rₛ/(2r²)`. -/
noncomputable def killingRate (rs r : ℝ) : ℝ :=
  rs / (2 * r ^ 2)

/-- Distance from the static observer to the axis: `ℓ = ν/κ`. -/
noncomputable def axisDistance (rs r : ℝ) : ℝ :=
  killingNorm rs r / killingRate rs r

/-- Static Killing bivector at radius `r`. -/
noncomputable def staticKilling (rs r : ℝ) : PGA :=
  killingBivector (killingRate rs r) (killingNorm rs r)

theorem hasDerivAt_schwarzschildA (rs : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (schwarzschildA rs) (rs / r ^ 2) r := by
  have h : HasDerivAt (fun x => 1 - rs * x⁻¹) (-(rs * -(r ^ 2)⁻¹)) r :=
    ((hasDerivAt_inv hr).const_mul rs).const_sub 1
  have hfun : (fun x => 1 - rs * x⁻¹) = schwarzschildA rs := by
    funext x
    simp [schwarzschildA, div_eq_mul_inv]
  rw [hfun] at h
  convert h using 1
  ring

/-- `ν' = ∂_r √A`. -/
theorem hasDerivAt_killingNorm {rs r : ℝ} (h : IsExterior rs r) :
    HasDerivAt (killingNorm rs) (dSqrtA_dr rs r) r := by
  have hr : r ≠ 0 := (lt_trans h.1 h.2).ne'
  have hA := schwarzschildA_pos h
  have hd : HasDerivAt (killingNorm rs)
      (rs / r ^ 2 / (2 * Real.sqrt (schwarzschildA rs r))) r :=
    (hasDerivAt_schwarzschildA rs hr).sqrt hA.ne'
  refine hd.congr_deriv ?_
  rw [dSqrtA_dr]
  ring

theorem killingNorm_pos {rs r : ℝ} (h : IsExterior rs r) : 0 < killingNorm rs r :=
  Real.sqrt_pos.mpr (schwarzschildA_pos h)

/-- The boost rate has the sign of the mass. -/
theorem killingRate_pos_iff {rs r : ℝ} (hr : r ≠ 0) : 0 < killingRate rs r ↔ 0 < rs := by
  unfold killingRate
  have h2 : 0 < 2 * r ^ 2 := by positivity
  exact div_pos_iff_of_pos_right h2

theorem killingRate_pos {rs r : ℝ} (h : IsExterior rs r) : 0 < killingRate rs r :=
  (killingRate_pos_iff (lt_trans h.1 h.2).ne').mpr h.1

/-- `κ = ½ A'`. -/
theorem killingRate_eq_half_deriv (rs r : ℝ) : killingRate rs r = (1 / 2) * (rs / r ^ 2) := by
  unfold killingRate
  ring

/-- `κ = ν ν'`: the proper radial derivative of the Killing norm. -/
theorem killingRate_eq_norm_mul_deriv {rs r : ℝ} (h : IsExterior rs r) :
    killingRate rs r = killingNorm rs r * dSqrtA_dr rs r := by
  have hs := (killingNorm_pos h).ne'
  unfold killingNorm at hs ⊢
  rw [killingRate, dSqrtA_dr]
  field_simp

/-- Gauss's law for the boost part: `r² κ = rₛ/2`. -/
theorem sq_mul_killingRate (rs : ℝ) {r : ℝ} (hr : r ≠ 0) : r ^ 2 * killingRate rs r = rs / 2 := by
  unfold killingRate
  field_simp

theorem killingNorm_eq_exp {rs r : ℝ} (h : IsExterior rs r) :
    killingNorm rs r = Real.exp (-schwarzschildRapidity rs r) :=
  (exp_neg_schwarzschildRapidity h.1 h.2).symm

theorem axisDistance_pos {rs r : ℝ} (h : IsExterior rs r) : 0 < axisDistance rs r :=
  div_pos (killingNorm_pos h) (killingRate_pos h)

/-- `κ ℓ = ν`. -/
theorem killingRate_mul_axisDistance {rs r : ℝ} (h : IsExterior rs r) :
    killingRate rs r * axisDistance rs r = killingNorm rs r :=
  mul_div_cancel₀ _ (killingRate_pos h).ne'

theorem axisDistance_eq {rs r : ℝ} (h : IsExterior rs r) :
    axisDistance rs r = 2 / rs * r ^ 2 * killingNorm rs r := by
  have hrs := h.1.ne'
  have hr := (lt_trans h.1 h.2).ne'
  rw [axisDistance, killingRate]
  field_simp

/-- `ℓ · ∂_r√A = 1`: the axis distance is the inverse hover acceleration. -/
theorem axisDistance_mul_dSqrtA_dr {rs r : ℝ} (h : IsExterior rs r) :
    axisDistance rs r * dSqrtA_dr rs r = 1 := by
  have hs := (killingNorm_pos h).ne'
  have hk := (killingRate_pos h).ne'
  have hrs := h.1.ne'
  have hr := (lt_trans h.1 h.2).ne'
  rw [axisDistance, dSqrtA_dr]
  unfold killingNorm killingRate at *
  field_simp

/-- The hover acceleration is the time-leg Weitzenböck torsion `T⁰_{rt}`. -/
theorem axisDistance_mul_torsion {rs r : ℝ} (h : IsExterior rs r) (θ : ℝ) :
    axisDistance rs r * weitzenbockTorsion (schwarzschildPartials rs r θ) 0 1 0 = 1 := by
  rw [schwarzschild_torsion_T0_r_t]
  exact axisDistance_mul_dSqrtA_dr h

/-- In rapidity: `ℓ · (-√A φ') = 1`; gravity points up the rapidity gradient. -/
theorem axisDistance_mul_rapidity {rs r : ℝ} (h : IsExterior rs r) :
    axisDistance rs r * (-(dRapidity_dr rs r) * killingNorm rs r) = 1 := by
  rw [killingNorm, ← dSqrtA_dr_eq_neg_dRapidity_mul_sqrtA h]
  exact axisDistance_mul_dSqrtA_dr h

theorem dRapidity_dr_neg {rs r : ℝ} (h : IsExterior rs r) : dRapidity_dr rs r < 0 := by
  have hr : 0 < r := lt_trans h.1 h.2
  have hA := schwarzschildA_pos h
  have := h.1
  rw [dRapidity_dr_eq]
  have : 0 < rs / (2 * r ^ 2 * schwarzschildA rs r) := by positivity
  linarith

/-- The static Killing bivector is the pure boost `(κ/2) B⁺` moved inward by `ℓ`. -/
theorem staticKilling_eq_sandwich {rs r : ℝ} (h : IsExterior rs r) :
    staticKilling rs r =
      sandwich (expTrans (radialShift (axisDistance rs r)))
        ((killingRate rs r / 2) • hyperbolic 0) := by
  rw [sandwich_radialShift_boost, killingRate_mul_axisDistance h, staticKilling]

/-- On the radial line the static motion stops exactly at `s = -ℓ`. -/
theorem staticKilling_velocity_eq_zero_iff {rs r : ℝ} (h : IsExterior rs r) (s : ℝ) :
    commutator (staticKilling rs r) (event ![0, s, 0, 0]) = 0 ↔ s = -axisDistance rs r := by
  rw [staticKilling, killing_velocity_eq_zero_iff, ← killingRate_mul_axisDistance h, ← mul_add,
    mul_eq_zero, or_iff_right (killingRate_pos h).ne']
  constructor <;> intro hs <;> linarith

/-- The static observer's orbit is the hovering hyperbola about the inward axis. -/
theorem sandwich_exp_staticKilling_event_zero {rs r : ℝ} (h : IsExterior rs r) (τ : ℝ) :
    sandwich (exp (τ • staticKilling rs r)) (event 0) =
      event (hoverWorldline (killingRate rs r) (axisDistance rs r) τ) := by
  rw [staticKilling, ← killingRate_mul_axisDistance h, sandwich_exp_killing_event_zero]

/-- The axis recedes monotonically with radius. -/
theorem axisDistance_strictMonoOn {rs : ℝ} (hrs : 0 < rs) :
    StrictMonoOn (axisDistance rs) (Ioi rs) := by
  intro r1 hr1 r2 hr2 hlt
  simp only [mem_Ioi] at hr1 hr2
  have h1 : IsExterior rs r1 := ⟨hrs, hr1⟩
  have h2 : IsExterior rs r2 := ⟨hrs, hr2⟩
  rw [axisDistance_eq h1, axisDistance_eq h2]
  have hA := schwarzschildA_strictMonoOn hrs (mem_Ioi.mpr hr1) (mem_Ioi.mpr hr2) hlt
  have hs : killingNorm rs r1 < killingNorm rs r2 :=
    Real.sqrt_lt_sqrt (schwarzschildA_pos h1).le hA
  have hn1 := killingNorm_pos h1
  have hr1pos : 0 < r1 := hrs.trans hr1
  have hsq : r1 ^ 2 < r2 ^ 2 := pow_lt_pow_left₀ hlt hr1pos.le (by norm_num)
  have hc : 0 < 2 / rs := div_pos two_pos hrs
  have hprod : r1 ^ 2 * killingNorm rs r1 < r2 ^ 2 * killingNorm rs r2 := by
    have hr2sq : 0 < r2 ^ 2 := pow_pos (hrs.trans hr2) 2
    nlinarith [mul_lt_mul_of_pos_right hsq hn1, mul_lt_mul_of_pos_left hs hr2sq]
  have := mul_lt_mul_of_pos_left hprod hc
  simpa [mul_assoc] using this

theorem tendsto_killingNorm_horizon {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (killingNorm rs) (𝓝[>] rs) (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_schwarzschildA_nhdsWithin_gt hrs)
  rw [Real.sqrt_zero] at h
  exact h

theorem tendsto_killingRate_horizon {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (killingRate rs) (𝓝[>] rs) (𝓝 (1 / (2 * rs))) := by
  have hc : ContinuousAt (fun r : ℝ => rs / (2 * r ^ 2)) rs :=
    continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 2))
      (mul_ne_zero two_ne_zero (pow_ne_zero 2 hrs.ne'))
  have h : Tendsto (fun r : ℝ => rs / (2 * r ^ 2)) (𝓝[>] rs) (𝓝 (rs / (2 * rs ^ 2))) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hval : rs / (2 * rs ^ 2) = 1 / (2 * rs) := by
    field_simp
  rw [hval] at h
  exact h

/-- At the horizon the axis reaches the observer. -/
theorem tendsto_axisDistance_horizon {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (axisDistance rs) (𝓝[>] rs) (𝓝 0) := by
  have h := (tendsto_killingNorm_horizon hrs).div (tendsto_killingRate_horizon hrs)
    (div_ne_zero one_ne_zero (mul_ne_zero two_ne_zero hrs.ne'))
  rw [zero_div] at h
  exact h

/-- At the horizon `K` becomes the pure boost of rate `1/(2rₛ)`, the surface gravity. -/
theorem tendsto_staticKilling_horizon {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (staticKilling rs) (𝓝[>] rs) (𝓝 ((1 / (4 * rs)) • hyperbolic 0)) := by
  have h := (((tendsto_killingRate_horizon hrs).div_const 2).smul_const (hyperbolic 0)).add
    (((tendsto_killingNorm_horizon hrs).div_const 2).smul_const (null 0))
  have hval : (1 / (2 * rs) / 2) • hyperbolic 0 + ((0 : ℝ) / 2) • null 0 =
      (1 / (4 * rs)) • hyperbolic 0 := by
    rw [zero_div, zero_smul, add_zero]
    congr 1
    field_simp
    ring
  rw [hval] at h
  exact h

theorem tendsto_killingNorm_atTop (rs : ℝ) :
    Tendsto (killingNorm rs) atTop (𝓝 1) := by
  have h := (Real.continuous_sqrt.tendsto 1).comp (tendsto_schwarzschildA_atTop rs)
  rw [Real.sqrt_one] at h
  exact h

theorem tendsto_killingRate_atTop (rs : ℝ) :
    Tendsto (killingRate rs) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop two_ne_zero).const_mul_atTop two_pos)

/-- Far away the axis recedes without bound. -/
theorem tendsto_axisDistance_atTop {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (axisDistance rs) atTop atTop := by
  have hpow : Tendsto (fun r : ℝ => 2 / rs * r ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop (div_pos two_pos hrs)
  have h := hpow.atTop_mul_pos one_pos (tendsto_killingNorm_atTop rs)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop rs] with r hr
  rw [axisDistance_eq ⟨hrs, hr⟩]

/-- Far away `K` becomes the pure time translation `½ N₀`. -/
theorem tendsto_staticKilling_atTop (rs : ℝ) :
    Tendsto (staticKilling rs) atTop (𝓝 ((1 / 2 : ℝ) • null 0)) := by
  have h := (((tendsto_killingRate_atTop rs).div_const 2).smul_const (hyperbolic 0)).add
    (((tendsto_killingNorm_atTop rs).div_const 2).smul_const (null 0))
  rw [zero_div, zero_smul, zero_add] at h
  exact h

/-- The torsional scalar of the Killing boost is the redshifted field seed. -/
theorem J_killingRate {rs r : ℝ} (h : IsExterior rs r) :
    Invariant.J (pureBoost (killingRate rs r)) = schwarzschildA rs r ^ 2 * J_field rs r := by
  have hA := (schwarzschildA_pos h).ne'
  have hr := (lt_trans h.1 h.2).ne'
  rw [J_pureBoost, J_field_coef h, killingRate]
  field_simp
  ring

/-- Per unit proper time the boost rate is the hover acceleration, with `J = A J_field`. -/
theorem J_hoverAcceleration {rs r : ℝ} (h : IsExterior rs r) :
    Invariant.J (pureBoost (dSqrtA_dr rs r)) = schwarzschildA rs r * J_field rs r := by
  have hApos := schwarzschildA_pos h
  have hA := hApos.ne'
  have hr := (lt_trans h.1 h.2).ne'
  have hs2 : Real.sqrt (schwarzschildA rs r) ^ 2 = schwarzschildA rs r := Real.sq_sqrt hApos.le
  rw [J_pureBoost, J_field_coef h, dSqrtA_dr, div_pow, hs2]
  field_simp
  ring

/-- On the exterior chart the flat-model initial acceleration is `-∂_r √A`. -/
theorem released_initial_acceleration_exterior {rs r : ℝ} (h : IsExterior rs r) :
    deriv (deriv (releasedDisplacementProper (axisDistance rs r))) 0 =
      -dSqrtA_dr rs r := by
  have hℓ := axisDistance_pos h
  rw [released_initial_acceleration hℓ.ne']
  have hdiv : dSqrtA_dr rs r = 1 / axisDistance rs r := by
    rw [eq_div_iff hℓ.ne', mul_comm]
    exact axisDistance_mul_dSqrtA_dr h
  rw [hdiv]
  ring

end KillingAxis

end Gravity

end DstDiophantine
