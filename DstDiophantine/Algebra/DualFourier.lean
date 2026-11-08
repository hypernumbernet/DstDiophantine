import DstDiophantine.Algebra.DirichletKernel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Notation.Support
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fourier analysis on the discrete dual circle

The dual angle is discretised as `θ ∈ (2π/N) ℤ`, with the usual rapidity left
continuous. Amplitudes on that circle, and on the three dual angles
`(ℤ/Nℤ)³`, form finite Hilbert spaces. The Fourier transform onto winding
labels is unitary there.

The normalised Dirichlet kernel is the average of `N` phases of unit modulus.
Those centered phases are not identified with the characters of `ℤ/Nℤ`: the
offset `(N-1)/2` is an integer mode only for odd `N`.

Shift of the angle and multiplication by a winding character preserve the
inner product, return the amplitude after `N` steps and after no fewer positive
number of steps, and differ by the phase `χ_r(s)`. The transform turns a shift
into that multiplication, a multiplication into a shift of the winding label,
and circular convolution into a product. A nonzero amplitude and its transform
have supports whose cardinalities multiply to at least `N`, and to at least
`N³` on the three dual angles; both bounds are attained. An amplitude that
separates across the three angles has transform equal to the product of the
three circle transforms.

This is not the state space `ℂ²` and not the indefinite Killing pairing.
The finite space is not the operator pair on the chart. On one chart axis
the same shift and clock, read at the `N` samples of one period, are that
chart's translation and momentum kick (`Logic.Quantum.AngleChart`).
-/

namespace DstDiophantine

namespace DualFourier

open Complex Finset
open scoped BigOperators ComplexConjugate InnerProductSpace Real

noncomputable section

/-- `exp(i x)` for real `x`. -/
def expAngle (x : ℝ) : ℂ := exp ((x : ℂ) * I)

lemma expAngle_add (x y : ℝ) : expAngle (x + y) = expAngle x * expAngle y := by
  simp [expAngle, add_mul, exp_add]

lemma expAngle_zero : expAngle 0 = 1 := by
  simp [expAngle]

lemma expAngle_nat (n : ℕ) (x : ℝ) : expAngle (n * x) = expAngle x ^ n := by
  rw [expAngle, expAngle, ← exp_nat_mul]
  congr 1
  push_cast
  ring

lemma star_expAngle (x : ℝ) : star (expAngle x) = expAngle (-x) := by
  rw [expAngle, expAngle, exp_ofReal_mul_I, exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
    star_add, star_mul]
  simp only [star_def, conj_ofReal, conj_I, ofReal_neg]
  ring_nf

lemma norm_expAngle (x : ℝ) : ‖expAngle x‖ = 1 := by
  rw [expAngle]
  exact norm_exp_ofReal_mul_I x

lemma expAngle_eq_one_iff (x : ℝ) : expAngle x = 1 ↔ ∃ n : ℤ, x = n * (2 * π) := by
  rw [expAngle, exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    have : (x : ℂ) = n * (2 * π) := by
      apply mul_right_cancel₀ hI
      simpa [mul_assoc, mul_left_comm, mul_comm] using hn
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

lemma expAngle_neg_two_pi_int (r : ℤ) : expAngle (-(2 * π * r)) = 1 := by
  rw [expAngle_eq_one_iff]
  refine ⟨-r, ?_⟩
  push_cast
  ring

lemma expAngle_neg_two_pi_div_eq_one_iff {N : ℕ} (hN : N ≠ 0) (r : ℤ) :
    expAngle (-(2 * π * r) / N) = 1 ↔ (N : ℤ) ∣ r := by
  rw [expAngle_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have h2π : (2 * π : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    rw [div_eq_iff hN0] at hn
    have hr : (r : ℝ) + n * N = 0 := by
      apply mul_left_cancel₀ h2π
      linear_combination -hn
    have hrZ : r + n * (N : ℤ) = 0 := by exact_mod_cast hr
    refine ⟨-n, ?_⟩
    rw [eq_neg_iff_add_eq_zero.mpr hrZ]
    ring
  · rintro ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    rw [ht]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp
    push_cast
    ring

/-- Geometric sum of the characters `exp(-2π i r n / N)`. -/
lemma sum_range_expAngle {N : ℕ} (hN : N ≠ 0) (r : ℤ) :
    ∑ n ∈ range N, expAngle (n * (-(2 * π * r) / N)) =
      if (N : ℤ) ∣ r then (N : ℂ) else 0 := by
  by_cases hr : (N : ℤ) ∣ r
  · simp only [hr, ↓reduceIte]
    have h1 : expAngle (-(2 * π * r) / N) = 1 :=
      (expAngle_neg_two_pi_div_eq_one_iff hN r).2 hr
    calc
      ∑ n ∈ range N, expAngle (n * (-(2 * π * r) / N))
          = ∑ n ∈ range N, (1 : ℂ) := by
            refine sum_congr rfl fun n _ => ?_
            rw [expAngle_nat, h1, one_pow]
      _ = ↑N := by simp [sum_const, card_range, nsmul_eq_mul]
  · simp only [hr, ↓reduceIte]
    have hω : expAngle (-(2 * π * r) / N) ≠ 1 :=
      (expAngle_neg_two_pi_div_eq_one_iff hN r).not.mpr hr
    simp_rw [expAngle_nat, geom_sum_eq hω]
    have hωN : expAngle (-(2 * π * r) / N) ^ N = 1 := by
      rw [← expAngle_nat]
      have harg : (N : ℝ) * (-(2 * π * r) / N) = -(2 * π * r) := by
        have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
        field_simp
      rw [harg, expAngle_neg_two_pi_int]
    rw [hωN, sub_self, zero_div]

lemma sum_zmod_expAngle {N : ℕ} [NeZero N] (r : ℤ) :
    ∑ j : ZMod N, expAngle (j.val * (-(2 * π * r) / N)) =
      if (N : ℤ) ∣ r then (N : ℂ) else 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  rw [← sum_range_expAngle hN r]
  symm
  refine sum_nbij' (fun n : ℕ => (n : ZMod N)) (fun j => j.val)
    (fun n hn => mem_univ _) (fun j _ => mem_range.mpr j.val_lt)
    (fun n hn => ZMod.val_natCast_of_lt (mem_range.mp hn))
    (fun j _ => ZMod.natCast_zmod_val j) ?_
  intro n hn
  rw [ZMod.val_natCast_of_lt (mem_range.mp hn)]

lemma dvd_val_sub_iff {N : ℕ} [NeZero N] (k m : ZMod N) :
    (N : ℤ) ∣ (k.val : ℤ) - m.val ↔ k = m := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h
    have hk : (k.val : ℤ) < N := by exact_mod_cast k.val_lt
    have hm : (m.val : ℤ) < N := by exact_mod_cast m.val_lt
    have hk0 : 0 ≤ (k.val : ℤ) := by exact_mod_cast Nat.zero_le k.val
    have hm0 : 0 ≤ (m.val : ℤ) := by exact_mod_cast Nat.zero_le m.val
    have habs : |(k.val : ℤ) - m.val| < N := by
      rw [abs_lt]
      constructor <;> omega
    have hmul : |(N : ℤ) * t| < N := by rwa [← ht]
    have hNpos : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
    have ht1 : |t| < 1 := by
      have hmul' : |(N : ℤ)| * |t| < |(N : ℤ)| * 1 := by
        simpa [abs_mul, abs_of_pos hNpos, mul_one] using hmul
      exact lt_of_mul_lt_mul_left hmul' (abs_nonneg (N : ℤ))
    have ht0 : t = 0 := by
      have hle : |t| ≤ 0 := (Int.lt_add_one_iff).mp (by simpa using ht1)
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg t))
    rw [ht0, mul_zero, sub_eq_zero] at ht
    exact ZMod.val_injective N (by exact_mod_cast ht)
  · intro h
    simp [h]

/-! ### Characters of one dual circle -/

variable {N : ℕ} [NeZero N]

/-- Character `χ_k(j) = exp(-2π i k j / N)` of the discrete dual circle. -/
def dualCircleChar (k j : ZMod N) : ℂ :=
  expAngle (-(2 * π * (k.val * j.val : ℕ)) / N)

lemma dualCircleChar_comm (k j : ZMod N) : dualCircleChar k j = dualCircleChar j k := by
  simp [dualCircleChar, mul_comm]

omit [NeZero N] in
lemma star_dualCircleChar (k j : ZMod N) :
    star (dualCircleChar k j) = expAngle ((2 * π * (k.val * j.val : ℕ)) / N) := by
  rw [dualCircleChar, star_expAngle]
  congr 1
  ring

omit [NeZero N] in
lemma dualCircleChar_mul_star (k m j : ZMod N) :
    dualCircleChar k j * star (dualCircleChar m j) =
      expAngle (-(2 * π * (((k.val : ℤ) - m.val) * j.val)) / N) := by
  rw [dualCircleChar, star_dualCircleChar, ← expAngle_add]
  congr 1
  push_cast
  ring

/-- The characters are orthogonal: the sum is `N` on the diagonal and `0` off it. -/
theorem dualCircle_orthogonality (k m : ZMod N) :
    ∑ j : ZMod N, dualCircleChar k j * star (dualCircleChar m j) =
      if k = m then (N : ℂ) else 0 := by
  suffices ∑ j : ZMod N, dualCircleChar k j * star (dualCircleChar m j) =
      if (N : ℤ) ∣ (k.val : ℤ) - m.val then (N : ℂ) else 0 by
    by_cases hr : (N : ℤ) ∣ (k.val : ℤ) - m.val
    · have hkm : k = m := (dvd_val_sub_iff k m).1 hr
      calc
        ∑ j, dualCircleChar k j * star (dualCircleChar m j)
            = if (N : ℤ) ∣ (k.val : ℤ) - m.val then (N : ℂ) else 0 := this
        _ = (N : ℂ) := by split_ifs; rfl
        _ = if k = m then (N : ℂ) else 0 := by simp [hkm]
    · have hkm : k ≠ m := fun hk => hr ((dvd_val_sub_iff k m).2 hk)
      calc
        ∑ j, dualCircleChar k j * star (dualCircleChar m j)
            = if (N : ℤ) ∣ (k.val : ℤ) - m.val then (N : ℂ) else 0 := this
        _ = 0 := by split_ifs; rfl
        _ = if k = m then (N : ℂ) else 0 := by simp [hkm]
  refine Eq.trans ?_ (sum_zmod_expAngle (N := N) ((k.val : ℤ) - m.val))
  refine sum_congr rfl fun j _ => ?_
  rw [dualCircleChar_mul_star]
  congr 1
  push_cast
  ring_nf

/-! ### Fourier inversion and Parseval from orthogonality -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sum_star_char_mul (χ : ι → ι → ℂ) (c : ℂ)
    (hχ : ∀ a b, ∑ t, χ a t * star (χ b t) = if a = b then c else 0)
    (hcomm : ∀ a t, χ a t = χ t a) (p q : ι) :
    ∑ t, star (χ t p) * χ t q = if p = q then c else 0 := by
  have h := hχ q p
  have h1 : ∀ t, star (χ t p) * χ t q = χ q t * star (χ p t) := by
    intro t
    rw [hcomm q t, hcomm p t, mul_comm]
  simp_rw [h1]
  simpa [eq_comm] using h

private theorem fourier_adj_fourier (χ : ι → ι → ℂ) (c : ℂ)
    (hχ : ∀ a b, ∑ t, χ a t * star (χ b t) = if a = b then c else 0)
    (hcomm : ∀ a t, χ a t = χ t a) (f : ι → ℂ) (j : ι) :
    ∑ k, (∑ m, f m * χ k m) * star (χ k j) = c * f j := by
  have hopen : ∑ k, (∑ m, f m * χ k m) * star (χ k j) =
      ∑ k, ∑ m, f m * (χ k m * star (χ k j)) := by
    refine sum_congr rfl fun k _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun m _ => by ring
  rw [hopen, sum_comm]
  have hswap : ∀ m, ∑ k, χ k m * star (χ k j) = if m = j then c else 0 := by
    intro m
    have h := sum_star_char_mul χ c hχ hcomm j m
    have hsum : ∑ k, χ k m * star (χ k j) = ∑ k, star (χ k j) * χ k m := by
      refine sum_congr rfl fun k _ => by ring
    rw [hsum, h]
    by_cases hmj : m = j
    · simp [hmj]
    · simp [hmj, Ne.symm hmj]
  simp_rw [← mul_sum, hswap]
  rw [sum_eq_single j (fun m _ hm => by simp [hm]) (fun hj => (hj (mem_univ j)).elim)]
  simp [mul_comm]

private theorem fourier_inner (χ : ι → ι → ℂ) (c : ℂ)
    (hχ : ∀ a b, ∑ t, χ a t * star (χ b t) = if a = b then c else 0)
    (hcomm : ∀ a t, χ a t = χ t a) (f g : ι → ℂ) :
    ∑ k, star (∑ j, f j * χ k j) * (∑ m, g m * χ k m) =
      c * ∑ j, star (f j) * g j := by
  let term : ι → ι → ι → ℂ := fun k j m =>
    star (f j) * star (χ k j) * (g m * χ k m)
  have hreorder : ∑ k, ∑ j, ∑ m, term k j m = ∑ j, ∑ m, ∑ k, term k j m := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm]
  have hterm : ∀ k j m, term k j m = star (f j) * g m * (star (χ k j) * χ k m) := by
    intro k j m
    ring
  calc
    ∑ k, star (∑ j, f j * χ k j) * (∑ m, g m * χ k m)
      = ∑ k, (∑ j, star (f j) * star (χ k j)) * (∑ m, g m * χ k m) := by
          refine sum_congr rfl fun k _ => ?_
          congr 1
          have hsum := map_sum (starRingEnd ℂ) (fun j => f j * χ k j) (univ : Finset ι)
          simp only [starRingEnd_apply, map_mul] at hsum
          exact hsum
    _ = ∑ k, ∑ j, ∑ m, term k j m := by
          simp_rw [sum_mul, mul_sum]
          rfl
    _ = ∑ j, ∑ m, ∑ k, term k j m := hreorder
    _ = ∑ j, ∑ m, star (f j) * g m * ∑ k, star (χ k j) * χ k m := by
          simp_rw [hterm, ← mul_sum]
    _ = ∑ j, ∑ m, star (f j) * g m * (if j = m then c else 0) := by
          simp_rw [sum_star_char_mul χ c hχ hcomm]
    _ = ∑ j, star (f j) * g j * c := by
          refine sum_congr rfl fun j _ => ?_
          rw [sum_eq_single j
            (fun m _ hm => by simp [show j ≠ m from hm.symm])
            (fun hj => (hj (mem_univ j)).elim)]
          simp
    _ = c * ∑ j, star (f j) * g j := by
          simp_rw [mul_comm _ c]
          rw [← mul_sum]

private theorem fourier_right_inverse (χ : ι → ι → ℂ) (c : ℂ)
    (hχ : ∀ a b, ∑ t, χ a t * star (χ b t) = if a = b then c else 0)
    (hcomm : ∀ a t, χ a t = χ t a) (f : ι → ℂ) (k : ι) :
    ∑ j, (∑ m, f m * star (χ m j)) * χ k j = c * f k := by
  have hopen : ∑ j, (∑ m, f m * star (χ m j)) * χ k j =
      ∑ j, ∑ m, (f m * star (χ m j)) * χ k j := by
    refine sum_congr rfl fun j _ => sum_mul _ _ _
  rw [hopen, sum_comm]
  have hfac : ∑ m, ∑ j, (f m * star (χ m j)) * χ k j =
      ∑ m, f m * ∑ j, star (χ m j) * χ k j := by
    refine sum_congr rfl fun m _ => ?_
    have hterm : ∑ j, (f m * star (χ m j)) * χ k j =
        ∑ j, f m * (star (χ m j) * χ k j) := by
      refine sum_congr rfl fun j _ => mul_assoc _ _ _
    rw [hterm, ← mul_sum]
  rw [hfac]
  have hswap : ∀ m, ∑ j, star (χ m j) * χ k j = if m = k then c else 0 := by
    intro m
    refine Eq.trans ?_ (sum_star_char_mul χ c hχ hcomm m k)
    refine sum_congr rfl fun j _ => ?_
    rw [hcomm m j, hcomm k j]
  simp_rw [hswap]
  rw [sum_eq_single k (fun m _ hm => by simp [hm]) (fun hk => (hk (mem_univ k)).elim)]
  simp [mul_comm]

lemma inv_sqrt_sq (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹ = (x : ℂ)⁻¹ := by
  have hmul : (Real.sqrt x : ℂ) * Real.sqrt x = x := by
    rw [← ofReal_mul, Real.mul_self_sqrt hx]
  rw [← mul_inv, hmul]

lemma star_inv_sqrt (x : ℝ) : star ((Real.sqrt x : ℂ)⁻¹) = (Real.sqrt x : ℂ)⁻¹ := by
  rw [← ofReal_inv, star_def, conj_ofReal]

/-! ### The circle transform -/

/-- Fourier transform `f̂(k) = ∑_j f(j) χ_k(j)`. -/
def dualCircleFourier (f : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ j, f j * dualCircleChar k j

/-- Conjugate sum, inverting the transform before division by `N`. -/
def dualCircleFourierAdj (f : ZMod N → ℂ) (j : ZMod N) : ℂ :=
  ∑ k, f k * star (dualCircleChar k j)

theorem dualCircleFourier_adj_fourier (f : ZMod N → ℂ) (j : ZMod N) :
    dualCircleFourierAdj (dualCircleFourier f) j = (N : ℂ) * f j := by
  simpa [dualCircleFourier, dualCircleFourierAdj] using
    fourier_adj_fourier dualCircleChar (N : ℂ) dualCircle_orthogonality
      dualCircleChar_comm f j

theorem dualCircleFourier_fourier_adj (f : ZMod N → ℂ) (k : ZMod N) :
    dualCircleFourier (dualCircleFourierAdj f) k = (N : ℂ) * f k := by
  simpa [dualCircleFourier, dualCircleFourierAdj] using
    fourier_right_inverse dualCircleChar (N : ℂ) dualCircle_orthogonality
      dualCircleChar_comm f k

/-- Inversion: the value is the conjugate average of the transform. -/
theorem dualCircleFourier_inversion (f : ZMod N → ℂ) (j : ZMod N) :
    f j = (N : ℂ)⁻¹ * ∑ k, dualCircleFourier f k * star (dualCircleChar k j) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  calc
    f j = (N : ℂ)⁻¹ * ((N : ℂ) * f j) := (inv_mul_cancel_left₀ hN (f j)).symm
    _ = (N : ℂ)⁻¹ * dualCircleFourierAdj (dualCircleFourier f) j := by
          rw [dualCircleFourier_adj_fourier]
    _ = (N : ℂ)⁻¹ * ∑ k, dualCircleFourier f k * star (dualCircleChar k j) := rfl

theorem dualCircleFourier_inner (f g : ZMod N → ℂ) :
    ∑ k, star (dualCircleFourier f k) * dualCircleFourier g k =
      (N : ℂ) * ∑ j, star (f j) * g j := by
  simpa [dualCircleFourier] using
    fourier_inner dualCircleChar (N : ℂ) dualCircle_orthogonality
      dualCircleChar_comm f g

/-- Parseval: `∑_k |f̂(k)|² = N ∑_j |f(j)|²`. -/
theorem dualCircleFourier_parseval (f : ZMod N → ℂ) :
    ∑ k, ‖dualCircleFourier f k‖ ^ 2 = (N : ℝ) * ∑ j, ‖f j‖ ^ 2 := by
  have h := dualCircleFourier_inner f f
  apply ofReal_injective
  rw [ofReal_mul, ofReal_natCast, ofReal_sum, ofReal_sum]
  simp_rw [← normSq_eq_norm_sq, normSq_eq_conj_mul_self]
  simpa [star_def] using h

lemma dualCircleFourierAdj_const (a : ℂ) (f : ZMod N → ℂ) (j : ZMod N) :
    dualCircleFourierAdj (fun k => a * f k) j = a * dualCircleFourierAdj f j := by
  simp [dualCircleFourierAdj, mul_sum, mul_assoc]

/-- Normalised Fourier transform on `ℓ²(ℤ/Nℤ)`. -/
def dualCircleFourierNormed (f : EuclideanSpace ℂ (ZMod N)) : EuclideanSpace ℂ (ZMod N) :=
  WithLp.toLp 2 fun k =>
    (Real.sqrt (N : ℝ) : ℂ)⁻¹ * dualCircleFourier (fun j => f j) k

/-- Conjugate normalised transform, the inverse operator. -/
def dualCircleFourierNormedAdj (f : EuclideanSpace ℂ (ZMod N)) : EuclideanSpace ℂ (ZMod N) :=
  WithLp.toLp 2 fun j =>
    (Real.sqrt (N : ℝ) : ℂ)⁻¹ * dualCircleFourierAdj (fun k => f k) j

@[simp] lemma dualCircleFourierNormed_apply (f : EuclideanSpace ℂ (ZMod N)) (k : ZMod N) :
    dualCircleFourierNormed f k =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * dualCircleFourier (fun j => f j) k := rfl

@[simp] lemma dualCircleFourierNormedAdj_apply (f : EuclideanSpace ℂ (ZMod N)) (j : ZMod N) :
    dualCircleFourierNormedAdj f j =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * dualCircleFourierAdj (fun k => f k) j := rfl

theorem dualCircleFourierNormed_left_inv (f : EuclideanSpace ℂ (ZMod N)) :
    dualCircleFourierNormedAdj (dualCircleFourierNormed f) = f := by
  ext j
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  calc
    dualCircleFourierNormedAdj (dualCircleFourierNormed f) j
        = (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
            dualCircleFourierAdj (fun k => dualCircleFourierNormed f k) j := by
          rw [dualCircleFourierNormedAdj_apply]
    _ = (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
          dualCircleFourierAdj (fun k =>
            (Real.sqrt (N : ℝ) : ℂ)⁻¹ * dualCircleFourier (fun i => f i) k) j := rfl
    _ = (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (N : ℝ) : ℂ)⁻¹ *
            dualCircleFourierAdj (dualCircleFourier (fun i => f i)) j) := by
          rw [dualCircleFourierAdj_const]
    _ = (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (N : ℝ) : ℂ)⁻¹ * ((N : ℂ) * f j)) := by
          rw [dualCircleFourier_adj_fourier]
    _ = f j := by
          rw [← mul_assoc, inv_sqrt_sq _ (Nat.cast_nonneg _), ofReal_natCast,
            inv_mul_cancel_left₀ hN (f j)]

theorem dualCircleFourierNormed_right_inv (f : EuclideanSpace ℂ (ZMod N)) :
    dualCircleFourierNormed (dualCircleFourierNormedAdj f) = f := by
  ext k
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  calc
    dualCircleFourierNormed (dualCircleFourierNormedAdj f) k
        = (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
            dualCircleFourier (fun j => dualCircleFourierNormedAdj f j) k := by
          rw [dualCircleFourierNormed_apply]
    _ = (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
          dualCircleFourier (fun j =>
            (Real.sqrt (N : ℝ) : ℂ)⁻¹ * dualCircleFourierAdj (fun i => f i) j) k := rfl
    _ = (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (N : ℝ) : ℂ)⁻¹ *
            dualCircleFourier (dualCircleFourierAdj (fun i => f i)) k) := by
          simp [dualCircleFourier, mul_sum, mul_assoc]
    _ = (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (N : ℝ) : ℂ)⁻¹ * ((N : ℂ) * f k)) := by
          rw [dualCircleFourier_fourier_adj]
    _ = f k := by
          rw [← mul_assoc, inv_sqrt_sq _ (Nat.cast_nonneg _), ofReal_natCast,
            inv_mul_cancel_left₀ hN (f k)]

/-- The normalised Fourier transform is a linear automorphism of `ℓ²(ℤ/Nℤ)`. -/
def dualCircleFourierEquiv :
    EuclideanSpace ℂ (ZMod N) ≃ₗ[ℂ] EuclideanSpace ℂ (ZMod N) where
  toFun := dualCircleFourierNormed
  invFun := dualCircleFourierNormedAdj
  left_inv := dualCircleFourierNormed_left_inv
  right_inv := dualCircleFourierNormed_right_inv
  map_add' f g := by
    ext k
    rw [PiLp.add_apply, dualCircleFourierNormed_apply, dualCircleFourierNormed_apply,
      dualCircleFourierNormed_apply, ← mul_add]
    congr 1
    simp only [dualCircleFourier, PiLp.add_apply, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  map_smul' a f := by
    ext k
    rw [PiLp.smul_apply, dualCircleFourierNormed_apply, dualCircleFourierNormed_apply]
    simp [dualCircleFourier, smul_eq_mul, mul_sum, mul_assoc, mul_left_comm]

@[simp] lemma dualCircleFourierEquiv_apply (f : EuclideanSpace ℂ (ZMod N)) :
    dualCircleFourierEquiv f = dualCircleFourierNormed f := rfl

/-- The normalised transform is unitary. -/
theorem inner_dualCircleFourierEquiv (f g : EuclideanSpace ℂ (ZMod N)) :
    inner ℂ (dualCircleFourierEquiv f) (dualCircleFourierEquiv g) = inner ℂ f g := by
  have h := dualCircleFourier_inner (fun j => f j) (fun j => g j)
  have hc := star_inv_sqrt (N : ℝ)
  have hscale := inv_sqrt_sq (N : ℝ) (Nat.cast_nonneg N)
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [RCLike.inner_apply']
  simp only [dualCircleFourierEquiv_apply, dualCircleFourierNormed_apply]
  have hstar (z : ℂ) :
      (starRingEnd ℂ) ((Real.sqrt (N : ℝ) : ℂ)⁻¹ * z) =
        (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) z := by
    have hc' : (starRingEnd ℂ) ((Real.sqrt (N : ℝ) : ℂ)⁻¹) =
        (Real.sqrt (N : ℝ) : ℂ)⁻¹ := by
      rw [starRingEnd_apply]
      exact hc
    rw [map_mul, hc']
  simp_rw [hstar]
  have hterm : ∀ k,
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (dualCircleFourier (fun j => f j) k) *
          ((Real.sqrt (N : ℝ) : ℂ)⁻¹ * dualCircleFourier (fun j => g j) k) =
        ((Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt (N : ℝ) : ℂ)⁻¹) *
          ((starRingEnd ℂ) (dualCircleFourier (fun j => f j) k) *
            dualCircleFourier (fun j => g j) k) := by
    intro k
    ring
  simp_rw [hterm, ← mul_sum]
  simp only [starRingEnd_apply]
  rw [h, hscale, ofReal_natCast]
  exact inv_mul_cancel_left₀ hN _

/-! ### Three dual angles -/

/-- Character of `(ℤ/Nℤ)³`, the product of the three dual-angle characters. -/
def dualAngleChar (k j : Fin 3 → ZMod N) : ℂ :=
  ∏ a, dualCircleChar (k a) (j a)

lemma dualAngleChar_comm (k j : Fin 3 → ZMod N) : dualAngleChar k j = dualAngleChar j k := by
  simp [dualAngleChar, dualCircleChar_comm]

omit [NeZero N] in
lemma star_dualAngleChar (k j : Fin 3 → ZMod N) :
    star (dualAngleChar k j) = ∏ a, star (dualCircleChar (k a) (j a)) := by
  simp [dualAngleChar]

theorem dualAngle_orthogonality (k m : Fin 3 → ZMod N) :
    ∑ j : Fin 3 → ZMod N, dualAngleChar k j * star (dualAngleChar m j) =
      if k = m then (N : ℂ) ^ 3 else 0 := by
  classical
  have hterm : ∀ j : Fin 3 → ZMod N,
      dualAngleChar k j * star (dualAngleChar m j) =
        ∏ a, dualCircleChar (k a) (j a) * star (dualCircleChar (m a) (j a)) := by
    intro j
    simp [dualAngleChar, prod_mul_distrib]
  simp_rw [hterm]
  have hfactor :
      (∑ j : Fin 3 → ZMod N, ∏ a,
          dualCircleChar (k a) (j a) * star (dualCircleChar (m a) (j a))) =
        ∏ a, ∑ t : ZMod N, dualCircleChar (k a) t * star (dualCircleChar (m a) t) := by
    rw [← Fintype.piFinset_univ]
    simpa using
      (sum_prod_piFinset (univ : Finset (ZMod N))
        (fun a t => dualCircleChar (k a) t * star (dualCircleChar (m a) t)))
  rw [hfactor]
  simp_rw [dualCircle_orthogonality]
  by_cases hkm : k = m
  · simp [hkm, prod_const, card_univ, Fintype.card_fin]
  · obtain ⟨a, ha⟩ : ∃ a, k a ≠ m a := by
      contrapose! hkm
      funext a
      exact hkm a
    rw [prod_eq_zero (mem_univ a) (by simp [ha])]
    simp [hkm]

def dualAngleFourier (f : (Fin 3 → ZMod N) → ℂ) (k : Fin 3 → ZMod N) : ℂ :=
  ∑ j, f j * dualAngleChar k j

def dualAngleFourierAdj (f : (Fin 3 → ZMod N) → ℂ) (j : Fin 3 → ZMod N) : ℂ :=
  ∑ k, f k * star (dualAngleChar k j)

theorem dualAngleFourier_adj_fourier (f : (Fin 3 → ZMod N) → ℂ) (j : Fin 3 → ZMod N) :
    dualAngleFourierAdj (dualAngleFourier f) j = (N : ℂ) ^ 3 * f j := by
  simpa [dualAngleFourier, dualAngleFourierAdj] using
    fourier_adj_fourier dualAngleChar ((N : ℂ) ^ 3) dualAngle_orthogonality
      dualAngleChar_comm f j

theorem dualAngleFourier_inversion (f : (Fin 3 → ZMod N) → ℂ) (j : Fin 3 → ZMod N) :
    f j = ((N : ℂ) ^ 3)⁻¹ * ∑ k, dualAngleFourier f k * star (dualAngleChar k j) := by
  have hN : (N : ℂ) ^ 3 ≠ 0 := by
    exact pow_ne_zero 3 (by exact_mod_cast NeZero.ne N)
  calc
    f j = ((N : ℂ) ^ 3)⁻¹ * ((N : ℂ) ^ 3 * f j) := (inv_mul_cancel_left₀ hN (f j)).symm
    _ = ((N : ℂ) ^ 3)⁻¹ * dualAngleFourierAdj (dualAngleFourier f) j := by
          rw [dualAngleFourier_adj_fourier]
    _ = ((N : ℂ) ^ 3)⁻¹ * ∑ k, dualAngleFourier f k * star (dualAngleChar k j) := rfl

theorem dualAngleFourier_inner (f g : (Fin 3 → ZMod N) → ℂ) :
    ∑ k, star (dualAngleFourier f k) * dualAngleFourier g k =
      (N : ℂ) ^ 3 * ∑ j, star (f j) * g j := by
  simpa [dualAngleFourier] using
    fourier_inner dualAngleChar ((N : ℂ) ^ 3) dualAngle_orthogonality
      dualAngleChar_comm f g

/-- Parseval on the three dual angles: `∑ |f̂|² = N³ ∑ |f|²`. -/
theorem dualAngleFourier_parseval (f : (Fin 3 → ZMod N) → ℂ) :
    ∑ k, ‖dualAngleFourier f k‖ ^ 2 = (N : ℝ) ^ 3 * ∑ j, ‖f j‖ ^ 2 := by
  have h := dualAngleFourier_inner f f
  apply ofReal_injective
  rw [ofReal_mul, ofReal_pow, ofReal_natCast, ofReal_sum, ofReal_sum]
  simp_rw [← normSq_eq_norm_sq, normSq_eq_conj_mul_self]
  simpa [star_def] using h

/-! ### Shift, clock, and convolution on one dual circle -/

/-- Translation `j ↦ j + s` of the discrete dual circle. -/
def dualCircleTranslate (s : ZMod N) : ZMod N ≃ ZMod N where
  toFun j := j + s
  invFun j := j - s
  left_inv j := add_sub_cancel_right j s
  right_inv j := sub_add_cancel j s

lemma expAngle_add_int_two_pi (x : ℝ) (n : ℤ) :
    expAngle (x + n * (2 * π)) = expAngle x := by
  rw [expAngle_add]
  have hone : expAngle (n * (2 * π)) = 1 := by
    rw [expAngle_eq_one_iff]
    exact ⟨n, rfl⟩
  rw [hone, mul_one]

omit [NeZero N] in
lemma dualCircleChar_zero_right (k : ZMod N) : dualCircleChar k 0 = 1 := by
  simp [dualCircleChar, ZMod.val_zero, expAngle_zero]

omit [NeZero N] in
lemma dualCircleChar_zero_left (j : ZMod N) : dualCircleChar 0 j = 1 := by
  simp [dualCircleChar, ZMod.val_zero, expAngle_zero]

lemma norm_dualCircleChar (k j : ZMod N) : ‖dualCircleChar k j‖ = 1 := by
  simpa [dualCircleChar] using norm_expAngle _

lemma dualCircleChar_ne_zero (k j : ZMod N) : dualCircleChar k j ≠ 0 := by
  intro h
  have := norm_dualCircleChar k j
  rw [h, norm_zero] at this
  exact absurd this zero_ne_one

/-- A carry of `N` in the exponents does not change the character product. -/
lemma expAngle_mul_of_sum {a b n q : ℕ} (h : a + b = n + N * q) :
    expAngle (-(2 * π * a) / N) * expAngle (-(2 * π * b) / N) =
      expAngle (-(2 * π * n) / N) := by
  rw [← expAngle_add]
  have hR : (a : ℝ) + b = (n : ℝ) + (N : ℝ) * q := by exact_mod_cast h
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have harg :
      -(2 * π * (a : ℝ)) / N + -(2 * π * (b : ℝ)) / N =
        -(2 * π * (n : ℝ)) / N + (-(q : ℤ)) * (2 * π) := by
    have hleft :
        -(2 * π * (a : ℝ)) / N + -(2 * π * (b : ℝ)) / N =
          -(2 * π * ((a : ℝ) + b)) / N := by
      field_simp [hN]
      ring
    have hright :
        -(2 * π * ((n : ℝ) + (N : ℝ) * q)) / N =
          -(2 * π * (n : ℝ)) / N + (-(q : ℤ)) * (2 * π) := by
      field_simp [hN]
      push_cast
      ring
    rw [hleft, hR, hright]
  rw [harg]
  convert expAngle_add_int_two_pi (-(2 * π * (n : ℝ)) / N) (-(q : ℤ)) using 2
  push_cast
  ring

lemma dualCircleChar_add_right (k j s : ZMod N) :
    dualCircleChar k (j + s) = dualCircleChar k j * dualCircleChar k s := by
  set q : ℕ := (j.val + s.val) / N
  have hsplit : j.val + s.val = (j + s).val + N * q := by
    simpa [q, ZMod.val_add, add_comm] using (Nat.mod_add_div (j.val + s.val) N).symm
  have hprod : k.val * j.val + k.val * s.val =
      k.val * (j + s).val + N * (k.val * q) := by
    calc
      k.val * j.val + k.val * s.val = k.val * (j.val + s.val) := by ring
      _ = k.val * ((j + s).val + N * q) := by rw [hsplit]
      _ = k.val * (j + s).val + N * (k.val * q) := by ring
  rw [dualCircleChar, dualCircleChar, dualCircleChar]
  exact (expAngle_mul_of_sum hprod).symm

lemma dualCircleChar_add_left (k r j : ZMod N) :
    dualCircleChar (k + r) j = dualCircleChar k j * dualCircleChar r j := by
  set q : ℕ := (k.val + r.val) / N
  have hsplit : k.val + r.val = (k + r).val + N * q := by
    simpa [q, ZMod.val_add, add_comm] using (Nat.mod_add_div (k.val + r.val) N).symm
  have hprod : k.val * j.val + r.val * j.val =
      (k + r).val * j.val + N * (q * j.val) := by
    calc
      k.val * j.val + r.val * j.val = (k.val + r.val) * j.val := by ring
      _ = ((k + r).val + N * q) * j.val := by rw [hsplit]
      _ = (k + r).val * j.val + N * (q * j.val) := by ring
  rw [dualCircleChar, dualCircleChar, dualCircleChar]
  exact (expAngle_mul_of_sum hprod).symm

lemma dualCircleChar_pow (n : ℕ) (j : ZMod N) :
    dualCircleChar (1 : ZMod N) j ^ n = dualCircleChar (n : ZMod N) j := by
  induction n with
  | zero => simp [dualCircleChar_zero_left]
  | succ n ih =>
      rw [pow_succ, ih, ← dualCircleChar_add_left]
      congr 1
      push_cast
      ring

omit [NeZero N] in
lemma zmod_natCast_ne_zero {k : ℕ} (hk0 : 0 < k) (hkN : k < N) :
    (k : ZMod N) ≠ 0 := by
  intro h
  have hval : (k : ZMod N).val = 0 := by simp [h]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hkN] at hval
  omega

lemma dualCircleChar_ne_one {k : ZMod N} (hk : k ≠ 0) : dualCircleChar k 1 ≠ 1 := by
  have hkval : k.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hk
  have hN : 1 < N := by
    have hlt : k.val < N := k.val_lt
    have hpos : 0 < k.val := Nat.pos_of_ne_zero hkval
    omega
  have hfact : Fact (1 < N) := ⟨hN⟩
  rw [dualCircleChar, ZMod.val_one N, mul_one]
  intro h
  have hdiv : (N : ℤ) ∣ (k.val : ℤ) :=
    (expAngle_neg_two_pi_div_eq_one_iff (NeZero.ne N) (k.val : ℤ)).1 h
  rcases hdiv with ⟨t, ht⟩
  have hlt : (k.val : ℤ) < N := by exact_mod_cast k.val_lt
  have hnn : 0 ≤ (k.val : ℤ) := by exact_mod_cast Nat.zero_le k.val
  have hmul : |(N : ℤ)| * |t| < |(N : ℤ)| := by
    rw [← abs_mul, ← ht, abs_of_nonneg hnn]
    exact_mod_cast k.val_lt
  have htone : |t| < 1 := by
    have : |(N : ℤ)| * |t| < |(N : ℤ)| * 1 := by simpa [mul_one] using hmul
    exact lt_of_mul_lt_mul_left this (abs_nonneg _)
  have ht0 : t = 0 := by
    have hle : |t| ≤ 0 := (Int.lt_add_one_iff).mp (by simpa using htone)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg t))
  rw [ht0, mul_zero] at ht
  exact hkval (by exact_mod_cast ht)

/-- Amplitude concentrated at the identity of the discrete dual circle. -/
def dualCircleDelta (j : ZMod N) : ℂ :=
  if j = 0 then 1 else 0

theorem dualCircleFourier_delta (k : ZMod N) : dualCircleFourier dualCircleDelta k = 1 := by
  unfold dualCircleFourier dualCircleDelta
  rw [sum_eq_single (0 : ZMod N)]
  · simp [dualCircleChar_zero_right]
  · intro j _ hj
    simp [hj]
  · intro h
    exact (h (mem_univ _)).elim

/-- Shift the discrete dual angle by `s`. -/
def dualCircleShift (s : ZMod N) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  fun j => f (j - s)

/-- Multiply by the winding character `χ_r`. -/
def dualCircleClock (r : ZMod N) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  fun j => dualCircleChar r j * f j

omit [NeZero N] in
theorem dualCircleShift_iterate (n : ℕ) (f : ZMod N → ℂ) :
    (dualCircleShift (1 : ZMod N))^[n] f = dualCircleShift (n : ZMod N) f := by
  induction n with
  | zero =>
      ext j
      simp [dualCircleShift]
  | succ n ih =>
      ext j
      rw [Function.iterate_succ_apply', ih]
      simp only [dualCircleShift]
      congr 1
      push_cast
      ring

omit [NeZero N] in
theorem dualCircleShift_order (f : ZMod N → ℂ) :
    (dualCircleShift (1 : ZMod N))^[N] f = f := by
  rw [dualCircleShift_iterate]
  ext j
  simp [dualCircleShift]

omit [NeZero N] in
theorem dualCircleShift_iterate_ne {k : ℕ} (hk0 : 0 < k) (hkN : k < N) :
    (dualCircleShift (1 : ZMod N))^[k] dualCircleDelta ≠ dualCircleDelta := by
  intro h
  have h0 := congr_fun h (k : ZMod N)
  rw [dualCircleShift_iterate] at h0
  have hkz : (k : ZMod N) ≠ 0 := zmod_natCast_ne_zero hk0 hkN
  simp only [dualCircleShift, dualCircleDelta, sub_self, hkz] at h0
  exact one_ne_zero h0

theorem dualCircleClock_iterate (n : ℕ) (f : ZMod N → ℂ) :
    (dualCircleClock (1 : ZMod N))^[n] f =
      fun j => dualCircleChar (n : ZMod N) j * f j := by
  induction n with
  | zero =>
      ext j
      simp [dualCircleChar_zero_left]
  | succ n ih =>
      ext j
      rw [Function.iterate_succ_apply', ih, dualCircleClock, ← mul_assoc,
        ← dualCircleChar_add_left]
      have hidx : (1 + (n : ZMod N)) = ((n + 1 : ℕ) : ZMod N) := by
        rw [Nat.cast_add, Nat.cast_one, add_comm]
      rw [hidx]

theorem dualCircleClock_order (f : ZMod N → ℂ) :
    (dualCircleClock (1 : ZMod N))^[N] f = f := by
  ext j
  rw [dualCircleClock_iterate]
  simp [dualCircleChar_zero_left]

theorem dualCircleClock_iterate_ne {k : ℕ} (hk0 : 0 < k) (hkN : k < N) :
    (dualCircleClock (1 : ZMod N))^[k] (fun _ : ZMod N => (1 : ℂ)) ≠ fun _ => 1 := by
  intro h
  have h1 := congr_fun h 1
  rw [dualCircleClock_iterate] at h1
  simp only [mul_one] at h1
  exact dualCircleChar_ne_one (zmod_natCast_ne_zero hk0 hkN) h1

theorem inner_dualCircleShift (s : ZMod N) (f g : ZMod N → ℂ) :
    ∑ j, star (dualCircleShift s f j) * dualCircleShift s g j =
      ∑ j, star (f j) * g j := by
  unfold dualCircleShift
  refine Fintype.sum_equiv (dualCircleTranslate s).symm _ _ ?_
  intro j
  simp [dualCircleTranslate]

theorem inner_dualCircleClock (r : ZMod N) (f g : ZMod N → ℂ) :
    ∑ j, star (dualCircleClock r f j) * dualCircleClock r g j =
      ∑ j, star (f j) * g j := by
  refine sum_congr rfl fun j _ => ?_
  have hχ : star (dualCircleChar r j) * dualCircleChar r j = 1 := by
    have hnorm : ‖dualCircleChar r j‖ ^ 2 = 1 := by
      rw [norm_dualCircleChar, one_pow]
    rw [star_def, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq]
    exact_mod_cast hnorm
  simp only [dualCircleClock]
  rw [star_mul]
  calc
    star (f j) * star (dualCircleChar r j) * (dualCircleChar r j * g j)
        = star (f j) * g j * (star (dualCircleChar r j) * dualCircleChar r j) := by ring
    _ = star (f j) * g j := by rw [hχ, mul_one]

/-- Clock after shift differs from shift after clock by the character `χ_r(s)`. -/
theorem dualCircle_weyl (r s : ZMod N) (f : ZMod N → ℂ) (j : ZMod N) :
    dualCircleClock r (dualCircleShift s f) j =
      dualCircleChar r s * dualCircleShift s (dualCircleClock r f) j := by
  simp only [dualCircleClock, dualCircleShift]
  have hj : j = (j - s) + s := by ring
  rw [hj, dualCircleChar_add_right]
  ring_nf

theorem dualCircleFourier_shift (s : ZMod N) (f : ZMod N → ℂ) (k : ZMod N) :
    dualCircleFourier (dualCircleShift s f) k =
      dualCircleChar k s * dualCircleFourier f k := by
  unfold dualCircleFourier dualCircleShift
  have hre : ∑ j, f (j - s) * dualCircleChar k j =
      ∑ j, f j * dualCircleChar k (j + s) := by
    refine (Fintype.sum_equiv (dualCircleTranslate s)
      (fun j => f j * dualCircleChar k (j + s))
      (fun j => f (j - s) * dualCircleChar k j) ?_).symm
    intro j
    simp [dualCircleTranslate, add_sub_cancel_right]
  rw [hre]
  have hterm : ∀ j, f j * dualCircleChar k (j + s) =
      (f j * dualCircleChar k j) * dualCircleChar k s := by
    intro j
    rw [dualCircleChar_add_right]
    ring
  simp_rw [hterm]
  rw [← sum_mul, mul_comm]

theorem dualCircleFourier_clock (r : ZMod N) (f : ZMod N → ℂ) (k : ZMod N) :
    dualCircleFourier (dualCircleClock r f) k = dualCircleFourier f (k + r) := by
  unfold dualCircleFourier dualCircleClock
  refine sum_congr rfl fun j _ => ?_
  calc
    dualCircleChar r j * f j * dualCircleChar k j
        = f j * (dualCircleChar k j * dualCircleChar r j) := by ring
    _ = f j * dualCircleChar (k + r) j := by rw [← dualCircleChar_add_left]

/-- Circular convolution on the discrete dual circle. -/
def dualCircleConv (f g : ZMod N → ℂ) (j : ZMod N) : ℂ :=
  ∑ t, f t * g (j - t)

theorem dualCircleFourier_conv (f g : ZMod N → ℂ) (k : ZMod N) :
    dualCircleFourier (dualCircleConv f g) k =
      dualCircleFourier f k * dualCircleFourier g k := by
  unfold dualCircleFourier dualCircleConv
  have hswap : ∑ j, (∑ t, f t * g (j - t)) * dualCircleChar k j =
      ∑ t, ∑ j, f t * g (j - t) * dualCircleChar k j := by
    simp_rw [sum_mul]
    exact sum_comm
  rw [hswap]
  have hinner : ∀ t, ∑ j, g (j - t) * dualCircleChar k (j - t) =
      ∑ j, g j * dualCircleChar k j := by
    intro t
    refine Fintype.sum_equiv (dualCircleTranslate t).symm _ _ ?_
    intro j
    simp [dualCircleTranslate]
  have hfac : ∑ t, ∑ j, f t * g (j - t) * dualCircleChar k j =
      ∑ t, f t * dualCircleChar k t *
        ∑ j, g j * dualCircleChar k j := by
    refine sum_congr rfl fun t _ => ?_
    rw [← hinner t]
    have hterm : ∑ j, f t * g (j - t) * dualCircleChar k j =
        ∑ j, f t * dualCircleChar k t * (g (j - t) * dualCircleChar k (j - t)) := by
      refine sum_congr rfl fun j _ => ?_
      have hj : j = (j - t) + t := by ring
      rw [hj, dualCircleChar_add_right]
      ring_nf
    rw [hterm, ← mul_sum]
  rw [hfac, sum_mul]

lemma sq_sum_le_card_mul_sum_sq_real {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, a i ^ 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert x s hx ih =>
      rw [sum_insert hx, sum_insert hx, card_insert_of_notMem hx]
      have hexpand : ∑ i ∈ s, (a x - a i) ^ 2 =
          (s.card : ℝ) * a x ^ 2 - 2 * a x * ∑ i ∈ s, a i + ∑ i ∈ s, a i ^ 2 := by
        have hterm : ∀ i, (a x - a i) ^ 2 = a x ^ 2 - 2 * a x * a i + a i ^ 2 := by
          intro i
          ring
        simp_rw [hterm, sum_add_distrib, sum_sub_distrib]
        simp only [sum_const, nsmul_eq_mul, mul_sum]
      have hgap : 0 ≤ ∑ i ∈ s, (a x - a i) ^ 2 :=
        sum_nonneg fun _ _ => sq_nonneg _
      push_cast
      nlinarith [ih, hexpand, hgap]

private lemma normSq_charSum_le_support
    {α : Type*} [Fintype α]
    (χ : α → α → ℂ) (hχ : ∀ a b, ‖χ a b‖ = 1)
    (f : α → ℂ) (k : α) :
    ‖∑ j, f j * χ k j‖ ^ 2 ≤ (f.support.ncard : ℝ) * ∑ j, ‖f j‖ ^ 2 := by
  classical
  let S := univ.filter (fun j => f j ≠ 0)
  have hScard : f.support.ncard = S.card := by
    have hset : f.support = (S : Set α) := by
      ext j
      simp [S, Function.mem_support]
    rw [hset, Set.ncard_coe_finset]
  have hsum : ∑ j, f j * χ k j = ∑ j ∈ S, f j * χ k j := by
    symm
    refine sum_subset (subset_univ S) ?_
    intro j _ hj
    simp [S, mem_filter] at hj
    simp [hj]
  have hmass : ∑ j ∈ S, ‖f j‖ ^ 2 = ∑ j, ‖f j‖ ^ 2 := by
    refine sum_subset (subset_univ S) ?_
    intro j _ hj
    simp [S, mem_filter] at hj
    simp [hj]
  rw [hsum, hScard]
  have hnorm : ‖∑ j ∈ S, f j * χ k j‖ ≤ ∑ j ∈ S, ‖f j‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine sum_le_sum fun j _ => ?_
    rw [norm_mul, hχ k j, mul_one]
  have hsq : ‖∑ j ∈ S, f j * χ k j‖ ^ 2 ≤ (∑ j ∈ S, ‖f j‖) ^ 2 := by
    apply (sq_le_sq).2
    rw [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (sum_nonneg fun _ _ => norm_nonneg _)]
    exact hnorm
  have hcs := sq_sum_le_card_mul_sum_sq_real S (fun j => ‖f j‖)
  have hchain : ‖∑ j ∈ S, f j * χ k j‖ ^ 2 ≤ (S.card : ℝ) * ∑ j ∈ S, ‖f j‖ ^ 2 :=
    hsq.trans hcs
  simpa [hmass] using hchain

private lemma support_uncertainty_char
    {α : Type*} [Fintype α]
    (χ : α → α → ℂ) (hχ : ∀ a b, ‖χ a b‖ = 1)
    (c : ℕ)
    (hparse : ∀ f : α → ℂ,
      ∑ k, ‖∑ j, f j * χ k j‖ ^ 2 = (c : ℝ) * ∑ j, ‖f j‖ ^ 2)
    {f : α → ℂ} (hf : ∃ j, f j ≠ 0) :
    c ≤ f.support.ncard * (fun k => ∑ j, f j * χ k j).support.ncard := by
  classical
  let hat : α → ℂ := fun k => ∑ j, f j * χ k j
  let T := univ.filter (fun k => hat k ≠ 0)
  have hmass_pos : 0 < ∑ j, ‖f j‖ ^ 2 := by
    obtain ⟨j, hj⟩ := hf
    have hpos : 0 < ‖f j‖ ^ 2 := pow_pos (norm_pos_iff.mpr hj) 2
    exact lt_of_lt_of_le hpos
      (single_le_sum (f := fun i => ‖f i‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ j))
  have hpoint : ∀ k, ‖hat k‖ ^ 2 ≤ (f.support.ncard : ℝ) * ∑ j, ‖f j‖ ^ 2 :=
    fun k => normSq_charSum_le_support χ hχ f k
  have hTsum : ∑ k, ‖hat k‖ ^ 2 = ∑ k ∈ T, ‖hat k‖ ^ 2 := by
    symm
    refine sum_subset (subset_univ T) ?_
    intro k _ hk
    simp [T, mem_filter] at hk
    simp [hk]
  have hle : ∑ k ∈ T, ‖hat k‖ ^ 2 ≤
      ∑ k ∈ T, (f.support.ncard : ℝ) * ∑ j, ‖f j‖ ^ 2 :=
    sum_le_sum fun k _ => hpoint k
  rw [sum_const, nsmul_eq_mul] at hle
  have hTcard : hat.support.ncard = T.card := by
    have hset : hat.support = (T : Set α) := by
      ext k
      simp [T, Function.mem_support]
    rw [hset, Set.ncard_coe_finset]
  have hparsef := hparse f
  rw [hTsum] at hparsef
  rw [← hTcard] at hle
  have hbound : (c : ℝ) * ∑ j, ‖f j‖ ^ 2 ≤
      (f.support.ncard : ℝ) * (hat.support.ncard : ℝ) * ∑ j, ‖f j‖ ^ 2 := by
    calc
      (c : ℝ) * ∑ j, ‖f j‖ ^ 2 = ∑ k ∈ T, ‖hat k‖ ^ 2 := by
        simpa [hat] using hparsef.symm
      _ ≤ (hat.support.ncard : ℝ) * ((f.support.ncard : ℝ) * ∑ j, ‖f j‖ ^ 2) := hle
      _ = (f.support.ncard : ℝ) * (hat.support.ncard : ℝ) * ∑ j, ‖f j‖ ^ 2 := by ring
  have hdiv : (c : ℝ) ≤ (f.support.ncard : ℝ) * (hat.support.ncard : ℝ) :=
    le_of_mul_le_mul_right hbound hmass_pos
  have hnat : (c : ℝ) ≤ ((f.support.ncard * hat.support.ncard : ℕ) : ℝ) := by
    simpa [Nat.cast_mul] using hdiv
  exact Nat.cast_le.mp hnat

theorem dualCircle_support_uncertainty {f : ZMod N → ℂ} (hf : ∃ j, f j ≠ 0) :
    N ≤ f.support.ncard * (dualCircleFourier f).support.ncard := by
  have hparse : ∀ g : ZMod N → ℂ,
      ∑ k, ‖∑ j, g j * dualCircleChar k j‖ ^ 2 =
        (N : ℝ) * ∑ j, ‖g j‖ ^ 2 := by
    intro g
    simpa [dualCircleFourier] using dualCircleFourier_parseval g
  unfold dualCircleFourier
  exact support_uncertainty_char dualCircleChar norm_dualCircleChar N hparse hf

theorem dualCircle_support_eq_site :
    (dualCircleDelta (N := N)).support.ncard *
      (dualCircleFourier (N := N) (dualCircleDelta (N := N))).support.ncard = N := by
  have hdelta : dualCircleDelta.support = {(0 : ZMod N)} := by
    ext j
    simp [Function.mem_support, dualCircleDelta]
  have hhat : (dualCircleFourier (N := N) dualCircleDelta).support = Set.univ := by
    ext k
    simp [Function.mem_support, dualCircleFourier_delta]
  rw [hdelta, hhat, Set.ncard_singleton, Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card N,
    one_mul]

theorem dualCircleFourier_char (m k : ZMod N) :
    dualCircleFourier (fun j => dualCircleChar m j) k =
      if k + m = 0 then (N : ℂ) else 0 := by
  unfold dualCircleFourier
  have hmul : ∀ j, dualCircleChar m j * dualCircleChar k j =
      dualCircleChar (k + m) j := by
    intro j
    rw [dualCircleChar_add_left, mul_comm]
  simp_rw [hmul]
  have hsum := dualCircle_orthogonality (k + m) (0 : ZMod N)
  simpa [dualCircleChar_zero_left] using hsum

theorem dualCircle_support_eq_winding (m : ZMod N) :
    (fun j => dualCircleChar m j).support.ncard *
      (dualCircleFourier (fun j => dualCircleChar m j)).support.ncard = N := by
  have hfull : (fun j => dualCircleChar m j).support = Set.univ := by
    ext j
    simp [Function.mem_support, dualCircleChar_ne_zero]
  have hhat : (dualCircleFourier (fun j => dualCircleChar m j)).support = {(-m : ZMod N)} := by
    ext k
    simp only [Function.mem_support, Set.mem_singleton_iff, dualCircleFourier_char]
    by_cases hk : k + m = 0
    · simp [NeZero.ne N, show k = -m from (add_eq_zero_iff_eq_neg).1 hk]
    · simp [hk, eq_neg_iff_add_eq_zero]
  rw [hfull, hhat, Set.ncard_univ, Set.ncard_singleton, Nat.card_eq_fintype_card, ZMod.card N,
    mul_one]

/-! ### Three dual angles, continued -/

lemma norm_dualAngleChar (k j : Fin 3 → ZMod N) : ‖dualAngleChar k j‖ = 1 := by
  simp [dualAngleChar, norm_prod, norm_dualCircleChar]

omit [NeZero N] in
lemma dualAngleChar_zero (k : Fin 3 → ZMod N) : dualAngleChar k 0 = 1 := by
  simp [dualAngleChar, dualCircleChar_zero_right]

lemma dualAngleChar_ne_zero (k j : Fin 3 → ZMod N) : dualAngleChar k j ≠ 0 := by
  intro h
  have := norm_dualAngleChar k j
  rw [h, norm_zero] at this
  exact absurd this zero_ne_one

omit [NeZero N] in
lemma dualAngleChar_zero_left (j : Fin 3 → ZMod N) : dualAngleChar 0 j = 1 := by
  simp [dualAngleChar, dualCircleChar_zero_left]

lemma dualAngleChar_add_left (k r j : Fin 3 → ZMod N) :
    dualAngleChar (k + r) j = dualAngleChar k j * dualAngleChar r j := by
  simp [dualAngleChar, dualCircleChar_add_left, prod_mul_distrib]

def dualAngleDelta (j : Fin 3 → ZMod N) : ℂ :=
  if j = 0 then 1 else 0

theorem dualAngleFourier_delta (k : Fin 3 → ZMod N) : dualAngleFourier dualAngleDelta k = 1 := by
  unfold dualAngleFourier dualAngleDelta
  rw [sum_eq_single (0 : Fin 3 → ZMod N)]
  · simp [dualAngleChar_zero]
  · intro j _ hj
    simp [hj]
  · intro h
    exact (h (mem_univ _)).elim

theorem sum_dualAngleChar (r : Fin 3 → ZMod N) :
    ∑ j, dualAngleChar r j = if r = 0 then (N : ℂ) ^ 3 else 0 := by
  have hstar : ∀ j, star (dualAngleChar (0 : Fin 3 → ZMod N) j) = 1 := by
    intro j
    simp [dualAngleChar_zero_left]
  simpa [hstar] using dualAngle_orthogonality r 0

theorem dualAngleFourier_char (m k : Fin 3 → ZMod N) :
    dualAngleFourier (fun j => dualAngleChar m j) k =
      if k + m = 0 then (N : ℂ) ^ 3 else 0 := by
  unfold dualAngleFourier
  have hmul : ∀ j, dualAngleChar m j * dualAngleChar k j = dualAngleChar (k + m) j := by
    intro j
    rw [dualAngleChar_add_left, mul_comm]
  simp_rw [hmul]
  exact sum_dualAngleChar (k + m)

/-- The amplitude on each dual angle, read from a `Fin 3` label. -/
def dualAngleAxis (f0 f1 f2 : ZMod N → ℂ) (a : Fin 3) : ZMod N → ℂ :=
  if a = 0 then f0 else if a = 1 then f1 else f2

theorem dualAngleFourier_separable (f0 f1 f2 : ZMod N → ℂ) (k : Fin 3 → ZMod N) :
    dualAngleFourier (fun j => f0 (j 0) * f1 (j 1) * f2 (j 2)) k =
      dualCircleFourier f0 (k 0) * dualCircleFourier f1 (k 1) *
        dualCircleFourier f2 (k 2) := by
  classical
  unfold dualAngleFourier dualAngleChar dualCircleFourier
  have haxis : ∀ j : Fin 3 → ZMod N,
      ∏ a, dualAngleAxis f0 f1 f2 a (j a) =
        f0 (j 0) * f1 (j 1) * f2 (j 2) := by
    intro j
    have hU : (univ : Finset (Fin 3)) = insert 0 (insert 1 ({2} : Finset (Fin 3))) := by
      decide
    rw [hU, prod_insert, prod_insert, prod_singleton]
    · simp [dualAngleAxis, mul_assoc]
    · decide
    · decide
  have hterm : ∀ j : Fin 3 → ZMod N,
      f0 (j 0) * f1 (j 1) * f2 (j 2) * ∏ a, dualCircleChar (k a) (j a) =
        ∏ a, dualAngleAxis f0 f1 f2 a (j a) * dualCircleChar (k a) (j a) := by
    intro j
    rw [← haxis j, Finset.prod_mul_distrib]
  simp_rw [hterm]
  have hfactor :=
    sum_prod_piFinset (univ : Finset (ZMod N))
      (fun a t => dualAngleAxis f0 f1 f2 a t * dualCircleChar (k a) t)
  rw [Fintype.piFinset_univ] at hfactor
  rw [hfactor]
  have hU : (univ : Finset (Fin 3)) = insert 0 (insert 1 ({2} : Finset (Fin 3))) := by
    decide
  rw [hU, prod_insert, prod_insert, prod_singleton]
  · simp [dualAngleAxis]
    ring
  · decide
  · decide

theorem dualAngle_support_uncertainty {f : (Fin 3 → ZMod N) → ℂ} (hf : ∃ j, f j ≠ 0) :
    N ^ 3 ≤ f.support.ncard * (dualAngleFourier f).support.ncard := by
  have hparse : ∀ g : (Fin 3 → ZMod N) → ℂ,
      ∑ k, ‖∑ j, g j * dualAngleChar k j‖ ^ 2 =
        ((N ^ 3 : ℕ) : ℝ) * ∑ j, ‖g j‖ ^ 2 := by
    intro g
    have h := dualAngleFourier_parseval g
    rw [← Nat.cast_pow] at h
    simpa [dualAngleFourier] using h
  unfold dualAngleFourier
  exact support_uncertainty_char dualAngleChar norm_dualAngleChar (N ^ 3) hparse hf

theorem dualAngle_support_eq_site :
    (dualAngleDelta (N := N)).support.ncard *
      (dualAngleFourier (N := N) (dualAngleDelta (N := N))).support.ncard = N ^ 3 := by
  have hdelta : dualAngleDelta.support = {(0 : Fin 3 → ZMod N)} := by
    ext j
    simp [Function.mem_support, dualAngleDelta]
  have hhat : (dualAngleFourier (N := N) dualAngleDelta).support = Set.univ := by
    ext k
    simp [Function.mem_support, dualAngleFourier_delta]
  have hcard : Nat.card (Fin 3 → ZMod N) = N ^ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin,
      ZMod.card N]
  rw [hdelta, hhat, Set.ncard_singleton, Set.ncard_univ, hcard, one_mul]

theorem dualAngle_support_eq_winding (m : Fin 3 → ZMod N) :
    (fun j => dualAngleChar m j).support.ncard *
      (dualAngleFourier (fun j => dualAngleChar m j)).support.ncard = N ^ 3 := by
  have hfull : (fun j => dualAngleChar m j).support = Set.univ := by
    ext j
    simp [Function.mem_support, dualAngleChar_ne_zero]
  have hhat : (dualAngleFourier (fun j => dualAngleChar m j)).support =
      {(-m : Fin 3 → ZMod N)} := by
    ext k
    simp only [Function.mem_support, Set.mem_singleton_iff, dualAngleFourier_char]
    by_cases hk : k + m = 0
    · have hpow : (N : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 (by exact_mod_cast NeZero.ne N)
      simp [hpow, show k = -m from (add_eq_zero_iff_eq_neg).1 hk]
    · simp [hk, eq_neg_iff_add_eq_zero]
  have hcard : Nat.card (Fin 3 → ZMod N) = N ^ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin,
      ZMod.card N]
  rw [hfull, hhat, Set.ncard_univ, Set.ncard_singleton, hcard, mul_one]

/-! ### Dirichlet kernel as a phase average -/

lemma expAngle_sub_neg (x : ℝ) :
    expAngle x - expAngle (-x) = 2 * I * (Real.sin x : ℂ) := by
  rw [expAngle, expAngle, exp_ofReal_mul_I, exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
    ofReal_neg]
  ring_nf

lemma expAngle_half (x : ℝ) : expAngle x = expAngle (x / 2) ^ 2 := by
  rw [sq, ← expAngle_add]
  congr 1
  ring

lemma expAngle_neg_pair (x : ℝ) : expAngle x * expAngle (-x) = 1 := by
  rw [← expAngle_add, add_neg_cancel, expAngle_zero]

lemma expAngle_sub_one (x : ℝ) :
    expAngle x - 1 = expAngle (x / 2) * (2 * I * (Real.sin (x / 2) : ℂ)) := by
  rw [expAngle_half, sq, ← expAngle_neg_pair (x / 2)]
  calc
    expAngle (x / 2) * expAngle (x / 2) - expAngle (x / 2) * expAngle (-(x / 2))
        = expAngle (x / 2) * (expAngle (x / 2) - expAngle (-(x / 2))) := by ring
    _ = expAngle (x / 2) * (2 * I * (Real.sin (x / 2) : ℂ)) := by rw [expAngle_sub_neg]

lemma expAngle_one_of_sin_half {θ : ℝ} (h : Real.sin (θ / 2) = 0) : expAngle θ = 1 := by
  have hcos : Real.cos (θ / 2) ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq (θ / 2)
    simpa [h] using this
  have hhalf : expAngle (θ / 2) = Real.cos (θ / 2) := by
    rw [expAngle, exp_ofReal_mul_I]
    simp [h]
  rw [expAngle_half, hhalf, ← ofReal_pow, hcos, ofReal_one]

lemma expAngle_ne_one_of_sin_half {θ : ℝ} (h : Real.sin (θ / 2) ≠ 0) : expAngle θ ≠ 1 := by
  intro h1
  rw [expAngle_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have : θ / 2 = n * π := by rw [hn]; ring
  rw [this, Real.sin_int_mul_pi] at h
  exact h rfl

omit [NeZero N] in
lemma phaseSum_shift (θ : ℝ) :
    ∑ k ∈ range N, expAngle (((k : ℝ) - ((N : ℝ) - 1) / 2) * θ) =
      expAngle (-(((N : ℝ) - 1) / 2) * θ) * ∑ k ∈ range N, expAngle ((k : ℝ) * θ) := by
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← expAngle_add]
  congr 1
  ring

omit [NeZero N] in
lemma phaseSum_geom (θ : ℝ) (h : expAngle θ ≠ 1) :
    ∑ k ∈ range N, expAngle ((k : ℝ) * θ) =
      (expAngle ((N : ℝ) * θ) - 1) / (expAngle θ - 1) := by
  have hpow : ∀ k : ℕ, expAngle ((k : ℝ) * θ) = expAngle θ ^ k := by
    intro k
    simpa [mul_comm] using expAngle_nat k θ
  simp_rw [hpow]
  exact geom_sum_eq h N

omit [NeZero N] in
lemma phaseSum_sin (θ : ℝ) (hs : Real.sin (θ / 2) ≠ 0) :
    ∑ k ∈ range N, expAngle (((k : ℝ) - ((N : ℝ) - 1) / 2) * θ) =
      (Real.sin ((N : ℝ) * θ / 2) : ℂ) / Real.sin (θ / 2) := by
  have hθ : expAngle θ ≠ 1 := expAngle_ne_one_of_sin_half hs
  rw [phaseSum_shift, phaseSum_geom θ hθ, expAngle_sub_one ((N : ℝ) * θ), expAngle_sub_one θ]
  have hjoin : expAngle (-(((N : ℝ) - 1) / 2) * θ) * expAngle ((N : ℝ) * θ / 2) =
      expAngle (θ / 2) := by
    rw [← expAngle_add]
    congr 1
    ring
  have hsC : (Real.sin (θ / 2) : ℂ) ≠ 0 := by exact_mod_cast hs
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  rw [mul_div, ← mul_assoc, hjoin]
  field_simp [htwo, I_ne_zero, hsC]
  have he : expAngle (θ / 2) ≠ 0 := by simp [expAngle]
  field_simp [he]

lemma cos_sq_of_sin_zero {x : ℝ} (h : Real.sin x = 0) : Real.cos x ^ 2 = 1 := by
  have := Real.sin_sq_add_cos_sq x
  simpa [h] using this

omit [NeZero N] in
lemma phaseSum_on_lattice (θ : ℝ) (hs : Real.sin (θ / 2) = 0) :
    ∑ k ∈ range N, expAngle (((k : ℝ) - ((N : ℝ) - 1) / 2) * θ) =
      (N : ℂ) * (Real.cos ((N : ℝ) * θ / 2) / Real.cos (θ / 2)) := by
  have h1 : expAngle θ = 1 := expAngle_one_of_sin_half hs
  have hcommon : ∀ k : ℕ,
      expAngle (((k : ℝ) - ((N : ℝ) - 1) / 2) * θ) =
        expAngle (-(((N : ℝ) - 1) / 2) * θ) := by
    intro k
    rw [show ((k : ℝ) - ((N : ℝ) - 1) / 2) * θ =
      (k : ℝ) * θ + (-(((N : ℝ) - 1) / 2) * θ) by ring, expAngle_add]
    rw [mul_comm, expAngle_nat, h1, one_pow, mul_one]
  rw [sum_congr rfl fun k _ => hcommon k, sum_const, card_range, nsmul_eq_mul]
  have hhalf : expAngle (θ / 2) = Real.cos (θ / 2) := by
    rw [expAngle, exp_ofReal_mul_I]
    simp [hs]
  have hz2 : expAngle ((N : ℝ) * θ / 2) ^ 2 = 1 := by
    rw [← expAngle_half]
    have hmul : (N : ℝ) * θ = (N : ℕ) * θ := by simp
    rw [hmul, expAngle_nat, h1, one_pow]
  have hzreal : expAngle ((N : ℝ) * θ / 2) = Real.cos ((N : ℝ) * θ / 2) := by
    have him : (expAngle ((N : ℝ) * θ / 2)).im = Real.sin ((N : ℝ) * θ / 2) := by
      rw [expAngle, exp_ofReal_mul_I_im]
    have hsq : (expAngle ((N : ℝ) * θ / 2) - 1) * (expAngle ((N : ℝ) * θ / 2) + 1) = 0 := by
      have : (expAngle ((N : ℝ) * θ / 2) - 1) * (expAngle ((N : ℝ) * θ / 2) + 1) =
          expAngle ((N : ℝ) * θ / 2) ^ 2 - 1 := by ring
      rw [this, hz2, sub_self]
    have hone : expAngle ((N : ℝ) * θ / 2) = 1 ∨ expAngle ((N : ℝ) * θ / 2) = -1 := by
      rcases mul_eq_zero.mp hsq with h0 | h0
      · exact Or.inl (sub_eq_zero.mp h0)
      · exact Or.inr (eq_neg_iff_add_eq_zero.mpr (by simpa using h0))
    have hsin0 : Real.sin ((N : ℝ) * θ / 2) = 0 := by
      cases hone with
      | inl h0 =>
          have := congrArg Complex.im h0
          simpa [him] using this
      | inr h0 =>
          have := congrArg Complex.im h0
          simpa [him] using this
    rw [expAngle, exp_ofReal_mul_I]
    simp [hsin0]
  have hneg : expAngle (-((N : ℝ) * θ / 2)) = expAngle ((N : ℝ) * θ / 2) := by
    have hx0 : expAngle ((N : ℝ) * θ / 2) ≠ 0 := by
      simp [expAngle]
    have hinv : expAngle (-((N : ℝ) * θ / 2)) =
        (expAngle ((N : ℝ) * θ / 2))⁻¹ := by
      apply mul_left_cancel₀ hx0
      rw [expAngle_neg_pair, mul_inv_cancel₀ hx0]
    have hself : (expAngle ((N : ℝ) * θ / 2))⁻¹ = expAngle ((N : ℝ) * θ / 2) :=
      inv_eq_of_mul_eq_one_right (by simpa [sq] using hz2)
    rw [hinv, hself]
  have hsplit : expAngle (-(((N : ℝ) - 1) / 2) * θ) =
      expAngle (-((N : ℝ) * θ / 2)) * expAngle (θ / 2) := by
    rw [← expAngle_add]
    congr 1
    ring
  rw [hsplit, hneg, hzreal, hhalf, ← ofReal_mul]
  have hcos : Real.cos ((N : ℝ) * θ / 2) * Real.cos (θ / 2) =
      Real.cos ((N : ℝ) * θ / 2) / Real.cos (θ / 2) := by
    have hc : Real.cos (θ / 2) ^ 2 = 1 := cos_sq_of_sin_zero hs
    have hne : Real.cos (θ / 2) ≠ 0 := by
      intro h0
      have := cos_sq_of_sin_zero hs
      simp [h0] at this
    rw [div_eq_mul_inv]
    congr 1
    exact (inv_eq_of_mul_eq_one_right (by simpa [sq] using hc)).symm
  rw [hcos]
  push_cast
  ring

/-- Off the lattice and on it,
`D_N(θ) = (1/N) ∑_{k<N} exp(i (k-(N-1)/2) θ)`. -/
theorem dirichletKernel_eq_phaseAverage (θ : ℝ) :
    (DirichletKernel.dirichletKernel N θ : ℂ) =
      (N : ℂ)⁻¹ * ∑ k ∈ range N,
        exp (I * (((k : ℝ) - ((N : ℝ) - 1) / 2) * θ)) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hconv : ∑ k ∈ range N, exp (I * (((k : ℝ) - ((N : ℝ) - 1) / 2) * θ)) =
      ∑ k ∈ range N, expAngle (((k : ℝ) - ((N : ℝ) - 1) / 2) * θ) := by
    refine sum_congr rfl fun k _ => ?_
    congr 1
    push_cast
    ring
  rw [hconv]
  by_cases hs : Real.sin (θ / 2) = 0
  · rw [DirichletKernel.dirichletKernel_of_sin_eq_zero hs, phaseSum_on_lattice θ hs,
      ofReal_div]
    rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  · rw [DirichletKernel.dirichletKernel_of_sin_ne_zero hs, phaseSum_sin θ hs, ofReal_div,
      ofReal_mul, ofReal_natCast]
    field_simp

end

end DualFourier

end DstDiophantine
