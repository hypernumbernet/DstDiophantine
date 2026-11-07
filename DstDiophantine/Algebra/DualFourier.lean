import DstDiophantine.Algebra.DirichletKernel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Fintype.Pi
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

This is not the state space `ℂ²`, not the indefinite Killing pairing, and not
the canonical pair on the continuous chart.
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
