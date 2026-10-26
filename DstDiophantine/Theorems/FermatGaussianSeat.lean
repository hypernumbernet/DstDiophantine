import DstDiophantine.Embedding.FermatMotor
import DstDiophantine.Theorems.FermatMixed
import DstDiophantine.Theorems.BealGaussianCube
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Gaussian generator versus the Pythagorean dual rotor

On the equal-odd Beal leaf the hypotenuse is a norm in `ℤ[i]`. That one
Gaussian integer carries two seats:

* the square-difference legs `(m² − n², 2mn, m² + n²)` are a pure dual rotor
  (vanishing boost) whose cyclic angle is twice the argument of `m + ni`;
* the generators read against the integer base of `m² + n² = c^e`, for odd
  `e ≥ 5`, are a mixed motor. The boost equals `((e − 2) / 2) log c` and
  exceeds a right angle, so the seed lies outside the admissible cone.

The boost sits on axis `0` and the cyclic angle on axis `1`. The two axes
do not commute. This is the same split that forces every positive solution
of degree `n ≥ 3` to be mixed. The cone excludes the generator as a particle
configuration; it does not decide the integer residual.
-/

namespace DstDiophantine

namespace Theorems

open _root_.DstDiophantine.Embedding Real Amplification Admissible Operations Invariant

private theorem natAbs_coe_eq_coe_of_pos {z : ℤ} (hz : 0 < z) :
    (z.natAbs : ℝ) = (z : ℝ) := by
  have h : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg (le_of_lt hz)
  calc (z.natAbs : ℝ) = ((z.natAbs : ℤ) : ℝ) := rfl
    _ = (z : ℝ) := by rw [h]

private theorem natAbs_cast_sq (z : ℤ) :
    (z.natAbs : ℝ) ^ 2 = (z : ℝ) ^ 2 := by
  have h : ((z.natAbs : ℕ) : ℤ) = |z| := Int.natCast_natAbs z
  have hR : (z.natAbs : ℝ) = |(z : ℝ)| := by
    have := congrArg (fun t : ℤ => (t : ℝ)) h
    simp [Int.cast_abs]
  rw [hR, sq_abs]

private theorem natAbs_ge_two_of_even_ne_zero {z : ℤ} (he : Even z) (hz : z ≠ 0) :
    2 ≤ z.natAbs := by
  have he' : Even z.natAbs := Int.natAbs_even.mpr he
  have hne : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  obtain ⟨k, hk⟩ := he'
  have hk2 : z.natAbs = 2 * k := by simpa [two_mul] using hk
  have hk0 : k ≠ 0 := by
    intro hk0
    apply hne
    simp [hk2, hk0]
  omega

private theorem sq_ge_of_natAbs_ge {z : ℤ} {k : ℕ} (hk : k ≤ z.natAbs) :
    ((k : ℤ) ^ 2) ≤ z ^ 2 := by
  have hnat : k ^ 2 ≤ z.natAbs ^ 2 := Nat.pow_le_pow_left hk 2
  have hcast : ((z.natAbs : ℕ) : ℤ) ^ 2 = z ^ 2 := by
    rw [Int.natCast_natAbs, sq_abs]
  have : ((k : ℕ) : ℤ) ^ 2 ≤ ((z.natAbs : ℕ) : ℤ) ^ 2 := by
    exact_mod_cast hnat
  simpa [hcast] using this

/-- Opposite parity makes `m² + n²` an odd integer at least `5`. -/
theorem sum_sq_ge_five_of_opposite_parity {m n : ℤ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    (5 : ℤ) ≤ m ^ 2 + n ^ 2 ∧ Odd (m ^ 2 + n ^ 2) := by
  have hone {z : ℤ} (hz : z ≠ 0) : (1 : ℤ) ≤ z ^ 2 := by
    have h1 : 1 ≤ z.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hz)
    exact sq_ge_of_natAbs_ge h1
  rcases hpar with ⟨hmE, hnO⟩ | ⟨hmO, hnE⟩
  · have hm4 : (4 : ℤ) ≤ m ^ 2 :=
      sq_ge_of_natAbs_ge (natAbs_ge_two_of_even_ne_zero hmE hm)
    have hn1 : (1 : ℤ) ≤ n ^ 2 := hone hn
    refine ⟨by linarith, ?_⟩
    rw [Int.odd_iff]
    have hm_mod : m % 2 = 0 := Int.even_iff.mp hmE
    have hn_mod : n % 2 = 1 := Int.odd_iff.mp hnO
    have hsq {z : ℤ} : z ^ 2 % 2 = z % 2 := by
      have : z % 2 = 0 ∨ z % 2 = 1 := by omega
      rcases this with h | h <;> simp [pow_two, Int.mul_emod, h]
    have : (m ^ 2 + n ^ 2) % 2 = (0 + 1) % 2 := by
      rw [Int.add_emod, hsq, hsq, hm_mod, hn_mod]
    simpa using this
  · have hn4 : (4 : ℤ) ≤ n ^ 2 :=
      sq_ge_of_natAbs_ge (natAbs_ge_two_of_even_ne_zero hnE hn)
    have hm1 : (1 : ℤ) ≤ m ^ 2 := hone hm
    refine ⟨by linarith, ?_⟩
    rw [Int.odd_iff]
    have hm_mod : m % 2 = 1 := Int.odd_iff.mp hmO
    have hn_mod : n % 2 = 0 := Int.even_iff.mp hnE
    have hsq {z : ℤ} : z ^ 2 % 2 = z % 2 := by
      have : z % 2 = 0 ∨ z % 2 = 1 := by omega
      rcases this with h | h <;> simp [pow_two, Int.mul_emod, h]
    have : (m ^ 2 + n ^ 2) % 2 = (1 + 0) % 2 := by
      rw [Int.add_emod, hsq, hsq, hm_mod, hn_mod]
    simpa using this

/-- A pure odd power of an opposite-parity norm has base at least `3`. -/
theorem nat_base_ge_three_of_opposite_parity_pow {m n : ℤ} {c e : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (he : 0 < e)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e) :
    3 ≤ c := by
  obtain ⟨hge, hodd⟩ := sum_sq_ge_five_of_opposite_parity hm hn hpar
  have hpow : (5 : ℤ) ≤ (c : ℤ) ^ e := by simpa [heq] using hge
  have hodd' : Odd ((c : ℤ) ^ e) := by simpa [heq] using hodd
  by_contra hlt
  have hc_le : c ≤ 2 := by omega
  have hc0 : c ≠ 0 := by
    intro h0
    subst h0
    simp [zero_pow (by omega : e ≠ 0)] at hpow
  have hc1 : c ≠ 1 := by
    intro h1
    subst h1
    simp at hpow
  have hc_eq : c = 2 := by omega
  subst hc_eq
  have heven : Even ((2 : ℤ) ^ e) := by
    refine ⟨(2 : ℤ) ^ (e - 1), ?_⟩
    have he1 : e = (e - 1) + 1 := by omega
    conv_lhs => rw [he1]
    rw [pow_succ]
    ring
  exact Int.not_odd_iff_even.mpr heven hodd'

/--
`m² + n² = c^e` fixes the radius boost:
`α = ((e − 2) / 2) log c`.
-/
theorem fermatBoost_of_sum_sq_eq_pow {m n c : ℤ} {e : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (heq : m ^ 2 + n ^ 2 = c ^ e) :
    fermatBoost m n c (ne_of_gt hc) =
      (((e : ℝ) - 2) / 2) * Real.log (c : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hs : (m : ℝ) ^ 2 + (n : ℝ) ^ 2 = (c : ℝ) ^ e := by exact_mod_cast heq
  have hspos : 0 < (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by positivity
  have hL : fermatL2 m n = Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) := by
    unfold fermatL2
    rw [natAbs_coe_eq_coe_of_pos hm, natAbs_coe_eq_coe_of_pos hn]
  have hcAbs : (c.natAbs : ℝ) = (c : ℝ) := natAbs_coe_eq_coe_of_pos hc
  unfold fermatBoost
  rw [hL, hcAbs, hs]
  have hsqrt : 0 ≤ (c : ℝ) ^ e := by positivity
  rw [Real.log_div (Real.sqrt_pos.mpr (by positivity : 0 < (c : ℝ) ^ e)).ne' hcR.ne',
    Real.log_sqrt hsqrt, Real.log_pow]
  ring

private theorem fermatBoost_eq_abs {a b c : ℤ} (hc : c ≠ 0) :
    fermatBoost a b c hc = fermatBoost |a| |b| c hc := by
  unfold fermatBoost fermatL2
  congr 1
  congr 1
  rw [Int.natAbs_abs a, Int.natAbs_abs b]

private theorem half_pi_lt_three_halves_log_three :
    Real.pi / 2 < (3 / 2) * Real.log 3 := by
  have hlog : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have hpi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  nlinarith

/-- For `e ≥ 5` and base at least `3`, the norm boost exceeds a right angle. -/
theorem fermatBoost_gt_half_pi_of_sum_sq_eq_pow {m n c : ℤ} {e : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hc : 3 ≤ c) (he : 5 ≤ e)
    (heq : m ^ 2 + n ^ 2 = c ^ e) :
    Real.pi / 2 < fermatBoost m n c (by omega) := by
  have hc0 : 0 < c := by omega
  rw [fermatBoost_of_sum_sq_eq_pow hm hn hc0 heq]
  have he' : (3 : ℝ) / 2 ≤ ((e : ℝ) - 2) / 2 := by
    have : (5 : ℝ) ≤ e := by exact_mod_cast he
    linarith
  have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
  have hlog : Real.log 3 ≤ Real.log (c : ℝ) :=
    (Real.log_le_log_iff (by norm_num) (by exact_mod_cast hc0)).mpr hcR
  have hmul : (3 / 2) * Real.log 3 ≤ (((e : ℝ) - 2) / 2) * Real.log (c : ℝ) := by
    have hlog0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    exact mul_le_mul he' hlog hlog0 (by linarith)
  exact lt_of_lt_of_le half_pi_lt_three_halves_log_three hmul

theorem fermatBoost_gt_half_pi_of_gaussian_norm {m n : ℤ} {c e : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (he : 5 ≤ e)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e) :
    Real.pi / 2 < fermatBoost m n (c : ℤ) (by
      have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
      exact_mod_cast (by omega : c ≠ 0)) := by
  have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
  have hmabs : 0 < |m| := abs_pos.mpr hm
  have hnabs : 0 < |n| := abs_pos.mpr hn
  have heqAbs' : |m| ^ 2 + |n| ^ 2 = (c : ℤ) ^ e := by
    rw [sq_abs, sq_abs, heq]
  have hboost :=
    fermatBoost_gt_half_pi_of_sum_sq_eq_pow (c := (c : ℤ)) (e := e)
      hmabs hnabs (by exact_mod_cast hc3) he heqAbs'
  have hcne : (c : ℤ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  rw [fermatBoost_eq_abs hcne]
  exact hboost

theorem isMixedFermatMotor_of_gaussian_norm {m n : ℤ} {c e : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (he : 5 ≤ e)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e) :
    IsMixedFermatMotor m n (c : ℤ) hm (by
      have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
      exact_mod_cast (by omega : c ≠ 0)) := by
  have hcne : (c : ℤ) ≠ 0 := by
    have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
    exact_mod_cast (by omega : c ≠ 0)
  refine ⟨?_, fermatAngle_pos_of_b_ne hm hn, fermatAngle_lt_half_pi m n hm⟩
  exact lt_trans (by positivity) (fermatBoost_gt_half_pi_of_gaussian_norm hm hn he hpar heq)

theorem fermatBoost_gt_fermatAngle_of_gaussian_norm {m n : ℤ} {c e : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (he : 5 ≤ e)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e) :
    fermatAngle m n hm <
      fermatBoost m n (c : ℤ) (by
        have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
        exact_mod_cast (by omega : c ≠ 0)) := by
  have hβ : fermatAngle m n hm < Real.pi / 2 := fermatAngle_lt_half_pi m n hm
  exact lt_trans hβ (fermatBoost_gt_half_pi_of_gaussian_norm hm hn he hpar heq)

theorem J_fermatTorsion_pos_of_gaussian_norm {m n : ℤ} {c e : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (he : 5 ≤ e)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e) :
    0 < J (fermatTorsion m n (c : ℤ) hm (by
      have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
      exact_mod_cast (by omega : c ≠ 0))) := by
  have hcne : (c : ℤ) ≠ 0 := by
    have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
    exact_mod_cast (by omega : c ≠ 0)
  rw [J_fermatTorsion]
  have hlt := fermatBoost_gt_fermatAngle_of_gaussian_norm hm hn he hpar heq
  have hβ : 0 ≤ fermatAngle m n hm := fermatAngle_nonneg m n hm
  have hsq : fermatAngle m n hm ^ 2 < fermatBoost m n (c : ℤ) hcne ^ 2 := by
    nlinarith [hβ, hlt]
  linarith

theorem not_isAdmissible_fermatTorsion_of_gaussian_norm {m n : ℤ} {c e : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (he : 5 ≤ e)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e) :
    ¬ IsAdmissibleContinuous (fermatTorsion m n (c : ℤ) hm (by
      have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
      exact_mod_cast (by omega : c ≠ 0))) := by
  have hcne : (c : ℤ) ≠ 0 := by
    have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
    exact_mod_cast (by omega : c ≠ 0)
  intro hAdm
  have hsum := admissibleContinuous_sum_le _ hAdm 0
  have hne01 : (0 : Fin 3) ≠ 1 := by decide
  simp only [fermatTorsion, hne01, ite_false, ite_true, add_zero] at hsum
  exact not_le_of_gt (fermatBoost_gt_half_pi_of_gaussian_norm hm hn he hpar heq) hsum

theorem fermatInterfere_ne_zero_of_gaussian_norm {m n : ℤ} {c e : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (he : 5 ≤ e)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e) :
    fermatInterfere m n (c : ℤ) hm (by
      have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
      exact_mod_cast (by omega : c ≠ 0)) ≠ 0 :=
  fermatInterfere_ne_zero_of_mixed hm _ (isMixedFermatMotor_of_gaussian_norm hm hn he hpar heq)

/-! ### Square-difference legs: a pure dual rotor -/

theorem pythagorean_generator_identity (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  ring

theorem isPureCyclic_pythagorean_generators {m n : ℤ}
    (hm : m ≠ 0) (hne : m.natAbs ≠ n.natAbs) :
    IsPureCyclicFermatMotor (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2)
      (by
        intro h
        nlinarith [sq_nonneg m, sq_nonneg n, sq_pos_of_ne_zero hm, h]) := by
  have ha : m ^ 2 - n ^ 2 ≠ 0 := by
    intro h
    have hm_sq : (m.natAbs : ℤ) ^ 2 = m ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
    have hn_sq : (n.natAbs : ℤ) ^ 2 = n ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
    have hsqZ : (m.natAbs : ℤ) ^ 2 = (n.natAbs : ℤ) ^ 2 := by
      rw [hm_sq, hn_sq]
      linarith
    have hsq : m.natAbs ^ 2 = n.natAbs ^ 2 := by exact_mod_cast hsqZ
    exact hne (Nat.pow_left_injective (by decide : 2 ≠ 0) hsq)
  have hc : m ^ 2 + n ^ 2 ≠ 0 := by
    intro h
    nlinarith [sq_nonneg m, sq_nonneg n, sq_pos_of_ne_zero hm, h]
  rw [isPureCyclic_iff_pythagorean hc (Or.inl ha)]
  have hid := pythagorean_generator_identity m n
  have hR : ((m ^ 2 - n ^ 2 : ℤ) : ℝ) ^ 2 + ((2 * m * n : ℤ) : ℝ) ^ 2 =
      ((m ^ 2 + n ^ 2 : ℤ) : ℝ) ^ 2 := by exact_mod_cast hid
  rw [natAbs_cast_sq (m ^ 2 - n ^ 2), natAbs_cast_sq (2 * m * n),
    natAbs_cast_sq (m ^ 2 + n ^ 2)]
  exact hR

theorem natAbs_ne_of_opposite_parity {m n : ℤ}
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    m.natAbs ≠ n.natAbs := by
  intro h
  have hparN : (Even m.natAbs ∧ Odd n.natAbs) ∨ (Odd m.natAbs ∧ Even n.natAbs) := by
    rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
    · exact Or.inl ⟨Int.natAbs_even.mpr hm, Int.natAbs_odd.mpr hn⟩
    · exact Or.inr ⟨Int.natAbs_odd.mpr hm, Int.natAbs_even.mpr hn⟩
  rw [h] at hparN
  rcases hparN with ⟨he, ho⟩ | ⟨ho, he⟩
  · exact Nat.not_even_iff_odd.mpr ho he
  · exact Nat.not_even_iff_odd.mpr ho he

/-- The cyclic angle of the legs is twice the argument of the Gaussian generator. -/
theorem fermatAngle_pythagorean_eq_two_mul {m n : ℤ}
    (hm : 0 < m) (hn : 0 < n) (hlt : n < m) :
    fermatAngle (m ^ 2 - n ^ 2) (2 * m * n)
        (by
          have : 0 < m ^ 2 - n ^ 2 := by nlinarith
          exact ne_of_gt this) =
      2 * fermatAngle m n (ne_of_gt hm) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hltR : (n : ℝ) < m := by exact_mod_cast hlt
  have ha0 : 0 < m ^ 2 - n ^ 2 := by nlinarith
  have hb0 : 0 < 2 * m * n := by nlinarith
  unfold fermatAngle
  rw [natAbs_coe_eq_coe_of_pos ha0, natAbs_coe_eq_coe_of_pos hb0,
    natAbs_coe_eq_coe_of_pos hm, natAbs_coe_eq_coe_of_pos hn]
  set t : ℝ := (n : ℝ) / m
  have ht0 : 0 < t := div_pos hnR hmR
  have ht1 : t < 1 := (div_lt_one hmR).mpr hltR
  have htwo := Real.two_mul_arctan (x := t) (by linarith) ht1
  have hden : (m : ℝ) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) ^ 2 - (n : ℝ) ^ 2 := by exact_mod_cast ha0
    exact ne_of_gt this
  have hcast :
      ((2 * m * n : ℤ) : ℝ) / ((m ^ 2 - n ^ 2 : ℤ) : ℝ) =
        2 * t / (1 - t ^ 2) := by
    unfold t
    push_cast
    field_simp
  rw [hcast, htwo]

/-- The same doubling, measured from the larger coordinate when it is the second generator. -/
theorem fermatAngle_pythagorean_eq_two_mul_of_gt {m n : ℤ}
    (hm : 0 < m) (hn : 0 < n) (hlt : m < n) :
    fermatAngle (m ^ 2 - n ^ 2) (2 * m * n)
        (by
          have : m ^ 2 - n ^ 2 ≠ 0 := by nlinarith
          exact this) =
      2 * fermatAngle n m (ne_of_gt hn) := by
  have h := fermatAngle_pythagorean_eq_two_mul hn hm hlt
  unfold fermatAngle at h ⊢
  have hleg : (m ^ 2 - n ^ 2).natAbs = (n ^ 2 - m ^ 2).natAbs := by
    have : m ^ 2 - n ^ 2 = -(n ^ 2 - m ^ 2) := by ring
    rw [this, Int.natAbs_neg]
  have hprod : (2 * m * n).natAbs = (2 * n * m).natAbs := by
    have : 2 * m * n = 2 * n * m := by ring
    rw [this]
  rw [hleg, hprod]
  exact h

theorem odd_leg_ne_zero_of_natAbs_ne {m n : ℤ} (hne : m.natAbs ≠ n.natAbs) :
    m ^ 2 - n ^ 2 ≠ 0 := by
  intro h
  have hm_sq : (m.natAbs : ℤ) ^ 2 = m ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
  have hn_sq : (n.natAbs : ℤ) ^ 2 = n ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
  have hsqZ : (m.natAbs : ℤ) ^ 2 = (n.natAbs : ℤ) ^ 2 := by
    rw [hm_sq, hn_sq]
    linarith
  exact hne (Nat.pow_left_injective (by decide : 2 ≠ 0) (by exact_mod_cast hsqZ))

theorem hyp_ne_zero_of_ne {m n : ℤ} (hm : m ≠ 0) : m ^ 2 + n ^ 2 ≠ 0 := by
  intro h
  nlinarith [sq_nonneg m, sq_nonneg n, sq_pos_of_ne_zero hm, h]

private theorem torsionParams_eq {p q : TorsionParams}
    (hα : p.alpha = q.alpha) (hβ : p.beta = q.beta) : p = q := by
  cases p
  cases q
  cases hα
  cases hβ
  rfl

/-- The Pythagorean seat is the dual rotor of its cyclic angle. -/
theorem fermatTorsion_eq_pureRotation1_of_pythagorean {m n : ℤ}
    (hm : m ≠ 0) (_hn : n ≠ 0) (hne : m.natAbs ≠ n.natAbs) :
    fermatTorsion (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2)
        (odd_leg_ne_zero_of_natAbs_ne hne) (hyp_ne_zero_of_ne hm) =
      pureRotation1
        (fermatAngle (m ^ 2 - n ^ 2) (2 * m * n) (odd_leg_ne_zero_of_natAbs_ne hne)) := by
  have h0 := isPureCyclic_pythagorean_generators hm hne
  have hboost :
      fermatBoost (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2) (hyp_ne_zero_of_ne hm) = 0 := by
    simpa [IsPureCyclicFermatMotor] using h0
  have hα : (fermatTorsion (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2)
      (odd_leg_ne_zero_of_natAbs_ne hne) (hyp_ne_zero_of_ne hm)).alpha =
      (pureRotation1 (fermatAngle (m ^ 2 - n ^ 2) (2 * m * n)
        (odd_leg_ne_zero_of_natAbs_ne hne))).alpha := by
    ext i
    fin_cases i <;> simp [fermatTorsion, pureRotation1, hboost]
  have hβ : (fermatTorsion (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2)
      (odd_leg_ne_zero_of_natAbs_ne hne) (hyp_ne_zero_of_ne hm)).beta =
      (pureRotation1 (fermatAngle (m ^ 2 - n ^ 2) (2 * m * n)
        (odd_leg_ne_zero_of_natAbs_ne hne))).beta := by
    ext i
    fin_cases i <;> simp [fermatTorsion, pureRotation1]
  exact torsionParams_eq hα hβ

/-- The square-difference seat lies in the admissible cone. -/
theorem isAdmissible_pythagorean_generators {m n : ℤ}
    (hm : m ≠ 0) (_hn : n ≠ 0) (hne : m.natAbs ≠ n.natAbs) :
    IsAdmissibleContinuous
      (fermatTorsion (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2)
        (odd_leg_ne_zero_of_natAbs_ne hne) (hyp_ne_zero_of_ne hm)) := by
  have h0 := isPureCyclic_pythagorean_generators hm hne
  have hboost :
      fermatBoost (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2) (hyp_ne_zero_of_ne hm) = 0 := by
    simpa [IsPureCyclicFermatMotor] using h0
  intro i
  fin_cases i
  · refine ⟨?_, ?_, ?_⟩
    · simp [fermatTorsion, hboost]
    · simp [fermatTorsion]
    · simpa [fermatTorsion, hboost] using (Real.pi_div_two_pos.le)
  · refine ⟨?_, ?_, ?_⟩
    · simp [fermatTorsion]
    · simpa [fermatTorsion] using
        fermatAngle_nonneg (m ^ 2 - n ^ 2) (2 * m * n) (odd_leg_ne_zero_of_natAbs_ne hne)
    · have hlt :=
        fermatAngle_lt_half_pi (m ^ 2 - n ^ 2) (2 * m * n) (odd_leg_ne_zero_of_natAbs_ne hne)
      simpa [fermatTorsion] using hlt.le
  · refine ⟨by simp [fermatTorsion], by simp [fermatTorsion], ?_⟩
    simpa [fermatTorsion] using Real.pi_div_two_pos.le

/--
Equal-odd Gaussian hypotenuse of exponent `e ≥ 5`: the generator is a mixed
hyperbolic motor outside the admissible cone, and the square-difference legs
are an admissible pure dual rotor.
-/
theorem gaussian_hyp_split_of_exp_ge_five {m n : ℤ} {e : ℕ}
    (he : 5 ≤ e) (hm : m ≠ 0) (hn : n ≠ 0)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (hIs : IsGaussianHypotenusePower m n e) :
    ∃ c : ℕ, ∃ (_h3 : 3 ≤ c) (hc : (c : ℤ) ≠ 0),
      m ^ 2 + n ^ 2 = (c : ℤ) ^ e ∧
      fermatBoost m n (c : ℤ) hc = (((e : ℝ) - 2) / 2) * Real.log (c : ℝ) ∧
      Real.pi / 2 < fermatBoost m n (c : ℤ) hc ∧
      IsMixedFermatMotor m n (c : ℤ) hm hc ∧
      ¬ IsAdmissibleContinuous (fermatTorsion m n (c : ℤ) hm hc) ∧
      IsPureCyclicFermatMotor (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2)
        (hyp_ne_zero_of_ne hm) ∧
      IsAdmissibleContinuous
        (fermatTorsion (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2)
          (odd_leg_ne_zero_of_natAbs_ne (natAbs_ne_of_opposite_parity hpar))
          (hyp_ne_zero_of_ne hm)) := by
  obtain ⟨c, heq⟩ := sum_sq_eq_natAbs_norm_pow_of_gaussian_hyp hIs
  have hc3 := nat_base_ge_three_of_opposite_parity_pow hm hn hpar (by omega) heq
  have hcne : (c : ℤ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hne := natAbs_ne_of_opposite_parity hpar
  refine ⟨c, hc3, hcne, heq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmabs : 0 < |m| := abs_pos.mpr hm
    have hnabs : 0 < |n| := abs_pos.mpr hn
    have heqAbs' : |m| ^ 2 + |n| ^ 2 = (c : ℤ) ^ e := by
      rw [sq_abs, sq_abs, heq]
    have hformula :=
      fermatBoost_of_sum_sq_eq_pow (c := (c : ℤ)) (e := e) hmabs hnabs
        (by exact_mod_cast (show 0 < c by omega)) heqAbs'
    rw [fermatBoost_eq_abs hcne]
    exact hformula
  · exact fermatBoost_gt_half_pi_of_gaussian_norm hm hn he hpar heq
  · exact isMixedFermatMotor_of_gaussian_norm hm hn he hpar heq
  · exact not_isAdmissible_fermatTorsion_of_gaussian_norm hm hn he hpar heq
  · exact isPureCyclic_pythagorean_generators hm hne
  · exact isAdmissible_pythagorean_generators hm hn hne

end Theorems

end DstDiophantine
