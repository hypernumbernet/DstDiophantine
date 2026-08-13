import DstDiophantine.Theorems.Beal
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Phase 7h: Pythagorean UFD descent for Beal `d = 2`

Isolated from `Beal.lean` / `BealSlice.lean`.

## Closed (no hypotheses)

* `bealExpGcd = 2` with `4 ∣ x ∧ 4 ∣ z` and the symmetric `4 ∣ y ∧ 4 ∣ z`;
* any `d = 2` solution where at least two of `{x,y,z}` are divisible by 4.

## Residual (type only)

* `BealPythagoreanResidual`

## Discrete tools

* `ℕ`-UFD for `2mn` an `e`-th power;
* `ℤ[i]` hypotenuse-power preparation (full descent deferred).

Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

open GaussianInt

local notation "ℤ[i]" => GaussianInt

/-! ### Helpers -/

private lemma natAbs_pow_four (a : ℤ) : (a.natAbs : ℤ) ^ 4 = a ^ 4 := by
  have hnonneg : 0 ≤ a ^ 4 := Even.pow_nonneg (by decide : Even 4) a
  calc (a.natAbs : ℤ) ^ 4
      = ↑(a.natAbs ^ 4) := by norm_cast
    _ = ↑((a ^ 4).natAbs) := by rw [← Int.natAbs_pow]
    _ = a ^ 4 := Int.natAbs_of_nonneg hnonneg

private lemma four_dvd_iff_even_div_two {n : ℕ} (h2 : 2 ∣ n) :
    4 ∣ n ↔ Even (n / 2) := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk, show 4 * k = 2 * (2 * k) from by ring,
      Nat.mul_div_right (2 * k) (by decide : 0 < 2)]
    exact even_two_mul _
  · intro h
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp h
    have hn : n = 2 * (n / 2) := (Nat.mul_div_cancel' h2).symm
    rw [hn, hk]
    exact ⟨k, by ring⟩

/-! ### Coprime products of powers (`ℕ` UFD) -/

theorem nat_eq_pow_of_mul_eq_pow_of_coprime {a b c : ℕ} {e : ℕ}
    (hcop : Nat.Coprime a b) (h : a * b = c ^ e) :
    ∃ u, a = u ^ e := by
  have hab : IsUnit (Nat.gcd a b) := by
    rw [Nat.Coprime.gcd_eq_one hcop]
    exact isUnit_one
  exact exists_eq_pow_of_mul_eq_pow hab h

theorem nat_eq_pow_of_mul_eq_pow_of_coprime_right {a b c : ℕ} {e : ℕ}
    (hcop : Nat.Coprime a b) (h : a * b = c ^ e) :
    ∃ v, b = v ^ e := by
  rw [mul_comm] at h
  exact nat_eq_pow_of_mul_eq_pow_of_coprime hcop.symm h

/--
If `m, n` are coprime of opposite parity and `2 * m * n` is an `e`-th power,
then the odd factor is an `e`-th power and twice the even factor is an `e`-th
power.
-/
theorem exists_pow_of_two_mul_coprime_eq_pow {m n k : ℕ} {e : ℕ}
    (hcop : Nat.Coprime m n)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : 2 * m * n = k ^ e) :
    (Even m ∧ (∃ u v, n = u ^ e ∧ 2 * m = v ^ e)) ∨
      (Even n ∧ (∃ u v, m = u ^ e ∧ 2 * n = v ^ e)) := by
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · have h2n : Nat.Coprime 2 n :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Odd.not_two_dvd_nat hn)
    have hcop2 : Nat.Coprime (2 * m) n := Nat.Coprime.mul_left h2n hcop
    have hprod : (2 * m) * n = k ^ e := by simpa [mul_assoc] using heq
    obtain ⟨u, hu⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime_right hcop2 hprod
    obtain ⟨v, hv⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime hcop2 hprod
    exact Or.inl ⟨hm, u, v, hu, hv⟩
  · have h2m : Nat.Coprime 2 m :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Odd.not_two_dvd_nat hm)
    have hcop2 : Nat.Coprime m (2 * n) := by
      rw [Nat.coprime_comm]
      exact Nat.Coprime.mul_left h2m hcop.symm
    have hprod : m * (2 * n) = k ^ e := by convert heq using 1; ring
    obtain ⟨u, hu⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime hcop2 hprod
    obtain ⟨v, hv⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime_right hcop2 hprod
    exact Or.inr ⟨hn, u, v, hu, hv⟩

theorem exists_sq_of_two_mul_coprime_eq_sq {m n k : ℕ}
    (hcop : Nat.Coprime m n)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : 2 * m * n = k ^ 2) :
    (Even m ∧ (∃ u v, n = u ^ 2 ∧ 2 * m = v ^ 2)) ∨
      (Even n ∧ (∃ u v, m = u ^ 2 ∧ 2 * n = v ^ 2)) :=
  exists_pow_of_two_mul_coprime_eq_pow hcop hpar heq

/-! ### `ℤ[i]` preparation (hypotenuse dictionary) -/

theorem gaussian_norm_mk (m n : ℤ) :
    Zsqrtd.norm (⟨m, n⟩ : ℤ[i]) = m ^ 2 + n ^ 2 := by
  simp [Zsqrtd.norm, sq]

/--
Preparation label: the hypotenuse `m^2 + n^2` is the norm of an `e`-th power in
`ℤ[i]`. Full unique-factorisation descent is left for a later cycle.
-/
def IsGaussianHypotenusePower (m n : ℤ) (e : ℕ) : Prop :=
  ∃ g : ℤ[i], Zsqrtd.norm (g ^ e) = m ^ 2 + n ^ 2

theorem isGaussianHypotenusePower_one (m n : ℤ) :
    IsGaussianHypotenusePower m n 1 :=
  ⟨⟨m, n⟩, by simp [gaussian_norm_mk]⟩

theorem isGaussianHypotenusePower_of_mk_pow {m n : ℤ} {e : ℕ}
    (h : IsGaussianHypotenusePower m n e) :
    ∃ g : ℤ[i], Zsqrtd.norm (g ^ e) = Zsqrtd.norm (⟨m, n⟩ : ℤ[i]) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.trans (gaussian_norm_mk m n).symm⟩

/-! ### Core: `a^4 + b^2 ≠ c^4` (Fermat descent on `x^4 = y^4 + z^2`) -/

/-- Nat descent target equivalent to `x^4 - y^4 = z^2` with positive terms. -/
def DiffFourthSqPos (x y : ℕ) : Prop :=
  0 < y ∧ y < x ∧ ∃ z : ℕ, 0 < z ∧ x ^ 4 = y ^ 4 + z ^ 2

private lemma gcd_sq_leg_eq_one {x y z : ℕ} (hy0 : 0 < y) (_hyx : y < x)
    (heq : x ^ 4 = y ^ 4 + z ^ 2) (hcop : Nat.Coprime x y) :
    Int.gcd ((y : ℤ) ^ 2) (z : ℤ) = 1 := by
  rw [Int.gcd, Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_natCast]
  by_contra hne
  have hgt : 1 < Nat.gcd (y ^ 2) z :=
    lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.gcd_pos_of_pos_left _ (pow_pos hy0 2)))
      (Ne.symm hne)
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
  have hp_y : p ∣ y :=
    hp.dvd_of_dvd_pow (Nat.dvd_trans hdiv (Nat.gcd_dvd_left _ _))
  have hp_z : p ∣ z := Nat.dvd_trans hdiv (Nat.gcd_dvd_right _ _)
  have hp_x : p ∣ x := by
    have : p ∣ y ^ 4 + z ^ 2 :=
      dvd_add (dvd_pow hp_y (by decide : 4 ≠ 0))
        (dvd_pow hp_z (by decide : 2 ≠ 0))
    exact hp.dvd_of_dvd_pow (heq ▸ this)
  exact hp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp hcop) ▸ Nat.dvd_gcd hp_x hp_y)

private lemma hyp_eq_of_classification {x : ℕ} {m n : ℤ}
    (hx2 : (x : ℤ) ^ 2 = m ^ 2 + n ^ 2 ∨ (x : ℤ) ^ 2 = -(m ^ 2 + n ^ 2)) :
    (x : ℤ) ^ 2 = m ^ 2 + n ^ 2 := by
  rcases hx2 with h | h
  · exact h
  · have hxnonneg : (0 : ℤ) ≤ (x : ℤ) ^ 2 := sq_nonneg _
    have hmnnonneg : (0 : ℤ) ≤ m ^ 2 + n ^ 2 := by positivity
    linarith [h, hxnonneg, hmnnonneg]

/--
No positive Nat solution of `x^4 = y^4 + z^2`.

Proved by strong induction on `x`, using Pythagorean classification of
`(y^2, z, x^2)` and `ℤ`/`ℕ`-UFD lemmas (Fermat descent).
-/
theorem not_diffFourthSqPos : ∀ {x y : ℕ}, DiffFourthSqPos x y → False := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro y ⟨hy0, hyx, z, hz0, heq⟩
    by_cases hcop : Nat.Coprime x y
    · -- Coprime case
      have hpyth : PythagoreanTriple ((y : ℤ) ^ 2) (z : ℤ) ((x : ℤ) ^ 2) := by
        delta PythagoreanTriple
        have : (y : ℤ) ^ 4 + (z : ℤ) ^ 2 = (x : ℤ) ^ 4 := by exact_mod_cast heq.symm
        linear_combination this
      have hgc : Int.gcd ((y : ℤ) ^ 2) (z : ℤ) = 1 :=
        gcd_sq_leg_eq_one hy0 hyx heq hcop
      obtain ⟨m, n, hleg, hhyp, hmn, hpar⟩ :=
        (PythagoreanTriple.coprime_classification).mp ⟨hpyth, hgc⟩
      have hx2 : (x : ℤ) ^ 2 = m ^ 2 + n ^ 2 := hyp_eq_of_classification hhyp
      rcases hleg with ⟨hy2o, _⟩ | ⟨hy2e, _⟩
      · -- Odd-leg
        have hn0 : n ≠ 0 := by
          intro hn
          have hy2o' : (y : ℤ) ^ 2 = m ^ 2 := by simpa [hn] using hy2o
          have hx2' : (x : ℤ) ^ 2 = m ^ 2 := by simpa [hn] using hx2
          have : (y : ℤ) ^ 2 = (x : ℤ) ^ 2 := by linarith [hy2o', hx2']
          have hyx_eq : y = x :=
            (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
              (by
                have := congrArg Int.natAbs this
                simpa [Int.natAbs_pow, Int.natAbs_natCast] using this))
          exact (ne_of_lt hyx) hyx_eq
        have hm0 : m ≠ 0 := by
          intro hm
          have hy2o' : (y : ℤ) ^ 2 = -n ^ 2 := by simpa [hm] using hy2o
          have hy2le : (y : ℤ) ^ 2 ≤ 0 := by linarith [hy2o', sq_nonneg n]
          have hy2eq : (y : ℤ) ^ 2 = 0 := le_antisymm hy2le (sq_nonneg _)
          have : (y : ℤ) = 0 := (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hy2eq
          exact (ne_of_gt hy0) (by exact_mod_cast this)
        have hmulZ : m ^ 4 = n ^ 4 + ((x : ℤ) * y) ^ 2 := by
          have hfactor : (m ^ 2 + n ^ 2) * (m ^ 2 - n ^ 2) = m ^ 4 - n ^ 4 := by ring
          have : m ^ 4 - n ^ 4 = ((x : ℤ) * y) ^ 2 := by
            rw [← hfactor, ← hx2, ← hy2o]; ring
          linarith
        have hmul : m.natAbs ^ 4 = n.natAbs ^ 4 + (x * y) ^ 2 := by
          have hm4 := natAbs_pow_four m
          have hn4 := natAbs_pow_four n
          have hxy2 : ((x * y : ℕ) : ℤ) ^ 2 = ((x : ℤ) * y) ^ 2 := by
            push_cast; rfl
          have : (m.natAbs : ℤ) ^ 4 =
              (n.natAbs : ℤ) ^ 4 + ((x * y : ℕ) : ℤ) ^ 2 := by
            rw [hm4, hn4, hxy2, hmulZ]
          exact_mod_cast this
        have hlt : m.natAbs < x := by
          have hn2pos : (0 : ℤ) < n ^ 2 := sq_pos_of_ne_zero hn0
          have hm2 : (m.natAbs : ℤ) ^ 2 = m ^ 2 := Int.natAbs_sq m
          have : (m.natAbs : ℤ) ^ 2 < (x : ℤ) ^ 2 := by linarith [hx2, hm2, hn2pos]
          exact (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp
            (by exact_mod_cast this)
        have hy' : 0 < n.natAbs := Int.natAbs_pos.mpr hn0
        have hyx' : n.natAbs < m.natAbs := by
          have hy2pos : (0 : ℤ) < (y : ℤ) ^ 2 := by exact_mod_cast pow_pos hy0 2
          have hm2 : (m.natAbs : ℤ) ^ 2 = m ^ 2 := Int.natAbs_sq m
          have hn2 : (n.natAbs : ℤ) ^ 2 = n ^ 2 := Int.natAbs_sq n
          have : (n.natAbs : ℤ) ^ 2 < (m.natAbs : ℤ) ^ 2 := by
            linarith [hy2o, hm2, hn2, hy2pos]
          exact (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp
            (by exact_mod_cast this)
        have hzpos : 0 < x * y := Nat.mul_pos (Nat.zero_lt_of_lt hyx) hy0
        exact ih m.natAbs hlt ⟨hy', hyx', x * y, hzpos, hmul⟩
      · -- Even-leg
        obtain ⟨p, q, hp_odd, _, hre⟩ :
            ∃ p q : ℤ, p % 2 = 1 ∧ q % 2 = 0 ∧
              ((p = m ∧ q = n) ∨ (p = n ∧ q = m)) := by
          rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
          · exact ⟨n, m, hn, hm, Or.inr ⟨rfl, rfl⟩⟩
          · exact ⟨m, n, hm, hn, Or.inl ⟨rfl, rfl⟩⟩
        have hsum : p ^ 2 + q ^ 2 = (x : ℤ) ^ 2 := by
          rcases hre with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith [hx2]
        have hprod2 : 2 * p * q = (y : ℤ) ^ 2 := by
          rcases hre with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith [hy2e]
        have hcop_pq : Int.gcd p q = 1 := by
          rcases hre with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hmn
          · rwa [Int.gcd_comm]
        have htrip : PythagoreanTriple p q (x : ℤ) := by
          delta PythagoreanTriple; linarith [hsum]
        have hxpos : (0 : ℤ) < x := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hyx)
        obtain ⟨P, Q, hp_eq, hq_eq, hx_eq, hPQ, _, _⟩ :=
          htrip.coprime_classification' hcop_pq hp_odd hxpos
        have hy_even : Even y := by
          have h2 : (2 : ℤ) ∣ (y : ℤ) ^ 2 := ⟨p * q, by linarith [hprod2]⟩
          have : 2 ∣ y := Int.Prime.dvd_natAbs_of_coe_dvd_sq Nat.prime_two (y : ℤ) h2
          exact even_iff_two_dvd.2 this
        obtain ⟨t, ht⟩ := even_iff_exists_two_mul.mp hy_even
        have ht_eq : (t : ℤ) ^ 2 = P * Q * (P ^ 2 - Q ^ 2) := by
          have hy_div : (y : ℤ) ^ 2 = 4 * (P * Q * (P ^ 2 - Q ^ 2)) := by
            rw [← hprod2, hp_eq, hq_eq]; ring
          have h4 : (y : ℤ) ^ 2 = 4 * (t : ℤ) ^ 2 := by
            rw [ht]; push_cast; ring
          exact (mul_right_inj' (by decide : (4 : ℤ) ≠ 0)).mp (h4 ▸ hy_div)
        have hP0 : P ≠ 0 := by
          intro hP0
          have hy0' : (y : ℤ) ^ 2 = 0 := by
            simp [hP0, hq_eq] at hprod2; exact hprod2.symm
          have : y = 0 := by
            exact_mod_cast (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hy0'
          omega
        have hQ0 : Q ≠ 0 := by
          intro hQ0
          have hy0' : (y : ℤ) ^ 2 = 0 := by
            simp [hQ0, hq_eq] at hprod2; exact hprod2.symm
          have : y = 0 := by
            exact_mod_cast (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hy0'
          omega
        have hDiff0 : P ^ 2 - Q ^ 2 ≠ 0 := by
          intro hD
          have hp0 : p = 0 := by rw [hp_eq, hD]
          have : p % 2 = 0 := by simp [hp0]
          exact absurd this (by simp [hp_odd])
        have hcop_P_diff_nat : Nat.Coprime P.natAbs (P ^ 2 - Q ^ 2).natAbs := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          obtain ⟨r, hr, hrP, hrD⟩ := Nat.Prime.not_coprime_iff_dvd.mp (by
            simpa [Nat.coprime_iff_gcd_eq_one] using hne)
          have hrQ : r ∣ Q.natAbs := by
            have : (r : ℤ) ∣ Q ^ 2 := by
              have h1 : (r : ℤ) ∣ P ^ 2 :=
                dvd_pow (Int.natCast_dvd.mpr hrP) two_ne_zero
              have h2 : (r : ℤ) ∣ P ^ 2 - (P ^ 2 - Q ^ 2) :=
                dvd_sub h1 (Int.natCast_dvd.mpr hrD)
              simpa using h2
            exact hr.dvd_of_dvd_pow
              (by simpa [Int.natAbs_pow] using Int.natCast_dvd.mp this)
          exact hr.not_dvd_one (hPQ ▸ Nat.dvd_gcd hrP hrQ)
        have hcop_Q_diff_nat : Nat.Coprime Q.natAbs (P ^ 2 - Q ^ 2).natAbs := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          obtain ⟨r, hr, hrQ, hrD⟩ := Nat.Prime.not_coprime_iff_dvd.mp (by
            simpa [Nat.coprime_iff_gcd_eq_one] using hne)
          have hrP : r ∣ P.natAbs := by
            have hQ2 : (r : ℤ) ∣ Q ^ 2 :=
              dvd_pow (Int.natCast_dvd.mpr hrQ) two_ne_zero
            have hP2 : (r : ℤ) ∣ P ^ 2 := by
              have : (r : ℤ) ∣ (P ^ 2 - Q ^ 2) + Q ^ 2 :=
                dvd_add (Int.natCast_dvd.mpr hrD) hQ2
              simpa using this
            exact hr.dvd_of_dvd_pow
              (by simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hP2)
          exact hr.not_dvd_one (hPQ ▸ Nat.dvd_gcd hrP hrQ)
        have hcop_PQ_nat : Nat.Coprime P.natAbs Q.natAbs := by
          simpa [Int.gcd] using hPQ
        have hcop_mul :
            Nat.Coprime (P.natAbs * Q.natAbs) (P ^ 2 - Q ^ 2).natAbs :=
          Nat.Coprime.mul_left hcop_P_diff_nat hcop_Q_diff_nat
        have hprod_nat :
            P.natAbs * Q.natAbs * (P ^ 2 - Q ^ 2).natAbs = t ^ 2 := by
          have := congrArg Int.natAbs ht_eq
          simpa [Int.natAbs_mul, Int.natAbs_pow] using this.symm
        obtain ⟨s, hs⟩ :=
          nat_eq_pow_of_mul_eq_pow_of_coprime hcop_mul hprod_nat
        obtain ⟨T, hT⟩ :=
          nat_eq_pow_of_mul_eq_pow_of_coprime_right hcop_mul hprod_nat
        obtain ⟨R, hR⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime hcop_PQ_nat hs
        obtain ⟨S, hS⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime_right hcop_PQ_nat hs
        have hR0 : 0 < R := by
          have hPabs : 0 < P.natAbs := Int.natAbs_pos.mpr hP0
          rw [hR] at hPabs
          exact (Nat.pos_iff_ne_zero).2 fun hR0 => by simp [hR0] at hPabs
        have hS0 : 0 < S := by
          have hQabs : 0 < Q.natAbs := Int.natAbs_pos.mpr hQ0
          rw [hS] at hQabs
          exact (Nat.pos_iff_ne_zero).2 fun hS0 => by simp [hS0] at hQabs
        have hT0 : 0 < T := by
          have hDabs : 0 < (P ^ 2 - Q ^ 2).natAbs := Int.natAbs_pos.mpr hDiff0
          rw [hT] at hDabs
          exact (Nat.pos_iff_ne_zero).2 fun hT0 => by simp [hT0] at hDabs
        have hP2 : P ^ 2 = (R : ℤ) ^ 4 := by
          have : (P.natAbs : ℤ) ^ 2 = P ^ 2 := Int.natAbs_sq P
          rw [← this, hR]; push_cast; ring
        have hQ2 : Q ^ 2 = (S : ℤ) ^ 4 := by
          have : (Q.natAbs : ℤ) ^ 2 = Q ^ 2 := Int.natAbs_sq Q
          rw [← this, hS]; push_cast; ring
        have hD : P ^ 2 - Q ^ 2 = (T : ℤ) ^ 2 ∨
            P ^ 2 - Q ^ 2 = -((T : ℤ) ^ 2) := by
          have := (Int.natAbs_eq_iff).mp (by
            simpa [Int.natAbs_pow] using hT)
          simpa using this
        have hsmaller : DiffFourthSqPos (max R S) (min R S) := by
          rcases hD with hpos | hneg
          · have h1 : (R : ℤ) ^ 4 = (S : ℤ) ^ 4 + (T : ℤ) ^ 2 := by
              linarith [hP2, hQ2, hpos]
            have hRS : S < R := by
              have hTpos : (0 : ℤ) < (T : ℤ) ^ 2 :=
                sq_pos_of_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hT0))
              have : (S : ℤ) ^ 4 < (R : ℤ) ^ 4 := by linarith [h1, hTpos]
              exact (Nat.pow_lt_pow_iff_left (by decide : (4 : ℕ) ≠ 0)).mp
                (by exact_mod_cast this)
            rw [Nat.max_eq_left (le_of_lt hRS), Nat.min_eq_right (le_of_lt hRS)]
            exact ⟨hS0, hRS, T, hT0, by exact_mod_cast h1⟩
          · have h2 : (S : ℤ) ^ 4 = (R : ℤ) ^ 4 + (T : ℤ) ^ 2 := by
              linarith [hP2, hQ2, hneg]
            have hSR : R < S := by
              have hTpos : (0 : ℤ) < (T : ℤ) ^ 2 :=
                sq_pos_of_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hT0))
              have : (R : ℤ) ^ 4 < (S : ℤ) ^ 4 := by linarith [h2, hTpos]
              exact (Nat.pow_lt_pow_iff_left (by decide : (4 : ℕ) ≠ 0)).mp
                (by exact_mod_cast this)
            rw [Nat.max_eq_right (le_of_lt hSR), Nat.min_eq_left (le_of_lt hSR)]
            exact ⟨hR0, hSR, T, hT0, by exact_mod_cast h2⟩
        have hlt : max R S < x := by
          have hR_le : R ≤ R ^ 4 := Nat.le_self_pow (by decide : (4 : ℕ) ≠ 0) R
          have hS_le : S ≤ S ^ 4 := Nat.le_self_pow (by decide : (4 : ℕ) ≠ 0) S
          have hR4 : R ^ 4 = P.natAbs ^ 2 := by rw [hR]; ring
          have hS4 : S ^ 4 = Q.natAbs ^ 2 := by rw [hS]; ring
          have hxP : P.natAbs ^ 2 < x := by
            have : (P.natAbs : ℤ) ^ 2 < (x : ℤ) := by
              have hP2' : (P.natAbs : ℤ) ^ 2 = P ^ 2 := Int.natAbs_sq P
              linarith [hx_eq, hP2', sq_pos_of_ne_zero hQ0]
            exact_mod_cast this
          have hxQ : Q.natAbs ^ 2 < x := by
            have : (Q.natAbs : ℤ) ^ 2 < (x : ℤ) := by
              have hQ2' : (Q.natAbs : ℤ) ^ 2 = Q ^ 2 := Int.natAbs_sq Q
              linarith [hx_eq, hQ2', sq_pos_of_ne_zero hP0]
            exact_mod_cast this
          omega
        exact ih (max R S) hlt hsmaller
    · -- Non-coprime
      have hne : ¬ Nat.Coprime x y := hcop
      have hgt : 1 < Nat.gcd x y := by
        have hpos : 0 < Nat.gcd x y :=
          Nat.gcd_pos_of_pos_left _ (Nat.zero_lt_of_lt hyx)
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hpos)
          (Ne.symm (Nat.coprime_iff_gcd_eq_one.not.mp hne))
      obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
      have hp_x : p ∣ x := Nat.dvd_trans hdiv (Nat.gcd_dvd_left _ _)
      have hp_y : p ∣ y := Nat.dvd_trans hdiv (Nat.gcd_dvd_right _ _)
      obtain ⟨x1, rfl⟩ := hp_x
      obtain ⟨y1, rfl⟩ := hp_y
      have hp0 : 0 < p := hp.pos
      have hx1 : 0 < x1 := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hyx)
      have hy1 : 0 < y1 := Nat.pos_of_mul_pos_left hy0
      have hp4_z2 : (p : ℤ) ^ 4 ∣ (z : ℤ) ^ 2 := by
        have hZ : ((p * x1 : ℕ) : ℤ) ^ 4 =
            ((p * y1 : ℕ) : ℤ) ^ 4 + (z : ℤ) ^ 2 := by exact_mod_cast heq
        have hsub : (z : ℤ) ^ 2 =
            ((p * x1 : ℕ) : ℤ) ^ 4 - ((p * y1 : ℕ) : ℤ) ^ 4 := by linarith [hZ]
        have : (z : ℤ) ^ 2 =
            (p : ℤ) ^ 4 * ((x1 : ℤ) ^ 4 - (y1 : ℤ) ^ 4) := by
          convert hsub using 1; push_cast; ring
        exact ⟨(x1 : ℤ) ^ 4 - (y1 : ℤ) ^ 4, this⟩
      have hp2_zZ : (p : ℤ) ^ 2 ∣ (z : ℤ) := by
        have : ((p : ℤ) ^ 2) ^ 2 ∣ (z : ℤ) ^ 2 := by
          convert hp4_z2 using 1; ring
        exact (Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp this
      have hp2_z : p ^ 2 ∣ z := by
        simpa [Int.natCast_pow] using Int.natCast_dvd.mp hp2_zZ
      obtain ⟨z1, rfl⟩ := hp2_z
      have heq1 : x1 ^ 4 = y1 ^ 4 + z1 ^ 2 := by
        have hZ : ((p * x1 : ℕ) : ℤ) ^ 4 =
            ((p * y1 : ℕ) : ℤ) ^ 4 + ((p ^ 2 * z1 : ℕ) : ℤ) ^ 2 := by
          exact_mod_cast heq
        have h' : (p : ℤ) ^ 4 * (x1 : ℤ) ^ 4 =
            (p : ℤ) ^ 4 * ((y1 : ℤ) ^ 4 + (z1 : ℤ) ^ 2) := by
          convert hZ using 1 <;> push_cast <;> ring
        have hne4 : (p : ℤ) ^ 4 ≠ 0 := pow_ne_zero 4 (Nat.cast_ne_zero.mpr (ne_of_gt hp0))
        have := (mul_right_inj' hne4).mp h'
        exact_mod_cast this
      have hz1pos : 0 < z1 := Nat.pos_of_mul_pos_left hz0
      have hy1x1 : y1 < x1 := Nat.lt_of_mul_lt_mul_left (a := p) hyx
      have hlt : x1 < p * x1 := lt_mul_of_one_lt_left hx1 hp.one_lt
      exact ih x1 hlt ⟨hy1, hy1x1, z1, hz1pos, heq1⟩

theorem not_pow_four_sub_pow_four_eq_sq {x y z : ℤ}
    (_hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  intro h
  have hx4 := natAbs_pow_four x
  have hy4 := natAbs_pow_four y
  have hz2 : (z.natAbs : ℤ) ^ 2 = z ^ 2 := Int.natAbs_sq z
  have heq : x.natAbs ^ 4 = y.natAbs ^ 4 + z.natAbs ^ 2 := by
    have : (x.natAbs : ℤ) ^ 4 = (y.natAbs : ℤ) ^ 4 + (z.natAbs : ℤ) ^ 2 := by
      rw [hx4, hy4, hz2]; linarith [h]
    exact_mod_cast this
  have hyx : y.natAbs < x.natAbs := by
    have hzpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
    have : y.natAbs ^ 4 < x.natAbs ^ 4 := by
      have hpos : 0 < z.natAbs ^ 2 := Nat.pow_pos hzpos
      omega
    exact (Nat.pow_lt_pow_iff_left (by decide : (4 : ℕ) ≠ 0)).mp this
  exact not_diffFourthSqPos
    ⟨Int.natAbs_pos.mpr hy, hyx, z.natAbs, Int.natAbs_pos.mpr hz, heq⟩

theorem not_pow_four_add_sq_eq_pow_four {a b c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 4 + b ^ 2 ≠ c ^ 4 := by
  intro h
  by_cases hc : c = 0
  · subst hc
    have h1 : (0 : ℤ) ≤ a ^ 4 := Even.pow_nonneg (by decide : Even 4) a
    have h2 : (0 : ℤ) < b ^ 2 := sq_pos_of_ne_zero hb
    have : a ^ 4 + b ^ 2 = 0 := by simpa using h
    linarith
  · exact not_pow_four_sub_pow_four_eq_sq hc ha hb (by linarith [h])

/-! ### Beal `d = 2` fourth-divisibility slices -/

theorem not_beal_sol_of_expGcd_eq_two_of_four_dvd_xz {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (_hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (hx4 : 4 ∣ x) (hz4 : 4 ∣ z) :
    ¬ A ^ x + B ^ y = C ^ z := by
  intro hsol
  obtain ⟨_, _, _, hsq⟩ := beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol
  have hx_eq : x / 2 = 2 * (x / 4) := by omega
  have hz_eq : z / 2 = 2 * (z / 4) := by omega
  have hA4 : A ^ (x / 2) = (A ^ (x / 4)) ^ 2 := by rw [hx_eq, mul_comm, pow_mul]
  have hC4 : C ^ (z / 2) = (C ^ (z / 4)) ^ 2 := by rw [hz_eq, mul_comm, pow_mul]
  have hform : (A ^ (x / 4)) ^ 4 + (B ^ (y / 2)) ^ 2 = (C ^ (z / 4)) ^ 4 := by
    have hA' : (A ^ (x / 2)) ^ 2 = (A ^ (x / 4)) ^ 4 := by rw [hA4, ← pow_mul]
    have hC' : (C ^ (z / 2)) ^ 2 = (C ^ (z / 4)) ^ 4 := by rw [hC4, ← pow_mul]
    calc (A ^ (x / 4)) ^ 4 + (B ^ (y / 2)) ^ 2
        = (A ^ (x / 2)) ^ 2 + (B ^ (y / 2)) ^ 2 := by rw [← hA']
      _ = (C ^ (z / 2)) ^ 2 := hsq
      _ = (C ^ (z / 4)) ^ 4 := hC'
  exact not_pow_four_add_sq_eq_pow_four (pow_ne_zero _ hA) (pow_ne_zero _ hB) hform

theorem not_beal_sol_of_expGcd_eq_two_of_four_dvd_yz {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (hy4 : 4 ∣ y) (hz4 : 4 ∣ z) :
    ¬ A ^ x + B ^ y = C ^ z := by
  intro hsol
  have hd' : bealExpGcd y x z = 2 := by
    simp only [bealExpGcd] at hd ⊢
    convert hd using 1
    ac_rfl
  exact not_beal_sol_of_expGcd_eq_two_of_four_dvd_xz hy hx hz hB hA hC hd' hy4 hz4
    (by linarith [hsol])

private theorem not_beal_sol_of_expGcd_eq_two_of_four_dvd_xy' {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (_hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (hx4 : 4 ∣ x) (hy4 : 4 ∣ y) :
    ¬ A ^ x + B ^ y = C ^ z := by
  intro hsol
  obtain ⟨_, _, _, hsq⟩ := beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol
  have hx_eq : x / 2 = 2 * (x / 4) := by omega
  have hy_eq : y / 2 = 2 * (y / 4) := by omega
  have hA4 : A ^ (x / 2) = (A ^ (x / 4)) ^ 2 := by rw [hx_eq, mul_comm, pow_mul]
  have hB4 : B ^ (y / 2) = (B ^ (y / 4)) ^ 2 := by rw [hy_eq, mul_comm, pow_mul]
  have hform : (A ^ (x / 4)) ^ 4 + (B ^ (y / 4)) ^ 4 = (C ^ (z / 2)) ^ 2 := by
    have hA' : (A ^ (x / 2)) ^ 2 = (A ^ (x / 4)) ^ 4 := by rw [hA4, ← pow_mul]
    have hB' : (B ^ (y / 2)) ^ 2 = (B ^ (y / 4)) ^ 4 := by rw [hB4, ← pow_mul]
    rw [← hA', ← hB', hsq]
  exact not_fermat_42 (pow_ne_zero _ hA) (pow_ne_zero _ hB) hform

theorem not_beal_sol_of_expGcd_eq_two_of_two_four_dvd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (h4 : (4 ∣ x ∧ 4 ∣ y) ∨ (4 ∣ x ∧ 4 ∣ z) ∨ (4 ∣ y ∧ 4 ∣ z)) :
    ¬ A ^ x + B ^ y = C ^ z := by
  rcases h4 with hxy | hxz | hyz
  · exact not_beal_sol_of_expGcd_eq_two_of_four_dvd_xy' hx hy hz hA hB hC hd hxy.1 hxy.2
  · exact not_beal_sol_of_expGcd_eq_two_of_four_dvd_xz hx hy hz hA hB hC hd hxz.1 hxz.2
  · exact not_beal_sol_of_expGcd_eq_two_of_four_dvd_yz hx hy hz hA hB hC hd hyz.1 hyz.2

/-! ### Residual type for remaining `d = 2` -/

/--
**Residual** (phase 7h, unproved): no three-way-coprime Beal solution with
`bealExpGcd = 2` outside the fourth-divisibility slices already closed.
-/
def BealPythagoreanResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 2 →
    ¬ (4 ∣ x ∧ 4 ∣ y) →
    ¬ (4 ∣ x ∧ 4 ∣ z) →
    ¬ (4 ∣ y ∧ 4 ∣ z) →
      ¬ A ^ x + B ^ y = C ^ z

theorem beal_pythagorean_residual_iff_two_odd_reduced {x y z : ℕ}
    (hd : bealExpGcd x y z = 2) :
    (¬ (4 ∣ x ∧ 4 ∣ y) ∧ ¬ (4 ∣ x ∧ 4 ∣ z) ∧ ¬ (4 ∣ y ∧ 4 ∣ z)) ↔
      (Odd (x / 2) ∧ Odd (y / 2)) ∨
        (Odd (x / 2) ∧ Odd (z / 2)) ∨
          (Odd (y / 2) ∧ Odd (z / 2)) := by
  obtain ⟨hx2, hy2, hz2⟩ := bealExpGcd_eq_two_dvd hd
  have h4x := four_dvd_iff_even_div_two hx2
  have h4y := four_dvd_iff_even_div_two hy2
  have h4z := four_dvd_iff_even_div_two hz2
  constructor
  · intro ⟨hxy, hxz, hyz⟩
    have hx' : ¬ Even (x / 2) ∨ ¬ Even (y / 2) := by
      have := mt (fun h : Even (x / 2) ∧ Even (y / 2) =>
        And.intro (h4x.mpr h.1) (h4y.mpr h.2)) hxy
      tauto
    have hx'' : ¬ Even (x / 2) ∨ ¬ Even (z / 2) := by
      have := mt (fun h : Even (x / 2) ∧ Even (z / 2) =>
        And.intro (h4x.mpr h.1) (h4z.mpr h.2)) hxz
      tauto
    have hy'' : ¬ Even (y / 2) ∨ ¬ Even (z / 2) := by
      have := mt (fun h : Even (y / 2) ∧ Even (z / 2) =>
        And.intro (h4y.mpr h.1) (h4z.mpr h.2)) hyz
      tauto
    simp only [← Nat.not_even_iff_odd] at hx' hx'' hy'' ⊢
    rcases hx' with hx_odd | hy_odd
    · rcases hx'' with _ | hz_odd
      · rcases hy'' with hy_odd | hz_odd
        · exact Or.inl ⟨hx_odd, hy_odd⟩
        · exact Or.inr (Or.inl ⟨hx_odd, hz_odd⟩)
      · exact Or.inr (Or.inl ⟨hx_odd, hz_odd⟩)
    · rcases hy'' with _ | hz_odd
      · rcases hx'' with hx_odd | hz_odd
        · exact Or.inl ⟨hx_odd, hy_odd⟩
        · exact Or.inr (Or.inr ⟨hy_odd, hz_odd⟩)
      · exact Or.inr (Or.inr ⟨hy_odd, hz_odd⟩)
  · intro h
    rw [h4x, h4y, h4z]
    rcases h with ⟨hx_odd, hy_odd⟩ | ⟨hx_odd, hz_odd⟩ | ⟨hy_odd, hz_odd⟩
    · exact ⟨fun ⟨_, b⟩ => Nat.not_even_iff_odd.mpr hy_odd b,
        fun ⟨a, _⟩ => Nat.not_even_iff_odd.mpr hx_odd a,
        fun ⟨a, _⟩ => Nat.not_even_iff_odd.mpr hy_odd a⟩
    · exact ⟨fun ⟨a, _⟩ => Nat.not_even_iff_odd.mpr hx_odd a,
        fun ⟨_, b⟩ => Nat.not_even_iff_odd.mpr hz_odd b,
        fun ⟨_, b⟩ => Nat.not_even_iff_odd.mpr hz_odd b⟩
    · exact ⟨fun ⟨_, b⟩ => Nat.not_even_iff_odd.mpr hy_odd b,
        fun ⟨_, b⟩ => Nat.not_even_iff_odd.mpr hz_odd b,
        fun ⟨a, _⟩ => Nat.not_even_iff_odd.mpr hy_odd a⟩

end Theorems

end DstDiophantine
