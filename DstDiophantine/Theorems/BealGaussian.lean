import DstDiophantine.Theorems.Beal
import DstDiophantine.Theorems.BealPythagorean
import DstDiophantine.Theorems.FermatLast
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Phase 7i: Gaussian-integer UFD descent for Beal

Tools for the `d = 2` / even two-equal `d = 1` programme, plus assembly of
positive classical Beal from the two residuals under the FLT axiom.

Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

open GaussianInt
open Zsqrtd (re_mul im_mul star_mk)

local notation "ℤ[i]" => GaussianInt

/-! ### Divisibility by `1+i` -/

private theorem mul_one_add_I (x y : ℤ) :
    (⟨1, 1⟩ * ⟨x, y⟩ : ℤ[i]) = ⟨x - y, x + y⟩ := by
  ext <;> simp [re_mul, im_mul] <;> ring

theorem one_add_I_dvd_iff {m n : ℤ} :
    (⟨1, 1⟩ : ℤ[i]) ∣ ⟨m, n⟩ ↔ m % 2 = n % 2 := by
  constructor
  · rintro ⟨⟨x, y⟩, h⟩
    have hxy := mul_one_add_I x y
    rw [hxy] at h
    have hre : m = x - y := (Zsqrtd.ext_iff.mp h).1
    have him : n = x + y := (Zsqrtd.ext_iff.mp h).2
    have hsum : m + n = 2 * x := by linarith [hre, him]
    have : (m + n) % 2 = 0 := by
      rw [hsum]; exact Int.mul_emod_right _ _
    have := Int.add_emod m n
    omega
  · intro _
    have hsum_even : Even (m + n) := by
      refine Int.even_iff.mpr ?_
      have := Int.add_emod m n
      omega
    have hdiff_even : Even (n - m) := by
      refine Int.even_iff.mpr ?_
      have := Int.sub_emod n m
      omega
    obtain ⟨x, hx⟩ := even_iff_exists_two_mul.mp hsum_even
    obtain ⟨y, hy⟩ := even_iff_exists_two_mul.mp hdiff_even
    refine ⟨⟨x, y⟩, ?_⟩
    rw [mul_one_add_I]
    ext
    · exact (by linarith [hx, hy] : m = x - y)
    · exact (by linarith [hx, hy] : n = x + y)

theorem not_one_add_I_dvd_of_opposite_parity {m n : ℤ}
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    ¬ (⟨1, 1⟩ : ℤ[i]) ∣ ⟨m, n⟩ := by
  rw [one_add_I_dvd_iff]
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · have : m % 2 = 0 := Int.even_iff.mp hm
    have : n % 2 = 1 := Int.odd_iff.mp hn
    omega
  · have : m % 2 = 1 := Int.odd_iff.mp hm
    have : n % 2 = 0 := Int.even_iff.mp hn
    omega

theorem isUnit_I : IsUnit (⟨0, 1⟩ : ℤ[i]) :=
  isUnit_iff_exists_inv.mpr ⟨⟨0, -1⟩, by ext <;> simp [re_mul, im_mul]⟩

theorem two_eq_neg_I_mul_one_add_I_sq :
    (2 : ℤ[i]) = -(⟨0, 1⟩ : ℤ[i]) * (⟨1, 1⟩ : ℤ[i]) ^ 2 := by
  ext <;> simp [pow_two, re_mul, im_mul]

theorem one_add_I_dvd_two : (⟨1, 1⟩ : ℤ[i]) ∣ (2 : ℤ[i]) := by
  refine ⟨-(⟨0, 1⟩ : ℤ[i]) * ⟨1, 1⟩, ?_⟩
  calc (-(⟨0, 1⟩ : ℤ[i]) * ⟨1, 1⟩) * ⟨1, 1⟩
      = -(⟨0, 1⟩ : ℤ[i]) * (⟨1, 1⟩ : ℤ[i]) ^ 2 := by ring
    _ = 2 := two_eq_neg_I_mul_one_add_I_sq.symm

/-! ### Coprimality to the conjugate -/

private theorem mk_add_star (m n : ℤ) :
    (⟨m, n⟩ : ℤ[i]) + star (⟨m, n⟩ : ℤ[i]) = (2 * m : ℤ[i]) :=
  calc (⟨m, n⟩ : ℤ[i]) + star ⟨m, n⟩
      = (⟨m, n⟩ : ℤ[i]) + ⟨m, -n⟩ := by rw [star_mk]
    _ = ⟨m + m, n + -n⟩ := rfl
    _ = ⟨2 * m, 0⟩ := by simp [two_mul]
    _ = (2 * m : ℤ[i]) := by
        ext <;> simp [re_mul, im_mul]

private theorem mk_sub_star (m n : ℤ) :
    (⟨m, n⟩ : ℤ[i]) - star (⟨m, n⟩ : ℤ[i]) =
      (2 * n : ℤ[i]) * (⟨0, 1⟩ : ℤ[i]) :=
  calc (⟨m, n⟩ : ℤ[i]) - star ⟨m, n⟩
      = (⟨m, n⟩ : ℤ[i]) - ⟨m, -n⟩ := by rw [star_mk]
    _ = ⟨m - m, n - -n⟩ := rfl
    _ = ⟨0, 2 * n⟩ := by simp [two_mul]
    _ = (2 * n : ℤ[i]) * ⟨0, 1⟩ := by
        ext <;> simp [re_mul, im_mul]

private theorem dvd_two_of_dvd_two_mul_coprime {δ : ℤ[i]} {m n : ℤ}
    (hcop : Int.gcd m n = 1)
    (hm : δ ∣ (2 * m : ℤ[i])) (hn : δ ∣ (2 * n : ℤ[i])) :
    δ ∣ (2 : ℤ[i]) := by
  obtain ⟨a, b, hab⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have h2 : (2 : ℤ[i]) =
      (a : ℤ[i]) * (2 * m : ℤ[i]) + (b : ℤ[i]) * (2 * n : ℤ[i]) := by
    have : (2 : ℤ) = a * (2 * m) + b * (2 * n) := by
      linarith [show (a * m + b * n : ℤ) = 1 from hab]
    exact_mod_cast this
  exact h2 ▸ dvd_add (hm.mul_left _) (hn.mul_left _)

private theorem associated_one_add_I_of_norm_eq_two {π : ℤ[i]}
    (h : Zsqrtd.norm π = 2) :
    Associated (⟨1, 1⟩ : ℤ[i]) π := by
  have hnorm : π.re ^ 2 + π.im ^ 2 = 2 := by simpa [Zsqrtd.norm, sq] using h
  have hre_le : π.re.natAbs ≤ 1 := by
    by_contra hgt
    have h2 : 2 ≤ π.re.natAbs := Nat.not_le.mp hgt
    have h4 : 4 ≤ π.re.natAbs ^ 2 := Nat.pow_le_pow_left h2 2
    have : (4 : ℤ) ≤ π.re ^ 2 + π.im ^ 2 := by
      have hre2 : π.re ^ 2 = (π.re.natAbs : ℤ) ^ 2 := (Int.natAbs_sq π.re).symm
      have : (4 : ℤ) ≤ (π.re.natAbs : ℤ) ^ 2 := by exact_mod_cast h4
      linarith [sq_nonneg π.im]
    linarith
  have him_le : π.im.natAbs ≤ 1 := by
    by_contra hgt
    have h2 : 2 ≤ π.im.natAbs := Nat.not_le.mp hgt
    have h4 : 4 ≤ π.im.natAbs ^ 2 := Nat.pow_le_pow_left h2 2
    have : (4 : ℤ) ≤ π.re ^ 2 + π.im ^ 2 := by
      have him2 : π.im ^ 2 = (π.im.natAbs : ℤ) ^ 2 := (Int.natAbs_sq π.im).symm
      have : (4 : ℤ) ≤ (π.im.natAbs : ℤ) ^ 2 := by exact_mod_cast h4
      linarith [sq_nonneg π.re]
    linarith
  have hre0 : π.re.natAbs ≠ 0 := by
    intro h0
    have hr0 : π.re = 0 := Int.natAbs_eq_zero.mp h0
    have : (π.im.natAbs : ℤ) ^ 2 = 2 := by
      have him2 : π.im ^ 2 = 2 := by simpa [hr0] using hnorm
      have := Int.natAbs_sq π.im; linarith
    interval_cases π.im.natAbs <;> norm_num at this
  have him0 : π.im.natAbs ≠ 0 := by
    intro h0
    have hi0 : π.im = 0 := Int.natAbs_eq_zero.mp h0
    have : (π.re.natAbs : ℤ) ^ 2 = 2 := by
      have hr2 : π.re ^ 2 = 2 := by simpa [hi0] using hnorm
      have := Int.natAbs_sq π.re; linarith
    interval_cases π.re.natAbs <;> norm_num at this
  have hre : π.re.natAbs = 1 := by omega
  have him : π.im.natAbs = 1 := by omega
  have hre' : π.re = 1 ∨ π.re = -1 := Int.natAbs_eq_iff.mp hre
  have him' : π.im = 1 ∨ π.im = -1 := Int.natAbs_eq_iff.mp him
  rcases hre' with hr | hr <;> rcases him' with hi | hi
  · exact ⟨1, by ext <;> simp [hr, hi]⟩
  · refine ⟨⟨⟨0, -1⟩, ⟨0, 1⟩, by ext <;> simp [re_mul, im_mul],
        by ext <;> simp [re_mul, im_mul]⟩, ?_⟩
    ext <;> simp [hr, hi, re_mul, im_mul]
  · refine ⟨⟨⟨0, 1⟩, ⟨0, -1⟩, by ext <;> simp [re_mul, im_mul],
        by ext <;> simp [re_mul, im_mul]⟩, ?_⟩
    ext <;> simp [hr, hi, re_mul, im_mul]
  · exact ⟨-1, by ext <;> simp [hr, hi]⟩

private theorem one_add_I_dvd_of_dvd_two_of_not_unit {δ : ℤ[i]}
    (hδ : δ ∣ (2 : ℤ[i])) (h0 : δ ≠ 0) (hu : ¬ IsUnit δ) :
    (⟨1, 1⟩ : ℤ[i]) ∣ δ := by
  obtain ⟨t, ht⟩ := hδ
  have hn : Zsqrtd.norm δ * Zsqrtd.norm t = 4 := by
    have h := congrArg Zsqrtd.norm ht
    rw [Zsqrtd.norm_mul] at h
    simpa [Zsqrtd.norm] using h.symm
  have hnn : 0 < Zsqrtd.norm δ := (GaussianInt.norm_pos).mpr h0
  have hne1 : Zsqrtd.norm δ ≠ 1 := by
    intro h1
    exact hu ((Zsqrtd.norm_eq_one_iff' (by simp) _).mp h1)
  have hN : (Zsqrtd.norm δ).natAbs * (Zsqrtd.norm t).natAbs = 4 := by
    have := congrArg Int.natAbs hn
    rw [Int.natAbs_mul] at this
    simpa [Int.natAbs_of_nonneg (GaussianInt.norm_nonneg δ),
      Int.natAbs_of_nonneg (GaussianInt.norm_nonneg t)] using this
  have hAbs : (Zsqrtd.norm δ).natAbs = 2 ∨ (Zsqrtd.norm δ).natAbs = 4 := by
    have hdiv4 : (Zsqrtd.norm δ).natAbs ∣ 4 := ⟨(Zsqrtd.norm t).natAbs, hN.symm⟩
    have hposN : 0 < (Zsqrtd.norm δ).natAbs := Int.natAbs_pos.mpr hnn.ne'
    have hle : (Zsqrtd.norm δ).natAbs ≤ 4 := Nat.le_of_dvd (by decide) hdiv4
    have hcases :
        (Zsqrtd.norm δ).natAbs = 1 ∨ (Zsqrtd.norm δ).natAbs = 2 ∨
          (Zsqrtd.norm δ).natAbs = 3 ∨ (Zsqrtd.norm δ).natAbs = 4 := by omega
    rcases hcases with h1 | h2 | h3 | h4
    · have : Zsqrtd.norm δ = 1 := by
        have := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg δ)
        omega
      exact absurd this hne1
    · exact Or.inl h2
    · exact absurd (h3 ▸ hdiv4) (by decide : ¬(3 ∣ 4))
    · exact Or.inr h4
  have hdiv : Zsqrtd.norm δ = 2 ∨ Zsqrtd.norm δ = 4 := by
    have := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg δ)
    rcases hAbs with h | h
    · left; omega
    · right; omega
  rcases hdiv with h2 | h4
  · exact (associated_one_add_I_of_norm_eq_two h2).dvd
  · have ht_unit : IsUnit t := by
      have : Zsqrtd.norm t = 1 := by
        have ht0 : 0 ≤ Zsqrtd.norm t := GaussianInt.norm_nonneg t
        nlinarith [ht0, hn, h4]
      exact (Zsqrtd.norm_eq_one_iff' (by simp) _).mp this
    obtain ⟨u, rfl⟩ := ht_unit
    have : (⟨1, 1⟩ : ℤ[i]) ∣ δ * (u : ℤ[i]) := by
      rw [← ht]; exact one_add_I_dvd_two
    exact (u.isUnit.dvd_mul_right).mp this

theorem isCoprime_mk_star_of_coprime_opposite_parity {m n : ℤ}
    (hcop : Int.gcd m n = 1)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    IsCoprime (⟨m, n⟩ : ℤ[i]) (star (⟨m, n⟩ : ℤ[i])) := by
  classical
  let z : ℤ[i] := ⟨m, n⟩
  let d := EuclideanDomain.gcd z (star z)
  have hd_dvd_z : d ∣ z := EuclideanDomain.gcd_dvd_left _ _
  have hd_dvd_s : d ∣ star z := EuclideanDomain.gcd_dvd_right _ _
  have h2m : d ∣ (2 * m : ℤ[i]) := by
    have := dvd_add hd_dvd_z hd_dvd_s
    rwa [mk_add_star] at this
  have h2n : d ∣ (2 * n : ℤ[i]) := by
    have h := dvd_sub hd_dvd_z hd_dvd_s
    rw [mk_sub_star] at h
    exact isUnit_I.dvd_mul_right.mp h
  have h2 : d ∣ (2 : ℤ[i]) := dvd_two_of_dvd_two_mul_coprime hcop h2m h2n
  have hunit : IsUnit d := by
    by_contra hu
    by_cases h0 : d = 0
    · have hz0 : z = 0 := (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
      have hm0 : m = 0 := by simpa [z] using (Zsqrtd.ext_iff.mp hz0).1
      have hn0 : n = 0 := by simpa [z] using (Zsqrtd.ext_iff.mp hz0).2
      have : Int.gcd m n = 0 := by simp [hm0, hn0]
      omega
    · have h1i : (⟨1, 1⟩ : ℤ[i]) ∣ d :=
        one_add_I_dvd_of_dvd_two_of_not_unit h2 h0 hu
      exact not_one_add_I_dvd_of_opposite_parity hpar (h1i.trans hd_dvd_z)
  exact EuclideanDomain.gcd_isUnit_iff.mp hunit

/-! ### Hypotenuse power via UFD -/

theorem exists_associated_pow_of_hyp_eq_pow {m n c : ℤ} {e : ℕ}
    (_he : 0 < e)
    (hcop : Int.gcd m n = 1)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = c ^ e) :
    ∃ g : ℤ[i], Associated (g ^ e) (⟨m, n⟩ : ℤ[i]) := by
  have hprod : (⟨m, n⟩ : ℤ[i]) * star (⟨m, n⟩ : ℤ[i]) = (c : ℤ[i]) ^ e := by
    have hn : Zsqrtd.norm (⟨m, n⟩ : ℤ[i]) = m ^ 2 + n ^ 2 := by
      simp [Zsqrtd.norm, sq]
    have hnorm := Zsqrtd.norm_eq_mul_conj (⟨m, n⟩ : ℤ[i])
    rw [← hnorm, hn, heq]
    simp
  exact exists_associated_pow_of_mul_eq_pow'
    (isCoprime_mk_star_of_coprime_opposite_parity hcop hpar) hprod

theorem isGaussianHypotenusePower_of_hyp_eq_pow {m n c : ℤ} {e : ℕ}
    (he : 0 < e)
    (hcop : Int.gcd m n = 1)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = c ^ e) :
    IsGaussianHypotenusePower m n e := by
  obtain ⟨g, ⟨u, hu⟩⟩ := exists_associated_pow_of_hyp_eq_pow he hcop hpar heq
  refine ⟨g, ?_⟩
  have hmn : (⟨m, n⟩ : ℤ[i]) = g ^ e * u := hu.symm
  have hnu : Zsqrtd.norm (u : ℤ[i]) = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by simp : (-1 : ℤ) ≤ 0) _).mpr u.isUnit
  have := congrArg Zsqrtd.norm hmn
  rw [Zsqrtd.norm_mul, hnu, mul_one] at this
  simpa [Zsqrtd.norm, sq] using this.symm

/-! ### Assembly (FLT axiom + residuals) -/

/--
Phase 7i assembly: under the FLT axiom, positive classical Beal follows from the
two residuals `BealMixedExpResidual` and `BealPythagoreanResidual`.
-/
theorem beal_conjecture_pos_of_residuals
    (hMix : BealMixedExpResidual)
    (hPyth : BealPythagoreanResidual) :
    ∀ {A B C : ℤ} {x y z : ℕ},
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by
  intro A B C x y z hx hy hz hA hB hC hsol
  by_contra hnot
  have hcop : bealGcd A B C = 1 := bealGcd_eq_one_of_not_gt hA.ne' hnot
  rcases bealExpGcd_eq_one_or_eq_two_or_ge_three hx with hd1 | hd2 | hd3
  · exact hMix A B C x y z hx hy hz hA.ne' hB.ne' hC.ne' hcop hd1 hsol
  · by_cases hxy : 4 ∣ x ∧ 4 ∣ y
    · exact not_beal_sol_of_expGcd_eq_two_of_two_four_dvd
        hx hy hz hA.ne' hB.ne' hC.ne' hd2 (Or.inl hxy) hsol
    · by_cases hxz : 4 ∣ x ∧ 4 ∣ z
      · exact not_beal_sol_of_expGcd_eq_two_of_two_four_dvd
          hx hy hz hA.ne' hB.ne' hC.ne' hd2 (Or.inr (Or.inl hxz)) hsol
      · by_cases hyz : 4 ∣ y ∧ 4 ∣ z
        · exact not_beal_sol_of_expGcd_eq_two_of_two_four_dvd
            hx hy hz hA.ne' hB.ne' hC.ne' hd2 (Or.inr (Or.inr hyz)) hsol
        · exact hPyth A B C x y z hx hy hz hA.ne' hB.ne' hC.ne' hcop hd2
            hxy hxz hyz hsol
  · exact not_beal_sol_of_expGcd_ge_three hA.ne' hB.ne' hC.ne' hd3 hsol

/-! ### `d = 2` equal-odd reduced exponents -/

private theorem hyp_natAbs_pow_of_classification {m n C : ℤ} {e : ℕ}
    (hhyp : C ^ e = m ^ 2 + n ^ 2 ∨ C ^ e = -(m ^ 2 + n ^ 2)) :
    m ^ 2 + n ^ 2 = (C.natAbs : ℤ) ^ e := by
  have hnn : 0 ≤ m ^ 2 + n ^ 2 := by positivity
  have hAbs : (C ^ e).natAbs = C.natAbs ^ e := Int.natAbs_pow _ _
  have hkey : (C ^ e).natAbs = (m ^ 2 + n ^ 2).natAbs := by
    rcases hhyp with h | h
    · rw [h]
    · rw [h, Int.natAbs_neg]
  calc m ^ 2 + n ^ 2
      = ↑(m ^ 2 + n ^ 2).natAbs := (Int.natAbs_of_nonneg hnn).symm
    _ = ↑(C ^ e).natAbs := by rw [hkey]
    _ = ↑(C.natAbs ^ e) := by rw [hAbs]
    _ = (C.natAbs : ℤ) ^ e := by norm_cast

private theorem parity_of_emod {m n : ℤ}
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    (Even m ∧ Odd n) ∨ (Odd m ∧ Even n) := by
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · exact Or.inl ⟨Int.even_iff.mpr hm, Int.odd_iff.mpr hn⟩
  · exact Or.inr ⟨Int.odd_iff.mpr hm, Int.even_iff.mpr hn⟩

private theorem odd_div_two_ge_three {n : ℕ}
    (_h2 : 2 ∣ n) (_h3 : 3 ≤ n) (hodd : Odd (n / 2)) : 3 ≤ n / 2 := by
  have : n / 2 ≠ 2 := by
    intro h; exact Nat.not_even_iff_odd.mpr hodd (by simp [h])
  omega

/--
If both legs of a primitive sum of squares are pure `e`-th powers (`e ≥ 3`),
the FLT axiom forbids the hypotenuse from also being an `e`-th power.
-/
theorem not_hyp_pow_of_both_legs_pow {u v c : ℤ} {e : ℕ}
    (he : 3 ≤ e) (hu : u ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0)
    (heq : (u ^ e) ^ 2 + (v ^ e) ^ 2 = c ^ e) : False := by
  have hFLT : FermatLastTheoremFor e := fermatLastTheorem e he
  have hInt : FermatLastTheoremWith ℤ e := (fermatLastTheoremFor_iff_int).mp hFLT
  have hform : (u ^ 2) ^ e + (v ^ 2) ^ e = c ^ e := by
    calc (u ^ 2) ^ e + (v ^ 2) ^ e
        = u ^ (2 * e) + v ^ (2 * e) := by simp [← pow_mul]
      _ = (u ^ e) ^ 2 + (v ^ e) ^ 2 := by simp [pow_mul, mul_comm]
      _ = c ^ e := heq
  exact hInt (u ^ 2) (v ^ 2) c (pow_ne_zero 2 hu) (pow_ne_zero 2 hv) hc hform

theorem exists_natAbs_pow_of_two_mul_eq_pow {m n K : ℤ} {e : ℕ}
    (hcop : Int.gcd m n = 1)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : 2 * m * n = K ^ e) (_he : 0 < e) :
    (Even m.natAbs ∧ (∃ u v : ℕ, n.natAbs = u ^ e ∧ 2 * m.natAbs = v ^ e)) ∨
      (Even n.natAbs ∧ (∃ u v : ℕ, m.natAbs = u ^ e ∧ 2 * n.natAbs = v ^ e)) := by
  have hcopN : Nat.Coprime m.natAbs n.natAbs := by
    simpa [Int.gcd] using hcop
  have hparN : (Even m.natAbs ∧ Odd n.natAbs) ∨ (Odd m.natAbs ∧ Even n.natAbs) := by
    rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
    · exact Or.inl ⟨Int.natAbs_even.mpr hm, Int.natAbs_odd.mpr hn⟩
    · exact Or.inr ⟨Int.natAbs_odd.mpr hm, Int.natAbs_even.mpr hn⟩
  have heqN : 2 * m.natAbs * n.natAbs = K.natAbs ^ e := by
    have := congrArg Int.natAbs heq
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  exact exists_pow_of_two_mul_coprime_eq_pow hcopN hparN heqN

/--
`d = 2` with `y = z` and odd reduced exponent: Pythagorean parameters yield a
Gaussian hypotenuse `e`-th power (`e = y/2`), as a unit times an `e`-th power.
-/
theorem exists_gaussian_hyp_pow_of_expGcd_eq_two_of_eq_odd_yz
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hyz : y = z)
    (_hodd : Odd (y / 2))
    (hsol : A ^ x + B ^ y = C ^ z) :
    ∃ m n : ℤ,
      Int.gcd m n = 1 ∧
        ((Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) ∧
          IsGaussianHypotenusePower m n (y / 2) ∧
            ∃ g : ℤ[i], Associated (g ^ (y / 2)) (⟨m, n⟩ : ℤ[i]) := by
  obtain ⟨m, n, _hleg, hhyp, hmn, hpar⟩ :=
    beal_pythagorean_classification_of_expGcd_eq_two hx hy hz hA hB hC hgcd hd hsol
  have he : 0 < y / 2 := by
    have := (beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol).2.1
    omega
  have hpar' := parity_of_emod hpar
  have hhyp' : C ^ (y / 2) = m ^ 2 + n ^ 2 ∨ C ^ (y / 2) = -(m ^ 2 + n ^ 2) := by
    simpa [hyz, show z / 2 = y / 2 by omega] using hhyp
  have heq := hyp_natAbs_pow_of_classification hhyp'
  refine ⟨m, n, hmn, hpar',
    isGaussianHypotenusePower_of_hyp_eq_pow he hmn hpar' heq, ?_⟩
  exact exists_associated_pow_of_hyp_eq_pow he hmn hpar' heq

/-- Symmetric `x = z` equal-odd slice. -/
theorem exists_gaussian_hyp_pow_of_expGcd_eq_two_of_eq_odd_xz
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hxz : x = z)
    (_hodd : Odd (x / 2))
    (hsol : A ^ x + B ^ y = C ^ z) :
    ∃ m n : ℤ,
      Int.gcd m n = 1 ∧
        ((Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) ∧
          IsGaussianHypotenusePower m n (x / 2) ∧
            ∃ g : ℤ[i], Associated (g ^ (x / 2)) (⟨m, n⟩ : ℤ[i]) := by
  obtain ⟨m, n, _hleg, hhyp, hmn, hpar⟩ :=
    beal_pythagorean_classification_of_expGcd_eq_two hx hy hz hA hB hC hgcd hd hsol
  have he : 0 < x / 2 := by
    have := (beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol).1
    omega
  have hpar' := parity_of_emod hpar
  have hhyp' : C ^ (x / 2) = m ^ 2 + n ^ 2 ∨ C ^ (x / 2) = -(m ^ 2 + n ^ 2) := by
    simpa [hxz, show z / 2 = x / 2 by omega] using hhyp
  have heq := hyp_natAbs_pow_of_classification hhyp'
  refine ⟨m, n, hmn, hpar',
    isGaussianHypotenusePower_of_hyp_eq_pow he hmn hpar' heq, ?_⟩
  exact exists_associated_pow_of_hyp_eq_pow he hmn hpar' heq

/--
From even leg `2mn = K^e` and hyp `m^2+n^2 = C^e` with odd `e ≥ 3`, the Nat-UFD
coordinate powers together with the FLT axiom forbid pure both-leg `e`-th powers.
This is the FLT gate used by the equal-odd Beal slices.
-/
theorem not_pure_coord_pow_hyp {u v c : ℤ} {e : ℕ}
    (he : 3 ≤ e) (hu : u ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0)
    (heq : u ^ (2 * e) + v ^ (2 * e) = c ^ e) : False := by
  have h' : (u ^ e) ^ 2 + (v ^ e) ^ 2 = c ^ e := by
    calc (u ^ e) ^ 2 + (v ^ e) ^ 2
        = u ^ (e * 2) + v ^ (e * 2) := by rw [← pow_mul, ← pow_mul]
      _ = u ^ (2 * e) + v ^ (2 * e) := by simp [mul_comm]
      _ = c ^ e := heq
  exact not_hyp_pow_of_both_legs_pow he hu hv hc h'

/-! ### Equal-odd descent package -/

/--
Equal-odd `y = z` package: Gaussian hypotenuse associate power with `e = y/2 ≥ 3`.
-/
theorem eq_odd_yz_descent {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hyz : y = z)
    (hodd : Odd (y / 2))
    (hsol : A ^ x + B ^ y = C ^ z) :
    ∃ m n : ℤ,
      Int.gcd m n = 1 ∧
        ((Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) ∧
          IsGaussianHypotenusePower m n (y / 2) ∧
            (∃ g : ℤ[i], Associated (g ^ (y / 2)) (⟨m, n⟩ : ℤ[i])) ∧
              3 ≤ y / 2 := by
  obtain ⟨m, n, hmn, hpar, hIs, hG⟩ :=
    exists_gaussian_hyp_pow_of_expGcd_eq_two_of_eq_odd_yz
      hx hy hz hA hB hC hgcd hd hyz hodd hsol
  have he3 : 3 ≤ y / 2 := by
    obtain ⟨_, hy2, _⟩ := bealExpGcd_eq_two_dvd hd
    exact odd_div_two_ge_three hy2 hy hodd
  exact ⟨m, n, hmn, hpar, hIs, hG, he3⟩

/-- Symmetric `x = z` package. -/
theorem eq_odd_xz_descent {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hxz : x = z)
    (hodd : Odd (x / 2))
    (hsol : A ^ x + B ^ y = C ^ z) :
    ∃ m n : ℤ,
      Int.gcd m n = 1 ∧
        ((Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) ∧
          IsGaussianHypotenusePower m n (x / 2) ∧
            (∃ g : ℤ[i], Associated (g ^ (x / 2)) (⟨m, n⟩ : ℤ[i])) ∧
              3 ≤ x / 2 := by
  obtain ⟨m, n, hmn, hpar, hIs, hG⟩ :=
    exists_gaussian_hyp_pow_of_expGcd_eq_two_of_eq_odd_xz
      hx hy hz hA hB hC hgcd hd hxz hodd hsol
  have he3 : 3 ≤ x / 2 := by
    obtain ⟨hx2, _, _⟩ := bealExpGcd_eq_two_dvd hd
    exact odd_div_two_ge_three hx2 hx hodd
  exact ⟨m, n, hmn, hpar, hIs, hG, he3⟩

/-! ### Equal-odd: mod 4, FLT pure gate, two-factor residual -/

private theorem odd_sq_emod_four {a : ℤ} (h : Odd a) : a ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ := h
  have : (2 * k + 1) ^ 2 % 4 = 1 := by ring_nf; omega
  exact this

private theorem sq_emod_four_ne_two (a : ℤ) : a ^ 2 % 4 ≠ 2 := by
  have h : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases h with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

private theorem bealExpGcd_comm_left (x y z : ℕ) :
    bealExpGcd y x z = bealExpGcd x y z := by
  simp [bealExpGcd, Nat.gcd_left_comm]

private theorem bealGcd_comm_left (A B C : ℤ) :
    bealGcd B A C = bealGcd A B C := by
  simp [bealGcd, Nat.gcd_left_comm]

theorem not_both_odd_bases_of_expGcd_eq_two_of_eq_odd_yz {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hd : bealExpGcd x y z = 2) (_hyz : y = z)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hAodd : Odd A) (hBodd : Odd B) : False := by
  obtain ⟨_, _, _, hpy⟩ := beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol
  have h1 : (A ^ (x / 2)) ^ 2 % 4 = 1 := odd_sq_emod_four (Odd.pow hAodd)
  have h2 : (B ^ (y / 2)) ^ 2 % 4 = 1 := odd_sq_emod_four (Odd.pow hBodd)
  have hsum : ((A ^ (x / 2)) ^ 2 + (B ^ (y / 2)) ^ 2) % 4 = 2 := by
    have := Int.add_emod ((A ^ (x / 2)) ^ 2) ((B ^ (y / 2)) ^ 2)
    omega
  have : (C ^ (z / 2)) ^ 2 % 4 = 2 := by rwa [hpy] at hsum
  exact (sq_emod_four_ne_two (C ^ (z / 2))) this

theorem not_both_odd_bases_of_expGcd_eq_two_of_eq_odd_xz {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hd : bealExpGcd x y z = 2) (hxz : x = z)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hAodd : Odd A) (hBodd : Odd B) : False := by
  have hsol' : B ^ y + A ^ x = C ^ z := by rw [add_comm]; exact hsol
  have hd' : bealExpGcd y x z = 2 := by rw [bealExpGcd_comm_left]; exact hd
  exact not_both_odd_bases_of_expGcd_eq_two_of_eq_odd_yz
    hy hx hz hd' hxz hsol' hBodd hAodd

theorem not_eq_odd_pure_coords {m n C : ℤ} {e : ℕ}
    (he : 3 ≤ e) (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (hw : ∃ w : ℕ, m.natAbs = w ^ e)
    (hu : ∃ u : ℕ, n.natAbs = u ^ e)
    (heq : m ^ 2 + n ^ 2 = (C.natAbs : ℤ) ^ e) : False := by
  obtain ⟨w, hw'⟩ := hw
  obtain ⟨u, hu'⟩ := hu
  have hu0 : (u : ℤ) ≠ 0 := by
    intro h
    have : u = 0 := by exact_mod_cast h
    subst this
    have he0 : e ≠ 0 := by omega
    have : n.natAbs = 0 := by simpa [zero_pow he0] using hu'
    exact hn0 (Int.natAbs_eq_zero.mp this)
  have hw0 : (w : ℤ) ≠ 0 := by
    intro h
    have : w = 0 := by exact_mod_cast h
    subst this
    have he0 : e ≠ 0 := by omega
    have : m.natAbs = 0 := by simpa [zero_pow he0] using hw'
    exact hm0 (Int.natAbs_eq_zero.mp this)
  have hc0 : (C.natAbs : ℤ) ≠ 0 := by
    intro h
    have hC0 : C.natAbs = 0 := by exact_mod_cast h
    have he0 : e ≠ 0 := by omega
    have hsum0 : m ^ 2 + n ^ 2 = 0 := by simpa [hC0, zero_pow he0] using heq
    exact hm0 (by nlinarith [sq_nonneg m, sq_nonneg n, hsum0])
  apply not_pure_coord_pow_hyp he hu0 hw0 hc0
  have hn' : (n.natAbs : ℤ) = (u : ℤ) ^ e := by exact_mod_cast hu'
  have hm' : (m.natAbs : ℤ) = (w : ℤ) ^ e := by exact_mod_cast hw'
  calc (u : ℤ) ^ (2 * e) + (w : ℤ) ^ (2 * e)
      = ((u : ℤ) ^ e) ^ 2 + ((w : ℤ) ^ e) ^ 2 := by
        rw [← pow_mul, ← pow_mul]; simp [mul_comm]
    _ = (n.natAbs : ℤ) ^ 2 + (m.natAbs : ℤ) ^ 2 := by rw [hn', hm']
    _ = m ^ 2 + n ^ 2 := by
        simp [sq, add_comm]
    _ = (C.natAbs : ℤ) ^ e := heq

def BealEqualOddTwoFactorResidual : Prop :=
  ∀ (m n : ℤ) (e : ℕ),
    3 ≤ e → Odd e →
    Int.gcd m n = 1 →
    ((Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) →
    (∃ g : ℤ[i], Associated (g ^ e) (⟨m, n⟩ : ℤ[i])) →
    ((∃ u v : ℕ, n.natAbs = u ^ e ∧ 2 * m.natAbs = v ^ e) ∨
      (∃ u v : ℕ, m.natAbs = u ^ e ∧ 2 * n.natAbs = v ^ e)) →
    False

theorem not_beal_sol_of_expGcd_eq_two_of_eq_odd_yz
    (hRes : BealEqualOddTwoFactorResidual)
    {A B C : ℤ} {x y z : ℕ}
    (_hx : 3 ≤ x) (hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0)
    (_hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hyz : y = z)
    (hodd : Odd (y / 2))
    (_hsol : A ^ x + B ^ y = C ^ z)
    (hBeven :
      ∃ m n : ℤ,
        A ^ (x / 2) = m ^ 2 - n ^ 2 ∧
          B ^ (y / 2) = 2 * m * n ∧
            (C ^ (z / 2) = m ^ 2 + n ^ 2 ∨ C ^ (z / 2) = -(m ^ 2 + n ^ 2)) ∧
              Int.gcd m n = 1 ∧
                (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)) :
    False := by
  obtain ⟨m, n, _, hBleg, hhyp, hmn, hpar⟩ := hBeven
  have he3 : 3 ≤ y / 2 := by
    obtain ⟨_, hy2, _⟩ := bealExpGcd_eq_two_dvd hd
    exact odd_div_two_ge_three hy2 hy hodd
  have he : 0 < y / 2 := lt_of_lt_of_le (by decide : 0 < 3) he3
  have hparE := parity_of_emod hpar
  have heq := hyp_natAbs_pow_of_classification (by
    simpa [hyz, show z / 2 = y / 2 by omega] using hhyp)
  obtain ⟨g, hg⟩ := exists_associated_pow_of_hyp_eq_pow he hmn hparE heq
  have hKeq : 2 * m * n = B ^ (y / 2) := by simpa [mul_assoc] using hBleg.symm
  have hdat := exists_natAbs_pow_of_two_mul_eq_pow hmn hparE hKeq he
  exact hRes m n (y / 2) he3 hodd hmn hparE ⟨g, hg⟩ (by
    rcases hdat with ⟨_, u, v, hn, hm⟩ | ⟨_, u, v, hm, hn⟩
    · exact Or.inl ⟨u, v, hn, hm⟩
    · exact Or.inr ⟨u, v, hm, hn⟩)

theorem not_beal_sol_of_expGcd_eq_two_of_eq_odd_xz
    (hRes : BealEqualOddTwoFactorResidual)
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hxz : x = z)
    (hodd : Odd (x / 2))
    (hsol : A ^ x + B ^ y = C ^ z)
    (hAeven :
      ∃ m n : ℤ,
        A ^ (x / 2) = 2 * m * n ∧
          B ^ (y / 2) = m ^ 2 - n ^ 2 ∧
            (C ^ (z / 2) = m ^ 2 + n ^ 2 ∨ C ^ (z / 2) = -(m ^ 2 + n ^ 2)) ∧
              Int.gcd m n = 1 ∧
                (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)) :
    False := by
  have hsol' : B ^ y + A ^ x = C ^ z := by rw [add_comm]; exact hsol
  have hd' : bealExpGcd y x z = 2 := by rw [bealExpGcd_comm_left]; exact hd
  have hgcd' : bealGcd B A C = 1 := by rw [bealGcd_comm_left]; exact hgcd
  refine not_beal_sol_of_expGcd_eq_two_of_eq_odd_yz
    hRes hy hx hz hB hA hC hgcd' hd' hxz hodd hsol' ?_
  obtain ⟨m, n, hAleg, hBleg, hhyp, hmn, hpar⟩ := hAeven
  refine ⟨m, n, hBleg, ?_, ?_, hmn, hpar⟩
  · simpa [hxz, show x / 2 = z / 2 by omega] using hAleg
  · simpa [hxz, show x / 2 = z / 2 by omega] using hhyp

/-! ### `d = 1` two-equal even progress -/

def BealTwoEqualEvenResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Even x) ∨ (y = z ∧ Even y) ∨ (x = z ∧ Even x)) →
    ¬ A ^ x + B ^ y = C ^ z

private theorem odd_z_of_even_x_coprime {x z : ℕ}
    (hxeven : Even x) (hgcd : Nat.gcd x z = 1) : Odd z := by
  have hx2 : 2 ∣ x := even_iff_two_dvd.mp hxeven
  have : ¬ (2 ∣ z) := by
    intro hz2
    have : 2 ∣ Nat.gcd x z := Nat.dvd_gcd hx2 hz2
    omega
  exact Nat.not_even_iff_odd.1 (fun h => this (even_iff_two_dvd.mp h))

private theorem even_pow_of_even {a : ℤ} {n : ℕ} (ha : Even a) (hn : n ≠ 0) :
    Even (a ^ n) := by
  rw [even_iff_two_dvd] at ha ⊢
  exact dvd_pow ha hn

private theorem odd_of_odd_pow {a : ℤ} {n : ℕ} (hn : n ≠ 0) (h : Odd (a ^ n)) :
    Odd a := by
  by_contra hnot
  have ha : Even a := Int.not_odd_iff_even.mp hnot
  exact Int.not_odd_iff_even.mpr (even_pow_of_even ha hn) h

theorem beal_two_equal_xy_even_not_both_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x) (hAodd : Odd A) (hBodd : Odd B) (hCodd : Odd C)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  subst hxy
  obtain ⟨hg, _⟩ := beal_two_equal_exp_of_expGcd_eq_one hx rfl hd
  have hzodd : Odd z := odd_z_of_even_x_coprime hxeven hg
  obtain ⟨t, ht⟩ := even_iff_two_dvd.mp hxeven
  have hform : (A ^ t) ^ 2 + (B ^ t) ^ 2 = C ^ z := by
    calc (A ^ t) ^ 2 + (B ^ t) ^ 2
        = A ^ (2 * t) + B ^ (2 * t) := by simp [pow_mul, mul_comm]
      _ = A ^ x + B ^ x := by rw [← ht]
      _ = C ^ z := hsol
  have h1 : (A ^ t) ^ 2 % 4 = 1 := odd_sq_emod_four (Odd.pow hAodd)
  have h2 : (B ^ t) ^ 2 % 4 = 1 := odd_sq_emod_four (Odd.pow hBodd)
  have hsum : ((A ^ t) ^ 2 + (B ^ t) ^ 2) % 4 = 2 := by
    have := Int.add_emod ((A ^ t) ^ 2) ((B ^ t) ^ 2); omega
  have hCz : C ^ z % 4 = C % 4 := by
    obtain ⟨k, hk⟩ := hzodd
    have ha2 : C ^ 2 % 4 = 1 := odd_sq_emod_four hCodd
    have hpow : ∀ k : ℕ, (C ^ 2) ^ k % 4 = 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Int.mul_emod, ih, ha2]; norm_num
    have hrewrite : C ^ (2 * k + 1) = (C ^ 2) ^ k * C := by
      rw [pow_add, pow_one, pow_mul]
    rw [hk, hrewrite, Int.mul_emod, hpow k]
    omega
  have hCmod : C % 4 = 1 ∨ C % 4 = 3 := by
    have : C % 2 = 1 := Int.odd_iff.mp hCodd
    have h : C % 4 = 0 ∨ C % 4 = 1 ∨ C % 4 = 2 ∨ C % 4 = 3 := by omega
    rcases h with h | h | h | h
    · omega
    · exact Or.inl h
    · omega
    · exact Or.inr h
  have : C ^ z % 4 = 2 := by rwa [hform] at hsum
  rcases hCmod with h | h <;> omega

theorem beal_two_equal_xy_even_sq_sum {A B C : ℤ} {x y z : ℕ}
    (_hx : 3 ≤ x) (hxy : x = y) (_hd : bealExpGcd x y z = 1)
    (hxeven : Even x)
    (hsol : A ^ x + B ^ y = C ^ z) :
    (A ^ (x / 2)) ^ 2 + (B ^ (x / 2)) ^ 2 = C ^ z := by
  subst hxy
  obtain ⟨t, ht⟩ := even_iff_two_dvd.mp hxeven
  have ht' : x / 2 = t := by omega
  rw [ht']
  calc (A ^ t) ^ 2 + (B ^ t) ^ 2
      = A ^ (2 * t) + B ^ (2 * t) := by simp [pow_mul, mul_comm]
    _ = A ^ x + B ^ x := by rw [← ht]
    _ = C ^ z := hsol

theorem beal_two_equal_xy_even_opposite_parity_of_odd_C {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x) (hCodd : Odd C)
    (_hA : A ≠ 0) (_hB : B ≠ 0)
    (_hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    (Even A ∧ Odd B) ∨ (Odd A ∧ Even B) := by
  subst hxy
  have hx0 : x ≠ 0 := by omega
  by_cases hAe : Even A
  · by_cases hBe : Even B
    · exact False.elim (by
        have : Even (A ^ x + B ^ x) :=
          Even.add (even_pow_of_even hAe hx0) (even_pow_of_even hBe hx0)
        have hOdd : Odd (C ^ z) := Odd.pow hCodd
        have hEven : Even (C ^ z) := by simpa [hsol] using this
        exact Int.not_odd_iff_even.mpr hEven hOdd)
    · exact Or.inl ⟨hAe, Int.not_even_iff_odd.mp hBe⟩
  · by_cases hBe : Even B
    · exact Or.inr ⟨Int.not_even_iff_odd.mp hAe, hBe⟩
    · exact False.elim (beal_two_equal_xy_even_not_both_odd hx rfl hd hxeven
        (Int.not_even_iff_odd.mp hAe) (Int.not_even_iff_odd.mp hBe) hCodd hsol)

theorem beal_two_equal_xy_even_C_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hz : 3 ≤ z) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x)
    (hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) : Odd C := by
  subst hxy
  have hx0 : x ≠ 0 := by omega
  have hz0 : z ≠ 0 := by omega
  by_contra hnot
  have hCeven : Even C := Int.not_odd_iff_even.mp hnot
  by_cases hAe : Even A
  · by_cases hBe : Even B
    · have hA2 : 2 ∣ A.natAbs :=
        even_iff_two_dvd.mp (Int.natAbs_even.mpr hAe)
      have hB2 : 2 ∣ B.natAbs :=
        even_iff_two_dvd.mp (Int.natAbs_even.mpr hBe)
      have hC2 : 2 ∣ C.natAbs :=
        even_iff_two_dvd.mp (Int.natAbs_even.mpr hCeven)
      have : 2 ∣ bealGcd A B C := by
        simpa [bealGcd] using Nat.dvd_gcd hA2 (Nat.dvd_gcd hB2 hC2)
      have : 2 ≤ bealGcd A B C := Nat.le_of_dvd (bealGcd_pos hA) this
      omega
    · have : Odd (A ^ x + B ^ x) :=
        Even.add_odd (even_pow_of_even hAe hx0)
          (Odd.pow (Int.not_even_iff_odd.mp hBe))
      have : Odd (C ^ z) := by simpa [hsol] using this
      exact Int.not_odd_iff_even.mpr hCeven (odd_of_odd_pow hz0 this)
  · by_cases hBe : Even B
    · have : Odd (A ^ x + B ^ x) :=
        Odd.add_even (Odd.pow (Int.not_even_iff_odd.mp hAe))
          (even_pow_of_even hBe hx0)
      have : Odd (C ^ z) := by simpa [hsol] using this
      exact Int.not_odd_iff_even.mpr hCeven (odd_of_odd_pow hz0 this)
    · have hform := beal_two_equal_xy_even_sq_sum hx rfl hd hxeven hsol
      have hAo := Int.not_even_iff_odd.mp hAe
      have hBo := Int.not_even_iff_odd.mp hBe
      have h1 : (A ^ (x / 2)) ^ 2 % 4 = 1 := odd_sq_emod_four (Odd.pow hAo)
      have h2 : (B ^ (x / 2)) ^ 2 % 4 = 1 := odd_sq_emod_four (Odd.pow hBo)
      have hsum : ((A ^ (x / 2)) ^ 2 + (B ^ (x / 2)) ^ 2) % 4 = 2 := by
        have := Int.add_emod ((A ^ (x / 2)) ^ 2) ((B ^ (x / 2)) ^ 2); omega
      have hCz0 : (C ^ z) % 4 = 0 := by
        have hC2 : 2 ∣ C := even_iff_two_dvd.mp hCeven
        obtain ⟨c, rfl⟩ := hC2
        have hz2 : 2 ≤ z := Nat.le_trans (by decide : 2 ≤ 3) hz
        have : (4 : ℤ) ∣ (2 * c) ^ z := by
          have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ z := by
            have : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ z := pow_dvd_pow (2 : ℤ) hz2
            simpa using this
          have : (4 : ℤ) ∣ 2 ^ z * c ^ z := Dvd.dvd.mul_right h4 _
          simpa [mul_pow] using this
        exact Int.emod_eq_zero_of_dvd this
      have : (C ^ z) % 4 = 2 := by rwa [hform] at hsum
      omega

theorem beal_two_equal_xy_even_progress {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hz : 3 ≤ z) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Odd C ∧
      ((Even A ∧ Odd B) ∨ (Odd A ∧ Even B)) ∧
        (A ^ (x / 2)) ^ 2 + (B ^ (x / 2)) ^ 2 = C ^ z := by
  have hCodd := beal_two_equal_xy_even_C_odd hx hz hxy hd hxeven hA hB hC hgcd hsol
  exact ⟨hCodd,
    beal_two_equal_xy_even_opposite_parity_of_odd_C hx hxy hd hxeven hCodd hA hB hgcd hsol,
    beal_two_equal_xy_even_sq_sum hx hxy hd hxeven hsol⟩

theorem beal_two_equal_xy_even_of_residual
    (hRes : BealTwoEqualEvenResidual)
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxy : x = y) (hxeven : Even x)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  hRes A B C x y z hx hy hz hA hB hC hgcd hd (Or.inl ⟨hxy, hxeven⟩) hsol

end Theorems

end DstDiophantine
