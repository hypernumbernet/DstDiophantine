import DstDiophantine.Framework.Lattice
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Discrete torsional spectrum

The admissible image of `latticeMismatch` is the three-fold sumset of
one-axis differences of squares in the triangle `n + m ≤ ⌊N/4⌋`.  That
sumset is a proper subset of `{−3K²,…,3K²}` for some `K` (spectral holes).
The slot `Δ = ±1` is occupied as soon as `N ≥ 4`, so the nonzero height
floor `16/(3N²)` is attained.
-/

namespace DstDiophantine

namespace Framework

open Discrete Invariant Finset

/-! ### One-axis mismatch -/

/-- Signed one-axis quadratic mismatch. -/
def axisMismatch (n m : ℕ) : ℤ :=
  (n : ℤ) ^ 2 - (m : ℤ) ^ 2

/-- Unsigned one-axis quadratic mass. -/
def axisMass (n m : ℕ) : ℕ :=
  n ^ 2 + m ^ 2

theorem axisMismatch_comm (n m : ℕ) :
    axisMismatch n m = -axisMismatch m n := by
  unfold axisMismatch; ring

theorem axisMismatch_eq_zero_of_eq {n m : ℕ} (h : n = m) :
    axisMismatch n m = 0 := by
  unfold axisMismatch; simp [h]

theorem abs_axisMismatch_le_axisMass (n m : ℕ) :
    |axisMismatch n m| ≤ (axisMass n m : ℤ) := by
  unfold axisMismatch axisMass
  set nZ : ℤ := (n : ℤ)
  set mZ : ℤ := (m : ℤ)
  have hcast : ((n ^ 2 + m ^ 2 : ℕ) : ℤ) = nZ ^ 2 + mZ ^ 2 := by
    simp [nZ, mZ]
  rw [hcast]
  have hn : 0 ≤ nZ ^ 2 := sq_nonneg nZ
  have hm : 0 ≤ mZ ^ 2 := sq_nonneg mZ
  rcases le_total (nZ ^ 2) (mZ ^ 2) with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)]; linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]; linarith

theorem axisMass_add_mismatch (n m : ℕ) :
    (axisMass n m : ℤ) + axisMismatch n m = 2 * (n : ℤ) ^ 2 := by
  unfold axisMass axisMismatch
  push_cast
  ring

theorem axisMismatch_modEq_axisMass (n m : ℕ) :
    axisMismatch n m ≡ (axisMass n m : ℤ) [ZMOD 2] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨(m : ℤ) ^ 2, ?_⟩
  unfold axisMismatch axisMass
  push_cast
  ring

theorem abs_axisMismatch_le_add_sq (n m : ℕ) :
    |axisMismatch n m| ≤ ((n + m : ℕ) : ℤ) ^ 2 := by
  unfold axisMismatch
  have hfac : (n : ℤ) ^ 2 - (m : ℤ) ^ 2 =
      ((n : ℤ) - (m : ℤ)) * ((n : ℤ) + (m : ℤ)) := by ring
  rw [hfac, abs_mul]
  have hsum_nn : (0 : ℤ) ≤ (n : ℤ) + (m : ℤ) :=
    add_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)
  have hsum : (n : ℤ) + (m : ℤ) = ((n + m : ℕ) : ℤ) := by push_cast; rfl
  rw [abs_of_nonneg hsum_nn, hsum]
  have hdiff : |(n : ℤ) - (m : ℤ)| ≤ ((n + m : ℕ) : ℤ) := by
    rw [← hsum]
    rcases le_total (n : ℤ) (m : ℤ) with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]; linarith
  have hmul :
      |(n : ℤ) - (m : ℤ)| * ((n + m : ℕ) : ℤ) ≤
        ((n + m : ℕ) : ℤ) * ((n + m : ℕ) : ℤ) :=
    mul_le_mul_of_nonneg_right hdiff (Nat.cast_nonneg (n + m))
  simpa [pow_two] using hmul

theorem abs_axisMismatch_le_of_triangle {K n m : ℕ} (h : n + m ≤ K) :
    |axisMismatch n m| ≤ (K : ℤ) ^ 2 :=
  (abs_axisMismatch_le_add_sq n m).trans <|
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h) 2

/-- Wall pairs saturating `|n² − m²| = K²`. -/
theorem abs_axisMismatch_eq_Ksq_iff {K n m : ℕ} (h : n + m ≤ K) :
    |axisMismatch n m| = (K : ℤ) ^ 2 ↔
      (n = K ∧ m = 0) ∨ (n = 0 ∧ m = K) := by
  constructor
  · intro heq
    have hle := abs_axisMismatch_le_add_sq n m
    have hsumK : ((n + m : ℕ) : ℤ) ^ 2 = (K : ℤ) ^ 2 :=
      le_antisymm
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h) 2)
        (heq.symm.trans_le hle)
    have hsum : n + m = K := by
      have hnn : (0 : ℤ) ≤ ((n + m : ℕ) : ℤ) := Nat.cast_nonneg _
      have hK : (0 : ℤ) ≤ (K : ℤ) := Nat.cast_nonneg _
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsumK) with hpos | hneg
      · exact_mod_cast hpos
      · have hn0 : (n + m : ℕ) = 0 := by
          have : ((n + m : ℕ) : ℤ) = 0 := by nlinarith [hnn, hK, hneg]
          exact_mod_cast this
        have hK0 : K = 0 := by
          have : (K : ℤ) = 0 := by nlinarith [hnn, hK, hneg]
          exact_mod_cast this
        omega
    have hfac : axisMismatch n m =
        ((n : ℤ) - (m : ℤ)) * ((n : ℤ) + (m : ℤ)) := by
      unfold axisMismatch; ring
    have hsum_nn : (0 : ℤ) ≤ (n : ℤ) + (m : ℤ) :=
      add_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)
    have hcast : (n : ℤ) + (m : ℤ) = ((n + m : ℕ) : ℤ) := by push_cast; rfl
    have hsumZ : ((n + m : ℕ) : ℤ) = (K : ℤ) := by exact_mod_cast hsum
    have habsprod : |(n : ℤ) - (m : ℤ)| * (K : ℤ) = (K : ℤ) ^ 2 := by
      calc |(n : ℤ) - (m : ℤ)| * (K : ℤ)
          = |(n : ℤ) - (m : ℤ)| * |(n : ℤ) + (m : ℤ)| := by
            rw [← hsumZ, ← hcast, abs_of_nonneg hsum_nn]
        _ = |axisMismatch n m| := by rw [hfac, abs_mul]
        _ = (K : ℤ) ^ 2 := heq
    rcases eq_or_ne K 0 with hK0 | hK0
    · subst hK0
      have : n = 0 ∧ m = 0 := by omega
      exact Or.inl this
    · have hKpos : (0 : ℤ) < K := by exact_mod_cast (Nat.pos_of_ne_zero hK0)
      have hdiff : |(n : ℤ) - (m : ℤ)| = (K : ℤ) :=
        (mul_left_inj' hKpos.ne').mp (by simpa [pow_two, mul_comm] using habsprod)
      have hcases : (n : ℤ) - (m : ℤ) = K ∨ (n : ℤ) - (m : ℤ) = -K :=
        (abs_eq (Nat.cast_nonneg K)).mp hdiff
      have hnadd : (n : ℤ) + (m : ℤ) = K := by
        rw [hcast, hsumZ]
      rcases hcases with hpos | hneg
      · have hm0 : (m : ℤ) = 0 := by linarith
        have hnK : (n : ℤ) = K := by linarith
        exact Or.inl ⟨by exact_mod_cast hnK, by exact_mod_cast hm0⟩
      · have hn0 : (n : ℤ) = 0 := by linarith
        have hmK : (m : ℤ) = K := by linarith
        exact Or.inr ⟨by exact_mod_cast hn0, by exact_mod_cast hmK⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [axisMismatch]

/-! ### Triangle pairs and the three-fold sumset -/

/-- Integer pairs in the admissible triangle `n + m ≤ K`. -/
def axisPairs (K : ℕ) : Finset (ℕ × ℕ) :=
  (range (K + 1)).biUnion fun n =>
    (range (K + 1 - n)).image fun m => (n, m)

theorem mem_axisPairs {K n m : ℕ} :
    (n, m) ∈ axisPairs K ↔ n + m ≤ K := by
  simp only [axisPairs, mem_biUnion, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨n', hn', m', hm', rfl, rfl⟩
    omega
  · intro h
    refine ⟨n, ?_, m, ?_, rfl, rfl⟩
    · omega
    · omega

/-- Occupied one-axis mismatches. -/
def axisMismatchSet (K : ℕ) : Finset ℤ :=
  (axisPairs K).image fun p => axisMismatch p.1 p.2

theorem mem_axisMismatchSet {K : ℕ} {x : ℤ} :
    x ∈ axisMismatchSet K ↔ ∃ n m, n + m ≤ K ∧ axisMismatch n m = x := by
  constructor
  · intro hx
    obtain ⟨⟨n, m⟩, hnm, rfl⟩ := mem_image.mp hx
    exact ⟨n, m, mem_axisPairs.mp hnm, rfl⟩
  · rintro ⟨n, m, hnm, rfl⟩
    exact mem_image.mpr ⟨(n, m), mem_axisPairs.mpr hnm, rfl⟩

theorem axisMismatchSet_zero (K : ℕ) : (0 : ℤ) ∈ axisMismatchSet K := by
  rw [mem_axisMismatchSet]
  exact ⟨0, 0, Nat.zero_le _, by simp [axisMismatch]⟩

theorem axisMismatchSet_neg {K : ℕ} {x : ℤ}
    (hx : x ∈ axisMismatchSet K) : -x ∈ axisMismatchSet K := by
  rw [mem_axisMismatchSet] at hx ⊢
  obtain ⟨n, m, hnm, rfl⟩ := hx
  refine ⟨m, n, ?_, axisMismatch_comm m n⟩
  omega

theorem one_mem_axisMismatchSet_iff {K : ℕ} :
    (1 : ℤ) ∈ axisMismatchSet K ↔ 1 ≤ K := by
  constructor
  · intro hx
    rw [mem_axisMismatchSet] at hx
    obtain ⟨n, m, hnm, heq⟩ := hx
    have : n + m ≠ 0 := by
      intro h0
      have hn : n = 0 := by omega
      have hm : m = 0 := by omega
      simp [axisMismatch, hn, hm] at heq
    omega
  · intro hK
    rw [mem_axisMismatchSet]
    refine ⟨1, 0, ?_, ?_⟩
    · omega
    · simp [axisMismatch]

theorem neg_one_mem_axisMismatchSet_iff {K : ℕ} :
    (-1 : ℤ) ∈ axisMismatchSet K ↔ 1 ≤ K := by
  constructor
  · intro hx
    have := axisMismatchSet_neg hx
    simpa using (one_mem_axisMismatchSet_iff (K := K)).mp this
  · intro hK
    exact axisMismatchSet_neg ((one_mem_axisMismatchSet_iff (K := K)).mpr hK)

/-- Three-fold sumset of one-axis mismatches. -/
def threeMismatchSet (K : ℕ) : Finset ℤ :=
  (axisMismatchSet K).biUnion fun a =>
    (axisMismatchSet K).biUnion fun b =>
      (axisMismatchSet K).image fun c => a + b + c

theorem mem_threeMismatchSet {K : ℕ} {x : ℤ} :
    x ∈ threeMismatchSet K ↔
      ∃ n0 m0 n1 m1 n2 m2,
        n0 + m0 ≤ K ∧ n1 + m1 ≤ K ∧ n2 + m2 ≤ K ∧
          axisMismatch n0 m0 + axisMismatch n1 m1 + axisMismatch n2 m2 = x := by
  simp only [threeMismatchSet, mem_biUnion, mem_image, mem_axisMismatchSet]
  constructor
  · rintro ⟨a, ⟨n0, m0, h0, rfl⟩, b, ⟨n1, m1, h1, rfl⟩, c, ⟨n2, m2, h2, rfl⟩, rfl⟩
    exact ⟨n0, m0, n1, m1, n2, m2, h0, h1, h2, rfl⟩
  · rintro ⟨n0, m0, n1, m1, n2, m2, h0, h1, h2, rfl⟩
    exact ⟨_, ⟨n0, m0, h0, rfl⟩, _, ⟨n1, m1, h1, rfl⟩, _, ⟨n2, m2, h2, rfl⟩, rfl⟩

theorem threeMismatchSet_zero (K : ℕ) : (0 : ℤ) ∈ threeMismatchSet K := by
  rw [mem_threeMismatchSet]
  exact ⟨0, 0, 0, 0, 0, 0, by omega, by omega, by omega, by simp [axisMismatch]⟩

theorem three_mul_Ksq_mem (K : ℕ) :
    (3 : ℤ) * (K : ℤ) ^ 2 ∈ threeMismatchSet K := by
  rw [mem_threeMismatchSet]
  refine ⟨K, 0, K, 0, K, 0, by omega, by omega, by omega, ?_⟩
  simp [axisMismatch]; ring

theorem neg_three_mul_Ksq_mem (K : ℕ) :
    -((3 : ℤ) * (K : ℤ) ^ 2) ∈ threeMismatchSet K := by
  rw [mem_threeMismatchSet]
  refine ⟨0, K, 0, K, 0, K, by omega, by omega, by omega, ?_⟩
  simp [axisMismatch]; ring

theorem abs_threeMismatch_le {K : ℕ} {x : ℤ} (hx : x ∈ threeMismatchSet K) :
    |x| ≤ 3 * (K : ℤ) ^ 2 := by
  rw [mem_threeMismatchSet] at hx
  obtain ⟨n0, m0, n1, m1, n2, m2, h0, h1, h2, rfl⟩ := hx
  have b0 := abs_axisMismatch_le_of_triangle h0
  have b1 := abs_axisMismatch_le_of_triangle h1
  have b2 := abs_axisMismatch_le_of_triangle h2
  calc
    |axisMismatch n0 m0 + axisMismatch n1 m1 + axisMismatch n2 m2|
        ≤ |axisMismatch n0 m0| + |axisMismatch n1 m1| + |axisMismatch n2 m2| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ (K : ℤ) ^ 2 + (K : ℤ) ^ 2 + (K : ℤ) ^ 2 := by gcongr
      _ = 3 * (K : ℤ) ^ 2 := by ring

/-- Computable closed interval `{−3K²,…,3K²}`. -/
def mismatchInterval (K : ℕ) : Finset ℤ :=
  (Finset.range (2 * (3 * K ^ 2) + 1)).image fun i : ℕ =>
    (i : ℤ) - (3 * (K : ℤ) ^ 2)

theorem mem_mismatchInterval {K : ℕ} {x : ℤ} :
    x ∈ mismatchInterval K ↔ |x| ≤ 3 * (K : ℤ) ^ 2 := by
  simp only [mismatchInterval, mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, hx⟩
    have hi' : (i : ℤ) < 2 * (3 * (K : ℤ) ^ 2) + 1 := by
      exact_mod_cast hi
    have hi0 : (0 : ℤ) ≤ (i : ℤ) := Nat.cast_nonneg i
    rw [← hx, abs_le]
    constructor <;> linarith
  · intro hx
    have hle := abs_le.mp hx
    set b : ℤ := 3 * (K : ℤ) ^ 2
    have hlo : 0 ≤ x + b := by linarith [hle.1]
    have hhi : x + b ≤ 2 * b := by linarith [hle.2]
    refine ⟨(x + b).toNat, ?_, ?_⟩
    · have hbNat : ((2 * (3 * K ^ 2) : ℕ) : ℤ) = 2 * b := by
        simp [b]
      have hcast : ((x + b).toNat : ℤ) ≤ 2 * b := by
        rw [Int.toNat_of_nonneg hlo]; exact hhi
      have : (x + b).toNat ≤ 2 * (3 * K ^ 2) := by
        exact_mod_cast (hcast.trans_eq hbNat.symm)
      exact Nat.lt_succ_of_le this
    · have : ((x + b).toNat : ℤ) = x + b := Int.toNat_of_nonneg hlo
      linarith

theorem threeMismatchSet_subset_interval (K : ℕ) :
    threeMismatchSet K ⊆ mismatchInterval K := by
  intro x hx
  exact mem_mismatchInterval.2 (abs_threeMismatch_le hx)

/-- Unoccupied slots inside the bound interval. -/
def mismatchHoles (K : ℕ) : Finset ℤ :=
  mismatchInterval K \ threeMismatchSet K

/-! ### Same-wall equality for the three-axis ceiling -/

private theorem abs_eq_of_sum_three {x y z c : ℤ}
    (hx : |x| ≤ c) (hy : |y| ≤ c) (hz : |z| ≤ c)
    (hs : |x| + |y| + |z| = 3 * c) :
    |x| = c ∧ |y| = c ∧ |z| = c :=
  ⟨le_antisymm hx (by linarith), le_antisymm hy (by linarith),
    le_antisymm hz (by linarith)⟩

private theorem signed_sum_of_walls {c d0 d1 d2 : ℤ} (hc : 0 < c)
    (h0 : d0 = c ∨ d0 = -c) (h1 : d1 = c ∨ d1 = -c) (h2 : d2 = c ∨ d2 = -c)
    (hsum : |d0 + d1 + d2| = 3 * c) :
    (d0 = c ∧ d1 = c ∧ d2 = c) ∨ (d0 = -c ∧ d1 = -c ∧ d2 = -c) := by
  have hcabs : |-c| = c := by rw [abs_neg, abs_of_nonneg hc.le]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl ⟨h0, h1, h2⟩
  · rw [h0, h1, h2] at hsum
    have : |c + c + -c| = c := by ring_nf; exact abs_of_nonneg hc.le
    linarith
  · rw [h0, h1, h2] at hsum
    have : |c + -c + c| = c := by ring_nf; exact abs_of_nonneg hc.le
    linarith
  · rw [h0, h1, h2] at hsum
    have : |c + -c + -c| = c := by ring_nf; exact hcabs
    linarith
  · rw [h0, h1, h2] at hsum
    have : |-c + c + c| = c := by ring_nf; exact abs_of_nonneg hc.le
    linarith
  · rw [h0, h1, h2] at hsum
    have : |-c + c + -c| = c := by ring_nf; exact hcabs
    linarith
  · rw [h0, h1, h2] at hsum
    have : |-c + -c + c| = c := by ring_nf; exact hcabs
    linarith
  · exact Or.inr ⟨h0, h1, h2⟩

/-- The three-axis ceiling is attained iff every axis sits on the same wall. -/
theorem abs_three_axis_eq_ceiling_iff {K n0 m0 n1 m1 n2 m2 : ℕ}
    (h0 : n0 + m0 ≤ K) (h1 : n1 + m1 ≤ K) (h2 : n2 + m2 ≤ K) :
    |axisMismatch n0 m0 + axisMismatch n1 m1 + axisMismatch n2 m2| =
        3 * (K : ℤ) ^ 2 ↔
      (n0 = K ∧ m0 = 0 ∧ n1 = K ∧ m1 = 0 ∧ n2 = K ∧ m2 = 0) ∨
        (n0 = 0 ∧ m0 = K ∧ n1 = 0 ∧ m1 = K ∧ n2 = 0 ∧ m2 = K) := by
  constructor
  · intro heq
    set c := (K : ℤ) ^ 2 with hcdef
    have b0 := abs_axisMismatch_le_of_triangle h0
    have b1 := abs_axisMismatch_le_of_triangle h1
    have b2 := abs_axisMismatch_le_of_triangle h2
    have habs_sum :
        |axisMismatch n0 m0 + axisMismatch n1 m1 + axisMismatch n2 m2| ≤
          |axisMismatch n0 m0| + |axisMismatch n1 m1| + |axisMismatch n2 m2| := by
      refine (abs_add_le _ _).trans ?_
      gcongr
      exact abs_add_le _ _
    have hsat :
        |axisMismatch n0 m0| + |axisMismatch n1 m1| + |axisMismatch n2 m2| =
          3 * c := by
      have hle : |axisMismatch n0 m0| + |axisMismatch n1 m1| + |axisMismatch n2 m2| ≤
          3 * c := by
        have hsum := add_le_add (add_le_add b0 b1) b2
        have : (K : ℤ) ^ 2 + (K : ℤ) ^ 2 + (K : ℤ) ^ 2 = 3 * c := by
          simp [c]; ring
        rwa [this] at hsum
      have : 3 * c ≤ |axisMismatch n0 m0| + |axisMismatch n1 m1| + |axisMismatch n2 m2| := by
        simpa [heq, c] using habs_sum
      exact le_antisymm hle this
    have ⟨e0, e1, e2⟩ := abs_eq_of_sum_three b0 b1 b2 (by simpa [c] using hsat)
    have w0 := (abs_axisMismatch_eq_Ksq_iff h0).mp (by simpa [c] using e0)
    have w1 := (abs_axisMismatch_eq_Ksq_iff h1).mp (by simpa [c] using e1)
    have w2 := (abs_axisMismatch_eq_Ksq_iff h2).mp (by simpa [c] using e2)
    by_cases hK0 : K = 0
    · subst hK0
      have : n0 = 0 ∧ m0 = 0 ∧ n1 = 0 ∧ m1 = 0 ∧ n2 = 0 ∧ m2 = 0 := by omega
      exact Or.inl this
    · have hc : 0 < c := by
        have : (0 : ℤ) < K := by exact_mod_cast (Nat.pos_of_ne_zero hK0)
        positivity
      have d0 : axisMismatch n0 m0 = c ∨ axisMismatch n0 m0 = -c := by
        rcases w0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (by simp [axisMismatch, c])
        · exact Or.inr (by simp [axisMismatch, c])
      have d1 : axisMismatch n1 m1 = c ∨ axisMismatch n1 m1 = -c := by
        rcases w1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (by simp [axisMismatch, c])
        · exact Or.inr (by simp [axisMismatch, c])
      have d2 : axisMismatch n2 m2 = c ∨ axisMismatch n2 m2 = -c := by
        rcases w2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (by simp [axisMismatch, c])
        · exact Or.inr (by simp [axisMismatch, c])
      have hall := signed_sum_of_walls hc d0 d1 d2 (by simpa [c] using heq)
      rcases hall with ⟨hd0, hd1, hd2⟩ | ⟨hd0, hd1, hd2⟩
      · refine Or.inl ?_
        have hw0 : n0 = K ∧ m0 = 0 := by
          rcases w0 with h | h
          · exact h
          · have : axisMismatch n0 m0 = -c := by simp [axisMismatch, h, c]
            exact (lt_irrefl c (by linarith [hd0, this, hc])).elim
        have hw1 : n1 = K ∧ m1 = 0 := by
          rcases w1 with h | h
          · exact h
          · have : axisMismatch n1 m1 = -c := by simp [axisMismatch, h, c]
            exact (lt_irrefl c (by linarith [hd1, this, hc])).elim
        have hw2 : n2 = K ∧ m2 = 0 := by
          rcases w2 with h | h
          · exact h
          · have : axisMismatch n2 m2 = -c := by simp [axisMismatch, h, c]
            exact (lt_irrefl c (by linarith [hd2, this, hc])).elim
        exact ⟨hw0.1, hw0.2, hw1.1, hw1.2, hw2.1, hw2.2⟩
      · refine Or.inr ?_
        have hw0 : n0 = 0 ∧ m0 = K := by
          rcases w0 with h | h
          · have : axisMismatch n0 m0 = c := by simp [axisMismatch, h, c]
            exact (lt_irrefl c (by linarith [hd0, this, hc])).elim
          · exact h
        have hw1 : n1 = 0 ∧ m1 = K := by
          rcases w1 with h | h
          · have : axisMismatch n1 m1 = c := by simp [axisMismatch, h, c]
            exact (lt_irrefl c (by linarith [hd1, this, hc])).elim
          · exact h
        have hw2 : n2 = 0 ∧ m2 = K := by
          rcases w2 with h | h
          · have : axisMismatch n2 m2 = c := by simp [axisMismatch, h, c]
            exact (lt_irrefl c (by linarith [hd2, this, hc])).elim
          · exact h
        exact ⟨hw0.1, hw0.2, hw1.1, hw1.2, hw2.1, hw2.2⟩
  · rintro (⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    · simp [axisMismatch]; ring_nf; simp
    · simp [axisMismatch]; ring_nf; simp

/-! ### Zero-height triples and the balanced cube -/

/-- Three independent triangle pairs. -/
def axisTriples (K : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  axisPairs K ×ˢ (axisPairs K ×ˢ axisPairs K)

def mismatchOfTriple (p : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  axisMismatch p.1.1 p.1.2 + axisMismatch p.2.1.1 p.2.1.2 +
    axisMismatch p.2.2.1 p.2.2.2

def massOfTriple (p : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  axisMass p.1.1 p.1.2 + axisMass p.2.1.1 p.2.1.2 + axisMass p.2.2.1 p.2.2.2

def zeroHeightTriples (K : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  (axisTriples K).filter fun p => mismatchOfTriple p = 0

def balancedPairs (K : ℕ) : Finset (ℕ × ℕ) :=
  (range (K / 2 + 1)).image fun n => (n, n)

theorem mem_balancedPairs {K n m : ℕ} :
    (n, m) ∈ balancedPairs K ↔ n = m ∧ n + m ≤ K := by
  simp only [balancedPairs, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, rfl, rfl⟩
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, hsum⟩
    refine ⟨n, ?_, rfl, rfl⟩
    omega

theorem balancedPairs_subset_axisPairs (K : ℕ) :
    balancedPairs K ⊆ axisPairs K := by
  intro p hp
  rcases p with ⟨n, m⟩
  rw [mem_balancedPairs] at hp
  exact (mem_axisPairs).2 hp.2

def balancedTriples (K : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  balancedPairs K ×ˢ (balancedPairs K ×ˢ balancedPairs K)

theorem card_balancedPairs (K : ℕ) : (balancedPairs K).card = K / 2 + 1 := by
  rw [balancedPairs, card_image_of_injective]
  · simp
  · intro a b h
    simpa using congrArg Prod.fst h

theorem card_balancedTriples (K : ℕ) :
    (balancedTriples K).card = (K / 2 + 1) ^ 3 := by
  simp [balancedTriples, card_product, card_balancedPairs]
  ring

theorem balancedTriples_subset_zeroHeight (K : ℕ) :
    balancedTriples K ⊆ zeroHeightTriples K := by
  intro p hp
  simp only [balancedTriples, mem_product] at hp
  refine mem_filter.2 ⟨?_, ?_⟩
  · simp only [axisTriples, mem_product]
    exact ⟨balancedPairs_subset_axisPairs K hp.1,
      ⟨balancedPairs_subset_axisPairs K hp.2.1,
        balancedPairs_subset_axisPairs K hp.2.2⟩⟩
  · rcases p with ⟨⟨n0, m0⟩, ⟨n1, m1⟩, ⟨n2, m2⟩⟩
    have h0 := (mem_balancedPairs (K := K)).1 hp.1
    have h1 := (mem_balancedPairs (K := K)).1 hp.2.1
    have h2 := (mem_balancedPairs (K := K)).1 hp.2.2
    simp [mismatchOfTriple, axisMismatch_eq_zero_of_eq h0.1,
      axisMismatch_eq_zero_of_eq h1.1, axisMismatch_eq_zero_of_eq h2.1]

/-- Cross-axis cancellation: `(1,0)+(0,1)+(0,0)` has vanishing mismatch. -/
def unbalancedZeroTriple : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) :=
  ((1, 0), (0, 1), (0, 0))

theorem unbalancedZeroTriple_mem {K : ℕ} (hK : 1 ≤ K) :
    unbalancedZeroTriple ∈ zeroHeightTriples K := by
  refine mem_filter.2 ⟨?_, ?_⟩
  · simp only [axisTriples, mem_product, mem_axisPairs, unbalancedZeroTriple]
    omega
  · simp [mismatchOfTriple, unbalancedZeroTriple, axisMismatch]

theorem unbalancedZeroTriple_not_balanced {K : ℕ} :
    unbalancedZeroTriple ∉ balancedTriples K := by
  simp only [balancedTriples, mem_product, mem_balancedPairs, unbalancedZeroTriple]
  intro h
  exact one_ne_zero h.1.1

theorem card_zeroHeight_gt_balanced {K : ℕ} (hK : 1 ≤ K) :
    (K / 2 + 1) ^ 3 < (zeroHeightTriples K).card := by
  have hsub := balancedTriples_subset_zeroHeight K
  have hcard := card_le_card hsub
  have hne : unbalancedZeroTriple ∈ zeroHeightTriples K \ balancedTriples K :=
    mem_sdiff.2 ⟨unbalancedZeroTriple_mem hK, unbalancedZeroTriple_not_balanced⟩
  have hlt : (balancedTriples K).card < (zeroHeightTriples K).card := by
    have : (zeroHeightTriples K).card = (balancedTriples K).card +
        (zeroHeightTriples K \ balancedTriples K).card := by
      rw [← card_union_of_disjoint (disjoint_sdiff), union_sdiff_of_subset hsub]
    have hpos : 0 < (zeroHeightTriples K \ balancedTriples K).card :=
      card_pos.2 ⟨unbalancedZeroTriple, hne⟩
    omega
  simpa [card_balancedTriples] using hlt

/-! ### Lifting triangle triples onto the discrete torus -/

/-- Embed non-negative integer rapidities as canonical torus representatives. -/
def ofAxisVals {N : ℕ} [NeZero N] (n m : Fin 3 → ℕ) : DiscreteTorsion N where
  n := fun a => (n a : ZMod N)
  m := fun a => (m a : ZMod N)

private theorem nat_lt_N_of_le_div_four {N k : ℕ} [NeZero N] (h : k ≤ N / 4) :
    k < N :=
  Nat.lt_of_le_of_lt h (Nat.div_lt_self (NeZero.pos N) (by decide : 1 < 4))

theorem ofAxisVals_val {N : ℕ} [NeZero N] {n m : Fin 3 → ℕ}
    (hn : ∀ a, n a ≤ N / 4) (hm : ∀ a, m a ≤ N / 4) (a : Fin 3) :
    ((ofAxisVals (N := N) n m).n a).val = n a ∧
      ((ofAxisVals (N := N) n m).m a).val = m a := by
  constructor
  · exact ZMod.val_natCast_of_lt (nat_lt_N_of_le_div_four (N := N) (hn a))
  · exact ZMod.val_natCast_of_lt (nat_lt_N_of_le_div_four (N := N) (hm a))

theorem ofAxisVals_admissible {N : ℕ} [NeZero N] {n m : Fin 3 → ℕ}
    (h : ∀ a, n a + m a ≤ N / 4) :
    IsAdmissible (ofAxisVals (N := N) n m) := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  have hnAll : ∀ a, n a ≤ N / 4 := fun a =>
    Nat.le_trans (Nat.le_add_right _ _) (h a)
  have hmAll : ∀ a, m a ≤ N / 4 := fun a =>
    Nat.le_trans (Nat.le_add_left _ _) (h a)
  have hval := ofAxisVals_val (N := N) hnAll hmAll a
  rw [hval.1, hval.2]
  have : 4 * (n a + m a) ≤ 4 * (N / 4) := Nat.mul_le_mul_left 4 (h a)
  exact this.trans (Nat.mul_div_le N 4)

theorem ofAxisVals_mismatch {N : ℕ} [NeZero N] {n m : Fin 3 → ℕ}
    (hn : ∀ a, n a ≤ N / 4) (hm : ∀ a, m a ≤ N / 4) :
    latticeMismatch (ofAxisVals (N := N) n m) =
      axisMismatch (n 0) (m 0) + axisMismatch (n 1) (m 1) + axisMismatch (n 2) (m 2) := by
  have h0 := ofAxisVals_val (N := N) hn hm 0
  have h1 := ofAxisVals_val (N := N) hn hm 1
  have h2 := ofAxisVals_val (N := N) hn hm 2
  unfold latticeMismatch axisMismatch
  simp only [Fin.sum_univ_three]
  rw [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem ofAxisVals_mass {N : ℕ} [NeZero N] {n m : Fin 3 → ℕ}
    (hn : ∀ a, n a ≤ N / 4) (hm : ∀ a, m a ≤ N / 4) :
    latticeMass (ofAxisVals (N := N) n m) =
      axisMass (n 0) (m 0) + axisMass (n 1) (m 1) + axisMass (n 2) (m 2) := by
  have h0 := ofAxisVals_val (N := N) hn hm 0
  have h1 := ofAxisVals_val (N := N) hn hm 1
  have h2 := ofAxisVals_val (N := N) hn hm 2
  unfold latticeMass axisMass
  simp only [Fin.sum_univ_three]
  rw [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

private theorem val_add_le_div_four {N : ℕ} {n m : ZMod N}
    (h : 4 * (n.val + m.val) ≤ N) :
    n.val + m.val ≤ N / 4 :=
  (Nat.le_div_iff_mul_le (by decide : 0 < (4 : ℕ))).2 (by
    simpa [mul_comm (4 : ℕ)] using h)

theorem latticeMismatch_mem_threeMismatchSet {N : ℕ} [NeZero N]
    (t : DiscreteTorsion N) (h : IsAdmissible t) :
    latticeMismatch t ∈ threeMismatchSet (N / 4) := by
  have hfour := (AdmissibleClass.isAdmissible_iff_four_le t).mp h
  rw [mem_threeMismatchSet]
  refine ⟨(t.n 0).val, (t.m 0).val, (t.n 1).val, (t.m 1).val,
    (t.n 2).val, (t.m 2).val, ?_, ?_, ?_, ?_⟩
  · exact val_add_le_div_four (hfour 0)
  · exact val_add_le_div_four (hfour 1)
  · exact val_add_le_div_four (hfour 2)
  · simp [latticeMismatch, axisMismatch, Fin.sum_univ_three]
    ring

/-! ### Global even lattice and mass comparison -/

theorem abs_latticeMismatch_le_latticeMass {N : ℕ} [NeZero N]
    (t : DiscreteTorsion N) :
    |latticeMismatch t| ≤ (latticeMass t : ℤ) := by
  have h0 := abs_axisMismatch_le_axisMass (t.n 0).val (t.m 0).val
  have h1 := abs_axisMismatch_le_axisMass (t.n 1).val (t.m 1).val
  have h2 := abs_axisMismatch_le_axisMass (t.n 2).val (t.m 2).val
  have htri :
      |axisMismatch (t.n 0).val (t.m 0).val +
          axisMismatch (t.n 1).val (t.m 1).val +
          axisMismatch (t.n 2).val (t.m 2).val| ≤
        |axisMismatch (t.n 0).val (t.m 0).val| +
          |axisMismatch (t.n 1).val (t.m 1).val| +
          |axisMismatch (t.n 2).val (t.m 2).val| := by
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  have hsum :
      |axisMismatch (t.n 0).val (t.m 0).val| +
          |axisMismatch (t.n 1).val (t.m 1).val| +
          |axisMismatch (t.n 2).val (t.m 2).val| ≤
        (axisMass (t.n 0).val (t.m 0).val : ℤ) +
          (axisMass (t.n 1).val (t.m 1).val : ℤ) +
          (axisMass (t.n 2).val (t.m 2).val : ℤ) := by
    gcongr
  have hΔ : latticeMismatch t =
      axisMismatch (t.n 0).val (t.m 0).val +
        axisMismatch (t.n 1).val (t.m 1).val +
        axisMismatch (t.n 2).val (t.m 2).val := by
    simp [latticeMismatch, axisMismatch, Fin.sum_univ_three]
    ring
  have hMass : (latticeMass t : ℤ) =
      (axisMass (t.n 0).val (t.m 0).val : ℤ) +
        (axisMass (t.n 1).val (t.m 1).val : ℤ) +
        (axisMass (t.n 2).val (t.m 2).val : ℤ) := by
    unfold latticeMass axisMass
    simp only [Fin.sum_univ_three]
    push_cast; rfl
  rw [hΔ, hMass]
  exact htri.trans hsum

theorem latticeMismatch_modEq_latticeMass {N : ℕ} [NeZero N]
    (t : DiscreteTorsion N) :
    latticeMismatch t ≡ (latticeMass t : ℤ) [ZMOD 2] := by
  have h0 := axisMismatch_modEq_axisMass (t.n 0).val (t.m 0).val
  have h1 := axisMismatch_modEq_axisMass (t.n 1).val (t.m 1).val
  have h2 := axisMismatch_modEq_axisMass (t.n 2).val (t.m 2).val
  have hsum := (h0.add h1).add h2
  have hΔ : latticeMismatch t =
      axisMismatch (t.n 0).val (t.m 0).val +
        axisMismatch (t.n 1).val (t.m 1).val +
        axisMismatch (t.n 2).val (t.m 2).val := by
    simp [latticeMismatch, axisMismatch, Fin.sum_univ_three]
    ring
  have hMass : (latticeMass t : ℤ) =
      (axisMass (t.n 0).val (t.m 0).val : ℤ) +
        (axisMass (t.n 1).val (t.m 1).val : ℤ) +
        (axisMass (t.n 2).val (t.m 2).val : ℤ) := by
    unfold latticeMass axisMass
    simp only [Fin.sum_univ_three]
    push_cast; rfl
  rwa [hΔ, hMass]

theorem latticeMass_eq_zero_iff {N : ℕ} [NeZero N] (t : DiscreteTorsion N) :
    latticeMass t = 0 ↔ ∀ a : Fin 3, t.n a = 0 ∧ t.m a = 0 := by
  constructor
  · intro h
    have hsum : ∀ a, (t.n a).val ^ 2 + (t.m a).val ^ 2 = 0 := by
      have hs : ∑ a : Fin 3, ((t.n a).val ^ 2 + (t.m a).val ^ 2) = 0 := by
        simpa [latticeMass] using h
      have hnn : ∀ i ∈ (univ : Finset (Fin 3)),
          0 ≤ (t.n i).val ^ 2 + (t.m i).val ^ 2 := fun _ _ => Nat.zero_le _
      intro a
      exact (sum_eq_zero_iff_of_nonneg hnn).mp hs a (mem_univ a)
    intro a
    have ⟨hn2, hm2⟩ := Nat.add_eq_zero_iff.mp (hsum a)
    have hn : (t.n a).val = 0 := (Nat.pow_eq_zero.mp hn2).1
    have hm : (t.m a).val = 0 := (Nat.pow_eq_zero.mp hm2).1
    exact ⟨(ZMod.val_eq_zero (t.n a)).mp hn, (ZMod.val_eq_zero (t.m a)).mp hm⟩
  · intro h
    unfold latticeMass
    apply Finset.sum_eq_zero
    intro a _
    simp [(h a).1, (h a).2]

/-! ### Attained gap `Δ = ±1` and the discrete ceiling iff -/

/-- Single-axis unit hyperbolic seed: mismatch `1`. -/
def unitHyperbolicDiscrete (N : ℕ) [NeZero N] : DiscreteTorsion N where
  n := fun a => if a = 0 then 1 else 0
  m := fun _ => 0

/-- Single-axis unit elliptic seed: mismatch `-1`. -/
def unitEllipticDiscrete (N : ℕ) [NeZero N] : DiscreteTorsion N where
  n := fun _ => 0
  m := fun a => if a = 0 then 1 else 0

private theorem zmod_val_one {N : ℕ} [NeZero N] (hN : 1 < N) :
    (1 : ZMod N).val = 1 :=
  have : Fact (1 < N) := ⟨hN⟩
  ZMod.val_one N

theorem unitHyperbolicDiscrete_admissible {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    IsAdmissible (unitHyperbolicDiscrete N) := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  have h1 : 1 < N := lt_of_lt_of_le (by decide : 1 < 4) hN
  simp only [unitHyperbolicDiscrete]
  fin_cases a
  · simp [zmod_val_one h1, ZMod.val_zero]; linarith
  · simp [ZMod.val_zero]
  · simp [ZMod.val_zero]

theorem unitEllipticDiscrete_admissible {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    IsAdmissible (unitEllipticDiscrete N) := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  have h1 : 1 < N := lt_of_lt_of_le (by decide : 1 < 4) hN
  simp only [unitEllipticDiscrete]
  fin_cases a
  · simp [zmod_val_one h1, ZMod.val_zero]; linarith
  · simp [ZMod.val_zero]
  · simp [ZMod.val_zero]

theorem latticeMismatch_unitHyperbolicDiscrete {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    latticeMismatch (unitHyperbolicDiscrete N) = 1 := by
  have h1 : 1 < N := lt_of_lt_of_le (by decide : 1 < 4) hN
  simp only [latticeMismatch, unitHyperbolicDiscrete, Fin.sum_univ_three]
  simp [zmod_val_one h1, ZMod.val_zero]

theorem latticeMismatch_unitEllipticDiscrete {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    latticeMismatch (unitEllipticDiscrete N) = -1 := by
  have h1 : 1 < N := lt_of_lt_of_le (by decide : 1 < 4) hN
  simp only [latticeMismatch, unitEllipticDiscrete, Fin.sum_univ_three]
  simp [zmod_val_one h1, ZMod.val_zero]

theorem exists_admissible_mismatch_one {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    ∃ t : DiscreteTorsion N, IsAdmissible t ∧ latticeMismatch t = 1 :=
  ⟨unitHyperbolicDiscrete N, unitHyperbolicDiscrete_admissible hN,
    latticeMismatch_unitHyperbolicDiscrete hN⟩

theorem exists_admissible_mismatch_neg_one {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    ∃ t : DiscreteTorsion N, IsAdmissible t ∧ latticeMismatch t = -1 :=
  ⟨unitEllipticDiscrete N, unitEllipticDiscrete_admissible hN,
    latticeMismatch_unitEllipticDiscrete hN⟩

/-- For `N ≥ 4` the universal floor `16/(3N²)` is attained. -/
theorem torsion_gap_attained {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    ∃ t : DiscreteTorsion N, IsAdmissible t ∧
      |JNormalized (toTorsionParams t)| = (16 : ℝ) / (3 * (N : ℝ) ^ 2) := by
  refine ⟨unitHyperbolicDiscrete N, unitHyperbolicDiscrete_admissible hN, ?_⟩
  rw [JNormalized_eq_sixteen_lattice, latticeMismatch_unitHyperbolicDiscrete hN]
  simp [abs_of_pos (by positivity : (0 : ℝ) < 16 / (3 * (N : ℝ) ^ 2))]

/-- Cross-axis cancellation on the torus: vanishing `J` with positive mass,
not from balanced axes. -/
def unbalancedZeroDiscrete (N : ℕ) [NeZero N] : DiscreteTorsion N where
  n := fun a => if a = 0 then 1 else 0
  m := fun a => if a = 1 then 1 else 0

theorem unbalancedZeroDiscrete_admissible {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    IsAdmissible (unbalancedZeroDiscrete N) := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  have h1 : 1 < N := lt_of_lt_of_le (by decide : 1 < 4) hN
  simp only [unbalancedZeroDiscrete]
  fin_cases a <;> simp [zmod_val_one h1, ZMod.val_zero] <;> linarith

theorem latticeMismatch_unbalancedZeroDiscrete {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    latticeMismatch (unbalancedZeroDiscrete N) = 0 := by
  have h1 : 1 < N := lt_of_lt_of_le (by decide : 1 < 4) hN
  simp only [latticeMismatch, unbalancedZeroDiscrete, Fin.sum_univ_three]
  simp [zmod_val_one h1, ZMod.val_zero]

theorem latticeMass_unbalancedZeroDiscrete {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    latticeMass (unbalancedZeroDiscrete N) = 2 := by
  have h1 : 1 < N := lt_of_lt_of_le (by decide : 1 < 4) hN
  simp only [latticeMass, unbalancedZeroDiscrete, Fin.sum_univ_three]
  simp [zmod_val_one h1, ZMod.val_zero]

theorem exists_unbalanced_zeroHeight_massive {N : ℕ} [NeZero N] (hN : 4 ≤ N) :
    ∃ t : DiscreteTorsion N, IsAdmissible t ∧ latticeMismatch t = 0 ∧
      0 < latticeMass t ∧ ¬ (∀ a, t.n a = t.m a) := by
  refine ⟨unbalancedZeroDiscrete N, unbalancedZeroDiscrete_admissible hN,
    latticeMismatch_unbalancedZeroDiscrete hN, ?_, ?_⟩
  · rw [latticeMass_unbalancedZeroDiscrete hN]; norm_num
  · intro h
    have h1 : 1 < N := lt_of_lt_of_le (by decide : 1 < 4) hN
    have h0 := h 0
    simp only [unbalancedZeroDiscrete] at h0
    have : (1 : ZMod N) = 0 := by simpa using h0
    have hval : (1 : ZMod N).val = 0 := by simp [this]
    rw [zmod_val_one h1] at hval
    exact one_ne_zero hval

/-! ### Discrete ceiling equality -/

private theorem latticeMismatch_eq_sum_axis {N : ℕ} [NeZero N] (t : DiscreteTorsion N) :
    latticeMismatch t =
      axisMismatch (t.n 0).val (t.m 0).val +
        axisMismatch (t.n 1).val (t.m 1).val +
        axisMismatch (t.n 2).val (t.m 2).val := by
  simp [latticeMismatch, axisMismatch, Fin.sum_univ_three]
  ring

theorem abs_latticeMismatch_eq_ceiling_iff {N : ℕ} [NeZero N]
    (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |latticeMismatch t| = 3 * ((N / 4 : ℕ) : ℤ) ^ 2 ↔
      (∀ a, (t.n a).val = N / 4 ∧ (t.m a).val = 0) ∨
        (∀ a, (t.n a).val = 0 ∧ (t.m a).val = N / 4) := by
  have hfour := (AdmissibleClass.isAdmissible_iff_four_le t).mp h
  have h0 := val_add_le_div_four (hfour 0)
  have h1 := val_add_le_div_four (hfour 1)
  have h2 := val_add_le_div_four (hfour 2)
  have hiff := abs_three_axis_eq_ceiling_iff (K := N / 4) h0 h1 h2
  constructor
  · intro heq
    have : |axisMismatch (t.n 0).val (t.m 0).val +
        axisMismatch (t.n 1).val (t.m 1).val +
        axisMismatch (t.n 2).val (t.m 2).val| =
        3 * ((N / 4 : ℕ) : ℤ) ^ 2 := by
      rwa [← latticeMismatch_eq_sum_axis]
    have hall := hiff.mp this
    rcases hall with hhyp | hell
    · refine Or.inl ?_
      intro a; fin_cases a <;> simp [hhyp]
    · refine Or.inr ?_
      intro a; fin_cases a <;> simp [hell]
  · intro hwall
    have : |axisMismatch (t.n 0).val (t.m 0).val +
        axisMismatch (t.n 1).val (t.m 1).val +
        axisMismatch (t.n 2).val (t.m 2).val| =
        3 * ((N / 4 : ℕ) : ℤ) ^ 2 :=
      hiff.mpr <| by
        rcases hwall with hhyp | hell
        · exact Or.inl ⟨(hhyp 0).1, (hhyp 0).2, (hhyp 1).1, (hhyp 1).2,
            (hhyp 2).1, (hhyp 2).2⟩
        · exact Or.inr ⟨(hell 0).1, (hell 0).2, (hell 1).1, (hell 1).2,
            (hell 2).1, (hell 2).2⟩
    rwa [← latticeMismatch_eq_sum_axis] at this

theorem JNormalized_eq_sharp_iff {N : ℕ} [NeZero N]
    (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |JNormalized (toTorsionParams t)| = ((4 * (N / 4 : ℕ) : ℝ) / N) ^ 2 ↔
      (∀ a, (t.n a).val = N / 4 ∧ (t.m a).val = 0) ∨
        (∀ a, (t.n a).val = 0 ∧ (t.m a).val = N / 4) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hcoef : 0 < (16 : ℝ) / (3 * (N : ℝ) ^ 2) := by positivity
  have hscale :
      |JNormalized (toTorsionParams t)| =
        ((16 : ℝ) / (3 * (N : ℝ) ^ 2)) * |(latticeMismatch t : ℝ)| := by
    rw [JNormalized_eq_sixteen_lattice, abs_mul, abs_of_pos hcoef]
  have hceil : ((4 * (N / 4 : ℕ) : ℝ) / N) ^ 2 =
      ((16 : ℝ) / (3 * (N : ℝ) ^ 2)) * (3 * ((N / 4 : ℕ) : ℝ) ^ 2) := by
    field_simp [hN]; ring
  have hiffInt := abs_latticeMismatch_eq_ceiling_iff t h
  constructor
  · intro heq
    have : |(latticeMismatch t : ℝ)| = 3 * ((N / 4 : ℕ) : ℝ) ^ 2 := by
      have hmul := heq
      rw [hscale, hceil] at hmul
      exact mul_left_cancel₀ hcoef.ne' hmul
    have hint : |latticeMismatch t| = 3 * ((N / 4 : ℕ) : ℤ) ^ 2 := by
      have hL : (|latticeMismatch t| : ℤ) = |latticeMismatch t| := rfl
      have : ((|latticeMismatch t| : ℤ) : ℝ) = 3 * ((N / 4 : ℕ) : ℝ) ^ 2 := by
        rwa [Int.cast_abs]
      have hrhs : ((3 * ((N / 4 : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) =
          3 * ((N / 4 : ℕ) : ℝ) ^ 2 := by norm_cast
      have : ((|latticeMismatch t| : ℤ) : ℝ) = ((3 * ((N / 4 : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) :=
        this.trans hrhs.symm
      exact_mod_cast this
    exact hiffInt.mp hint
  · intro hwall
    have hint := hiffInt.mpr hwall
    rw [hscale, hceil]
    have : |(latticeMismatch t : ℝ)| = 3 * ((N / 4 : ℕ) : ℝ) ^ 2 := by
      have h1 : (|latticeMismatch t| : ℝ) =
          ((3 * ((N / 4 : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) := by exact_mod_cast hint
      have h2 : ((3 * ((N / 4 : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) =
          3 * ((N / 4 : ℕ) : ℝ) ^ 2 := by norm_cast
      exact h1.trans h2
    rw [this]

end Framework

end DstDiophantine
