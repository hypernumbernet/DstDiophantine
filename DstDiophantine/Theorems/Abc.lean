import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.nativeDecide false

/-!
# Phase 5–7: abc conjecture (quality / modular bridge)

We formalise Chapter 7 of `dst-diophantine.tex` as a **quality–torsional height**
argument on the pure-boost mismatch model
`Ω = pureBoost(2(log c − log rad(abc)))`, together with a finite computational
certificate and bridges recovering the classical Oesterlé–Masser statement.

## Paper gap (not closed)

Classical abc (`∀ ε > 0, ∃ Cε, c ≤ Cε · rad(abc)^{1+ε}` for primitive triples) is
**not** claimed unconditionally. Dual-sector rotors `R_dual(p)`, Lemma
`radical-dual`, and the paper's `O(1)` error in
`θ = 2 log rad · (q − 1) + O(1)` are left informal. The Lean model drops the
`O(1)` term and treats quality–height as an exact pure-boost identity.

Continuous `AbcAdmissibleBridge` is **diagnostic only**: it asks for an
admissible configuration already past the model quality ceiling, which is
impossible (`AbcAdmissibleBridge_false`). The live programme is
`AbcModularBridge`: a **solution-dependent** modular witness on
`quantizeAbcMismatch`, together with the residual conformal-gauge gap
`ConformalGaugeAdmissible` (provisionally identified with the PGA real-scale
cone). Legacy coarse real-scale witnesses stay equation-independently empty.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Operations Real ModularAmplification
open Finset
open _root_.DstDiophantine.Embedding
open _root_.DstDiophantine.Framework

/-! ### Radical (local; mathlib `v4.34.0-rc1` has no `Nat.radical`) -/

/-- Product of the distinct prime factors of `n` (squarefree kernel). -/
def abcRadical (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

theorem abcRadical_one : abcRadical 1 = 1 := by
  simp [abcRadical]

theorem abcRadical_pos (n : ℕ) : 0 < abcRadical n :=
  Finset.prod_pos fun _ hp => Nat.pos_of_mem_primeFactors hp

theorem abcRadical_ne_zero (n : ℕ) : abcRadical n ≠ 0 :=
  ne_of_gt (abcRadical_pos n)

theorem one_le_abcRadical (n : ℕ) : 1 ≤ abcRadical n :=
  Nat.succ_le_of_lt (abcRadical_pos n)

theorem two_le_abcRadical_of_one_lt {n : ℕ} (hn : 1 < n) : 2 ≤ abcRadical n := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  obtain ⟨p, hp⟩ := hne
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hle : p ≤ abcRadical n :=
    Finset.single_le_prod'
      (fun q hq => Nat.succ_le_of_lt (Nat.pos_of_mem_primeFactors hq)) hp
  exact le_trans hp2 hle

theorem abcRadical_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : Nat.Coprime a b) :
    abcRadical (a * b) = abcRadical a * abcRadical b := by
  unfold abcRadical
  have hdisj := hab.disjoint_primeFactors
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hdisj]

theorem abcRadical_mul_triple {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    abcRadical (a * b * c) = abcRadical a * abcRadical b * abcRadical c := by
  have ha0 : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha
  have hb0 : b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hc0 : c ≠ 0 := Nat.pos_iff_ne_zero.mp hc
  have habc : Nat.Coprime (a * b) c := Nat.Coprime.mul_left hac hbc
  have hmul_ab : a * b ≠ 0 := mul_ne_zero ha0 hb0
  calc abcRadical (a * b * c)
      = abcRadical (a * b) * abcRadical c := abcRadical_mul_of_coprime hmul_ab hc0 habc
    _ = abcRadical a * abcRadical b * abcRadical c := by
        rw [abcRadical_mul_of_coprime ha0 hb0 hab]

/-! ### Classical abc triples -/

/-- A primitive positive abc triple: `a + b = c` with `Nat.Coprime a b`. -/
def IsAbcTriple (a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b

theorem isAbcTriple_c_pos {a b c : ℕ} (h : IsAbcTriple a b c) : 0 < c := by
  have : 0 < a + b := Nat.add_pos_left h.1 b
  rwa [h.2.2.1] at this

theorem isAbcTriple_c_ne_zero {a b c : ℕ} (h : IsAbcTriple a b c) : c ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (isAbcTriple_c_pos h)

theorem isAbcTriple_mul_one_lt {a b c : ℕ} (h : IsAbcTriple a b c) :
    1 < a * b * c := by
  have ha : 1 ≤ a := Nat.succ_le_of_lt h.1
  have hb : 1 ≤ b := Nat.succ_le_of_lt h.2.1
  have hc : 2 ≤ c := by
    have : 2 ≤ a + b := Nat.add_le_add ha hb
    rwa [h.2.2.1] at this
  have hab : 1 ≤ a * b := Nat.mul_le_mul ha hb
  calc
    1 < 2 := by decide
    _ ≤ c := hc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * b * c := Nat.mul_le_mul_right c hab

theorem isAbcTriple_radical_two_le {a b c : ℕ} (h : IsAbcTriple a b c) :
    2 ≤ abcRadical (a * b * c) :=
  two_le_abcRadical_of_one_lt (isAbcTriple_mul_one_lt h)

theorem isAbcTriple_coprime_ac {a b c : ℕ} (h : IsAbcTriple a b c) : Nat.Coprime a c := by
  have hab := h.2.2.2
  rw [← h.2.2.1, Nat.add_comm]
  exact Nat.coprime_add_self_right.mpr hab

theorem isAbcTriple_coprime_bc {a b c : ℕ} (h : IsAbcTriple a b c) : Nat.Coprime b c := by
  have hab := h.2.2.2
  rw [← h.2.2.1]
  exact Nat.coprime_comm.mp (Nat.coprime_add_self_left.mpr hab)

theorem isAbcTriple_gcd_one {a b c : ℕ} (h : IsAbcTriple a b c) :
    Nat.gcd a (Nat.gcd b c) = 1 := by
  have hab : Nat.gcd a b = 1 := h.2.2.2
  have hdiv : Nat.gcd a (Nat.gcd b c) ∣ Nat.gcd a b :=
    Nat.gcd_dvd_gcd_of_dvd_right _ (Nat.gcd_dvd_left b c)
  exact Nat.dvd_one.mp (hab ▸ hdiv)

theorem isAbcTriple_radical_mul {a b c : ℕ} (h : IsAbcTriple a b c) :
    abcRadical (a * b * c) =
      abcRadical a * abcRadical b * abcRadical c :=
  abcRadical_mul_triple h.1 h.2.1 (isAbcTriple_c_pos h)
    h.2.2.2 (isAbcTriple_coprime_ac h) (isAbcTriple_coprime_bc h)

/-! ### Motor encoding -/

theorem abc_sum_iff_motor (a b c : ℤ) :
    a + b = c ↔ powerSumMotor (Framework.abcEquation a b c) = 1 :=
  (Framework.abcMotor_one_iff a b c).symm

theorem abc_solution_iff_motor {a b c : ℕ} (h : IsAbcTriple a b c) :
    powerSumMotor (Framework.abcEquation (a : ℤ) (b : ℤ) (c : ℤ)) = 1 := by
  rw [Framework.abcMotor_one_iff]
  exact_mod_cast h.2.2.1

/-! ### Quality -/

/-- Classical quality `q(a,b,c) = log c / log rad(abc)`. -/
noncomputable def abcQuality (a b c : ℕ) : ℝ :=
  Real.log c / Real.log (abcRadical (a * b * c))

theorem log_radical_pos {a b c : ℕ} (h : IsAbcTriple a b c) :
    0 < Real.log (abcRadical (a * b * c)) := by
  have hrad : 2 ≤ abcRadical (a * b * c) := isAbcTriple_radical_two_le h
  have hcast : (2 : ℝ) ≤ (abcRadical (a * b * c) : ℝ) := Nat.cast_le.mpr hrad
  exact Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hcast)

theorem log_c_nonneg {a b c : ℕ} (h : IsAbcTriple a b c) :
    0 ≤ Real.log c := by
  have hc : 1 ≤ c := Nat.succ_le_of_lt (isAbcTriple_c_pos h)
  exact Real.log_nonneg (Nat.one_le_cast.mpr hc)

theorem abcQuality_le_iff_rpow {a b c : ℕ} (h : IsAbcTriple a b c) {t : ℝ}
    (_ht : 0 ≤ t) :
    abcQuality a b c ≤ t ↔
      (c : ℝ) ≤ (abcRadical (a * b * c) : ℝ) ^ t := by
  set R : ℝ := (abcRadical (a * b * c) : ℝ)
  have hRpos : 0 < R := Nat.cast_pos.mpr (abcRadical_pos _)
  have hLpos : 0 < Real.log R := by
    change 0 < Real.log (abcRadical (a * b * c))
    exact log_radical_pos h
  have hcpos : 0 < (c : ℝ) := Nat.cast_pos.mpr (isAbcTriple_c_pos h)
  constructor
  · intro hq
    have hlogc : Real.log c ≤ t * Real.log R := by
      unfold abcQuality at hq
      exact (div_le_iff₀ hLpos).mp hq
    have : Real.log c ≤ Real.log (R ^ t) := by
      rwa [Real.log_rpow hRpos t]
    exact (Real.log_le_log_iff hcpos (Real.rpow_pos_of_pos hRpos t)).mp this
  · intro hpow
    unfold abcQuality
    have hlog := (Real.log_le_log_iff hcpos (Real.rpow_pos_of_pos hRpos t)).mpr hpow
    have hlog' : Real.log c ≤ t * Real.log R := by
      rwa [Real.log_rpow hRpos t] at hlog
    exact (div_le_iff₀ hLpos).mpr hlog'

/-! ### Pure-boost mismatch height -/

/-- Pure-boost parameters encoding usual vs radical imbalance. -/
noncomputable def abcMismatchParams (a b c : ℕ) : TorsionParams :=
  pureBoost (2 * (Real.log c - Real.log (abcRadical (a * b * c))))

/-- Normalised torsional height of an abc triple in the pure-boost model. -/
noncomputable def abcHeight (a b c : ℕ) : ℝ :=
  |JNormalized (abcMismatchParams a b c)|

theorem abcHeight_eq (a b c : ℕ) :
    abcHeight a b c =
      (16 / (3 * Real.pi ^ 2)) *
        (Real.log c - Real.log (abcRadical (a * b * c))) ^ 2 := by
  unfold abcHeight abcMismatchParams
  set δ : ℝ := Real.log c - Real.log (abcRadical (a * b * c))
  have hnonneg : 0 ≤ JNormalized (pureBoost (2 * δ)) :=
    JNormalized_pureBoost_nonneg (2 * δ)
  rw [abs_of_nonneg hnonneg, JNormalized_coef]
  simp only [pureBoost, Fin.sum_univ_three, pow_two, zero_pow two_ne_zero, sub_zero, mul_zero,
    add_zero]
  ring

/-- Quality–height identity (exact pure-boost model; paper drops `O(1)`). -/
theorem abcHeight_eq_quality {a b c : ℕ} (h : IsAbcTriple a b c) :
    abcHeight a b c =
      (16 / (3 * Real.pi ^ 2)) *
        (Real.log (abcRadical (a * b * c))) ^ 2 * (abcQuality a b c - 1) ^ 2 := by
  rw [abcHeight_eq]
  set R : ℝ := (abcRadical (a * b * c) : ℝ)
  set L : ℝ := Real.log R
  set Lc : ℝ := Real.log c
  have hLne : L ≠ 0 := ne_of_gt (by
    change 0 < Real.log (abcRadical (a * b * c))
    exact log_radical_pos h)
  have hdiff : Lc - L = L * (Lc / L - 1) := by field_simp [hLne]
  unfold abcQuality
  change
      (16 / (3 * Real.pi ^ 2)) * (Lc - L) ^ 2 =
        (16 / (3 * Real.pi ^ 2)) * L ^ 2 * (Lc / L - 1) ^ 2
  rw [hdiff]
  ring

/-- Explicit coefficient `c₁` in `H = c₁ (q − 1)²`. -/
noncomputable def abcHeightCoef (rad : ℕ) : ℝ :=
  (16 / (3 * Real.pi ^ 2)) * (Real.log rad) ^ 2

theorem abcHeightCoef_pos {a b c : ℕ} (h : IsAbcTriple a b c) :
    0 < abcHeightCoef (abcRadical (a * b * c)) := by
  unfold abcHeightCoef
  have hLpos : 0 < Real.log (abcRadical (a * b * c)) := log_radical_pos h
  positivity

theorem abcHeight_eq_coef {a b c : ℕ} (h : IsAbcTriple a b c) :
    abcHeight a b c =
      abcHeightCoef (abcRadical (a * b * c)) * (abcQuality a b c - 1) ^ 2 := by
  rw [abcHeight_eq_quality h, abcHeightCoef]

/-! ### Admissible quality ceiling -/

/-- Model quality ceiling forced by `|JNormalized| ≤ 1` when `rad > 1`. -/
noncomputable def abcQualityCeiling (rad : ℕ) : ℝ :=
  1 + Real.sqrt ((3 * Real.pi ^ 2) / (16 * (Real.log rad) ^ 2))

theorem abcQualityCeiling_eq {rad : ℕ} (hrad : 1 < rad) :
    abcQualityCeiling rad = 1 + Real.sqrt (1 / abcHeightCoef rad) := by
  have h2 : 2 ≤ rad := Nat.succ_le_of_lt hrad
  have hLpos : 0 < Real.log rad :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (Nat.cast_le.mpr h2))
  have hLne : Real.log rad ≠ 0 := ne_of_gt hLpos
  unfold abcQualityCeiling abcHeightCoef
  congr 1
  field_simp [hLne]

theorem abc_quality_bound_of_admissible {a b c : ℕ} (h : IsAbcTriple a b c)
    (hadm : IsAdmissibleContinuous (abcMismatchParams a b c)) :
    abcQuality a b c ≤ abcQualityCeiling (abcRadical (a * b * c)) := by
  have hbound := torsion_bound_continuous _ hadm
  have hH : abcHeight a b c ≤ 1 := by
    unfold abcHeight
    exact hbound
  rw [abcHeight_eq_coef h] at hH
  set R := abcRadical (a * b * c)
  set q := abcQuality a b c
  have hcoef_pos : 0 < abcHeightCoef R := abcHeightCoef_pos h
  have hsq : (q - 1) ^ 2 ≤ 1 / abcHeightCoef R :=
    (le_div_iff₀ hcoef_pos).mpr (by linarith [hH])
  have hsqrt : q - 1 ≤ Real.sqrt (1 / abcHeightCoef R) := by
    cases le_total (q - 1) 0 with
    | inl hneg => exact le_trans hneg (Real.sqrt_nonneg _)
    | inr hnonneg =>
      calc
        q - 1 = Real.sqrt ((q - 1) ^ 2) := (Real.sqrt_sq hnonneg).symm
        _ ≤ Real.sqrt (1 / abcHeightCoef R) := Real.sqrt_le_sqrt hsq
  have hrad_lt : 1 < R :=
    lt_of_lt_of_le (by decide : (1 : ℕ) < 2) (isAbcTriple_radical_two_le h)
  have hceil : abcQualityCeiling R = 1 + Real.sqrt (1 / abcHeightCoef R) :=
    abcQualityCeiling_eq hrad_lt
  linarith [hsqrt, hceil]

/-- Exceeding the model ceiling contradicts continuous admissibility. -/
theorem abc_amplification_contradiction {a b c : ℕ} (h : IsAbcTriple a b c)
    (hadm : IsAdmissibleContinuous (abcMismatchParams a b c))
    (hbig : abcQualityCeiling (abcRadical (a * b * c)) < abcQuality a b c) :
    False :=
  not_le_of_gt hbig (abc_quality_bound_of_admissible h hadm)

/-- Contrapositive form of the quality ceiling. -/
theorem abc_quality_gt_ceiling_not_admissible {a b c : ℕ} (h : IsAbcTriple a b c)
    (hbig : abcQualityCeiling (abcRadical (a * b * c)) < abcQuality a b c) :
    ¬ IsAdmissibleContinuous (abcMismatchParams a b c) :=
  fun hadm => abc_amplification_contradiction h hadm hbig

/-- Log-gap form of quality: `1 < q ↔ rad(abc) < c`. -/
theorem one_lt_abcQuality_iff {a b c : ℕ} (h : IsAbcTriple a b c) :
    1 < abcQuality a b c ↔ abcRadical (a * b * c) < c := by
  set R := abcRadical (a * b * c)
  have hRpos : 0 < (R : ℝ) := Nat.cast_pos.mpr (abcRadical_pos _)
  have hLpos : 0 < Real.log (R : ℝ) := by
    change 0 < Real.log (abcRadical (a * b * c) : ℝ)
    exact log_radical_pos h
  have hcpos : 0 < (c : ℝ) := Nat.cast_pos.mpr (isAbcTriple_c_pos h)
  constructor
  · intro hq
    unfold abcQuality at hq
    have hlog : Real.log (R : ℝ) < Real.log (c : ℝ) := (one_lt_div hLpos).mp hq
    exact Nat.cast_lt.mp ((Real.log_lt_log_iff hRpos hcpos).mp hlog)
  · intro hlt
    unfold abcQuality
    have hlog : Real.log (R : ℝ) < Real.log (c : ℝ) :=
      (Real.log_lt_log_iff hRpos hcpos).mpr (Nat.cast_lt.mpr hlt)
    exact (one_lt_div hLpos).mpr hlog

/-- Pure-boost rapidity of an abc mismatch: `θ = 2 (q − 1) log rad`. -/
theorem abcMismatch_rapidity {a b c : ℕ} (h : IsAbcTriple a b c) :
    2 * (Real.log c - Real.log (abcRadical (a * b * c))) =
      2 * (abcQuality a b c - 1) * Real.log (abcRadical (a * b * c)) := by
  set R : ℝ := (abcRadical (a * b * c) : ℝ)
  set L : ℝ := Real.log R
  set Lc : ℝ := Real.log c
  have hLne : L ≠ 0 := ne_of_gt (by
    change 0 < Real.log (abcRadical (a * b * c))
    exact log_radical_pos h)
  have hdiff : Lc - L = L * (Lc / L - 1) := by field_simp [hLne]
  unfold abcQuality
  change 2 * (Lc - L) = 2 * (Lc / L - 1) * L
  rw [hdiff]
  ring

/-- Continuous admissibility of the abc pure-boost seed. -/
theorem isAdmissibleContinuous_abcMismatch_iff {a b c : ℕ} (_h : IsAbcTriple a b c) :
    IsAdmissibleContinuous (abcMismatchParams a b c) ↔
      0 ≤ Real.log c - Real.log (abcRadical (a * b * c)) ∧
        Real.log c - Real.log (abcRadical (a * b * c)) ≤ Real.pi / 4 := by
  set δ : ℝ := Real.log c - Real.log (abcRadical (a * b * c))
  unfold abcMismatchParams
  rw [isAdmissibleContinuous_pureBoost_iff]
  change (0 ≤ 2 * δ ∧ 2 * δ ≤ Real.pi / 2) ↔ (0 ≤ δ ∧ δ ≤ Real.pi / 4)
  constructor
  · rintro ⟨h0, hπ⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h0, hπ⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-! ### Discrete ceiling (paper `Q(N)` shape) -/

/--
Discrete quality ceiling `1 + √(1/(c₁ ε_N))` with
`ε_N = 16/(3N²)` from `discrete_nonzero_height_lb`.
-/
noncomputable def discreteAbcCeiling (N rad : ℕ) : ℝ :=
  1 + Real.sqrt (1 / (abcHeightCoef rad * ((16 : ℝ) / (3 * (N : ℝ) ^ 2))))

/-- Under continuous admissibility the model ceiling applies (discrete form of Ch.7). -/
theorem discrete_abc_bound {a b c : ℕ} (h : IsAbcTriple a b c)
    (hadm : IsAdmissibleContinuous (abcMismatchParams a b c)) :
    abcQuality a b c ≤ abcQualityCeiling (abcRadical (a * b * c)) :=
  abc_quality_bound_of_admissible h hadm

/-- Nonzero discrete seeds are at least `ε_N` tall (shared core). -/
theorem discrete_abc_height_lb {N : ℕ} [NeZero N] (t : DiscreteTorsion N)
    (hne : latticeMismatch t ≠ 0) :
    (16 : ℝ) / (3 * (N : ℝ) ^ 2) ≤ |JNormalized (toTorsionParams t)| :=
  Framework.discrete_nonzero_height_lb t hne

/-! ### Finite computational certificate -/

/-- Decidable radical-power bound for a single candidate pair. -/
def abcRadicalPowOk (a b c : ℕ) : Bool :=
  decide (c ≤ (abcRadical (a * b * c)) ^ 2)

/-- All primitive triples with `c ≤ N` satisfy `c ≤ rad(abc)²`. -/
def allAbcRadicalPowBoundUpTo (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun c =>
    (List.range (c + 1)).all fun a =>
      let b := c - a
      if decide (0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b) then
        abcRadicalPowOk a b c
      else
        true

theorem allAbcRadicalPowBoundUpTo_sound {N : ℕ}
    (hcert : allAbcRadicalPowBoundUpTo N = true) :
    ∀ a b c : ℕ, IsAbcTriple a b c → c ≤ N →
      c ≤ (abcRadical (a * b * c)) ^ 2 := by
  intro a b c h hcN
  have hc_lt : c < N + 1 := Nat.lt_succ_of_le hcN
  have hall_c := (List.all_eq_true.mp hcert) c (List.mem_range.mpr hc_lt)
  have ha_le : a ≤ c := by
    rw [← h.2.2.1]
    exact Nat.le_add_right a b
  have ha_mem : a ∈ List.range (c + 1) := List.mem_range.mpr (Nat.lt_succ_of_le ha_le)
  have hall_a := (List.all_eq_true.mp hall_c) a ha_mem
  have hb_eq : c - a = b := by
    rw [← h.2.2.1, Nat.add_sub_cancel_left]
  have hcond : (0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b) :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  have hcondB : decide (0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b) = true :=
    decide_eq_true_eq.mpr hcond
  simp only [hb_eq, hcondB, ↓reduceIte, abcRadicalPowOk, decide_eq_true_eq] at hall_a
  exact hall_a

/-- Chapter 7 finite-exploration certificate for targets up to `100`. -/
theorem abc_radical_pow_of_le_hundred {a b c : ℕ} (h : IsAbcTriple a b c)
    (hc : c ≤ 100) : c ≤ (abcRadical (a * b * c)) ^ 2 :=
  allAbcRadicalPowBoundUpTo_sound
    (by native_decide : allAbcRadicalPowBoundUpTo 100 = true) a b c h hc

/-! ### Continuous bridge (diagnostic only) -/

/--
Continuous diagnostic abc quality bridge.

* **Assumption:** a primitive triple with quality `> 1 + ε` yields an
  admissible continuous pure-boost already past the model quality ceiling.
* **Proved core:** `abc_amplification_contradiction` /
  `torsion_bound_continuous`.
* **Obstruction:** the two conjuncts cannot hold together
  (`abc_quality_bound_of_admissible`). Explicitly `¬ AbcAdmissibleBridge`
  via the triple `1 + 8 = 9`.
* **Does not claim:** unconditional classical abc (Oesterlé–Masser).
-/
def AbcAdmissibleBridge : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (a b c : ℕ),
    IsAbcTriple a b c →
    1 + ε < abcQuality a b c →
      IsAdmissibleContinuous (abcMismatchParams a b c) ∧
        abcQualityCeiling (abcRadical (a * b * c)) < abcQuality a b c

/-- Conditional DST recovery of the classical abc conjecture (vacuous bridge). -/
theorem abc_conjecture_of_bridge (hbridge : AbcAdmissibleBridge) :
    ∀ (ε : ℝ), 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a b c : ℕ), IsAbcTriple a b c →
          (c : ℝ) ≤ C * (abcRadical (a * b * c) : ℝ) ^ (1 + ε) := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro a b c h
  by_cases hq : abcQuality a b c ≤ 1 + ε
  · have ht : 0 ≤ 1 + ε := add_nonneg zero_le_one hε.le
    have := (abcQuality_le_iff_rpow h ht).mp hq
    simpa using this
  · have hlt : 1 + ε < abcQuality a b c := lt_of_not_ge hq
    obtain ⟨hadm, hbig⟩ := hbridge ε hε a b c h hlt
    exact (abc_amplification_contradiction h hadm hbig).elim

theorem isAbcTriple_one_eight_nine : IsAbcTriple 1 8 9 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

theorem abcRadical_one_eight_nine : abcRadical (1 * 8 * 9) = 6 := by
  native_decide

theorem one_lt_abcQuality_one_eight_nine : 1 < abcQuality 1 8 9 := by
  have h := isAbcTriple_one_eight_nine
  rw [one_lt_abcQuality_iff h, abcRadical_one_eight_nine]
  decide

/-- The continuous quality bridge is false: it demands an impossible pair of
conjuncts on any triple with quality `> 1` (e.g. `1 + 8 = 9`). -/
theorem AbcAdmissibleBridge_false : ¬ AbcAdmissibleBridge := by
  intro hbridge
  set q := abcQuality 1 8 9
  have hq : 1 < q := one_lt_abcQuality_one_eight_nine
  set ε : ℝ := (q - 1) / 2
  have hε : 0 < ε := by
    unfold ε
    linarith [hq]
  have hlt : 1 + ε < q := by
    unfold ε
    linarith [hq]
  obtain ⟨hadm, hbig⟩ := hbridge ε hε 1 8 9 isAbcTriple_one_eight_nine hlt
  exact abc_amplification_contradiction isAbcTriple_one_eight_nine hadm hbig

/-! ### Quality-seed quantisation (solution-dependent payload) -/

/-- Quantise the abc log-gap `log c − log rad(abc)` to a pure-boost lattice seed. -/
noncomputable def quantizeAbcMismatch (N : ℕ) [NeZero N] (a b c : ℕ)
    (_h : IsAbcTriple a b c) : DiscreteTorsion N :=
  Embedding.quantizeMismatch N (abcRadical (a * b * c) : ℤ) (c : ℤ)
    (Int.natCast_ne_zero.mpr (abcRadical_ne_zero _))
    (Int.natCast_ne_zero.mpr (isAbcTriple_c_ne_zero _h))

theorem quantizeAbcMismatch_pureBoost (N : ℕ) [NeZero N] {a b c : ℕ}
    (h : IsAbcTriple a b c) :
    ModularAmplification.IsPureBoostSeed (quantizeAbcMismatch N a b c h) :=
  Embedding.quantizeMismatch_pureBoost _ _ _ _

theorem quantizeAbcMismatch_eq_quantizeRapidity (N : ℕ) [NeZero N] {a b c : ℕ}
    (h : IsAbcTriple a b c) :
    (quantizeAbcMismatch N a b c h).n 0 =
      (quantizeRapidity N
        (Real.log c - Real.log (abcRadical (a * b * c))) : ZMod N) := by
  simp only [quantizeAbcMismatch, quantizeMismatch, Int.natAbs_natCast]

theorem quantizeAbcMismatch_error (N : ℕ) [NeZero N] {a b c : ℕ}
    (h : IsAbcTriple a b c) :
    |(Real.log c - Real.log (abcRadical (a * b * c))) -
        rapidityOfIndex N
          (quantizeRapidity N
            (Real.log c - Real.log (abcRadical (a * b * c))))| <
      2 * Real.pi / N := by
  have ha : (abcRadical (a * b * c) : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (abcRadical_ne_zero _)
  have hc : (c : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (isAbcTriple_c_ne_zero h)
  have herr := Embedding.quantizeMismatch_error (N := N)
    (abcRadical (a * b * c) : ℤ) (c : ℤ) ha hc
  simpa [logMismatch, pureBoost, Int.natAbs_natCast] using herr

/-- Log gap `δ = log c − log rad(abc) = (q − 1) log rad`. -/
noncomputable def abcLogGap (a b c : ℕ) : ℝ :=
  Real.log c - Real.log (abcRadical (a * b * c))

theorem abcLogGap_eq_quality {a b c : ℕ} (h : IsAbcTriple a b c) :
    abcLogGap a b c =
      (abcQuality a b c - 1) * Real.log (abcRadical (a * b * c)) := by
  have hθ := abcMismatch_rapidity h
  unfold abcLogGap
  linarith [hθ]

/-! ### Live modular bridge (solution-dependent payload) -/

/--
**Live modular abc bridge** (unproved).

* **Payload (solution-dependent):** the quantised log-gap
  `t := quantizeAbcMismatch N a b c` is admissible, carries a
  `ModularAmplificationWitness N k` with `w.t.val = t`, and the powered
  real-scale configuration is `ConformalGaugeAdmissible`.
* **Unlike** `AbcAdmissibleBridge`: the continuous ceiling contradiction is
  avoided; the witness type is inhabited in general, but the bridge demands
  that the *triple's* quantised gap be that witness.
* **Proved core used by the conditional wrapper:**
  `ModularAmplificationWitness.not_admissible_real_scale`.
* **Residual gap:** conformal / CGA gauge vs PGA real-scale cone (same as FLT).
* **Does not claim:** unconditional classical abc.
-/
def AbcModularBridge : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (a b c : ℕ) (h : IsAbcTriple a b c),
    1 + ε < abcQuality a b c →
      ∃ (N k : ℕ) (hN : N ≠ 0),
        letI : NeZero N := ⟨hN⟩
        let t := quantizeAbcMismatch N a b c h
        IsAdmissible t ∧
          (∃ w : ModularAmplificationWitness N k, w.t.val = t) ∧
            ModularAmplification.ConformalGaugeAdmissible
              (scaleTorsion (k : ℝ) (toTorsionParams t))

/-- Conditional classical abc from the modular bridge. -/
theorem abc_conjecture_of_modular_bridge (hbridge : AbcModularBridge) :
    ∀ (ε : ℝ), 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a b c : ℕ), IsAbcTriple a b c →
          (c : ℝ) ≤ C * (abcRadical (a * b * c) : ℝ) ^ (1 + ε) := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro a b c h
  by_cases hq : abcQuality a b c ≤ 1 + ε
  · have ht : 0 ≤ 1 + ε := add_nonneg zero_le_one hε.le
    have := (abcQuality_le_iff_rpow h ht).mp hq
    simpa using this
  · have hlt : 1 + ε < abcQuality a b c := lt_of_not_ge hq
    obtain ⟨N, k, hN, _hadm, ⟨w, hw⟩, hconf⟩ := hbridge ε hε a b c h hlt
    let : NeZero N := ⟨hN⟩
    have hnot :=
      ModularAmplification.ModularAmplificationWitness.not_admissible_real_scale w
    rw [hw] at hnot
    exact (hnot hconf).elim

/-! ### Partial winding construction on the principal interval -/

/--
Specialisation to abc log-gaps on the principal interval: if
`2π/k ≤ δ < 2π` and `k ∣ N`, the quantised abc seed has nonzero total winding.
General rapidity helpers live in `Algebra.ModularAmplification`.
-/
theorem abc_has_winding_of_logGap_ge (N k : ℕ) [NeZero N] (hk : 0 < k)
    {a b c : ℕ} (h : IsAbcTriple a b c)
    (hle : 2 * Real.pi / k ≤ abcLogGap a b c)
    (hlt : abcLogGap a b c < 2 * Real.pi)
    (hdvd : k ∣ N) :
    windingTotal k (quantizeAbcMismatch N a b c h) ≠ 0 := by
  have hπk : 0 ≤ 2 * Real.pi / k :=
    div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le) (Nat.cast_nonneg _)
  have h0 : 0 ≤ abcLogGap a b c := le_trans hπk hle
  have heq :
      quantizeAbcMismatch N a b c h =
        pureBoostSeedOfRapidity N (abcLogGap a b c) := by
    -- `fin_cases` leaves some axes with unused simp lemmas; silence that linter here.
    set_option linter.unusedSimpArgs false in
    refine congr_arg₂ DiscreteTorsion.mk ?_ rfl
    funext i
    fin_cases i <;>
      simp [quantizeAbcMismatch, quantizeMismatch, pureBoostSeedOfRapidity, abcLogGap,
        Int.natAbs_natCast]
  rw [heq]
  exact windingTotal_ne_zero_of_rapidity_ge N k hk (abcLogGap a b c) h0 hle hlt hdvd

-- FLT / Beal remain independent special cases (Ch.5–6); abc treats all
-- coprime sums `a + b = c`. See `fermat_last_theorem_of_modular_bridge` /
-- `beal_conjecture_of_modular_bridge`.

end Theorems

end DstDiophantine
