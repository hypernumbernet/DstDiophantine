import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.nativeDecide false

/-!
# Phase 5: abc conjecture (DST quality / height core)

We formalise Chapter 7 of `dst-diophantine.tex` as a **quality–torsional height**
argument on the pure-boost mismatch model
`Ω = pureBoost(2(log c − log rad(abc)))`, together with a finite computational
certificate and a bridge hypothesis recovering the classical Oesterlé–Masser
statement.

## Paper gap (not closed)

Classical abc (`∀ ε > 0, ∃ Cε, c ≤ Cε · rad(abc)^{1+ε}` for primitive triples) is
**not** claimed unconditionally. Dual-sector rotors `R_dual(p)`, Lemma
`radical-dual`, and the paper's `O(1)` error in
`θ = 2 log rad · (q − 1) + O(1)` are left informal. The Lean model drops the
`O(1)` term and treats quality–height as an exact pure-boost identity. Encoding a
high-quality classical triple as an *admissible* continuous configuration (with
quality already past the model ceiling) is `AbcAdmissibleBridge`. Continuum
recovery of `Cε` via `Q(N) → ∞` is absorbed into that bridge rather than proved
as a separate limit theorem.

Legacy coarse real-scale witnesses are equation-independently empty; reusing
that design stays vacuous. A modular / quality redesign needs a
**solution-dependent** payload (cf. `FermatModularBridge`), not a bare
inhabited modular witness.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Operations Real
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

/-! ### Classical abc under an explicit bridge hypothesis -/

/--
Continuous abc quality bridge.

* **Assumption (unproved):** a primitive triple with quality `> 1 + ε` yields an
  admissible continuous pure-boost past the model quality ceiling.
* **Proved core:** `abc_amplification_contradiction` /
  `torsion_bound_continuous`.
* **Does not claim:** unconditional classical abc (Oesterlé–Masser).
-/
def AbcAdmissibleBridge : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (a b c : ℕ),
    IsAbcTriple a b c →
    1 + ε < abcQuality a b c →
      IsAdmissibleContinuous (abcMismatchParams a b c) ∧
        abcQualityCeiling (abcRadical (a * b * c)) < abcQuality a b c

/-- Conditional DST recovery of the classical abc conjecture. -/
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

-- FLT / Beal remain independent special cases (Ch.5–6); abc treats all
-- coprime sums `a + b = c`. See `fermat_last_theorem_of_bridge` /
-- `beal_conjecture_of_bridge`.

end Theorems

end DstDiophantine
