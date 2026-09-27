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
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorial.Basic
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

## What is proved

On the pure-boost chart `Ω = pureBoost(2 δ)` with `δ = log c − log rad(abc)`,
the normalised height is exactly `(16/(3π²)) δ²`. Continuous admissibility is
the branch `0 ≤ δ ≤ π/4`, so an admissible seed obeys
`c ≤ exp(π/4) · rad(abc)` and `|JNormalized| ≤ 1/3`. The torsional ceiling
`|JNormalized| ≤ 1` lies strictly outside that cone: it becomes active only
for `δ > π √3 / 4`.

Every primitive triple with `c ≤ 80` satisfies `c ≤ 2 · rad(abc)`. Since
`2 < exp(π/4)`, none of them leaves the cone. The first exit is
`1 + 80 = 81` (`1 + 2⁴·5 = 3⁴`), with radical `30` and ratio `27/10`: the
seed is not admissible, yet the normalised height is still strictly less
than one. The sum `3 + 5³ = 2⁷` has the same radical and ratio `64/15`, so
the normalised height exceeds one, and that seed is likewise not admissible.

## Paper gap (not closed)

Classical abc (`∀ ε > 0, ∃ Cε, c ≤ Cε · rad(abc)^{1+ε}` for primitive triples) is
**not** claimed unconditionally. The cone estimate is the strong form, but
only for admissible seeds. `AbcAdmissibleBridge` is diagnostic: it asks for an
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

/-- Quality–height identity in the pure-boost chart. -/
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

/-! ### Logarithmic gap -/

/-- Log gap `δ = log c − log rad(abc) = (q − 1) log rad`. -/
noncomputable def abcLogGap (a b c : ℕ) : ℝ :=
  Real.log c - Real.log (abcRadical (a * b * c))

theorem abcLogGap_eq_quality {a b c : ℕ} (h : IsAbcTriple a b c) :
    abcLogGap a b c =
      (abcQuality a b c - 1) * Real.log (abcRadical (a * b * c)) := by
  have hθ := abcMismatch_rapidity h
  unfold abcLogGap
  linarith [hθ]

/-! ### Numeric envelopes for the cone and the height threshold -/

private theorem two_lt_exp_pi_div_four : (2 : ℝ) < Real.exp (Real.pi / 4) := by
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have harg : (3 : ℝ) / 4 < Real.pi / 4 := by linarith
  have hseries :
      (2 : ℝ) < ∑ i ∈ Finset.range 3, ((3 : ℝ) / 4) ^ i / i.factorial := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one, pow_zero, pow_one,
      zero_add]
    norm_num
  have hsum :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4) 3
  exact lt_trans (hseries.trans_le hsum) (Real.exp_lt_exp.mpr harg)

private theorem exp_pi_div_four_lt_27_div_10 :
    Real.exp (Real.pi / 4) < (27 : ℝ) / 10 := by
  have harg : Real.pi / 4 < (63 : ℝ) / 80 := by
    have hπ : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
    linarith
  have hx0 : (0 : ℝ) ≤ (63 : ℝ) / 80 := by norm_num
  have hx1 : (63 : ℝ) / 80 ≤ 1 := by norm_num
  have hbound := Real.exp_bound' hx0 hx1 (n := 4) (by norm_num)
  have h4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num
  have hclosed :
      (∑ m ∈ Finset.range 4, ((63 : ℝ) / 80) ^ m / m.factorial) +
          ((63 : ℝ) / 80) ^ 4 * (4 + 1) / ((Nat.factorial 4 : ℝ) * 4) <
        (27 : ℝ) / 10 := by
    rw [h4]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one, pow_zero, pow_one,
      zero_add]
    norm_num
  exact (Real.exp_lt_exp.mpr harg).trans (hbound.trans_lt hclosed)

private theorem exp_one_gt_27_div_10 : (27 : ℝ) / 10 < Real.exp 1 := by
  have hseries :
      (27 : ℝ) / 10 < ∑ i ∈ Finset.range 6, (1 : ℝ) ^ i / i.factorial := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one, pow_zero, pow_one,
      zero_add]
    norm_num
  exact hseries.trans_le (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 6)

private theorem one_lt_pi_mul_sqrt_three_div_four :
    (1 : ℝ) < Real.pi * Real.sqrt 3 / 4 := by
  have hπ : (314 : ℝ) / 100 < Real.pi := by
    convert (Real.pi_gt_d2 : (3.14 : ℝ) < Real.pi) using 1
    norm_num
  have hsq : ((4 : ℝ) / (314 / 100)) ^ 2 < 3 := by norm_num
  have hs : (4 : ℝ) / (314 / 100) < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt hsq
  have hpos : (0 : ℝ) < 314 / 100 := by norm_num
  have hmul : (4 : ℝ) < Real.pi * Real.sqrt 3 := by
    calc
      (4 : ℝ) = (314 / 100) * (4 / (314 / 100)) := by field_simp
      _ < Real.pi * Real.sqrt 3 :=
          mul_lt_mul hπ hs.le (by positivity) (le_of_lt (hpos.trans hπ))
  linarith

private theorem sqrt_three_lt_1733 : Real.sqrt 3 < (1733 : ℝ) / 1000 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

private theorem pi_lt_31416 : Real.pi < (31416 : ℝ) / 10000 := by
  convert Real.pi_lt_d4 using 1
  norm_num

private theorem exp_two_fifths_le_taylor :
    Real.exp ((2 : ℝ) / 5) ≤
      1 + (2 : ℝ) / 5 + ((2 : ℝ) / 5) ^ 2 / 2 + ((2 : ℝ) / 5) ^ 3 / 6 +
        ((2 : ℝ) / 5) ^ 4 * 5 / 96 := by
  have hx0 : (0 : ℝ) ≤ (2 : ℝ) / 5 := by norm_num
  have hx1 : (2 : ℝ) / 5 ≤ 1 := by norm_num
  have hbound := Real.exp_bound' hx0 hx1 (n := 4) (by norm_num)
  have h4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num
  have hclosed :
      (∑ m ∈ Finset.range 4, ((2 : ℝ) / 5) ^ m / m.factorial) +
          ((2 : ℝ) / 5) ^ 4 * (4 + 1) / ((Nat.factorial 4 : ℝ) * 4) =
        1 + (2 : ℝ) / 5 + ((2 : ℝ) / 5) ^ 2 / 2 + ((2 : ℝ) / 5) ^ 3 / 6 +
          ((2 : ℝ) / 5) ^ 4 * 5 / 96 := by
    rw [h4]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one, pow_zero, pow_one,
      zero_add]
    ring
  linarith

private theorem exp_pi_sqrt_three_div_four_lt_64_div_15 :
    Real.exp (Real.pi * Real.sqrt 3 / 4) < (64 : ℝ) / 15 := by
  have hπ := pi_lt_31416
  have hs := sqrt_three_lt_1733
  have hmul : Real.pi * Real.sqrt 3 < (31416 : ℝ) / 10000 * ((1733 : ℝ) / 1000) :=
    mul_lt_mul hπ hs.le (Real.sqrt_pos.mpr (by norm_num)) (by positivity)
  have hnum : (31416 : ℝ) / 10000 * ((1733 : ℝ) / 1000) / 4 < (7 : ℝ) / 5 := by
    norm_num
  have harg : Real.pi * Real.sqrt 3 / 4 < (7 : ℝ) / 5 := by linarith
  have hsplit : Real.exp ((7 : ℝ) / 5) = Real.exp 1 * Real.exp ((2 : ℝ) / 5) := by
    rw [← Real.exp_add]
    ring_nf
  set T : ℝ :=
    1 + (2 : ℝ) / 5 + ((2 : ℝ) / 5) ^ 2 / 2 + ((2 : ℝ) / 5) ^ 3 / 6 +
      ((2 : ℝ) / 5) ^ 4 * 5 / 96
  have hTpos : (0 : ℝ) < T := by
    unfold T
    norm_num
  have hprod : Real.exp 1 * Real.exp ((2 : ℝ) / 5) < (2.7182818286 : ℝ) * T := by
    have hle : Real.exp 1 * Real.exp ((2 : ℝ) / 5) ≤ Real.exp 1 * T :=
      mul_le_mul_of_nonneg_left exp_two_fifths_le_taylor (Real.exp_pos _).le
    have hlt : Real.exp 1 * T < (2.7182818286 : ℝ) * T :=
      mul_lt_mul_of_pos_right Real.exp_one_lt_d9 hTpos
    exact hle.trans_lt hlt
  have hnumT : (2.7182818286 : ℝ) * T < (64 : ℝ) / 15 := by
    unfold T
    norm_num
  calc
    Real.exp (Real.pi * Real.sqrt 3 / 4) < Real.exp ((7 : ℝ) / 5) :=
      Real.exp_lt_exp.mpr harg
    _ = Real.exp 1 * Real.exp ((2 : ℝ) / 5) := hsplit
    _ < (2.7182818286 : ℝ) * T := hprod
    _ < (64 : ℝ) / 15 := hnumT

/-! ### Admissible cone: linear radical bound, height at most one third -/

theorem abcHeight_eq_logGap (a b c : ℕ) :
    abcHeight a b c =
      (16 / (3 * Real.pi ^ 2)) * (abcLogGap a b c) ^ 2 := by
  simpa [abcLogGap] using abcHeight_eq a b c

/-- Normalised height equals one at rapidity `π √3 / 4`. -/
private theorem abcHeight_unit_at_threshold :
    (16 / (3 * Real.pi ^ 2)) * (Real.pi * Real.sqrt 3 / 4) ^ 2 = 1 := by
  have hsq : (Real.pi * Real.sqrt 3 / 4) ^ 2 = 3 * Real.pi ^ 2 / 16 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    field_simp
    norm_num
  rw [hsq]
  field_simp

/-- Normalised height passes below 1 exactly inside rapidity `π √3 / 4`. -/
theorem abcHeight_lt_one_iff (a b c : ℕ) :
    abcHeight a b c < 1 ↔
      |abcLogGap a b c| < Real.pi * Real.sqrt 3 / 4 := by
  rw [abcHeight_eq_logGap]
  set δ : ℝ := abcLogGap a b c
  set κ : ℝ := 16 / (3 * Real.pi ^ 2)
  set ρ : ℝ := Real.pi * Real.sqrt 3 / 4
  have hκ : 0 < κ := by
    unfold κ
    positivity
  have hρ : 0 < ρ := by
    unfold ρ
    positivity
  have hunit : κ * ρ ^ 2 = 1 := by
    simpa [κ, ρ] using abcHeight_unit_at_threshold
  constructor
  · intro h
    have hsq : δ ^ 2 < ρ ^ 2 := by
      have hlt : κ * δ ^ 2 < κ * ρ ^ 2 := by simpa [hunit, mul_comm] using h
      exact lt_of_mul_lt_mul_left hlt (le_of_lt hκ)
    have habs := (sq_lt_sq).mp hsq
    rwa [abs_of_pos hρ] at habs
  · intro h
    have hsq : δ ^ 2 < ρ ^ 2 := (sq_lt_sq).mpr (by rwa [abs_of_pos hρ])
    have hlt : κ * δ ^ 2 < κ * ρ ^ 2 := mul_lt_mul_of_pos_left hsq hκ
    simpa [hunit, mul_comm] using hlt

theorem one_lt_abcHeight_of_abs_logGap_gt (a b c : ℕ)
    (h : Real.pi * Real.sqrt 3 / 4 < |abcLogGap a b c|) :
    1 < abcHeight a b c := by
  rw [abcHeight_eq_logGap]
  set δ : ℝ := abcLogGap a b c
  set κ : ℝ := 16 / (3 * Real.pi ^ 2)
  set ρ : ℝ := Real.pi * Real.sqrt 3 / 4
  have hκ : 0 < κ := by
    unfold κ
    positivity
  have hρ : 0 < ρ := by
    unfold ρ
    positivity
  have hunit : κ * ρ ^ 2 = 1 := by
    simpa [κ, ρ] using abcHeight_unit_at_threshold
  have hsq : ρ ^ 2 < δ ^ 2 := (sq_lt_sq).mpr (by rwa [abs_of_pos hρ])
  have hlt : κ * ρ ^ 2 < κ * δ ^ 2 := mul_lt_mul_of_pos_left hsq hκ
  simpa [hunit, mul_comm] using hlt

/-- Admissible pure-boost seeds obey the strong radical bound `c ≤ e^{π/4} rad`. -/
theorem abc_c_le_exp_mul_radical_of_admissible {a b c : ℕ} (h : IsAbcTriple a b c)
    (hadm : IsAdmissibleContinuous (abcMismatchParams a b c)) :
    (c : ℝ) ≤
      Real.exp (Real.pi / 4) * (abcRadical (a * b * c) : ℝ) := by
  have hδ := (isAdmissibleContinuous_abcMismatch_iff h).mp hadm
  set R : ℝ := (abcRadical (a * b * c) : ℝ)
  have hRpos : 0 < R := Nat.cast_pos.mpr (abcRadical_pos _)
  have hlogR : Real.log (c : ℝ) ≤ Real.log R + Real.pi / 4 := by
    simp only [R] at hδ ⊢
    linarith
  have hcpos : 0 < (c : ℝ) := Nat.cast_pos.mpr (isAbcTriple_c_pos h)
  have htarget : 0 < R * Real.exp (Real.pi / 4) := mul_pos hRpos (Real.exp_pos _)
  have hlog :
      Real.log (c : ℝ) ≤ Real.log (R * Real.exp (Real.pi / 4)) := by
    rw [Real.log_mul hRpos.ne' (Real.exp_ne_zero _), Real.log_exp]
    exact hlogR
  have hle : (c : ℝ) ≤ R * Real.exp (Real.pi / 4) :=
    (Real.log_le_log_iff hcpos htarget).mp hlog
  simpa [mul_comm] using hle

/-- Inside the cone the quality cannot exceed the branch ceiling. -/
theorem abc_quality_le_branch_of_admissible {a b c : ℕ} (h : IsAbcTriple a b c)
    (hadm : IsAdmissibleContinuous (abcMismatchParams a b c)) :
    abcQuality a b c ≤
      1 + (Real.pi / 4) / Real.log (abcRadical (a * b * c)) := by
  have hδ := (isAdmissibleContinuous_abcMismatch_iff h).mp hadm
  have hgap := abcLogGap_eq_quality h
  have hLpos : 0 < Real.log (abcRadical (a * b * c)) := log_radical_pos h
  have hle : (abcQuality a b c - 1) * Real.log (abcRadical (a * b * c)) ≤
      Real.pi / 4 := by
    rw [← hgap]
    simpa [abcLogGap] using hδ.2
  have hquot : abcQuality a b c - 1 ≤
      (Real.pi / 4) / Real.log (abcRadical (a * b * c)) :=
    (le_div_iff₀ hLpos).mpr hle
  linarith

/-- On the admissible cone the normalised height is at most one third. -/
theorem abcHeight_le_one_third_of_admissible {a b c : ℕ} (h : IsAbcTriple a b c)
    (hadm : IsAdmissibleContinuous (abcMismatchParams a b c)) :
    abcHeight a b c ≤ 1 / 3 := by
  have hδ := (isAdmissibleContinuous_abcMismatch_iff h).mp hadm
  rw [abcHeight_eq_logGap]
  set δ : ℝ := abcLogGap a b c
  have hsq : δ ^ 2 ≤ (Real.pi / 4) ^ 2 := by
    have h0 : 0 ≤ δ := by
      unfold δ abcLogGap
      exact hδ.1
    have hπle : δ ≤ Real.pi / 4 := by
      unfold δ abcLogGap
      exact hδ.2
    have habs : |δ| ≤ |Real.pi / 4| := by
      rw [abs_of_nonneg h0, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 4)]
      exact hπle
    exact (sq_le_sq).mpr habs
  have hcoef : (0 : ℝ) ≤ 16 / (3 * Real.pi ^ 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsq hcoef
  have hconst :
      (16 : ℝ) / (3 * Real.pi ^ 2) * (Real.pi / 4) ^ 2 = 1 / 3 := by
    field_simp
    ring
  linarith

/-! ### Coarser ceiling from `|JNormalized| ≤ 1` -/

/--
Discrete quality ceiling `1 + √(1/(c₁ ε_N))` with
`ε_N = 16/(3N²)` from `discrete_nonzero_height_lb`.
-/
noncomputable def discreteAbcCeiling (N rad : ℕ) : ℝ :=
  1 + Real.sqrt (1 / (abcHeightCoef rad * ((16 : ℝ) / (3 * (N : ℝ) ^ 2))))

/-- Admissibility also implies the coarser ceiling coming from `|JNormalized| ≤ 1`.
The branch `δ ≤ π/4` is the stricter cut. -/
theorem discrete_abc_bound {a b c : ℕ} (h : IsAbcTriple a b c)
    (hadm : IsAdmissibleContinuous (abcMismatchParams a b c)) :
    abcQuality a b c ≤ abcQualityCeiling (abcRadical (a * b * c)) :=
  abc_quality_bound_of_admissible h hadm

/-- Nonzero discrete seeds are at least `ε_N` tall (shared core). -/
theorem discrete_abc_height_lb {N : ℕ} [NeZero N] (t : DiscreteTorsion N)
    (hne : latticeMismatch t ≠ 0) :
    (16 : ℝ) / (3 * (N : ℝ) ^ 2) ≤ |JNormalized (toTorsionParams t)| :=
  Framework.discrete_nonzero_height_lb t hne

/-! ### Finite search over primitive triples -/

/-- Enumerate primitive triples with `c ≤ N` and test `ok`. -/
def allPrimitiveAbcUpTo (N : ℕ) (ok : ℕ → ℕ → ℕ → Bool) : Bool :=
  (List.range (N + 1)).all fun c =>
    (List.range (c + 1)).all fun a =>
      let b := c - a
      if decide (0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b) then
        ok a b c
      else
        true

theorem allPrimitiveAbcUpTo_sound {N : ℕ} {ok : ℕ → ℕ → ℕ → Bool}
    (hcert : allPrimitiveAbcUpTo N ok = true) :
    ∀ a b c : ℕ, IsAbcTriple a b c → c ≤ N → ok a b c = true := by
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
  simpa only [hb_eq, hcondB, ↓reduceIte] using hall_a

/-- Decidable radical-power bound for a single candidate pair. -/
def abcRadicalPowOk (a b c : ℕ) : Bool :=
  decide (c ≤ (abcRadical (a * b * c)) ^ 2)

/-- All primitive triples with `c ≤ N` satisfy `c ≤ rad(abc)²`. -/
def allAbcRadicalPowBoundUpTo (N : ℕ) : Bool :=
  allPrimitiveAbcUpTo N abcRadicalPowOk

theorem allAbcRadicalPowBoundUpTo_sound {N : ℕ}
    (hcert : allAbcRadicalPowBoundUpTo N = true) :
    ∀ a b c : ℕ, IsAbcTriple a b c → c ≤ N →
      c ≤ (abcRadical (a * b * c)) ^ 2 := by
  intro a b c h hc
  have hok := allPrimitiveAbcUpTo_sound hcert a b c h hc
  simpa [abcRadicalPowOk, decide_eq_true_eq] using hok

/-- Chapter 7 finite-exploration certificate for targets up to `100`. -/
theorem abc_radical_pow_of_le_hundred {a b c : ℕ} (h : IsAbcTriple a b c)
    (hc : c ≤ 100) : c ≤ (abcRadical (a * b * c)) ^ 2 :=
  allAbcRadicalPowBoundUpTo_sound
    (by native_decide : allAbcRadicalPowBoundUpTo 100 = true) a b c h hc

/-- Decidable comparison `c ≤ 2 · rad(abc)`. -/
def abcTwiceRadicalOk (a b c : ℕ) : Bool :=
  decide (c ≤ 2 * abcRadical (a * b * c))

/-- All primitive triples with `c ≤ N` satisfy `c ≤ 2 · rad(abc)`. -/
def allAbcTwiceRadicalUpTo (N : ℕ) : Bool :=
  allPrimitiveAbcUpTo N abcTwiceRadicalOk

theorem abc_twice_radical_of_le_eighty {a b c : ℕ} (h : IsAbcTriple a b c)
    (hc : c ≤ 80) : c ≤ 2 * abcRadical (a * b * c) := by
  have hok := allPrimitiveAbcUpTo_sound
    (by native_decide : allAbcTwiceRadicalUpTo 80 = true) a b c h hc
  simpa [abcTwiceRadicalOk, decide_eq_true_eq] using hok

/-- Sums up to `80` stay strictly inside the upper wall of the cone. -/
theorem abc_logGap_lt_pi_div_four_of_le_eighty {a b c : ℕ} (h : IsAbcTriple a b c)
    (hc : c ≤ 80) : abcLogGap a b c < Real.pi / 4 := by
  have htwice := abc_twice_radical_of_le_eighty h hc
  have hcast : (c : ℝ) ≤ 2 * (abcRadical (a * b * c) : ℝ) := by
    exact_mod_cast htwice
  have hstrict : (c : ℝ) < Real.exp (Real.pi / 4) * (abcRadical (a * b * c) : ℝ) := by
    have hRpos : (0 : ℝ) < abcRadical (a * b * c) := Nat.cast_pos.mpr (abcRadical_pos _)
    calc
      (c : ℝ) ≤ 2 * (abcRadical (a * b * c) : ℝ) := hcast
      _ < Real.exp (Real.pi / 4) * (abcRadical (a * b * c) : ℝ) :=
          mul_lt_mul_of_pos_right two_lt_exp_pi_div_four hRpos
  have hcpos : 0 < (c : ℝ) := Nat.cast_pos.mpr (isAbcTriple_c_pos h)
  have htarget : 0 < Real.exp (Real.pi / 4) * (abcRadical (a * b * c) : ℝ) :=
    mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr (abcRadical_pos _))
  have hlog := (Real.log_lt_log_iff hcpos htarget).mpr hstrict
  rw [Real.log_mul (Real.exp_ne_zero _) (Nat.cast_ne_zero.mpr (abcRadical_ne_zero _)),
    Real.log_exp] at hlog
  unfold abcLogGap
  linarith

theorem isAbcTriple_one_eighty_eighty_one : IsAbcTriple 1 80 81 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

theorem abcRadical_one_eighty_eighty_one : abcRadical (1 * 80 * 81) = 30 := by
  native_decide

/-- `1 + 2^4 · 5 = 3^4` is the first primitive sum that leaves the cone. -/
theorem pi_div_four_lt_abcLogGap_one_eighty :
    Real.pi / 4 < abcLogGap 1 80 81 := by
  rw [abcLogGap, abcRadical_one_eighty_eighty_one]
  push_cast
  rw [← Real.log_div (by norm_num) (by norm_num)]
  have hratio : Real.exp (Real.pi / 4) < (81 : ℝ) / 30 := by
    have hnum : (81 : ℝ) / 30 = 27 / 10 := by norm_num
    rw [hnum]
    exact exp_pi_div_four_lt_27_div_10
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr hratio

theorem not_admissible_abc_one_eighty :
    ¬ IsAdmissibleContinuous (abcMismatchParams 1 80 81) := by
  intro hadm
  have hle :=
    (isAdmissibleContinuous_abcMismatch_iff isAbcTriple_one_eighty_eighty_one).mp hadm
  exact not_lt_of_ge hle.2 pi_div_four_lt_abcLogGap_one_eighty

/-- The first exit still has normalised height strictly below one. -/
theorem abcHeight_lt_one_one_eighty : abcHeight 1 80 81 < 1 := by
  rw [abcHeight_lt_one_iff]
  have hpos : 0 < abcLogGap 1 80 81 :=
    lt_trans (by positivity : (0 : ℝ) < Real.pi / 4) pi_div_four_lt_abcLogGap_one_eighty
  rw [abs_of_pos hpos]
  rw [abcLogGap, abcRadical_one_eighty_eighty_one]
  push_cast
  rw [← Real.log_div (by norm_num) (by norm_num)]
  have hratio : (81 : ℝ) / 30 < Real.exp (Real.pi * Real.sqrt 3 / 4) := by
    have h27 : (27 : ℝ) / 10 < Real.exp 1 := exp_one_gt_27_div_10
    have h1 : (1 : ℝ) < Real.pi * Real.sqrt 3 / 4 := one_lt_pi_mul_sqrt_three_div_four
    have hexp : Real.exp 1 < Real.exp (Real.pi * Real.sqrt 3 / 4) :=
      Real.exp_lt_exp.mpr h1
    have hnum : (81 : ℝ) / 30 = (27 : ℝ) / 10 := by norm_num
    linarith
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr hratio

theorem isAbcTriple_one_eight_nine : IsAbcTriple 1 8 9 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

theorem abcRadical_one_eight_nine : abcRadical (1 * 8 * 9) = 6 := by
  native_decide

theorem isAdmissibleContinuous_abc_one_eight_nine :
    IsAdmissibleContinuous (abcMismatchParams 1 8 9) := by
  rw [isAdmissibleContinuous_abcMismatch_iff isAbcTriple_one_eight_nine]
  constructor
  · rw [abcRadical_one_eight_nine]
    push_cast
    exact le_of_lt (sub_pos.mpr
      (Real.log_lt_log (by norm_num) (by norm_num : (6 : ℝ) < 9)))
  · rw [abcRadical_one_eight_nine]
    push_cast
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have hratio : (9 : ℝ) / 6 < Real.exp (Real.pi / 4) := by
      exact (by norm_num : (9 : ℝ) / 6 < 2).trans two_lt_exp_pi_div_four
    exact le_of_lt ((Real.log_lt_iff_lt_exp (by norm_num)).mpr hratio)

theorem isAbcTriple_three_one_two_five : IsAbcTriple 3 125 128 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

theorem abcRadical_three_one_two_five : abcRadical (3 * 125 * 128) = 30 := by
  native_decide

/-- `3 + 5³ = 2⁷` crosses the height threshold, hence leaves the cone. -/
theorem pi_sqrt_three_div_four_lt_abcLogGap_two_seven :
    Real.pi * Real.sqrt 3 / 4 < abcLogGap 3 125 128 := by
  rw [abcLogGap, abcRadical_three_one_two_five]
  push_cast
  rw [← Real.log_div (by norm_num) (by norm_num)]
  have hratio : Real.exp (Real.pi * Real.sqrt 3 / 4) < (128 : ℝ) / 30 := by
    have hnum : (64 : ℝ) / 15 = (128 : ℝ) / 30 := by norm_num
    rw [← hnum]
    exact exp_pi_sqrt_three_div_four_lt_64_div_15
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr hratio

theorem one_lt_abcHeight_three_one_two_five : 1 < abcHeight 3 125 128 := by
  apply one_lt_abcHeight_of_abs_logGap_gt
  have hgt := pi_sqrt_three_div_four_lt_abcLogGap_two_seven
  rwa [abs_of_pos (lt_trans (by positivity : (0 : ℝ) < Real.pi * Real.sqrt 3 / 4) hgt)]

theorem not_admissible_abc_three_one_two_five :
    ¬ IsAdmissibleContinuous (abcMismatchParams 3 125 128) := by
  intro hadm
  have hle :=
    (isAdmissibleContinuous_abcMismatch_iff isAbcTriple_three_one_two_five).mp hadm
  have hhalf : Real.pi / 4 < Real.pi * Real.sqrt 3 / 4 := by
    have hs : (1 : ℝ) < Real.sqrt 3 :=
      Real.lt_sqrt_of_sq_lt (by norm_num : (1 : ℝ) ^ 2 < 3)
    nlinarith [Real.pi_pos, hs]
  exact not_lt_of_ge hle.2 (hhalf.trans pi_sqrt_three_div_four_lt_abcLogGap_two_seven)

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
