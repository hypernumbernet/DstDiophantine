import DstDiophantine.Gravity.NeutronMagnet
import DstDiophantine.Gravity.ShieldCeiling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Charge-silent dual control

The neutron is the case in which the electromagnetic label vanishes.
Two laboratory readings of a dual-only increment then separate.

## Paper boundary (do **not** claim)

A V--A coupling, a Fermi constant, a lifetime, a helicity-odd drive of
\(J\), and an identification of this increment with the weak-interaction
operator are **not** derived.

## What is proved

* On an admissible pure usual seed, \(\sum_a\alpha_a\le 3\pi/4\) already
  forces \(\sum_a\alpha_a^2\le 5\pi^2/16\). Equality holds precisely on the
  permutations of \((\pi/2,\pi/4,0)\). The dual-only shield of such a seed
  is its wall, of mass \(5\pi^2/16\).
* With the label at zero the substitution \(\theta\mapsto\theta+eA\) is the
  identity, so a circular potential drops no ponderomotive mean.
* A nonnegative magnetic increment that is not zero lowers \(J\) strictly
  and raises the unsigned mass by the same amount. On a balanced seed the
  result is repulsive. The rest-frame sandwich of every magnetic increment
  vanishes.
* Where an axis still has room to the wall, an admissible increment of this
  kind exists. Where every axis is already on the wall, none does. The
  heaviest shield is such a wall.
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible PGA

/-! ### The linear wall bound carries the mass ceiling -/

/-- Usual rapidities of the heaviest dual-only-shieldable seed, up to order. -/
def IsHeaviestUsualSeed (α : Fin 3 → ℝ) : Prop :=
  (α 0 = Real.pi / 2 ∧ α 1 = Real.pi / 4 ∧ α 2 = 0) ∨
    (α 0 = Real.pi / 2 ∧ α 1 = 0 ∧ α 2 = Real.pi / 4) ∨
    (α 0 = Real.pi / 4 ∧ α 1 = Real.pi / 2 ∧ α 2 = 0) ∨
    (α 0 = 0 ∧ α 1 = Real.pi / 2 ∧ α 2 = Real.pi / 4) ∨
    (α 0 = Real.pi / 4 ∧ α 1 = 0 ∧ α 2 = Real.pi / 2) ∨
    (α 0 = 0 ∧ α 1 = Real.pi / 4 ∧ α 2 = Real.pi / 2)

private theorem three_has_largest (α : Fin 3 → ℝ) :
    (α 1 ≤ α 0 ∧ α 2 ≤ α 0) ∨ (α 0 ≤ α 1 ∧ α 2 ≤ α 1) ∨
      (α 0 ≤ α 2 ∧ α 1 ≤ α 2) := by
  rcases le_total (α 0) (α 1) with h01 | h10
  · rcases le_total (α 1) (α 2) with h12 | h21
    · right; right
      exact ⟨h01.trans h12, h12⟩
    · rcases le_total (α 0) (α 2) with h02 | h20
      · right; left
        exact ⟨h01, h21⟩
      · right; left
        exact ⟨h01, h20.trans h01⟩
  · rcases le_total (α 0) (α 2) with h02 | h20
    · right; right
      exact ⟨h02, h10.trans h02⟩
    · rcases le_total (α 1) (α 2) with h12 | h21
      · left
        exact ⟨h12.trans h20, h20⟩
      · left
        exact ⟨h10, h21.trans h10⟩

private theorem three_quarter_sq_lt :
    3 * (Real.pi / 4) ^ 2 < 5 * Real.pi ^ 2 / 16 := by
  have h : (Real.pi / 4) ^ 2 = Real.pi ^ 2 / 16 := by ring
  rw [h]
  have hp : (0 : ℝ) < Real.pi ^ 2 := by positivity
  linarith

private theorem sum_sq_le_of_largest {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hacap : a ≤ Real.pi / 2) (hbLe : b ≤ a) (hcLe : c ≤ a)
    (hs : a + b + c ≤ 3 * Real.pi / 4) :
    a ^ 2 + b ^ 2 + c ^ 2 ≤ 5 * Real.pi ^ 2 / 16 := by
  by_cases hge : Real.pi / 4 ≤ a
  · have hT : 0 ≤ 3 * Real.pi / 4 - a := by linarith
    have hbc : b + c ≤ 3 * Real.pi / 4 - a := by linarith
    have hbc0 : 0 ≤ b + c := add_nonneg hb hc
    have hsq : (b + c) ^ 2 ≤ (3 * Real.pi / 4 - a) ^ 2 :=
      pow_le_pow_left₀ hbc0 hbc 2
    have hsplit : b ^ 2 + c ^ 2 ≤ (b + c) ^ 2 := by nlinarith [mul_nonneg hb hc]
    have hdiff :
        a ^ 2 + (3 * Real.pi / 4 - a) ^ 2 - 5 * Real.pi ^ 2 / 16 =
          2 * (a - Real.pi / 2) * (a - Real.pi / 4) := by ring
    have hnonpos : 2 * (a - Real.pi / 2) * (a - Real.pi / 4) ≤ 0 := by
      have h1 : a - Real.pi / 2 ≤ 0 := by linarith
      have h2 : 0 ≤ a - Real.pi / 4 := sub_nonneg.mpr hge
      have : (a - Real.pi / 2) * (a - Real.pi / 4) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h1 h2
      nlinarith
    linarith
  · push Not at hge
    have haSq : a ^ 2 ≤ (Real.pi / 4) ^ 2 := by
      have : a ≤ Real.pi / 4 := le_of_lt hge
      exact pow_le_pow_left₀ ha this 2
    have hbSq : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb hbLe 2
    have hcSq : c ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hc hcLe 2
    have hthree : a ^ 2 + b ^ 2 + c ^ 2 ≤ 3 * a ^ 2 := by nlinarith
    have hcap : 3 * a ^ 2 ≤ 3 * (Real.pi / 4) ^ 2 := by nlinarith
    linarith [three_quarter_sq_lt]

/-- An admissible pure usual seed whose dual wall is nonpositive already
weighs at most the shield ceiling. -/
theorem sum_sq_le_of_cone_and_wall_budget {α : Fin 3 → ℝ}
    (h0 : ∀ a, 0 ≤ α a) (hcap : ∀ a, α a ≤ Real.pi / 2)
    (hs : ∑ a : Fin 3, α a ≤ 3 * Real.pi / 4) :
    ∑ a : Fin 3, α a ^ 2 ≤ 5 * Real.pi ^ 2 / 16 := by
  have hs' : α 0 + α 1 + α 2 ≤ 3 * Real.pi / 4 := by
    simpa [Fin.sum_univ_three] using hs
  rcases three_has_largest α with h | h | h
  · have hle :=
      sum_sq_le_of_largest (h0 0) (h0 1) (h0 2) (hcap 0) h.1 h.2 hs'
    simpa [Fin.sum_univ_three] using hle
  · have hle :=
      sum_sq_le_of_largest (h0 1) (h0 0) (h0 2) (hcap 1) h.1 h.2
        (by linarith)
    have : α 0 ^ 2 + α 1 ^ 2 + α 2 ^ 2 ≤ 5 * Real.pi ^ 2 / 16 := by linarith
    simpa [Fin.sum_univ_three] using this
  · have hle :=
      sum_sq_le_of_largest (h0 2) (h0 0) (h0 1) (hcap 2) h.1 h.2
        (by linarith)
    have : α 0 ^ 2 + α 1 ^ 2 + α 2 ^ 2 ≤ 5 * Real.pi ^ 2 / 16 := by linarith
    simpa [Fin.sum_univ_three] using this

private theorem sum_sq_eq_of_largest {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hacap : a ≤ Real.pi / 2) (hbLe : b ≤ a) (hcLe : c ≤ a)
    (hs : a + b + c ≤ 3 * Real.pi / 4)
    (heq : a ^ 2 + b ^ 2 + c ^ 2 = 5 * Real.pi ^ 2 / 16) :
    a = Real.pi / 2 ∧
      (b = Real.pi / 4 ∧ c = 0 ∨ b = 0 ∧ c = Real.pi / 4) := by
  have hnot : ¬ a < Real.pi / 4 := by
    intro hlt
    have haSq : a ^ 2 < (Real.pi / 4) ^ 2 :=
      pow_lt_pow_left₀ hlt ha (by decide : (2 : ℕ) ≠ 0)
    have hbSq : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb hbLe 2
    have hcSq : c ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hc hcLe 2
    have hthree : a ^ 2 + b ^ 2 + c ^ 2 ≤ 3 * a ^ 2 := by nlinarith
    have hstrict : 3 * a ^ 2 < 3 * (Real.pi / 4) ^ 2 := by nlinarith
    linarith [three_quarter_sq_lt]
  have hge : Real.pi / 4 ≤ a := le_of_not_gt hnot
  have hT : 0 ≤ 3 * Real.pi / 4 - a := by linarith
  have hbc : b + c ≤ 3 * Real.pi / 4 - a := by linarith
  have hbc0 : 0 ≤ b + c := add_nonneg hb hc
  have hsq : (b + c) ^ 2 ≤ (3 * Real.pi / 4 - a) ^ 2 :=
    pow_le_pow_left₀ hbc0 hbc 2
  have hsplit : b ^ 2 + c ^ 2 ≤ (b + c) ^ 2 := by nlinarith [mul_nonneg hb hc]
  have hdiff :
      a ^ 2 + (3 * Real.pi / 4 - a) ^ 2 - 5 * Real.pi ^ 2 / 16 =
        2 * (a - Real.pi / 2) * (a - Real.pi / 4) := by ring
  have hnonpos : a ^ 2 + (3 * Real.pi / 4 - a) ^ 2 ≤ 5 * Real.pi ^ 2 / 16 := by
    have h1 : a - Real.pi / 2 ≤ 0 := by linarith
    have h2 : 0 ≤ a - Real.pi / 4 := sub_nonneg.mpr hge
    have : (a - Real.pi / 2) * (a - Real.pi / 4) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h1 h2
    linarith
  have hchain : a ^ 2 + b ^ 2 + c ^ 2 ≤ a ^ 2 + (3 * Real.pi / 4 - a) ^ 2 := by
    linarith
  have htop : a ^ 2 + (3 * Real.pi / 4 - a) ^ 2 = 5 * Real.pi ^ 2 / 16 := by
    apply le_antisymm hnonpos
    linarith
  have hsumEq : b + c = 3 * Real.pi / 4 - a := by
    have hsqEq : (b + c) ^ 2 = (3 * Real.pi / 4 - a) ^ 2 := by
      have hmid : b ^ 2 + c ^ 2 = (3 * Real.pi / 4 - a) ^ 2 := by linarith
      have hsplitEq : b ^ 2 + c ^ 2 = (b + c) ^ 2 := by
        apply le_antisymm hsplit
        linarith
      linarith
    have hroot := sq_eq_sq_iff_eq_or_eq_neg.mp hsqEq
    rcases hroot with h | h
    · exact h
    · have : b + c ≤ 0 := by linarith
      have : b + c = 0 := le_antisymm this hbc0
      have hT0 : 3 * Real.pi / 4 - a = 0 := by linarith
      linarith
  have hprod : b * c = 0 := by
    have : b ^ 2 + c ^ 2 = (b + c) ^ 2 := by
      apply le_antisymm hsplit
      have : (b + c) ^ 2 = (3 * Real.pi / 4 - a) ^ 2 := by rw [hsumEq]
      linarith
    nlinarith
  have hendpoint : a = Real.pi / 2 ∨ a = Real.pi / 4 := by
    have : 2 * (a - Real.pi / 2) * (a - Real.pi / 4) = 0 := by linarith
    have hmul : (a - Real.pi / 2) * (a - Real.pi / 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp hmul with h | h
    · left; linarith
    · right; linarith
  rcases hendpoint with hhalf | hquarter
  · refine ⟨hhalf, ?_⟩
    have hsum4 : b + c = Real.pi / 4 := by
      rw [hsumEq, hhalf]
      ring
    rcases mul_eq_zero.mp hprod with hb0 | hc0
    · right
      exact ⟨hb0, by linarith⟩
    · left
      exact ⟨by linarith, hc0⟩
  · have hsum2 : b + c = Real.pi / 2 := by
      rw [hsumEq, hquarter]
      ring
    have hcge : Real.pi / 4 ≤ c := by linarith
    have hbge : Real.pi / 4 ≤ b := by
      have : c ≤ Real.pi / 4 := by linarith [hcLe, hquarter]
      linarith
    have hb4 : b = Real.pi / 4 := le_antisymm (by linarith [hbLe, hquarter]) hbge
    have hc4 : c = Real.pi / 4 := le_antisymm (by linarith [hcLe, hquarter]) hcge
    exfalso
    have hpos : 0 < b * c := by
      rw [hb4, hc4]
      positivity
    linarith [hprod]

/-- Equality in the shield ceiling, for a usual seed inside the cone and
under the linear wall bound, holds exactly on the permutations of
\((\pi/2,\pi/4,0)\). -/
theorem sum_sq_eq_shield_ceiling_iff {α : Fin 3 → ℝ}
    (h0 : ∀ a, 0 ≤ α a) (hcap : ∀ a, α a ≤ Real.pi / 2)
    (hs : ∑ a : Fin 3, α a ≤ 3 * Real.pi / 4) :
    ∑ a : Fin 3, α a ^ 2 = 5 * Real.pi ^ 2 / 16 ↔ IsHeaviestUsualSeed α := by
  constructor
  · intro heq
    have hs' : α 0 + α 1 + α 2 ≤ 3 * Real.pi / 4 := by
      simpa [Fin.sum_univ_three] using hs
    have heq' : α 0 ^ 2 + α 1 ^ 2 + α 2 ^ 2 = 5 * Real.pi ^ 2 / 16 := by
      simpa [Fin.sum_univ_three] using heq
    rcases three_has_largest α with h | h | h
    · obtain ⟨ha, hbc⟩ :=
        sum_sq_eq_of_largest (h0 0) (h0 1) (h0 2) (hcap 0) h.1 h.2 hs' heq'
      rcases hbc with hbc | hbc
      · left
        exact ⟨ha, hbc.1, hbc.2⟩
      · right; left
        exact ⟨ha, hbc.1, hbc.2⟩
    · have heqSwap : α 1 ^ 2 + α 0 ^ 2 + α 2 ^ 2 = 5 * Real.pi ^ 2 / 16 := by
        linarith
      obtain ⟨ha, hbc⟩ :=
        sum_sq_eq_of_largest (h0 1) (h0 0) (h0 2) (hcap 1) h.1 h.2
          (by linarith) heqSwap
      rcases hbc with hbc | hbc
      · right; right; left
        exact ⟨hbc.1, ha, hbc.2⟩
      · right; right; right; left
        exact ⟨hbc.1, ha, hbc.2⟩
    · have heqSwap : α 2 ^ 2 + α 0 ^ 2 + α 1 ^ 2 = 5 * Real.pi ^ 2 / 16 := by
        linarith
      obtain ⟨ha, hbc⟩ :=
        sum_sq_eq_of_largest (h0 2) (h0 0) (h0 1) (hcap 2) h.1 h.2
          (by linarith) heqSwap
      rcases hbc with hbc | hbc
      · right; right; right; right; left
        exact ⟨hbc.1, hbc.2, ha⟩
      · right; right; right; right; right
        exact ⟨hbc.1, hbc.2, ha⟩
  · intro hseed
    rcases hseed with h | h | h | h | h | h <;>
      simp only [Fin.sum_univ_three, h.1, h.2.1, h.2.2] <;>
      ring

theorem sum_heaviestUsualSeed {α : Fin 3 → ℝ} (h : IsHeaviestUsualSeed α) :
    ∑ a : Fin 3, α a = 3 * Real.pi / 4 ∧
      ∑ a : Fin 3, α a ^ 2 = 5 * Real.pi ^ 2 / 16 := by
  rcases h with h | h | h | h | h | h <;>
    simp only [Fin.sum_univ_three, h.1, h.2.1, h.2.2] <;>
    constructor <;> ring

/-- The dual-only shield of a heaviest usual seed is the wall itself, and
that wall weighs \(5\pi^2/16\). -/
theorem heaviestUsualSeed_wall {α : Fin 3 → ℝ} (h : IsHeaviestUsualSeed α) :
    let p : TorsionParams := { alpha := α, beta := fun _ => 0 }
    J (dualWallParams p) = 0 ∧
      mass (dualWallParams p) = 5 * Real.pi ^ 2 / 16 ∧
      (∀ a, (dualWallParams p).alpha a + (dualWallParams p).beta a =
        Real.pi / 2) := by
  intro p
  have hsum := sum_heaviestUsualSeed h
  have hJ : J (dualWallParams p) = 0 := by
    rw [J_dualWallParams_eq_sum_alpha]
    simp only [p, hsum.1]
    ring
  refine ⟨hJ, ?_, ?_⟩
  · rw [mass_eq_sum_alpha_of_J_eq_zero hJ]
    simpa [p, dualWallParams] using hsum.2
  · intro a
    simp [p, dualWallParams, dualWall]

/-! ### A silent label closes the ponderomotive channel -/

theorem J_coupleA_zero_label (p : TorsionParams) (A : Fin 3 → ℝ) :
    J (coupleA p 0 A) = J p := by
  simpa using congrArg J (coupleA_zero_label p A)

theorem quadMean_J_coupleA_zero_label (p : TorsionParams)
    (A : ℝ → Fin 3 → ℝ) :
    quadMean (fun ψ => J (coupleA p 0 (A ψ))) = J p := by
  have hfun : (fun ψ => J (coupleA p 0 (A ψ))) = fun _ => J p := by
    funext ψ
    exact J_coupleA_zero_label p (A ψ)
  rw [hfun]
  exact quadMean_const (J p)

/-! ### Magnetic superposition is the remaining dual-only increment -/

theorem mass_rise_eq_J_drop_magnetic (p : TorsionParams) (B : Fin 3 → ℝ) :
    mass (superpose p (magneticFaraday B)) - mass p =
      J p - J (superpose p (magneticFaraday B)) := by
  have h := superpose_magnetic_conserves_J_add_mass p B
  linarith

/-- A nonnegative magnetic increment that is not zero lowers \(J\) strictly. -/
theorem J_superpose_magnetic_lt {p : TorsionParams} {B : Fin 3 → ℝ}
    (hβ : ∀ a, 0 ≤ p.beta a) (hB : ∀ a, 0 ≤ B a)
    (hne : ∑ a : Fin 3, B a ^ 2 ≠ 0) :
    J (superpose p (magneticFaraday B)) < J p := by
  have hnn : 0 ≤ ∑ a : Fin 3, B a ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpos : 0 < ∑ a : Fin 3, B a ^ 2 := lt_of_le_of_ne hnn hne.symm
  have hcross : 0 ≤ ∑ a : Fin 3, p.beta a * B a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hβ a) (hB a)
  have hJ := J_superpose_magnetic p B
  linarith

theorem mass_superpose_magnetic_lt {p : TorsionParams} {B : Fin 3 → ℝ}
    (hβ : ∀ a, 0 ≤ p.beta a) (hB : ∀ a, 0 ≤ B a)
    (hne : ∑ a : Fin 3, B a ^ 2 ≠ 0) :
    mass p < mass (superpose p (magneticFaraday B)) := by
  have hJ := J_superpose_magnetic_lt hβ hB hne
  have hmass := mass_rise_eq_J_drop_magnetic p B
  linarith

/-- On a balanced seed the same increment is repulsive, and the unsigned
mass rises by the drop in \(J\). -/
theorem balanced_magnetic_repels {p : TorsionParams} {B : Fin 3 → ℝ}
    (hJ : J p = 0) (hβ : ∀ a, 0 ≤ p.beta a) (hB : ∀ a, 0 ≤ B a)
    (hne : ∑ a : Fin 3, B a ^ 2 ≠ 0) :
    J (superpose p (magneticFaraday B)) < 0 ∧
      mass p < mass (superpose p (magneticFaraday B)) := by
  have hlt := J_superpose_magnetic_lt hβ hB hne
  have hmass := mass_superpose_magnetic_lt hβ hB hne
  exact ⟨by linarith, hmass⟩

theorem magnetic_increment_rest_silent (B : Fin 3 → ℝ) :
    sandwichIncrement (faradayDual (magneticFaraday B)) (ι 0) = 0 :=
  magnet_rest_kick (magneticFaraday B)

/-- A wall configuration admits no further nonnegative magnetic increment. -/
theorem not_admissible_magnetic_on_wall {p : TorsionParams} {B : Fin 3 → ℝ}
    (hw : ∀ a, p.alpha a + p.beta a = Real.pi / 2)
    (hB : ∀ a, 0 ≤ B a) (hne : ∑ a : Fin 3, B a ^ 2 ≠ 0) :
    ¬ IsAdmissibleContinuous (superpose p (magneticFaraday B)) := by
  intro hadm
  have hex : ∃ a, 0 < B a := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ a, B a = 0 := fun a => le_antisymm (hnone a) (hB a)
    have : ∑ a : Fin 3, B a ^ 2 = 0 := by simp [hzero]
    exact hne this
  obtain ⟨a, ha⟩ := hex
  have hsum := (hadm a).2.2
  simp only [superpose_alpha, superpose_beta, magneticFaraday] at hsum
  linarith [hw a]

theorem maximalShield_on_wall (a : Fin 3) :
    maximalShield.alpha a + maximalShield.beta a = Real.pi / 2 := by
  fin_cases a <;> simp [maximalShield, ceilingWitness]

theorem maximalShield_magnetic_rigid {B : Fin 3 → ℝ}
    (hB : ∀ a, 0 ≤ B a) (hne : ∑ a : Fin 3, B a ^ 2 ≠ 0) :
    ¬ IsAdmissibleContinuous (superpose maximalShield (magneticFaraday B)) :=
  not_admissible_magnetic_on_wall maximalShield_on_wall hB hne

/-- Slack to the wall supplies an admissible magnetic increment. It lowers
a balanced seed into repulsion, raises the unsigned mass, and still exerts
no rest-frame force. -/
theorem exists_admissible_magnetic_repulsion {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hJ : J p = 0)
    (hslack : ∃ a, p.alpha a + p.beta a < Real.pi / 2) :
    ∃ B : Fin 3 → ℝ,
      (∀ a, 0 ≤ B a) ∧ ∑ a : Fin 3, B a ^ 2 ≠ 0 ∧
        IsAdmissibleContinuous (superpose p (magneticFaraday B)) ∧
        J (superpose p (magneticFaraday B)) < 0 ∧
        mass p < mass (superpose p (magneticFaraday B)) ∧
        sandwichIncrement (faradayDual (magneticFaraday B)) (ι 0) = 0 := by
  obtain ⟨i, hi⟩ := hslack
  have hε : 0 < Real.pi / 2 - p.alpha i - p.beta i := by linarith
  let ε : ℝ := Real.pi / 2 - p.alpha i - p.beta i
  let B : Fin 3 → ℝ := fun b => if b = i then ε else 0
  have hB : ∀ b, 0 ≤ B b := by
    intro b
    by_cases hb : b = i
    · simpa [B, hb, ε] using hε.le
    · simp [B, hb]
  have hne : ∑ b : Fin 3, B b ^ 2 ≠ 0 := by
    intro hzero
    have hnn : ∀ b ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ B b ^ 2 :=
      fun _ _ => sq_nonneg _
    have hterm :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
    have hε0 : ε = 0 := sq_eq_zero_iff.mp (by simpa [B] using hterm)
    have hε0' : Real.pi / 2 - p.alpha i - p.beta i = 0 := by simpa [ε] using hε0
    exact absurd hε0' (ne_of_gt hε)
  have hadm : IsAdmissibleContinuous (superpose p (magneticFaraday B)) := by
    intro b
    by_cases hb : b = i
    · refine ⟨?_, ?_, ?_⟩
      · simpa [superpose_alpha, magneticFaraday] using (hp b).1
      · have hβ : 0 ≤ p.beta b + ε := by
          have : 0 ≤ ε := le_of_lt (by simpa [ε] using hε)
          exact add_nonneg (hp b).2.1 this
        simpa [superpose_beta, magneticFaraday, B, hb] using hβ
      · have hsum : p.alpha b + p.beta b + ε = Real.pi / 2 := by
          have hεb : ε = Real.pi / 2 - p.alpha b - p.beta b := by
            simp [ε, hb]
          linarith
        have : (superpose p (magneticFaraday B)).alpha b +
            (superpose p (magneticFaraday B)).beta b =
              p.alpha b + p.beta b + ε := by
          simp [superpose_alpha, superpose_beta, magneticFaraday, B, hb]
          ring
        linarith
    · have hBz : B b = 0 := by simp [B, hb]
      have hα : (superpose p (magneticFaraday B)).alpha b = p.alpha b := by
        simp [superpose_alpha, magneticFaraday]
      have hβ : (superpose p (magneticFaraday B)).beta b = p.beta b + B b := by
        simp [superpose_beta, magneticFaraday]
      rw [hBz] at hβ
      refine ⟨?_, ?_, ?_⟩
      · rw [hα]
        exact (hp b).1
      · rw [hβ]
        simpa using (hp b).2.1
      · rw [hα, hβ]
        simpa using (hp b).2.2
  have hrep := balanced_magnetic_repels hJ (fun b => (hp b).2.1) hB hne
  exact ⟨B, hB, hne, hadm, hrep.1, hrep.2, magnetic_increment_rest_silent B⟩

end Gravity

end DstDiophantine
