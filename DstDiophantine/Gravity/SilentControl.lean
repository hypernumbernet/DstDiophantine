import DstDiophantine.Gravity.NeutronMagnet
import DstDiophantine.Gravity.ShieldCeiling
import DstDiophantine.Gravity.ShieldClock
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
\(J\), the absolute mass gap, and an identification of either increment
with the weak-interaction operator are **not** derived.

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
* A nonnegative electric increment is the usual-only mirror: it raises \(J\)
  and the unsigned mass by the same amount, holds the magnetic square fixed,
  and is blocked by the same wall. Along one axis its rest-frame sandwich
  is a nonzero electric kick.
* On an equal-scale seed the two increments of one vector write opposite
  values of \(J\) and the same unsigned mass. The magnetic one enlarges the
  magnetic square. A decrease of a dual angle that stays nonnegative spends
  that square, lowers the mass by half the drop, writes attraction, and
  remains admissible. On one equal-scale axis the enlargement drives
  \(\gamma_{\mathrm{eff}}\) further from \(1\), and the decrease brings it back.
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

/-! ### The electric increment is the usual-only mirror -/

theorem J_electricFaraday (E : Fin 3 → ℝ) :
    J (toTorsion (electricFaraday E)) = (1 / 2) * ∑ a : Fin 3, E a ^ 2 := by
  rw [J_faraday]
  simp [electricFaraday, energySq, magneticSq]

theorem faradayCross_electric (p : TorsionParams) (E : Fin 3 → ℝ) :
    faradayCross (toFaraday p) (electricFaraday E) = ∑ a : Fin 3, p.alpha a * E a := by
  simp [faradayCross, toFaraday, electricFaraday]

theorem J_superpose_electric (p : TorsionParams) (E : Fin 3 → ℝ) :
    J (superpose p (electricFaraday E)) =
      J p + ∑ a : Fin 3, p.alpha a * E a + (1 / 2) * ∑ a : Fin 3, E a ^ 2 := by
  rw [J_superpose, J_electricFaraday, faradayCross_electric]
  ring

theorem mass_rise_eq_J_rise_electric (p : TorsionParams) (E : Fin 3 → ℝ) :
    mass (superpose p (electricFaraday E)) - mass p =
      J (superpose p (electricFaraday E)) - J p := by
  have h := superpose_electric_conserves_mass_sub_J p E
  linarith

theorem magneticSq_superpose_electric (p : TorsionParams) (E : Fin 3 → ℝ) :
    magneticSq (toFaraday (superpose p (electricFaraday E))) =
      magneticSq (toFaraday p) := by
  simp [magneticSq, toFaraday, electricFaraday, superpose_beta]

/-- A nonnegative electric increment that is not zero raises \(J\) strictly. -/
theorem J_superpose_electric_gt {p : TorsionParams} {E : Fin 3 → ℝ}
    (hα : ∀ a, 0 ≤ p.alpha a) (hE : ∀ a, 0 ≤ E a)
    (hne : ∑ a : Fin 3, E a ^ 2 ≠ 0) :
    J p < J (superpose p (electricFaraday E)) := by
  have hcross : 0 ≤ ∑ a : Fin 3, p.alpha a * E a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hα a) (hE a)
  have hnn : 0 ≤ ∑ a : Fin 3, E a ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpos : 0 < ∑ a : Fin 3, E a ^ 2 := lt_of_le_of_ne hnn hne.symm
  have hJ := J_superpose_electric p E
  linarith

theorem mass_superpose_electric_gt {p : TorsionParams} {E : Fin 3 → ℝ}
    (hα : ∀ a, 0 ≤ p.alpha a) (hE : ∀ a, 0 ≤ E a)
    (hne : ∑ a : Fin 3, E a ^ 2 ≠ 0) :
    mass p < mass (superpose p (electricFaraday E)) := by
  have hJ := J_superpose_electric_gt hα hE hne
  have hmass := mass_rise_eq_J_rise_electric p E
  linarith

theorem balanced_electric_attracts {p : TorsionParams} {E : Fin 3 → ℝ}
    (hJ : J p = 0) (hα : ∀ a, 0 ≤ p.alpha a) (hE : ∀ a, 0 ≤ E a)
    (hne : ∑ a : Fin 3, E a ^ 2 ≠ 0) :
    0 < J (superpose p (electricFaraday E)) ∧
      mass p < mass (superpose p (electricFaraday E)) := by
  have hlt := J_superpose_electric_gt hα hE hne
  have hmass := mass_superpose_electric_gt hα hE hne
  exact ⟨by linarith, hmass⟩

theorem not_admissible_electric_on_wall {p : TorsionParams} {E : Fin 3 → ℝ}
    (hw : ∀ a, p.alpha a + p.beta a = Real.pi / 2)
    (hE : ∀ a, 0 ≤ E a) (hne : ∑ a : Fin 3, E a ^ 2 ≠ 0) :
    ¬ IsAdmissibleContinuous (superpose p (electricFaraday E)) := by
  intro hadm
  have hex : ∃ a, 0 < E a := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ a, E a = 0 := fun a => le_antisymm (hnone a) (hE a)
    have : ∑ a : Fin 3, E a ^ 2 = 0 := by simp [hzero]
    exact hne this
  obtain ⟨a, ha⟩ := hex
  have hsum := (hadm a).2.2
  simp only [superpose_alpha, superpose_beta, electricFaraday] at hsum
  linarith [hw a]

/-- A one-axis electric increment of nonzero size kicks the rest frame. -/
theorem electric_axis_rest_ne_zero {c : ℝ} {i : Fin 3} (hc : c ≠ 0) :
    let E : Fin 3 → ℝ := fun b => if b = i then c else 0
    sandwichIncrement (faradayUsual (electricFaraday E)) (ι 0) ≠ 0 := by
  intro E
  rw [sandwichIncrement_rest_faradayUsual]
  fin_cases i
  · intro h
    have : c • spatialVec 0 = 0 := by
      simpa [E, electricFaraday, spatialVec] using h
    have hι : spatialVec 0 = 0 := (smul_eq_zero.mp this).resolve_left hc
    exact spatialGen_ne_zero 0 (by simpa [spatialGen, spatialVec] using hι)
  · intro h
    have : c • spatialVec 1 = 0 := by
      simpa [E, electricFaraday, spatialVec] using h
    have hι : spatialVec 1 = 0 := (smul_eq_zero.mp this).resolve_left hc
    exact spatialGen_ne_zero 1 (by simpa [spatialGen, spatialVec] using hι)
  · intro h
    have : c • spatialVec 2 = 0 := by
      simpa [E, electricFaraday, spatialVec] using h
    have hι : spatialVec 2 = 0 := (smul_eq_zero.mp this).resolve_left hc
    exact spatialGen_ne_zero 2 (by simpa [spatialGen, spatialVec] using hι)

theorem exists_admissible_electric_attraction {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hJ : J p = 0)
    (hslack : ∃ a, p.alpha a + p.beta a < Real.pi / 2) :
    ∃ E : Fin 3 → ℝ,
      (∀ a, 0 ≤ E a) ∧ ∑ a : Fin 3, E a ^ 2 ≠ 0 ∧
        IsAdmissibleContinuous (superpose p (electricFaraday E)) ∧
        0 < J (superpose p (electricFaraday E)) ∧
        mass p < mass (superpose p (electricFaraday E)) ∧
        magneticSq (toFaraday (superpose p (electricFaraday E))) =
          magneticSq (toFaraday p) ∧
        sandwichIncrement (faradayUsual (electricFaraday E)) (ι 0) ≠ 0 := by
  obtain ⟨i, hi⟩ := hslack
  have hε : 0 < Real.pi / 2 - p.alpha i - p.beta i := by linarith
  let ε : ℝ := Real.pi / 2 - p.alpha i - p.beta i
  let E : Fin 3 → ℝ := fun b => if b = i then ε else 0
  have hE : ∀ b, 0 ≤ E b := by
    intro b
    by_cases hb : b = i
    · simpa [E, hb, ε] using hε.le
    · simp [E, hb]
  have hne : ∑ b : Fin 3, E b ^ 2 ≠ 0 := by
    intro hzero
    have hnn : ∀ b ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ E b ^ 2 :=
      fun _ _ => sq_nonneg _
    have hterm :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
    have hε0 : ε = 0 := sq_eq_zero_iff.mp (by simpa [E] using hterm)
    exact absurd (by simpa [ε] using hε0) (ne_of_gt hε)
  have hadm : IsAdmissibleContinuous (superpose p (electricFaraday E)) := by
    intro b
    by_cases hb : b = i
    · refine ⟨?_, ?_, ?_⟩
      · have hα : 0 ≤ p.alpha b + ε := add_nonneg (hp b).1 (le_of_lt (by simpa [ε] using hε))
        simpa [superpose_alpha, electricFaraday, E, hb] using hα
      · simpa [superpose_beta, electricFaraday] using (hp b).2.1
      · have hsum : p.alpha b + ε + p.beta b = Real.pi / 2 := by
          have hεb : ε = Real.pi / 2 - p.alpha b - p.beta b := by simp [ε, hb]
          linarith
        have : (superpose p (electricFaraday E)).alpha b +
            (superpose p (electricFaraday E)).beta b = p.alpha b + ε + p.beta b := by
          simp [superpose_alpha, superpose_beta, electricFaraday, E, hb]
        linarith
    · have hEz : E b = 0 := by simp [E, hb]
      refine ⟨?_, ?_, ?_⟩
      · simpa [superpose_alpha, electricFaraday, hEz] using (hp b).1
      · simpa [superpose_beta, electricFaraday] using (hp b).2.1
      · simpa [superpose_alpha, superpose_beta, electricFaraday, hEz] using (hp b).2.2
  have hattr := balanced_electric_attracts hJ (fun b => (hp b).1) hE hne
  have hkick := electric_axis_rest_ne_zero (ne_of_gt hε) (i := i)
  exact ⟨E, hE, hne, hadm, hattr.1, hattr.2, magneticSq_superpose_electric p E,
    by simpa [E, ε] using hkick⟩

/-! ### Equal scale: the square is spent by unwinding, not by repulsion -/

theorem equalScale_increments_opposite (α v : Fin 3 → ℝ) :
    let p : TorsionParams := equalScaleOf { alpha := α, beta := fun _ => 0 }
    J (superpose p (electricFaraday v)) = -J (superpose p (magneticFaraday v)) ∧
      mass (superpose p (electricFaraday v)) =
        mass (superpose p (magneticFaraday v)) := by
  intro p
  have hJ : J p = 0 := J_equalScaleOf _
  have hβ : p.beta = α := by simp [p, equalScaleOf]
  have hα : p.alpha = α := by simp [p, equalScaleOf]
  have hJe := J_superpose_electric p v
  have hJm := J_superpose_magnetic p v
  have hJe' : J (superpose p (electricFaraday v)) =
      ∑ a : Fin 3, α a * v a + (1 / 2) * ∑ a : Fin 3, v a ^ 2 := by
    rw [hJe, hJ]
    simp only [hα]
    ring
  have hJm' : J (superpose p (magneticFaraday v)) =
      -(∑ a : Fin 3, α a * v a + (1 / 2) * ∑ a : Fin 3, v a ^ 2) := by
    rw [hJm, hJ]
    simp only [hβ]
    ring
  refine ⟨?_, ?_⟩
  · rw [hJe', hJm']
    ring
  · have hMe := mass_rise_eq_J_rise_electric p v
    have hMm := mass_rise_eq_J_drop_magnetic p v
    rw [hJ] at hMe hMm
    linarith [hJe', hJm']

theorem mass_eq_half_squares (p : TorsionParams) :
    mass p = (1 / 2) * (energySq (toFaraday p) + magneticSq (toFaraday p)) := by
  simpa using mass_faraday (toFaraday p)

theorem energySq_superpose_magnetic (p : TorsionParams) (B : Fin 3 → ℝ) :
    energySq (toFaraday (superpose p (magneticFaraday B))) = energySq (toFaraday p) := by
  simp [energySq, toFaraday, magneticFaraday, superpose_alpha]

/-- A magnetic increment moves the unsigned mass by half the change in the
magnetic square, and moves \(J\) by the opposite amount. -/
theorem magnetic_increment_half_square (p : TorsionParams) (B : Fin 3 → ℝ) :
    let q := superpose p (magneticFaraday B)
    mass q - mass p =
      (magneticSq (toFaraday q) - magneticSq (toFaraday p)) / 2 ∧
      J q - J p = mass p - mass q := by
  intro q
  have hE : energySq (toFaraday q) = energySq (toFaraday p) :=
    energySq_superpose_magnetic p B
  have hm := mass_eq_half_squares p
  have hq := mass_eq_half_squares q
  have hcons := superpose_magnetic_conserves_J_add_mass p B
  constructor
  · rw [hm, hq, hE]
    ring
  · have : J q + mass q = J p + mass p := hcons
    linarith

theorem magneticSq_strict_mono_of_nonneg {p : TorsionParams} {B : Fin 3 → ℝ}
    (hβ : ∀ a, 0 ≤ p.beta a) (hB : ∀ a, 0 ≤ B a)
    (hne : ∑ a : Fin 3, B a ^ 2 ≠ 0) :
    magneticSq (toFaraday p) <
      magneticSq (toFaraday (superpose p (magneticFaraday B))) := by
  have hdiff : magneticSq (toFaraday (superpose p (magneticFaraday B))) -
      magneticSq (toFaraday p) =
        ∑ a : Fin 3, (2 * p.beta a * B a + B a ^ 2) := by
    simp only [magneticSq, toFaraday, magneticFaraday, superpose_beta, Fin.sum_univ_three]
    ring
  have hnn : 0 ≤ ∑ a : Fin 3, (2 * p.beta a * B a) :=
    Finset.sum_nonneg fun a _ => mul_nonneg (mul_nonneg (by norm_num) (hβ a)) (hB a)
  have hpos : 0 < ∑ a : Fin 3, B a ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) hne.symm
  have hsum : 0 < ∑ a : Fin 3, (2 * p.beta a * B a + B a ^ 2) := by
    have : ∑ a : Fin 3, (2 * p.beta a * B a + B a ^ 2) =
        ∑ a : Fin 3, (2 * p.beta a * B a) + ∑ a : Fin 3, B a ^ 2 := by
      simp [Finset.sum_add_distrib]
    linarith
  linarith

theorem isAdmissibleContinuous_dual_unwind {p : TorsionParams} {v : Fin 3 → ℝ}
    (hp : IsAdmissibleContinuous p) (hv0 : ∀ a, 0 ≤ v a)
    (hvβ : ∀ a, v a ≤ p.beta a) :
    IsAdmissibleContinuous (superpose p (magneticFaraday (fun a => -v a))) := by
  intro a
  refine ⟨?_, ?_, ?_⟩
  · simpa [superpose_alpha, magneticFaraday] using (hp a).1
  · have hβ : 0 ≤ p.beta a + -v a := by linarith [hvβ a]
    simpa [superpose_beta, magneticFaraday] using hβ
  · have hle : p.alpha a + (p.beta a + -v a) ≤ p.alpha a + p.beta a := by linarith [hv0 a]
    have : (superpose p (magneticFaraday (fun b => -v b))).alpha a +
        (superpose p (magneticFaraday (fun b => -v b))).beta a =
          p.alpha a + (p.beta a + -v a) := by
      simp [superpose_alpha, superpose_beta, magneticFaraday]
    linarith [(hp a).2.2]

theorem J_unwind_pos_of_equalScale {α v : Fin 3 → ℝ}
    (hv0 : ∀ a, 0 ≤ v a) (hvα : ∀ a, v a ≤ α a)
    (hne : ∑ a : Fin 3, v a ^ 2 ≠ 0) :
    let p : TorsionParams := equalScaleOf { alpha := α, beta := fun _ => 0 }
    0 < J (superpose p (magneticFaraday (fun a => -v a))) := by
  intro p
  have hJ0 : J p = 0 := J_equalScaleOf _
  have hβ : ∀ a, p.beta a = α a := by intro a; simp [p, equalScaleOf]
  have hformula := J_superpose_magnetic p (fun a => -v a)
  have hcross : ∑ a : Fin 3, p.beta a * -v a = -∑ a : Fin 3, α a * v a := by
    simp only [hβ, mul_neg, Finset.sum_neg_distrib]
  have hsq : ∑ a : Fin 3, (-v a) ^ 2 = ∑ a : Fin 3, v a ^ 2 := by
    simp
  have hJ : J (superpose p (magneticFaraday (fun a => -v a))) =
      ∑ a : Fin 3, α a * v a - (1 / 2) * ∑ a : Fin 3, v a ^ 2 := by
    rw [hformula, hJ0, hcross, hsq]
    ring
  have hlower : (1 / 2) * ∑ a : Fin 3, v a ^ 2 ≤
      ∑ a : Fin 3, α a * v a - (1 / 2) * ∑ a : Fin 3, v a ^ 2 := by
    have hterm : ∀ a, v a ^ 2 ≤ α a * v a := by
      intro a
      nlinarith [hv0 a, hvα a]
    have hle : ∑ a : Fin 3, v a ^ 2 ≤ ∑ a : Fin 3, α a * v a :=
      Finset.sum_le_sum fun a _ => hterm a
    linarith
  have hpos : 0 < ∑ a : Fin 3, v a ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) hne.symm
  linarith

theorem magneticSq_unwind_lt_of_equalScale {α v : Fin 3 → ℝ}
    (hv0 : ∀ a, 0 ≤ v a) (hvα : ∀ a, v a ≤ α a)
    (hne : ∑ a : Fin 3, v a ^ 2 ≠ 0) :
    let p : TorsionParams := equalScaleOf { alpha := α, beta := fun _ => 0 }
    magneticSq (toFaraday (superpose p (magneticFaraday (fun a => -v a)))) <
      magneticSq (toFaraday p) := by
  intro p
  have hβ : ∀ a, p.beta a = α a := by intro a; simp [p, equalScaleOf]
  have hdiff : magneticSq (toFaraday p) -
      magneticSq (toFaraday (superpose p (magneticFaraday (fun a => -v a)))) =
        ∑ a : Fin 3, (2 * α a * v a - v a ^ 2) := by
    simp only [magneticSq, toFaraday, magneticFaraday, superpose_beta, hβ, Fin.sum_univ_three]
    ring
  have hterm : ∀ a, v a ^ 2 ≤ 2 * α a * v a - v a ^ 2 := by
    intro a
    nlinarith [hv0 a, hvα a]
  have hsum : ∑ a : Fin 3, v a ^ 2 ≤ ∑ a : Fin 3, (2 * α a * v a - v a ^ 2) :=
    Finset.sum_le_sum fun a _ => hterm a
  have hpos : 0 < ∑ a : Fin 3, v a ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) hne.symm
  linarith

/-- On a positive equal-scale seed, decreasing a dual angle that is already
present stays admissible, spends the magnetic square, lowers the mass by
half that drop, and writes attraction. The rest-frame sandwich still vanishes. -/
theorem exists_equalScale_unwind_spends {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (heq : ∀ a, p.alpha a = p.beta a)
    (hM : 0 < mass p) :
    ∃ v : Fin 3 → ℝ,
      (∀ a, 0 ≤ v a) ∧ (∀ a, v a ≤ p.beta a) ∧ ∑ a : Fin 3, v a ^ 2 ≠ 0 ∧
        let q := superpose p (magneticFaraday (fun a => -v a))
        IsAdmissibleContinuous q ∧ 0 < J q ∧ mass q < mass p ∧
          magneticSq (toFaraday q) < magneticSq (toFaraday p) ∧
          mass p - mass q = (magneticSq (toFaraday p) - magneticSq (toFaraday q)) / 2 ∧
          sandwichIncrement (faradayDual (magneticFaraday (fun a => -v a))) (ι 0) = 0 := by
  have hex : ∃ i, 0 < p.alpha i := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ a, p.alpha a = 0 := fun a => le_antisymm (hnone a) (hp a).1
    have hβ0 : ∀ a, p.beta a = 0 := fun a => by rw [← heq a, hzero a]
    have hmass : mass p = 0 := by
      rw [mass_coef]
      simp [hzero, hβ0]
    linarith
  obtain ⟨i, hi⟩ := hex
  let v : Fin 3 → ℝ := fun a => if a = i then p.beta i else 0
  have hv0 : ∀ a, 0 ≤ v a := by
    intro a
    by_cases ha : a = i
    · have : 0 ≤ p.beta i := by simpa [heq] using (hp i).1
      simpa [v, ha] using this
    · simp [v, ha]
  have hvβ : ∀ a, v a ≤ p.beta a := by
    intro a
    by_cases ha : a = i
    · simp [v, ha]
    · have : (0 : ℝ) ≤ p.beta a := (hp a).2.1
      simpa [v, ha] using this
  have hne : ∑ a : Fin 3, v a ^ 2 ≠ 0 := by
    intro hzero
    have hnn : ∀ a ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ v a ^ 2 :=
      fun _ _ => sq_nonneg _
    have hterm :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
    have hv0i : v i = 0 := sq_eq_zero_iff.mp (by simpa [v] using hterm)
    have hβi : p.beta i = 0 := by simpa [v] using hv0i
    have hαi : p.alpha i = 0 := by rw [heq i, hβi]
    exact absurd hαi (ne_of_gt hi)
  let q := superpose p (magneticFaraday (fun a => -v a))
  have hadm := isAdmissibleContinuous_dual_unwind hp hv0 hvβ
  have hvα : ∀ a, v a ≤ p.alpha a := by
    intro a
    simpa [heq] using hvβ a
  have hseed : p = equalScaleOf { alpha := p.alpha, beta := fun _ => 0 } :=
    torsionParams_ext (by simp [equalScaleOf]) (by
      funext a
      simp [equalScaleOf, heq])
  have hJpos : 0 < J q := by
    have hpos := J_unwind_pos_of_equalScale hv0 hvα hne
    rwa [← hseed] at hpos
  have hsq : magneticSq (toFaraday q) < magneticSq (toFaraday p) := by
    have hlt := magneticSq_unwind_lt_of_equalScale hv0 hvα hne
    rwa [← hseed] at hlt
  have hhalf := magnetic_increment_half_square p (fun a => -v a)
  have hmass : mass q < mass p := by
    have hdrop : 0 < magneticSq (toFaraday p) - magneticSq (toFaraday q) := by linarith
    have : mass p - mass q = (magneticSq (toFaraday p) - magneticSq (toFaraday q)) / 2 := by
      have := hhalf.1
      simp only [q] at this ⊢
      linarith
    linarith
  have hhalf' : mass p - mass q =
      (magneticSq (toFaraday p) - magneticSq (toFaraday q)) / 2 := by
    have := hhalf.1
    simp only [q] at this ⊢
    linarith
  exact ⟨v, hv0, hvβ, hne, hadm, hJpos, hmass, hsq, hhalf',
    magnetic_increment_rest_silent (fun a => -v a)⟩

/-! ### One equal-scale axis: the clock and the square move apart -/

theorem equalScale_axis_magnetic_lowers_clock {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hcone : 2 * α + ε ≤ Real.pi / 2) :
    gammaEff α (α + ε) < gammaEff α α := by
  have hlo : 0 ≤ α := le_of_lt hα
  have hlt : α < α + ε := by linarith
  have hhi : α + ε ≤ Real.pi / 2 := by linarith
  exact gammaEff_lt_gammaEff_of_lt_beta hα hlo hlt hhi

theorem equalScale_axis_unwind_raises_clock {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hεα : ε ≤ α) (hαπ : α ≤ Real.pi / 2) :
    gammaEff α α < gammaEff α (α - ε) := by
  have hlo : 0 ≤ α - ε := by linarith
  have hlt : α - ε < α := by linarith
  exact gammaEff_lt_gammaEff_of_lt_beta hα hlo hlt hαπ

end Gravity

end DstDiophantine
