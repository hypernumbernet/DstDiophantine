import DstDiophantine.Gravity.ElectronOrbit
import DstDiophantine.Gravity.SignReversal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scattering signs fix the channel-length window

A slow nucleon pair is repulsive at `1/2` fm and attractive throughout `[1, 2]` fm.
For a positive reversal that pattern is exactly `1/2 < r₁ < 1`, hence
`14/15 < ℓ < 19/10`. It does not select a point: `3/5` and `9/10` both match, and
they place the rapidity wall on opposite sides of `1` fm.

`gammaSEqual` is even, so the opposite length has the same signs. Positivity of `r₁`
is the choice of a separation, not a consequence of the repulsive sample.
The charged-pion selector is a different identification and is not used here.
Two sample radii, rather than the whole segment `[1, 2]`, are not the observable:
a later positive chamber can match `1` and `2` while the segment between them changes sign.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

theorem gammaSEqual_even (x : ℝ) : gammaSEqual (-x) = gammaSEqual x := by
  unfold gammaSEqual
  simp [cosh_neg, sinh_neg, cos_neg, sin_neg]

theorem branchNode_zero_eq : branchNode 0 = resonanceRoot1 := by
  have hspec := branchNode_spec 0
  have hroot : resonanceRoot1 ∈ Ioo (((0 : ℕ) : ℝ) * π) (((0 : ℕ) : ℝ) * π + π) ∧
      gammaSEqual resonanceRoot1 = 0 := by
    refine ⟨⟨?_, ?_⟩, resonanceRoot1_gammaSEqual_zero⟩
    · simp
      linarith [resonanceRoot1_bounds.1]
    · simp
      linarith [resonanceRoot1_sharp_bounds.2, pi_gt_three]
  exact (exists_unique_node_branch 0).unique hspec hroot

theorem branchNode_mem_sharp (n : ℕ) :
    branchNode n ∈ Ioo ((n : ℝ) * π + π / 4) ((n : ℝ) * π + π / 2) :=
  node_mem_sharp_branch n (branchNode_spec n).1 (branchNode_spec n).2

/-- Static equal-scale pair at separation `r`, read as repulsive when `γ_s < 0`. -/
def slowPairRepels (ℓ r : ℝ) : Prop :=
  gammaSEqual (ℓ / (2 * r)) < 0

/-- Static equal-scale pair at separation `r`, read as attractive when `γ_s > 0`. -/
def slowPairAttracts (ℓ r : ℝ) : Prop :=
  0 < gammaSEqual (ℓ / (2 * r))

theorem slowPairRepels_neg {ℓ r : ℝ} : slowPairRepels (-ℓ) r ↔ slowPairRepels ℓ r := by
  unfold slowPairRepels
  have harg : (-ℓ) / (2 * r) = -(ℓ / (2 * r)) := by ring
  rw [harg, gammaSEqual_even]

theorem slowPairAttracts_neg {ℓ r : ℝ} :
    slowPairAttracts (-ℓ) r ↔ slowPairAttracts ℓ r := by
  unfold slowPairAttracts
  have harg : (-ℓ) / (2 * r) = -(ℓ / (2 * r)) := by ring
  rw [harg, gammaSEqual_even]

theorem reversalPhase {r₁ r : ℝ} (hr : r ≠ 0) :
    lengthOfReversal r₁ / (2 * r) = resonanceRoot1 * r₁ / r := by
  unfold lengthOfReversal
  field_simp [hr]

/-- Repulsion at `1/2` and attraction on the whole segment `[1, 2]`. -/
def scatteringForceSigns (r₁ : ℝ) : Prop :=
  slowPairRepels (lengthOfReversal r₁) (1 / 2) ∧
    ∀ r : ℝ, 1 ≤ r → r ≤ 2 → slowPairAttracts (lengthOfReversal r₁) r

theorem scatteringForceSigns_neg {r₁ : ℝ} :
    scatteringForceSigns (-r₁) ↔ scatteringForceSigns r₁ := by
  have hlen : lengthOfReversal (-r₁) = -lengthOfReversal r₁ := by
    unfold lengthOfReversal
    ring
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← slowPairRepels_neg, ← hlen]
      exact h.1
    · intro r hrlo hrhi
      rw [← slowPairAttracts_neg, ← hlen]
      exact h.2 r hrlo hrhi
  · intro h
    refine ⟨?_, ?_⟩
    · rw [hlen, slowPairRepels_neg]
      exact h.1
    · intro r hrlo hrhi
      rw [hlen, slowPairAttracts_neg]
      exact h.2 r hrlo hrhi

/-- Positive reversal whose slow-pair signs match the scattering window. -/
def scatteringSignCuts (r₁ : ℝ) : Prop :=
  0 < r₁ ∧ scatteringForceSigns r₁

theorem scatteringForceSigns_of_window {r₁ : ℝ} (hr0 : 1 / 2 < r₁) (hr1 : r₁ < 1) :
    scatteringForceSigns r₁ := by
  have hx := firstNode_num_window
  have hxpos : 0 < resonanceRoot1 := lt_trans (by norm_num) hx.1
  constructor
  · unfold slowPairRepels
    rw [reversalPhase (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    have hrew : resonanceRoot1 * r₁ / (1 / 2) = 2 * resonanceRoot1 * r₁ := by ring
    rw [hrew]
    refine gammaSEqual_neg_right_of_first_node ⟨?_, ?_⟩
    · nlinarith [hxpos]
    · have htwo : 2 * resonanceRoot1 * r₁ < 2 := by nlinarith
      linarith [pi_gt_three]
  · intro r hrlo hrhi
    have hrpos : (0 : ℝ) < r := by linarith
    unfold slowPairAttracts
    rw [reversalPhase hrpos.ne']
    refine gammaSEqual_pos_left_of_first_node ⟨?_, ?_⟩
    · positivity
    · rw [div_lt_iff₀ hrpos]
      nlinarith

private theorem exists_node_past {x : ℝ} (_hx : 0 ≤ x) : ∃ n : ℕ, x < branchNode n := by
  refine ⟨Nat.floor (x / π) + 1, ?_⟩
  have hπ : 0 < π := pi_pos
  have hdiv : x / π < ↑(Nat.floor (x / π)) + 1 := Nat.lt_floor_add_one (x / π)
  have hxlt : x < (↑(Nat.floor (x / π)) + 1) * π := (div_lt_iff₀ hπ).mp hdiv
  have hnode : (↑(Nat.floor (x / π)) + 1) * π < branchNode (Nat.floor (x / π) + 1) := by
    have hlt := (mem_Ioo.mp (branchNode_spec (Nat.floor (x / π) + 1)).1).1
    simpa [Nat.cast_add, Nat.cast_one] using hlt
  linarith

private theorem exists_branch_gap {x : ℝ} (hx : branchNode 0 < x) (hγ : gammaSEqual x ≠ 0) :
    ∃ n : ℕ, branchNode n < x ∧ x < branchNode (n + 1) := by
  have hx0 : 0 ≤ x := by
    have hlo := (mem_Ioo.mp (branchNode_mem_sharp 0)).1
    simp only [Nat.cast_zero, zero_mul, zero_add] at hlo
    have hpos : (0 : ℝ) < branchNode 0 := by linarith [pi_pos]
    exact le_of_lt (lt_trans hpos hx)
  obtain ⟨N, hN⟩ := exists_node_past hx0
  have hgap : ∀ M : ℕ, x < branchNode M → ∃ n, branchNode n < x ∧ x < branchNode (n + 1) := by
    intro M
    induction M with
    | zero =>
        intro hlt
        exact absurd hlt (not_lt_of_gt hx)
    | succ M ih =>
        intro hlt
        by_cases hprev : x < branchNode M
        · exact ih hprev
        · have hle : branchNode M ≤ x := le_of_not_gt hprev
          have hstrict : branchNode M < x := by
            rcases eq_or_lt_of_le hle with hEq | hlt'
            · exact absurd (hEq ▸ (branchNode_spec M).2) hγ
            · exact hlt'
          exact ⟨M, hstrict, hlt⟩
  exact hgap N hN

private theorem gamma_pos_later_well {x : ℝ} (hx : branchNode 0 < x) (hγ : 0 < gammaSEqual x) :
    ∃ k : ℕ, x ∈ Ioo (branchNode (2 * k + 1)) (branchNode (2 * k + 2)) := by
  obtain ⟨n, hn, hn'⟩ := exists_branch_gap hx hγ.ne'
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, hk⟩ := h
    have hmem : x ∈ Ioo (branchNode (2 * k)) (branchNode (2 * k + 1)) := by
      subst hk
      refine ⟨?_, ?_⟩
      · rw [two_mul]
        exact hn
      · rw [two_mul]
        exact hn'
    exact absurd (gammaSEqual_neg_between_even k hmem) (not_lt_of_gt hγ)
  · obtain ⟨k, hk⟩ := h
    have hmem : x ∈ Ioo (branchNode (2 * k + 1)) (branchNode (2 * k + 2)) := by
      subst hk
      refine ⟨hn, ?_⟩
      rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring]
      exact hn'
    exact ⟨k, hmem⟩

private theorem segment_gamma_pos {φ : ℝ} (hφ : 0 < φ)
    (hatt : ∀ r : ℝ, 1 ≤ r → r ≤ 2 → 0 < gammaSEqual (φ / r)) :
    ∀ x, x ∈ Icc (φ / 2) φ → 0 < gammaSEqual x := by
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le (by linarith : (0 : ℝ) < φ / 2) hx.1
  have hrlo : 1 ≤ φ / x := by
    rw [le_div_iff₀ hxpos]
    linarith [hx.2]
  have hrhi : φ / x ≤ 2 := by
    rw [div_le_iff₀ hxpos]
    linarith [hx.1]
  have hγ := hatt (φ / x) hrlo hrhi
  have hrew : φ / (φ / x) = x := by field_simp [hφ.ne', hxpos.ne']
  rwa [hrew] at hγ

private theorem doubled_segment_not_in_later_well {k : ℕ} {φ : ℝ} (hφ : 0 < φ)
    (hseg : ∀ x, x ∈ Icc (φ / 2) φ →
      x ∈ Ioo (branchNode (2 * k + 1)) (branchNode (2 * k + 2))) : False := by
  have hhalf := hseg (φ / 2) ⟨le_rfl, by linarith⟩
  have hfull := hseg φ ⟨by linarith, le_rfl⟩
  have hleft := branchNode_mem_sharp (2 * k + 1)
  have hright := branchNode_mem_sharp (2 * k + 2)
  have hπ : 0 < π := pi_pos
  have hlower : ((2 * k + 1 : ℕ) : ℝ) * π + π / 4 < φ / 2 := by
    have hnode : ((2 * k + 1 : ℕ) : ℝ) * π + π / 4 < branchNode (2 * k + 1) :=
      (mem_Ioo.mp hleft).1
    linarith [hhalf.1]
  have hupper : φ < ((2 * k + 2 : ℕ) : ℝ) * π + π / 2 := by
    have hnode : branchNode (2 * k + 2) < ((2 * k + 2 : ℕ) : ℝ) * π + π / 2 :=
      (mem_Ioo.mp hright).2
    linarith [hfull.2]
  have hspan : ((2 * k + 2 : ℕ) : ℝ) * π + π / 2 -
      (((2 * k + 1 : ℕ) : ℝ) * π + π / 4) = π + π / 4 := by
    have hstep : ((2 * k + 2 : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [hstep]
    ring
  have hshort : φ / 2 < π + π / 4 := by
    have hdiff : φ - φ / 2 <
        (((2 * k + 2 : ℕ) : ℝ) * π + π / 2) - (((2 * k + 1 : ℕ) : ℝ) * π + π / 4) := by
      linarith [hlower, hupper]
    have hhalfφ : φ - φ / 2 = φ / 2 := by ring
    linarith [hspan, hdiff, hhalfφ]
  have hone : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 (2 * k)
  have hlong : π + π / 4 < φ / 2 := by
    have hbase : (1 : ℝ) * π + π / 4 ≤ ((2 * k + 1 : ℕ) : ℝ) * π + π / 4 := by
      nlinarith [hπ, hone]
    linarith [hlower, hbase]
  linarith

private theorem forceSigns_window_pos {r₁ : ℝ} (hr : 0 < r₁) (h : scatteringForceSigns r₁) :
    1 / 2 < r₁ ∧ r₁ < 1 := by
  have hxpos : 0 < resonanceRoot1 :=
    lt_trans (by norm_num) firstNode_num_window.1
  set φ : ℝ := resonanceRoot1 * r₁
  have hφ : 0 < φ := by positivity
  have hrep : gammaSEqual (2 * φ) < 0 := by
    have hraw := h.1
    unfold slowPairRepels at hraw
    rw [reversalPhase (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hraw
    have hrew : resonanceRoot1 * r₁ / (1 / 2) = 2 * φ := by
      dsimp [φ]
      ring
    rwa [hrew] at hraw
  have hatt : ∀ r : ℝ, 1 ≤ r → r ≤ 2 → 0 < gammaSEqual (φ / r) := by
    intro r hrlo hrhi
    have hrpos : (0 : ℝ) < r := by linarith
    have hraw := h.2 r hrlo hrhi
    unfold slowPairAttracts at hraw
    rw [reversalPhase hrpos.ne'] at hraw
    simpa [φ] using hraw
  have hseg := segment_gamma_pos hφ hatt
  have hφ_lt : φ < resonanceRoot1 := by
    by_contra hge
    have hφge : resonanceRoot1 ≤ φ := le_of_not_gt hge
    have hhalf_ge : resonanceRoot1 ≤ φ / 2 := by
      by_contra hlt
      have hlt' : φ / 2 < resonanceRoot1 := lt_of_not_ge hlt
      have hmem : resonanceRoot1 ∈ Icc (φ / 2) φ := ⟨hlt'.le, hφge⟩
      have hγ := hseg resonanceRoot1 hmem
      rw [resonanceRoot1_gammaSEqual_zero] at hγ
      exact lt_irrefl (0 : ℝ) hγ
    have hhalf_pos : 0 < gammaSEqual (φ / 2) :=
      hseg (φ / 2) ⟨le_rfl, by linarith⟩
    have hhalf_gt : branchNode 0 < φ / 2 := by
      rw [branchNode_zero_eq]
      exact lt_of_le_of_ne hhalf_ge (by
        intro hEq
        have hzero : gammaSEqual (φ / 2) = 0 := by
          rw [← hEq, resonanceRoot1_gammaSEqual_zero]
        linarith)
    obtain ⟨k, hk⟩ := gamma_pos_later_well hhalf_gt hhalf_pos
    have hfull_lt : φ < branchNode (2 * k + 2) := by
      by_contra hnot
      have hle : branchNode (2 * k + 2) ≤ φ := le_of_not_gt hnot
      have hnode_mem : branchNode (2 * k + 2) ∈ Icc (φ / 2) φ := by
        refine ⟨le_of_lt hk.2, hle⟩
      have hγ := hseg _ hnode_mem
      rw [(branchNode_spec (2 * k + 2)).2] at hγ
      exact lt_irrefl (0 : ℝ) hγ
    have hinside : ∀ x, x ∈ Icc (φ / 2) φ →
        x ∈ Ioo (branchNode (2 * k + 1)) (branchNode (2 * k + 2)) := by
      intro x hx
      refine ⟨?_, ?_⟩
      · exact lt_of_lt_of_le hk.1 hx.1
      · exact lt_of_le_of_lt hx.2 hfull_lt
    exact doubled_segment_not_in_later_well hφ hinside
  have htwo_gt : resonanceRoot1 < 2 * φ := by
    by_contra hle
    have hle' : 2 * φ ≤ resonanceRoot1 := le_of_not_gt hle
    have hpos2 : 0 < 2 * φ := by linarith
    have hγ : 0 ≤ gammaSEqual (2 * φ) := by
      rcases eq_or_lt_of_le hle' with hEq | hlt
      · rw [hEq, resonanceRoot1_gammaSEqual_zero]
      · exact (gammaSEqual_pos_left_of_first_node ⟨hpos2, hlt⟩).le
    linarith
  constructor
  · have hmid : resonanceRoot1 * (1 / 2) < resonanceRoot1 * r₁ := by
      dsimp [φ] at htwo_gt
      linarith
    exact (mul_lt_mul_iff_of_pos_left hxpos).mp hmid
  · have hmid : resonanceRoot1 * r₁ < resonanceRoot1 * 1 := by
      simpa [φ] using hφ_lt
    exact (mul_lt_mul_iff_of_pos_left hxpos).mp hmid

theorem scatteringForceSigns_iff_abs {r₁ : ℝ} :
    scatteringForceSigns r₁ ↔ 1 / 2 < |r₁| ∧ |r₁| < 1 := by
  constructor
  · intro h
    have hr0 : r₁ ≠ 0 := by
      intro h0
      have hrep := h.1
      rw [h0] at hrep
      unfold slowPairRepels lengthOfReversal at hrep
      have harg : (2 * resonanceRoot1 * (0 : ℝ)) / (2 * (1 / 2)) = 0 := by ring
      rw [harg, gammaSEqual_zero] at hrep
      linarith
    have hsigns : scatteringForceSigns |r₁| := by
      rcases le_total (0 : ℝ) r₁ with hle | hle
      · rw [abs_of_nonneg hle]
        exact h
      · rw [abs_of_nonpos hle]
        exact (scatteringForceSigns_neg).mpr h
    exact forceSigns_window_pos (abs_pos.mpr hr0) hsigns
  · intro h
    have hpos : scatteringForceSigns |r₁| :=
      scatteringForceSigns_of_window h.1 h.2
    rcases le_total (0 : ℝ) r₁ with hle | hle
    · rwa [abs_of_nonneg hle] at hpos
    · rw [abs_of_nonpos hle] at hpos
      exact (scatteringForceSigns_neg).mp hpos

/-- The scattering signs on a positive reversal are the window `1/2 < r₁ < 1`. -/
theorem scatteringSignCuts_iff {r₁ : ℝ} :
    scatteringSignCuts r₁ ↔ 1 / 2 < r₁ ∧ r₁ < 1 := by
  constructor
  · intro h
    have habs := (scatteringForceSigns_iff_abs).mp h.2
    rw [abs_of_pos h.1] at habs
    exact habs
  · intro h
    have hpos : 0 < r₁ := by linarith
    refine ⟨hpos, (scatteringForceSigns_iff_abs).mpr ?_⟩
    rw [abs_of_pos hpos]
    exact h

theorem length_window_of_scatteringSignCuts {r₁ : ℝ} (h : scatteringSignCuts r₁) :
    (14 / 15 : ℝ) < lengthOfReversal r₁ ∧ lengthOfReversal r₁ < 19 / 10 :=
  lengthOfReversal_bounds ((scatteringSignCuts_iff).mp h).1 ((scatteringSignCuts_iff).mp h).2

theorem scatteringSignCuts_not_unique : ¬ ∃! r₁ : ℝ, scatteringSignCuts r₁ := by
  intro h
  obtain ⟨r, -, huniq⟩ := h
  have h35 : scatteringSignCuts (3 / 5) := (scatteringSignCuts_iff).mpr (by norm_num)
  have h910 : scatteringSignCuts (9 / 10) := (scatteringSignCuts_iff).mpr (by norm_num)
  have hleft := huniq (3 / 5) h35
  have hright := huniq (9 / 10) h910
  exact absurd (hleft.trans hright.symm) (by norm_num)

theorem scattering_second_node_below_core {r₁ : ℝ} (h : scatteringSignCuts r₁) :
    ∃ x₂ ∈ Ioo (π + π / 4) (π + π / 2), gammaSEqual x₂ = 0 ∧
      layerRadius (lengthOfReversal r₁) x₂ < (1 / 2 : ℝ) :=
  second_node_below_core ((scatteringSignCuts_iff).mp h).1 ((scatteringSignCuts_iff).mp h).2

theorem scattering_wall_below_chargeRadii {r₁ : ℝ} (h : scatteringSignCuts r₁) :
    2 * lengthOfReversal r₁ / π < (he4ChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (deuteronChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (oxygen16ChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (calcium40ChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (calcium48ChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (lead208ChargeRadiusFmLower : ℝ) :=
  reversal_wall_below_chargeRadii (lt_trans (by norm_num) ((scatteringSignCuts_iff).mp h).1)
    ((scatteringSignCuts_iff).mp h).2

theorem scattering_wall_below_spacing {r₁ s : ℝ} (h : scatteringSignCuts r₁) (hs : 0 < s)
    (hcube : s ^ 3 = (1 / saturationDensityFm3Approx : ℝ)) :
    2 * lengthOfReversal r₁ / π < s :=
  reversal_wall_below_spacing (lt_trans (by norm_num) ((scatteringSignCuts_iff).mp h).1)
    ((scatteringSignCuts_iff).mp h).2 hs hcube

theorem scattering_channelMassRatio_window {r₁ : ℝ} (h : scatteringSignCuts r₁) :
    (2 / 19 : ℝ) < channelMassRatio r₁ ∧ channelMassRatio r₁ < 9 / 28 :=
  channelMassRatio_window ((scatteringSignCuts_iff).mp h).1 ((scatteringSignCuts_iff).mp h).2

theorem scattering_wall_inside_one :
    ∃ r₁ : ℝ, scatteringSignCuts r₁ ∧ 2 * lengthOfReversal r₁ / π < 1 :=
  ⟨3 / 5, (scatteringSignCuts_iff).mpr (by norm_num), window_does_not_fix_wall_against_one.1⟩

theorem scattering_wall_outside_one :
    ∃ r₁ : ℝ, scatteringSignCuts r₁ ∧ 1 < 2 * lengthOfReversal r₁ / π :=
  ⟨9 / 10, (scatteringSignCuts_iff).mpr (by norm_num), window_does_not_fix_wall_against_one.2⟩

theorem scattering_coulomb_below_deuteron :
    ∃ r₁ : ℝ, scatteringSignCuts r₁ ∧
      (coulombMeVFm : ℝ) / r₁ < (deuteronBindingMeVLower : ℝ) :=
  ⟨9 / 10, (scatteringSignCuts_iff).mpr (by norm_num),
    coulomb_lt_deuteronBinding_of_wide (by norm_num) (by norm_num)⟩

theorem scattering_coulomb_above_deuteron :
    ∃ r₁ : ℝ, scatteringSignCuts r₁ ∧
      (deuteronBindingMeVUpper : ℝ) < (coulombMeVFm : ℝ) / r₁ :=
  ⟨3 / 5, (scatteringSignCuts_iff).mpr (by norm_num),
    coulomb_gt_deuteronBinding_of_narrow (by norm_num) (by norm_num)⟩

end Gravity

end DstDiophantine
