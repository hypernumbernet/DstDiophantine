import DstDiophantine.Gravity.ElectronForce
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Electronegativity along the outer-well segment

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. Nothing here produces a Pauling number, an
Allred–Rochow number, a Mulliken average, or a screened charge. The
cancellation on the segment is not a seat, not a shell, and not a bond
equilibrium. No centrifugal term is added.

## What is proved

* At one phase in the outer well the pull is the nuclear charge times
  `4x²/γ_s`. A larger charge pulls more. The same charge pulls more at a
  larger phase. A smaller charge outpulls a larger one only at a larger phase.
* On the segment between charges `Z` and `W`, with phase `φ = ℓ/(2D)` strictly
  below `x₁/2`, an electron fraction `t` keeps both distances in the outer
  well precisely on `(φ/x₁, 1 - φ/x₁)`. The net pull toward `Z` is
  `Z Y(φ/t) - W Y(φ/(1-t))`. It is strictly decreasing in `t` and vanishes
  once.
* At the midpoint the pull is `(Z-W) Y(2φ)`. When `Z > W > 0` the root lies
  strictly above `1/2`, so it is closer to the smaller charge, and the side
  drawn toward the larger charge is the longer side. Equal charges cancel at
  the midpoint. On the side toward `Z` the force points toward `Z`, and on the
  side toward `W` it points toward `W`. Raising `Z` moves the root toward `W`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set

/-! ### Ordering the pull -/

theorem charge_orders_pull {Z W x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1)
    (hZ : 0 ≤ Z) (hW : Z < W) :
    Z * pairAttraction x < W * pairAttraction x := by
  have hY : 0 < pairAttraction x := pairAttraction_pos_outer hx
  have hWpos : 0 < W := lt_of_le_of_lt hZ hW
  linarith [mul_pos (sub_pos.mpr hW) hY, hWpos]

theorem phase_orders_pull {Z x y : ℝ} (hZ : 0 < Z)
    (hx : x ∈ Ioo 0 resonanceRoot1) (hy : y ∈ Ioo 0 resonanceRoot1) (hxy : x < y) :
    Z * pairAttraction x < Z * pairAttraction y :=
  mul_lt_mul_of_pos_left (pairAttraction_strictMono_outer hx hy hxy) hZ

/-- A smaller charge outpulls a larger one only by standing at a larger phase. -/
theorem weaker_charge_closer {Z W x y : ℝ} (hZ : 0 < Z) (hW : Z < W)
    (hx : x ∈ Ioo 0 resonanceRoot1) (hy : y ∈ Ioo 0 resonanceRoot1)
    (hp : W * pairAttraction y < Z * pairAttraction x) :
    y < x := by
  by_contra hge
  have hle : x ≤ y := le_of_not_gt hge
  rcases eq_or_lt_of_le hle with rfl | hlt
  · linarith [charge_orders_pull hx (le_of_lt hZ) hW]
  · linarith [phase_orders_pull hZ hx hy hlt, charge_orders_pull hy (le_of_lt hZ) hW]

/-! ### The open segment on which both distances lie in the outer well -/

/-- Fraction `t` of the segment, measured from the charge of phase weight `φ`. -/
noncomputable def segmentPhase (φ t : ℝ) : ℝ := φ / t

/-- Fractions that keep both nucleus–electron distances in the outer well.
`φ = ℓ/(2D)` is the phase of the nuclear separation. -/
noncomputable def segmentSlot (φ : ℝ) : Set ℝ :=
  Ioo (φ / resonanceRoot1) (1 - φ / resonanceRoot1)

/-- Net pull toward the first nucleus, in units of `k e²/ℓ²`. -/
noncomputable def segmentPull (Z W φ t : ℝ) : ℝ :=
  Z * pairAttraction (segmentPhase φ t) - W * pairAttraction (segmentPhase φ (1 - t))

theorem sepPhase_outer {ℓ D : ℝ} (hℓ : 0 < ℓ) (hD : ℓ / resonanceRoot1 < D) :
    ℓ / (2 * D) ∈ Ioo 0 (resonanceRoot1 / 2) := by
  have hroot : 0 < resonanceRoot1 :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
  have hDpos : 0 < D := lt_trans (div_pos hℓ hroot) hD
  refine ⟨div_pos hℓ (by linarith : (0 : ℝ) < 2 * D), ?_⟩
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * D)]
  have hright : resonanceRoot1 / 2 * (2 * D) = resonanceRoot1 * D := by ring
  rw [hright]
  have hmul : ℓ < D * resonanceRoot1 := (div_lt_iff₀ hroot).mp hD
  linarith

private theorem segmentPhase_mem {φ t : ℝ} (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2))
    (ht : t ∈ segmentSlot φ) :
    segmentPhase φ t ∈ Ioo 0 resonanceRoot1 ∧
      segmentPhase φ (1 - t) ∈ Ioo 0 resonanceRoot1 := by
  have hroot : 0 < resonanceRoot1 :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
  have ht0 : 0 < t := lt_trans (div_pos hφ.1 hroot) ht.1
  have h1t : 0 < 1 - t := by
    have : t < 1 - φ / resonanceRoot1 := ht.2
    linarith [div_pos hφ.1 hroot]
  constructor
  · refine ⟨div_pos hφ.1 ht0, ?_⟩
    unfold segmentPhase
    rw [div_lt_iff₀ ht0]
    have hmul : φ < t * resonanceRoot1 := (div_lt_iff₀ hroot).mp ht.1
    linarith
  · refine ⟨div_pos hφ.1 h1t, ?_⟩
    unfold segmentPhase
    rw [div_lt_iff₀ h1t]
    have hlt : φ / resonanceRoot1 < 1 - t := by linarith [ht.2]
    have hmul : φ < (1 - t) * resonanceRoot1 := (div_lt_iff₀ hroot).mp hlt
    linarith

theorem segmentSlot_symm {φ t : ℝ} (ht : t ∈ segmentSlot φ) : 1 - t ∈ segmentSlot φ := by
  refine ⟨?_, ?_⟩
  · linarith [ht.2]
  · linarith [ht.1]

theorem half_mem_segmentSlot {φ : ℝ} (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) :
    (1 / 2 : ℝ) ∈ segmentSlot φ := by
  have hroot : 0 < resonanceRoot1 :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
  have hφroot : φ / resonanceRoot1 < 1 / 2 := by
    rw [div_lt_iff₀ hroot]
    linarith [hφ.2]
  exact ⟨hφroot, by linarith⟩

theorem segmentPull_midpoint (Z W φ : ℝ) :
    segmentPull Z W φ (1 / 2) = (Z - W) * pairAttraction (2 * φ) := by
  unfold segmentPull segmentPhase
  have hL : φ / (1 / 2 : ℝ) = 2 * φ := by ring
  have hR : φ / (1 - 1 / 2 : ℝ) = 2 * φ := by ring
  rw [hL, hR]
  ring

private theorem segmentPull_swap (Z W φ t : ℝ) :
    segmentPull W Z φ (1 - t) = -segmentPull Z W φ t := by
  unfold segmentPull segmentPhase
  have h : (1 : ℝ) - (1 - t) = t := by ring
  rw [h]
  ring

private theorem segmentPull_strictAnti {Z W φ : ℝ} (hZ : 0 < Z) (hW : 0 < W)
    (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) :
    StrictAntiOn (segmentPull Z W φ) (segmentSlot φ) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have hmem₁ := segmentPhase_mem hφ ht₁
  have hmem₂ := segmentPhase_mem hφ ht₂
  have ht₁0 : 0 < t₁ := by
    have hroot : 0 < resonanceRoot1 :=
      lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
    exact lt_trans (div_pos hφ.1 hroot) ht₁.1
  have hroot₁ : 0 < resonanceRoot1 :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
  have h1₂ : 0 < 1 - t₂ := by linarith [ht₂.2, div_pos hφ.1 hroot₁]
  have hphaseL : segmentPhase φ t₂ < segmentPhase φ t₁ := by
    unfold segmentPhase
    exact div_lt_div_of_pos_left hφ.1 ht₁0 hlt
  have hphaseR : segmentPhase φ (1 - t₁) < segmentPhase φ (1 - t₂) := by
    unfold segmentPhase
    have hden : 1 - t₂ < 1 - t₁ := by linarith
    exact div_lt_div_of_pos_left hφ.1 h1₂ hden
  have hYL : pairAttraction (segmentPhase φ t₂) < pairAttraction (segmentPhase φ t₁) :=
    pairAttraction_strictMono_outer hmem₂.1 hmem₁.1 hphaseL
  have hYR : pairAttraction (segmentPhase φ (1 - t₁)) <
      pairAttraction (segmentPhase φ (1 - t₂)) :=
    pairAttraction_strictMono_outer hmem₁.2 hmem₂.2 hphaseR
  have hZlt : Z * pairAttraction (segmentPhase φ t₂) <
      Z * pairAttraction (segmentPhase φ t₁) := mul_lt_mul_of_pos_left hYL hZ
  have hWlt : W * pairAttraction (segmentPhase φ (1 - t₁)) <
      W * pairAttraction (segmentPhase φ (1 - t₂)) := mul_lt_mul_of_pos_left hYR hW
  unfold segmentPull
  linarith

/-- On the side toward the first nucleus the pull points that way, and on the
other side it points toward the second nucleus. -/
theorem segmentPull_sign {Z W φ t s : ℝ} (hZ : 0 < Z) (hW : 0 < W)
    (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) (ht : t ∈ segmentSlot φ)
    (hs : s ∈ segmentSlot φ) (h0 : segmentPull Z W φ t = 0) :
    (0 < segmentPull Z W φ s ↔ s < t) ∧ (segmentPull Z W φ s < 0 ↔ t < s) := by
  have hanti := segmentPull_strictAnti hZ hW hφ
  constructor
  · constructor
    · intro hpos
      by_contra hge
      have hle : t ≤ s := le_of_not_gt hge
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact (ne_of_gt hpos) h0
      · linarith [hanti ht hs hlt, h0]
    · intro hlt
      linarith [hanti hs ht hlt, h0]
  · constructor
    · intro hneg
      by_contra hge
      have hle : s ≤ t := le_of_not_gt hge
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact (ne_of_lt hneg) h0
      · linarith [hanti hs ht hlt, h0]
    · intro hlt
      linarith [hanti ht hs hlt, h0]

/-! ### The pull is unbounded at either node -/

private theorem pairAttraction_gt_near_node {a M : ℝ} (ha : a < resonanceRoot1)
    (hM : 0 < M) : ∃ x ∈ Ioo a resonanceRoot1, M < pairAttraction x := by
  have hroot_gt : π / 4 < resonanceRoot1 := resonanceRoot1_sharp_bounds.1
  have hslope : 0 < nodeSlopeHi := nodeSlopeHi_pos
  set b : ℝ := max a (π / 4)
  have hb_lt : b < resonanceRoot1 := max_lt ha hroot_gt
  have hb_ge : π / 4 ≤ b := le_max_right a (π / 4)
  set numLo : ℝ := Real.pi ^ 2 / 4
  have hnumLo : 0 < numLo := by positivity
  set room : ℝ := numLo / (M * nodeSlopeHi)
  have hroom : 0 < room := by positivity
  set ε : ℝ := min room (resonanceRoot1 - b)
  have hε : 0 < ε := lt_min hroom (by linarith)
  set x : ℝ := resonanceRoot1 - ε / 2
  have hx_gt : b < x := by
    unfold x
    linarith [min_le_right room (resonanceRoot1 - b), hε]
  have hx_lt : x < resonanceRoot1 := by
    unfold x
    linarith
  have hx_pi : π / 4 ≤ x := le_trans hb_ge (le_of_lt hx_gt)
  have hx0 : 0 ≤ x := le_trans (by positivity : (0 : ℝ) ≤ π / 4) hx_pi
  have hγpos : 0 < gammaSEqual x :=
    gammaSEqual_pos_of_lt_firstNode hx0 hx_lt
  have hγ_lt : gammaSEqual x < nodeSlopeHi * (resonanceRoot1 - x) :=
    (gammaSEqual_linear_firstNode ⟨hx_pi, hx_lt⟩).2
  have hnum : numLo ≤ 4 * x ^ 2 := by
    unfold numLo
    have hsq : (Real.pi / 4) ^ 2 ≤ x ^ 2 := by
      rw [sq_le_sq]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4), abs_of_nonneg hx0]
      exact hx_pi
    have hpi : (Real.pi / 4) ^ 2 = Real.pi ^ 2 / 16 := by ring
    linarith
  have hgap : resonanceRoot1 - x = ε / 2 := by ring
  have hε_le : ε ≤ room := min_le_left _ _
  have hprod : M * nodeSlopeHi * ε ≤ numLo := by
    unfold room at hε_le
    have hc : 0 < M * nodeSlopeHi := mul_pos hM hslope
    have hmul : ε * (M * nodeSlopeHi) ≤ numLo := (le_div_iff₀ hc).mp hε_le
    linarith
  have hden : 0 < nodeSlopeHi * (ε / 2) := by positivity
  have htwo : 2 * M ≤ numLo / (nodeSlopeHi * (ε / 2)) := by
    rw [le_div_iff₀ hden]
    linarith
  have hγ_gap : gammaSEqual x < nodeSlopeHi * (ε / 2) := by
    simpa [hgap] using hγ_lt
  have hdiv : numLo / (nodeSlopeHi * (ε / 2)) < numLo / gammaSEqual x :=
    div_lt_div_of_pos_left hnumLo hγpos hγ_gap
  have hle : numLo / gammaSEqual x ≤ 4 * x ^ 2 / gammaSEqual x :=
    div_le_div_of_nonneg_right hnum hγpos.le
  have hstep : numLo / (nodeSlopeHi * (ε / 2)) < pairAttraction x := by
    unfold pairAttraction
    exact lt_of_lt_of_le hdiv hle
  have ha_lt : a < x := lt_of_le_of_lt (le_max_left a (π / 4)) hx_gt
  have hMlt : M < numLo / (nodeSlopeHi * (ε / 2)) :=
    lt_of_lt_of_le (by linarith : M < 2 * M) htwo
  exact ⟨x, ⟨ha_lt, hx_lt⟩, lt_trans hMlt hstep⟩

private theorem matePhase_anti {φ x y : ℝ} (hφ : 0 < φ) (hx : φ < x) (hxy : x < y) :
    φ * y / (y - φ) < φ * x / (x - φ) := by
  have hxden : 0 < x - φ := by linarith
  have hyden : 0 < y - φ := by linarith
  rw [div_lt_div_iff₀ hyden hxden]
  apply lt_of_sub_pos
  have hdiff : (φ * x) * (y - φ) - (φ * y) * (x - φ) = φ ^ 2 * (y - x) := by ring
  rw [hdiff]
  exact mul_pos (pow_pos hφ 2) (sub_pos.mpr hxy)

private theorem exists_segmentPull_pos {Z W φ : ℝ} (hZ : 0 < Z) (hW : 0 < W)
    (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) :
    ∃ t ∈ segmentSlot φ, 0 < segmentPull Z W φ t := by
  have hroot : 0 < resonanceRoot1 :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
  have hden : 0 < resonanceRoot1 - φ := by linarith [hφ.2]
  set pR : ℝ := φ * resonanceRoot1 / (resonanceRoot1 - φ)
  have hpR_pos : 0 < pR := by
    unfold pR
    exact div_pos (mul_pos hφ.1 hroot) hden
  have hpR_lt : pR < resonanceRoot1 := by
    unfold pR
    rw [div_lt_iff₀ hden]
    have htwo : 2 * φ < resonanceRoot1 := by
      have hmul : φ * 2 < resonanceRoot1 :=
        (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hφ.2
      linarith
    have hleft : φ * resonanceRoot1 < resonanceRoot1 / 2 * resonanceRoot1 :=
      mul_lt_mul_of_pos_right hφ.2 hroot
    have hhalf : resonanceRoot1 / 2 < resonanceRoot1 - φ := by linarith
    have hright : resonanceRoot1 * (resonanceRoot1 / 2) <
        resonanceRoot1 * (resonanceRoot1 - φ) := mul_lt_mul_of_pos_left hhalf hroot
    have hcomm : resonanceRoot1 / 2 * resonanceRoot1 =
        resonanceRoot1 * (resonanceRoot1 / 2) := by ring
    linarith
  have hpR_gt_φ : φ < pR := by
    unfold pR
    rw [lt_div_iff₀ hden]
    exact mul_lt_mul_of_pos_left (by linarith [hφ.1] : resonanceRoot1 - φ < resonanceRoot1) hφ.1
  set x0 : ℝ := (pR + resonanceRoot1) / 2
  have hx0_gt : pR < x0 := by
    unfold x0
    linarith
  have hx0_lt : x0 < resonanceRoot1 := by
    unfold x0
    linarith
  have hx0φ : φ < x0 := lt_trans hpR_gt_φ hx0_gt
  set m0 : ℝ := φ * x0 / (x0 - φ)
  have hm0_den : 0 < x0 - φ := by linarith
  have hx0_pos : 0 < x0 := lt_trans hφ.1 hx0φ
  have hm0_pos : 0 < m0 := by
    unfold m0
    exact div_pos (mul_pos hφ.1 hx0_pos) hm0_den
  have hm0_lt : m0 < resonanceRoot1 := by
    unfold m0
    rw [div_lt_iff₀ hm0_den]
    have hp : φ * resonanceRoot1 < x0 * (resonanceRoot1 - φ) :=
      (div_lt_iff₀ hden).mp (by simpa [pR] using hx0_gt)
    linarith
  have hm0_mem : m0 ∈ Ioo 0 resonanceRoot1 := ⟨hm0_pos, hm0_lt⟩
  have hMpos : 0 < W * pairAttraction m0 / Z := by
    exact div_pos (mul_pos hW (pairAttraction_pos_outer hm0_mem)) hZ
  obtain ⟨x, hx, hxM⟩ := pairAttraction_gt_near_node hx0_lt hMpos
  have hxφ : φ < x := lt_trans hx0φ hx.1
  have hx_den : 0 < x - φ := by linarith [hxφ]
  set mate : ℝ := φ * x / (x - φ)
  have hmate_lt_m0 : mate < m0 := matePhase_anti hφ.1 hx0φ hx.1
  have hmate_gt : pR < mate := by
    have hanti : φ * resonanceRoot1 / (resonanceRoot1 - φ) < φ * x / (x - φ) :=
      matePhase_anti hφ.1 hxφ hx.2
    simpa [pR, mate] using hanti
  have hmate_lt_root : mate < resonanceRoot1 := by
    unfold mate
    rw [div_lt_iff₀ hx_den]
    have hx_p : pR < x := lt_trans hx0_gt hx.1
    have hp : φ * resonanceRoot1 < x * (resonanceRoot1 - φ) :=
      (div_lt_iff₀ hden).mp (by simpa [pR] using hx_p)
    linarith
  have hmate_mem : mate ∈ Ioo 0 resonanceRoot1 :=
    ⟨lt_trans hpR_pos hmate_gt, hmate_lt_root⟩
  have hYmate : pairAttraction mate < pairAttraction m0 :=
    pairAttraction_strictMono_outer hmate_mem hm0_mem hmate_lt_m0
  have hZpull : W * pairAttraction m0 < Z * pairAttraction x := by
    have hdiv : W * pairAttraction m0 / Z < pairAttraction x := hxM
    have hmul : W * pairAttraction m0 < pairAttraction x * Z := (div_lt_iff₀ hZ).mp hdiv
    linarith
  have hWpull : W * pairAttraction mate < W * pairAttraction m0 :=
    mul_lt_mul_of_pos_left hYmate hW
  set t : ℝ := φ / x
  have hx_pos : 0 < x := lt_trans hφ.1 hxφ
  have hx_p : pR < x := lt_trans hx0_gt hx.1
  have hmul : φ * resonanceRoot1 < x * (resonanceRoot1 - φ) :=
    (div_lt_iff₀ hden).mp (by simpa [pR] using hx_p)
  have ht_slot : t ∈ segmentSlot φ := by
    refine ⟨?_, ?_⟩
    · exact div_lt_div_of_pos_left hφ.1 hx_pos hx.2
    · rw [div_lt_iff₀ hx_pos]
      have hfactor : (1 - φ / resonanceRoot1) * x =
          x * (resonanceRoot1 - φ) / resonanceRoot1 := by
        field_simp [hroot.ne']
      rw [hfactor, lt_div_iff₀ hroot]
      exact hmul
  refine ⟨t, ht_slot, ?_⟩
  have hmate_eq : segmentPhase φ (1 - t) = mate := by
    unfold segmentPhase mate t
    field_simp
  have hleft_eq : segmentPhase φ t = x := by
    unfold segmentPhase t
    field_simp [hx_pos.ne']
    exact div_self hφ.1.ne'
  unfold segmentPull
  rw [hleft_eq, hmate_eq]
  linarith

private theorem continuousOn_pairAttraction_outer :
    ContinuousOn pairAttraction (Ioo 0 resonanceRoot1) := by
  refine ContinuousOn.div ?_ continuous_gammaSEqual.continuousOn ?_
  · exact (by continuity : Continuous fun y : ℝ => 4 * y ^ 2).continuousOn
  · intro x hx
    exact (gammaSEqual_pos_left_of_first_node hx).ne'

private theorem continuousOn_segmentPull {Z W φ a b : ℝ}
    (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) (ha : a ∈ segmentSlot φ)
    (hb : b ∈ segmentSlot φ) (_hab : a ≤ b) :
    ContinuousOn (segmentPull Z W φ) (Icc a b) := by
  have hsub : Icc a b ⊆ segmentSlot φ := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩
  have hL : ContinuousOn (fun t : ℝ => segmentPhase φ t) (Icc a b) := by
    unfold segmentPhase
    refine ContinuousOn.div continuousOn_const continuousOn_id ?_
    intro t ht
    have hroot : 0 < resonanceRoot1 :=
      lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
    exact (lt_trans (div_pos hφ.1 hroot) (hsub ht).1).ne'
  have hR : ContinuousOn (fun t : ℝ => segmentPhase φ (1 - t)) (Icc a b) := by
    unfold segmentPhase
    refine ContinuousOn.div continuousOn_const
      (continuousOn_const.sub continuousOn_id) ?_
    intro t ht
    have hroot : 0 < resonanceRoot1 :=
      lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
    have h1t : 0 < 1 - t := by linarith [(hsub ht).2, div_pos hφ.1 hroot]
    exact h1t.ne'
  unfold segmentPull
  refine ContinuousOn.sub ?_ ?_
  · exact ContinuousOn.mul continuousOn_const
      ((continuousOn_pairAttraction_outer).comp hL fun t ht => (segmentPhase_mem hφ (hsub ht)).1)
  · exact ContinuousOn.mul continuousOn_const
      ((continuousOn_pairAttraction_outer).comp hR fun t ht => (segmentPhase_mem hφ (hsub ht)).2)

theorem exists_unique_segmentPull {Z W φ : ℝ} (hZ : 0 < Z) (hW : 0 < W)
    (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) :
    ∃! t : ℝ, t ∈ segmentSlot φ ∧ segmentPull Z W φ t = 0 := by
  obtain ⟨tpos, htpos, hpos⟩ := exists_segmentPull_pos hZ hW hφ
  obtain ⟨s, hs, hposW⟩ := exists_segmentPull_pos hW hZ hφ
  set tneg : ℝ := 1 - s
  have htneg : tneg ∈ segmentSlot φ := segmentSlot_symm hs
  have hneg : segmentPull Z W φ tneg < 0 := by
    have hswap := segmentPull_swap W Z φ s
    have hlt0 : segmentPull Z W φ (1 - s) < 0 := by linarith [hswap, hposW]
    simpa [tneg] using hlt0
  have hlt : tpos < tneg := by
    by_contra hge
    have hle : tneg ≤ tpos := le_of_not_gt hge
    rcases eq_or_lt_of_le hle with rfl | hord
    · linarith
    · linarith [segmentPull_strictAnti hZ hW hφ htneg htpos hord]
  have hmem : (0 : ℝ) ∈ Ioo (segmentPull Z W φ tneg) (segmentPull Z W φ tpos) :=
    ⟨hneg, hpos⟩
  obtain ⟨t, ht, ht0⟩ := intermediate_value_Ioo' hlt.le
    (continuousOn_segmentPull hφ htpos htneg hlt.le) hmem
  have ht_slot : t ∈ segmentSlot φ :=
    ⟨lt_trans htpos.1 ht.1, lt_trans ht.2 htneg.2⟩
  refine ⟨t, ⟨ht_slot, ht0⟩, ?_⟩
  intro y hy
  exact (segmentPull_strictAnti hZ hW hφ).injOn hy.1 ht_slot (by rw [hy.2, ht0])

theorem segmentRoot_gt_half {Z W φ t : ℝ} (hW : 0 < W) (hZ : W < Z)
    (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) (ht : t ∈ segmentSlot φ)
    (h0 : segmentPull Z W φ t = 0) :
    1 / 2 < t := by
  have hZ0 : 0 < Z := lt_trans hW hZ
  have hmid : 0 < segmentPull Z W φ (1 / 2) := by
    rw [segmentPull_midpoint]
    have h2 : 2 * φ ∈ Ioo 0 resonanceRoot1 := ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
    exact mul_pos (sub_pos.mpr hZ) (pairAttraction_pos_outer h2)
  exact (segmentPull_sign hZ0 hW hφ ht (half_mem_segmentSlot hφ) h0).1.mp hmid

theorem segmentRoot_eq_half {Z φ t : ℝ} (hZ : 0 < Z)
    (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) (ht : t ∈ segmentSlot φ)
    (h0 : segmentPull Z Z φ t = 0) :
    t = 1 / 2 := by
  have hhalf : (1 / 2 : ℝ) ∈ segmentSlot φ := half_mem_segmentSlot hφ
  have hmid : segmentPull Z Z φ (1 / 2) = 0 := by
    rw [segmentPull_midpoint]
    ring
  exact (segmentPull_strictAnti hZ hZ hφ).injOn ht hhalf (by rw [h0, hmid])

/-- The side drawn toward the larger charge is the longer side of the segment. -/
theorem larger_charge_longer_reach {Z W φ t : ℝ} (hW : 0 < W) (hZ : W < Z)
    (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) (ht : t ∈ segmentSlot φ)
    (h0 : segmentPull Z W φ t = 0) :
    (1 - φ / resonanceRoot1) - t < t - φ / resonanceRoot1 := by
  have ht_half : 1 / 2 < t := segmentRoot_gt_half hW hZ hφ ht h0
  linarith

/-- Raising the charge at one end moves the cancellation toward the other end. -/
theorem segmentRoot_moves_with_charge {Z₁ Z₂ W φ t₁ t₂ : ℝ} (hZ₁ : 0 < Z₁) (hZ : Z₁ < Z₂)
    (hW : 0 < W) (hφ : φ ∈ Ioo 0 (resonanceRoot1 / 2)) (ht₁ : t₁ ∈ segmentSlot φ)
    (h₁ : segmentPull Z₁ W φ t₁ = 0) (ht₂ : t₂ ∈ segmentSlot φ)
    (h₂ : segmentPull Z₂ W φ t₂ = 0) :
    t₁ < t₂ := by
  have hmem := (segmentPhase_mem hφ ht₁).1
  have hY : 0 < pairAttraction (segmentPhase φ t₁) := pairAttraction_pos_outer hmem
  have hgt : 0 < segmentPull Z₂ W φ t₁ := by
    unfold segmentPull at h₁ ⊢
    have hdiff : Z₁ * pairAttraction (segmentPhase φ t₁) <
        Z₂ * pairAttraction (segmentPhase φ t₁) :=
      mul_lt_mul_of_pos_right hZ hY
    linarith
  exact (segmentPull_sign (lt_trans hZ₁ hZ) hW hφ ht₂ ht₁ h₂).1.mp hgt

end Gravity

end DstDiophantine
