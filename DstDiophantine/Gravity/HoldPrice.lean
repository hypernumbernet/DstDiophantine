import DstDiophantine.Gravity.EnvelopeLock
import DstDiophantine.Gravity.ShieldHold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The price of holding a shield

Cross-axis compensation buys unsigned mass. Axiswise alignment is what sits
with no force. Between those extremes the cone prices the hold.

On the admissible cone the lag budget is at least \(4M-3\pi^2/4\), with
equality if and only if every axis lies on the wall. For positive stiffness
and \(M\ge 3\pi^2/16\), the written potential is therefore at least
\(2m(M-3\pi^2/16)\), with equality on the wall and nowhere else. A neutral
wall has vanishing sum of lags, so each channel's three holding forces sum
to zero. The bound is attained from the isotropic wall
\(\alpha_a=\beta_a=\pi/4\) through to the heaviest shield, which is the
endpoint of that wall.

A matched hold \(v_a=u_a=m(\alpha_a-\beta_a)\) exchanges power only through
the lag rate. Whenever the two angular velocities agree on each axis, the
power vanishes.

## Paper boundary (do **not** claim)

No electromagnetic coupling, no laboratory protocol, and no identification
of either channel force with a Faraday field. The sum of the three scalar
controls is not a spatial force. Vanishing power along a joint motion is
not free fall.
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-! ### Lag versus unsigned mass -/

theorem four_mass_eq_axisSum_add_lag (p : TorsionParams) :
    4 * mass p =
      (∑ a : Fin 3, (p.alpha a + p.beta a) ^ 2) + lagSq p := by
  rw [mass_coef, lagSq]
  simp only [Fin.sum_univ_three]
  ring

private theorem axisSum_sq_le {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    (p.alpha a + p.beta a) ^ 2 ≤ (Real.pi / 2) ^ 2 := by
  have hs0 : 0 ≤ p.alpha a + p.beta a := add_nonneg (h a).1 (h a).2.1
  have hs : p.alpha a + p.beta a ≤ Real.pi / 2 := (h a).2.2
  have hk : (0 : ℝ) ≤ Real.pi / 2 := le_of_lt Real.pi_div_two_pos
  nlinarith

private theorem axisSum_eq_of_sq_eq {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ Real.pi / 2) (hsq : s ^ 2 = (Real.pi / 2) ^ 2) :
    s = Real.pi / 2 := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · linarith [Real.pi_div_two_pos]

private theorem three_halfPi_sq :
    3 * (Real.pi / 2) ^ 2 = 3 * Real.pi ^ 2 / 4 := by
  ring

private theorem sum_axisSum_sq_eq_iff {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    (∑ a : Fin 3, (p.alpha a + p.beta a) ^ 2) = 3 * Real.pi ^ 2 / 4 ↔
      OnWall p := by
  constructor
  · intro heq
    rw [Fin.sum_univ_three, ← three_halfPi_sq] at heq
    have h0 := axisSum_sq_le h 0
    have h1 := axisSum_sq_le h 1
    have h2 := axisSum_sq_le h 2
    have e0 : (p.alpha 0 + p.beta 0) ^ 2 = (Real.pi / 2) ^ 2 := by linarith
    have e1 : (p.alpha 1 + p.beta 1) ^ 2 = (Real.pi / 2) ^ 2 := by linarith
    have e2 : (p.alpha 2 + p.beta 2) ^ 2 = (Real.pi / 2) ^ 2 := by linarith
    intro a
    have hcase : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
    rcases hcase a with rfl | rfl | rfl
    · exact axisSum_eq_of_sq_eq (add_nonneg (h 0).1 (h 0).2.1) (h 0).2.2 e0
    · exact axisSum_eq_of_sq_eq (add_nonneg (h 1).1 (h 1).2.1) (h 1).2.2 e1
    · exact axisSum_eq_of_sq_eq (add_nonneg (h 2).1 (h 2).2.1) (h 2).2.2 e2
  · intro hw
    rw [Fin.sum_univ_three, hw 0, hw 1, hw 2]
    ring

/-- On the cone the lag budget is at least \(4M-3\pi^2/4\). -/
theorem lagSq_ge_mass_wall {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    4 * mass p - 3 * Real.pi ^ 2 / 4 ≤ lagSq p := by
  have h4 := four_mass_eq_axisSum_add_lag p
  have hle : (∑ a : Fin 3, (p.alpha a + p.beta a) ^ 2) ≤ 3 * Real.pi ^ 2 / 4 := by
    rw [Fin.sum_univ_three, ← three_halfPi_sq]
    linarith [axisSum_sq_le h 0, axisSum_sq_le h 1, axisSum_sq_le h 2]
  linarith

/-- Equality holds exactly on the wall. -/
theorem lagSq_eq_mass_wall_iff {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    lagSq p = 4 * mass p - 3 * Real.pi ^ 2 / 4 ↔ OnWall p := by
  constructor
  · intro heq
    have h4 := four_mass_eq_axisSum_add_lag p
    have hsum :
        (∑ a : Fin 3, (p.alpha a + p.beta a) ^ 2) = 3 * Real.pi ^ 2 / 4 := by
      linarith
    exact (sum_axisSum_sq_eq_iff h).mp hsum
  · intro hw
    have h4 := four_mass_eq_axisSum_add_lag p
    have hsum := (sum_axisSum_sq_eq_iff h).mpr hw
    linarith

theorem lagSq_gt_mass_wall_of_not_onWall {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hw : ¬ OnWall p) :
    4 * mass p - 3 * Real.pi ^ 2 / 4 < lagSq p := by
  have hge := lagSq_ge_mass_wall h
  have hne : lagSq p ≠ 4 * mass p - 3 * Real.pi ^ 2 / 4 := by
    intro heq
    exact hw ((lagSq_eq_mass_wall_iff h).mp heq)
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-! ### Potential price -/

private theorem potential_price_identity (m M : ℝ) :
    (m / 2) * (4 * M - 3 * Real.pi ^ 2 / 4) =
      2 * m * (M - 3 * Real.pi ^ 2 / 16) := by
  ring

/-- The written potential is at least \(2m(M-3\pi^2/16)\). -/
theorem stiffness_ge_excess {m : ℝ} {p : TorsionParams}
    (hm : 0 ≤ m) (h : IsAdmissibleContinuous p) :
    2 * m * (mass p - 3 * Real.pi ^ 2 / 16) ≤ stiffnessPotential m p := by
  rw [stiffnessPotential_eq_lag]
  have hlag := lagSq_ge_mass_wall h
  have hmul :
      (m / 2) * (4 * mass p - 3 * Real.pi ^ 2 / 4) ≤ (m / 2) * lagSq p :=
    mul_le_mul_of_nonneg_left hlag (by linarith)
  linarith [potential_price_identity m (mass p)]

/-- For positive stiffness the price is attained exactly on the wall. -/
theorem stiffness_eq_excess_iff {m : ℝ} {p : TorsionParams}
    (hm : 0 < m) (h : IsAdmissibleContinuous p) :
    stiffnessPotential m p = 2 * m * (mass p - 3 * Real.pi ^ 2 / 16) ↔
      OnWall p := by
  rw [stiffnessPotential_eq_lag]
  constructor
  · intro heq
    have hhalf := heq.trans (potential_price_identity m (mass p)).symm
    have hm2 : m / 2 ≠ 0 := by linarith
    exact (lagSq_eq_mass_wall_iff h).mp (mul_left_cancel₀ hm2 hhalf)
  · intro hw
    rw [(lagSq_eq_mass_wall_iff h).mpr hw]
    exact potential_price_identity m (mass p)

theorem stiffness_gt_excess_of_not_onWall {m : ℝ} {p : TorsionParams}
    (hm : 0 < m) (h : IsAdmissibleContinuous p) (hw : ¬ OnWall p) :
    2 * m * (mass p - 3 * Real.pi ^ 2 / 16) < stiffnessPotential m p := by
  have hge := stiffness_ge_excess (le_of_lt hm) h
  have hne :
      stiffnessPotential m p ≠ 2 * m * (mass p - 3 * Real.pi ^ 2 / 16) := by
    intro heq
    exact hw ((stiffness_eq_excess_iff hm h).mp heq)
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-! ### A neutral wall is a balanced hold -/

theorem sum_lag_eq_zero_of_onWall_neutral {p : TorsionParams}
    (hw : OnWall p) (hn : IsGravNeutral p) :
    ∑ a : Fin 3, (p.alpha a - p.beta a) = 0 := by
  have htwo := two_J_eq_sum_lag_sum p
  rw [hn, Fin.sum_univ_three] at htwo
  have hprod :
      (Real.pi / 2) *
        ((p.alpha 0 - p.beta 0) + (p.alpha 1 - p.beta 1) +
          (p.alpha 2 - p.beta 2)) = 0 := by
    rw [hw 0, hw 1, hw 2] at htwo
    linarith
  have hsum :
      (p.alpha 0 - p.beta 0) + (p.alpha 1 - p.beta 1) +
        (p.alpha 2 - p.beta 2) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt Real.pi_div_two_pos)
  rw [Fin.sum_univ_three]
  exact hsum

/-- The three usual-channel forces of a neutral wall sum to zero, and the
three dual-channel forces are the same coefficients. -/
theorem sum_holdForce_eq_zero_of_onWall_neutral {m : ℝ} {p : TorsionParams}
    (hw : OnWall p) (hn : IsGravNeutral p) :
    ∑ a : Fin 3, m * (p.alpha a - p.beta a) = 0 := by
  rw [← Finset.mul_sum, sum_lag_eq_zero_of_onWall_neutral hw hn, mul_zero]

private theorem fin3_cases : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by
  decide

/-! ### The wall from the free sit to the heaviest shield -/

/-- Neutral wall with lags \((t,-t,0)\). At \(t=0\) the lag vanishes and the
mass is the free-sitting ceiling; at \(t=\pi/2\) the mass and the lag are
those of the heaviest shield. -/
noncomputable def balancedWall (t : ℝ) : TorsionParams where
  alpha := fun a =>
    if a.val = 0 then Real.pi / 4 + t / 2
    else if a.val = 1 then Real.pi / 4 - t / 2
    else Real.pi / 4
  beta := fun a =>
    if a.val = 0 then Real.pi / 4 - t / 2
    else if a.val = 1 then Real.pi / 4 + t / 2
    else Real.pi / 4

theorem isAdmissibleContinuous_balancedWall {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ Real.pi / 2) :
    IsAdmissibleContinuous (balancedWall t) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  intro a
  rcases fin3_cases a with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    simp only [balancedWall] <;>
    norm_num <;>
    linarith

theorem onWall_balancedWall (t : ℝ) : OnWall (balancedWall t) := by
  intro a
  rcases fin3_cases a with rfl | rfl | rfl <;>
    simp only [balancedWall] <;>
    norm_num <;>
    ring

theorem J_balancedWall (t : ℝ) : J (balancedWall t) = 0 := by
  rw [J_coef]
  simp only [balancedWall, Fin.sum_univ_three]
  norm_num

theorem isGravNeutral_balancedWall (t : ℝ) : IsGravNeutral (balancedWall t) :=
  J_balancedWall t

theorem mass_balancedWall (t : ℝ) :
    mass (balancedWall t) = 3 * Real.pi ^ 2 / 16 + t ^ 2 / 2 := by
  rw [mass_coef]
  simp only [balancedWall, Fin.sum_univ_three]
  norm_num
  ring

theorem lagSq_balancedWall (t : ℝ) : lagSq (balancedWall t) = 2 * t ^ 2 := by
  rw [lagSq]
  simp only [balancedWall, Fin.sum_univ_three]
  norm_num
  ring

theorem sum_lag_balancedWall (t : ℝ) :
    ∑ a : Fin 3, ((balancedWall t).alpha a - (balancedWall t).beta a) = 0 := by
  simp only [balancedWall, Fin.sum_univ_three]
  norm_num
  ring

/-- The far end of the family is the heaviest shield. -/
theorem balancedWall_half_pi : balancedWall (Real.pi / 2) = maximalShield := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a
    rcases fin3_cases a with rfl | rfl | rfl <;>
      norm_num [balancedWall, maximalShield, ceilingWitness] <;>
      ring
  · funext a
    rcases fin3_cases a with rfl | rfl | rfl <;>
      norm_num [balancedWall, maximalShield, ceilingWitness] <;>
      ring

theorem stiffness_balancedWall {m t : ℝ} :
    stiffnessPotential m (balancedWall t) =
      2 * m * (mass (balancedWall t) - 3 * Real.pi ^ 2 / 16) := by
  rw [stiffnessPotential_eq_lag, lagSq_balancedWall, mass_balancedWall]
  ring

/-- Neutral wall of unsigned mass \(M\), for \(M\) between the free-sitting
ceiling and the heaviest shield. -/
noncomputable def balancedWallOfMass (M : ℝ) : TorsionParams :=
  balancedWall (Real.sqrt (2 * (M - 3 * Real.pi ^ 2 / 16)))

theorem balancedWallOfMass_spec {M : ℝ}
    (hlo : 3 * Real.pi ^ 2 / 16 ≤ M) (hhi : M ≤ 5 * Real.pi ^ 2 / 16) :
    let p := balancedWallOfMass M
    IsAdmissibleContinuous p ∧ IsGravNeutral p ∧ OnWall p ∧
      mass p = M ∧
      lagSq p = 4 * M - 3 * Real.pi ^ 2 / 4 ∧
      ∑ a : Fin 3, (p.alpha a - p.beta a) = 0 := by
  intro p
  let t : ℝ := Real.sqrt (2 * (M - 3 * Real.pi ^ 2 / 16))
  have hδ : 0 ≤ M - 3 * Real.pi ^ 2 / 16 := sub_nonneg.mpr hlo
  have harg : 0 ≤ 2 * (M - 3 * Real.pi ^ 2 / 16) := mul_nonneg (by norm_num) hδ
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 2 * (M - 3 * Real.pi ^ 2 / 16) := Real.sq_sqrt harg
  have hδhi : M - 3 * Real.pi ^ 2 / 16 ≤ Real.pi ^ 2 / 8 := by
    have hsub :
        M - 3 * Real.pi ^ 2 / 16 ≤ 5 * Real.pi ^ 2 / 16 - 3 * Real.pi ^ 2 / 16 :=
      sub_le_sub_right hhi _
    have hcap : 5 * Real.pi ^ 2 / 16 - 3 * Real.pi ^ 2 / 16 = Real.pi ^ 2 / 8 := by
      ring
    rwa [hcap] at hsub
  have ht_le : t ≤ Real.pi / 2 := by
    have ht2_le : t ^ 2 ≤ (Real.pi / 2) ^ 2 := by
      rw [ht2]
      have htwo :
          2 * (M - 3 * Real.pi ^ 2 / 16) ≤ 2 * (Real.pi ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hδhi (by norm_num)
      have hcap : 2 * (Real.pi ^ 2 / 8) = (Real.pi / 2) ^ 2 := by ring
      linarith
    have hs : Real.sqrt (t ^ 2) ≤ Real.sqrt ((Real.pi / 2) ^ 2) :=
      Real.sqrt_le_sqrt ht2_le
    rw [Real.sqrt_sq ht0, Real.sqrt_sq (le_of_lt Real.pi_div_two_pos)] at hs
    exact hs
  have hadm := isAdmissibleContinuous_balancedWall ht0 ht_le
  have hmass : mass (balancedWall t) = M := by
    rw [mass_balancedWall, ht2]
    ring
  have hlag : lagSq (balancedWall t) = 4 * M - 3 * Real.pi ^ 2 / 4 := by
    rw [lagSq_balancedWall, ht2]
    ring
  have hp : p = balancedWall t := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hp] using hadm
  · simpa [hp] using isGravNeutral_balancedWall t
  · simpa [hp] using onWall_balancedWall t
  · simpa [hp] using hmass
  · simpa [hp] using hlag
  · simpa [hp] using sum_lag_balancedWall t

/-! ### Matched forces exchange power only through the lag rate -/

private theorem holdPower_matched {m : ℝ} {φ θ φdot θdot : Fin 3 → ℝ} :
    holdPower (fun a => m * (φ a - θ a)) (fun a => m * (φ a - θ a)) φdot θdot =
      ∑ a : Fin 3, m * (φ a - θ a) * (φdot a - θdot a) := by
  unfold holdPower
  refine Finset.sum_congr rfl ?_
  intro a _
  ring

/-- A matched hold does no work when the two rotors share an angular
velocity on every axis. Rest is the case of vanishing velocity. -/
theorem holdPower_matched_of_equal_velocity {m : ℝ} {φ θ φdot θdot : Fin 3 → ℝ}
    (h : ∀ a, φdot a = θdot a) :
    holdPower (fun a => m * (φ a - θ a)) (fun a => m * (φ a - θ a))
      φdot θdot = 0 := by
  rw [holdPower_matched]
  refine Finset.sum_eq_zero ?_
  intro a _
  rw [h a]
  ring

end Gravity

end DstDiophantine
