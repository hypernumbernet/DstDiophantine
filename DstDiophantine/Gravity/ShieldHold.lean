import DstDiophantine.Gravity.DualRotorDynamics
import DstDiophantine.Gravity.RestMass
import DstDiophantine.Gravity.ShieldCeiling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Holding a shield still

Unsigned mass and the holding force are different budgets. Cross-axis
compensation buys the heaviest neutral states. Axiswise alignment is what
the written action can park with no force.

## Paper boundary (do **not** claim)

No electromagnetic coupling, no laboratory protocol, and no identification
of either channel force with a Faraday field. Vanishing holding force is
not free fall: a common scale can leave the relative rotor away from the
identity.

## What is proved

* Both angular accelerations vanish if and only if, on every axis, the
  usual force and the dual force equal the stiffness times the lag,
  \(v_a=u_a=m(\alpha_a-\beta_a)\). At rest the sum of the Jacobi rates is
  zero.
* For \(m\neq 0\) the zero force occurs exactly on axiswise agreement of
  the rapidities. Every such configuration is neutral, its potential
  vanishes, and on the cone its unsigned mass is at most \(3\pi^2/16\).
* On the cone a neutral configuration has lag budget
  \(\sum(\alpha_a-\beta_a)^2\le\pi^2/2\). The heaviest shield attains it.
* From a pure usual seed, the equal-scale dual-only point has lag budget
  \(0\), and the cross-axis shield of the same rapidity has lag budget
  \(2\alpha^2\).
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-! ### Matched forces park the written action -/

/-- The written two-force system on all three axes. -/
def BothHeld (m : ℝ) (φ θ φddot θddot v u : Fin 3 → ℝ) : Prop :=
  ∀ a, PaperBothSourcedEL m (φ a) (θ a) (φddot a) (θddot a) (v a) (u a)

theorem bothHeld_static_iff {m : ℝ} {φ θ v u : Fin 3 → ℝ} :
    BothHeld m φ θ (fun _ => 0) (fun _ => 0) v u ↔
      ∀ a, v a = m * (φ a - θ a) ∧ u a = m * (φ a - θ a) := by
  constructor
  · intro h a
    rcases h a with ⟨hφ, hθ⟩
    exact ⟨by linarith, by linarith⟩
  · intro h a
    rcases h a with ⟨hv, hu⟩
    exact ⟨by linarith, by linarith⟩

/-- Sum of the two controls' pairings with the two velocities. -/
def holdPower (v u φdot θdot : Fin 3 → ℝ) : ℝ :=
  ∑ a : Fin 3, (v a * φdot a - u a * θdot a)

theorem holdPower_eq_sum_energyDot {m : ℝ}
    {φ θ φdot θdot φddot θddot v u : Fin 3 → ℝ}
    (h : BothHeld m φ θ φddot θddot v u) :
    (∑ a : Fin 3, paperEnergyDot m (φ a) (θ a) (φdot a) (θdot a)
        (φddot a) (θddot a)) =
      holdPower v u φdot θdot := by
  unfold holdPower
  refine Finset.sum_congr rfl ?_
  intro a _
  exact paperEnergyDot_both_sourced (h a)

theorem holdPower_at_rest {v u φdot θdot : Fin 3 → ℝ}
    (hφ : ∀ a, φdot a = 0) (hθ : ∀ a, θdot a = 0) :
    holdPower v u φdot θdot = 0 := by
  unfold holdPower
  refine Finset.sum_eq_zero ?_
  intro a _
  simp [hφ a, hθ a]

/-- Nonzero stiffness: the zero force parks exactly the aligned configurations. -/
theorem bothHeld_zero_force_iff_aligned {m : ℝ} {φ θ : Fin 3 → ℝ} (hm : m ≠ 0) :
    BothHeld m φ θ (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) ↔
      ∀ a, φ a = θ a := by
  constructor
  · intro h a
    have hv := ((bothHeld_static_iff.mp h) a).1
    have hmul : m * (φ a - θ a) = 0 := by simpa using hv
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hm)
  · intro h a
    rw [h a]
    constructor <;> ring

theorem aligned_is_neutral {p : TorsionParams} (h : p.beta = p.alpha) :
    IsGravNeutral p ∧ lagSq p = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  refine ⟨?_, ?_⟩
  · rw [IsGravNeutral, J_coef, Fin.sum_univ_three, h0, h1, h2]
    ring
  · rw [lagSq, Fin.sum_univ_three, h0, h1, h2]
    ring

/-- An aligned admissible shield weighs at most three sixteenths of \(\pi^2\). -/
theorem aligned_mass_le {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (heq : p.beta = p.alpha) :
    IsGravNeutral p ∧ lagSq p = 0 ∧ mass p ≤ 3 * Real.pi ^ 2 / 16 :=
  ⟨(aligned_is_neutral heq).1, (aligned_is_neutral heq).2,
    mass_le_equalScale_ceiling h heq⟩

/-! ### Neutral lag budget -/

private theorem sq_sum_zero_of_nonneg {s0 s1 s2 d0 d1 d2 : ℝ}
    (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2)
    (hd0 : |d0| ≤ s0) (hd1 : |d1| ≤ s1) (hd2 : |d2| ≤ s2)
    (hp0 : 0 ≤ d0) (hp1 : 0 ≤ d1) (hp2 : 0 ≤ d2)
    (hbal : s0 * d0 + s1 * d1 + s2 * d2 = 0) :
    d0 = 0 ∧ d1 = 0 ∧ d2 = 0 := by
  have hnn0 : 0 ≤ s0 * d0 := mul_nonneg hs0 hp0
  have hnn1 : 0 ≤ s1 * d1 := mul_nonneg hs1 hp1
  have hnn2 : 0 ≤ s2 * d2 := mul_nonneg hs2 hp2
  have hz0 : s0 * d0 = 0 := by nlinarith
  have hz1 : s1 * d1 = 0 := by nlinarith
  have hz2 : s2 * d2 = 0 := by nlinarith
  have h0le : d0 ≤ s0 := (abs_le.mp hd0).2
  have h1le : d1 ≤ s1 := (abs_le.mp hd1).2
  have h2le : d2 ≤ s2 := (abs_le.mp hd2).2
  have h0sq : d0 ^ 2 ≤ s0 * d0 := by nlinarith
  have h1sq : d1 ^ 2 ≤ s1 * d1 := by nlinarith
  have h2sq : d2 ^ 2 ≤ s2 * d2 := by nlinarith
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- One nonnegative lag and two nonpositive lags, balanced, stay within \(2k^2\). -/
private theorem lag_sq_le_of_pos_side {k s0 s1 s2 d0 d1 d2 : ℝ}
    (hk0 : s0 ≤ k) (hs0 : 0 ≤ s0) (_hs1 : 0 ≤ s1) (_hs2 : 0 ≤ s2)
    (hd0 : |d0| ≤ s0) (hd1 : |d1| ≤ s1) (hd2 : |d2| ≤ s2)
    (hp : 0 ≤ d0) (hn1 : d1 ≤ 0) (hn2 : d2 ≤ 0)
    (hbal : s0 * d0 + s1 * d1 + s2 * d2 = 0) :
    d0 ^ 2 + d1 ^ 2 + d2 ^ 2 ≤ 2 * k ^ 2 := by
  have h0le : d0 ≤ s0 := (abs_le.mp hd0).2
  have h1lo : -(s1) ≤ d1 := (abs_le.mp hd1).1
  have h2lo : -(s2) ≤ d2 := (abs_le.mp hd2).1
  have hd0sq : d0 ^ 2 ≤ s0 * d0 := by nlinarith
  have hd1sq : d1 ^ 2 ≤ -(s1 * d1) := by nlinarith
  have hd2sq : d2 ^ 2 ≤ -(s2 * d2) := by nlinarith
  have hsum : d0 ^ 2 + d1 ^ 2 + d2 ^ 2 ≤ 2 * (s0 * d0) := by
    have hcancel : -(s1 * d1) + -(s2 * d2) = s0 * d0 := by linarith
    linarith
  have hsd : s0 * d0 ≤ k ^ 2 := by
    have hk : 0 ≤ k := le_trans hs0 hk0
    have hsq : s0 ^ 2 ≤ k ^ 2 := by nlinarith
    nlinarith
  linarith

private theorem lag_sq_le_of_balanced {k s0 s1 s2 d0 d1 d2 : ℝ}
    (hk0 : s0 ≤ k) (hk1 : s1 ≤ k) (hk2 : s2 ≤ k)
    (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2)
    (hd0 : |d0| ≤ s0) (hd1 : |d1| ≤ s1) (hd2 : |d2| ≤ s2)
    (hbal : s0 * d0 + s1 * d1 + s2 * d2 = 0) :
    d0 ^ 2 + d1 ^ 2 + d2 ^ 2 ≤ 2 * k ^ 2 := by
  by_cases h0 : 0 ≤ d0
  · by_cases h1 : 0 ≤ d1
    · by_cases h2 : 0 ≤ d2
      · obtain ⟨z0, z1, z2⟩ :=
          sq_sum_zero_of_nonneg hs0 hs1 hs2 hd0 hd1 hd2 h0 h1 h2 hbal
        simp [z0, z1, z2]
        have hk : 0 ≤ k := le_trans hs0 hk0
        nlinarith
      · -- Axes 0 and 1 nonnegative, axis 2 the unique negative side.
        have h2le : d2 < 0 := lt_of_not_ge h2
        have hflip :
            (-d2) ^ 2 + (-d0) ^ 2 + (-d1) ^ 2 ≤ 2 * k ^ 2 :=
          lag_sq_le_of_pos_side hk2 hs2 hs0 hs1
            (by simpa [abs_neg] using hd2) (by simpa [abs_neg] using hd0)
            (by simpa [abs_neg] using hd1)
            (by linarith) (by linarith) (by linarith)
            (by linarith)
        linarith
    · by_cases h2 : 0 ≤ d2
      · have h1le : d1 < 0 := lt_of_not_ge h1
        have hflip :
            (-d1) ^ 2 + (-d0) ^ 2 + (-d2) ^ 2 ≤ 2 * k ^ 2 :=
          lag_sq_le_of_pos_side hk1 hs1 hs0 hs2
            (by simpa [abs_neg] using hd1) (by simpa [abs_neg] using hd0)
            (by simpa [abs_neg] using hd2)
            (by linarith) (by linarith) (by linarith)
            (by linarith)
        linarith
      · have h1le : d1 < 0 := lt_of_not_ge h1
        have h2le : d2 < 0 := lt_of_not_ge h2
        exact lag_sq_le_of_pos_side hk0 hs0 hs1 hs2 hd0 hd1 hd2 h0 h1le.le h2le.le hbal
  · by_cases h1 : 0 ≤ d1
    · by_cases h2 : 0 ≤ d2
      · have h0le : d0 < 0 := lt_of_not_ge h0
        have hflip :
            (-d0) ^ 2 + (-d1) ^ 2 + (-d2) ^ 2 ≤ 2 * k ^ 2 :=
          lag_sq_le_of_pos_side hk0 hs0 hs1 hs2
            (by simpa [abs_neg] using hd0) (by simpa [abs_neg] using hd1)
            (by simpa [abs_neg] using hd2)
            (by linarith) (by linarith) (by linarith)
            (by linarith)
        linarith
      · have h0le : d0 < 0 := lt_of_not_ge h0
        have h2le : d2 < 0 := lt_of_not_ge h2
        have hperm :
            d1 ^ 2 + d0 ^ 2 + d2 ^ 2 ≤ 2 * k ^ 2 :=
          lag_sq_le_of_pos_side (k := k)
            (s0 := s1) (s1 := s0) (s2 := s2) (d0 := d1) (d1 := d0) (d2 := d2)
            hk1 hs1 hs0 hs2 hd1 hd0 hd2 h1 h0le.le h2le.le (by linarith)
        linarith
    · by_cases h2 : 0 ≤ d2
      · have h0le : d0 < 0 := lt_of_not_ge h0
        have h1le : d1 < 0 := lt_of_not_ge h1
        have hperm :
            d2 ^ 2 + d0 ^ 2 + d1 ^ 2 ≤ 2 * k ^ 2 :=
          lag_sq_le_of_pos_side (k := k)
            (s0 := s2) (s1 := s0) (s2 := s1) (d0 := d2) (d1 := d0) (d2 := d1)
            hk2 hs2 hs0 hs1 hd2 hd0 hd1 h2 h0le.le h1le.le (by linarith)
        linarith
      · have h0le : d0 < 0 := lt_of_not_ge h0
        have h1le : d1 < 0 := lt_of_not_ge h1
        have h2le : d2 < 0 := lt_of_not_ge h2
        obtain ⟨z0, z1, z2⟩ :=
          sq_sum_zero_of_nonneg hs0 hs1 hs2
            (by simpa [abs_neg] using hd0) (by simpa [abs_neg] using hd1)
            (by simpa [abs_neg] using hd2)
            (by linarith : 0 ≤ -d0) (by linarith : 0 ≤ -d1) (by linarith : 0 ≤ -d2)
            (by linarith)
        have e0 : d0 = 0 := by linarith
        have e1 : d1 = 0 := by linarith
        have e2 : d2 = 0 := by linarith
        rw [e0, e1, e2]
        have hk : 0 ≤ k := le_trans hs0 hk0
        nlinarith

theorem two_J_eq_sum_lag_sum (p : TorsionParams) :
    2 * J p =
      ∑ a : Fin 3, (p.alpha a + p.beta a) * (p.alpha a - p.beta a) := by
  rw [J_coef]
  simp only [Fin.sum_univ_three]
  ring

theorem abs_lag_le_axis_sum {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    |p.alpha a - p.beta a| ≤ p.alpha a + p.beta a := by
  have hα := (h a).1
  have hβ := (h a).2.1
  rw [abs_le]
  constructor <;> linarith

/-- A neutral admissible configuration has lag budget at most \(\pi^2/2\). -/
theorem lagSq_le_of_neutral {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hn : IsGravNeutral p) :
    lagSq p ≤ Real.pi ^ 2 / 2 := by
  have hJ : J p = 0 := hn
  have hbal :
      (p.alpha 0 + p.beta 0) * (p.alpha 0 - p.beta 0) +
        (p.alpha 1 + p.beta 1) * (p.alpha 1 - p.beta 1) +
        (p.alpha 2 + p.beta 2) * (p.alpha 2 - p.beta 2) = 0 := by
    have hsum := two_J_eq_sum_lag_sum p
    rw [hJ, Fin.sum_univ_three] at hsum
    linarith
  have hsq :=
    lag_sq_le_of_balanced
      (k := Real.pi / 2)
      (s0 := p.alpha 0 + p.beta 0) (s1 := p.alpha 1 + p.beta 1)
      (s2 := p.alpha 2 + p.beta 2)
      (d0 := p.alpha 0 - p.beta 0) (d1 := p.alpha 1 - p.beta 1)
      (d2 := p.alpha 2 - p.beta 2)
      (h 0).2.2 (h 1).2.2 (h 2).2.2
      (add_nonneg (h 0).1 (h 0).2.1)
      (add_nonneg (h 1).1 (h 1).2.1)
      (add_nonneg (h 2).1 (h 2).2.1)
      (abs_lag_le_axis_sum h 0) (abs_lag_le_axis_sum h 1) (abs_lag_le_axis_sum h 2)
      hbal
  rw [lagSq, Fin.sum_univ_three]
  have htwo : 2 * (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 2 := by ring
  linarith

theorem stiffness_le_of_neutral {m : ℝ} {p : TorsionParams}
    (hm : 0 ≤ m) (h : IsAdmissibleContinuous p) (hn : IsGravNeutral p) :
    stiffnessPotential m p ≤ m * Real.pi ^ 2 / 4 := by
  rw [stiffnessPotential_eq_lag]
  have hlag := lagSq_le_of_neutral h hn
  nlinarith

theorem lagSq_maximalShield : lagSq maximalShield = Real.pi ^ 2 / 2 := by
  rw [lagSq, Fin.sum_univ_three]
  simp only [maximalShield, ceilingWitness]
  norm_num
  ring

theorem stiffness_maximalShield (m : ℝ) :
    stiffnessPotential m maximalShield = m * Real.pi ^ 2 / 4 := by
  rw [stiffnessPotential_eq_lag, lagSq_maximalShield]
  ring

theorem maximalShield_attains_lag :
    IsAdmissibleContinuous maximalShield ∧ IsGravNeutral maximalShield ∧
      lagSq maximalShield = Real.pi ^ 2 / 2 :=
  ⟨isAdmissibleContinuous_maximalShield, J_maximalShield, lagSq_maximalShield⟩

/-! ### Coaxial alignment relaxes the lag; a silent axis raises it -/

theorem lagSq_axisUsual (α : ℝ) : lagSq (axisUsual α) = α ^ 2 := by
  rw [lagSq, Fin.sum_univ_three]
  simp [axisUsual, finCoord]

theorem lagSq_equalScale_axisUsual (α : ℝ) :
    lagSq (equalScaleOf (axisUsual α)) = 0 := by
  rw [lagSq, Fin.sum_univ_three]
  simp [equalScaleOf, axisUsual]

theorem lagSq_equalScale_lt_axisUsual {α : ℝ} (hα : α ≠ 0) :
    lagSq (equalScaleOf (axisUsual α)) < lagSq (axisUsual α) := by
  rw [lagSq_equalScale_axisUsual, lagSq_axisUsual]
  exact sq_pos_of_ne_zero hα

theorem lagSq_cross_eq_two_axisUsual (α : ℝ) :
    lagSq (crossAxisDual α) = 2 * lagSq (axisUsual α) := by
  rw [lagSq_crossAxisDual, lagSq_axisUsual]

theorem lagSq_cross_gt_axisUsual {α : ℝ} (hα : α ≠ 0) :
    lagSq (axisUsual α) < lagSq (crossAxisDual α) := by
  rw [lagSq_axisUsual, lagSq_crossAxisDual]
  nlinarith [sq_pos_of_ne_zero hα]

theorem stiffness_equalScale_axisUsual (m α : ℝ) :
    stiffnessPotential m (equalScaleOf (axisUsual α)) = 0 := by
  rw [stiffnessPotential_eq_lag, lagSq_equalScale_axisUsual]
  ring

theorem stiffness_cross_eq_twice_axisUsual (m α : ℝ) :
    stiffnessPotential m (crossAxisDual α) =
      2 * stiffnessPotential m (axisUsual α) := by
  rw [stiffnessPotential_eq_lag, stiffnessPotential_eq_lag, lagSq_cross_eq_two_axisUsual]
  ring

end Gravity

end DstDiophantine
