import DstDiophantine.Algebra.SourceSuperposition
import DstDiophantine.Gravity.DualRotorDynamics
import DstDiophantine.Gravity.RestMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# What surrounding matter fixes

Sources determine the admissible point a particle expresses. They do not
determine the stiffness `m`.

The configuration expressed by a list of sources is the nearest admissible
point of their bivector sum, and that sum does not depend on order. The empty
list expresses the origin: every rapidity vanishes, the stiffness potential
vanishes at every `m`, and the written action assigns no angular acceleration.

On one axis the written action drives the common rapidity by
`σ̈ = -2m(α - β)`. Aligned pure boosts of rapidity `φ ≥ 0` add until the
wall. While `nφ ≤ π/2`, the common acceleration of the expressed state is
`n` times the acceleration of one boost. Once `nφ ≥ π/2`, the expressed lag
is `π/2` and the common acceleration is `-mπ`, however large `nφ` becomes.
Two boosts of rapidity `π/4` therefore add their accelerations and do not add
their values of `J`. A third leaves the acceleration at `-mπ`.

A lag the particle already carries is not that reading. A pure boost of
rapidity `π/4`, taken as the particle's own angles, still has common
acceleration `-mπ/2` when the source list is empty.

## What is not claimed

No derivation of `m` from the source sum, no identification with `F = ma`,
and no ceiling on laboratory proper acceleration. The additive-then-saturated
acceleration is the aligned pure-boost family, not a Newtonian multi-body law.
-/

namespace DstDiophantine

namespace Gravity

open Admissible Invariant Operations SourceSuperposition Real

/-- Common angular acceleration of the written action, \(-2m(\alpha-\beta)\). -/
def commonAccel (m α β : ℝ) : ℝ :=
  -2 * m * (α - β)

theorem commonAccel_empty_angles (m : ℝ) : commonAccel m 0 0 = 0 := by
  unfold commonAccel
  ring

/-- The empty source list is the origin of coefficient space. -/
theorem sumParams_nil :
    sumParams ([] : List TorsionParams) = ⟨fun _ => 0, fun _ => 0⟩ := by
  refine congrArg₂ TorsionParams.mk ?_ ?_ <;> funext a <;> simp

theorem express_origin :
    express ⟨fun _ => 0, fun _ => 0⟩ = ⟨fun _ => 0, fun _ => 0⟩ := by
  apply express_eq_of_admissible
  rw [admissible_iff_axes]
  intro a
  exact ⟨le_rfl, le_rfl, by linarith [Real.pi_pos]⟩

theorem express_nil :
    express (sumParams ([] : List TorsionParams)) = sumParams ([] : List TorsionParams) := by
  rw [sumParams_nil, express_origin]

theorem expressed_nil_alpha (a : Fin 3) :
    (expressedSuperposition ([] : List TorsionParams)).alpha a = 0 := by
  unfold expressedSuperposition
  rw [express_nil, sumParams_nil]

theorem expressed_nil_beta (a : Fin 3) :
    (expressedSuperposition ([] : List TorsionParams)).beta a = 0 := by
  unfold expressedSuperposition
  rw [express_nil, sumParams_nil]

theorem lagSq_origin : lagSq ⟨fun _ => 0, fun _ => 0⟩ = 0 := by
  unfold lagSq
  simp

/-- Emptiness extinguishes the potential at every stiffness, including a nonzero one. -/
theorem empty_sources_zero_stiffness (m : ℝ) :
    stiffnessPotential m (expressedSuperposition ([] : List TorsionParams)) = 0 := by
  rw [stiffnessPotential_eq_lag]
  unfold expressedSuperposition
  rw [express_nil, sumParams_nil, lagSq_origin]
  ring

/-- At the origin the written action assigns no angular acceleration, for every `m`. -/
theorem empty_sources_no_acceleration (m φddot θddot : ℝ) :
    PaperActualEL m 0 0 φddot θddot ↔ φddot = 0 ∧ θddot = 0 := by
  rw [paperActualEL_eq]
  constructor
  · intro ⟨hφ, hθ⟩
    constructor <;> linarith
  · intro ⟨hφ, hθ⟩
    constructor <;> linarith

theorem expressedLag_perm {ps qs : List TorsionParams} (h : ps.Perm qs) (a : Fin 3) :
    (expressedSuperposition ps).alpha a - (expressedSuperposition ps).beta a =
      (expressedSuperposition qs).alpha a - (expressedSuperposition qs).beta a := by
  unfold expressedSuperposition
  rw [sumParams_perm h]

/-- Expressed aligned pure boosts stop at rapidity `π/2`. -/
theorem express_replicate_axisBoost {n : ℕ} {a0 : Fin 3} {φ : ℝ} (hφ : 0 ≤ φ) :
    express (sumParams (List.replicate n (axisBoost a0 φ))) =
      axisBoost a0 (min ((n : ℝ) * φ) (Real.pi / 2)) := by
  have hsum := sumParams_replicate_axisBoost n a0 φ
  have hψ : 0 ≤ (n : ℝ) * φ := mul_nonneg (Nat.cast_nonneg n) hφ
  rcases le_total ((n : ℝ) * φ) (Real.pi / 2) with hle | hge
  · have hadm : IsAdmissibleContinuous (axisBoost a0 ((n : ℝ) * φ)) :=
      axisBoost_admissible hψ hle
    rw [hsum, express_eq_of_admissible hadm, min_eq_left hle]
  · rw [hsum, express_axisBoost_saturated hge, min_eq_right hge]

theorem expressed_boost_alpha {n : ℕ} {a0 : Fin 3} {φ : ℝ} (hφ : 0 ≤ φ) (a : Fin 3) :
    (expressedSuperposition (List.replicate n (axisBoost a0 φ))).alpha a =
      if a = a0 then min ((n : ℝ) * φ) (Real.pi / 2) else 0 := by
  have hex := express_replicate_axisBoost (n := n) (a0 := a0) (φ := φ) hφ
  have h := congrArg (fun p : TorsionParams => p.alpha a) hex
  simpa [expressedSuperposition, axisBoost] using h

theorem expressed_boost_beta {n : ℕ} {a0 : Fin 3} {φ : ℝ} (hφ : 0 ≤ φ) (a : Fin 3) :
    (expressedSuperposition (List.replicate n (axisBoost a0 φ))).beta a = 0 := by
  have hex := express_replicate_axisBoost (n := n) (a0 := a0) (φ := φ) hφ
  have h := congrArg (fun p : TorsionParams => p.beta a) hex
  simpa [expressedSuperposition, axisBoost] using h

theorem commonAccel_expressed_boost {m : ℝ} {n : ℕ} {a0 : Fin 3} {φ : ℝ} (hφ : 0 ≤ φ) :
    commonAccel m
        ((expressedSuperposition (List.replicate n (axisBoost a0 φ))).alpha a0)
        ((expressedSuperposition (List.replicate n (axisBoost a0 φ))).beta a0) =
      -2 * m * min ((n : ℝ) * φ) (Real.pi / 2) := by
  unfold commonAccel
  rw [expressed_boost_alpha hφ a0, expressed_boost_beta hφ a0]
  simp

/-- While the internal rapidity stays inside the wall, accelerations add. -/
theorem aligned_boosts_accel_scales {n : ℕ} {m φ : ℝ} {a0 : Fin 3}
    (hφ : 0 ≤ φ) (hle : (n : ℝ) * φ ≤ Real.pi / 2) :
    commonAccel m
        ((expressedSuperposition (List.replicate n (axisBoost a0 φ))).alpha a0)
        ((expressedSuperposition (List.replicate n (axisBoost a0 φ))).beta a0) =
      (n : ℝ) *
        commonAccel m
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 φ))).alpha a0)
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 φ))).beta a0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [commonAccel_expressed_boost (n := 0) hφ,
      commonAccel_expressed_boost (n := 1) (a0 := a0) (φ := φ) hφ]
    have hmin0 : min (((0 : ℕ) : ℝ) * φ) (Real.pi / 2) = 0 := by
      rw [Nat.cast_zero, zero_mul, min_eq_left (by linarith [Real.pi_pos])]
    rw [hmin0]
    ring
  · rw [commonAccel_expressed_boost (n := n) hφ,
      commonAccel_expressed_boost (n := 1) (a0 := a0) (φ := φ) hφ]
    have hminn : min ((n : ℝ) * φ) (Real.pi / 2) = (n : ℝ) * φ := min_eq_left hle
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hφle : φ ≤ Real.pi / 2 := by
      have hmul : φ ≤ (n : ℝ) * φ := by nlinarith
      linarith
    have hmin1 : min (((1 : ℕ) : ℝ) * φ) (Real.pi / 2) = φ := by
      rw [Nat.cast_one, one_mul, min_eq_left hφle]
    rw [hminn, hmin1]
    ring

/-- Past the wall the expressed common acceleration is \(-m\pi\), for every larger sum. -/
theorem aligned_boosts_accel_saturated {n : ℕ} {m φ : ℝ} {a0 : Fin 3}
    (hφ : 0 ≤ φ) (hs : Real.pi / 2 ≤ (n : ℝ) * φ) :
    commonAccel m
        ((expressedSuperposition (List.replicate n (axisBoost a0 φ))).alpha a0)
        ((expressedSuperposition (List.replicate n (axisBoost a0 φ))).beta a0) =
      -m * Real.pi := by
  rw [commonAccel_expressed_boost hφ, min_eq_right hs]
  ring

theorem two_quarter_boosts_add_accel (m : ℝ) (a0 : Fin 3) :
    commonAccel m
        ((expressedSuperposition (List.replicate 2 (axisBoost a0 (Real.pi / 4)))).alpha a0)
        ((expressedSuperposition (List.replicate 2 (axisBoost a0 (Real.pi / 4)))).beta a0) =
      commonAccel m
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 (Real.pi / 4)))).alpha a0)
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 (Real.pi / 4)))).beta a0) +
        commonAccel m
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 (Real.pi / 4)))).alpha a0)
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 (Real.pi / 4)))).beta a0) := by
  have h := aligned_boosts_accel_scales (n := 2) (m := m) (φ := Real.pi / 4) (a0 := a0)
      (by positivity) (by linarith [Real.pi_pos])
  simpa [two_mul] using h

theorem two_quarter_boosts_accel (m : ℝ) (a0 : Fin 3) :
    commonAccel m
        ((expressedSuperposition (List.replicate 2 (axisBoost a0 (Real.pi / 4)))).alpha a0)
        ((expressedSuperposition (List.replicate 2 (axisBoost a0 (Real.pi / 4)))).beta a0) =
      -m * Real.pi :=
  aligned_boosts_accel_saturated (n := 2) (m := m) (φ := Real.pi / 4) (a0 := a0)
    (by positivity) (by linarith [Real.pi_pos])

/-- A further quarter-boost does not add another copy of the one-boost acceleration. -/
theorem quarter_boosts_past_wall {m : ℝ} (hm : m ≠ 0) {n : ℕ} (hn : 3 ≤ n) (a0 : Fin 3) :
    commonAccel m
        ((expressedSuperposition (List.replicate n (axisBoost a0 (Real.pi / 4)))).alpha a0)
        ((expressedSuperposition (List.replicate n (axisBoost a0 (Real.pi / 4)))).beta a0) ≠
      (n : ℝ) *
        commonAccel m
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 (Real.pi / 4)))).alpha a0)
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 (Real.pi / 4)))).beta a0) := by
  have hleft := aligned_boosts_accel_saturated (n := n) (m := m) (φ := Real.pi / 4) (a0 := a0)
      (by positivity) (by
        have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [Real.pi_pos])
  have hright := commonAccel_expressed_boost (m := m) (n := 1) (a0 := a0) (φ := Real.pi / 4)
      (by positivity)
  rw [hleft, hright]
  have hmin : min (((1 : ℕ) : ℝ) * (Real.pi / 4)) (Real.pi / 2) = Real.pi / 4 := by
    rw [Nat.cast_one, one_mul, min_eq_left (by linarith [Real.pi_pos])]
  rw [hmin]
  intro heq
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have heq' : (n : ℝ) * m = 2 * m := by
    field_simp [hπ] at heq
    linarith
  have hfac : m * ((n : ℝ) - 2) = 0 := by
    have hdiff : (n : ℝ) * m - 2 * m = 0 := by linarith
    ring_nf at hdiff ⊢
    linarith
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exact hm h0
  · linarith

/-- A pure boost of rapidity `π/4`, carried as the particle's own angles,
has common acceleration `-mπ/2`. -/
theorem carried_quarter_boost_accel (m : ℝ) (a0 : Fin 3) :
    commonAccel m ((axisBoost a0 (Real.pi / 4)).alpha a0)
        ((axisBoost a0 (Real.pi / 4)).beta a0) =
      -m * Real.pi / 2 := by
  unfold commonAccel
  simp [axisBoost]
  ring

/-- A lag already carried is not the state expressed by an empty source list. -/
theorem carried_quarter_boost_not_empty {m : ℝ} (hm : m ≠ 0) (a0 : Fin 3) :
    commonAccel m ((axisBoost a0 (Real.pi / 4)).alpha a0) ((axisBoost a0 (Real.pi / 4)).beta a0) ≠
      commonAccel m
        ((expressedSuperposition ([] : List TorsionParams)).alpha a0)
        ((expressedSuperposition ([] : List TorsionParams)).beta a0) := by
  have hempty := expressed_nil_alpha a0
  have hemptyβ := expressed_nil_beta a0
  have hα : (axisBoost a0 (Real.pi / 4)).alpha a0 = Real.pi / 4 := by simp [axisBoost]
  have hβ : (axisBoost a0 (Real.pi / 4)).beta a0 = 0 := by simp [axisBoost]
  unfold commonAccel
  rw [hα, hβ, hempty, hemptyβ]
  intro heq
  have hzero : -2 * m * (Real.pi / 4) = 0 := by
    simpa using heq
  have hπ : 0 < Real.pi := Real.pi_pos
  have hprod : m * Real.pi = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact hm h0
  · exact ne_of_gt hπ h0

end Gravity

end DstDiophantine
