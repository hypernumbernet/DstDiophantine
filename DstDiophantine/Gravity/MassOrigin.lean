import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.LorentzLie
import DstDiophantine.Gravity.DualRotorDynamics
import DstDiophantine.Gravity.RestMass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Where unsigned mass sits

The time-reversing dual map on rapidity parameters is the quarter-turn
`(α, β) ↦ (β, -α)`. It preserves the unsigned mass and reverses `J`.
The only configuration it fixes is the origin, where that mass vanishes.

Exchange of the two sectors fixes a larger set: the rapidities agree on
every axis. There `J` vanishes, the stiffness potential vanishes, and the
written action assigns no angular acceleration, while the unsigned mass
equals `∑ α_a²` and need not vanish. On one axis the rotors do not
coincide. The dual map sends this state to one of equal unsigned mass
whose potential is `2mM`. A positive admissible state of this kind is
sent outside the cone.

## What is not claimed

No derivation of the coefficient `m`, no mass gap produced by leaving
the sector-symmetric state, and no identification with `F = ma`.
-/

namespace DstDiophantine

namespace Gravity

open Admissible Invariant LorentzLie Operations RelativeRotor

/-! ### What each symmetry fixes -/

theorem daggerParams_eq_self_iff (p : TorsionParams) :
    daggerParams p = p ↔ ∀ a, p.alpha a = p.beta a := by
  constructor
  · intro h a
    have hα := congrFun (congrArg TorsionParams.alpha h) a
    simpa [daggerParams] using hα.symm
  · intro h
    refine congrArg₂ TorsionParams.mk ?_ ?_
    · funext a
      simpa [daggerParams] using (h a).symm
    · funext a
      simpa [daggerParams] using h a

theorem dualParams_eq_self_iff (p : TorsionParams) :
    dualParams p = p ↔ ∀ a, p.alpha a = 0 ∧ p.beta a = 0 := by
  constructor
  · intro h a
    have hα := congrFun (congrArg TorsionParams.alpha h) a
    have hβ := congrFun (congrArg TorsionParams.beta h) a
    simp only [dualParams] at hα hβ
    have hα0 : p.alpha a = 0 := by linarith
    exact ⟨hα0, by linarith⟩
  · intro h
    refine congrArg₂ TorsionParams.mk ?_ ?_
    · funext a
      rw [(h a).2, (h a).1]
    · funext a
      rw [(h a).1, (h a).2]
      ring

/-- The time-reversing map fixes a configuration exactly at vanishing unsigned mass. -/
theorem dualParams_eq_self_iff_mass (p : TorsionParams) :
    dualParams p = p ↔ mass p = 0 := by
  rw [dualParams_eq_self_iff, mass_eq_zero_iff]

theorem sectorFixed_mass {p : TorsionParams} (h : daggerParams p = p) :
    mass p = ∑ a : Fin 3, p.alpha a ^ 2 := by
  rw [mass_coef, Fin.sum_univ_three, Fin.sum_univ_three]
  have hax := (daggerParams_eq_self_iff p).mp h
  simp only [hax 0, hax 1, hax 2]
  ring

theorem sectorFixed_mismatch {p : TorsionParams} (h : daggerParams p = p) :
    J p = 0 := by
  have hJ := J_dagger p
  rw [h] at hJ
  linarith

theorem sectorFixed_potential {m : ℝ} {p : TorsionParams} (h : daggerParams p = p) :
    stiffnessPotential m p = 0 := by
  rw [stiffnessPotential_eq_lag, lagSq, Fin.sum_univ_three]
  have hax := (daggerParams_eq_self_iff p).mp h
  simp only [hax 0, hax 1, hax 2]
  ring

/-- Where the sectors agree, the written action assigns no angular acceleration. -/
theorem sectorFixed_sits {p : TorsionParams} (h : daggerParams p = p) (m : ℝ) (a : Fin 3) :
    PaperActualEL m (p.alpha a) (p.beta a) 0 0 := by
  rw [paperActualEL_eq]
  have hax := (daggerParams_eq_self_iff p).mp h a
  constructor <;> simp [hax]

/-! ### The dual map trades the potential for the unsigned mass -/

theorem lagSq_dualParams (p : TorsionParams) :
    lagSq (dualParams p) = ∑ a : Fin 3, (p.alpha a + p.beta a) ^ 2 := by
  unfold lagSq
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [dualParams]
  ring

theorem stiffness_dual_sub (m : ℝ) (p : TorsionParams) :
    stiffnessPotential m (dualParams p) - stiffnessPotential m p =
      2 * m * ∑ a : Fin 3, p.alpha a * p.beta a := by
  rw [stiffnessPotential_eq_lag, stiffnessPotential_eq_lag, lagSq_dualParams, lagSq]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  ring

theorem sectorFixed_pair_sum {p : TorsionParams} (h : daggerParams p = p) :
    ∑ a : Fin 3, p.alpha a * p.beta a = mass p := by
  rw [sectorFixed_mass h, Fin.sum_univ_three, Fin.sum_univ_three]
  have hax := (daggerParams_eq_self_iff p).mp h
  rw [← hax 0, ← hax 1, ← hax 2]
  ring

/-- On a sector-symmetric state the image potential is `2mM`. -/
theorem sectorFixed_dual_potential {m : ℝ} {p : TorsionParams} (h : daggerParams p = p) :
    stiffnessPotential m (dualParams p) = 2 * m * mass p := by
  have hsub := stiffness_dual_sub m p
  rw [sectorFixed_potential h, sectorFixed_pair_sum h, sub_zero] at hsub
  exact hsub

theorem dualParams_ne_of_mass {p : TorsionParams} (hM : mass p ≠ 0) :
    dualParams p ≠ p := by
  intro hd
  exact hM ((dualParams_eq_self_iff_mass p).mp hd)

/-! ### One axis, and the cone -/

theorem dualParams_aligned (φ : ℝ) :
    dualParams (axisParams φ φ) = axisParams φ (-φ) := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a
    simp only [axisParams]
  · funext a
    change -((axisParams φ φ).alpha a) = (axisParams φ (-φ)).beta a
    simp only [axisParams]
    split_ifs <;> ring

theorem aligned_axis_sectorFixed (φ : ℝ) :
    daggerParams (axisParams φ φ) = axisParams φ φ := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a
    simp only [axisParams]
  · funext a
    simp only [axisParams]

theorem aligned_axis_not_freefall {φ : ℝ} (hφ : φ ≠ 0) :
    relativeRotor (axisParams φ φ) ≠ 1 := by
  intro hΩ
  have hrot := (relativeRotor_eq_one_iff _).mp hΩ
  have hs : Real.sinh (φ / 2) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact div_ne_zero hφ two_ne_zero
  exact balanced_axis_rotors_ne hs hrot

theorem aligned_admissible {φ : ℝ} (h0 : 0 ≤ φ) (hw : φ ≤ Real.pi / 4) :
    IsAdmissibleContinuous (axisParams φ φ) := by
  intro a
  refine ⟨?_, ?_, ?_⟩
  · simp only [axisParams]
    split_ifs <;> linarith
  · simp only [axisParams]
    split_ifs <;> linarith
  · simp only [axisParams]
    split_ifs <;> linarith [Real.pi_pos]

theorem dual_aligned_not_admissible {φ : ℝ} (hφ : 0 < φ) :
    ¬ IsAdmissibleContinuous (dualParams (axisParams φ φ)) := by
  rw [dualParams_aligned]
  intro h
  have hβ := (h 0).2.1
  simp [axisParams] at hβ
  linarith

/-- A positive admissible state with the sectors in agreement leaves the cone. -/
theorem sectorFixed_admissible_image_leaves {p : TorsionParams}
    (hsec : daggerParams p = p) (hadm : IsAdmissibleContinuous p) (hM : 0 < mass p) :
    ¬ IsAdmissibleContinuous (dualParams p) := by
  intro himg
  have hax := (daggerParams_eq_self_iff p).mp hsec
  have hex : ∃ a, 0 < p.alpha a := by
    by_contra hnone
    have hmass : mass p = 0 := by
      rw [sectorFixed_mass hsec, Fin.sum_univ_three]
      simp only [not_exists, not_lt] at hnone
      have h0 (a : Fin 3) : p.alpha a = 0 :=
        le_antisymm (hnone a) (hadm a).1
      simp [h0 0, h0 1, h0 2]
    exact ne_of_gt hM hmass
  obtain ⟨a, hpos⟩ := hex
  have hβ : (dualParams p).beta a < 0 := by
    simp [dualParams]
    linarith
  exact not_lt_of_ge (himg a).2.1 hβ

theorem quarter_balance_mass :
    mass (axisParams (Real.pi / 4) (Real.pi / 4)) = (Real.pi / 4) ^ 2 := by
  rw [mass_axisParams]
  ring

/-- The wall balance `φ = π/4` sits, is massive, and its dual image leaves the cone. -/
theorem quarter_balance_sits (m : ℝ) :
    let p := axisParams (Real.pi / 4) (Real.pi / 4)
    daggerParams p = p ∧
      J p = 0 ∧
      mass p = (Real.pi / 4) ^ 2 ∧
      stiffnessPotential m p = 0 ∧
      stiffnessPotential m (dualParams p) = 2 * m * mass p ∧
      relativeRotor p ≠ 1 ∧
      IsAdmissibleContinuous p ∧
      ¬ IsAdmissibleContinuous (dualParams p) := by
  intro p
  refine ⟨aligned_axis_sectorFixed _, sectorFixed_mismatch (aligned_axis_sectorFixed _),
      quarter_balance_mass, sectorFixed_potential (aligned_axis_sectorFixed _),
      sectorFixed_dual_potential (aligned_axis_sectorFixed _),
      aligned_axis_not_freefall (by positivity),
      aligned_admissible (by positivity) le_rfl,
      dual_aligned_not_admissible (by positivity)⟩

end Gravity

end DstDiophantine
