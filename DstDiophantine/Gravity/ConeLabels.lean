import DstDiophantine.Gravity.DualControl
import DstDiophantine.Logic.Connective
import DstDiophantine.Logic.Interpretation

/-!
# Four regimes of the admissible cone

The normalised mismatch on an admissible configuration takes one of four
values of sign and saturation. Saturated attraction is a single point of
the cone, and it is the unique point whose usual rapidities admit no
other admissible dual completion. Dual-only motion is frozen there, so a
repulsive continuation is not available without moving the usual sector.
A usual seed with negative dual wall carries repulsion and balance on
that fiber; a positive wall keeps the whole fiber in unsaturated
attraction whenever the pure-usual height lies strictly below the
ceiling. The conjunction of a height with its sector swap is balance
when the height vanishes and repulsion otherwise.
-/

namespace DstDiophantine

namespace Gravity

open Admissible Invariant Operations Real

private theorem JNormalized_coeff_pos : 0 < (8 / (3 * Real.pi ^ 2) : ℝ) := by
  positivity

theorem JNormalized_eq_zero_iff (p : TorsionParams) :
    JNormalized p = 0 ↔ J p = 0 := by
  unfold JNormalized
  have hc : (8 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := by positivity
  simp [mul_eq_zero, hc]

theorem JNormalized_pos_iff (p : TorsionParams) :
    0 < JNormalized p ↔ 0 < J p := by
  have hc := JNormalized_coeff_pos
  unfold JNormalized
  constructor
  · intro h
    have : (8 / (3 * Real.pi ^ 2)) * 0 < (8 / (3 * Real.pi ^ 2)) * J p := by
      simpa using h
    exact (mul_lt_mul_iff_of_pos_left hc).mp this
  · intro h
    have : (8 / (3 * Real.pi ^ 2)) * 0 < (8 / (3 * Real.pi ^ 2)) * J p :=
      (mul_lt_mul_iff_of_pos_left hc).mpr h
    simpa using this

theorem JNormalized_lt_zero_iff (p : TorsionParams) :
    JNormalized p < 0 ↔ J p < 0 := by
  have hc := JNormalized_coeff_pos
  unfold JNormalized
  constructor
  · intro h
    have : (8 / (3 * Real.pi ^ 2)) * J p < (8 / (3 * Real.pi ^ 2)) * 0 := by
      simpa using h
    exact (mul_lt_mul_iff_of_pos_left hc).mp this
  · intro h
    have : (8 / (3 * Real.pi ^ 2)) * J p < (8 / (3 * Real.pi ^ 2)) * 0 :=
      (mul_lt_mul_iff_of_pos_left hc).mpr h
    simpa using this

theorem JNormalized_lt_one_iff (p : TorsionParams) :
    JNormalized p < 1 ↔ J p < 3 * Real.pi ^ 2 / 8 := by
  have hc := JNormalized_coeff_pos
  have hceil : (8 / (3 * Real.pi ^ 2)) * (3 * Real.pi ^ 2 / 8) = 1 := by
    field_simp
  rw [JNormalized, ← hceil]
  exact mul_lt_mul_iff_of_pos_left hc

theorem ofParams_eq_B_iff_neg {p : TorsionParams} (hp : IsAdmissibleContinuous p) :
    Logic.ofParams p hp = .B ↔ JNormalized p < 0 := by
  rw [Logic.ofParams_eq_B_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨(abs_le.mp (torsion_bound_continuous p hp)).1, h⟩

/-- Saturated attraction is the unique admissible point whose usual
rapidities admit no other dual completion. -/
theorem dualOnly_rigid_iff_F {p : TorsionParams} (hp : IsAdmissibleContinuous p) :
    (∀ q : TorsionParams, IsAdmissibleContinuous q → q.alpha = p.alpha → q = p) ↔
      Logic.ofParams p hp = .F := by
  constructor
  · intro hfib
    have hwall : dualWallParams p = p :=
      hfib _ (isAdmissibleContinuous_dualWallParams hp) rfl
    have hzero : zeroDual p = p :=
      hfib _ (isAdmissibleContinuous_zeroDual hp) rfl
    have hβ0 : ∀ a, p.beta a = 0 := by
      intro a
      have h0 : (zeroDual p).beta a = 0 := by simp [zeroDual]
      have heq := congrFun (congrArg TorsionParams.beta hzero) a
      rw [h0] at heq
      exact heq.symm
    have hα : ∀ a, p.alpha a = Real.pi / 2 := by
      intro a
      have hw := congrFun (congrArg TorsionParams.beta hwall) a
      have hβ : p.beta a = Real.pi / 2 - p.alpha a := by
        simpa [dualWallParams, dualWall] using hw.symm
      linarith [hβ0 a, hβ]
    rw [Logic.ofParams_F_iff_pureHyperbolic]
    intro a
    exact ⟨hα a, hβ0 a⟩
  · intro hF q hq hα
    have hpure : IsPureHyperbolic p :=
      (Logic.ofParams_F_iff_pureHyperbolic hp).mp hF
    refine torsionParams_ext hα ?_
    funext a
    have hqa : q.alpha a = Real.pi / 2 := by rw [hα]; exact (hpure a).1
    have hle := admissibleContinuous_beta_le_dualWall hq a
    have hnn := admissibleContinuous_beta_nonneg q hq a
    have hqβ : q.beta a = 0 := by
      simp [dualWall, hqa] at hle
      linarith
    have hpβ : p.beta a = 0 := (hpure a).2
    simp [hqβ, hpβ]

/-- A repulsive dual-only continuation exists exactly on a negative wall. -/
theorem exists_dualOnly_B_iff {p : TorsionParams} (hp : IsAdmissibleContinuous p) :
    (∃ q : TorsionParams, ∃ hq : IsAdmissibleContinuous q,
      q.alpha = p.alpha ∧ Logic.ofParams q hq = .B) ↔
      J (dualWallParams p) < 0 := by
  constructor
  · rintro ⟨q, hq, hα, hB⟩
    have hJ : J q < 0 := (JNormalized_lt_zero_iff q).mp ((ofParams_eq_B_iff_neg hq).mp hB)
    exact lt_of_le_of_lt (J_dual_only_ge_wall hα hq) hJ
  · intro hwall
    refine ⟨dualWallParams p, isAdmissibleContinuous_dualWallParams hp, rfl, ?_⟩
    exact (ofParams_eq_B_iff_neg (isAdmissibleContinuous_dualWallParams hp)).mpr
      ((JNormalized_lt_zero_iff _).mpr hwall)

/-- A balanced dual-only continuation exists exactly on a nonpositive wall. -/
theorem exists_dualOnly_T_iff {p : TorsionParams} (hp : IsAdmissibleContinuous p) :
    (∃ q : TorsionParams, ∃ hq : IsAdmissibleContinuous q,
      q.alpha = p.alpha ∧ Logic.ofParams q hq = .T) ↔
      J (dualWallParams p) ≤ 0 := by
  constructor
  · rintro ⟨q, hq, hα, hT⟩
    have hJ : J q = 0 :=
      (JNormalized_eq_zero_iff q).mp ((Logic.ofParams_eq_T_iff hq).mp hT)
    have hle := J_dual_only_ge_wall hα hq
    linarith
  · intro hwall
    obtain ⟨q, hα, hq, hJ⟩ := exists_dual_only_J_eq_zero hp hwall
    refine ⟨q, hq, hα, ?_⟩
    exact (Logic.ofParams_eq_T_iff hq).mpr ((JNormalized_eq_zero_iff q).mpr hJ)

/-- The attractive ceiling has no dual-only repulsive continuation. -/
theorem no_dualOnly_repulsion_of_F {p : TorsionParams} (hp : IsAdmissibleContinuous p)
    (hF : Logic.ofParams p hp = .F) :
    ¬ ∃ q : TorsionParams, ∃ hq : IsAdmissibleContinuous q,
      q.alpha = p.alpha ∧ Logic.ofParams q hq = .B := by
  intro ⟨q, hq, hα, hB⟩
  have hq_eq : q = p := ((dualOnly_rigid_iff_F hp).mpr hF) q hq hα
  have hJB : JNormalized q < 0 := (ofParams_eq_B_iff_neg hq).mp hB
  have hJF : JNormalized p = 1 := (Logic.ofParams_eq_F_iff hp).mp hF
  rw [hq_eq] at hJB
  linarith

/-- A balanced dual-only continuation of a nonzero usual seed is massive. -/
theorem dualOnly_T_mass_pos {p q : TorsionParams} (hα : q.alpha = p.alpha)
    (hq : IsAdmissibleContinuous q) (hT : Logic.ofParams q hq = .T)
    (hseed : ∃ a, p.alpha a ≠ 0) :
    0 < mass q := by
  have hJ : J q = 0 :=
    (JNormalized_eq_zero_iff q).mp ((Logic.ofParams_eq_T_iff hq).mp hT)
  rw [mass_dual_only_of_J_eq_zero hα hJ]
  rcases hseed with ⟨a, ha⟩
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨a, Finset.mem_univ a, sq_pos_of_ne_zero ha⟩

/-- Sector swap sends saturated attraction to the repulsive endpoint. -/
theorem dagger_of_F {p : TorsionParams} (hp : IsAdmissibleContinuous p)
    (hF : Logic.ofParams p hp = .F) :
    JNormalized (daggerParams p) = -1 ∧
      Logic.ofParams (daggerParams p) (Logic.isAdmissibleContinuous_dagger hp) = .B := by
  have hJ : JNormalized p = 1 := (Logic.ofParams_eq_F_iff hp).mp hF
  refine ⟨?_, ?_⟩
  · rw [JNormalized_dagger, hJ]
  · exact (ofParams_eq_B_iff_neg (Logic.isAdmissibleContinuous_dagger hp)).mpr
      (by rw [JNormalized_dagger, hJ]; norm_num)

theorem meet_swap_eq_T_iff {p : TorsionParams} (hp : IsAdmissibleContinuous p) :
    Logic.classifyOfMem
        (Logic.conjJ (JNormalized p) (Logic.negJ (JNormalized p)))
        (Logic.abs_conj_neg_le (torsion_bound_continuous p hp)) = .T ↔
      Logic.ofParams p hp = .T := by
  have hj := torsion_bound_continuous p hp
  have hk := Logic.abs_conj_neg_le hj
  rw [Logic.classifyOfMem_eq_T_iff hk, Logic.conj_neg_eq_neg_abs, Logic.ofParams_eq_T_iff]
  constructor
  · intro h
    exact abs_eq_zero.mp (by linarith)
  · intro h
    simp [h]

theorem meet_swap_eq_B_iff {p : TorsionParams} (hp : IsAdmissibleContinuous p) :
    Logic.classifyOfMem
        (Logic.conjJ (JNormalized p) (Logic.negJ (JNormalized p)))
        (Logic.abs_conj_neg_le (torsion_bound_continuous p hp)) = .B ↔
      Logic.ofParams p hp ≠ .T := by
  constructor
  · intro hB hT
    have hmeetT := (meet_swap_eq_T_iff hp).mpr hT
    rw [hmeetT] at hB
    exact absurd hB (by decide)
  · intro hne
    rcases Logic.classify_conj_neg_T_or_B (torsion_bound_continuous p hp) with hT | hB
    · exact absurd ((meet_swap_eq_T_iff hp).mp hT) hne
    · exact hB

/-- Below the ceiling, a positive wall freezes every dual-only continuation
in unsaturated attraction. -/
theorem dualOnly_eq_U_of_positive_wall {p q : TorsionParams}
    (hq : IsAdmissibleContinuous q)
    (hα : q.alpha = p.alpha) (hwall : 0 < J (dualWallParams p))
    (hceil : J (zeroDual p) < 3 * Real.pi ^ 2 / 8) :
    Logic.ofParams q hq = .U := by
  have hJpos : 0 < J q := not_dual_only_J_eq_zero_of_wall_pos hα hq hwall
  have hJlt : J q < 3 * Real.pi ^ 2 / 8 :=
    lt_of_le_of_lt (J_dual_only_le_zeroDual hα) hceil
  rw [Logic.ofParams_eq_U_iff]
  exact ⟨(JNormalized_pos_iff q).mpr hJpos, (JNormalized_lt_one_iff q).mpr hJlt⟩

private theorem zeroDual_uniform_beta_zero (α : ℝ) :
    zeroDual (uniformTorsion α 0) = uniformTorsion α 0 := by
  refine torsionParams_ext rfl ?_
  funext a
  simp [zeroDual, uniformTorsion]

private theorem J_uniform_usual_lt_ceiling {α : ℝ} (hα : 0 ≤ α) (hαπ : α < Real.pi / 2) :
    J (uniformTorsion α 0) < 3 * Real.pi ^ 2 / 8 := by
  rw [J_uniform, show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero]
  have hsq : α ^ 2 < (Real.pi / 2) ^ 2 := by
    have hne : α ≠ Real.pi / 2 := ne_of_lt hαπ
    have hle : α ^ 2 ≤ (Real.pi / 2) ^ 2 := pow_le_pow_left₀ hα (le_of_lt hαπ) 2
    exact lt_of_le_of_ne hle (by
      intro h
      have hor := (sq_eq_sq_iff_eq_or_eq_neg.mp h).resolve_right (by
        have hπ : 0 < Real.pi / 2 := by positivity
        intro hneg
        linarith)
      exact hne hor)
  have hcoef : 0 < (3 / 2 : ℝ) := by norm_num
  have hmul : (3 / 2) * α ^ 2 < (3 / 2) * (Real.pi / 2) ^ 2 :=
    mul_lt_mul_of_pos_left hsq hcoef
  have hceil : (3 / 2) * (Real.pi / 2) ^ 2 = 3 * Real.pi ^ 2 / 8 := by ring
  linarith

theorem uniform_pi_div_six_three_labels :
    (∃ q : TorsionParams, ∃ hq : IsAdmissibleContinuous q,
        q.alpha = (uniformTorsion (Real.pi / 6) 0).alpha ∧ Logic.ofParams q hq = .B) ∧
      (∃ q : TorsionParams, ∃ hq : IsAdmissibleContinuous q,
        q.alpha = (uniformTorsion (Real.pi / 6) 0).alpha ∧ Logic.ofParams q hq = .T) ∧
      Logic.ofParams (uniformTorsion (Real.pi / 6) 0) uniform_pi_div_six_admissible = .U ∧
      ¬ ∃ q : TorsionParams, ∃ hq : IsAdmissibleContinuous q,
        q.alpha = (uniformTorsion (Real.pi / 6) 0).alpha ∧ Logic.ofParams q hq = .F := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (exists_dualOnly_B_iff uniform_pi_div_six_admissible).mpr uniform_pi_div_six_wall_neg
  · exact (exists_dualOnly_T_iff uniform_pi_div_six_admissible).mpr
      (le_of_lt uniform_pi_div_six_wall_neg)
  · have hJpos : 0 < J (uniformTorsion (Real.pi / 6) 0) := by
      rw [J_uniform]
      have hπ : 0 < Real.pi := Real.pi_pos
      nlinarith
    have hJlt : J (uniformTorsion (Real.pi / 6) 0) < 3 * Real.pi ^ 2 / 8 := by
      have hα : (0 : ℝ) ≤ Real.pi / 6 := by positivity
      have hαπ : Real.pi / 6 < Real.pi / 2 := by
        have hπ : 0 < Real.pi := Real.pi_pos
        nlinarith
      exact J_uniform_usual_lt_ceiling hα hαπ
    rw [Logic.ofParams_eq_U_iff, JNormalized_pos_iff, JNormalized_lt_one_iff]
    exact ⟨hJpos, hJlt⟩
  · intro ⟨q, hq, hα, hF⟩
    have hpure : IsPureHyperbolic q := (Logic.ofParams_F_iff_pureHyperbolic hq).mp hF
    have h0 : q.alpha 0 = Real.pi / 6 := by simp [hα, uniformTorsion]
    have hπ2 : q.alpha 0 = Real.pi / 2 := (hpure 0).1
    have : Real.pi / 6 = Real.pi / 2 := by rw [← h0, hπ2]
    have hpos : 0 < Real.pi := Real.pi_pos
    nlinarith

/-- A uniform usual rapidity \(\pi/3\) keeps every dual-only continuation
in unsaturated attraction. -/
theorem uniform_pi_div_three_dualOnly_U {q : TorsionParams}
    (hα : ∀ a, q.alpha a = Real.pi / 3) (hq : IsAdmissibleContinuous q) :
    Logic.ofParams q hq = .U := by
  have hαp : q.alpha = (uniformTorsion (Real.pi / 3) 0).alpha := by
    funext a
    exact hα a
  have hceil : J (zeroDual (uniformTorsion (Real.pi / 3) 0)) < 3 * Real.pi ^ 2 / 8 := by
    rw [zeroDual_uniform_beta_zero]
    have hα0 : (0 : ℝ) ≤ Real.pi / 3 := by positivity
    have hαπ : Real.pi / 3 < Real.pi / 2 := by
      have hπ : 0 < Real.pi := Real.pi_pos
      nlinarith
    exact J_uniform_usual_lt_ceiling hα0 hαπ
  exact dualOnly_eq_U_of_positive_wall hq hαp
    uniform_pi_div_three_wall_pos hceil

end Gravity

end DstDiophantine
