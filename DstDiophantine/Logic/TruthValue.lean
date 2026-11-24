import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.Invariant
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Group.Abs

/-!
# Four D4L states

Sign and saturation of `JNormalized` on the mismatch cone image `[-4, 4]`, not of raw `J`.
`classify?` is `none` outside that interval.
-/

namespace DstDiophantine

namespace Logic

open Admissible Invariant Operations Real

inductive TruthValue
  | T
  | U
  | F
  | B
  deriving DecidableEq, Repr

noncomputable def classifyOfMem (j : ℝ) (_hj : |j| ≤ 4) : TruthValue :=
  if j = 0 then .T
  else if j = 1 then .F
  else if 0 < j then .U
  else .B

/-- `none` outside `[-1, 1]`. -/
noncomputable def classify? (j : ℝ) : Option TruthValue :=
  if h : |j| ≤ 4 then some (classifyOfMem j h) else none

theorem classify?_eq_some_iff {j : ℝ} :
    (classify? j).isSome ↔ |j| ≤ 4 := by
  unfold classify?
  split_ifs with h
  · simp [h]
  · simp [h]

theorem classifyOfMem_eq_of_eq {j k : ℝ} (hjk : j = k) (hj : |j| ≤ 4) (hk : |k| ≤ 4) :
    classifyOfMem j hj = classifyOfMem k hk := by
  subst hjk
  rfl

theorem classifyOfMem_eq_T_iff {j : ℝ} (hj : |j| ≤ 4) :
    classifyOfMem j hj = .T ↔ j = 0 := by
  unfold classifyOfMem
  split_ifs <;> simp_all

theorem classifyOfMem_eq_F_iff {j : ℝ} (hj : |j| ≤ 4) :
    classifyOfMem j hj = .F ↔ j = 1 := by
  unfold classifyOfMem
  split_ifs with h0 h1
  · subst h0; simp
  · simp [h1]
  · simp [h1]
  · simp [h1]

theorem classifyOfMem_eq_U_iff {j : ℝ} (hj : |j| ≤ 4) :
    classifyOfMem j hj = .U ↔ 0 < j ∧ j ≠ 1 := by
  unfold classifyOfMem
  constructor <;> intro h
  · split_ifs at h <;> simp_all
  · split_ifs <;> simp_all

theorem classifyOfMem_eq_B_iff {j : ℝ} (hj : |j| ≤ 4) :
    classifyOfMem j hj = .B ↔ j < 0 := by
  unfold classifyOfMem
  constructor
  · intro h
    contrapose! h
    rcases le_iff_eq_or_lt.mp h with rfl | hpos
    · simp
    · split_ifs <;> simp_all
  · intro hjneg
    have h0 : j ≠ 0 := ne_of_lt hjneg
    have h1 : j ≠ 1 := by linarith
    have hpos : ¬ 0 < j := not_lt.mpr (le_of_lt hjneg)
    simp only [classifyOfMem, if_neg h0, if_neg h1, if_neg hpos, ite_true]

noncomputable def ofParams (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    TruthValue :=
  classifyOfMem (JNormalized p) (torsion_bound_continuous p h)

theorem ofParams_eq_T_iff {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    ofParams p h = .T ↔ JNormalized p = 0 :=
  classifyOfMem_eq_T_iff _

theorem ofParams_eq_F_iff {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    ofParams p h = .F ↔ JNormalized p = 1 :=
  classifyOfMem_eq_F_iff _

theorem ofParams_eq_U_iff {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    ofParams p h = .U ↔ 0 < JNormalized p ∧ JNormalized p ≠ 1 :=
  classifyOfMem_eq_U_iff (torsion_bound_continuous p h)

theorem ofParams_eq_B_iff {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    ofParams p h = .B ↔ JNormalized p < 0 :=
  classifyOfMem_eq_B_iff _

theorem ofParams_F_iff_pureHyperbolic {p : TorsionParams} (h : IsAdmissibleContinuous p)
    (hleg : IsAdmissibleContinuousLegacy p) :
    ofParams p h = .F ↔ IsPureHyperbolic p := by
  rw [ofParams_eq_F_iff]
  exact Invariant.JNormalized_eq_one_iff_pureHyperbolic p hleg

theorem ofParams_deepB_iff_pureElliptic {p : TorsionParams} (h : IsAdmissibleContinuous p)
    (hleg : IsAdmissibleContinuousLegacy p) :
    JNormalized p = -1 ↔ IsPureElliptic p := by
  constructor
  · intro hj
    have : |JNormalized p| = 1 := by simp [hj]
    exact ((abs_JNormalized_eq_one_iff p hleg).mp this).resolve_left fun hhyp => by
      have := JNormalized_of_pureHyperbolic p hhyp
      linarith
  · exact JNormalized_of_pureElliptic p

theorem exists_ofParams (tv : TruthValue) :
    ∃ (p : TorsionParams) (h : IsAdmissibleContinuous p), ofParams p h = tv := by
  cases tv with
  | T =>
    refine ⟨Invariant.pureHyperbolicRay 0, ?_, ?_⟩
    · exact Invariant.isAdmissibleContinuous_pureHyperbolicRay (by norm_num) (by norm_num)
    · rw [ofParams_eq_T_iff, Invariant.JNormalized_pureHyperbolicRay]; norm_num
  | U =>
    refine ⟨Invariant.pureHyperbolicRay (Real.sqrt (1 / 2)), ?_, ?_⟩
    · refine Invariant.isAdmissibleContinuous_pureHyperbolicRay (Real.sqrt_nonneg _) ?_
      exact (Real.sqrt_le_one).2 (by norm_num)
    · rw [ofParams_eq_U_iff, Invariant.JNormalized_pureHyperbolicRay, Real.sq_sqrt (by norm_num)]
      norm_num
  | F =>
    refine ⟨Invariant.pureHyperbolicRay 1, ?_, ?_⟩
    · exact Invariant.isAdmissibleContinuous_pureHyperbolicRay (by norm_num) (by norm_num)
    · rw [ofParams_eq_F_iff, Invariant.JNormalized_pureHyperbolicRay]; norm_num
  | B =>
    refine ⟨Invariant.pureEllipticRay (Real.sqrt (1 / 2)), ?_, ?_⟩
    · refine Invariant.isAdmissibleContinuous_pureEllipticRay (Real.sqrt_nonneg _) ?_
      exact (Real.sqrt_le_one).2 (by norm_num)
    · rw [ofParams_eq_B_iff, Invariant.JNormalized_pureEllipticRay, Real.sq_sqrt (by norm_num)]
      norm_num

end Logic

end DstDiophantine
