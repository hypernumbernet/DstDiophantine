import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.Invariant
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Group.Abs

/-!
# Four D4L states from `JNormalized`

Truth values are the sign and saturation of the already-proved normalised
torsional scalar. The interval \([-1,1]\) belongs to `JNormalized`, not raw
`J` (whose admissible ceiling is \(3\pi^2/8\)).

Outside `[-1, 1]` classification is refused. On the admissible cone the bound
`|JNormalized| ≤ 1` makes the classifier total.
-/

namespace DstDiophantine

namespace Logic

open Admissible Invariant Operations Real

/-- Four Dual-Spacetime 4-valued states. -/
inductive TruthValue
  | T
  | U
  | F
  | B
  deriving DecidableEq, Repr

/-- Classify a real already known to lie in `[-1, 1]`. -/
noncomputable def classifyOfMem (j : ℝ) (_hj : |j| ≤ 1) : TruthValue :=
  if j = 0 then .T
  else if j = 1 then .F
  else if 0 < j then .U
  else .B

/-- Partial classifier: `none` outside `[-1, 1]`. -/
noncomputable def classify? (j : ℝ) : Option TruthValue :=
  if h : |j| ≤ 1 then some (classifyOfMem j h) else none

theorem classify?_eq_some_iff {j : ℝ} :
    (classify? j).isSome ↔ |j| ≤ 1 := by
  unfold classify?
  split_ifs with h
  · simp [h]
  · simp [h]

theorem classifyOfMem_eq_of_eq {j k : ℝ} (hjk : j = k) (hj : |j| ≤ 1) (hk : |k| ≤ 1) :
    classifyOfMem j hj = classifyOfMem k hk := by
  subst hjk
  rfl

theorem classifyOfMem_eq_T_iff {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .T ↔ j = 0 := by
  unfold classifyOfMem
  split_ifs <;> simp_all

theorem classifyOfMem_eq_F_iff {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .F ↔ j = 1 := by
  unfold classifyOfMem
  split_ifs with h0 h1
  · subst h0; simp
  · simp [h1]
  · simp [h1]
  · simp [h1]

theorem classifyOfMem_eq_U_iff {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .U ↔ 0 < j ∧ j < 1 := by
  unfold classifyOfMem
  split_ifs with h0 h1 hpos
  · subst h0; simp
  · subst h1; simp
  · have hj1 : j < 1 := lt_of_le_of_ne (abs_le.mp hj).2 h1
    simp [hpos, hj1]
  · have : ¬ 0 < j := hpos
    simp [this]

theorem classifyOfMem_eq_B_iff {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .B ↔ -1 ≤ j ∧ j < 0 := by
  unfold classifyOfMem
  split_ifs with h0 h1 hpos
  · subst h0; simp
  · subst h1; constructor <;> intro h
    · cases h
    · linarith
  · have : 0 < j := hpos
    constructor <;> intro h
    · cases h
    · linarith
  · have hj0 : j < 0 := lt_of_le_of_ne (le_of_not_gt hpos) h0
    have hjle : -1 ≤ j := (abs_le.mp hj).1
    simp [hjle, hj0]

/-- Truth value of an admissible continuous configuration. -/
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
    ofParams p h = .U ↔ 0 < JNormalized p ∧ JNormalized p < 1 :=
  classifyOfMem_eq_U_iff _

theorem ofParams_eq_B_iff {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    ofParams p h = .B ↔ -1 ≤ JNormalized p ∧ JNormalized p < 0 :=
  classifyOfMem_eq_B_iff _

theorem ofParams_F_iff_pureHyperbolic {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    ofParams p h = .F ↔ IsPureHyperbolic p := by
  rw [ofParams_eq_F_iff]
  constructor
  · intro hj
    have : |JNormalized p| = 1 := by simp [hj]
    exact ((abs_JNormalized_eq_one_iff p h).mp this).resolve_right fun hell => by
      have := JNormalized_of_pureElliptic p hell
      linarith
  · exact JNormalized_of_pureHyperbolic p

theorem ofParams_deepB_iff_pureElliptic {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    JNormalized p = -1 ↔ IsPureElliptic p := by
  constructor
  · intro hj
    have : |JNormalized p| = 1 := by simp [hj]
    exact ((abs_JNormalized_eq_one_iff p h).mp this).resolve_left fun hhyp => by
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
