import DstDiophantine.Logic.Formula
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Valuations and designated values

`HoldsT` is `j = 0`. `HoldsNotF` is `j < 1`.
`IsNamedTwo` is `{0, 1}` and is not closed under `negJ`. `IsWallTwo` is `{-1, 1}`.
-/

namespace DstDiophantine

namespace Logic

structure Valuation where
  assign : ℕ → ℝ
  mem : ∀ n, |assign n| ≤ 1

namespace Valuation

def const (j : ℝ) (hj : |j| ≤ 1) : Valuation where
  assign := fun _ => j
  mem := fun _ => hj

@[simp] theorem const_assign (j : ℝ) (hj : |j| ≤ 1) (n : ℕ) :
    (const j hj).assign n = j := rfl

/-- Atom `0 ↦ j`, atom `1 ↦ k`, and `0` elsewhere. -/
def pair (j k : ℝ) (hj : |j| ≤ 1) (hk : |k| ≤ 1) : Valuation where
  assign := fun n => if n = 0 then j else if n = 1 then k else 0
  mem := fun n => by
    by_cases h0 : n = 0
    · simpa [h0] using hj
    · by_cases h1 : n = 1
      · simpa [h0, h1] using hk
      · simp [h0, h1]

@[simp] theorem pair_zero (j k : ℝ) (hj : |j| ≤ 1) (hk : |k| ≤ 1) :
    (pair j k hj hk).assign 0 = j := by
  simp [pair]

@[simp] theorem pair_one (j k : ℝ) (hj : |j| ≤ 1) (hk : |k| ≤ 1) :
    (pair j k hj hk).assign 1 = k := by
  simp [pair]

theorem eval_mem (v : Valuation) (φ : Formula) : |φ.eval v.assign| ≤ 1 :=
  φ.eval_mem v.mem

end Valuation

/-- Synchrony: `j = 0`. -/
def HoldsT (j : ℝ) : Prop :=
  j = 0

/-- Non-refutation: `j < 1`. -/
def HoldsNotF (j : ℝ) : Prop :=
  j < 1

/-- Fragment `{0, 1}`. -/
def IsNamedTwo (j : ℝ) : Prop :=
  j = 0 ∨ j = 1

/-- Fragment `{-1, 1}`. -/
def IsWallTwo (j : ℝ) : Prop :=
  j = -1 ∨ j = 1

theorem holdsT_iff_classify {j : ℝ} (hj : |j| ≤ 4) :
    HoldsT j ↔ classifyOfMem j hj = .T :=
  (classifyOfMem_eq_T_iff hj).symm

theorem holdsNotF_iff_ne_one {j : ℝ} (hj : |j| ≤ 1) :
    HoldsNotF j ↔ j ≠ 1 :=
  ⟨ne_of_lt, fun hne => lt_of_le_of_ne (abs_le.mp hj).2 hne⟩

theorem holdsNotF_iff_ne_F {j : ℝ} (hj1 : |j| ≤ 1) :
    HoldsNotF j ↔ classifyOfMem j (hj1.trans (by norm_num : (1 : ℝ) ≤ 4)) ≠ .F := by
  have hj := hj1.trans (by norm_num : (1 : ℝ) ≤ 4)
  exact (holdsNotF_iff_ne_one hj1).trans (Iff.symm (Iff.not (classifyOfMem_eq_F_iff hj)))

theorem holdsT_holdsNotF {j : ℝ} (h : HoldsT j) : HoldsNotF j := by
  simp [HoldsT, HoldsNotF] at h ⊢
  linarith

theorem holdsNotF_conj (j k : ℝ) :
    HoldsNotF (conjJ j k) ↔ HoldsNotF j ∨ HoldsNotF k := by
  simp only [HoldsNotF, conjJ]
  constructor
  · intro h
    rcases le_total j k with hjk | hkj
    · exact Or.inl (by rwa [min_eq_left hjk] at h)
    · exact Or.inr (by rwa [min_eq_right hkj] at h)
  · intro h
    rcases h with h | h
    · exact lt_of_le_of_lt (min_le_left j k) h
    · exact lt_of_le_of_lt (min_le_right j k) h

theorem holdsNotF_disj (j k : ℝ) :
    HoldsNotF (disjJ j k) ↔ HoldsNotF j ∧ HoldsNotF k := by
  simp only [HoldsNotF, disjJ, max_lt_iff]

theorem holdsT_excluded_middle (j : ℝ) :
    HoldsT (disjJ j (negJ j)) ↔ HoldsT j := by
  simp only [disj_neg_eq_abs, HoldsT, abs_eq_zero]

theorem not_holdsNotF_excluded_middle_iff {j : ℝ} (hj : |j| ≤ 1) :
    ¬ HoldsNotF (disjJ j (negJ j)) ↔ j = 1 ∨ j = -1 := by
  rw [disj_neg_eq_abs]
  simp only [HoldsNotF]
  constructor
  · intro h
    have hge : 1 ≤ |j| := not_lt.mp (by simpa using h)
    have hle : |j| ≤ 1 := hj
    have heq : |j| = 1 := le_antisymm hle hge
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heq with rfl | rfl <;> norm_num
  · rintro (rfl | rfl) <;> norm_num

theorem conj_neg_holdsNotF (j : ℝ) : HoldsNotF (conjJ j (negJ j)) := by
  unfold HoldsNotF
  rw [conj_neg_eq_neg_abs]
  linarith [abs_nonneg j]

theorem namedTwo_holdsNotF_iff_holdsT {j : ℝ} (h : IsNamedTwo j) :
    HoldsNotF j ↔ HoldsT j := by
  rcases h with h | h <;> simp [HoldsNotF, HoldsT, h]

theorem namedTwo_notF_only_T {j : ℝ} :
    IsNamedTwo j ∧ HoldsNotF j ↔ j = 0 := by
  constructor
  · intro h
    exact (namedTwo_holdsNotF_iff_holdsT h.1).mp h.2
  · intro hj
    exact ⟨Or.inl hj, by simp [HoldsNotF, hj]⟩

@[simp] theorem negJ_zero : negJ (0 : ℝ) = 0 :=
  neg_zero

theorem namedTwo_not_closed_under_neg :
    ∃ j, IsNamedTwo j ∧ ¬ IsNamedTwo (negJ j) :=
  ⟨1, Or.inr rfl, by simp [IsNamedTwo, negJ]; norm_num⟩

theorem wallTwo_neg {j : ℝ} (h : IsWallTwo j) : IsWallTwo (negJ j) := by
  rcases h with h | h <;> simp [IsWallTwo, negJ, h]

theorem wall_not_both_pos {j : ℝ} (h : IsWallTwo j) :
    ¬ (j = 1 ∧ negJ j = 1) := by
  rcases h with h | h <;> simp [negJ, h] <;> norm_num

theorem residuumJ_U_T_holdsT : HoldsT (residuumJ (1 / 2 : ℝ) 0) := by
  rw [HoldsT, residuumJ_U_T]

theorem residuumJ_B_T_eq_F :
    classifyOfMem (residuumJ (-1 / 2 : ℝ) 0)
      (by simp [residuumJ_B_T]) = .F := by
  rw [classifyOfMem_eq_F_iff]
  exact residuumJ_B_T

theorem exists_holdsNotF_label {tv : TruthValue} (hne : tv ≠ .F) :
    ∃ (j : ℝ) (hj : |j| ≤ 4),
      classifyOfMem j hj = tv ∧ HoldsNotF j := by
  cases tv with
  | T =>
    refine ⟨0, by norm_num, ?_, by norm_num [HoldsNotF]⟩
    exact (classifyOfMem_eq_T_iff (by norm_num : |(0 : ℝ)| ≤ 4)).mpr rfl
  | U =>
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_, by norm_num [HoldsNotF]⟩
    exact (classifyOfMem_eq_U_iff (by norm_num : |(1 / 2 : ℝ)| ≤ 4)).mpr
      (by norm_num)
  | F => exact (hne rfl).elim
  | B =>
    refine ⟨(-1 / 2 : ℝ), by norm_num, ?_, by norm_num [HoldsNotF]⟩
    exact (classifyOfMem_eq_B_iff (by norm_num : |(-1 / 2 : ℝ)| ≤ 4)).mpr
      (by norm_num)

end Logic

end DstDiophantine
