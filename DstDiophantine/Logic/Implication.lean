import DstDiophantine.Logic.Valuation

/-!
# Why the amplitude height has no implication

Synchrony (`HoldsT`, the point `0`) and non-refutation (`HoldsNotF`, the
cut `j < 1`) each admit a residual on `[-1,1]`. No single operation
residuates both: a height other than balance or the positive wall,
implying that wall, is forced to `0` by synchrony and to `1` by
non-refutation.

The normalised residuals agree on an open height implying synchrony, and
both designate it. Regime implication refuses that designation. It
residuates only the non-refutation cut on the four names.
-/

namespace DstDiophantine

namespace Logic

/-- Synchrony residual. A balanced antecedent returns the consequent;
every other antecedent sits at balance. -/
noncomputable def syncImp (j k : ℝ) : ℝ :=
  if j = 0 then k else 0

/-- Non-refutation residual. A refuted antecedent returns balance; a
non-refuted antecedent implying the positive wall returns that wall;
otherwise the consequent is remembered. -/
noncomputable def nonrefImp (j k : ℝ) : ℝ :=
  if j = 1 then 0 else if k = 1 then 1 else k

theorem syncImp_of_ne_zero {j k : ℝ} (hj : j ≠ 0) : syncImp j k = 0 := by
  simp [syncImp, hj]

theorem nonrefImp_of_eq_one (k : ℝ) : nonrefImp 1 k = 0 := by
  simp [nonrefImp]

theorem nonrefImp_of_failure {j k : ℝ} (hj : j ≠ 1) (hk : k = 1) :
    nonrefImp j k = 1 := by
  simp [nonrefImp, hj, hk]

theorem nonrefImp_of_pass {j k : ℝ} (hj : j ≠ 1) (hk : k ≠ 1) :
    nonrefImp j k = k := by
  simp [nonrefImp, hj, hk]

/-- The synchrony residual is synchronous exactly under the synchrony conditional. -/
theorem syncImp_holdsT_iff (j k : ℝ) :
    HoldsT (syncImp j k) ↔ (HoldsT j → HoldsT k) := by
  unfold syncImp HoldsT
  split_ifs with hj
  · simp [hj]
  · simp [hj]

/-- Every synchrony residual returns balance when the antecedent is not balanced. -/
theorem sync_residual_of_ne_zero (imp : ℝ → ℝ → ℝ) {j k : ℝ} (hj : j ≠ 0)
    (hiff : HoldsT (imp j k) ↔ (HoldsT j → HoldsT k)) :
    imp j k = 0 := by
  have hT : HoldsT (imp j k) := by
    rw [hiff]
    intro hj0
    exact (hj hj0).elim
  simpa [HoldsT] using hT

/-- Remembering the consequent at balance fixes the synchrony residual. -/
theorem syncImp_unique (imp : ℝ → ℝ → ℝ)
    (hiff : ∀ j k : ℝ, HoldsT (imp j k) ↔ (HoldsT j → HoldsT k))
    (hnorm : ∀ k : ℝ, imp 0 k = k) :
    ∀ j k : ℝ, imp j k = syncImp j k := by
  intro j k
  classical
  by_cases hj : j = 0
  · simpa [syncImp, hj] using hnorm k
  · have h0 : imp j k = 0 := sync_residual_of_ne_zero imp hj (hiff j k)
    simpa [syncImp, hj] using h0

/-- The non-refutation residual tracks the non-refutation conditional. -/
theorem nonrefImp_holdsNotF_iff {j k : ℝ} (hj : |j| ≤ 1) (hk : |k| ≤ 1) :
    HoldsNotF (nonrefImp j k) ↔ (HoldsNotF j → HoldsNotF k) := by
  classical
  unfold nonrefImp HoldsNotF
  by_cases hj1 : j = 1
  · subst hj1
    simp
  · by_cases hk1 : k = 1
    · subst hk1
      have hjlt : j < 1 := lt_of_le_of_ne (abs_le.mp hj).2 hj1
      simp [hj1, hjlt]
    · have hklt : k < 1 := lt_of_le_of_ne (abs_le.mp hk).2 hk1
      simp [hj1, hk1, hklt]

/-- On the failure set, every non-refutation residual sits on the positive wall. -/
theorem nonref_residual_on_failure (imp : ℝ → ℝ → ℝ) {j k : ℝ}
    (hj : |j| ≤ 1)
    (hmem : |imp j k| ≤ 1)
    (hiff : HoldsNotF (imp j k) ↔ (HoldsNotF j → HoldsNotF k))
    (hfail : j ≠ 1 ∧ k = 1) :
    imp j k = 1 := by
  have hjlt : j < 1 := lt_of_le_of_ne (abs_le.mp hj).2 hfail.1
  have hnot : ¬ HoldsNotF (imp j k) := by
    rw [hiff]
    intro himp
    have hklt : k < 1 := by
      simpa [HoldsNotF] using himp (by simpa [HoldsNotF] using hjlt)
    rw [hfail.2] at hklt
    exact lt_irrefl _ hklt
  rw [holdsNotF_iff_ne_one hmem] at hnot
  exact Classical.not_not.mp hnot

/-- Balance on a refuted antecedent, and the consequent off the failure set,
fix the non-refutation residual. -/
theorem nonrefImp_unique (imp : ℝ → ℝ → ℝ)
    (hmem : ∀ j k : ℝ, |j| ≤ 1 → |k| ≤ 1 → |imp j k| ≤ 1)
    (hiff : ∀ j k : ℝ, |j| ≤ 1 → |k| ≤ 1 →
      (HoldsNotF (imp j k) ↔ (HoldsNotF j → HoldsNotF k)))
    (hwall : ∀ k : ℝ, |k| ≤ 1 → imp 1 k = 0)
    (hpass : ∀ j k : ℝ, |j| ≤ 1 → |k| ≤ 1 → j ≠ 1 → k ≠ 1 → imp j k = k) :
    ∀ j k : ℝ, |j| ≤ 1 → |k| ≤ 1 → imp j k = nonrefImp j k := by
  intro j k hj hk
  classical
  by_cases hj1 : j = 1
  · simpa [nonrefImp, hj1] using hwall k hk
  · by_cases hk1 : k = 1
    · have h1 : imp j k = 1 :=
        nonref_residual_on_failure imp hj (hmem j k hj hk) (hiff j k hj hk)
          ⟨hj1, hk1⟩
      simpa [nonrefImp, hj1, hk1] using h1
    · simpa [nonrefImp, hj1, hk1] using hpass j k hj hk hj1 hk1

/-- Synchrony places the value at balance; non-refutation places it on the wall. -/
theorem residual_demands_collide (imp : ℝ → ℝ → ℝ)
    (hmem : |imp (1 / 2 : ℝ) 1| ≤ 1)
    (hT : HoldsT (imp (1 / 2 : ℝ) 1) ↔
      (HoldsT (1 / 2 : ℝ) → HoldsT (1 : ℝ)))
    (hN : HoldsNotF (imp (1 / 2 : ℝ) 1) ↔
      (HoldsNotF (1 / 2 : ℝ) → HoldsNotF (1 : ℝ))) :
    imp (1 / 2 : ℝ) 1 = 0 ∧ imp (1 / 2 : ℝ) 1 = 1 := by
  refine ⟨sync_residual_of_ne_zero imp (by norm_num) hT, ?_⟩
  exact nonref_residual_on_failure imp (by norm_num) hmem hN ⟨by norm_num, rfl⟩

/-- No operation on the height residuates both designated predicates. -/
theorem no_common_residual :
    ¬ ∃ imp : ℝ → ℝ → ℝ,
      (∀ j k : ℝ, |j| ≤ 1 → |k| ≤ 1 → |imp j k| ≤ 1) ∧
        (∀ j k : ℝ, |j| ≤ 1 → |k| ≤ 1 →
          (HoldsT (imp j k) ↔ (HoldsT j → HoldsT k)) ∧
            (HoldsNotF (imp j k) ↔ (HoldsNotF j → HoldsNotF k))) := by
  rintro ⟨imp, hmem, hiff⟩
  have hpair := residual_demands_collide imp
    (hmem _ _ (by norm_num) (by norm_num))
    (hiff _ _ (by norm_num) (by norm_num)).1
    (hiff _ _ (by norm_num) (by norm_num)).2
  exact zero_ne_one (hpair.1.symm.trans hpair.2)

/-- Normalised residuals at a boost-dominant height implying the wall. -/
theorem sync_nonref_at_open_wall :
    syncImp (1 / 2 : ℝ) 1 = 0 ∧ nonrefImp (1 / 2 : ℝ) 1 = 1 :=
  ⟨syncImp_of_ne_zero (by norm_num), nonrefImp_of_failure (by norm_num) rfl⟩

/-- Both residuals designate a boost-dominant height implying synchrony. -/
theorem sync_nonref_agree_open_to_balance :
    syncImp (1 / 2 : ℝ) 0 = 0 ∧ nonrefImp (1 / 2 : ℝ) 0 = 0 :=
  ⟨syncImp_of_ne_zero (by norm_num),
    nonrefImp_of_pass (by norm_num) (by norm_num)⟩

/-- The Gödel residuum refutes a rotation-dominant height implying synchrony.
The non-refutation residual designates it. -/
theorem residuum_refutes_B_T_nonref_designates :
    residuumJ (-1 / 2 : ℝ) 0 = 1 ∧ nonrefImp (-1 / 2 : ℝ) 0 = 0 :=
  ⟨residuumJ_B_T, nonrefImp_of_pass (by norm_num) (by norm_num)⟩

/-- The normalised residuals agree exactly at balance, at the positive wall,
and on a synchronous consequent. -/
theorem syncImp_eq_nonrefImp_iff (j k : ℝ) :
    syncImp j k = nonrefImp j k ↔ j = 0 ∨ j = 1 ∨ k = 0 := by
  classical
  constructor
  · intro h
    by_cases hj0 : j = 0
    · exact Or.inl hj0
    · by_cases hj1 : j = 1
      · exact Or.inr (Or.inl hj1)
      · refine Or.inr (Or.inr ?_)
        have hs : syncImp j k = 0 := syncImp_of_ne_zero hj0
        by_cases hk1 : k = 1
        · have hn : nonrefImp j k = 1 := nonrefImp_of_failure hj1 hk1
          exact absurd (hs.symm.trans (h.trans hn)) zero_ne_one
        · have hn : nonrefImp j k = k := nonrefImp_of_pass hj1 hk1
          exact (hs.symm.trans (h.trans hn)).symm
  · rintro (rfl | rfl | rfl)
    · simp [syncImp, nonrefImp]
    · simp [syncImp, nonrefImp]
    · by_cases hj1 : j = 1
      · simp [syncImp, nonrefImp, hj1]
      · simp [syncImp, nonrefImp, hj1]

end Logic

end DstDiophantine
