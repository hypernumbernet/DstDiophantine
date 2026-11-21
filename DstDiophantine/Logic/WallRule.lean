import DstDiophantine.Logic.HeightIdentity

/-!
# Positive-wall rules, and where discharge stops

Modus ponens, modus tollens, disjunctive syllogism, and the syllogism
preserve the value `1` at every real height. So does the inference from
a height and its negation, because those two premises never occur
together. The formulas that package the same inferences do not: every
formula returns balance when every atom does, so none of them is the
positive wall under every assignment.

On the wall fragment a premise may be discharged into a material
implication. Off the walls the discharge fails. The atom `P` forces
`P ∨ ¬P` onto the positive wall, and `P → (P ∨ ¬P)` returns balance.

Inside the interval, preservation of the positive wall is decided by
the same three heights that decide equational identity. Weakening a
positive wall by a disjunct uses the bound `|j| ≤ 1`.
-/

namespace DstDiophantine

namespace Logic

attribute [local instance] Classical.propDecidable

open scoped Set

/-- Material implication as a formula, `¬φ ∨ ψ`. -/
def impF (φ ψ : Formula) : Formula :=
  φ.neg.disj ψ

theorem eval_impF (φ ψ : Formula) (v : ℕ → ℝ) :
    (impF φ ψ).eval v = impJ (φ.eval v) (ψ.eval v) := by
  simp [impF, impJ]

theorem max_eq_one {a b : ℝ} :
    max a b = 1 ↔ a ≤ 1 ∧ b ≤ 1 ∧ (a = 1 ∨ b = 1) := by
  constructor
  · intro h
    rcases le_total a b with hab | hab
    · rw [max_eq_right hab] at h
      exact ⟨hab.trans (le_of_eq h), le_of_eq h, Or.inr h⟩
    · rw [max_eq_left hab] at h
      exact ⟨le_of_eq h, hab.trans (le_of_eq h), Or.inl h⟩
  · rintro ⟨ha, hb, h | h⟩
    · rw [h]
      exact max_eq_left hb
    · rw [h]
      exact max_eq_right ha

/-- Modus tollens at every real height. -/
theorem impJ_tollens {j k : ℝ} (himp : impJ j k = 1) (hk : k = -1) : j = -1 := by
  simp only [impJ, disjJ, negJ] at himp
  rw [hk] at himp
  rcases ((max_eq_one).mp himp).2.2 with hneg | hwall
  · linarith
  · exact absurd hwall (by norm_num)

/-- Disjunctive syllogism at every real height. -/
theorem disjJ_tollens {j k : ℝ} (h : disjJ j k = 1) (hj : j = -1) : k = 1 := by
  simp only [disjJ] at h
  rw [hj] at h
  rcases ((max_eq_one).mp h).2.2 with hneg | hk
  · exact absurd hneg (by norm_num)
  · exact hk

/-- The syllogism rule at every real height. The packaged formula is not an identity. -/
theorem impJ_chain {j k m : ℝ} (hjk : impJ j k = 1) (hkm : impJ k m = 1) :
    impJ j m = 1 := by
  simp only [impJ, disjJ, negJ] at hjk hkm ⊢
  have hj := (max_eq_one).mp hjk
  have hk := (max_eq_one).mp hkm
  apply (max_eq_one).mpr
  refine ⟨hj.1, hk.2.1, ?_⟩
  rcases hk.2.2 with hneg | hm
  · have hkneg : k = -1 := by linarith
    rcases hj.2.2 with hjneg | hjk'
    · exact Or.inl hjneg
    · exact absurd hjk' (by rw [hkneg]; norm_num)
  · exact Or.inr hm

/-- A height and its negation are never both the positive wall. -/
theorem not_both_wall (j : ℝ) : ¬ (j = 1 ∧ negJ j = 1) := by
  rintro ⟨hj, hn⟩
  rw [negJ, hj] at hn
  norm_num at hn

/-- Every formula returns balance when every atom does. -/
theorem eval_balance (φ : Formula) : φ.eval (fun _ => 0) = 0 := by
  induction φ with
  | atom _ => simp
  | neg ψ ih => simp [ih, negJ]
  | conj ψ χ ihψ ihχ => simp [ihψ, ihχ, conjJ]
  | disj ψ χ ihψ ihχ => simp [ihψ, ihχ, disjJ]

/-- Premises at the positive wall force the conclusion there, at every real height. -/
def EntailsOne (Γ : Set Formula) (ψ : Formula) : Prop :=
  ∀ v : ℕ → ℝ, (∀ φ ∈ Γ, φ.eval v = 1) → ψ.eval v = 1

/-- The same forcing, restricted to heights in the interval. -/
def EntailsWall (Γ : Set Formula) (ψ : Formula) : Prop :=
  ∀ v : ℕ → ℝ, (∀ n, |v n| ≤ 1) → (∀ φ ∈ Γ, φ.eval v = 1) → ψ.eval v = 1

theorem entailsOne_to_wall {Γ : Set Formula} {ψ : Formula}
    (h : EntailsOne Γ ψ) : EntailsWall Γ ψ :=
  fun v _ hv => h v hv

theorem isThreeHeight_abs {j : ℝ} (h : IsThreeHeight j) : |j| ≤ 1 := by
  rcases h with rfl | rfl | rfl <;> norm_num

theorem entailsOne_modus_ponens (φ ψ : Formula) :
    EntailsOne {φ, impF φ ψ} ψ := by
  intro v hv
  exact impJ_detach_wall (hv φ (Set.mem_insert _ _))
    ((eval_impF φ ψ v).symm.trans (hv (impF φ ψ)
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem entailsOne_tollens (φ ψ : Formula) :
    EntailsOne {impF φ ψ, ψ.neg} φ.neg := by
  intro v hv
  have himp : impJ (φ.eval v) (ψ.eval v) = 1 :=
    (eval_impF φ ψ v).symm.trans
      (hv (impF φ ψ) (Set.mem_insert _ _))
  have hk : ψ.eval v = -1 := by
    have hneg : -(ψ.eval v) = 1 := by
      simpa [negJ] using hv ψ.neg (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    linarith
  have hj : φ.eval v = -1 := impJ_tollens himp hk
  simp [negJ, hj]

theorem entailsOne_disjunctive (φ ψ : Formula) :
    EntailsOne {φ.disj ψ, φ.neg} ψ := by
  intro v hv
  have hdisj : disjJ (φ.eval v) (ψ.eval v) = 1 := by
    simpa using hv (φ.disj ψ) (Set.mem_insert _ _)
  have hj : φ.eval v = -1 := by
    have hneg : -(φ.eval v) = 1 := by
      simpa [negJ] using hv φ.neg (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    linarith
  simpa using disjJ_tollens hdisj hj

theorem entailsOne_chain (φ ψ χ : Formula) :
    EntailsOne {impF φ ψ, impF ψ χ} (impF φ χ) := by
  intro v hv
  have hjk : impJ (φ.eval v) (ψ.eval v) = 1 :=
    (eval_impF φ ψ v).symm.trans
      (hv (impF φ ψ) (Set.mem_insert _ _))
  have hkm : impJ (ψ.eval v) (χ.eval v) = 1 :=
    (eval_impF ψ χ v).symm.trans
      (hv (impF ψ χ) (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  exact (eval_impF φ χ v).trans (impJ_chain hjk hkm)

/-- From a height and its negation the positive wall is preserved, vacuously. -/
theorem entailsOne_explosion (φ ψ : Formula) :
    EntailsOne {φ, φ.neg} ψ := by
  intro v hv
  have hj : φ.eval v = 1 := hv φ (Set.mem_insert _ _)
  have hn : negJ (φ.eval v) = 1 := by
    simpa using hv φ.neg (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact absurd ⟨hj, hn⟩ (not_both_wall (φ.eval v))

/-- No formula returns the positive wall under every real assignment. -/
theorem not_entailsOne_empty (φ : Formula) : ¬ EntailsOne ∅ φ := by
  intro h
  have h1 : φ.eval (fun _ => 0) = 1 := h (fun _ => 0) (by intro _ hφ; simp at hφ)
  rw [eval_balance φ] at h1
  exact zero_ne_one h1

theorem not_entailsWall_empty (φ : Formula) : ¬ EntailsWall ∅ φ := by
  intro h
  have h1 : φ.eval (fun _ => 0) = 1 :=
    h (fun _ => 0) (fun _ => by norm_num) (by intro _ hφ; simp at hφ)
  rw [eval_balance φ] at h1
  exact zero_ne_one h1

/-- On a wall assignment, material implication is the classical conditional. -/
theorem boolEval_impF (φ ψ : Formula) (b : ℕ → Bool) :
    (impF φ ψ).boolEval b = true ↔
      (φ.boolEval b = true → ψ.boolEval b = true) := by
  cases hφ : φ.boolEval b <;> cases hψ : ψ.boolEval b <;> simp [impF, hφ, hψ]

/-- Discharge is valid on the walls: one premise moves into the antecedent. -/
theorem discharge_on_walls (φ ψ : Formula) :
    (∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) → φ.eval v = 1 → ψ.eval v = 1) ↔
      (∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) → (impF φ ψ).eval v = 1) := by
  constructor
  · intro h
    have hbool : ∀ b : ℕ → Bool, φ.boolEval b = true → ψ.boolEval b = true := by
      intro b hb
      have hvb : ∀ n, IsWallTwo (ofBool (b n)) := fun n => ofBool_wall (b n)
      have hφ1 : φ.eval (fun n => ofBool (b n)) = 1 := by
        rw [eval_ofBool, hb, ofBool_true]
      have hψ1 : ψ.eval (fun n => ofBool (b n)) = 1 := h _ hvb hφ1
      rw [eval_ofBool] at hψ1
      exact (ofBool_eq_one).mp hψ1
    have himp : ∀ b : ℕ → Bool, (impF φ ψ).boolEval b = true :=
      fun b => (boolEval_impF φ ψ b).mpr (hbool b)
    intro v hv
    exact (classical_iff_positive_wall (impF φ ψ)).mp himp v hv
  · intro h v hv hφ
    exact impJ_detach_wall hφ ((eval_impF φ ψ v).symm.trans (h v hv))

/-- The atom forces its excluded middle onto the positive wall. -/
theorem entailsOne_excluded_middle :
    EntailsOne {(Formula.atom 0)} (excludedMiddle 0) := by
  intro v hv
  have h0 : v 0 = 1 := by simpa using hv (Formula.atom 0) (Set.mem_singleton _)
  simp [excludedMiddle_eval, h0]

/-- Discharging that inference returns balance at total balance. -/
theorem discharge_excluded_middle_balance :
    (impF (Formula.atom 0) (excludedMiddle 0)).eval (fun _ => 0) = 0 :=
  eval_balance _

theorem not_discharge_excluded_middle :
    ¬ ∀ v : ℕ → ℝ, (impF (Formula.atom 0) (excludedMiddle 0)).eval v = 1 := by
  intro h
  have h0 := h (fun _ => 0)
  rw [discharge_excluded_middle_balance] at h0
  exact zero_ne_one h0

/-- Positive-wall consequence on the interval is decided by `{-1, 0, 1}`. -/
theorem entailsWall_iff_threeHeight (Γ : Set Formula) (ψ : Formula) :
    EntailsWall Γ ψ ↔
      ∀ v : ℕ → ℝ, (∀ n, IsThreeHeight (v n)) →
        (∀ φ ∈ Γ, φ.eval v = 1) → ψ.eval v = 1 := by
  constructor
  · intro h v hv3 hprem
    exact h v (fun n => isThreeHeight_abs (hv3 n)) hprem
  · intro h v hv hprem
    classical
    let w : ℕ → ℝ := fun n => threeCollapse 1 (v n)
    have ht : (0 : ℝ) < 1 := by norm_num
    have hw3 : ∀ n, IsThreeHeight (w n) := fun n => threeCollapse_mem ht
    have hpremW : ∀ φ ∈ Γ, φ.eval w = 1 := by
      intro φ hφ
      have hφ1 : φ.eval v = 1 := hprem φ hφ
      have hcollapse : φ.eval w = threeCollapse 1 (φ.eval v) :=
        eval_threeCollapse ht φ v
      rw [hcollapse, hφ1]
      exact (threeCollapse_eq_one_iff ht).mpr (le_refl _)
    have hψw : ψ.eval w = 1 := h w hw3 hpremW
    have hcollapse : threeCollapse 1 (ψ.eval v) = 1 := by
      rw [← eval_threeCollapse ht ψ v]
      exact hψw
    have hge : (1 : ℝ) ≤ ψ.eval v := (threeCollapse_eq_one_iff ht).mp hcollapse
    have hle : ψ.eval v ≤ 1 := (abs_le.mp (Formula.eval_mem ψ hv)).2
    exact le_antisymm hle hge

/-- Inside the interval a positive wall may be weakened by any disjunct. -/
theorem entailsWall_disj (φ ψ : Formula) : EntailsWall {φ} (φ.disj ψ) := by
  intro v hv hprem
  have hφ : φ.eval v = 1 := hprem φ (Set.mem_singleton _)
  have hψ : ψ.eval v ≤ 1 := (abs_le.mp (Formula.eval_mem ψ hv)).2
  have hdisj : disjJ (φ.eval v) (ψ.eval v) = 1 := by
    rw [disjJ, hφ]
    exact max_eq_left hψ
  simpa using hdisj

/-- Above the wall the same weakening leaves the positive wall. -/
theorem not_entailsOne_disj :
    ¬ EntailsOne {(Formula.atom 0)} ((Formula.atom 0).disj (Formula.atom 1)) := by
  intro h
  let v : ℕ → ℝ := fun n => if n = 0 then 1 else 2
  have hprem : ∀ φ ∈ ({Formula.atom 0} : Set Formula), φ.eval v = 1 := by
    intro φ hφ
    rw [Set.eq_of_mem_singleton hφ]
    simp [v]
  have h1 := h v hprem
  simp [v, disjJ] at h1

end Logic

end DstDiophantine
