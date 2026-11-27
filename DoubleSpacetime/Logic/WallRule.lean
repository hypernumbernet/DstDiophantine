import DoubleSpacetime.Logic.HeightIdentity

/-!
# Positive-wall consequence

`EntailsOne` forces the value `1` at every real height. `EntailsWall` restricts assignments to
`[-1, 1]`. Discharge into material implication holds on the walls and fails off them. `EntailsOne`,
`EntailsT`, and `EntailsNotF` are pairwise incomparable.
-/

namespace DoubleSpacetime

namespace Logic

attribute [local instance] Classical.propDecidable

open scoped Set

/-- Formula `¬φ ∨ ψ`. -/
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

theorem impJ_tollens {j k : ℝ} (himp : impJ j k = 1) (hk : k = -1) : j = -1 := by
  simp only [impJ, disjJ, negJ] at himp
  rw [hk] at himp
  rcases ((max_eq_one).mp himp).2.2 with hneg | hwall
  · linarith
  · exact absurd hwall (by norm_num)

theorem disjJ_tollens {j k : ℝ} (h : disjJ j k = 1) (hj : j = -1) : k = 1 := by
  simp only [disjJ] at h
  rw [hj] at h
  rcases ((max_eq_one).mp h).2.2 with hneg | hk
  · exact absurd hneg (by norm_num)
  · exact hk

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

theorem not_both_wall (j : ℝ) : ¬ (j = 1 ∧ negJ j = 1) := by
  rintro ⟨hj, hn⟩
  rw [negJ, hj] at hn
  norm_num at hn

theorem eval_balance (φ : Formula) : φ.eval (fun _ => 0) = 0 := by
  induction φ with
  | atom _ => simp
  | neg ψ ih => simp [ih, negJ]
  | conj ψ χ ihψ ihχ => simp [ihψ, ihχ, conjJ]
  | disj ψ χ ihψ ihχ => simp [ihψ, ihχ, disjJ]

/-- Premises equal to `1` force the conclusion to `1`. -/
def EntailsOne (Γ : Set Formula) (ψ : Formula) : Prop :=
  ∀ v : ℕ → ℝ, (∀ φ ∈ Γ, φ.eval v = 1) → ψ.eval v = 1

/-- `EntailsOne` on assignments into `[-1, 1]`. -/
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

theorem entailsOne_explosion (φ ψ : Formula) :
    EntailsOne {φ, φ.neg} ψ := by
  intro v hv
  have hj : φ.eval v = 1 := hv φ (Set.mem_insert _ _)
  have hn : negJ (φ.eval v) = 1 := by
    simpa using hv φ.neg (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact absurd ⟨hj, hn⟩ (not_both_wall (φ.eval v))

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

theorem boolEval_impF (φ ψ : Formula) (b : ℕ → Bool) :
    (impF φ ψ).boolEval b = true ↔
      (φ.boolEval b = true → ψ.boolEval b = true) := by
  cases hφ : φ.boolEval b <;> cases hψ : ψ.boolEval b <;> simp [impF, hφ, hψ]

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

theorem entailsOne_excluded_middle :
    EntailsOne {(Formula.atom 0)} (excludedMiddle 0) := by
  intro v hv
  have h0 : v 0 = 1 := by simpa using hv (Formula.atom 0) (Set.mem_singleton _)
  simp [excludedMiddle_eval, h0]

theorem discharge_excluded_middle_balance :
    (impF (Formula.atom 0) (excludedMiddle 0)).eval (fun _ => 0) = 0 :=
  eval_balance _

theorem not_discharge_excluded_middle :
    ¬ ∀ v : ℕ → ℝ, (impF (Formula.atom 0) (excludedMiddle 0)).eval v = 1 := by
  intro h
  have h0 := h (fun _ => 0)
  rw [discharge_excluded_middle_balance] at h0
  exact zero_ne_one h0

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

theorem entailsWall_disj (φ ψ : Formula) : EntailsWall {φ} (φ.disj ψ) := by
  intro v hv hprem
  have hφ : φ.eval v = 1 := hprem φ (Set.mem_singleton _)
  have hψ : ψ.eval v ≤ 1 := (abs_le.mp (Formula.eval_mem ψ hv)).2
  have hdisj : disjJ (φ.eval v) (ψ.eval v) = 1 := by
    rw [disjJ, hφ]
    exact max_eq_left hψ
  simpa using hdisj

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

/-! ## Classical cut -/

/-- Classical consequence on Boolean assignments. -/
def EntailsClassical (Γ : Set Formula) (ψ : Formula) : Prop :=
  ∀ b : ℕ → Bool, (∀ φ ∈ Γ, φ.boolEval b = true) → ψ.boolEval b = true

theorem isWallTwo_abs {j : ℝ} (h : IsWallTwo j) : |j| ≤ 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem entailsClassical_iff_wall (Γ : Set Formula) (ψ : Formula) :
    EntailsClassical Γ ψ ↔
      ∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) →
        (∀ φ ∈ Γ, φ.eval v = 1) → ψ.eval v = 1 := by
  constructor
  · intro h v hv hprem
    let b : ℕ → Bool := fun n => wallBit (v n)
    have hvb : v = fun n => ofBool (b n) := by
      funext n
      exact wallBit_of_wall (hv n)
    have hpremB : ∀ φ ∈ Γ, φ.boolEval b = true := by
      intro φ hφ
      have h1 : φ.eval v = 1 := hprem φ hφ
      rw [hvb, eval_ofBool] at h1
      exact (ofBool_eq_one).mp h1
    have hψB : ψ.boolEval b = true := h b hpremB
    rw [hvb, eval_ofBool, hψB, ofBool_true]
  · intro h b hprem
    have hv : ∀ n, IsWallTwo (ofBool (b n)) := fun n => ofBool_wall _
    have hprem1 : ∀ φ ∈ Γ, φ.eval (fun n => ofBool (b n)) = 1 := by
      intro φ hφ
      rw [eval_ofBool, hprem φ hφ, ofBool_true]
    have h1 : ψ.eval (fun n => ofBool (b n)) = 1 := h _ hv hprem1
    rw [eval_ofBool] at h1
    exact (ofBool_eq_one).mp h1

/-- Atoms in the premises or the conclusion. -/
def support (Γ : Finset Formula) (ψ : Formula) : Finset ℕ :=
  Γ.biUnion Formula.atoms ∪ ψ.atoms

theorem mem_support_of_premise {Γ : Finset Formula} {ψ φ : Formula} {n : ℕ}
    (hφ : φ ∈ Γ) (hn : n ∈ φ.atoms) : n ∈ support Γ ψ :=
  Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨φ, hφ, hn⟩))

theorem mem_support_of_conclusion {Γ : Finset Formula} {ψ : Formula} {n : ℕ}
    (hn : n ∈ ψ.atoms) : n ∈ support Γ ψ :=
  Finset.mem_union.mpr (Or.inr hn)

theorem entailsWall_iff_support (Γ : Finset Formula) (ψ : Formula) :
    EntailsWall (↑Γ) ψ ↔
      ∀ v : ℕ → ℝ, (∀ n ∈ support Γ ψ, IsThreeHeight (v n)) →
        (∀ φ ∈ Γ, φ.eval v = 1) → ψ.eval v = 1 := by
  constructor
  · intro h v hv hprem
    let w : ℕ → ℝ := fun n => if n ∈ support Γ ψ then v n else 0
    have hw : ∀ n, |w n| ≤ 1 := by
      intro n
      by_cases hn : n ∈ support Γ ψ
      · rw [show w n = v n by simp [w, hn]]
        exact isThreeHeight_abs (hv n hn)
      · simp [w, hn]
    have hpremW : ∀ φ ∈ (↑Γ : Set Formula), φ.eval w = 1 := by
      intro φ hφ
      have hagree : φ.eval v = φ.eval w :=
        Formula.eval_eq_of_agree_on_atoms fun n hn => by
          have hn' : n ∈ support Γ ψ := mem_support_of_premise (ψ := ψ) hφ hn
          simp [w, hn']
      rw [← hagree]
      exact hprem φ hφ
    have hψw : ψ.eval w = 1 := h w hw hpremW
    have hagree : ψ.eval v = ψ.eval w :=
      Formula.eval_eq_of_agree_on_atoms fun n hn => by
        have hn' : n ∈ support Γ ψ := mem_support_of_conclusion (ψ := ψ) hn
        simp [w, hn']
    rw [hagree]
    exact hψw
  · intro h
    rw [entailsWall_iff_threeHeight]
    intro v hv hprem
    exact h v (fun n _ => hv n) hprem

/-- Codes of `{-1, 0, 1}`. -/
inductive HeightCode
  | neg
  | bal
  | pos
  deriving DecidableEq

namespace HeightCode

def toReal : HeightCode → ℝ
  | neg => -1
  | bal => 0
  | pos => 1

/-- `pos` is `true`. Balance is not a wall bit. -/
def bit : HeightCode → Bool
  | neg => false
  | bal => false
  | pos => true

noncomputable def ofThree (j : ℝ) : HeightCode :=
  if j = -1 then neg else if j = 0 then bal else pos

theorem abs_toReal (c : HeightCode) : |c.toReal| ≤ 1 := by
  cases c <;> norm_num [toReal]

theorem toReal_ofThree {j : ℝ} (h : IsThreeHeight j) : (ofThree j).toReal = j := by
  rcases h with rfl | rfl | rfl
  · simp [ofThree, toReal]
  · have h1 : ¬ ((0 : ℝ) = -1) := by norm_num
    simp [ofThree, toReal, h1]
  · have h1 : ¬ ((1 : ℝ) = -1) := by norm_num
    have h0 : ¬ ((1 : ℝ) = 0) := by norm_num
    simp [ofThree, toReal, h1, h0]

theorem ofThree_zero : ofThree 0 = bal := by
  simp [ofThree]

theorem ofBool_bit_of_ne_zero {j : ℝ} (h : IsThreeHeight j) (h0 : j ≠ 0) :
    ofBool (ofThree j).bit = j := by
  rcases h with rfl | rfl | rfl
  · simp [ofThree, bit, ofBool]
  · exact absurd rfl h0
  · have h1 : ¬ ((1 : ℝ) = -1) := by norm_num
    have hz : ¬ ((1 : ℝ) = 0) := by norm_num
    simp [ofThree, bit, ofBool, h1, hz]

end HeightCode

/-- Codes on `s`, balance off `s`. -/
noncomputable def extendHeight (s : Finset ℕ) (f : {n // n ∈ s} → HeightCode) (n : ℕ) : ℝ :=
  if h : n ∈ s then (f ⟨n, h⟩).toReal else 0

theorem extendHeight_abs (s : Finset ℕ) (f : {n // n ∈ s} → HeightCode) (n : ℕ) :
    |extendHeight s f n| ≤ 1 := by
  rw [extendHeight]
  by_cases hn : n ∈ s
  · rw [dite_eq_left hn]
    exact HeightCode.abs_toReal _
  · rw [dite_eq_right hn]
    norm_num

theorem extendHeight_eq_of_three {s : Finset ℕ} {v : ℕ → ℝ}
    (hv : ∀ n ∈ s, IsThreeHeight (v n)) (n : ℕ) (hn : n ∈ s) :
    extendHeight s (fun m => HeightCode.ofThree (v m)) n = v n := by
  rw [extendHeight, dite_eq_left hn]
  exact HeightCode.toReal_ofThree (hv n hn)

theorem eval_ofBool_on_atoms (φ : Formula) {v : ℕ → ℝ} {b : ℕ → Bool}
    (h : ∀ n ∈ φ.atoms, v n = ofBool (b n)) :
    φ.eval v = ofBool (φ.boolEval b) := by
  induction φ with
  | atom n =>
    simpa using h n (by simp)
  | neg ψ ih =>
    simp [ih h, ofBool_neg]
  | conj ψ χ ihψ ihχ =>
    simp [ihψ (fun n hn => h n (Finset.mem_union.mpr (Or.inl hn))),
      ihχ (fun n hn => h n (Finset.mem_union.mpr (Or.inr hn))), ofBool_conj]
  | disj ψ χ ihψ ihχ =>
    simp [ihψ (fun n hn => h n (Finset.mem_union.mpr (Or.inl hn))),
      ihχ (fun n hn => h n (Finset.mem_union.mpr (Or.inr hn))), ofBool_disj]

/-- Atoms left at balance still force the conclusion to `1`. -/
noncomputable def BalanceCase (Γ : Finset Formula) (ψ : Formula) : Prop :=
  ∀ f : {n // n ∈ support Γ ψ} → HeightCode,
    (∃ n, f n = .bal) →
    (∀ φ ∈ Γ, φ.eval (extendHeight (support Γ ψ) f) = 1) →
      ψ.eval (extendHeight (support Γ ψ) f) = 1

theorem entailsWall_cut (Γ : Finset Formula) (ψ : Formula) :
    EntailsWall (↑Γ) ψ ↔ EntailsClassical (↑Γ) ψ ∧ BalanceCase Γ ψ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [entailsClassical_iff_wall]
      intro v hv hprem
      exact h v (fun n => isWallTwo_abs (hv n)) hprem
    · intro f _ hprem
      exact h (extendHeight (support Γ ψ) f) (extendHeight_abs _ f) hprem
  · rintro ⟨hC, hB⟩
    rw [entailsWall_iff_support]
    intro v hv hprem
    let s := support Γ ψ
    let f : {n // n ∈ s} → HeightCode := fun m => HeightCode.ofThree (v m)
    have hpremE : ∀ φ ∈ Γ, φ.eval (extendHeight s f) = 1 := by
      intro φ hφ
      have hagree : φ.eval (extendHeight s f) = φ.eval v :=
        Formula.eval_eq_of_agree_on_atoms fun n hn => by
          exact extendHeight_eq_of_three hv n (mem_support_of_premise hφ hn)
      rw [hagree]
      exact hprem φ hφ
    by_cases hbal : ∃ n : {n // n ∈ s}, f n = HeightCode.bal
    · have hψE : ψ.eval (extendHeight s f) = 1 := hB f hbal hpremE
      have hagree : ψ.eval (extendHeight s f) = ψ.eval v :=
        Formula.eval_eq_of_agree_on_atoms fun n hn =>
          extendHeight_eq_of_three hv n (mem_support_of_conclusion hn)
      rw [← hagree]
      exact hψE
    · push Not at hbal
      have hwall : ∀ n ∈ s, v n ≠ 0 := by
        intro n hn h0
        have hf : f ⟨n, hn⟩ = HeightCode.bal := by
          simp [f, h0, HeightCode.ofThree_zero]
        exact hbal ⟨n, hn⟩ hf
      let b : ℕ → Bool := fun n =>
        if h : n ∈ s then (f ⟨n, h⟩).bit else false
      have hmatch (φ : Formula) (hsub : φ.atoms ⊆ s) :
          φ.eval (extendHeight s f) = ofBool (φ.boolEval b) :=
        eval_ofBool_on_atoms φ fun n hn => by
          have hn' : n ∈ s := hsub hn
          have hbit : ofBool (f ⟨n, hn'⟩).bit = v n := by
            simp only [f]
            exact HeightCode.ofBool_bit_of_ne_zero (hv n hn') (hwall n hn')
          have hext : extendHeight s f n = v n :=
            extendHeight_eq_of_three hv n hn'
          have hb : b n = (f ⟨n, hn'⟩).bit := by simp [b, hn']
          rw [hext, ← hbit, hb]
      have hpremB : ∀ φ ∈ (↑Γ : Set Formula), φ.boolEval b = true := by
        intro φ hφ
        have hsub : φ.atoms ⊆ s := fun n hn => mem_support_of_premise hφ hn
        have h1 : φ.eval (extendHeight s f) = 1 := hpremE φ hφ
        rw [hmatch φ hsub] at h1
        exact (ofBool_eq_one).mp h1
      have hψB : ψ.boolEval b = true := hC b hpremB
      have hsubψ : ψ.atoms ⊆ s := fun n hn => mem_support_of_conclusion hn
      have hψE : ψ.eval (extendHeight s f) = 1 := by
        rw [hmatch ψ hsubψ, hψB, ofBool_true]
      have hagree : ψ.eval (extendHeight s f) = ψ.eval v :=
        Formula.eval_eq_of_agree_on_atoms fun n hn =>
          extendHeight_eq_of_three hv n (mem_support_of_conclusion hn)
      rw [← hagree]
      exact hψE

theorem coe_finset_pair (φ ψ : Formula) :
    (↑({φ, ψ} : Finset Formula) : Set Formula) = {φ, ψ} := by
  ext χ
  simp

theorem cut_of_entailsOne (Γ : Finset Formula) {ψ : Formula}
    (h : EntailsOne (↑Γ) ψ) :
    EntailsClassical (↑Γ) ψ ∧ BalanceCase Γ ψ :=
  (entailsWall_cut Γ ψ).mp (entailsOne_to_wall h)

theorem modus_ponens_cut (φ ψ : Formula) :
    EntailsClassical (↑({φ, impF φ ψ} : Finset Formula)) ψ ∧
      BalanceCase {φ, impF φ ψ} ψ := by
  refine cut_of_entailsOne _ ?_
  rw [coe_finset_pair]
  exact entailsOne_modus_ponens φ ψ

theorem tollens_cut (φ ψ : Formula) :
    EntailsClassical (↑({impF φ ψ, ψ.neg} : Finset Formula)) φ.neg ∧
      BalanceCase {impF φ ψ, ψ.neg} φ.neg := by
  refine cut_of_entailsOne _ ?_
  rw [coe_finset_pair]
  exact entailsOne_tollens φ ψ

theorem disjunctive_cut (φ ψ : Formula) :
    EntailsClassical (↑({φ.disj ψ, φ.neg} : Finset Formula)) ψ ∧
      BalanceCase {φ.disj ψ, φ.neg} ψ := by
  refine cut_of_entailsOne _ ?_
  rw [coe_finset_pair]
  exact entailsOne_disjunctive φ ψ

theorem chain_cut (φ ψ χ : Formula) :
    EntailsClassical (↑({impF φ ψ, impF ψ χ} : Finset Formula)) (impF φ χ) ∧
      BalanceCase {impF φ ψ, impF ψ χ} (impF φ χ) := by
  refine cut_of_entailsOne _ ?_
  rw [coe_finset_pair]
  exact entailsOne_chain φ ψ χ

theorem excludedMiddle_classical_not_balance :
    EntailsClassical (↑(∅ : Finset Formula)) (excludedMiddle 0) ∧
      ¬ BalanceCase ∅ (excludedMiddle 0) := by
  refine ⟨?_, ?_⟩
  · intro b _
    exact excluded_middle_classical b
  · intro h
    have h0 : (0 : ℕ) ∈ support ∅ (excludedMiddle 0) := by
      simp [support, excludedMiddle]
    let f : {n // n ∈ support ∅ (excludedMiddle 0)} → HeightCode := fun _ => .bal
    have hψ := h f ⟨⟨0, h0⟩, rfl⟩ (by intro _ hφ; simp at hφ)
    have hext : extendHeight (support ∅ (excludedMiddle 0)) f 0 = 0 := by
      rw [extendHeight, dite_eq_left h0]
      simp [f, HeightCode.toReal]
    have heval : (excludedMiddle 0).eval (extendHeight _ f) = 0 := by
      rw [excludedMiddle_eval, hext]
      norm_num
    rw [heval] at hψ
    exact zero_ne_one hψ

theorem excludedMiddle_atom_at_balance :
    ∃ v : ℕ → ℝ, (∀ n ∈ support ∅ (excludedMiddle 0), IsThreeHeight (v n)) ∧
      v 0 = 0 ∧ (excludedMiddle 0).eval v = 0 := by
  refine ⟨fun _ => 0, ?_, rfl, ?_⟩
  · intro n _
    simp [IsThreeHeight]
  · simp [excludedMiddle_eval]

/-! ## Discharge -/

/-- `φ₁ → (⋯ → (φₙ → ψ))`. -/
def discharge : List Formula → Formula → Formula
  | [], ψ => ψ
  | φ :: Γ, ψ => impF φ (discharge Γ ψ)

theorem boolEval_discharge (Γ : List Formula) (ψ : Formula) (b : ℕ → Bool) :
    (discharge Γ ψ).boolEval b = true ↔
      ((∀ φ ∈ Γ, φ.boolEval b = true) → ψ.boolEval b = true) := by
  induction Γ with
  | nil => simp [discharge]
  | cons φ Γ ih =>
    simp only [discharge, List.mem_cons, boolEval_impF, ih]
    constructor
    · intro h hprem
      exact (h (hprem φ (Or.inl rfl)))
        (fun χ hχ => hprem χ (Or.inr hχ))
    · intro h hφ hΓ
      exact h (fun χ hχ => by
        rcases hχ with rfl | hχ
        · exact hφ
        · exact hΓ χ hχ)

theorem discharge_wall_iff (Γ : List Formula) (ψ : Formula) :
    (∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) →
        (∀ φ ∈ Γ, φ.eval v = 1) → ψ.eval v = 1) ↔
      (∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) →
        (discharge Γ ψ).eval v = 1) := by
  constructor
  · intro h
    have hbool : ∀ b : ℕ → Bool, (discharge Γ ψ).boolEval b = true := by
      intro b
      rw [boolEval_discharge]
      intro hprem
      have hv : ∀ n, IsWallTwo (ofBool (b n)) := fun n => ofBool_wall _
      have hprem1 : ∀ φ ∈ Γ, φ.eval (fun n => ofBool (b n)) = 1 := by
        intro φ hφ
        rw [eval_ofBool, hprem φ hφ, ofBool_true]
      have h1 : ψ.eval (fun n => ofBool (b n)) = 1 := h _ hv hprem1
      rw [eval_ofBool] at h1
      exact (ofBool_eq_one).mp h1
    intro v hv
    exact (classical_iff_positive_wall (discharge Γ ψ)).mp hbool v hv
  · intro h v hv hprem
    let b : ℕ → Bool := fun n => wallBit (v n)
    have hvb : v = fun n => ofBool (b n) := by
      funext n
      exact wallBit_of_wall (hv n)
    have hpremB : ∀ φ ∈ Γ, φ.boolEval b = true := by
      intro φ hφ
      have h1 : φ.eval v = 1 := hprem φ hφ
      rw [hvb, eval_ofBool] at h1
      exact (ofBool_eq_one).mp h1
    have hdis : (discharge Γ ψ).eval v = 1 := h v hv
    have hdisB : (discharge Γ ψ).boolEval b = true := by
      rw [hvb, eval_ofBool] at hdis
      exact (ofBool_eq_one).mp hdis
    rw [boolEval_discharge] at hdisB
    rw [hvb, eval_ofBool, hdisB hpremB, ofBool_true]

theorem discharge_balance (Γ : List Formula) (ψ : Formula) :
    (discharge Γ ψ).eval (fun _ => 0) = 0 :=
  eval_balance _

theorem discharge_depth (Γ : List Formula) (ψ : Formula) :
    ((∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) →
          (∀ φ ∈ Γ, φ.eval v = 1) → ψ.eval v = 1) ↔
        (∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) →
          (discharge Γ ψ).eval v = 1)) ∧
      (discharge Γ ψ).eval (fun _ => 0) = 0 :=
  ⟨discharge_wall_iff Γ ψ, discharge_balance Γ ψ⟩

theorem syllogismFormula_discharge :
    syllogismFormula =
      discharge [impF (Formula.atom 0) (Formula.atom 1),
          impF (Formula.atom 1) (Formula.atom 2)]
        (impF (Formula.atom 0) (Formula.atom 2)) := by
  rfl

theorem chain_depth_two :
    EntailsOne {impF (Formula.atom 0) (Formula.atom 1),
        impF (Formula.atom 1) (Formula.atom 2)}
      (impF (Formula.atom 0) (Formula.atom 2)) ∧
      syllogismFormula.eval (fun _ => 0) = 0 :=
  ⟨entailsOne_chain (Formula.atom 0) (Formula.atom 1) (Formula.atom 2),
    syllogism_balance⟩

/-! ## Incomparability -/

theorem entailsOne_not_entailsT :
    EntailsOne (contradict (Formula.atom 0)) (Formula.atom 1) ∧
      ¬ EntailsT (contradict (Formula.atom 0)) (Formula.atom 1) := by
  refine ⟨entailsOne_explosion _ _, ?_⟩
  intro h
  let v := Valuation.pair 0 1 (by norm_num) (by norm_num)
  have hM : ModelsT v (contradict (Formula.atom 0)) := by
    rw [modelsT_contradict]
    simp [v, HoldsT, negJ]
  have := h v hM
  simp [HoldsT, v] at this

theorem entailsT_not_entailsOne :
    EntailsT {(Formula.atom 0).disj (Formula.atom 0).neg} (Formula.atom 0) ∧
      ¬ EntailsOne {(Formula.atom 0).disj (Formula.atom 0).neg} (Formula.atom 0) := by
  constructor
  · intro v hv
    have h := hv _ (Set.mem_singleton _)
    simpa using (holdsT_excluded_middle (v.assign 0)).mp h
  · intro h
    let v : ℕ → ℝ := fun n => if n = 0 then -1 else 0
    have hprem : ∀ φ ∈
        ({(Formula.atom 0).disj (Formula.atom 0).neg} : Set Formula),
        φ.eval v = 1 := by
      intro φ hφ
      rw [Set.eq_of_mem_singleton hφ]
      simp [v, disj_neg_eq_abs]
    have h1 := h v hprem
    simp [v] at h1
    norm_num at h1

theorem entailsOne_not_entailsNotF :
    EntailsOne (contradict (Formula.atom 0)) (Formula.atom 1) ∧
      ¬ EntailsNotF (contradict (Formula.atom 0)) (Formula.atom 1) := by
  refine ⟨entailsOne_explosion _ _, ?_⟩
  intro h
  let v := Valuation.pair (-(1 / 2)) 1 (by norm_num) (by norm_num)
  have hM : ModelsNotF v (contradict (Formula.atom 0)) := by
    rw [modelsNotF_contradict]
    simp [v, HoldsNotF, negJ]
    norm_num
  have := h v hM
  simp [HoldsNotF, v] at this

theorem entailsNotF_not_entailsOne :
    EntailsNotF ∅ ((Formula.atom 0).conj (Formula.atom 0).neg) ∧
      ¬ EntailsOne ∅ ((Formula.atom 0).conj (Formula.atom 0).neg) := by
  refine ⟨entailsNotF_conj_neg _, ?_⟩
  intro h
  have h1 := h (fun _ => 0) (by intro _ hφ; simp at hφ)
  simp [conjJ, negJ] at h1

theorem entailsT_not_entailsNotF :
    EntailsT {(Formula.atom 0)} ((Formula.atom 0).disj (Formula.atom 0).neg) ∧
      ¬ EntailsNotF {(Formula.atom 0)}
        ((Formula.atom 0).disj (Formula.atom 0).neg) :=
  ⟨entailsT_excluded_middle _, not_entailsNotF_excluded_middle⟩

theorem entailsNotF_not_entailsT :
    EntailsNotF ∅ ((Formula.atom 0).conj (Formula.atom 0).neg) ∧
      ¬ EntailsT ∅ ((Formula.atom 0).conj (Formula.atom 0).neg) :=
  ⟨entailsNotF_conj_neg _, not_entailsT_conj_neg⟩

theorem consequence_relations_incomparable :
    (EntailsOne (contradict (Formula.atom 0)) (Formula.atom 1) ∧
      ¬ EntailsT (contradict (Formula.atom 0)) (Formula.atom 1)) ∧
    (EntailsT {(Formula.atom 0).disj (Formula.atom 0).neg} (Formula.atom 0) ∧
      ¬ EntailsOne {(Formula.atom 0).disj (Formula.atom 0).neg} (Formula.atom 0)) ∧
    (EntailsOne (contradict (Formula.atom 0)) (Formula.atom 1) ∧
      ¬ EntailsNotF (contradict (Formula.atom 0)) (Formula.atom 1)) ∧
    (EntailsNotF ∅ ((Formula.atom 0).conj (Formula.atom 0).neg) ∧
      ¬ EntailsOne ∅ ((Formula.atom 0).conj (Formula.atom 0).neg)) ∧
    (EntailsT {(Formula.atom 0)} ((Formula.atom 0).disj (Formula.atom 0).neg) ∧
      ¬ EntailsNotF {(Formula.atom 0)}
        ((Formula.atom 0).disj (Formula.atom 0).neg)) ∧
    (EntailsNotF ∅ ((Formula.atom 0).conj (Formula.atom 0).neg) ∧
      ¬ EntailsT ∅ ((Formula.atom 0).conj (Formula.atom 0).neg)) :=
  ⟨entailsOne_not_entailsT, entailsT_not_entailsOne, entailsOne_not_entailsNotF,
    entailsNotF_not_entailsOne, entailsT_not_entailsNotF, entailsNotF_not_entailsT⟩

end Logic

end DoubleSpacetime
