import DstDiophantine.Logic.Consequence

/-!
# The Boolean core of the height

Classical truth on the wall fragment is the positive wall `+1`, and
classical falsity is the negative wall `-1`. With that reading, `negJ`,
`min`, and `max` are the Boolean connectives, and a propositional formula
is a classical tautology exactly when every wall assignment returns `+1`.

Double negation, the De Morgan laws, distributivity, and absorption are
identities of every real height. A classical proof of them is the
specialisation of that identity; the two-valued case split is idle.
Excluded middle and the syllogism do not lift. They hold on the walls,
and they fail as soon as a height leaves them. At total balance the
syllogism returns synchrony, which the classical reading does not call truth.

Material implication `max (-j) k` detaches the positive wall on every
real height. It lies strictly below that wall exactly when the negated
antecedent and the consequent do. Balance implies every nonpositive
height, and that implication is balance, so synchrony does not detach.
-/

namespace DstDiophantine

namespace Logic

attribute [local instance] Classical.propDecidable

/-- The two walls, read as classical bits. `true` is the positive wall. -/
def ofBool (b : Bool) : ℝ :=
  if b then 1 else -1

@[simp] theorem ofBool_true : ofBool true = 1 := rfl

@[simp] theorem ofBool_false : ofBool false = -1 := rfl

theorem ofBool_wall (b : Bool) : IsWallTwo (ofBool b) := by
  cases b <;> simp [IsWallTwo]

theorem ofBool_eq_one {b : Bool} : ofBool b = 1 ↔ b = true := by
  cases b with
  | false => simp [ofBool]; norm_num
  | true => simp [ofBool]

theorem ofBool_injective {a b : Bool} (h : ofBool a = ofBool b) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [ofBool] at h; norm_num at h)

theorem ofBool_neg (b : Bool) : negJ (ofBool b) = ofBool (!b) := by
  cases b <;> simp [negJ]

theorem ofBool_conj (a b : Bool) : conjJ (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> simp [conjJ]

theorem ofBool_disj (a b : Bool) : disjJ (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> simp [disjJ]

/-- Bit of a wall. Off the positive wall the bit is `false`. -/
noncomputable def wallBit (j : ℝ) : Bool :=
  if j = 1 then true else false

theorem wallBit_of_wall {j : ℝ} (h : IsWallTwo j) : j = ofBool (wallBit j) := by
  rcases h with rfl | rfl <;> simp [wallBit, ofBool]

namespace Formula

/-- Classical evaluation. `true` is the positive wall. -/
def boolEval (φ : Formula) (v : ℕ → Bool) : Bool :=
  match φ with
  | atom n => v n
  | neg ψ => !(ψ.boolEval v)
  | conj ψ χ => ψ.boolEval v && χ.boolEval v
  | disj ψ χ => ψ.boolEval v || χ.boolEval v

@[simp] theorem boolEval_atom (n : ℕ) (v : ℕ → Bool) : (atom n).boolEval v = v n := rfl

@[simp] theorem boolEval_neg (φ : Formula) (v : ℕ → Bool) :
    φ.neg.boolEval v = !(φ.boolEval v) := rfl

@[simp] theorem boolEval_conj (φ ψ : Formula) (v : ℕ → Bool) :
    (φ.conj ψ).boolEval v = (φ.boolEval v && ψ.boolEval v) := rfl

@[simp] theorem boolEval_disj (φ ψ : Formula) (v : ℕ → Bool) :
    (φ.disj ψ).boolEval v = (φ.boolEval v || ψ.boolEval v) := rfl

end Formula

/-- Wall evaluation is the Boolean evaluation of the same formula. -/
theorem eval_ofBool (φ : Formula) (v : ℕ → Bool) :
    φ.eval (fun n => ofBool (v n)) = ofBool (φ.boolEval v) := by
  induction φ with
  | atom n => simp
  | neg ψ ih => simp [ih, ofBool_neg]
  | conj ψ χ ihψ ihχ => simp [ihψ, ihχ, ofBool_conj]
  | disj ψ χ ihψ ihχ => simp [ihψ, ihχ, ofBool_disj]

/-- The wall fragment is closed under the scalar connectives. -/
theorem eval_isWall {v : ℕ → ℝ} (hv : ∀ n, IsWallTwo (v n)) (φ : Formula) :
    IsWallTwo (φ.eval v) := by
  have hv' : v = fun n => ofBool (wallBit (v n)) := by
    funext n
    exact wallBit_of_wall (hv n)
  rw [hv', eval_ofBool]
  exact ofBool_wall _

/-- A formula is a classical tautology exactly when every wall assignment
returns the positive wall. -/
theorem classical_iff_positive_wall (φ : Formula) :
    (∀ b : ℕ → Bool, φ.boolEval b = true) ↔
      ∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) → φ.eval v = 1 := by
  constructor
  · intro h v hv
    have hv' : v = fun n => ofBool (wallBit (v n)) := by
      funext n
      exact wallBit_of_wall (hv n)
    rw [hv', eval_ofBool, h, ofBool_true]
  · intro h b
    have h1 : φ.eval (fun n => ofBool (b n)) = 1 :=
      h _ (fun n => ofBool_wall (b n))
    rw [eval_ofBool] at h1
    exact (ofBool_eq_one).mp h1

/-- An identity of heights specialises to a classical equivalence.
The two-valued case split is not required for that step. -/
theorem height_identity_specialises {φ ψ : Formula}
    (h : ∀ v : ℕ → ℝ, φ.eval v = ψ.eval v) (b : ℕ → Bool) :
    φ.boolEval b = ψ.boolEval b := by
  apply ofBool_injective
  rw [← eval_ofBool, ← eval_ofBool]
  exact h _

theorem eval_neg_neg (φ : Formula) (v : ℕ → ℝ) :
    φ.neg.neg.eval v = φ.eval v := by
  simp [negJ_involutive]

theorem eval_deMorgan_conj (φ ψ : Formula) (v : ℕ → ℝ) :
    (φ.conj ψ).neg.eval v = (φ.neg.disj ψ.neg).eval v := by
  simp [deMorgan_conj]

theorem eval_deMorgan_disj (φ ψ : Formula) (v : ℕ → ℝ) :
    (φ.disj ψ).neg.eval v = (φ.neg.conj ψ.neg).eval v := by
  simp [deMorgan_disj]

/-- Conjunction absorbs a disjunction with the same height. -/
theorem conjJ_absorb (a b : ℝ) : conjJ a (disjJ a b) = a := by
  simp [conjJ, disjJ]

/-- Disjunction absorbs a conjunction with the same height. -/
theorem disjJ_absorb (a b : ℝ) : disjJ a (conjJ a b) = a := by
  simp [conjJ, disjJ]

theorem eval_absorb_conj (φ ψ : Formula) (v : ℕ → ℝ) :
    (φ.conj (φ.disj ψ)).eval v = φ.eval v := by
  simp [conjJ_absorb]

theorem eval_distrib (φ ψ χ : Formula) (v : ℕ → ℝ) :
    (φ.conj (ψ.disj χ)).eval v = ((φ.conj ψ).disj (φ.conj χ)).eval v := by
  simp [conj_distrib_left]

theorem double_neg_classical (φ : Formula) (b : ℕ → Bool) :
    φ.neg.neg.boolEval b = φ.boolEval b :=
  height_identity_specialises (eval_neg_neg φ) b

theorem deMorgan_conj_classical (φ ψ : Formula) (b : ℕ → Bool) :
    (φ.conj ψ).neg.boolEval b = (φ.neg.disj ψ.neg).boolEval b :=
  height_identity_specialises (eval_deMorgan_conj φ ψ) b

/-- On the interval, the walls are exactly the saturation of excluded middle
and of non-contradiction. Off the walls both laws fail, and what remains
is the comparison `-|j| ≤ |k|`. -/
theorem wall_saturation_iff {j : ℝ} (hj : |j| ≤ 1) :
    disjJ j (negJ j) = 1 ∧ conjJ j (negJ j) = -1 ↔ IsWallTwo j := by
  rw [disj_neg_eq_abs, conj_neg_eq_neg_abs]
  constructor
  · intro ⟨habs, _⟩
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (rfl | rfl) <;> norm_num

theorem kleene_comparison (j k : ℝ) :
    conjJ j (negJ j) ≤ disjJ k (negJ k) := by
  rw [conj_neg_eq_neg_abs, disj_neg_eq_abs]
  linarith [abs_nonneg j, abs_nonneg k]

theorem excluded_middle_classical (b : ℕ → Bool) :
    ((Formula.atom 0).disj (Formula.atom 0).neg).boolEval b = true := by
  cases h : b 0 <;> simp [h]

/-- Material implication, read on the height as `¬j ∨ k`. -/
def impJ (j k : ℝ) : ℝ :=
  disjJ (negJ j) k

/-- The syllogism, written with material implication. -/
def syllogismFormula : Formula :=
  let P := Formula.atom 0
  let Q := Formula.atom 1
  let R := Formula.atom 2
  let imp (a b : Formula) := a.neg.disj b
  (imp P Q).neg.disj ((imp Q R).neg.disj (imp P R))

theorem syllogism_classical (b : ℕ → Bool) : syllogismFormula.boolEval b = true := by
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
    simp [syllogismFormula, h0, h1, h2]

/-- At total balance the syllogism returns synchrony, not the positive wall. -/
theorem syllogism_balance :
    syllogismFormula.eval (fun _ => 0) = 0 := by
  simp [syllogismFormula, negJ, disjJ]

theorem syllogism_not_height_identity :
    syllogismFormula.eval (fun _ => 0) ≠ 1 := by
  simp [syllogism_balance]

theorem impJ_wall_iff {j k : ℝ} (hj : IsWallTwo j) (hk : IsWallTwo k) :
    impJ j k = 1 ↔ (j = 1 → k = 1) := by
  rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> simp [impJ, disjJ, negJ]

/-- Classical detachment on every real height: the positive wall is inherited. -/
theorem impJ_detach_wall {j k : ℝ} (hj : j = 1) (himp : impJ j k = 1) : k = 1 := by
  subst hj
  simp only [impJ, disjJ, negJ] at himp
  rcases le_total k (-1) with hk | hk
  · rw [max_eq_left hk] at himp
    exact absurd himp (by norm_num)
  · rw [max_eq_right hk] at himp
    exact himp

/-- Non-refutation of a material implication is the pair of non-refutations
of the negated antecedent and of the consequent. -/
theorem holdsNotF_impJ (j k : ℝ) :
    HoldsNotF (impJ j k) ↔ HoldsNotF (negJ j) ∧ HoldsNotF k := by
  simp only [HoldsNotF, impJ, disjJ, negJ]
  exact max_lt_iff

/-- Balance materially implies every nonpositive height, and the implication is balance. -/
theorem impJ_zero_of_nonpos {k : ℝ} (hk : k ≤ 0) : impJ 0 k = 0 := by
  simp only [impJ, disjJ, negJ, neg_zero, max_eq_left hk]

/-- The negative wall materially implying balance is the positive wall. -/
theorem impJ_neg_wall_balance : impJ (-1) 0 = 1 := by
  have h0 : (0 : ℝ) ≤ 1 := by norm_num
  simp only [impJ, disjJ, negJ, neg_neg, max_eq_left h0]

end Logic

end DstDiophantine
