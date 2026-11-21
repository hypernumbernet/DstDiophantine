import DstDiophantine.Logic.ClassicalCore

/-!
# Which equivalences are identities of the height

Conjunction selects, disjunction selects, and negation swaps a sign, so
every formula returns the value of one literal. Two formulas therefore
agree at every real height if and only if they agree whenever every atom
lies in `{-1, 0, 1}`. The comparison is a homomorphism: the odd monotone
collapse at the threshold `max |φ| |ψ|` preserves `min`, `max`, and sign
flip, and it separates any two distinct reals.

Agreement on the two walls is strictly coarser. Both excluded middles
return the positive wall under every wall assignment, and the assignment
that sends one atom to the positive wall and the other to balance
separates them. A height identity rewrites under every one-hole context.
-/

namespace DstDiophantine

namespace Logic

attribute [local instance] Classical.propDecidable

/-- The three heights that decide equational identity. -/
def IsThreeHeight (j : ℝ) : Prop :=
  j = -1 ∨ j = 0 ∨ j = 1

/-- Odd monotone collapse onto those three heights.
A positive threshold sends every height strictly inside `(-t, t)` to
balance, and every height outside that interval to the wall of its sign. -/
noncomputable def threeCollapse (t x : ℝ) : ℝ :=
  if |x| < t then 0 else if 0 ≤ x then 1 else -1

theorem threeCollapse_eq_zero_iff {t x : ℝ} (_ht : 0 < t) :
    threeCollapse t x = 0 ↔ |x| < t := by
  constructor
  · intro h
    by_cases hx : |x| < t
    · exact hx
    · by_cases hx0 : 0 ≤ x
      · simp [threeCollapse, hx, hx0] at h
      · simp [threeCollapse, hx, hx0] at h
  · intro hx
    simp [threeCollapse, hx]

theorem threeCollapse_eq_one_iff {t x : ℝ} (ht : 0 < t) :
    threeCollapse t x = 1 ↔ t ≤ x := by
  constructor
  · intro h
    by_cases hx : |x| < t
    · simp [threeCollapse, hx] at h
    · by_cases hx0 : 0 ≤ x
      · rw [abs_of_nonneg hx0] at hx
        exact le_of_not_gt hx
      · simp [threeCollapse, hx, hx0] at h
        norm_num at h
  · intro hx
    have hx0 : 0 ≤ x := le_trans ht.le hx
    have hnot : ¬ |x| < t := by
      rw [abs_of_nonneg hx0]
      exact not_lt.mpr hx
    simp [threeCollapse, hnot, hx0]

theorem threeCollapse_eq_neg_one_iff {t x : ℝ} (ht : 0 < t) :
    threeCollapse t x = -1 ↔ x ≤ -t := by
  constructor
  · intro h
    by_cases hx : |x| < t
    · simp [threeCollapse, hx] at h
    · by_cases hx0 : 0 ≤ x
      · simp [threeCollapse, hx, hx0] at h
        norm_num at h
      · have hxlt : x < 0 := lt_of_not_ge hx0
        rw [abs_of_neg hxlt] at hx
        linarith
  · intro hx
    have hxlt : x < 0 := lt_of_le_of_lt hx (neg_neg_of_pos ht)
    have hnot : ¬ |x| < t := by
      rw [abs_of_neg hxlt]
      linarith
    have hx0 : ¬ 0 ≤ x := not_le.mpr hxlt
    simp [threeCollapse, hnot, hx0]

theorem threeCollapse_trichotomy {t x : ℝ} (ht : 0 < t) :
    threeCollapse t x = -1 ∨ threeCollapse t x = 0 ∨ threeCollapse t x = 1 := by
  by_cases hx : |x| < t
  · exact Or.inr (Or.inl ((threeCollapse_eq_zero_iff ht).mpr hx))
  · by_cases hx0 : 0 ≤ x
    · exact Or.inr (Or.inr (by simp [threeCollapse, hx, hx0]))
    · exact Or.inl (by simp [threeCollapse, hx, hx0])

theorem threeCollapse_mem {t x : ℝ} (ht : 0 < t) : IsThreeHeight (threeCollapse t x) := by
  rcases threeCollapse_trichotomy ht with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem threeCollapse_neg {t x : ℝ} (ht : 0 < t) :
    threeCollapse t (-x) = -threeCollapse t x := by
  rcases threeCollapse_trichotomy (x := x) ht with hx | hx | hx
  · have hle : x ≤ -t := (threeCollapse_eq_neg_one_iff ht).mp hx
    rw [hx, (threeCollapse_eq_one_iff ht).mpr (by linarith : t ≤ -x)]
    norm_num
  · have hlt : |-x| < t := by simpa [abs_neg] using (threeCollapse_eq_zero_iff ht).mp hx
    rw [hx, (threeCollapse_eq_zero_iff ht).mpr hlt]
    norm_num
  · have hle : t ≤ x := (threeCollapse_eq_one_iff ht).mp hx
    rw [hx, (threeCollapse_eq_neg_one_iff ht).mpr (by linarith : -x ≤ -t)]

theorem threeCollapse_mono {t : ℝ} (ht : 0 < t) {x y : ℝ} (hxy : x ≤ y) :
    threeCollapse t x ≤ threeCollapse t y := by
  rcases threeCollapse_trichotomy (x := x) ht with hx | hx | hx
  · rw [hx]
    rcases threeCollapse_trichotomy (x := y) ht with hy | hy | hy
    · rw [hy]
    · rw [hy]; norm_num
    · rw [hy]; norm_num
  · have hxlt : |x| < t := (threeCollapse_eq_zero_iff ht).mp hx
    have hnot : ¬ y ≤ -t := by
      intro hyt
      have hxle : x ≤ -t := hxy.trans hyt
      have hxabs : t ≤ |x| := by
        have hxneg : x < 0 := lt_of_le_of_lt hxle (neg_neg_of_pos ht)
        rw [abs_of_neg hxneg]
        linarith
      exact not_lt.mpr hxabs hxlt
    rw [hx]
    rcases threeCollapse_trichotomy (x := y) ht with hy | hy | hy
    · exact (hnot ((threeCollapse_eq_neg_one_iff ht).mp hy)).elim
    · rw [hy]
    · rw [hy]; norm_num
  · have htx : t ≤ x := (threeCollapse_eq_one_iff ht).mp hx
    rw [hx, (threeCollapse_eq_one_iff ht).mpr (htx.trans hxy)]

theorem threeCollapse_min {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    threeCollapse t (min x y) = min (threeCollapse t x) (threeCollapse t y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (threeCollapse_mono ht h)]
  · rw [min_eq_right h, min_eq_right (threeCollapse_mono ht h)]

theorem threeCollapse_max {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    threeCollapse t (max x y) = max (threeCollapse t x) (threeCollapse t y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (threeCollapse_mono ht h)]
  · rw [max_eq_left h, max_eq_left (threeCollapse_mono ht h)]

/-- A formula returns one atom or the swap of one atom. -/
theorem eval_eq_literal (φ : Formula) (v : ℕ → ℝ) :
    ∃ n, φ.eval v = v n ∨ φ.eval v = negJ (v n) := by
  induction φ with
  | atom n =>
    exact ⟨n, Or.inl rfl⟩
  | neg ψ ih =>
    rcases ih with ⟨n, hn | hn⟩
    · exact ⟨n, Or.inr (by simp [hn])⟩
    · exact ⟨n, Or.inl (by simp [hn, negJ_involutive])⟩
  | conj ψ χ ihψ ihχ =>
    rcases le_total (ψ.eval v) (χ.eval v) with h | h
    · rcases ihψ with ⟨n, hn⟩
      exact ⟨n, by simpa [Formula.eval, conjJ, min_eq_left h] using hn⟩
    · rcases ihχ with ⟨n, hn⟩
      exact ⟨n, by simpa [Formula.eval, conjJ, min_eq_right h] using hn⟩
  | disj ψ χ ihψ ihχ =>
    rcases le_total (ψ.eval v) (χ.eval v) with h | h
    · rcases ihχ with ⟨n, hn⟩
      exact ⟨n, by simpa [Formula.eval, disjJ, max_eq_right h] using hn⟩
    · rcases ihψ with ⟨n, hn⟩
      exact ⟨n, by simpa [Formula.eval, disjJ, max_eq_left h] using hn⟩

theorem eval_threeCollapse {t : ℝ} (ht : 0 < t) (φ : Formula) (v : ℕ → ℝ) :
    φ.eval (fun n => threeCollapse t (v n)) = threeCollapse t (φ.eval v) := by
  induction φ with
  | atom n => rfl
  | neg ψ ih =>
    simp only [Formula.eval_neg, negJ, ih]
    exact (threeCollapse_neg (x := ψ.eval v) ht).symm
  | conj ψ χ ihψ ihχ =>
    simp only [Formula.eval_conj, conjJ, ihψ, ihχ]
    exact (threeCollapse_min ht (ψ.eval v) (χ.eval v)).symm
  | disj ψ χ ihψ ihχ =>
    simp only [Formula.eval_disj, disjJ, ihψ, ihχ]
    exact (threeCollapse_max ht (ψ.eval v) (χ.eval v)).symm

theorem threeThreshold_pos {a b : ℝ} (hne : a ≠ b) : 0 < max |a| |b| := by
  refine lt_of_le_of_ne (le_max_of_le_left (abs_nonneg a)) ?_
  intro h
  have h0 : max |a| |b| = 0 := h.symm
  have ha : |a| = 0 :=
    le_antisymm (by simpa [h0] using le_max_left |a| |b|) (abs_nonneg a)
  have hb : |b| = 0 :=
    le_antisymm (by simpa [h0] using le_max_right |a| |b|) (abs_nonneg b)
  exact hne ((abs_eq_zero.mp ha).trans (abs_eq_zero.mp hb).symm)

theorem threeCollapse_separates_of_abs_lt {a b : ℝ} (hlt : |a| < |b|) :
    threeCollapse (max |a| |b|) a ≠ threeCollapse (max |a| |b|) b := by
  have ht : 0 < max |a| |b| := threeThreshold_pos (by
    intro h
    rw [h] at hlt
    exact lt_irrefl _ hlt)
  have hmax : max |a| |b| = |b| := max_eq_right hlt.le
  have ha : |a| < max |a| |b| := by simpa [hmax] using hlt
  have hb : ¬ |b| < max |a| |b| := by simp [hmax]
  have hca : threeCollapse (max |a| |b|) a = 0 := (threeCollapse_eq_zero_iff ht).mpr ha
  intro h
  exact hb ((threeCollapse_eq_zero_iff ht).mp (h.symm.trans hca))

theorem threeCollapse_separates {a b : ℝ} (hne : a ≠ b) :
    threeCollapse (max |a| |b|) a ≠ threeCollapse (max |a| |b|) b := by
  have ht : 0 < max |a| |b| := threeThreshold_pos hne
  rcases lt_trichotomy |a| |b| with hlt | heq | hgt
  · exact threeCollapse_separates_of_abs_lt hlt
  · have hsign : a = -b := by
      rcases (abs_eq_abs).mp heq with h | h
      · exact absurd h hne
      · exact h
    have hb : b = -a := neg_eq_iff_eq_neg.mp hsign.symm
    by_cases h0 : 0 ≤ a
    · have hmax : max |a| |b| = a := by
        have ha : |a| = a := abs_of_nonneg h0
        calc
          max |a| |b| = max |a| |a| := by rw [heq]
          _ = |a| := max_self _
          _ = a := ha
      have hca := (threeCollapse_eq_one_iff ht).mpr (le_of_eq hmax)
      have hcb := (threeCollapse_eq_neg_one_iff ht).mpr (by
        rw [hmax, hb] : b ≤ -(max |a| |b|))
      rw [hca, hcb]
      norm_num
    · have hlt_a : a < 0 := lt_of_not_ge h0
      have hmax : max |a| |b| = -a := by
        have ha : |a| = -a := abs_of_neg hlt_a
        calc
          max |a| |b| = max |a| |a| := by rw [heq]
          _ = |a| := max_self _
          _ = -a := ha
      have hca := (threeCollapse_eq_neg_one_iff ht).mpr (by
        rw [hmax]
        linarith : a ≤ -(max |a| |b|))
      have hcb := (threeCollapse_eq_one_iff ht).mpr (by
        rw [hmax, hb] : max |a| |b| ≤ b)
      rw [hca, hcb]
      norm_num
  · have hswap := threeCollapse_separates_of_abs_lt hgt
    simpa [max_comm] using hswap.symm

/-- A real disagreement is already a disagreement on `{-1, 0, 1}`. -/
theorem exists_threeHeight_of_eval_ne {φ ψ : Formula} {v : ℕ → ℝ}
    (hne : φ.eval v ≠ ψ.eval v) :
    ∃ w : ℕ → ℝ, (∀ n, IsThreeHeight (w n)) ∧ φ.eval w ≠ ψ.eval w := by
  let t := max |φ.eval v| |ψ.eval v|
  have ht : 0 < t := threeThreshold_pos hne
  refine ⟨fun n => threeCollapse t (v n), fun n => threeCollapse_mem ht, ?_⟩
  intro h
  have hφ := eval_threeCollapse ht φ v
  have hψ := eval_threeCollapse ht ψ v
  exact threeCollapse_separates hne (hφ.symm.trans (h.trans hψ))

/-- Equational identity on the height is decided by `{-1, 0, 1}`. -/
theorem height_identity_iff_threeHeight (φ ψ : Formula) :
    (∀ v : ℕ → ℝ, φ.eval v = ψ.eval v) ↔
      (∀ v : ℕ → ℝ, (∀ n, IsThreeHeight (v n)) → φ.eval v = ψ.eval v) := by
  constructor
  · intro h v _
    exact h v
  · intro h v
    by_contra hne
    rcases exists_threeHeight_of_eval_ne hne with ⟨w, hw, hneq⟩
    exact hneq (h w hw)

/-- A formula with one hole. Filling it is the rewrite used by an equational step. -/
inductive Ctx
  | hole
  | neg (C : Ctx)
  | conjL (C : Ctx) (χ : Formula)
  | conjR (χ : Formula) (C : Ctx)
  | disjL (C : Ctx) (χ : Formula)
  | disjR (χ : Formula) (C : Ctx)

namespace Ctx

def fill (C : Ctx) (φ : Formula) : Formula :=
  match C with
  | hole => φ
  | neg C => (C.fill φ).neg
  | conjL C χ => (C.fill φ).conj χ
  | conjR χ C => χ.conj (C.fill φ)
  | disjL C χ => (C.fill φ).disj χ
  | disjR χ C => χ.disj (C.fill φ)

/-- A height identity remains an identity inside any surrounding formula. -/
theorem fill_height_identity {φ ψ : Formula}
    (h : ∀ v : ℕ → ℝ, φ.eval v = ψ.eval v) (C : Ctx) (v : ℕ → ℝ) :
    (C.fill φ).eval v = (C.fill ψ).eval v := by
  induction C with
  | hole => simpa [fill] using h v
  | neg C ih =>
    simp only [fill, Formula.eval_neg]
    rw [ih]
  | conjL C χ ih =>
    simp only [fill, Formula.eval_conj]
    rw [ih]
  | conjR χ C ih =>
    simp only [fill, Formula.eval_conj]
    rw [ih]
  | disjL C χ ih =>
    simp only [fill, Formula.eval_disj]
    rw [ih]
  | disjR χ C ih =>
    simp only [fill, Formula.eval_disj]
    rw [ih]

end Ctx

/-- Excluded middle of one atom. -/
def excludedMiddle (n : ℕ) : Formula :=
  (Formula.atom n).disj (Formula.atom n).neg

theorem excludedMiddle_eval (n : ℕ) (v : ℕ → ℝ) :
    (excludedMiddle n).eval v = |v n| := by
  simp [excludedMiddle, disj_neg_eq_abs]

/-- Both excluded middles are classical tautologies: every wall assignment
returns the positive wall. -/
theorem excludedMiddle_on_wall (v : ℕ → ℝ) (hv : ∀ n, IsWallTwo (v n)) :
    (excludedMiddle 0).eval v = 1 ∧ (excludedMiddle 1).eval v = 1 := by
  have habs (n : ℕ) : |v n| = 1 := by
    rcases hv n with h | h <;> simp [h]
  exact ⟨by simp [excludedMiddle_eval, habs 0], by simp [excludedMiddle_eval, habs 1]⟩

/-- The positive wall against balance separates the two excluded middles.
The witness uses only the three heights. -/
theorem excludedMiddle_separated :
    let v : ℕ → ℝ := fun n => if n = 0 then 1 else 0
    (excludedMiddle 0).eval v = 1 ∧
      (excludedMiddle 1).eval v = 0 ∧
        ∀ n, IsThreeHeight (v n) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [excludedMiddle_eval]
  · simp [excludedMiddle_eval]
  · intro n
    by_cases hn : n = 0
    · simp [hn, IsThreeHeight]
    · simp [hn, IsThreeHeight]

theorem excludedMiddle_not_height_identity :
    ¬ ∀ v : ℕ → ℝ, (excludedMiddle 0).eval v = (excludedMiddle 1).eval v := by
  intro h
  have h1 : (excludedMiddle 0).eval (fun n => if n = 0 then 1 else 0) = 1 := by
    simp [excludedMiddle_eval]
  have h0 : (excludedMiddle 1).eval (fun n => if n = 0 then 1 else 0) = 0 := by
    simp [excludedMiddle_eval]
  have heq := h (fun n => if n = 0 then (1 : ℝ) else 0)
  exact zero_ne_one (h0.symm.trans (heq.symm.trans h1))

end Logic

end DstDiophantine
