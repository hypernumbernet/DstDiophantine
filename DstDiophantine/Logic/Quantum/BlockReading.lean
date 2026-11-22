import DstDiophantine.Logic.Quantum.BooleanIsland
import DstDiophantine.Logic.Connective

/-!
# From a Boolean block to the four labels

A classical step in dimension two stays inside one four-element island, and the height order cannot
receive its two atoms. No map sends a formula to a subspace.
-/

namespace DstDiophantine

namespace Logic

open scoped InnerProductSpace
open Submodule Module

theorem orthogonal_ne (A : QProp) : A ≠ Aᗮ := by
  intro h
  have hA : A = ⊥ := by
    have hinf := A.inf_orthogonal_eq_bot
    rwa [← h, inf_idem] at hinf
  have htop : (⊥ : QProp) = ⊤ := by
    have hO : Aᗮ = ⊤ := by
      rw [hA]
      exact Submodule.bot_orthogonal_eq_top
    rw [← hA, h, hO]
  have hdim := congrArg (fun S : QProp => finrank ℂ S) htop
  rw [finrank_bot, finrank_top, dualSpinor_finrank] at hdim
  exact absurd hdim (by decide : ¬ (0 : ℕ) = 2)

theorem bot_ne_top_qprop : (⊥ : QProp) ≠ ⊤ := by
  intro h
  have hdim := congrArg (fun S : QProp => finrank ℂ S) h
  rw [finrank_bot, finrank_top, dualSpinor_finrank] at hdim
  exact absurd hdim (by decide : ¬ (0 : ℕ) = 2)

theorem ray_incomparable {L : QProp} (hL : finrank ℂ L = 1) :
    ¬ L ≤ Lᗮ ∧ ¬ Lᗮ ≤ L := by
  constructor
  · intro hle
    have hbot : L = ⊥ := by
      have hle' : L ≤ L ⊓ Lᗮ := le_inf le_rfl hle
      rw [L.inf_orthogonal_eq_bot] at hle'
      exact le_bot_iff.mp hle'
    exact (bot_ne_of_finrank_one hL) hbot.symm
  · intro hle
    have hbot : Lᗮ = ⊥ := by
      have hle' : Lᗮ ≤ L ⊓ Lᗮ := le_inf hle le_rfl
      rw [L.inf_orthogonal_eq_bot] at hle'
      exact le_bot_iff.mp hle'
    exact (orthogonal_ne_bot_of_line hL) hbot.symm

theorem no_height_order_embedding {L : QProp} (hL : finrank ℂ L = 1) :
    ¬ ∃ φ : QProp → ℝ,
      ∀ A B : QProp, A ∈ Island L → B ∈ Island L → (A ≤ B ↔ φ A ≤ φ B) := by
  intro ⟨φ, hφ⟩
  have hLmem : L ∈ Island L := by simp [Island]
  have hOmem : Lᗮ ∈ Island L := by simp [Island]
  obtain ⟨h1, h2⟩ := ray_incomparable hL
  have n1 : ¬ φ L ≤ φ Lᗮ := by
    intro hle
    exact h1 ((hφ L Lᗮ hLmem hOmem).mpr hle)
  have n2 : ¬ φ Lᗮ ≤ φ L := by
    intro hle
    exact h2 ((hφ Lᗮ L hOmem hLmem).mpr hle)
  rcases le_total (φ L) (φ Lᗮ) with hle | hle
  · exact n1 hle
  · exact n2 hle

theorem distributes_of_splits {A B C : QProp}
    (hB : Compatible A B) (hC : Compatible A C) :
    A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C) := by
  rcases qprop_finrank_trichotomy A with h0 | h1 | h2
  · rw [eq_bot_of_finrank_zero h0, bot_inf_eq, bot_inf_eq, bot_inf_eq, bot_sup_eq]
  · have hAi : A ∈ Island A := by simp [Island]
    have hBi : B ∈ Island A :=
      (compatible_ray_iff_mem_island h1).mp (compatible_right hB)
    have hCi : C ∈ Island A :=
      (compatible_ray_iff_mem_island h1).mp (compatible_right hC)
    exact island_inf_sup_distrib hAi hBi hCi
  · rw [eq_top_of_finrank_two h2, top_inf_eq, top_inf_eq, top_inf_eq]

theorem splits_ray_forces_island {A B C : QProp}
    (hA : finrank ℂ A = 1) (hB : Compatible A B) (hC : Compatible A C) :
    B ∈ Island A ∧ C ∈ Island A ∧ Compatible B C := by
  have hBi : B ∈ Island A :=
    (compatible_ray_iff_mem_island hA).mp (compatible_right hB)
  have hCi : C ∈ Island A :=
    (compatible_ray_iff_mem_island hA).mp (compatible_right hC)
  exact ⟨hBi, hCi, island_compatible hBi hCi⟩

/-- Componentwise negation of the two classical bits. -/
def bitComplement (p : Bool × Bool) : Bool × Bool := (!p.1, !p.2)

theorem bitComplement_involutive (p : Bool × Bool) :
    bitComplement (bitComplement p) = p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

theorem bitComplement_ne (p : Bool × Bool) : bitComplement p ≠ p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> decide

theorem ofBits_orthogonal (L : QProp) (p : Bool × Bool) :
    (ofBits L p)ᗮ = ofBits L (bitComplement p) := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;>
    simp [ofBits, bitComplement, Submodule.bot_orthogonal_eq_top,
      Submodule.top_orthogonal_eq_bot, Submodule.orthogonal_orthogonal]

theorem ofBits_injective {L : QProp} (hL : finrank ℂ L = 1)
    {p q : Bool × Bool} (h : ofBits L p = ofBits L q) : p = q := by
  match p, q with
  | (false, false), (false, false) => rfl
  | (false, false), (false, true) => exact absurd h (orthogonal_ne_bot_of_line hL)
  | (false, false), (true, false) => exact absurd h (bot_ne_of_finrank_one hL)
  | (false, false), (true, true) => exact absurd h bot_ne_top_qprop
  | (false, true), (false, false) => exact absurd h (orthogonal_ne_bot_of_line hL).symm
  | (false, true), (false, true) => rfl
  | (false, true), (true, false) => exact absurd h (line_ne_orthogonal hL).symm
  | (false, true), (true, true) => exact absurd h (orthogonal_ne_top_of_line hL).symm
  | (true, false), (false, false) => exact absurd h (bot_ne_of_finrank_one hL).symm
  | (true, false), (false, true) => exact absurd h (line_ne_orthogonal hL)
  | (true, false), (true, false) => rfl
  | (true, false), (true, true) => exact absurd h (top_ne_of_finrank_one hL).symm
  | (true, true), (false, false) => exact absurd h bot_ne_top_qprop.symm
  | (true, true), (false, true) => exact absurd h (orthogonal_ne_top_of_line hL)
  | (true, true), (true, false) => exact absurd h (top_ne_of_finrank_one hL)
  | (true, true), (true, true) => rfl

private theorem pair_misses_U {x : ℝ} (hx : |x| ≤ 1) (hx1 : |x| = 1) :
    classifyOfMem x hx ≠ .U ∧
      classifyOfMem (-x) (by rw [abs_neg]; exact hx) ≠ .U := by
  constructor
  · intro h
    rw [classifyOfMem_eq_U_iff] at h
    rcases h with ⟨hpos, hlt⟩
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hx1 with h1 | h1
    · linarith
    · linarith
  · intro h
    rw [classifyOfMem_eq_U_iff] at h
    rcases h with ⟨hpos, hlt⟩
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hx1 with h1 | h1
    · linarith
    · linarith

private theorem pair_misses_F {x : ℝ} (hx : |x| ≤ 1) (hx1 : |x| ≠ 1) :
    classifyOfMem x hx ≠ .F ∧
      classifyOfMem (-x) (by rw [abs_neg]; exact hx) ≠ .F := by
  constructor
  · intro h
    have : |x| = 1 := by
      rw [(classifyOfMem_eq_F_iff hx).mp h]
      norm_num
    exact hx1 this
  · intro h
    have hneg : -x = 1 := (classifyOfMem_eq_F_iff _).mp h
    have : |x| = 1 := by
      rw [← abs_neg, hneg]
      norm_num
    exact hx1 this

private theorem ne_zero_misses_T {x : ℝ} (hx : |x| ≤ 1) (hx0 : x ≠ 0) :
    classifyOfMem x hx ≠ .T ∧
      classifyOfMem (-x) (by rw [abs_neg]; exact hx) ≠ .T := by
  constructor
  · intro h
    exact hx0 ((classifyOfMem_eq_T_iff hx).mp h)
  · intro h
    exact hx0 (neg_eq_zero.mp ((classifyOfMem_eq_T_iff _).mp h))

private theorem zero_class_T {hx : |(0 : ℝ)| ≤ 1} :
    classifyOfMem (0 : ℝ) hx = .T :=
  (classifyOfMem_eq_T_iff hx).mpr rfl

theorem two_negation_pairs_miss_label {z a : ℝ} (hz : |z| ≤ 1) (ha : |a| ≤ 1) :
    ∃ tv : TruthValue,
      classifyOfMem z hz ≠ tv ∧
        classifyOfMem (-z) (by rw [abs_neg]; exact hz) ≠ tv ∧
          classifyOfMem a ha ≠ tv ∧
            classifyOfMem (-a) (by rw [abs_neg]; exact ha) ≠ tv := by
  by_cases hz0 : z = 0
  · have hzT : classifyOfMem z hz = .T :=
      (classifyOfMem_eq_of_eq hz0 hz (by norm_num : |(0 : ℝ)| ≤ 1)).trans zero_class_T
    have hzT' : classifyOfMem (-z) (by rw [abs_neg]; exact hz) = .T :=
      (classifyOfMem_eq_of_eq (neg_eq_zero.mpr hz0) (by rw [abs_neg]; exact hz)
        (by norm_num : |(0 : ℝ)| ≤ 1)).trans zero_class_T
    by_cases ha1 : |a| = 1
    · refine ⟨.U, ?_, ?_, ?_, ?_⟩
      · rw [hzT]; decide
      · rw [hzT']; decide
      · exact (pair_misses_U ha ha1).1
      · exact (pair_misses_U ha ha1).2
    · refine ⟨.F, ?_, ?_, ?_, ?_⟩
      · rw [hzT]; decide
      · rw [hzT']; decide
      · exact (pair_misses_F ha ha1).1
      · exact (pair_misses_F ha ha1).2
  · by_cases ha0 : a = 0
    · have haT : classifyOfMem a ha = .T :=
        (classifyOfMem_eq_of_eq ha0 ha (by norm_num : |(0 : ℝ)| ≤ 1)).trans zero_class_T
      have haT' : classifyOfMem (-a) (by rw [abs_neg]; exact ha) = .T :=
        (classifyOfMem_eq_of_eq (neg_eq_zero.mpr ha0) (by rw [abs_neg]; exact ha)
          (by norm_num : |(0 : ℝ)| ≤ 1)).trans zero_class_T
      by_cases hz1 : |z| = 1
      · refine ⟨.U, ?_, ?_, ?_, ?_⟩
        · exact (pair_misses_U hz hz1).1
        · exact (pair_misses_U hz hz1).2
        · rw [haT]; decide
        · rw [haT']; decide
      · refine ⟨.F, ?_, ?_, ?_, ?_⟩
        · exact (pair_misses_F hz hz1).1
        · exact (pair_misses_F hz hz1).2
        · rw [haT]; decide
        · rw [haT']; decide
    · refine ⟨.T, ?_, ?_, ?_, ?_⟩
      · exact (ne_zero_misses_T hz hz0).1
      · exact (ne_zero_misses_T hz hz0).2
      · exact (ne_zero_misses_T ha ha0).1
      · exact (ne_zero_misses_T ha ha0).2

theorem no_sign_flip_realizes_four_labels :
    ¬ ∃ (φ : Bool × Bool → ℝ) (_hφ : ∀ p, |φ p| ≤ 1),
      (∀ p, φ (bitComplement p) = - φ p) ∧
        ∀ tv : TruthValue, ∃ p, classifyOfMem (φ p) (_hφ p) = tv := by
  intro ⟨φ, hφ, hneg, htv⟩
  have hzφ : |φ (false, false)| ≤ 1 := hφ _
  have haφ : |φ (true, false)| ≤ 1 := hφ _
  obtain ⟨tv, h1, h2, h3, h4⟩ := two_negation_pairs_miss_label hzφ haφ
  obtain ⟨p, hp⟩ := htv tv
  rcases p with ⟨b1, b2⟩
  cases b1 <;> cases b2
  · have heq := classifyOfMem_eq_of_eq
      (rfl : φ (false, false) = φ (false, false)) (hφ _) hzφ
    exact h1 (heq.symm.trans hp)
  · have hq : φ (false, true) = - φ (true, false) := by
      simpa [bitComplement] using hneg (true, false)
    have heq := classifyOfMem_eq_of_eq hq (hφ _) (by rw [abs_neg]; exact haφ)
    exact h4 (heq.symm.trans hp)
  · have heq := classifyOfMem_eq_of_eq
      (rfl : φ (true, false) = φ (true, false)) (hφ _) haφ
    exact h3 (heq.symm.trans hp)
  · have hq : φ (true, true) = - φ (false, false) := by
      simpa [bitComplement] using hneg (false, false)
    have heq := classifyOfMem_eq_of_eq hq (hφ _) (by rw [abs_neg]; exact hzφ)
    exact h2 (heq.symm.trans hp)

theorem meet_orthogonal_bot (A : QProp) : A ⊓ Aᗮ = ⊥ :=
  A.inf_orthogonal_eq_bot

theorem height_meet_neg_eq_zero_iff (j : ℝ) :
    conjJ j (negJ j) = 0 ↔ j = 0 := by
  rw [conj_neg_eq_neg_abs, neg_eq_zero, abs_eq_zero]

/-!
## Classical rules on an island

The four positive-wall rules, read on the two bits, are the classical ones. The reading does not
send a formula to a subspace.
-/

theorem ofBits_material (L : QProp) (p q : Bool × Bool) :
    material (ofBits L p) (ofBits L q) =
      ofBits L (!p.1 || q.1, !p.2 || q.2) := by
  rw [material, ofBits_orthogonal, ofBits_sup]
  rfl

theorem ofBits_eq_top_iff {L : QProp} (hL : finrank ℂ L = 1) {p : Bool × Bool} :
    ofBits L p = ⊤ ↔ p = (true, true) := by
  constructor
  · intro h
    exact ofBits_injective hL (h.trans (by simp [ofBits]))
  · rintro rfl
    rfl

theorem ofBits_eq_bot_iff {L : QProp} (hL : finrank ℂ L = 1) {p : Bool × Bool} :
    ofBits L p = ⊥ ↔ p = (false, false) := by
  constructor
  · intro h
    exact ofBits_injective hL (h.trans (by simp [ofBits]))
  · rintro rfl
    rfl

private theorem bool_chain (a b c : Bool)
    (hab : (!a || b) = true) (hbc : (!b || c) = true) : (!a || c) = true := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem island_modus_ponens {L : QProp} (hL : finrank ℂ L = 1) {p q : Bool × Bool}
    (hp : ofBits L p = ⊤) (hi : material (ofBits L p) (ofBits L q) = ⊤) :
    ofBits L q = ⊤ := by
  have hp' : p = (true, true) := (ofBits_eq_top_iff hL).mp hp
  have hbits : (!p.1 || q.1, !p.2 || q.2) = (true, true) :=
    (ofBits_eq_top_iff hL).mp (by rw [← ofBits_material]; exact hi)
  rcases hp' with rfl
  have hq : q = (true, true) := by
    simpa using hbits
  exact (ofBits_eq_top_iff hL).mpr hq

theorem island_tollens {L : QProp} (hL : finrank ℂ L = 1) {p q : Bool × Bool}
    (hi : material (ofBits L p) (ofBits L q) = ⊤) (hq : ofBits L q = ⊥) :
    ofBits L p = ⊥ := by
  have hq' : q = (false, false) := (ofBits_eq_bot_iff hL).mp hq
  have hbits : (!p.1 || q.1, !p.2 || q.2) = (true, true) :=
    (ofBits_eq_top_iff hL).mp (by rw [← ofBits_material]; exact hi)
  rcases hq' with rfl
  have hp : p = (false, false) := by
    cases p with
    | mk a b =>
      cases a <;> cases b <;> simp_all
  exact (ofBits_eq_bot_iff hL).mpr hp

theorem island_disjunctive {L : QProp} (hL : finrank ℂ L = 1) {p q : Bool × Bool}
    (h : ofBits L p ⊔ ofBits L q = ⊤) (hp : ofBits L p = ⊥) :
    ofBits L q = ⊤ := by
  have hp' : p = (false, false) := (ofBits_eq_bot_iff hL).mp hp
  have hbits : (p.1 || q.1, p.2 || q.2) = (true, true) :=
    (ofBits_eq_top_iff hL).mp (by rw [← ofBits_sup]; exact h)
  rcases hp' with rfl
  have hq : q = (true, true) := by
    simpa using hbits
  exact (ofBits_eq_top_iff hL).mpr hq

theorem island_chain {L : QProp} (hL : finrank ℂ L = 1) {p q r : Bool × Bool}
    (hq : material (ofBits L p) (ofBits L q) = ⊤)
    (hr : material (ofBits L q) (ofBits L r) = ⊤) :
    material (ofBits L p) (ofBits L r) = ⊤ := by
  have hqbits : (!p.1 || q.1, !p.2 || q.2) = (true, true) :=
    (ofBits_eq_top_iff hL).mp (by rw [← ofBits_material]; exact hq)
  have hrbits : (!q.1 || r.1, !q.2 || r.2) = (true, true) :=
    (ofBits_eq_top_iff hL).mp (by rw [← ofBits_material]; exact hr)
  rw [ofBits_material]
  have hpair : (!p.1 || r.1, !p.2 || r.2) = (true, true) :=
    Prod.ext
      (bool_chain p.1 q.1 r.1 (congrArg Prod.fst hqbits) (congrArg Prod.fst hrbits))
      (bool_chain p.2 q.2 r.2 (congrArg Prod.snd hqbits) (congrArg Prod.snd hrbits))
  rw [hpair]
  rfl

end Logic

end DstDiophantine
