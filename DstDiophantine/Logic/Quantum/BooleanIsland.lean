import DstDiophantine.Logic.Quantum.Sasaki
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith

/-!
# Boolean islands in the spinor lattice

A ray splits along another ray exactly when the two are equal or orthogonal.
A subspace splits along a ray exactly when it lies in the four-element island
`{⊥, ℓ, ℓ⊥, ⊤}` of that ray, and splitting along the ray already splits along
the orthogonal ray. The island is closed under meet, join, and orthocomplement;
meet distributes over join; and the lattice implication agrees with the
classical expansion throughout the island. The expansion detaches exactly
on pairs where the two implications agree, hence on the island, and it
does not detach on a basis ray against the diagonal. Distinct complementary pairs
determine islands that meet only at `{⊥, ⊤}`. The only subspaces that split
along every subspace are `⊥` and `⊤`.
-/

namespace DstDiophantine

namespace Logic

open scoped InnerProductSpace
open Submodule Module

private theorem finrank_top_qprop : finrank ℂ (⊤ : QProp) = 2 := by
  rw [finrank_top]
  exact dualSpinor_finrank

theorem qprop_finrank_le_two (A : QProp) : finrank ℂ A ≤ 2 := by
  simpa [dualSpinor_finrank] using Submodule.finrank_le A

theorem qprop_finrank_trichotomy (A : QProp) :
    finrank ℂ A = 0 ∨ finrank ℂ A = 1 ∨ finrank ℂ A = 2 := by
  have hle := qprop_finrank_le_two A
  omega

theorem eq_bot_of_finrank_zero {A : QProp} (h : finrank ℂ A = 0) : A = ⊥ :=
  Submodule.finrank_eq_zero.mp h

theorem eq_top_of_finrank_two {A : QProp} (h : finrank ℂ A = 2) : A = ⊤ :=
  eq_of_le_of_finrank_eq le_top (by rw [h, finrank_top_qprop])

theorem finrank_orthogonal_line {A : QProp} (hA : finrank ℂ A = 1) :
    finrank ℂ Aᗮ = 1 := by
  have h := A.finrank_add_finrank_orthogonal
  rw [hA, dualSpinor_finrank] at h
  omega

theorem bot_ne_of_finrank_one {A : QProp} (hA : finrank ℂ A = 1) : ⊥ ≠ A := by
  intro h
  have : finrank ℂ A = 0 := by rw [← h, finrank_bot]
  rw [hA] at this
  exact absurd this (by decide)

theorem top_ne_of_finrank_one {A : QProp} (hA : finrank ℂ A = 1) : ⊤ ≠ A := by
  intro h
  have : finrank ℂ A = 2 := by rw [← h, finrank_top_qprop]
  rw [hA] at this
  exact absurd this (by decide)

theorem inf_bot_of_lines_ne {A B : QProp}
    (hA : finrank ℂ A = 1) (hB : finrank ℂ B = 1) (hne : A ≠ B) :
    A ⊓ B = ⊥ := by
  by_contra hneBot
  have hpos : finrank ℂ (A ⊓ B : QProp) ≠ 0 := by
    intro h0
    exact hneBot (eq_bot_of_finrank_zero h0)
  have hle : finrank ℂ (A ⊓ B : QProp) ≤ 1 := by
    have hmono := Submodule.finrank_mono (inf_le_left : A ⊓ B ≤ A)
    simpa [hA] using hmono
  have hrank : finrank ℂ (A ⊓ B : QProp) = 1 :=
    (Nat.le_one_iff_eq_zero_or_eq_one.mp hle).resolve_left hpos
  have hAeq : A ⊓ B = A :=
    eq_of_le_of_finrank_eq inf_le_left (hrank.trans hA.symm)
  have hBeq : A ⊓ B = B :=
    eq_of_le_of_finrank_eq inf_le_right (hrank.trans hB.symm)
  exact hne (hAeq.symm.trans hBeq)

theorem exists_span_singleton_line {A : QProp} (hA : finrank ℂ A = 1) :
    ∃ v : DualSpinor, v ≠ 0 ∧ A = ℂ ∙ v := by
  have hne : A ≠ ⊥ := (bot_ne_of_finrank_one hA).symm
  have hex : ∃ v : DualSpinor, v ∈ A ∧ v ≠ 0 := by
    by_contra h
    apply hne
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  obtain ⟨v, hvA, hv0⟩ := hex
  refine ⟨v, hv0, ?_⟩
  have hle : ℂ ∙ v ≤ A := (span_singleton_le_iff_mem v A).mpr hvA
  have hdim : finrank ℂ (ℂ ∙ v) = finrank ℂ A := by
    rw [finrank_span_singleton hv0, hA]
  exact (eq_of_le_of_finrank_eq hle hdim).symm

theorem dualSpinor_coords (v : DualSpinor) : v = v 0 • e0 + v 1 • e1 := by
  ext i
  fin_cases i <;> simp [e0, e1, PiLp.add_apply, PiLp.smul_apply]

theorem span_singleton_smul_eq {c : ℂ} {v : DualSpinor} (hc : c ≠ 0) :
    (ℂ ∙ (c • v)) = ℂ ∙ v := by
  apply le_antisymm
  · rw [span_singleton_le_iff_mem]
    exact smul_mem _ c (mem_span_singleton_self v)
  · rw [span_singleton_le_iff_mem, mem_span_singleton]
    refine ⟨c⁻¹, ?_⟩
    rw [← mul_smul, inv_mul_cancel₀ hc, one_smul]

theorem lineOf_zero : lineOf 0 = lineE0 := by
  simp [lineOf, lineE0, zero_smul, add_zero]

theorem line_eq_lineE1_or_lineOf {A : QProp} (hA : finrank ℂ A = 1) :
    A = lineE1 ∨ ∃ z : ℂ, A = lineOf z := by
  obtain ⟨v, hv0, rfl⟩ := exists_span_singleton_line hA
  generalize ha : v 0 = a
  generalize hb : v 1 = b
  have hv : v = a • e0 + b • e1 := by
    rw [← ha, ← hb]
    exact dualSpinor_coords v
  by_cases h0 : a = 0
  · left
    have hv' : v = b • e1 := by
      rw [hv, h0, zero_smul, zero_add]
    have hb0 : b ≠ 0 := by
      intro hb0
      apply hv0
      rw [hv, h0, hb0, zero_smul, zero_smul, add_zero]
    rw [hv', span_singleton_smul_eq hb0]
    rfl
  · right
    refine ⟨b / a, ?_⟩
    have hv' : v = a • (e0 + (b / a) • e1) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ h0]
      exact hv
    rw [hv', span_singleton_smul_eq h0]
    rfl

theorem compatible_refl (A : QProp) : Compatible A A := by
  rw [Compatible, inf_idem, A.inf_orthogonal_eq_bot, sup_bot_eq]

theorem compatible_bot (B : QProp) : Compatible ⊥ B := by
  rw [Compatible, bot_inf_eq, bot_inf_eq, bot_sup_eq]

theorem compatible_top (B : QProp) : Compatible ⊤ B := by
  rw [Compatible, top_inf_eq, top_inf_eq]
  exact B.sup_orthogonal_of_hasOrthogonalProjection.symm

theorem compatible_orthogonal (A : QProp) : Compatible A Aᗮ := by
  rw [Compatible, A.inf_orthogonal_eq_bot, orthogonal_orthogonal, inf_idem, bot_sup_eq]

/-- A ray splits along another ray exactly when the two are equal or orthogonal. -/
theorem compatible_line_iff {A B : QProp}
    (hA : finrank ℂ A = 1) (hB : finrank ℂ B = 1) :
    Compatible A B ↔ A = B ∨ A ⟂ B := by
  constructor
  · intro h
    by_cases hAB : A = B
    · exact Or.inl hAB
    · right
      have hbot : A ⊓ B = ⊥ := inf_bot_of_lines_ne hA hB hAB
      have hsplit : A = A ⊓ Bᗮ := by
        simpa [Compatible, hbot, bot_sup_eq] using h
      exact (isOrtho_iff_le).mpr (by rw [hsplit]; exact inf_le_right)
  · rintro (rfl | hortho)
    · exact compatible_refl A
    · have hle : A ≤ Bᗮ := (isOrtho_iff_le).mp hortho
      have hAeq : A = Bᗮ :=
        eq_of_le_of_finrank_eq hle (hA.trans (finrank_orthogonal_line hB).symm)
      rw [hAeq]
      simpa using compatible_orthogonal Bᗮ

/-- Three distinct rays are never pairwise splitting. -/
theorem no_three_pairwise_compatible_lines {A B C : QProp}
    (hA : finrank ℂ A = 1) (hB : finrank ℂ B = 1) (hC : finrank ℂ C = 1)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hABc : Compatible A B) (hACc : Compatible A C) (hBCc : Compatible B C) : False := by
  have hABo : A ⟂ B := ((compatible_line_iff hA hB).mp hABc).resolve_left hAB
  have hACo : A ⟂ C := ((compatible_line_iff hA hC).mp hACc).resolve_left hAC
  have hBCo : B ⟂ C := ((compatible_line_iff hB hC).mp hBCc).resolve_left hBC
  exact no_three_pairwise_orthogonal_lines hA hB hC hABo hACo hBCo

/-- The island of a ray: the four subspaces of one complementary pair. -/
def Island (L : QProp) : Set QProp := {⊥, L, Lᗮ, ⊤}

theorem mem_island_iff {L A : QProp} :
    A ∈ Island L ↔ A = ⊥ ∨ A = L ∨ A = Lᗮ ∨ A = ⊤ := by
  simp [Island, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem island_orthogonal_mem {L A : QProp} (hA : A ∈ Island L) : Aᗮ ∈ Island L := by
  rcases mem_island_iff.mp hA with h | h | h | h <;>
    simp [Island, h, bot_orthogonal_eq_top, top_orthogonal_eq_bot, orthogonal_orthogonal]

theorem line_ne_orthogonal {L : QProp} (hL : finrank ℂ L = 1) : L ≠ Lᗮ := by
  intro h
  have hinf := L.inf_orthogonal_eq_bot
  rw [← h, inf_idem] at hinf
  exact (bot_ne_of_finrank_one hL) hinf.symm

theorem orthogonal_ne_bot_of_line {L : QProp} (hL : finrank ℂ L = 1) : ⊥ ≠ Lᗮ :=
  bot_ne_of_finrank_one (finrank_orthogonal_line hL)

theorem orthogonal_ne_top_of_line {L : QProp} (hL : finrank ℂ L = 1) : ⊤ ≠ Lᗮ :=
  top_ne_of_finrank_one (finrank_orthogonal_line hL)

/-- Bits of the four-element Boolean algebra, read in the island of `L`. -/
noncomputable def ofBits (L : QProp) : Bool × Bool → QProp
  | (false, false) => ⊥
  | (true, false) => L
  | (false, true) => Lᗮ
  | (true, true) => ⊤

theorem exists_ofBits {L A : QProp} (hA : A ∈ Island L) :
    ∃ p : Bool × Bool, ofBits L p = A := by
  rcases mem_island_iff.mp hA with h | h | h | h
  · exact ⟨(false, false), h.symm⟩
  · exact ⟨(true, false), h.symm⟩
  · exact ⟨(false, true), h.symm⟩
  · exact ⟨(true, true), h.symm⟩

theorem ofBits_mem (L : QProp) (p : Bool × Bool) : ofBits L p ∈ Island L := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> simp [ofBits, Island]

private theorem ofBits_table {L : QProp} (p q : Bool × Bool) :
    ofBits L p ⊓ ofBits L q = ofBits L (p.1 && q.1, p.2 && q.2) ∧
      ofBits L p ⊔ ofBits L q = ofBits L (p.1 || q.1, p.2 || q.2) := by
  have hmeet : L ⊓ Lᗮ = ⊥ := L.inf_orthogonal_eq_bot
  have hmeet' : Lᗮ ⊓ L = ⊥ := by rw [inf_comm, hmeet]
  have hjoin : L ⊔ Lᗮ = ⊤ := L.sup_orthogonal_of_hasOrthogonalProjection
  have hjoin' : Lᗮ ⊔ L = ⊤ := by rw [sup_comm, hjoin]
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;>
    simp [ofBits, hmeet, hmeet', hjoin, hjoin']

theorem ofBits_inf {L : QProp} (p q : Bool × Bool) :
    ofBits L p ⊓ ofBits L q = ofBits L (p.1 && q.1, p.2 && q.2) :=
  (ofBits_table p q).1

theorem ofBits_sup {L : QProp} (p q : Bool × Bool) :
    ofBits L p ⊔ ofBits L q = ofBits L (p.1 || q.1, p.2 || q.2) :=
  (ofBits_table p q).2

theorem ofBits_inf_sup_distrib {L : QProp} (p q r : Bool × Bool) :
    ofBits L p ⊓ (ofBits L q ⊔ ofBits L r) =
      (ofBits L p ⊓ ofBits L q) ⊔ (ofBits L p ⊓ ofBits L r) := by
  rw [ofBits_sup, ofBits_inf, ofBits_inf, ofBits_inf, ofBits_sup]
  apply congrArg (ofBits L)
  apply Prod.ext
  · cases p.1 <;> cases q.1 <;> cases r.1 <;> rfl
  · cases p.2 <;> cases q.2 <;> cases r.2 <;> rfl

theorem island_inf_mem {L A B : QProp} (hA : A ∈ Island L) (hB : B ∈ Island L) :
    A ⊓ B ∈ Island L := by
  obtain ⟨p, rfl⟩ := exists_ofBits hA
  obtain ⟨q, rfl⟩ := exists_ofBits hB
  rw [ofBits_inf]
  exact ofBits_mem L _

theorem island_sup_mem {L A B : QProp} (hA : A ∈ Island L) (hB : B ∈ Island L) :
    A ⊔ B ∈ Island L := by
  obtain ⟨p, rfl⟩ := exists_ofBits hA
  obtain ⟨q, rfl⟩ := exists_ofBits hB
  rw [ofBits_sup]
  exact ofBits_mem L _

/-- On the island, meet distributes over join. -/
theorem island_inf_sup_distrib {L A B C : QProp}
    (hA : A ∈ Island L) (hB : B ∈ Island L) (hC : C ∈ Island L) :
    A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C) := by
  obtain ⟨p, rfl⟩ := exists_ofBits hA
  obtain ⟨q, rfl⟩ := exists_ofBits hB
  obtain ⟨r, rfl⟩ := exists_ofBits hC
  exact ofBits_inf_sup_distrib p q r

theorem island_compatible {L A B : QProp}
    (hA : A ∈ Island L) (hB : B ∈ Island L) : Compatible A B := by
  rcases mem_island_iff.mp hA with hA | hA | hA | hA <;>
    rcases mem_island_iff.mp hB with hB | hB | hB | hB <;>
    simp only [hA, hB] <;>
    first
      | exact compatible_bot _
      | exact compatible_top _
      | exact compatible_refl _
      | exact compatible_orthogonal _
      | exact compatible_right (compatible_orthogonal _)
      | exact compatible_right (compatible_bot _)
      | exact compatible_right (compatible_top _)

/-- Throughout an island the two implications agree. -/
theorem island_implications_agree {L A B : QProp}
    (hA : A ∈ Island L) (hB : B ∈ Island L) :
    sasaki A B = material A B :=
  compatible_iff_sasaki_eq_material.mp (island_compatible hA hB)

/-- The classical expansion detaches exactly on pairs whose two implications
already agree. This is not a map from formulas into the lattice. -/
theorem expansion_detaches_iff_agree {A B : QProp} :
    A ⊓ material A B ≤ B ↔ sasaki A B = material A B := by
  rw [material_detach_iff_compatible, compatible_iff_sasaki_eq_material]

/-- On an island the expansion detaches, because the two implications agree. -/
theorem island_expansion_detaches {L A B : QProp}
    (hA : A ∈ Island L) (hB : B ∈ Island L) :
    A ⊓ material A B ≤ B :=
  expansion_detaches_iff_agree.mpr (island_implications_agree hA hB)

/-- On a basis ray and the diagonal the expansion does not detach. -/
theorem diagonal_expansion_does_not_detach :
    ¬ (lineE0 ⊓ material lineE0 lineD ≤ lineD) := by
  intro h
  exact diagonal_not_compatible (material_detach_iff_compatible.mp h)

/-- A subspace splits along a ray exactly when it lies in that ray's island.
Splitting along the ray already splits along the orthogonal ray. -/
theorem compatible_ray_iff_mem_island {L A : QProp} (hL : finrank ℂ L = 1) :
    Compatible A L ↔ A ∈ Island L := by
  constructor
  · intro hLc
    rcases qprop_finrank_trichotomy A with h0 | h1 | h2
    · rw [eq_bot_of_finrank_zero h0]
      simp [Island]
    · rcases (compatible_line_iff h1 hL).mp hLc with rfl | hortho
      · simp [Island]
      · have hAeq : A = Lᗮ :=
          eq_of_le_of_finrank_eq ((isOrtho_iff_le).mp hortho)
            (h1.trans (finrank_orthogonal_line hL).symm)
        simp [Island, hAeq]
    · rw [eq_top_of_finrank_two h2]
      simp [Island]
  · intro hA
    have hLmem : L ∈ Island L := by simp [Island]
    exact island_compatible hA hLmem

theorem splits_along_pair_iff {L A : QProp} (hL : finrank ℂ L = 1) :
    (Compatible A L ∧ Compatible A Lᗮ) ↔ A ∈ Island L := by
  constructor
  · intro h
    exact (compatible_ray_iff_mem_island hL).mp h.1
  · intro hA
    have hLmem : L ∈ Island L := by simp [Island]
    have hOmem : Lᗮ ∈ Island L := by simp [Island]
    exact ⟨island_compatible hA hLmem, island_compatible hA hOmem⟩

theorem island_inter_trivial {L M : QProp}
    (hL : finrank ℂ L = 1) (_hM : finrank ℂ M = 1)
    (hne : L ≠ M) (hneO : L ≠ Mᗮ) :
    Island L ∩ Island M = ({⊥, ⊤} : Set QProp) := by
  ext A
  constructor
  · intro h
    rcases mem_island_iff.mp h.1 with hA | hA | hA | hA
    · simp [hA]
    · have hmem : L ∈ Island M := by simpa [hA] using h.2
      rcases mem_island_iff.mp hmem with h1 | h1 | h1 | h1
      · exact absurd h1.symm (bot_ne_of_finrank_one hL)
      · exact absurd h1 hne
      · exact absurd h1 hneO
      · exact absurd h1.symm (top_ne_of_finrank_one hL)
    · have hmem : Lᗮ ∈ Island M := by simpa [hA] using h.2
      rcases mem_island_iff.mp hmem with h1 | h1 | h1 | h1
      · exact absurd h1.symm (orthogonal_ne_bot_of_line hL)
      · have hLM : L = Mᗮ := by
          rw [← orthogonal_orthogonal (K := L), h1]
        exact absurd hLM hneO
      · have hLM : L = M := by
          rw [← orthogonal_orthogonal (K := L), h1, orthogonal_orthogonal]
        exact absurd hLM hne
      · exact absurd h1.symm (orthogonal_ne_top_of_line hL)
    · simp [hA]
  · intro h
    have hbot : A = ⊥ ∨ A = ⊤ := by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    rcases hbot with rfl | rfl <;> simp [Island]

theorem inner_lineOf_e0 (z : ℂ) : inner ℂ (e0 + z • e1) e0 = 1 := by
  rw [inner_add_left, inner_smul_left]
  simp [e0, e1, EuclideanSpace.inner_single_left]

theorem lineOf_not_ortho_lineE0 (z : ℂ) : ¬ lineOf z ⟂ lineE0 := by
  intro h
  have h0 := h.inner_eq (mem_span_singleton_self _) (mem_span_singleton_self _)
  rw [inner_lineOf_e0] at h0
  exact one_ne_zero h0

theorem inner_e1_d01 : inner ℂ e1 d01 = 1 := by
  simp [e0, e1, d01, EuclideanSpace.inner_single_left, PiLp.add_apply]

theorem lineE1_ne_lineD : lineE1 ≠ lineD := by
  intro h
  have hbot : lineD = ⊥ := by
    have hinf := lineE1_inf_lineD
    rw [h, inf_idem] at hinf
    exact hinf
  have : finrank ℂ lineD = 0 := by rw [hbot, finrank_bot]
  rw [lineD_finrank] at this
  exact absurd this (by decide)

theorem lineE1_not_ortho_lineD : ¬ lineE1 ⟂ lineD := by
  intro h
  have h0 := h.inner_eq (mem_span_singleton_self _) (mem_span_singleton_self _)
  rw [inner_e1_d01] at h0
  exact one_ne_zero h0

/-- A subspace splits along every subspace exactly when it is `⊥` or `⊤`. -/
theorem compatible_all_iff {A : QProp} :
    (∀ B : QProp, Compatible A B) ↔ A = ⊥ ∨ A = ⊤ := by
  constructor
  · intro h
    rcases qprop_finrank_trichotomy A with h0 | h1 | h2
    · exact Or.inl (eq_bot_of_finrank_zero h0)
    · exfalso
      rcases line_eq_lineE1_or_lineOf h1 with rfl | ⟨z, rfl⟩
      · have hc := (compatible_line_iff lineE1_finrank lineD_finrank).mp (h lineD)
        rcases hc with hEq | hortho
        · exact lineE1_ne_lineD hEq
        · exact lineE1_not_ortho_lineD hortho
      · by_cases hz : z = 0
        · subst hz
          exact diagonal_not_compatible (by simpa [lineOf_zero] using h lineD)
        · have hc := (compatible_line_iff (lineOf_finrank z) lineE0_finrank).mp (h lineE0)
          rcases hc with hEq | hortho
          · exact hz (lineOf_injective (hEq.trans lineOf_zero.symm))
          · exact lineOf_not_ortho_lineE0 z hortho
    · exact Or.inr (eq_top_of_finrank_two h2)
  · rintro (rfl | rfl) B
    · exact compatible_bot B
    · exact compatible_top B

end Logic

end DstDiophantine
