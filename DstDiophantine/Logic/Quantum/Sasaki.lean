import DstDiophantine.Logic.Quantum.QuantumLogic
import Mathlib.Order.ModularLattice
import Mathlib.Tactic.Linarith

/-!
# Boolean blocks inside the spinor lattice

The implication carried by the orthomodular law is
`A → B = A⊥ ∨ (A ∧ B)`. It equals the whole space exactly when `A ≤ B`,
so an inclusion is one identity and does not need a distributive expansion.

That implication agrees with the classical expansion `A⊥ ∨ B` exactly when
`A` decomposes as `(A ∧ B) ∨ (A ∧ B⊥)`. Orthogonal computational rays are
compatible, and the two implications agree. A computational ray and the
diagonal are not: the classical expansion returns the whole space, and the
native implication returns only the orthogonal line.
-/

namespace DstDiophantine

namespace Logic

open scoped InnerProductSpace
open Submodule Module

/-- Implication native to the orthomodular lattice. -/
noncomputable def sasaki (A B : QProp) : QProp :=
  Aᗮ ⊔ A ⊓ B

/-- Classical expansion of an implication. -/
noncomputable def material (A B : QProp) : QProp :=
  Aᗮ ⊔ B

/-- `A` lies in a Boolean block with `B` when it splits along `B`. -/
def Compatible (A B : QProp) : Prop :=
  A = (A ⊓ B) ⊔ (A ⊓ Bᗮ)

theorem sasaki_le_material (A B : QProp) : sasaki A B ≤ material A B :=
  sup_le_sup le_rfl inf_le_right

/-- The native implication is the whole space exactly on the subspace order. -/
theorem sasaki_eq_top_iff {A B : QProp} : sasaki A B = ⊤ ↔ A ≤ B := by
  constructor
  · intro h
    have hC : A ⊓ B ≤ A := inf_le_left
    have hmod := sup_inf_assoc_of_le Aᗮ hC
    have hbot : Aᗮ ⊓ A = ⊥ := by
      rw [inf_comm]
      exact A.inf_orthogonal_eq_bot
    have hlhs : ((A ⊓ B) ⊔ Aᗮ) ⊓ A = A ⊓ B := by
      simpa [hbot, sup_bot_eq] using hmod
    have hEq : A = A ⊓ B := by
      have : sasaki A B ⊓ A = A ⊓ B := by
        simpa [sasaki, sup_comm] using hlhs
      simpa [h, top_inf_eq] using this
    exact (le_of_eq hEq).trans inf_le_right
  · intro h
    have hAB : A ⊓ B = A := inf_eq_left.mpr h
    rw [sasaki, hAB, sup_comm]
    exact sup_orthogonal_of_hasOrthogonalProjection

/-- The zero subspace implies every subspace. No nonzero vector sits in it. -/
theorem sasaki_bot (B : QProp) : sasaki ⊥ B = ⊤ := by
  rw [sasaki, Submodule.bot_orthogonal_eq_top, bot_inf_eq, top_sup_eq]

theorem compatible_right {A B : QProp} (h : Compatible A B) : Compatible B A := by
  rw [Compatible]
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro v hv
  let w := A.starProjection v
  have hwA : w ∈ A := A.starProjection_apply_mem v
  have hwSplit : w ∈ (A ⊓ B) ⊔ (A ⊓ Bᗮ) := by
    rw [← h]
    exact hwA
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_sup.mp hwSplit
  have hyv : inner ℂ y v = 0 := inner_left_of_mem_orthogonal hv hy.2
  have hyvw : inner ℂ y (v - w) = 0 :=
    inner_right_of_mem_orthogonal hy.1 (A.sub_starProjection_mem_orthogonal v)
  have hyw : inner ℂ y w = inner ℂ y y := by
    rw [← hxy, inner_add_right]
    have hyx : inner ℂ y x = 0 := inner_left_of_mem_orthogonal hx.2 hy.2
    rw [hyx, zero_add]
  have hyy : inner ℂ y y = 0 := by
    have hvsum : inner ℂ y v = inner ℂ y (v - w) + inner ℂ y w := by
      calc
        inner ℂ y v = inner ℂ y ((v - w) + w) := by
          congr 1
          exact (sub_add_cancel v w).symm
        _ = inner ℂ y (v - w) + inner ℂ y w := inner_add_right y (v - w) w
    rw [hyv, hyvw, hyw, zero_add] at hvsum
    exact hvsum.symm
  have hy0 : y = 0 := inner_self_eq_zero.mp hyy
  have hw : w = x := by
    rw [← hxy, hy0, add_zero]
  have hwB : w ∈ A ⊓ B := by
    rw [hw]
    exact hx
  have hvwA : v - w ∈ Aᗮ := A.sub_starProjection_mem_orthogonal v
  have hvwB : v - w ∈ B := B.sub_mem hv hwB.2
  exact mem_sup.mpr ⟨w, ⟨hwB.2, hwB.1⟩, v - w, ⟨hvwB, hvwA⟩, add_sub_cancel w v⟩

/-- Compatibility is exactly the agreement of the two implications. -/
theorem compatible_iff_sasaki_eq_material {A B : QProp} :
    Compatible A B ↔ sasaki A B = material A B := by
  constructor
  · intro h
    apply le_antisymm (sasaki_le_material A B)
    refine sup_le le_sup_left ?_
    intro v hv
    have hvSplit : v ∈ (B ⊓ A) ⊔ (B ⊓ Aᗮ) := by
      rw [← compatible_right h]
      exact hv
    rcases mem_sup.mp hvSplit with ⟨x, hx, y, hy, rfl⟩
    exact add_mem
      (mem_sup.mpr ⟨0, zero_mem _, x, ⟨hx.2, hx.1⟩, zero_add x⟩)
      (mem_sup.mpr ⟨y, hy.2, 0, zero_mem _, add_zero y⟩)
  · intro h
    rw [Compatible]
    refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    intro v hv
    let w := B.starProjection v
    have hwB : w ∈ B := B.starProjection_apply_mem v
    have hvw : v - w ∈ Bᗮ := B.sub_starProjection_mem_orthogonal v
    have hwS : w ∈ sasaki A B := by
      have hwM : w ∈ material A B :=
        mem_sup.mpr ⟨0, zero_mem _, w, hwB, zero_add w⟩
      rwa [← h] at hwM
    obtain ⟨a, ha, c, hc, hwc⟩ := mem_sup.mp hwS
    have ha_eq : a = w - c := eq_sub_of_add_eq hwc
    have haB : a ∈ B := by
      rw [ha_eq]
      exact B.sub_mem hwB hc.2
    have havw : inner ℂ a (v - w) = 0 :=
      inner_right_of_mem_orthogonal haB hvw
    have hav : inner ℂ a v = 0 :=
      inner_left_of_mem_orthogonal hv ha
    have hac : inner ℂ a c = 0 :=
      inner_left_of_mem_orthogonal hc.1 ha
    have haa : inner ℂ a a = 0 := by
      have hvsum : inner ℂ a v = inner ℂ a (v - w) + inner ℂ a w := by
        calc
          inner ℂ a v = inner ℂ a ((v - w) + w) := by
            congr 1
            exact (sub_add_cancel v w).symm
          _ = inner ℂ a (v - w) + inner ℂ a w := inner_add_right a (v - w) w
      rw [hav, havw, zero_add] at hvsum
      have hwinner : inner ℂ a w = inner ℂ a a + inner ℂ a c := by
        calc
          inner ℂ a w = inner ℂ a (a + c) := by
            congr 1
            exact hwc.symm
          _ = inner ℂ a a + inner ℂ a c := inner_add_right a a c
      rw [hwinner, hac, add_zero] at hvsum
      exact hvsum.symm
    have ha0 : a = 0 := inner_self_eq_zero.mp haa
    have hwA : w ∈ A ⊓ B := by
      have hw_eq : w = c := by
        calc
          w = a + c := hwc.symm
          _ = 0 + c := by rw [ha0]
          _ = c := zero_add _
      rw [hw_eq]
      exact hc
    exact mem_sup.mpr ⟨w, ⟨hwA.1, hwA.2⟩, v - w, ⟨A.sub_mem hv hwA.1, hvw⟩,
      add_sub_cancel w v⟩

private theorem finrank_top_qprop : finrank ℂ (⊤ : QProp) = 2 := by
  rw [finrank_top]
  exact dualSpinor_finrank

theorem lineE0_orthogonal_eq_lineE1 : lineE0ᗮ = lineE1 := by
  have hle : lineE1 ≤ lineE0ᗮ := lineE0_isOrtho_lineE1.symm
  have hdim : finrank ℂ lineE0ᗮ = 1 := by
    have h := lineE0.finrank_add_finrank_orthogonal
    rw [lineE0_finrank, dualSpinor_finrank] at h
    linarith
  symm
  exact eq_of_le_of_finrank_eq hle (lineE1_finrank.trans hdim.symm)

theorem lineE1_orthogonal_eq_lineE0 : lineE1ᗮ = lineE0 := by
  rw [← lineE0_orthogonal_eq_lineE1, Submodule.orthogonal_orthogonal]

theorem lineE0_compatible_lineE1 : Compatible lineE0 lineE1 := by
  rw [Compatible, lineE0_inf_lineE1, lineE1_orthogonal_eq_lineE0, inf_idem, bot_sup_eq]

theorem computational_rays_implications_agree :
    sasaki lineE0 lineE1 = material lineE0 lineE1 :=
  compatible_iff_sasaki_eq_material.mp lineE0_compatible_lineE1

theorem sasaki_lineE0_lineE1 : sasaki lineE0 lineE1 = lineE1 := by
  simp [sasaki, lineE0_orthogonal_eq_lineE1, lineE0_inf_lineE1]

theorem inner_e0_d01 : inner ℂ e0 d01 = 1 := by
  simp [e0, e1, d01, EuclideanSpace.inner_single_left, PiLp.add_apply]

theorem lineE0_not_ortho_lineD : ¬ lineE0 ⟂ lineD := by
  intro h
  have h0 := h.inner_eq (Submodule.mem_span_singleton_self _)
    (Submodule.mem_span_singleton_self _)
  rw [inner_e0_d01] at h0
  exact one_ne_zero h0

theorem lineE0_split_lineD :
    (lineE0 ⊓ lineD) ⊔ (lineE0 ⊓ lineDᗮ) = (⊥ : QProp) := by
  rw [lineE0_inf_lineD, bot_sup_eq]
  refine eq_bot_iff.mpr ?_
  intro x hx
  obtain ⟨a, rfl⟩ := mem_span_singleton.mp hx.1
  have hinner : inner ℂ d01 (a • e0) = 0 :=
    inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self _) hx.2
  have hde : inner ℂ d01 e0 = 1 := by
    rw [← inner_conj_symm, inner_e0_d01]
    simp
  rw [inner_smul_right, hde, mul_one] at hinner
  simp [hinner]

/-- A basis ray and the diagonal: the classical expansion is the whole
space, and the native implication is the orthogonal line. -/
theorem diagonal_classical_overshoots :
    sasaki lineE0 lineD = lineE1 ∧ material lineE0 lineD = ⊤ := by
  constructor
  · simp [sasaki, lineE0_orthogonal_eq_lineE1, lineE0_inf_lineD]
  · simp [material, lineE0_orthogonal_eq_lineE1, lineE1_sup_lineD]

theorem diagonal_not_compatible : ¬ Compatible lineE0 lineD := by
  intro h
  have hs := diagonal_classical_overshoots
  have hagree := compatible_iff_sasaki_eq_material.mp h
  have htop : (lineE1 : QProp) = ⊤ := by rw [← hs.1, hagree, hs.2]
  have hdim := congrArg (fun S : QProp => finrank ℂ S) htop
  rw [lineE1_finrank, finrank_top_qprop] at hdim
  exact absurd hdim (by decide)

end Logic

end DstDiophantine
