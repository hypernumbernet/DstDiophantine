import DstDiophantine.Algebra.LorentzLie
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Data.Finset.Sort

/-!
# The ten bivectors are a basis of the bivector grade

The binomial count `C(5,2) = 10` names a dimension. What is proved here is that
the three geometric classes realise it:

* `linearIndependent_tenGen`: boosts, rotations, and translations are linearly
  independent;
* `poincareSpan_eq_bivectorGrade`: their span is the whole grade-2 summand of
  `G(3,1,1)`, transported along the canonical module isomorphism with the
  exterior algebra;
* the three classes are complementary, of dimensions 3, 3, and 4, so
  `lorentzSpan ⊔ nullSpan` is a direct sum and equals that grade.

An abstract Lie-algebra isomorphism with `𝔦𝔰𝔬(3,1)` is not claimed.
-/

namespace DstDiophantine

open CliffordAlgebra ExteriorAlgebra PGA Generators

namespace BivectorBasis

noncomputable instance : Invertible (2 : ℝ) := ⟨2⁻¹, by norm_num, by norm_num⟩

private theorem associated_neg_basis_ortho {i j : Fin 5} (hij : i ≠ j) :
    QuadraticMap.associated (-Q311) (e5vec i) (e5vec j) = 0 := by
  rw [QuadraticMap.associated_isOrtho, QuadraticMap.isOrtho_def]
  have h := Q311_isOrtho_basis i j hij
  rw [QuadraticMap.isOrtho_def] at h
  simp only [neg_apply]
  rw [h]
  abel

/-- Off-diagonal products of basis vectors are sent to the corresponding
exterior products. The polar term vanishes because the basis is orthogonal. -/
theorem equivExterior_ι_mul_ι {i j : Fin 5} (hij : i ≠ j) :
    equivExterior Q311 (ι i * ι j) =
      ExteriorAlgebra.ι ℝ (e5vec i) * ExteriorAlgebra.ι ℝ (e5vec j) := by
  have hB := associated_neg_basis_ortho hij
  unfold equivExterior
  rw [changeFormEquiv_apply]
  dsimp [PGA.ι]
  rw [changeForm_ι_mul_ι, hB]
  simp

private theorem sort_pair {i j : Fin 5} (hij : i < j) :
    Finset.sort ({i, j} : Finset (Fin 5)) (· ≤ ·) = [i, j] := by
  have hi : i ∉ ({j} : Finset (Fin 5)) := by simp [hij.ne]
  have hpair : ({i, j} : Finset (Fin 5)) = insert i {j} := by
    ext k
    simp [Finset.mem_insert, Finset.mem_singleton]
  rw [hpair, Finset.sort_insert (r := (· ≤ ·)) (s := {j}) (a := i) (h₁ := ?_) (h₂ := hi)]
  · simp [Finset.sort_singleton]
  · intro b hb
    simp only [Finset.mem_singleton] at hb
    subst hb
    exact hij.le

/-- Ordered bivector `eᵢ eⱼ` for the increasing enumeration of a 2-set. -/
noncomputable def orderedBivector (s : Set.powersetCard (Fin 5) 2) : PGA :=
  let e := Finset.orderEmbOfFin (s : Finset (Fin 5)) (Set.powersetCard.card_eq s)
  ι (e 0) * ι (e 1)

theorem orderedBivector_eq_mul {i j : Fin 5} (hij : i < j)
    (s : Set.powersetCard (Fin 5) 2) (hs : (s : Finset (Fin 5)) = {i, j}) :
    orderedBivector s = ι i * ι j := by
  dsimp [orderedBivector]
  have hsort : ((s : Finset (Fin 5))).sort (· ≤ ·) = [i, j] := by
    rw [hs]
    exact sort_pair hij
  have h0 : Finset.orderEmbOfFin (s : Finset (Fin 5)) (Set.powersetCard.card_eq s) 0 = i := by
    rw [Finset.orderEmbOfFin_apply]
    have hlen : 0 < (((s : Finset (Fin 5))).sort (· ≤ ·)).length := by
      rw [Finset.length_sort, Set.powersetCard.card_eq]; decide
    have hget : (((s : Finset (Fin 5))).sort (· ≤ ·)).get ⟨0, hlen⟩ = i := by
      simpa [hsort] using (rfl : ([i, j] : List (Fin 5)).get ⟨0, by decide⟩ = i)
    simpa [Finset.orderEmbOfFin_apply] using hget
  have h1 : Finset.orderEmbOfFin (s : Finset (Fin 5)) (Set.powersetCard.card_eq s) 1 = j := by
    rw [Finset.orderEmbOfFin_apply]
    have hlen : 1 < (((s : Finset (Fin 5))).sort (· ≤ ·)).length := by
      rw [Finset.length_sort, Set.powersetCard.card_eq]; decide
    have hget : (((s : Finset (Fin 5))).sort (· ≤ ·)).get ⟨1, hlen⟩ = j := by
      simpa [hsort] using (rfl : ([i, j] : List (Fin 5)).get ⟨1, by decide⟩ = j)
    simpa [Finset.orderEmbOfFin_apply] using hget
  rw [h0, h1]

theorem equivExterior_orderedBivector (s : Set.powersetCard (Fin 5) 2) :
    equivExterior Q311 (orderedBivector s) =
      ExteriorAlgebra.ιMulti_family ℝ 2 (fun i : Fin 5 => e5vec i) s := by
  set e : Fin 2 ↪o Fin 5 :=
    Finset.orderEmbOfFin (s : Finset (Fin 5)) (Set.powersetCard.card_eq s)
  have hne : e 0 ≠ e 1 := fun h => (Fin.zero_ne_one : (0 : Fin 2) ≠ 1) (e.injective h)
  have hord : orderedBivector s = ι (e 0) * ι (e 1) := by
    simp [orderedBivector, e]
  rw [hord, equivExterior_ι_mul_ι hne]
  rw [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  simp [Matrix.vecTail, e5vec, e]

theorem linearIndependent_orderedBivector :
    LinearIndependent ℝ orderedBivector := by
  refine LinearIndependent.of_comp (equivExterior Q311).toLinearMap ?_
  have hv : LinearIndependent ℝ (fun i : Fin 5 => e5vec i) := by
    have hvec : (fun i : Fin 5 => e5vec i) = (⇑(Pi.basisFun ℝ (Fin 5))) := by
      funext i
      simp [e5vec, Pi.basisFun_apply]
    rw [hvec]
    exact (Pi.basisFun ℝ (Fin 5)).linearIndependent
  have hpow := exteriorPower.ιMulti_family_linearIndependent_field (n := 2) hv
  have hcoe : LinearIndependent ℝ
      ((Submodule.subtype (⋀[ℝ]^2 Vec5)) ∘
        exteriorPower.ιMulti_family ℝ 2 (fun i : Fin 5 => e5vec i)) :=
    hpow.map' _ (⋀[ℝ]^2 Vec5).ker_subtype
  have heq :
      (equivExterior Q311).toLinearMap ∘ orderedBivector =
        (Submodule.subtype (⋀[ℝ]^2 Vec5)) ∘
          exteriorPower.ιMulti_family ℝ 2 (fun i : Fin 5 => e5vec i) := by
    funext s
    rw [Function.comp_apply, Function.comp_apply]
    change equivExterior Q311 (orderedBivector s) = _
    rw [equivExterior_orderedBivector]
    rfl
  rw [heq]
  exact hcoe

/-- The ten generators, in the order boosts, then the three rotations, then translations. -/
noncomputable def tenGen : Fin 10 → PGA
  | 0 => hyperbolic 0
  | 1 => hyperbolic 1
  | 2 => hyperbolic 2
  | 3 => cyclic 2
  | 4 => cyclic 1
  | 5 => cyclic 0
  | 6 => null 0
  | 7 => null 1
  | 8 => null 2
  | 9 => null 3

/-- Pair of basis indices underlying each generator, increasingly ordered. -/
def pairIndex : Fin 10 → Set.powersetCard (Fin 5) 2
  | 0 => ⟨{0, 1}, Finset.card_pair (by decide : (0 : Fin 5) ≠ 1)⟩
  | 1 => ⟨{0, 2}, Finset.card_pair (by decide : (0 : Fin 5) ≠ 2)⟩
  | 2 => ⟨{0, 3}, Finset.card_pair (by decide : (0 : Fin 5) ≠ 3)⟩
  | 3 => ⟨{1, 2}, Finset.card_pair (by decide : (1 : Fin 5) ≠ 2)⟩
  | 4 => ⟨{1, 3}, Finset.card_pair (by decide : (1 : Fin 5) ≠ 3)⟩
  | 5 => ⟨{2, 3}, Finset.card_pair (by decide : (2 : Fin 5) ≠ 3)⟩
  | 6 => ⟨{0, 4}, Finset.card_pair (by decide : (0 : Fin 5) ≠ 4)⟩
  | 7 => ⟨{1, 4}, Finset.card_pair (by decide : (1 : Fin 5) ≠ 4)⟩
  | 8 => ⟨{2, 4}, Finset.card_pair (by decide : (2 : Fin 5) ≠ 4)⟩
  | 9 => ⟨{3, 4}, Finset.card_pair (by decide : (3 : Fin 5) ≠ 4)⟩

/-- Sign relating each generator to the increasing product `eᵢ eⱼ`. -/
def pairSign : Fin 10 → ℝˣ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => -1
  | 4 => 1
  | 5 => -1
  | 6 => -1
  | 7 => -1
  | 8 => -1
  | 9 => -1

theorem pairIndex_injective : Function.Injective pairIndex := by
  decide

private theorem tenGen_eq_signed (k : Fin 10) :
    tenGen k = (pairSign k : ℝ) • orderedBivector (pairIndex k) := by
  fin_cases k <;> dsimp
  · rw [show tenGen 0 = hyperbolic 0 from rfl, show pairSign 0 = 1 from rfl, Units.val_one, one_smul,
      show hyperbolic 0 = PGA.ι 0 * PGA.ι 1 from rfl]
    exact (orderedBivector_eq_mul (by decide : (0 : Fin 5) < 1) (pairIndex 0) rfl).symm
  · rw [show tenGen 1 = hyperbolic 1 from rfl, show pairSign 1 = 1 from rfl, Units.val_one, one_smul,
      show hyperbolic 1 = PGA.ι 0 * PGA.ι 2 from rfl]
    exact (orderedBivector_eq_mul (by decide : (0 : Fin 5) < 2) (pairIndex 1) rfl).symm
  · rw [show tenGen 2 = hyperbolic 2 from rfl, show pairSign 2 = 1 from rfl, Units.val_one, one_smul,
      show hyperbolic 2 = PGA.ι 0 * PGA.ι 3 from rfl]
    exact (orderedBivector_eq_mul (by decide : (0 : Fin 5) < 3) (pairIndex 2) rfl).symm
  · rw [show tenGen 3 = cyclic 2 from rfl, show pairSign 3 = -1 from rfl, show cyclic 2 =
        PGA.ι 2 * PGA.ι 1 from rfl, e_mul_anticomm (by decide : (2 : Fin 5) ≠ 1)]
    rw [Units.val_neg, neg_smul, Units.val_one, one_smul, neg_inj]
    exact (orderedBivector_eq_mul (by decide : (1 : Fin 5) < 2) (pairIndex 3) rfl).symm
  · rw [show tenGen 4 = cyclic 1 from rfl, show pairSign 4 = 1 from rfl, Units.val_one, one_smul,
      show cyclic 1 = PGA.ι 1 * PGA.ι 3 from rfl]
    exact (orderedBivector_eq_mul (by decide : (1 : Fin 5) < 3) (pairIndex 4) rfl).symm
  · rw [show tenGen 5 = cyclic 0 from rfl, show pairSign 5 = -1 from rfl, show cyclic 0 =
        PGA.ι 3 * PGA.ι 2 from rfl, e_mul_anticomm (by decide : (3 : Fin 5) ≠ 2)]
    rw [Units.val_neg, neg_smul, Units.val_one, one_smul, neg_inj]
    exact (orderedBivector_eq_mul (by decide : (2 : Fin 5) < 3) (pairIndex 5) rfl).symm
  · rw [show tenGen 6 = null 0 from rfl, show pairSign 6 = -1 from rfl, show null 0 =
        PGA.ι 4 * PGA.ι 0 from rfl, e_mul_anticomm (by decide : (4 : Fin 5) ≠ 0)]
    rw [Units.val_neg, neg_smul, Units.val_one, one_smul, neg_inj]
    exact (orderedBivector_eq_mul (by decide : (0 : Fin 5) < 4) (pairIndex 6) rfl).symm
  · rw [show tenGen 7 = null 1 from rfl, show pairSign 7 = -1 from rfl, show null 1 =
        PGA.ι 4 * PGA.ι 1 from rfl, e_mul_anticomm (by decide : (4 : Fin 5) ≠ 1)]
    rw [Units.val_neg, neg_smul, Units.val_one, one_smul, neg_inj]
    exact (orderedBivector_eq_mul (by decide : (1 : Fin 5) < 4) (pairIndex 7) rfl).symm
  · rw [show tenGen 8 = null 2 from rfl, show pairSign 8 = -1 from rfl, show null 2 =
        PGA.ι 4 * PGA.ι 2 from rfl, e_mul_anticomm (by decide : (4 : Fin 5) ≠ 2)]
    rw [Units.val_neg, neg_smul, Units.val_one, one_smul, neg_inj]
    exact (orderedBivector_eq_mul (by decide : (2 : Fin 5) < 4) (pairIndex 8) rfl).symm
  · rw [show tenGen 9 = null 3 from rfl, show pairSign 9 = -1 from rfl, show null 3 =
        PGA.ι 4 * PGA.ι 3 from rfl, e_mul_anticomm (by decide : (4 : Fin 5) ≠ 3)]
    rw [Units.val_neg, neg_smul, Units.val_one, one_smul, neg_inj]
    exact (orderedBivector_eq_mul (by decide : (3 : Fin 5) < 4) (pairIndex 9) rfl).symm

theorem linearIndependent_tenGen : LinearIndependent ℝ tenGen := by
  have hunits :=
    (linearIndependent_orderedBivector.comp pairIndex pairIndex_injective).units_smul pairSign
  have heq : tenGen = pairSign • (orderedBivector ∘ pairIndex) := by
    funext k
    rw [Pi.smul_apply', Units.smul_def]
    exact tenGen_eq_signed k
  rw [heq]
  exact hunits

theorem span_tenGen_eq_poincare :
    Submodule.span ℝ (Set.range tenGen) = LorentzLie.poincareSpan := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.mem_sup_left (LorentzLie.hyperbolic_mem_lorentzSpan 0)
    · exact Submodule.mem_sup_left (LorentzLie.hyperbolic_mem_lorentzSpan 1)
    · exact Submodule.mem_sup_left (LorentzLie.hyperbolic_mem_lorentzSpan 2)
    · exact Submodule.mem_sup_left (LorentzLie.cyclic_mem_lorentzSpan 2)
    · exact Submodule.mem_sup_left (LorentzLie.cyclic_mem_lorentzSpan 1)
    · exact Submodule.mem_sup_left (LorentzLie.cyclic_mem_lorentzSpan 0)
    · exact Submodule.mem_sup_right (mem_nullSpan 0)
    · exact Submodule.mem_sup_right (mem_nullSpan 1)
    · exact Submodule.mem_sup_right (mem_nullSpan 2)
    · exact Submodule.mem_sup_right (mem_nullSpan 3)
  · rw [LorentzLie.poincareSpan]
    refine sup_le ?_ ?_
    · rw [LorentzLie.lorentzSpan, Submodule.span_le]
      rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · fin_cases a
        · exact Submodule.subset_span ⟨0, rfl⟩
        · exact Submodule.subset_span ⟨1, rfl⟩
        · exact Submodule.subset_span ⟨2, rfl⟩
      · fin_cases a
        · exact Submodule.subset_span ⟨5, rfl⟩
        · exact Submodule.subset_span ⟨4, rfl⟩
        · exact Submodule.subset_span ⟨3, rfl⟩
    · rw [nullSpan, Submodule.span_le]
      rintro _ ⟨μ, rfl⟩
      fin_cases μ
      · exact Submodule.subset_span ⟨6, rfl⟩
      · exact Submodule.subset_span ⟨7, rfl⟩
      · exact Submodule.subset_span ⟨8, rfl⟩
      · exact Submodule.subset_span ⟨9, rfl⟩

theorem finrank_poincareSpan : Module.finrank ℝ LorentzLie.poincareSpan = 10 := by
  rw [← span_tenGen_eq_poincare, finrank_span_eq_card linearIndependent_tenGen]
  simp

/-- Grade-2 summand of `G(3,1,1)`, as a submodule, via the module isomorphism
with the exterior algebra. -/
noncomputable def bivectorGrade : Submodule ℝ PGA :=
  (⋀[ℝ]^2 Vec5).map (equivExterior Q311).symm.toLinearMap

theorem finrank_bivectorGrade : Module.finrank ℝ bivectorGrade = 10 := by
  rw [bivectorGrade, LinearEquiv.finrank_map_eq]
  rw [Module.finrank_eq_card_basis ((Pi.basisFun ℝ (Fin 5)).exteriorPower 2)]
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem poincareSpan_le_bivectorGrade :
    LorentzLie.poincareSpan ≤ bivectorGrade := by
  rw [← span_tenGen_eq_poincare, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  apply Submodule.mem_map.mpr
  refine ⟨equivExterior Q311 (tenGen k), ?_, (equivExterior Q311).symm_apply_apply _⟩
  rw [tenGen_eq_signed, LinearEquiv.map_smul, equivExterior_orderedBivector]
  refine Submodule.smul_mem _ _ ?_
  rw [ExteriorAlgebra.ιMulti_family]
  exact ExteriorAlgebra.ιMulti_range ℝ 2 (Set.mem_range_self _)

/-- The Poincaré span is the entire bivector grade. -/
theorem poincareSpan_eq_bivectorGrade :
    LorentzLie.poincareSpan = bivectorGrade :=
  Submodule.eq_of_le_of_finrank_eq poincareSpan_le_bivectorGrade
    (finrank_poincareSpan.trans finrank_bivectorGrade.symm)

/-! ### The three classes are complementary -/

private def boostIndex (a : Fin 3) : Fin 10 := a.castLE (by decide : 3 ≤ 10)

private theorem tenGen_boost (a : Fin 3) : tenGen (boostIndex a) = hyperbolic a := by
  fin_cases a <;> rfl

private def cycIndex : Fin 3 → Fin 10
  | 0 => 5
  | 1 => 4
  | 2 => 3

private theorem tenGen_cyc (a : Fin 3) : tenGen (cycIndex a) = cyclic a := by
  fin_cases a <;> rfl

private def nullIndex (μ : Fin 4) : Fin 10 := ⟨6 + μ.val, by omega⟩

private theorem nullIndex_injective : Function.Injective nullIndex := by
  intro a b h
  apply Fin.ext
  have := congrArg (fun i : Fin 10 => (i : ℕ)) h
  simp [nullIndex] at this
  omega

private theorem tenGen_null (μ : Fin 4) : tenGen (nullIndex μ) = null μ := by
  fin_cases μ <;> rfl

private def lorentzIndex : Fin 3 ⊕ Fin 3 → Fin 10
  | Sum.inl a => boostIndex a
  | Sum.inr a => cycIndex a

private theorem lorentzIndex_injective : Function.Injective lorentzIndex := by
  decide

private theorem tenGen_lorentzIndex :
    tenGen ∘ lorentzIndex = Sum.elim hyperbolic cyclic := by
  funext x
  cases x with
  | inl a => simpa [lorentzIndex] using tenGen_boost a
  | inr a => simpa [lorentzIndex] using tenGen_cyc a

private def poincareIndex : (Fin 3 ⊕ Fin 3) ⊕ Fin 4 → Fin 10
  | Sum.inl i => lorentzIndex i
  | Sum.inr μ => nullIndex μ

private theorem poincareIndex_injective : Function.Injective poincareIndex := by
  decide

private theorem tenGen_poincareIndex :
    tenGen ∘ poincareIndex = Sum.elim (Sum.elim hyperbolic cyclic) null := by
  funext x
  cases x with
  | inl i => simpa [poincareIndex] using congrFun tenGen_lorentzIndex i
  | inr μ => simpa [poincareIndex] using tenGen_null μ

private theorem span_sumElim_lorentz :
    Submodule.span ℝ (Set.range (Sum.elim hyperbolic cyclic)) = LorentzLie.lorentzSpan := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    cases x with
    | inl a => exact LorentzLie.hyperbolic_mem_lorentzSpan a
    | inr a => exact LorentzLie.cyclic_mem_lorentzSpan a
  · rw [LorentzLie.lorentzSpan, Submodule.span_le]
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inr a, rfl⟩

theorem linearIndependent_hyperbolic : LinearIndependent ℝ hyperbolic := by
  have hinj : Function.Injective boostIndex :=
    Fin.castLE_injective (by decide : 3 ≤ 10)
  have h := linearIndependent_tenGen.comp boostIndex hinj
  have heq : hyperbolic = tenGen ∘ boostIndex := by
    funext a
    exact (tenGen_boost a).symm
  simpa [heq] using h

theorem linearIndependent_cyclic : LinearIndependent ℝ cyclic := by
  have hinj : Function.Injective cycIndex := by decide
  have h := linearIndependent_tenGen.comp cycIndex hinj
  have heq : cyclic = tenGen ∘ cycIndex := by
    funext a
    exact (tenGen_cyc a).symm
  simpa [heq] using h

theorem linearIndependent_null : LinearIndependent ℝ null := by
  have h := linearIndependent_tenGen.comp nullIndex nullIndex_injective
  have heq : null = tenGen ∘ nullIndex := by
    funext μ
    exact (tenGen_null μ).symm
  simpa [heq] using h

theorem finrank_hyperbolicSpan :
    Module.finrank ℝ (Submodule.span ℝ (Set.range hyperbolic)) = 3 := by
  rw [finrank_span_eq_card linearIndependent_hyperbolic]
  simp

theorem finrank_cyclicSpan : Module.finrank ℝ LorentzLie.cyclicSpan = 3 := by
  rw [LorentzLie.cyclicSpan, finrank_span_eq_card linearIndependent_cyclic]
  simp

theorem finrank_nullSpan : Module.finrank ℝ nullSpan = 4 := by
  rw [nullSpan, finrank_span_eq_card linearIndependent_null]
  simp

theorem finrank_lorentzSpan : Module.finrank ℝ LorentzLie.lorentzSpan = 6 := by
  have hli : LinearIndependent ℝ (Sum.elim hyperbolic cyclic) := by
    simpa [tenGen_lorentzIndex] using
      linearIndependent_tenGen.comp lorentzIndex lorentzIndex_injective
  rw [← span_sumElim_lorentz, finrank_span_eq_card hli]
  simp

theorem disjoint_hyperbolic_cyclic :
    Disjoint (Submodule.span ℝ (Set.range hyperbolic)) LorentzLie.cyclicSpan := by
  have hli : LinearIndependent ℝ (Sum.elim hyperbolic cyclic) := by
    simpa [tenGen_lorentzIndex] using
      linearIndependent_tenGen.comp lorentzIndex lorentzIndex_injective
  have h := (linearIndependent_sum.mp hli).2.2
  simpa [LorentzLie.cyclicSpan] using h

theorem disjoint_lorentz_null :
    Disjoint LorentzLie.lorentzSpan nullSpan := by
  have hli : LinearIndependent ℝ (Sum.elim (Sum.elim hyperbolic cyclic) null) := by
    simpa [tenGen_poincareIndex] using
      linearIndependent_tenGen.comp poincareIndex poincareIndex_injective
  have h := (linearIndependent_sum.mp hli).2.2
  have hsup : Submodule.span ℝ (Set.range hyperbolic) ⊔
      Submodule.span ℝ (Set.range cyclic) = LorentzLie.lorentzSpan := by
    rw [← Submodule.span_union]
    rfl
  simpa [hsup, nullSpan] using h

end BivectorBasis

end DstDiophantine
