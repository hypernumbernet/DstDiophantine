import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Invariant
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Lie closure of the ten generators

The Lorentz and Poincaré spans are closed under the commutator, with duality a complex structure on
the Lorentz span. An abstract isomorphism with `𝔰𝔬(3,1)` is not claimed.
-/

namespace DstDiophantine

open CliffordAlgebra PGA Generators Operations Motor

namespace LorentzLie

/-- Rotation span: the three cyclic generators. -/
noncomputable def cyclicSpan : Submodule ℝ PGA :=
  Submodule.span ℝ (Set.range (cyclic : Fin 3 → PGA))

/-- Lorentz span: the six hyperbolic and cyclic generators. -/
noncomputable def lorentzSpan : Submodule ℝ PGA :=
  Submodule.span ℝ
    (Set.range (hyperbolic : Fin 3 → PGA) ∪ Set.range (cyclic : Fin 3 → PGA))

/-- Poincaré span: Lorentz span plus the null translation span. -/
noncomputable def poincareSpan : Submodule ℝ PGA :=
  lorentzSpan ⊔ nullSpan

theorem hyperbolic_mem_lorentzSpan (a : Fin 3) : hyperbolic a ∈ lorentzSpan :=
  Submodule.subset_span (Or.inl ⟨a, rfl⟩)

theorem cyclic_mem_lorentzSpan (a : Fin 3) : cyclic a ∈ lorentzSpan :=
  Submodule.subset_span (Or.inr ⟨a, rfl⟩)

theorem cyclic_mem_cyclicSpan (a : Fin 3) : cyclic a ∈ cyclicSpan :=
  Submodule.subset_span ⟨a, rfl⟩

theorem cyclicSpan_le_lorentzSpan : cyclicSpan ≤ lorentzSpan :=
  Submodule.span_mono Set.subset_union_right

theorem lorentzSpan_le_poincareSpan : lorentzSpan ≤ poincareSpan := le_sup_left

theorem nullSpan_le_poincareSpan : nullSpan ≤ poincareSpan := le_sup_right

theorem null_mem_poincareSpan (μ : Fin 4) : null μ ∈ poincareSpan :=
  nullSpan_le_poincareSpan (mem_nullSpan μ)

/-! ### Bilinear extension of a commutator table from generators to spans -/

private theorem commutator_span_mem {s t : Set PGA} {S : Submodule ℝ PGA}
    (h : ∀ u ∈ s, ∀ v ∈ t, commutator u v ∈ S) {x y : PGA}
    (hx : x ∈ Submodule.span ℝ s) (hy : y ∈ Submodule.span ℝ t) :
    commutator x y ∈ S := by
  refine Submodule.span_induction₂ (s := s) (t := t)
    (p := fun u v _ _ => commutator u v ∈ S) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro u v hu hv
    exact h u hu v hv
  · intro v _
    have : commutator 0 v = 0 := by simp [Generators.commutator]
    rw [this]; exact S.zero_mem
  · intro u _
    have : commutator u 0 = 0 := by simp [Generators.commutator]
    rw [this]; exact S.zero_mem
  · intro u₁ u₂ v _ _ _ h₁ h₂
    rw [commutator_add_left]; exact S.add_mem h₁ h₂
  · intro u v₁ v₂ _ _ _ h₁ h₂
    rw [commutator_add_right]; exact S.add_mem h₁ h₂
  · intro r u v _ _ h
    rw [commutator_smul_left]; exact S.smul_mem r h
  · intro r u v _ _ h
    rw [commutator_smul_right]; exact S.smul_mem r h

/-! ### The pseudoscalar is central on the Lorentz sector -/

private theorem ι_anticomm_pseudoscalar_of_ne (i : Fin 5) (hi : i ≠ e4Index) :
    ι i * pseudoscalar = -(pseudoscalar * ι i) := by
  fin_cases i
  · exact ι_anticomm_pseudoscalar 0
  · exact ι_anticomm_pseudoscalar 1
  · exact ι_anticomm_pseudoscalar 2
  · exact ι_anticomm_pseudoscalar 3
  · exact absurd rfl hi

private theorem commute_pseudoscalar_bivector {i j : Fin 5}
    (hi : i ≠ e4Index) (hj : j ≠ e4Index) :
    Commute pseudoscalar (ι i * ι j) := by
  unfold Commute SemiconjBy
  have hi' : pseudoscalar * ι i = -(ι i * pseudoscalar) :=
    neg_eq_iff_eq_neg.mp (ι_anticomm_pseudoscalar_of_ne i hi).symm
  have hj' : pseudoscalar * ι j = -(ι j * pseudoscalar) :=
    neg_eq_iff_eq_neg.mp (ι_anticomm_pseudoscalar_of_ne j hj).symm
  calc pseudoscalar * (ι i * ι j)
      = (pseudoscalar * ι i) * ι j := by rw [mul_assoc]
    _ = -(ι i * pseudoscalar) * ι j := by rw [hi']
    _ = -(ι i * (pseudoscalar * ι j)) := by simp [mul_assoc]
    _ = -(ι i * (-(ι j * pseudoscalar))) := by rw [hj']
    _ = ι i * ι j * pseudoscalar := by simp [mul_assoc]

theorem commute_pseudoscalar_hyperbolic (a : Fin 3) :
    Commute pseudoscalar (hyperbolic a) := by
  fin_cases a
  · exact commute_pseudoscalar_bivector (i := 0) (j := 1) (by decide) (by decide)
  · exact commute_pseudoscalar_bivector (i := 0) (j := 2) (by decide) (by decide)
  · exact commute_pseudoscalar_bivector (i := 0) (j := 3) (by decide) (by decide)

theorem commute_pseudoscalar_cyclic (a : Fin 3) :
    Commute pseudoscalar (cyclic a) := by
  fin_cases a
  · exact commute_pseudoscalar_bivector (i := 3) (j := 2) (by decide) (by decide)
  · exact commute_pseudoscalar_bivector (i := 1) (j := 3) (by decide) (by decide)
  · exact commute_pseudoscalar_bivector (i := 2) (j := 1) (by decide) (by decide)

theorem reverse_neg_of_mem_lorentzSpan {x : PGA} (hx : x ∈ lorentzSpan) :
    reverse x = -x := by
  refine Submodule.span_induction (p := fun y _ => reverse y = -y) ?_ ?_ ?_ ?_ hx
  · rintro y (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact hyperbolic_reverse a
    · exact cyclic_reverse a
  · simp
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, neg_add]
  · intro r y _ hy
    simp [map_smul, hy]

theorem scalar_add_lorentz_eq_zero {c : ℝ} {x : PGA} (hx : x ∈ lorentzSpan)
    (h : c • (1 : PGA) + x = 0) : c = 0 ∧ x = 0 := by
  have hrev : c • (1 : PGA) - x = 0 := by
    have hR := congrArg reverse h
    rw [map_add, map_smul, reverse.map_one, reverse_neg_of_mem_lorentzSpan hx] at hR
    simpa [sub_eq_add_neg, smul_neg] using hR
  have hsum : (c • (1 : PGA) + x) + (c • (1 : PGA) - x) = 0 := by
    rw [h, hrev, add_zero]
  have htwo : ((2 : ℝ) * c) • (1 : PGA) = 0 := by
    have hpair : c • (1 : PGA) + c • (1 : PGA) = 0 := by
      calc
        c • (1 : PGA) + c • (1 : PGA)
            = (c • (1 : PGA) + x) + (c • (1 : PGA) - x) := by abel
        _ = 0 := hsum
    simpa [two_mul, add_smul] using hpair
  have hc : (2 : ℝ) * c = 0 := by
    have hR : algebraMap ℝ PGA ((2 : ℝ) * c) = 0 := by
      simpa [Algebra.smul_def] using htwo
    exact (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp hR
  have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_left (by norm_num)
  refine ⟨hc0, ?_⟩
  simpa [hc0] using h

theorem commute_pseudoscalar_of_mem_lorentzSpan {x : PGA} (hx : x ∈ lorentzSpan) :
    Commute pseudoscalar x := by
  refine Submodule.span_induction (p := fun y _ => Commute pseudoscalar y) ?_ ?_ ?_ ?_ hx
  · rintro y (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact commute_pseudoscalar_hyperbolic a
    · exact commute_pseudoscalar_cyclic a
  · exact Commute.zero_right _
  · intro y z _ _ hy hz
    exact hy.add_right hz
  · intro r y _ hy
    unfold Commute SemiconjBy at hy ⊢
    rw [mul_smul_comm, smul_mul_assoc, hy]

/-! ### Duality as a complex structure on the Lorentz sector -/

theorem hyperbolic_eq_dual_cyclic (a : Fin 3) : hyperbolic a = dual (cyclic a) :=
  (dual_cyclic a).symm

theorem dual_dual (x : PGA) : dual (dual x) = -x := by
  simp [dual, mul_assoc, pseudoscalar_sq]

theorem dual_add (x y : PGA) : dual (x + y) = dual x + dual y := by
  simp [dual, add_mul]

theorem dual_smul (c : ℝ) (x : PGA) : dual (c • x) = c • dual x := by
  simp [dual]

theorem dual_mem_lorentzSpan {x : PGA} (hx : x ∈ lorentzSpan) : dual x ∈ lorentzSpan := by
  refine Submodule.span_induction (p := fun y _ => dual y ∈ lorentzSpan) ?_ ?_ ?_ ?_ hx
  · rintro y (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · rw [dual_hyperbolic]; exact lorentzSpan.neg_mem (cyclic_mem_lorentzSpan a)
    · rw [dual_cyclic]; exact hyperbolic_mem_lorentzSpan a
  · have : dual (0 : PGA) = 0 := by simp [dual]
    rw [this]; exact lorentzSpan.zero_mem
  · intro y z _ _ hy hz
    rw [dual_add]; exact lorentzSpan.add_mem hy hz
  · intro r y _ hy
    rw [dual_smul]; exact lorentzSpan.smul_mem r hy

theorem commutator_dual_left {x y : PGA} (hy : y ∈ lorentzSpan) :
    commutator (dual x) y = dual (commutator x y) := by
  have hc : pseudoscalar * y = y * pseudoscalar := commute_pseudoscalar_of_mem_lorentzSpan hy
  simp only [Generators.commutator, dual, sub_mul, mul_assoc, hc]

theorem commutator_dual_right {x y : PGA} (hx : x ∈ lorentzSpan) :
    commutator x (dual y) = dual (commutator x y) := by
  have hc : pseudoscalar * x = x * pseudoscalar := commute_pseudoscalar_of_mem_lorentzSpan hx
  simp only [Generators.commutator, dual, sub_mul, mul_assoc, hc]

theorem commutator_dual_dual {x y : PGA} (hx : x ∈ lorentzSpan) (hy : y ∈ lorentzSpan) :
    commutator (dual x) (dual y) = -commutator x y := by
  rw [commutator_dual_left (dual_mem_lorentzSpan hy), commutator_dual_right hx, dual_dual]

theorem commutator_hyperbolic_hyperbolic_eq_neg (a b : Fin 3) :
    commutator (hyperbolic a) (hyperbolic b) = -commutator (cyclic a) (cyclic b) := by
  rw [hyperbolic_eq_dual_cyclic, hyperbolic_eq_dual_cyclic]
  exact commutator_dual_dual (cyclic_mem_lorentzSpan a) (cyclic_mem_lorentzSpan b)

theorem commutator_hyperbolic_cyclic_eq_dual (a b : Fin 3) :
    commutator (hyperbolic a) (cyclic b) = dual (commutator (cyclic a) (cyclic b)) := by
  rw [hyperbolic_eq_dual_cyclic]
  exact commutator_dual_left (cyclic_mem_lorentzSpan b)

theorem commutator_hyperbolic_hyperbolic_cyclic (a b : Fin 3) :
    commutator (hyperbolic a) (hyperbolic b) =
      if a = b then 0
      else if b = a + 1 then -((2 : ℝ) • cyclic (a + 2))
      else (2 : ℝ) • cyclic (b + 2) := by
  rw [commutator_hyperbolic_hyperbolic_eq_neg, commutator_cyclic_cyclic]
  split_ifs <;> simp

theorem lorentzSpan_eq_sup :
    lorentzSpan = cyclicSpan ⊔ cyclicSpan.map (LinearMap.mulRight ℝ pseudoscalar) := by
  have hrange : Set.range (hyperbolic : Fin 3 → PGA) =
      (LinearMap.mulRight ℝ pseudoscalar) '' Set.range (cyclic : Fin 3 → PGA) := by
    rw [← Set.range_comp]
    congr 1
    funext a
    exact hyperbolic_eq_dual_cyclic a
  rw [lorentzSpan, Submodule.span_union, hrange, Submodule.span_image, sup_comm]
  rfl

theorem mem_lorentzSpan_iff {x : PGA} :
    x ∈ lorentzSpan ↔ ∃ u ∈ cyclicSpan, ∃ v ∈ cyclicSpan, x = u + dual v := by
  rw [lorentzSpan_eq_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, dual v, Submodule.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩

/-! ### Lie closure of the spans -/

private theorem commutator_gen_mem :
    ∀ u ∈ Set.range (hyperbolic : Fin 3 → PGA) ∪ Set.range (cyclic : Fin 3 → PGA),
    ∀ v ∈ Set.range (hyperbolic : Fin 3 → PGA) ∪ Set.range (cyclic : Fin 3 → PGA),
      commutator u v ∈ lorentzSpan := by
  rintro u (⟨a, rfl⟩ | ⟨a, rfl⟩) v (⟨b, rfl⟩ | ⟨b, rfl⟩)
  · rw [commutator_hyperbolic_hyperbolic_cyclic]
    split_ifs
    · exact lorentzSpan.zero_mem
    · exact lorentzSpan.neg_mem (lorentzSpan.smul_mem _ (cyclic_mem_lorentzSpan _))
    · exact lorentzSpan.smul_mem _ (cyclic_mem_lorentzSpan _)
  · rw [commutator_hyperbolic_cyclic]
    split_ifs
    · exact lorentzSpan.zero_mem
    · exact lorentzSpan.smul_mem _ (hyperbolic_mem_lorentzSpan _)
    · exact lorentzSpan.neg_mem (lorentzSpan.smul_mem _ (hyperbolic_mem_lorentzSpan _))
  · rw [commutator_neg, commutator_hyperbolic_cyclic]
    split_ifs
    · rw [neg_zero]; exact lorentzSpan.zero_mem
    · exact lorentzSpan.neg_mem (lorentzSpan.smul_mem _ (hyperbolic_mem_lorentzSpan _))
    · exact lorentzSpan.neg_mem
        (lorentzSpan.neg_mem (lorentzSpan.smul_mem _ (hyperbolic_mem_lorentzSpan _)))
  · rw [commutator_cyclic_cyclic]
    split_ifs
    · exact lorentzSpan.zero_mem
    · exact lorentzSpan.smul_mem _ (cyclic_mem_lorentzSpan _)
    · exact lorentzSpan.neg_mem (lorentzSpan.smul_mem _ (cyclic_mem_lorentzSpan _))

theorem commutator_mem_lorentzSpan {x y : PGA} (hx : x ∈ lorentzSpan) (hy : y ∈ lorentzSpan) :
    commutator x y ∈ lorentzSpan :=
  commutator_span_mem commutator_gen_mem hx hy

theorem commutator_lorentz_null_mem_nullSpan {x y : PGA}
    (hx : x ∈ lorentzSpan) (hy : y ∈ nullSpan) :
    commutator x y ∈ nullSpan := by
  refine commutator_span_mem ?_ hx hy
  rintro u (⟨a, rfl⟩ | ⟨a, rfl⟩) v ⟨μ, rfl⟩
  · exact commutator_hyperbolic_null_mem_span a μ
  · exact commutator_cyclic_null_mem_span a μ

theorem commutator_null_null_eq_zero {x y : PGA} (hx : x ∈ nullSpan) (hy : y ∈ nullSpan) :
    commutator x y = 0 := by
  simp [Generators.commutator, nullSpan_mul hx hy, nullSpan_mul hy hx]

theorem commutator_poincare_null_mem_nullSpan {x y : PGA}
    (hx : x ∈ poincareSpan) (hy : y ∈ nullSpan) :
    commutator x y ∈ nullSpan := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [commutator_add_left]
  refine nullSpan.add_mem (commutator_lorentz_null_mem_nullSpan hu hy) ?_
  rw [commutator_null_null_eq_zero hw hy]
  exact nullSpan.zero_mem

theorem commutator_mem_poincareSpan {x y : PGA}
    (hx : x ∈ poincareSpan) (hy : y ∈ poincareSpan) :
    commutator x y ∈ poincareSpan := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.mp hy
  rw [commutator_add_left, commutator_add_right, commutator_add_right]
  refine poincareSpan.add_mem (poincareSpan.add_mem ?_ ?_) (poincareSpan.add_mem ?_ ?_)
  · exact lorentzSpan_le_poincareSpan (commutator_mem_lorentzSpan hu hu')
  · exact nullSpan_le_poincareSpan (commutator_lorentz_null_mem_nullSpan hu hw')
  · rw [commutator_neg]
    exact poincareSpan.neg_mem
      (nullSpan_le_poincareSpan (commutator_lorentz_null_mem_nullSpan hu' hw))
  · rw [commutator_null_null_eq_zero hw hw']
    exact poincareSpan.zero_mem

/-- The Poincaré span is not abelian: the radial boost moves the time translation. -/
theorem commutator_hyperbolic0_null0_ne_zero : commutator (hyperbolic 0) (null 0) ≠ 0 := by
  rw [commutator_hyperbolic0_null0]
  intro h
  have : null 1 = 0 := (smul_eq_zero.mp h).resolve_left (by norm_num)
  exact null_one_ne_zero this

/-! ### Duality on torsion parameters -/

/-- Quarter-turn `(α, β) ↦ (β, -α)` on each axis. -/
def dualParams (p : TorsionParams) : TorsionParams where
  alpha := p.beta
  beta := fun a => -p.alpha a

theorem dualParams_dualParams (p : TorsionParams) : dualParams (dualParams p) =
    { alpha := fun a => -p.alpha a, beta := fun a => -p.beta a } := by
  simp [dualParams]

theorem dual_omegaTorsion (p : TorsionParams) :
    dual (omegaTorsion p) = omegaTorsion (dualParams p) := by
  have hlin : ∀ x, dual x = LinearMap.mulRight ℝ pseudoscalar x := fun _ => rfl
  simp only [omegaTorsion, dualParams]
  rw [hlin, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_add, map_smul, map_smul, ← hlin, ← hlin, dual_hyperbolic, dual_cyclic]
  module

theorem omegaTorsion_mem_lorentzSpan (p : TorsionParams) : omegaTorsion p ∈ lorentzSpan := by
  refine Submodule.sum_mem _ fun a _ => Submodule.add_mem _ ?_ ?_
  · exact lorentzSpan.smul_mem _ (hyperbolic_mem_lorentzSpan a)
  · exact lorentzSpan.smul_mem _ (cyclic_mem_lorentzSpan a)

theorem J_dualParams (p : TorsionParams) : Invariant.J (dualParams p) = -Invariant.J p := by
  rw [Invariant.J_coef, Invariant.J_coef]
  simp only [dualParams, Fin.sum_univ_three]
  ring

theorem mass_dualParams (p : TorsionParams) :
    Invariant.mass (dualParams p) = Invariant.mass p := by
  rw [Invariant.mass_coef, Invariant.mass_coef]
  simp only [dualParams, Fin.sum_univ_three]
  ring

theorem JNormalized_dualParams (p : TorsionParams) :
    Invariant.JNormalized (dualParams p) = -Invariant.JNormalized p := by
  unfold Invariant.JNormalized
  rw [J_dualParams]
  ring

/-! ### Packaging as mathlib Lie subalgebras

The bracket is the ring commutator, so closure is the `lie_mem'` field.
-/

section LieStructure

attribute [local instance] LieRing.ofAssociativeRing

theorem commutator_eq_lie (x y : PGA) : commutator x y = ⁅x, y⁆ := rfl

/-- The Lorentz span as a Lie subalgebra of `G(3,1,1)`. -/
noncomputable def lorentzLieSubalgebra : LieSubalgebra ℝ PGA :=
  { lorentzSpan with lie_mem' := fun hx hy => commutator_mem_lorentzSpan hx hy }

/-- The Poincaré span as a Lie subalgebra of `G(3,1,1)`. -/
noncomputable def poincareLieSubalgebra : LieSubalgebra ℝ PGA :=
  { poincareSpan with lie_mem' := fun hx hy => commutator_mem_poincareSpan hx hy }

theorem mem_lorentzLieSubalgebra {x : PGA} : x ∈ lorentzLieSubalgebra ↔ x ∈ lorentzSpan :=
  Iff.rfl

theorem mem_poincareLieSubalgebra {x : PGA} : x ∈ poincareLieSubalgebra ↔ x ∈ poincareSpan :=
  Iff.rfl

end LieStructure

end LorentzLie

end DstDiophantine
