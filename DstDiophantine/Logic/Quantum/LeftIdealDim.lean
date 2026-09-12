import DstDiophantine.Logic.Quantum.CompositeProjector
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Real dimension of the commuting left ideal

Right multiplication by the commuting square-\(+1\) generators \(e_1\) and
\(e_0e_2\) cuts \(G(3,1,1)\) down to an \(8\)-dimensional principal left
ideal. Irreducibility as a spinor module is not claimed.
-/

namespace DstDiophantine

namespace Logic

open PGA Generators LinearMap Module

private theorem mulRight_comp (a b : PGA) :
    (mulRight ℝ b).comp (mulRight ℝ a) = mulRight ℝ (a * b) := by
  ext x; simp [mulRight_apply, mul_assoc]

private theorem mulRight_one :
    (mulRight ℝ (1 : PGA)) = (LinearMap.id : PGA →ₗ[ℝ] PGA) := by
  ext x; simp

private theorem involution_apply {M : Type*} [AddCommGroup M] [Module ℝ M]
    {φ : M →ₗ[ℝ] M} (hφ : φ.comp φ = LinearMap.id) (x : M) : φ (φ x) = x :=
  show (φ.comp φ) x = x by rw [hφ]; rfl

private theorem mem_ker_sub_id {M : Type*} [AddCommGroup M] [Module ℝ M]
    {φ : M →ₗ[ℝ] M} {x : M} (h : x ∈ ker (φ - LinearMap.id)) : φ x = x :=
  sub_eq_zero.mp (show φ x - x = 0 from by
    simpa only [LinearMap.sub_apply, LinearMap.id_apply] using mem_ker.mp h)

private theorem mem_ker_add_id {M : Type*} [AddCommGroup M] [Module ℝ M]
    {φ : M →ₗ[ℝ] M} {x : M} (h : x ∈ ker (φ + LinearMap.id)) : φ x = -x :=
  eq_neg_of_add_eq_zero_left (show φ x + x = 0 from by
    simpa only [LinearMap.add_apply, LinearMap.id_apply] using mem_ker.mp h)

/-- For an involution \(\varphi\), the \(\pm 1\) eigenspaces are complementary. -/
private theorem involution_isCompl {M : Type*} [AddCommGroup M] [Module ℝ M]
    {φ : M →ₗ[ℝ] M} (hφ : φ.comp φ = LinearMap.id) :
    IsCompl (ker (φ - LinearMap.id)) (ker (φ + LinearMap.id)) := by
  constructor
  · rw [disjoint_iff]
    ext x
    constructor
    · intro hx
      have hxφ := mem_ker_sub_id hx.1
      have hxφ' := mem_ker_add_id hx.2
      have : (2 : ℝ) • x = 0 := by
        have : x + x = 0 := by
          calc x + x = φ x + x := by rw [hxφ]
            _ = -x + x := by rw [hxφ']
            _ = 0 := by abel
        simpa [two_smul] using this
      exact (smul_eq_zero.mp this).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
    · intro hx
      rw [Submodule.mem_bot] at hx
      subst hx
      simp
  · rw [codisjoint_iff]
    ext x
    constructor
    · intro; trivial
    · intro
      refine Submodule.mem_sup.mpr ?_
      refine ⟨(1 / 2 : ℝ) • (x + φ x), ?_, (1 / 2 : ℝ) • (x - φ x), ?_, ?_⟩
      · apply mem_ker.mpr
        change φ ((1 / 2 : ℝ) • (x + φ x)) - (1 / 2 : ℝ) • (x + φ x) = 0
        have : φ ((1 / 2 : ℝ) • (x + φ x)) = (1 / 2 : ℝ) • (x + φ x) := by
          rw [map_smul, map_add, involution_apply hφ, add_comm]
        rw [this, sub_self]
      · apply mem_ker.mpr
        change φ ((1 / 2 : ℝ) • (x - φ x)) + (1 / 2 : ℝ) • (x - φ x) = 0
        have : φ ((1 / 2 : ℝ) • (x - φ x)) = -((1 / 2 : ℝ) • (x - φ x)) := by
          rw [map_smul, map_sub, involution_apply hφ]
          module
        rw [this, neg_add_cancel]
      · have h2 : (1 / 2 : ℝ) • ((2 : ℝ) • x) = x := by
          rw [← mul_smul]; norm_num
        calc (1 / 2 : ℝ) • (x + φ x) + (1 / 2 : ℝ) • (x - φ x)
            = (1 / 2 : ℝ) • ((x + φ x) + (x - φ x)) := by rw [← smul_add]
          _ = (1 / 2 : ℝ) • (x + x) := by abel
          _ = (1 / 2 : ℝ) • ((2 : ℝ) • x) := by rw [two_smul]
          _ = x := h2

/-! ### Right multiplication operators -/

noncomputable def rightE1 : PGA →ₗ[ℝ] PGA := mulRight ℝ chiralityGen

theorem rightE1_sq : rightE1.comp rightE1 = LinearMap.id := by
  unfold rightE1; rw [mulRight_comp, chiralityGen_sq, mulRight_one]

noncomputable def rightE0 : PGA →ₗ[ℝ] PGA := mulRight ℝ (ι 0)

theorem rightE0_sq_apply (x : PGA) : rightE0 (rightE0 x) = -x := by
  calc rightE0 (rightE0 x)
      = (x * ι 0) * ι 0 := by simp [rightE0, mulRight_apply]
    _ = x * (ι 0 * ι 0) := by rw [mul_assoc]
    _ = x * algebraMap ℝ PGA (-1) := by rw [e0_sq]
    _ = (-1 : ℝ) • x := by simp [Algebra.smul_def, mul_comm]
    _ = -x := by simp [neg_smul]

theorem rightE1_anticomm_e0_apply (x : PGA) :
    rightE1 (rightE0 x) = -rightE0 (rightE1 x) := by
  have h : ι 0 * chiralityGen = -(chiralityGen * ι 0) :=
    e_mul_anticomm (by decide : (0 : Fin 5) ≠ 1)
  calc rightE1 (rightE0 x)
      = (x * ι 0) * chiralityGen := by simp [rightE1, rightE0, mulRight_apply]
    _ = x * (ι 0 * chiralityGen) := by rw [mul_assoc]
    _ = x * (-(chiralityGen * ι 0)) := by rw [h]
    _ = -((x * chiralityGen) * ι 0) := by simp [mul_neg, mul_assoc]
    _ = -rightE0 (rightE1 x) := by simp [rightE1, rightE0, mulRight_apply]

/-- Swap \(+1\) and \(-1\) eigenspaces of `rightE1` via right multiplication by \(e_0\). -/
noncomputable def rightE0_plusToMinus :
    ker (rightE1 - LinearMap.id) ≃ₗ[ℝ] ker (rightE1 + LinearMap.id) where
  toFun x :=
    ⟨rightE0 x.1, by
      apply mem_ker.mpr
      change rightE1 (rightE0 x.1) + rightE0 x.1 = 0
      rw [rightE1_anticomm_e0_apply, mem_ker_sub_id x.2, neg_add_cancel]⟩
  invFun y :=
    ⟨-rightE0 y.1, by
      apply mem_ker.mpr
      change rightE1 (-rightE0 y.1) - (-rightE0 y.1) = 0
      have hy := mem_ker_add_id y.2
      rw [map_neg, rightE1_anticomm_e0_apply, hy, map_neg]
      abel⟩
  left_inv x := by
    apply Subtype.ext
    simp [rightE0_sq_apply]
  right_inv y := by
    apply Subtype.ext
    simp [rightE0_sq_apply]
  map_add' x y := Subtype.ext (by simp [map_add])
  map_smul' c x := Subtype.ext (by simp [map_smul])

theorem finrank_ker_rightE1_plus : finrank ℝ (ker (rightE1 - LinearMap.id)) = 16 := by
  have hsum := Submodule.finrank_add_eq_of_isCompl (involution_isCompl rightE1_sq)
  rw [finrank_pga] at hsum
  have heq := LinearEquiv.finrank_eq rightE0_plusToMinus
  linarith

/-! ### \(e_0e_2\) and the complementary involution \(e_0e_3\) -/

noncomputable def rightHyp1 : PGA →ₗ[ℝ] PGA := mulRight ℝ (hyperbolic 1)

theorem rightHyp1_sq : rightHyp1.comp rightHyp1 = LinearMap.id := by
  unfold rightHyp1; rw [mulRight_comp, hyperbolic_sq 1, mulRight_one]

noncomputable def boost03 : PGA := ι 0 * ι 3

private theorem e3_sq' : ι 3 * ι 3 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (3 : Fin 5)

theorem boost03_sq : boost03 * boost03 = 1 := by
  unfold boost03
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h :
      ι 0 * ι 3 * (ι 0 * ι 3) = -algebraMap ℝ PGA (-1) := by
    calc ι 0 * ι 3 * (ι 0 * ι 3)
        = ι 0 * (ι 3 * ι 0) * ι 3 := by simp [mul_assoc]
      _ = ι 0 * (-(ι 0 * ι 3)) * ι 3 := by rw [h30]
      _ = -(ι 0 * ι 0) * (ι 3 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -algebraMap ℝ PGA (-1) := by rw [e0_sq, e3_sq']; simp
  calc boost03 * boost03
      = ι 0 * ι 3 * (ι 0 * ι 3) := rfl
    _ = -algebraMap ℝ PGA (-1) := h
    _ = 1 := by simp [Algebra.algebraMap_eq_smul_one, neg_smul]

theorem boost03_anticomm_hyp1 :
    boost03 * hyperbolic 1 = -(hyperbolic 1 * boost03) := by
  unfold boost03 hyperbolic
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  have hL : ι 0 * ι 3 * (ι 0 * ι 2) = -(ι 2 * ι 3) := by
    calc ι 0 * ι 3 * (ι 0 * ι 2)
        = ι 0 * (ι 3 * ι 0) * ι 2 := by simp [mul_assoc]
      _ = ι 0 * (-(ι 0 * ι 3)) * ι 2 := by rw [h30]
      _ = -(ι 0 * ι 0) * (ι 3 * ι 2) := by simp [mul_neg, mul_assoc]
      _ = ι 3 * ι 2 := by
            rw [e0_sq]
            simp [Algebra.algebraMap_eq_smul_one, neg_smul, mul_assoc]
      _ = -(ι 2 * ι 3) := h32
  have hR : ι 0 * ι 2 * (ι 0 * ι 3) = ι 2 * ι 3 := by
    calc ι 0 * ι 2 * (ι 0 * ι 3)
        = ι 0 * (ι 2 * ι 0) * ι 3 := by simp [mul_assoc]
      _ = ι 0 * (-(ι 0 * ι 2)) * ι 3 := by rw [h20]
      _ = -(ι 0 * ι 0) * (ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = ι 2 * ι 3 := by
            rw [e0_sq]
            simp [Algebra.algebraMap_eq_smul_one, neg_smul, mul_assoc]
  calc boost03 * hyperbolic 1
      = ι 0 * ι 3 * (ι 0 * ι 2) := rfl
    _ = -(ι 2 * ι 3) := hL
    _ = -(ι 0 * ι 2 * (ι 0 * ι 3)) := by rw [hR]
    _ = -(hyperbolic 1 * boost03) := rfl

theorem boost03_comm_e1 : Commute boost03 chiralityGen := by
  change boost03 * chiralityGen = chiralityGen * boost03
  unfold boost03 chiralityGen
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  calc ι 0 * ι 3 * ι 1
      = ι 0 * (ι 3 * ι 1) := by simp [mul_assoc]
    _ = ι 0 * (-(ι 1 * ι 3)) := by rw [h31]
    _ = -(ι 0 * ι 1) * ι 3 := by simp [mul_neg, mul_assoc]
    _ = (ι 1 * ι 0) * ι 3 := by rw [← h10]
    _ = ι 1 * (ι 0 * ι 3) := by simp [mul_assoc]

noncomputable def rightBoost03 : PGA →ₗ[ℝ] PGA := mulRight ℝ boost03

theorem rightBoost03_sq_apply (x : PGA) : rightBoost03 (rightBoost03 x) = x := by
  calc rightBoost03 (rightBoost03 x)
      = (x * boost03) * boost03 := by simp [rightBoost03, mulRight_apply]
    _ = x * (boost03 * boost03) := by rw [mul_assoc]
    _ = x * 1 := by rw [boost03_sq]
    _ = x := by simp

theorem rightHyp1_anticomm_boost03_apply (x : PGA) :
    rightHyp1 (rightBoost03 x) = -rightBoost03 (rightHyp1 x) := by
  calc rightHyp1 (rightBoost03 x)
      = (x * boost03) * hyperbolic 1 := by
          simp [rightHyp1, rightBoost03, mulRight_apply]
    _ = x * (boost03 * hyperbolic 1) := by rw [mul_assoc]
    _ = x * (-(hyperbolic 1 * boost03)) := by rw [boost03_anticomm_hyp1]
    _ = -((x * hyperbolic 1) * boost03) := by simp [mul_neg, mul_assoc]
    _ = -rightBoost03 (rightHyp1 x) := by
          simp [rightHyp1, rightBoost03, mulRight_apply]

/-- `rightHyp1` preserves the \(+1\) eigenspace of `rightE1`. -/
noncomputable def rightHyp1OnE1Plus :
    ker (rightE1 - LinearMap.id) →ₗ[ℝ] ker (rightE1 - LinearMap.id) where
  toFun x :=
    ⟨rightHyp1 x.1, by
      apply mem_ker.mpr
      change rightHyp1 x.1 * chiralityGen - rightHyp1 x.1 = 0
      have hx := mem_ker_sub_id x.2
      have hc : chiralityGen * hyperbolic 1 = hyperbolic 1 * chiralityGen :=
        commute_chiralityGen_hyperbolic1
      have : rightHyp1 x.1 * chiralityGen = rightHyp1 (x.1 * chiralityGen) := by
        simp [rightHyp1, mulRight_apply, mul_assoc, hc]
      have hx' : x.1 * chiralityGen = x.1 := by
        simpa [rightE1, mulRight_apply] using hx
      rw [this, hx', sub_self]⟩
  map_add' x y := Subtype.ext (by simp [map_add])
  map_smul' c x := Subtype.ext (by simp [map_smul])

theorem rightHyp1OnE1Plus_sq :
    rightHyp1OnE1Plus.comp rightHyp1OnE1Plus = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  change rightHyp1 (rightHyp1 x.1) = x.1
  exact show (rightHyp1.comp rightHyp1) x.1 = x.1 by rw [rightHyp1_sq]; rfl

noncomputable def rightBoost03OnE1Plus :
    ker (rightE1 - LinearMap.id) →ₗ[ℝ] ker (rightE1 - LinearMap.id) where
  toFun x :=
    ⟨rightBoost03 x.1, by
      apply mem_ker.mpr
      change rightBoost03 x.1 * chiralityGen - rightBoost03 x.1 = 0
      have hx := mem_ker_sub_id x.2
      have hc : boost03 * chiralityGen = chiralityGen * boost03 := boost03_comm_e1
      have : rightBoost03 x.1 * chiralityGen = rightBoost03 (x.1 * chiralityGen) := by
        simp [rightBoost03, mulRight_apply, mul_assoc, hc]
      have hx' : x.1 * chiralityGen = x.1 := by
        simpa [rightE1, mulRight_apply] using hx
      rw [this, hx', sub_self]⟩
  map_add' x y := Subtype.ext (by simp [map_add])
  map_smul' c x := Subtype.ext (by simp [map_smul])

noncomputable def rightBoost03_hypPlusToMinus :
    ker (rightHyp1OnE1Plus - LinearMap.id) ≃ₗ[ℝ]
      ker (rightHyp1OnE1Plus + LinearMap.id) where
  toFun x :=
    ⟨rightBoost03OnE1Plus x.1, by
      apply mem_ker.mpr
      change rightHyp1OnE1Plus (rightBoost03OnE1Plus x.1) + rightBoost03OnE1Plus x.1 = 0
      have hx := mem_ker_sub_id (φ := rightHyp1OnE1Plus) x.2
      have hanti : rightHyp1OnE1Plus (rightBoost03OnE1Plus x.1) =
          -rightBoost03OnE1Plus (rightHyp1OnE1Plus x.1) := by
        apply Subtype.ext
        exact rightHyp1_anticomm_boost03_apply x.1.1
      rw [hanti, hx, neg_add_cancel]⟩
  invFun y :=
    ⟨rightBoost03OnE1Plus y.1, by
      -- R03² = +1, so the same map swaps the ± eigenspaces of R_h
      apply mem_ker.mpr
      change rightHyp1OnE1Plus (rightBoost03OnE1Plus y.1) - rightBoost03OnE1Plus y.1 = 0
      have hy := mem_ker_add_id (φ := rightHyp1OnE1Plus) y.2
      have hanti : rightHyp1OnE1Plus (rightBoost03OnE1Plus y.1) =
          -rightBoost03OnE1Plus (rightHyp1OnE1Plus y.1) := by
        apply Subtype.ext
        exact rightHyp1_anticomm_boost03_apply y.1.1
      rw [hanti, hy, map_neg, neg_neg, sub_self]⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext ?_)
    change rightBoost03 (rightBoost03 x.1.1) = x.1.1
    exact rightBoost03_sq_apply x.1.1
  right_inv y := by
    refine Subtype.ext (Subtype.ext ?_)
    change rightBoost03 (rightBoost03 y.1.1) = y.1.1
    exact rightBoost03_sq_apply y.1.1
  map_add' x y := Subtype.ext (by simp [map_add])
  map_smul' c x := Subtype.ext (by simp [map_smul])

theorem finrank_ker_rightHyp1_on_e1Plus :
    finrank ℝ (ker (rightHyp1OnE1Plus - LinearMap.id)) = 8 := by
  have hdim16 : finrank ℝ (ker (rightE1 - LinearMap.id)) = 16 :=
    finrank_ker_rightE1_plus
  have hsum :=
    Submodule.finrank_add_eq_of_isCompl (involution_isCompl rightHyp1OnE1Plus_sq)
  have heq := LinearEquiv.finrank_eq rightBoost03_hypPlusToMinus
  have hsum' :
      finrank ℝ (ker (rightHyp1OnE1Plus - LinearMap.id)) +
        finrank ℝ (ker (rightHyp1OnE1Plus + LinearMap.id)) = 16 := by
    simpa [hdim16] using hsum
  linarith

/-! ### Identify the left ideal with the double \(+1\) eigenspace -/

theorem chiralityR_mul_chiralityGen : chiralityR * chiralityGen = chiralityR := by
  unfold chiralityR
  have hhalf : half * chiralityGen = chiralityGen * half := half_comm _
  calc ((1 : PGA) + chiralityGen) * half * chiralityGen
      = ((1 : PGA) + chiralityGen) * chiralityGen * half := by simp [mul_assoc, hhalf]
    _ = (chiralityGen + chiralityGen * chiralityGen) * half := by simp [add_mul]
    _ = ((1 : PGA) + chiralityGen) * half := by rw [chiralityGen_sq]; simp [add_comm]

theorem spinorIdemAxis1_mul_hyp1 :
    spinorIdemAxis1 * hyperbolic 1 = spinorIdemAxis1 := by
  unfold spinorIdemAxis1
  have hhalf : half * hyperbolic 1 = hyperbolic 1 * half := half_comm _
  calc ((1 : PGA) + hyperbolic 1) * half * hyperbolic 1
      = ((1 : PGA) + hyperbolic 1) * hyperbolic 1 * half := by simp [mul_assoc, hhalf]
    _ = (hyperbolic 1 + hyperbolic 1 * hyperbolic 1) * half := by simp [add_mul]
    _ = ((1 : PGA) + hyperbolic 1) * half := by rw [hyperbolic_sq 1]; simp [add_comm]

theorem commute_spinorIdemAxis1_chiralityGen :
    Commute spinorIdemAxis1 chiralityGen := by
  change spinorIdemAxis1 * chiralityGen = chiralityGen * spinorIdemAxis1
  unfold spinorIdemAxis1
  have hc : chiralityGen * hyperbolic 1 = hyperbolic 1 * chiralityGen :=
    commute_chiralityGen_hyperbolic1
  have hhalf : half * chiralityGen = chiralityGen * half := half_comm _
  calc ((1 : PGA) + hyperbolic 1) * half * chiralityGen
      = ((1 : PGA) + hyperbolic 1) * chiralityGen * half := by simp [mul_assoc, hhalf]
    _ = (chiralityGen + hyperbolic 1 * chiralityGen) * half := by simp [add_mul, hc]
    _ = chiralityGen * ((1 : PGA) + hyperbolic 1) * half := by simp [mul_add, hc]
    _ = chiralityGen * (((1 : PGA) + hyperbolic 1) * half) := by simp [mul_assoc]

theorem commutingSpinorIdem_mul_chiralityGen :
    commutingSpinorIdem * chiralityGen = commutingSpinorIdem := by
  unfold commutingSpinorIdem
  calc chiralityR * spinorIdemAxis1 * chiralityGen
      = chiralityR * (spinorIdemAxis1 * chiralityGen) := by simp [mul_assoc]
    _ = chiralityR * (chiralityGen * spinorIdemAxis1) := by
          rw [commute_spinorIdemAxis1_chiralityGen]
    _ = (chiralityR * chiralityGen) * spinorIdemAxis1 := by simp [mul_assoc]
    _ = chiralityR * spinorIdemAxis1 := by rw [chiralityR_mul_chiralityGen]

theorem commutingSpinorIdem_mul_hyp1 :
    commutingSpinorIdem * hyperbolic 1 = commutingSpinorIdem := by
  unfold commutingSpinorIdem
  have hc : chiralityR * hyperbolic 1 = hyperbolic 1 * chiralityR := by
    unfold chiralityR
    have hg : chiralityGen * hyperbolic 1 = hyperbolic 1 * chiralityGen :=
      commute_chiralityGen_hyperbolic1
    have hhalf : half * hyperbolic 1 = hyperbolic 1 * half := half_comm _
    calc ((1 : PGA) + chiralityGen) * half * hyperbolic 1
        = ((1 : PGA) + chiralityGen) * hyperbolic 1 * half := by simp [mul_assoc, hhalf]
      _ = (hyperbolic 1 + chiralityGen * hyperbolic 1) * half := by simp [add_mul, hg]
      _ = hyperbolic 1 * ((1 : PGA) + chiralityGen) * half := by simp [mul_add, hg]
      _ = hyperbolic 1 * (((1 : PGA) + chiralityGen) * half) := by simp [mul_assoc]
  calc chiralityR * spinorIdemAxis1 * hyperbolic 1
      = chiralityR * (spinorIdemAxis1 * hyperbolic 1) := by simp [mul_assoc]
    _ = chiralityR * spinorIdemAxis1 := by rw [spinorIdemAxis1_mul_hyp1]

theorem mem_leftIdeal_iff_fixed (x : PGA) :
    x ∈ leftIdealSub commutingSpinorIdem ↔
      x * chiralityGen = x ∧ x * hyperbolic 1 = x := by
  constructor
  · intro hx
    rcases (mem_leftIdealSub_iff).mp hx with ⟨a, rfl⟩
    exact ⟨by rw [mul_assoc, commutingSpinorIdem_mul_chiralityGen],
      by rw [mul_assoc, commutingSpinorIdem_mul_hyp1]⟩
  · intro ⟨he1, hh⟩
    have hR : x * chiralityR = x := by
      unfold chiralityR
      have h2 : x * ((1 : PGA) + chiralityGen) = (2 : ℝ) • x := by
        calc x * ((1 : PGA) + chiralityGen)
            = x + x * chiralityGen := by simp [mul_add]
          _ = x + x := by rw [he1]
          _ = (2 : ℝ) • x := by rw [two_smul]
      calc x * (((1 : PGA) + chiralityGen) * half)
          = (x * ((1 : PGA) + chiralityGen)) * half := by simp [mul_assoc]
        _ = ((2 : ℝ) • x) * half := by rw [h2]
        _ = x * (algebraMap ℝ PGA 2 * half) := by
              simp [Algebra.smul_def, mul_assoc, Algebra.commutes]
        _ = x := by rw [two_mul_half, mul_one]
    have hS : x * spinorIdemAxis1 = x := by
      unfold spinorIdemAxis1
      have h2 : x * ((1 : PGA) + hyperbolic 1) = (2 : ℝ) • x := by
        calc x * ((1 : PGA) + hyperbolic 1)
            = x + x * hyperbolic 1 := by simp [mul_add]
          _ = x + x := by rw [hh]
          _ = (2 : ℝ) • x := by rw [two_smul]
      calc x * (((1 : PGA) + hyperbolic 1) * half)
          = (x * ((1 : PGA) + hyperbolic 1)) * half := by simp [mul_assoc]
        _ = ((2 : ℝ) • x) * half := by rw [h2]
        _ = x * (algebraMap ℝ PGA 2 * half) := by
              simp [Algebra.smul_def, mul_assoc, Algebra.commutes]
        _ = x := by rw [two_mul_half, mul_one]
    have hP : x * commutingSpinorIdem = x := by
      unfold commutingSpinorIdem
      calc x * (chiralityR * spinorIdemAxis1)
          = (x * chiralityR) * spinorIdemAxis1 := by simp [mul_assoc]
        _ = x * spinorIdemAxis1 := by rw [hR]
        _ = x := hS
    exact (mem_leftIdealSub_iff).mpr ⟨x, hP.symm⟩

/-- The double \(+1\) eigenspace equals the principal left ideal. -/
noncomputable def leftIdealEquivDoublePlus :
    leftIdealSub commutingSpinorIdem ≃ₗ[ℝ]
      ker (rightHyp1OnE1Plus - LinearMap.id) where
  toFun x :=
    ⟨⟨x.1, by
        have hx := (mem_leftIdeal_iff_fixed x.1).mp x.2
        apply mem_ker.mpr
        change x.1 * chiralityGen - x.1 = 0
        rw [hx.1, sub_self]⟩,
      by
        have hx := (mem_leftIdeal_iff_fixed x.1).mp x.2
        apply mem_ker.mpr
        change rightHyp1OnE1Plus ⟨x.1, _⟩ - ⟨x.1, _⟩ = 0
        apply Subtype.ext
        change rightHyp1 x.1 - x.1 = 0
        simpa [rightHyp1, mulRight_apply] using sub_eq_zero.mpr hx.2⟩
  invFun y :=
    ⟨y.1.1, by
      have hyE1 := mem_ker_sub_id y.1.2
      have hyH := mem_ker_sub_id (φ := rightHyp1OnE1Plus) y.2
      have h1 : y.1.1 * chiralityGen = y.1.1 := by
        simpa [rightE1, mulRight_apply] using hyE1
      have h2 : y.1.1 * hyperbolic 1 = y.1.1 := by
        have := congrArg Subtype.val hyH
        simpa [rightHyp1OnE1Plus, rightHyp1, mulRight_apply] using this
      exact (mem_leftIdeal_iff_fixed y.1.1).mpr ⟨h1, h2⟩⟩
  left_inv x := rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' c x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Real dimension of the commuting left ideal is exactly \(8\). -/
theorem finrank_leftIdeal_commuting :
    finrank ℝ (leftIdealSub commutingSpinorIdem) = 8 := by
  rw [LinearEquiv.finrank_eq leftIdealEquivDoublePlus]
  exact finrank_ker_rightHyp1_on_e1Plus

end Logic

end DstDiophantine
