import DstDiophantine.Logic.Quantum.LeftIdealDim
import DstDiophantine.Algebra.Cl91
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Null doubling of the commuting left ideal

The commuting projector \(P\) lives in the Minkowski subalgebra. The
principal left ideal \(\mathcal{I}=G(3,1,1)\,P\) therefore splits as
\(\mathcal{I}_0\oplus e_4\mathcal{I}_0\), where
\(\mathcal{I}_0=\mathrm{Cl}(3,1)\,P\) is four-dimensional. The null
copy is a proper left \(G(3,1,1)\)-submodule, so \(\mathcal{I}\) is
reducible as a PGA-module.

Irreducibility of \(\mathcal{I}_0\) as a \(\mathrm{Cl}(3,1)\)-module is
not claimed, nor is an identification with the matrix representation on
\(\mathbb{C}^4\).
-/

namespace DstDiophantine

namespace Logic

open PGA Generators LinearMap Module CliffordAlgebra

/-! ### Minkowski image and the null copy -/

/-- Image of the Minkowski embedding. -/
noncomputable def minkowskiSub : Submodule ℝ PGA :=
  LinearMap.range Cl31.toPGA.toLinearMap

theorem mem_minkowskiSub {x : PGA} :
    x ∈ minkowskiSub ↔ ∃ c : Cl31, Cl31.toPGA c = x :=
  LinearMap.mem_range

theorem minkowskiSub_mul {x y : PGA}
    (hx : x ∈ minkowskiSub) (hy : y ∈ minkowskiSub) :
    x * y ∈ minkowskiSub := by
  rcases (mem_minkowskiSub.mp hx) with ⟨c, rfl⟩
  rcases (mem_minkowskiSub.mp hy) with ⟨d, rfl⟩
  exact ⟨c * d, map_mul (Cl31.toPGA : Cl31 →ₐ[ℝ] PGA) c d⟩

theorem minkowskiSub_add {x y : PGA}
    (hx : x ∈ minkowskiSub) (hy : y ∈ minkowskiSub) :
    x + y ∈ minkowskiSub :=
  Submodule.add_mem _ hx hy

theorem algebraMap_mem_minkowski (r : ℝ) :
    algebraMap ℝ PGA r ∈ minkowskiSub :=
  ⟨algebraMap ℝ Cl31 r, AlgHom.commutes Cl31.toPGA r⟩

theorem half_mem_minkowski : half ∈ minkowskiSub :=
  algebraMap_mem_minkowski _

theorem one_mem_minkowski : (1 : PGA) ∈ minkowskiSub :=
  algebraMap_mem_minkowski 1

theorem chiralityGen_mem_minkowski : chiralityGen ∈ minkowskiSub := by
  unfold chiralityGen
  refine ⟨Cl31.ι 1, ?_⟩
  change Cl31.toPGA (Cl31.ι 1) = PGA.ι 1
  rw [Cl31.toPGA_ι]
  rfl

theorem hyperbolic1_mem_minkowski : hyperbolic 1 ∈ minkowskiSub := by
  refine ⟨Cl31.ι 0 * Cl31.ι 2, ?_⟩
  change Cl31.toPGA (Cl31.ι 0 * Cl31.ι 2) = hyperbolic 1
  have hmul : Cl31.toPGA (Cl31.ι 0 * Cl31.ι 2) =
      Cl31.toPGA (Cl31.ι 0) * Cl31.toPGA (Cl31.ι 2) :=
    map_mul (Cl31.toPGA : Cl31 →ₐ[ℝ] PGA) _ _
  rw [hmul, Cl31.toPGA_ι, Cl31.toPGA_ι]
  rfl

theorem commutingSpinorIdem_mem_minkowski :
    commutingSpinorIdem ∈ minkowskiSub := by
  unfold commutingSpinorIdem chiralityR spinorIdemAxis1
  exact minkowskiSub_mul
    (minkowskiSub_mul (minkowskiSub_add one_mem_minkowski chiralityGen_mem_minkowski)
      half_mem_minkowski)
    (minkowskiSub_mul (minkowskiSub_add one_mem_minkowski hyperbolic1_mem_minkowski)
      half_mem_minkowski)

theorem finrank_minkowskiSub : finrank ℝ minkowskiSub = 16 := by
  have hinj : Function.Injective Cl31.toPGA.toLinearMap := by
    intro x y hxy
    exact Cl31.toPGA_injective (by simpa using hxy)
  have e := LinearEquiv.ofInjective Cl31.toPGA.toLinearMap hinj
  have h := LinearEquiv.finrank_eq e
  have h16 : finrank ℝ Cl31 = 16 := Cl91.finrank_cl31
  rw [h16] at h
  exact h.symm

/-- The complementary copy \(e_4\,\mathrm{Cl}(3,1)\) inside \(G(3,1,1)\). -/
noncomputable def nullMinkowski : Submodule ℝ PGA :=
  Submodule.map (mulLeft ℝ (PGA.ι PGA.e4Index)) minkowskiSub

theorem mem_nullMinkowski {x : PGA} :
    x ∈ nullMinkowski ↔
      ∃ y ∈ minkowskiSub, PGA.ι PGA.e4Index * y = x :=
  Submodule.mem_map

theorem minkowski_disjoint_nullMinkowski :
    Disjoint minkowskiSub nullMinkowski := by
  rw [disjoint_iff]
  ext x
  constructor
  · intro hx
    rcases (mem_minkowskiSub.mp hx.1) with ⟨c, rfl⟩
    rcases hx.2 with ⟨y, _, hxy⟩
    have hc : c = 0 := by
      have h := congrArg Cl31.ofPGA hxy
      simp only [mulLeft_apply, Cl31.ofPGA_mul_e4, Cl31.ofPGA_toPGA] at h
      exact h.symm
    rw [hc, map_zero]
    simp
  · intro hx
    rw [Submodule.mem_bot] at hx
    subst hx
    simp

private theorem toPGA_ι_mul (x : Cl31) (m : Vec4) :
    Cl31.toPGA (CliffordAlgebra.ι Q31 m * x) =
      CliffordAlgebra.ι Q311 (extend4 m) * Cl31.toPGA x := by
  rw [map_mul, Cl31.toPGA_eq_map, CliffordAlgebra.map_apply_ι]
  rfl

theorem minkowski_ι_extend_mul {y : PGA} (hy : y ∈ minkowskiSub) (m : Vec4) :
    CliffordAlgebra.ι Q311 (extend4 m) * y ∈ minkowskiSub := by
  rcases (mem_minkowskiSub.mp hy) with ⟨c, rfl⟩
  exact ⟨CliffordAlgebra.ι Q31 m * c, toPGA_ι_mul c m⟩

theorem ι_vec5_decomp (v : Vec5) :
    CliffordAlgebra.ι Q311 v =
      CliffordAlgebra.ι Q311 (extend4 (restrict4 v)) +
        v 4 • PGA.ι PGA.e4Index := by
  conv_lhs => rw [← extend4_restrict4_add_last v]
  rw [map_add, map_smul]
  rfl

theorem ι_extend4_mul_e4 (m : Vec4) (w : PGA) :
    CliffordAlgebra.ι Q311 (extend4 m) * (PGA.ι PGA.e4Index * w) =
      -(PGA.ι PGA.e4Index *
          (CliffordAlgebra.ι Q311 (extend4 m) * w)) := by
  have h' : CliffordAlgebra.ι Q311 (extend4 m) * PGA.ι PGA.e4Index =
      -(PGA.ι PGA.e4Index * CliffordAlgebra.ι Q311 (extend4 m)) :=
    (neg_eq_iff_eq_neg.mpr (e4_mul_ι_vec (extend4 m))).symm
  calc CliffordAlgebra.ι Q311 (extend4 m) * (PGA.ι PGA.e4Index * w)
      = (CliffordAlgebra.ι Q311 (extend4 m) * PGA.ι PGA.e4Index) * w := by
        rw [mul_assoc]
    _ = (-(PGA.ι PGA.e4Index * CliffordAlgebra.ι Q311 (extend4 m))) * w := by
        rw [h']
    _ = -(PGA.ι PGA.e4Index *
            (CliffordAlgebra.ι Q311 (extend4 m) * w)) := by
        simp [mul_assoc]

theorem e4_mul_e4_mul (w : PGA) :
    PGA.ι PGA.e4Index * (PGA.ι PGA.e4Index * w) = 0 := by
  rw [← mul_assoc, e4_sq_zero, zero_mul]

/-- Every PGA element is a Minkowski part plus an \(e_4\) copy. -/
theorem minkowski_sup_nullMinkowski :
    minkowskiSub ⊔ nullMinkowski = ⊤ := by
  have hxall (x : PGA) : x ∈ minkowskiSub ⊔ nullMinkowski := by
    induction x using CliffordAlgebra.left_induction with
    | algebraMap r =>
      exact Submodule.mem_sup_left (algebraMap_mem_minkowski r)
    | add a b ha hb =>
      exact add_mem ha hb
    | ι_mul x m ih =>
      rcases Submodule.mem_sup.mp ih with ⟨y, hy, z, hz, hxz⟩
      rcases hz with ⟨w, hw, rfl⟩
      have hy1 :
          CliffordAlgebra.ι Q311 (extend4 (restrict4 m)) * y ∈ minkowskiSub :=
        minkowski_ι_extend_mul hy (restrict4 m)
      have hy2 : PGA.ι PGA.e4Index * y ∈ nullMinkowski :=
        ⟨y, hy, rfl⟩
      have hw1 :
          CliffordAlgebra.ι Q311 (extend4 (restrict4 m)) * w ∈ minkowskiSub :=
        minkowski_ι_extend_mul hw (restrict4 m)
      have hz1 :
          CliffordAlgebra.ι Q311 (extend4 (restrict4 m)) *
              (PGA.ι PGA.e4Index * w) ∈ nullMinkowski := by
        rw [ι_extend4_mul_e4]
        exact neg_mem ⟨_, hw1, rfl⟩
      have hdecomp := ι_vec5_decomp m
      have hxeq :
          CliffordAlgebra.ι Q311 m * x =
            CliffordAlgebra.ι Q311 (extend4 (restrict4 m)) * y +
              m 4 • (PGA.ι PGA.e4Index * y) +
              CliffordAlgebra.ι Q311 (extend4 (restrict4 m)) *
                (PGA.ι PGA.e4Index * w) +
              m 4 • (PGA.ι PGA.e4Index * (PGA.ι PGA.e4Index * w)) := by
        rw [← hxz]
        simp only [mulLeft_apply]
        rw [hdecomp, add_mul, mul_add, mul_add]
        simp only [smul_mul_assoc]
        abel
      rw [hxeq, e4_mul_e4_mul, smul_zero, add_zero]
      refine add_mem
        (add_mem (Submodule.mem_sup_left hy1)
          (Submodule.smul_mem _ _ (Submodule.mem_sup_right hy2)))
        (Submodule.mem_sup_right hz1)
  exact eq_top_iff.mpr fun x _ => hxall x

theorem finrank_nullMinkowski : finrank ℝ nullMinkowski = 16 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    minkowskiSub nullMinkowski
  have htop : minkowskiSub ⊔ nullMinkowski = ⊤ := minkowski_sup_nullMinkowski
  have hbot : minkowskiSub ⊓ nullMinkowski = ⊥ :=
    minkowski_disjoint_nullMinkowski.eq_bot
  rw [htop, hbot, finrank_top, finrank_bot, finrank_pga, finrank_minkowskiSub]
    at hsum
  linarith

noncomputable def mulE4OnMinkowski : minkowskiSub →ₗ[ℝ] PGA :=
  (mulLeft ℝ (PGA.ι PGA.e4Index)).comp minkowskiSub.subtype

theorem range_mulE4OnMinkowski : LinearMap.range mulE4OnMinkowski = nullMinkowski := by
  unfold mulE4OnMinkowski nullMinkowski
  rw [LinearMap.range_comp, Submodule.range_subtype]

theorem mulLeft_e4_injective_on_minkowski {x : PGA}
    (hx : x ∈ minkowskiSub) (h : PGA.ι PGA.e4Index * x = 0) : x = 0 := by
  have hr := LinearMap.finrank_range_add_finrank_ker mulE4OnMinkowski
  rw [range_mulE4OnMinkowski, finrank_nullMinkowski, finrank_minkowskiSub] at hr
  have hker0 : finrank ℝ (ker mulE4OnMinkowski) = 0 := by linarith
  have hbot : ker mulE4OnMinkowski = ⊥ := Submodule.finrank_eq_zero.mp hker0
  have hx0 : (⟨x, hx⟩ : minkowskiSub) ∈ ker mulE4OnMinkowski := by
    apply mem_ker.mpr
    change PGA.ι PGA.e4Index * x = 0
    exact h
  rw [hbot, Submodule.mem_bot] at hx0
  exact Subtype.ext_iff.mp hx0

theorem exists_minkowski_split (a : PGA) :
    ∃ a0 a1, a0 ∈ minkowskiSub ∧ a1 ∈ minkowskiSub ∧
      a = a0 + PGA.ι PGA.e4Index * a1 := by
  have ha : a ∈ minkowskiSub ⊔ nullMinkowski := by
    rw [minkowski_sup_nullMinkowski]
    trivial
  rcases Submodule.mem_sup.mp ha with ⟨a0, ha0, z, hz, rfl⟩
  rcases hz with ⟨a1, ha1, rfl⟩
  exact ⟨a0, a1, ha0, ha1, rfl⟩

/-! ### Minkowski core of the commuting left ideal -/

noncomputable def minkowskiLeftIdeal : Submodule ℝ PGA :=
  leftIdealSub commutingSpinorIdem ⊓ minkowskiSub

theorem commutingSpinorIdem_mem_minkowskiLeftIdeal :
    commutingSpinorIdem ∈ minkowskiLeftIdeal :=
  ⟨commutingSpinorIdem_mem_leftIdealSub, commutingSpinorIdem_mem_minkowski⟩

theorem leftIdeal_mul_P {x : PGA} (hx : x ∈ leftIdealSub commutingSpinorIdem) :
    x * commutingSpinorIdem = x := by
  rcases (mem_leftIdealSub_iff).mp hx with ⟨a, rfl⟩
  rw [mul_assoc, commutingSpinorIdem_sq]

noncomputable def nullSlice : Submodule ℝ PGA :=
  Submodule.map (mulLeft ℝ (PGA.ι PGA.e4Index)) minkowskiLeftIdeal

theorem nullSlice_le_leftIdeal :
    nullSlice ≤ leftIdealSub commutingSpinorIdem := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rcases (mem_leftIdealSub_iff).mp hy.1 with ⟨a, rfl⟩
  exact (mem_leftIdealSub_iff).mpr ⟨PGA.ι PGA.e4Index * a, by simp [mul_assoc]⟩

theorem nullSlice_le_nullMinkowski : nullSlice ≤ nullMinkowski := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, hy.2, rfl⟩

theorem minkowskiLeftIdeal_disjoint_nullSlice :
    Disjoint minkowskiLeftIdeal nullSlice := by
  rw [disjoint_iff]
  ext x
  constructor
  · intro hx
    have hbot := minkowski_disjoint_nullMinkowski.le_bot
      ⟨hx.1.2, nullSlice_le_nullMinkowski hx.2⟩
    exact hbot
  · intro hx
    rw [Submodule.mem_bot] at hx
    subst hx
    simp

noncomputable def mulE4OnI0 : minkowskiLeftIdeal →ₗ[ℝ] PGA :=
  (mulLeft ℝ (PGA.ι PGA.e4Index)).comp minkowskiLeftIdeal.subtype

theorem mulE4OnI0_injective : Function.Injective mulE4OnI0 := by
  intro x y hxy
  apply Subtype.ext
  have : PGA.ι PGA.e4Index * (x.1 - y.1) = 0 := by
    simpa [mulE4OnI0, mul_sub] using congrArg (fun z => z - mulE4OnI0 y) hxy
  exact eq_of_sub_eq_zero
    (mulLeft_e4_injective_on_minkowski (Submodule.sub_mem _ x.2.2 y.2.2) this)

theorem range_mulE4OnI0 : LinearMap.range mulE4OnI0 = nullSlice := by
  unfold mulE4OnI0 nullSlice
  rw [LinearMap.range_comp, Submodule.range_subtype]

theorem finrank_nullSlice_eq_minkowskiLeftIdeal :
    finrank ℝ nullSlice = finrank ℝ minkowskiLeftIdeal := by
  have e := LinearEquiv.ofInjective mulE4OnI0 mulE4OnI0_injective
  have h := LinearEquiv.finrank_eq e
  rw [range_mulE4OnI0] at h
  exact h.symm

private theorem unique_minkowski_null {y y' z z' : PGA}
    (hy : y ∈ minkowskiSub) (hy' : y' ∈ minkowskiSub)
    (hz : z ∈ minkowskiSub) (hz' : z' ∈ minkowskiSub)
    (h : y + PGA.ι PGA.e4Index * z = y' + PGA.ι PGA.e4Index * z') :
    y = y' ∧ z = z' := by
  have hdiff : (y - y') + PGA.ι PGA.e4Index * (z - z') = 0 := by
    calc (y - y') + PGA.ι PGA.e4Index * (z - z')
        = y + PGA.ι PGA.e4Index * z - (y' + PGA.ι PGA.e4Index * z') := by
          simp [sub_eq_add_neg, mul_add, mul_neg]
          abel
      _ = 0 := sub_eq_zero.mpr h
  have hyD : y - y' ∈ minkowskiSub := Submodule.sub_mem _ hy hy'
  have hzD : z - z' ∈ minkowskiSub := Submodule.sub_mem _ hz hz'
  have hR : PGA.ι PGA.e4Index * (z - z') ∈ nullMinkowski := ⟨_, hzD, rfl⟩
  have hin : y - y' ∈ minkowskiSub ⊓ nullMinkowski := by
    refine ⟨hyD, ?_⟩
    have : y - y' = -(PGA.ι PGA.e4Index * (z - z')) :=
      add_eq_zero_iff_eq_neg.mp hdiff
    rw [this]
    exact neg_mem hR
  have hy0 : y - y' = 0 := by
    have hbot : minkowskiSub ⊓ nullMinkowski = ⊥ :=
      minkowski_disjoint_nullMinkowski.eq_bot
    rw [hbot, Submodule.mem_bot] at hin
    exact hin
  have hz0mul : PGA.ι PGA.e4Index * (z - z') = 0 := by
    simpa [hy0] using hdiff
  exact ⟨eq_of_sub_eq_zero hy0,
    eq_of_sub_eq_zero (mulLeft_e4_injective_on_minkowski hzD hz0mul)⟩

theorem leftIdeal_eq_core_sup_null :
    leftIdealSub commutingSpinorIdem =
      minkowskiLeftIdeal ⊔ nullSlice := by
  refine le_antisymm ?_ (sup_le inf_le_left nullSlice_le_leftIdeal)
  intro x hx
  obtain ⟨y, z, hy, hz, hxz⟩ := exists_minkowski_split x
  have hmul := leftIdeal_mul_P hx
  have hmul' :
      y * commutingSpinorIdem +
        PGA.ι PGA.e4Index * (z * commutingSpinorIdem) =
        y + PGA.ι PGA.e4Index * z := by
    rw [hxz, add_mul, mul_assoc] at hmul
    simpa [mul_assoc] using hmul
  have hyP : y * commutingSpinorIdem ∈ minkowskiSub :=
    minkowskiSub_mul hy commutingSpinorIdem_mem_minkowski
  have hzP : z * commutingSpinorIdem ∈ minkowskiSub :=
    minkowskiSub_mul hz commutingSpinorIdem_mem_minkowski
  obtain ⟨hyeq, hzeq⟩ := unique_minkowski_null hyP hy hzP hz hmul'
  have hyI : y ∈ leftIdealSub commutingSpinorIdem :=
    (mem_leftIdealSub_iff).mpr ⟨y, hyeq.symm⟩
  have hzI : z ∈ leftIdealSub commutingSpinorIdem :=
    (mem_leftIdealSub_iff).mpr ⟨z, hzeq.symm⟩
  rw [hxz]
  exact add_mem (Submodule.mem_sup_left ⟨hyI, hy⟩)
    (Submodule.mem_sup_right ⟨z, ⟨hzI, hz⟩, rfl⟩)

/-- \(\mathcal{I}=\mathcal{I}_0\oplus e_4\mathcal{I}_0\). -/
theorem leftIdeal_directSum_null :
    minkowskiLeftIdeal ⊔ nullSlice = leftIdealSub commutingSpinorIdem ∧
      minkowskiLeftIdeal ⊓ nullSlice = (⊥ : Submodule ℝ PGA) := by
  constructor
  · exact leftIdeal_eq_core_sup_null.symm
  · exact minkowskiLeftIdeal_disjoint_nullSlice.eq_bot

/-- Real dimension of the Minkowski core \(\mathrm{Cl}(3,1)\,P\). -/
theorem finrank_minkowskiLeftIdeal : finrank ℝ minkowskiLeftIdeal = 4 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    minkowskiLeftIdeal nullSlice
  have hI : minkowskiLeftIdeal ⊔ nullSlice = leftIdealSub commutingSpinorIdem :=
    leftIdeal_directSum_null.1
  have hbot : minkowskiLeftIdeal ⊓ nullSlice = ⊥ :=
    leftIdeal_directSum_null.2
  rw [hI, hbot, finrank_leftIdeal_commuting, finrank_bot,
    finrank_nullSlice_eq_minkowskiLeftIdeal] at hsum
  linarith

theorem finrank_nullSlice : finrank ℝ nullSlice = 4 := by
  rw [finrank_nullSlice_eq_minkowskiLeftIdeal, finrank_minkowskiLeftIdeal]

/-! ### Grade involution; left PGA-action on the null slice -/

theorem involute_toPGA (c : Cl31) :
    CliffordAlgebra.involute (Cl31.toPGA c) =
      Cl31.toPGA (CliffordAlgebra.involute c) := by
  induction c using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp
  | add a b ha hb =>
    simp [ha, hb]
  | ι_mul x m ih =>
    have hL : Cl31.toPGA (CliffordAlgebra.ι Q31 m * x) =
        CliffordAlgebra.ι Q311 (extend4 m) * Cl31.toPGA x :=
      toPGA_ι_mul x m
    have hι : Cl31.toPGA (CliffordAlgebra.ι Q31 m) =
        CliffordAlgebra.ι Q311 (extend4 m) := by
      rw [Cl31.toPGA_eq_map, CliffordAlgebra.map_apply_ι]; rfl
    have hR : Cl31.toPGA (CliffordAlgebra.involute (CliffordAlgebra.ι Q31 m * x)) =
        -(CliffordAlgebra.ι Q311 (extend4 m) *
          Cl31.toPGA (CliffordAlgebra.involute x)) := by
      rw [map_mul, involute_ι, neg_mul, map_neg, map_mul, hι]
    rw [hL, map_mul, involute_ι, neg_mul, ih, hR]

theorem toPGA_mul_e4 (c : Cl31) :
    Cl31.toPGA c * PGA.ι PGA.e4Index =
      PGA.ι PGA.e4Index * Cl31.toPGA (CliffordAlgebra.involute c) := by
  induction c using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp [Algebra.commutes]
  | add a b ha hb =>
    simp [add_mul, mul_add, ha, hb, map_add]
  | ι_mul x m ih =>
    have hanti :
        CliffordAlgebra.ι Q311 (extend4 m) * PGA.ι PGA.e4Index =
          -(PGA.ι PGA.e4Index * CliffordAlgebra.ι Q311 (extend4 m)) :=
      (neg_eq_iff_eq_neg.mpr (e4_mul_ι_vec (extend4 m))).symm
    have hL := toPGA_ι_mul x m
    have hι : Cl31.toPGA (CliffordAlgebra.ι Q31 m) =
        CliffordAlgebra.ι Q311 (extend4 m) := by
      rw [Cl31.toPGA_eq_map, CliffordAlgebra.map_apply_ι]; rfl
    rw [hL, mul_assoc, ih, ← mul_assoc, hanti, neg_mul, mul_assoc, ← hι]
    simp [map_mul, involute_ι, neg_mul]

theorem minkowski_mul_e4 {z : PGA} (hz : z ∈ minkowskiSub) :
    z * PGA.ι PGA.e4Index =
      PGA.ι PGA.e4Index * CliffordAlgebra.involute z := by
  rcases (mem_minkowskiSub.mp hz) with ⟨c, rfl⟩
  rw [toPGA_mul_e4, involute_toPGA]

theorem involute_mem_minkowski {z : PGA} (hz : z ∈ minkowskiSub) :
    CliffordAlgebra.involute z ∈ minkowskiSub := by
  rcases (mem_minkowskiSub.mp hz) with ⟨c, rfl⟩
  exact ⟨CliffordAlgebra.involute c, (involute_toPGA c).symm⟩

/-- Left multiplication by an arbitrary PGA element preserves the null slice. -/
theorem mul_mem_nullSlice (a : PGA) {x : PGA} (hx : x ∈ nullSlice) :
    a * x ∈ nullSlice := by
  rcases hx with ⟨y, hy, rfl⟩
  obtain ⟨a0, a1, ha0, ha1, ha⟩ := exists_minkowski_split a
  have hsec :
      (PGA.ι PGA.e4Index * a1) * (PGA.ι PGA.e4Index * y) = 0 := by
    calc PGA.ι PGA.e4Index * a1 * (PGA.ι PGA.e4Index * y)
        = (PGA.ι PGA.e4Index * a1 * PGA.ι PGA.e4Index) * y := by
          simp [mul_assoc]
      _ = 0 := by rw [e4_mul_mul_e4, zero_mul]
  have hfst :
      a0 * (PGA.ι PGA.e4Index * y) =
        PGA.ι PGA.e4Index * (CliffordAlgebra.involute a0 * y) := by
    have h := minkowski_mul_e4 ha0
    calc a0 * (PGA.ι PGA.e4Index * y)
        = (a0 * PGA.ι PGA.e4Index) * y := by rw [mul_assoc]
      _ = (PGA.ι PGA.e4Index * CliffordAlgebra.involute a0) * y := by rw [h]
      _ = PGA.ι PGA.e4Index * (CliffordAlgebra.involute a0 * y) := by
          rw [mul_assoc]
  have hprodI :
      CliffordAlgebra.involute a0 * y ∈ leftIdealSub commutingSpinorIdem := by
    rcases (mem_leftIdealSub_iff).mp hy.1 with ⟨b, rfl⟩
    exact (mem_leftIdealSub_iff).mpr
      ⟨CliffordAlgebra.involute a0 * b, by simp [mul_assoc]⟩
  have hprodM :
      CliffordAlgebra.involute a0 * y ∈ minkowskiSub :=
    minkowskiSub_mul (involute_mem_minkowski ha0) hy.2
  have hrewrite :
      a * (PGA.ι PGA.e4Index * y) =
        PGA.ι PGA.e4Index * (CliffordAlgebra.involute a0 * y) := by
    rw [ha, add_mul, hfst, hsec, add_zero]
  simp only [mulLeft_apply]
  rw [hrewrite]
  exact ⟨_, ⟨hprodI, hprodM⟩, rfl⟩

theorem iota_e4_mul_P_ne_zero :
    PGA.ι PGA.e4Index * commutingSpinorIdem ≠ 0 := by
  intro h
  have hP0 := mulLeft_e4_injective_on_minkowski
    commutingSpinorIdem_mem_minkowski h
  exact commutingSpinorIdem_ne_zero hP0

/-- The null copy is a proper nontrivial left \(G(3,1,1)\)-submodule of \(\mathcal{I}\). -/
theorem nullSlice_is_proper_submodule :
    nullSlice ≤ leftIdealSub commutingSpinorIdem ∧
      nullSlice ≠ ⊥ ∧
      nullSlice ≠ leftIdealSub commutingSpinorIdem ∧
      ∀ (a x : PGA), x ∈ nullSlice → a * x ∈ nullSlice := by
  refine ⟨nullSlice_le_leftIdeal, ?_, ?_, fun a x hx => mul_mem_nullSlice a hx⟩
  · intro hbot
    have hx : PGA.ι PGA.e4Index * commutingSpinorIdem ∈ nullSlice :=
      ⟨commutingSpinorIdem, commutingSpinorIdem_mem_minkowskiLeftIdeal, rfl⟩
    rw [hbot, Submodule.mem_bot] at hx
    exact iota_e4_mul_P_ne_zero hx
  · intro heq
    have hP : commutingSpinorIdem ∈ nullSlice := by
      rw [heq]
      exact commutingSpinorIdem_mem_leftIdealSub
    have hbot := minkowski_disjoint_nullMinkowski.le_bot
      ⟨commutingSpinorIdem_mem_minkowski, nullSlice_le_nullMinkowski hP⟩
    rw [Submodule.mem_bot] at hbot
    exact commutingSpinorIdem_ne_zero hbot

end Logic

end DstDiophantine


