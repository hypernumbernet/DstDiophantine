import DstDiophantine.Gravity.Electroweak
import DstDiophantine.Algebra.LorentzLie
import DstDiophantine.Logic.Quantum.Quaternion
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Chiral axes, Cartan $\mathfrak{so}(2,1)$, and the dual $\mathrm{SU}(2)$

## Paper boundary (do **not** claim)

A Weinberg angle, $W/Z$ masses, three Standard-Model generations, and a
Lorentz-invariant V--A gauge theory are **not** derived. Axis chirality is
not photon helicity (already in `Electroweak`). Compact $\mathrm{SU}(2)$ in
the Faraday six-space is identified only as the dual-rotor cyclic span at
the level of squares and the quaternion table; an abstract Lie-algebra
isomorphism is not formalised.

## What is proved

* Each spatial generator $e_1,e_2,e_3$ squares to $+1$ and yields a
  complementary projector pair. The time generator $e_0$ squares to $-1$,
  so $(1\pm e_0)/2$ fails to be idempotent for the same reason as
  $(1\pm i)/2$.
* Distinct-axis projectors do not commute, and the three right projectors
  do not sum to the unit: they are alternative embeddings of one $3+3$
  split, not a resolution of the identity and not three simultaneous
  generation labels.
* Relative to axis $e_a$ the commuting (Cartan) triple is
  $(B_a,E_{a+1},E_{a+2})$ and the anticommuting (charged) triple is
  $(E_a,B_{a+1},B_{a+2})$. Cartan brackets close as
  $\mathfrak{so}(2,1)$: one compact generator and two noncompact. The
  charged triple does not close; $[E_a,B_{a+1}]$ is the remaining Cartan
  electric. Duality exchanges the two triples (up to signs).
* Among the six written Faraday generators, every cyclic generator squares
  to $-1$ and every hyperbolic generator squares to $+1$. A Cartan triple
  therefore has mixed signature, while the dual-rotor triple is compact
  and satisfies the quaternion table $IJ=K$.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations Logic LorentzLie
open scoped Real

/-! ### Spatial chirality generators -/

/-- Spatial grade-1 generators \(e_1,e_2,e_3\). -/
noncomputable def spatialGen : Fin 3 → PGA
  | 0 => ι 1
  | 1 => ι 2
  | 2 => ι 3

theorem spatialGen_zero : spatialGen 0 = chiralityGen := rfl

theorem spatialGen_sq (a : Fin 3) : spatialGen a * spatialGen a = 1 := by
  fin_cases a <;> simp [spatialGen, e_sq, Q311_e5vec, w311]

theorem spatialGen_ne_zero (a : Fin 3) : spatialGen a ≠ 0 := by
  intro h
  have : (1 : PGA) = 0 := by rw [← spatialGen_sq a, h, mul_zero]
  have hR : (1 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hR

theorem spatialGen_anticomm {a b : Fin 3} (h : a ≠ b) :
    spatialGen a * spatialGen b = -(spatialGen b * spatialGen a) := by
  fin_cases a <;> fin_cases b <;> try { cases h rfl }
  all_goals
    simp only [spatialGen]
    exact e_mul_anticomm (by decide)

theorem spatialGen_mul_ne_zero (a b : Fin 3) :
    spatialGen a * spatialGen b ≠ 0 := by
  intro hz
  have : spatialGen a * (spatialGen b * spatialGen b) = 0 := by
    rw [← mul_assoc, hz, zero_mul]
  rw [spatialGen_sq, mul_one] at this
  exact spatialGen_ne_zero a this

/-! ### Projectors along an arbitrary spatial axis -/

noncomputable def chiralityRAxis (a : Fin 3) : PGA :=
  ((1 : PGA) + spatialGen a) * half

noncomputable def chiralityLAxis (a : Fin 3) : PGA :=
  ((1 : PGA) - spatialGen a) * half

theorem chiralityRAxis_zero : chiralityRAxis 0 = chiralityR := rfl

theorem chiralityLAxis_zero : chiralityLAxis 0 = chiralityL := rfl

theorem chiralityRAxis_sq (a : Fin 3) :
    chiralityRAxis a * chiralityRAxis a = chiralityRAxis a :=
  idempotent_of_sq_one (spatialGen_sq a)

theorem chiralityLAxis_sq (a : Fin 3) :
    chiralityLAxis a * chiralityLAxis a = chiralityLAxis a :=
  idempotent_of_sq_one_sub (spatialGen_sq a)

theorem chiralityLAxis_add_chiralityRAxis (a : Fin 3) :
    chiralityLAxis a + chiralityRAxis a = 1 := by
  unfold chiralityLAxis chiralityRAxis
  have h :
      ((1 : PGA) - spatialGen a) * half + ((1 : PGA) + spatialGen a) * half =
        half + half := by
    simp [sub_mul, add_mul, one_mul]
  rw [h, add_self_eq_map_two_mul, two_mul_half]

theorem chiralityLAxis_mul_chiralityRAxis (a : Fin 3) :
    chiralityLAxis a * chiralityRAxis a = 0 := by
  unfold chiralityLAxis chiralityRAxis
  have hdiff :
      ((1 : PGA) - spatialGen a) * ((1 : PGA) + spatialGen a) =
        (1 : PGA) - spatialGen a * spatialGen a := by
    noncomm_ring
  rw [mul_half_mul_half, hdiff, spatialGen_sq, sub_self, zero_mul]

/-- A generator with square \(-1\) cannot furnish a chirality projector. -/
theorem half_one_add_not_idempotent_of_sq_neg_one {g : PGA}
    (hg : g * g = -1) :
    ((1 : PGA) + g) * half * (((1 : PGA) + g) * half) ≠
      ((1 : PGA) + g) * half := by
  intro h
  have hexp :
      ((1 : PGA) + g) * ((1 : PGA) + g) = algebraMap ℝ PGA 2 * g := by
    calc ((1 : PGA) + g) * ((1 : PGA) + g)
        = 1 + g + g + g * g := by noncomm_ring
      _ = 1 + g + g + (-1 : PGA) := by rw [hg]
      _ = g + g := by abel
      _ = algebraMap ℝ PGA 2 * g := add_self_eq_map_two_mul g
  have hL :
      ((1 : PGA) + g) * half * (((1 : PGA) + g) * half) =
        algebraMap ℝ PGA (1 / 2) * g := by
    have h2q : algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4) =
        algebraMap ℝ PGA (1 / 2) := by
      rw [← map_mul]; norm_num
    calc ((1 : PGA) + g) * half * (((1 : PGA) + g) * half)
        = ((1 : PGA) + g) * ((1 : PGA) + g) * (half * half) :=
          mul_half_mul_half _ _
      _ = (algebraMap ℝ PGA 2 * g) * algebraMap ℝ PGA (1 / 4) := by
            rw [hexp, half_mul_half]
      _ = algebraMap ℝ PGA 2 * (g * algebraMap ℝ PGA (1 / 4)) := by
            rw [mul_assoc]
      _ = algebraMap ℝ PGA 2 * (algebraMap ℝ PGA (1 / 4) * g) := by
            rw [Algebra.commutes (1 / 4 : ℝ) g]
      _ = (algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4)) * g := by
            rw [← mul_assoc]
      _ = algebraMap ℝ PGA (1 / 2) * g := by rw [h2q]
  have hR :
      ((1 : PGA) + g) * half = algebraMap ℝ PGA (1 / 2) * ((1 : PGA) + g) :=
    (Algebra.commutes (1 / 2 : ℝ) ((1 : PGA) + g)).symm
  rw [hL, hR] at h
  have heq :
      algebraMap ℝ PGA (1 / 2) * (1 : PGA) + algebraMap ℝ PGA (1 / 2) * g =
        algebraMap ℝ PGA (1 / 2) * g := by
    simpa [mul_add, mul_one] using h.symm
  have hhalf : algebraMap ℝ PGA (1 / 2) * (1 : PGA) = 0 :=
    add_eq_right.mp heq
  have : algebraMap ℝ PGA (1 / 2) = 0 := by
    rw [mul_one] at hhalf
    exact hhalf
  have hℝ : (1 / 2 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hℝ

/-- The time axis cannot serve as a chirality generator. -/
theorem timeAxis_not_chirality_projector :
    ((1 : PGA) + ι 0) * half * (((1 : PGA) + ι 0) * half) ≠
      ((1 : PGA) + ι 0) * half :=
  half_one_add_not_idempotent_of_sq_neg_one (by simpa using e0_sq)

/-! ### Distinct-axis projectors are not simultaneous labels -/

theorem chiralityRAxis_not_commute {a b : Fin 3} (h : a ≠ b) :
    chiralityRAxis a * chiralityRAxis b ≠
      chiralityRAxis b * chiralityRAxis a := by
  intro heq
  have hL :
      chiralityRAxis a * chiralityRAxis b =
        ((1 : PGA) + spatialGen a) * ((1 : PGA) + spatialGen b) *
          (half * half) :=
    mul_half_mul_half _ _
  have hR :
      chiralityRAxis b * chiralityRAxis a =
        ((1 : PGA) + spatialGen b) * ((1 : PGA) + spatialGen a) *
          (half * half) :=
    mul_half_mul_half _ _
  have hdiff :
      (((1 : PGA) + spatialGen a) * ((1 : PGA) + spatialGen b) -
          ((1 : PGA) + spatialGen b) * ((1 : PGA) + spatialGen a)) *
        (half * half) = 0 := by
    rw [hL, hR] at heq
    simpa [sub_mul] using sub_eq_zero.mpr heq
  have hsub :
      ((1 : PGA) + spatialGen a) * ((1 : PGA) + spatialGen b) -
          ((1 : PGA) + spatialGen b) * ((1 : PGA) + spatialGen a) =
        spatialGen a * spatialGen b - spatialGen b * spatialGen a := by
    noncomm_ring
  rw [hsub, spatialGen_anticomm h, half_mul_half] at hdiff
  -- `hdiff` is now `(-(b*a) - (b*a)) * (1/4) = 0`, i.e. `-2 (b*a) / 4 = 0`.
  have hneg2 :
      -(spatialGen b * spatialGen a) - spatialGen b * spatialGen a =
        -(algebraMap ℝ PGA 2 * (spatialGen b * spatialGen a)) := by
    simp [add_self_eq_map_two_mul, sub_eq_add_neg]
  rw [hneg2] at hdiff
  have hprod :
      algebraMap ℝ PGA 2 * (spatialGen b * spatialGen a) *
        algebraMap ℝ PGA (1 / 4) = 0 := by
    simpa [neg_mul] using hdiff
  have hz : spatialGen b * spatialGen a = 0 := by
    have h2q : algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4) =
        algebraMap ℝ PGA (1 / 2) := by
      rw [← map_mul]; norm_num
    have hhalf : algebraMap ℝ PGA (1 / 2) * (spatialGen b * spatialGen a) = 0 := by
      calc algebraMap ℝ PGA (1 / 2) * (spatialGen b * spatialGen a)
          = algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4) *
              (spatialGen b * spatialGen a) := by rw [h2q]
        _ = algebraMap ℝ PGA 2 * (spatialGen b * spatialGen a) *
              algebraMap ℝ PGA (1 / 4) := by
              rw [mul_assoc,
                Algebra.commutes (1 / 4 : ℝ) (spatialGen b * spatialGen a),
                ← mul_assoc]
        _ = 0 := hprod
    have hsmul : (1 / 2 : ℝ) • (spatialGen b * spatialGen a) = 0 := by
      simpa [Algebra.smul_def] using hhalf
    exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num : (1 / 2 : ℝ) ≠ 0)
  exact spatialGen_mul_ne_zero b a hz

private theorem involute_spatialGen (a : Fin 3) :
    CliffordAlgebra.involute (Q := Q311) (spatialGen a) = -spatialGen a := by
  fin_cases a
  · simp only [spatialGen]
    exact CliffordAlgebra.involute_ι (Q := Q311) (e5vec 1)
  · simp only [spatialGen]
    exact CliffordAlgebra.involute_ι (Q := Q311) (e5vec 2)
  · simp only [spatialGen]
    exact CliffordAlgebra.involute_ι (Q := Q311) (e5vec 3)

private theorem involute_chiralityRAxis (a : Fin 3) :
    CliffordAlgebra.involute (Q := Q311) (chiralityRAxis a) = chiralityLAxis a := by
  unfold chiralityRAxis chiralityLAxis
  have hhalf :
      CliffordAlgebra.involute (Q := Q311) half = half := by
    unfold half
    simp
  rw [map_mul, hhalf, map_add, map_one, involute_spatialGen]
  simp [sub_eq_add_neg]

private theorem one_add_one_eq_two : (1 : PGA) + 1 = algebraMap ℝ PGA 2 := by
  calc (1 : PGA) + 1
      = algebraMap ℝ PGA 1 + algebraMap ℝ PGA 1 := by
          simp [Algebra.algebraMap_eq_smul_one]
    _ = algebraMap ℝ PGA (1 + 1) := (map_add _ _ _).symm
    _ = algebraMap ℝ PGA 2 := by norm_num

private theorem one_add_one_add_one_eq_three :
    (1 : PGA) + 1 + 1 = algebraMap ℝ PGA 3 := by
  calc (1 : PGA) + 1 + 1
      = algebraMap ℝ PGA 1 + algebraMap ℝ PGA 1 + algebraMap ℝ PGA 1 := by
          simp [Algebra.algebraMap_eq_smul_one]
    _ = algebraMap ℝ PGA (1 + 1 + 1) := by simp [map_add]
    _ = algebraMap ℝ PGA 3 := by norm_num

/-- The three right projectors are not a resolution of the identity. -/
theorem chiralityRAxis_sum_ne_one :
    chiralityRAxis 0 + chiralityRAxis 1 + chiralityRAxis 2 ≠ 1 := by
  intro h
  have hL :
      chiralityLAxis 0 + chiralityLAxis 1 + chiralityLAxis 2 = 1 := by
    have hα := congrArg (CliffordAlgebra.involute (Q := Q311)) h
    simpa [map_add, map_one, involute_chiralityRAxis] using hα
  have hsum2 :
      (chiralityLAxis 0 + chiralityLAxis 1 + chiralityLAxis 2) +
          (chiralityRAxis 0 + chiralityRAxis 1 + chiralityRAxis 2) =
        algebraMap ℝ PGA 2 := by
    rw [hL, h, one_add_one_eq_two]
  have hsum3 :
      (chiralityLAxis 0 + chiralityLAxis 1 + chiralityLAxis 2) +
          (chiralityRAxis 0 + chiralityRAxis 1 + chiralityRAxis 2) =
        algebraMap ℝ PGA 3 := by
    calc (chiralityLAxis 0 + chiralityLAxis 1 + chiralityLAxis 2) +
            (chiralityRAxis 0 + chiralityRAxis 1 + chiralityRAxis 2)
        = (chiralityLAxis 0 + chiralityRAxis 0) +
            (chiralityLAxis 1 + chiralityRAxis 1) +
              (chiralityLAxis 2 + chiralityRAxis 2) := by abel
      _ = (1 : PGA) + 1 + 1 := by simp [chiralityLAxis_add_chiralityRAxis]
      _ = algebraMap ℝ PGA 3 := one_add_one_add_one_eq_three
  have : algebraMap ℝ PGA (2 : ℝ) = algebraMap ℝ PGA (3 : ℝ) :=
    hsum2.symm.trans hsum3
  have hℝ : (2 : ℝ) = 3 :=
    FaithfulSMul.algebraMap_injective (R := ℝ) (A := PGA) this
  norm_num at hℝ

/-! ### Cartan versus charged triples -/

/-- Cartan generators of axis `a`: parallel magnetic and the two perpendicular
electrics, \((B_a, E_{a+1}, E_{a+2})\). -/
noncomputable def cartanGen (a i : Fin 3) : PGA :=
  match i with
  | 0 => cyclic a
  | 1 => hyperbolic (a + 1)
  | 2 => hyperbolic (a + 2)

/-- Charged generators of axis `a`: parallel electric and the two perpendicular
magnetics, \((E_a, B_{a+1}, B_{a+2})\). -/
noncomputable def chargedGen (a i : Fin 3) : PGA :=
  match i with
  | 0 => hyperbolic a
  | 1 => cyclic (a + 1)
  | 2 => cyclic (a + 2)

theorem cartanGen_sq (a : Fin 3) :
    cartanGen a 0 * cartanGen a 0 = -1 ∧
      cartanGen a 1 * cartanGen a 1 = 1 ∧
        cartanGen a 2 * cartanGen a 2 = 1 :=
  ⟨cyclic_sq a, hyperbolic_sq (a + 1), hyperbolic_sq (a + 2)⟩

theorem chargedGen_sq (a : Fin 3) :
    chargedGen a 0 * chargedGen a 0 = 1 ∧
      chargedGen a 1 * chargedGen a 1 = -1 ∧
        chargedGen a 2 * chargedGen a 2 = -1 :=
  ⟨hyperbolic_sq a, cyclic_sq (a + 1), cyclic_sq (a + 2)⟩

/-- Cartan signature is mixed: one compact generator, two noncompact. -/
theorem cartan_mixed_signature (a : Fin 3) :
    cartanGen a 0 * cartanGen a 0 = -1 ∧
      cartanGen a 1 * cartanGen a 1 ≠ -1 := by
  refine ⟨(cartanGen_sq a).1, ?_⟩
  rw [(cartanGen_sq a).2.1]
  intro h
  have : (1 : ℝ) = -1 :=
    FaithfulSMul.algebraMap_injective (R := ℝ) (A := PGA)
      (by simpa [map_one, map_neg] using h)
  norm_num at this

/-- Dual-rotor (magnetic) generators are compact. -/
theorem cyclic_compact (a : Fin 3) : cyclic a * cyclic a = -1 :=
  cyclic_sq a

/-- Usual-sector (electric) generators are noncompact. -/
theorem hyperbolic_noncompact (a : Fin 3) : hyperbolic a * hyperbolic a ≠ -1 := by
  rw [hyperbolic_sq]
  intro h
  have : (1 : ℝ) = -1 :=
    FaithfulSMul.algebraMap_injective (R := ℝ) (A := PGA)
      (by simpa [map_one, map_neg] using h)
  norm_num at this

/-! ### Bivector–vector commutation -/

private theorem commute_biv_vec {i j μ : Fin 5} (_hij : i ≠ j)
    (hμi : μ ≠ i) (hμj : μ ≠ j) :
    Commute (ι i * ι j) (ι μ) := by
  unfold Commute SemiconjBy
  have hμi' : ι μ * ι i = -(ι i * ι μ) := e_mul_anticomm hμi
  have hjμ : ι j * ι μ = -(ι μ * ι j) := e_mul_anticomm hμj.symm
  calc (ι i * ι j) * ι μ
      = ι i * (ι j * ι μ) := by rw [mul_assoc]
    _ = ι i * (-(ι μ * ι j)) := by rw [hjμ]
    _ = -(ι i * ι μ) * ι j := by simp [mul_neg, mul_assoc]
    _ = (ι μ * ι i) * ι j := by rw [← hμi']
    _ = ι μ * (ι i * ι j) := by simp [mul_assoc]

private theorem anticomm_biv_left {i j : Fin 5} (hij : i ≠ j) :
    (ι i * ι j) * ι i = -(ι i * (ι i * ι j)) := by
  have hji : ι j * ι i = -(ι i * ι j) := e_mul_anticomm hij.symm
  calc (ι i * ι j) * ι i
      = ι i * (ι j * ι i) := by rw [mul_assoc]
    _ = ι i * (-(ι i * ι j)) := by rw [hji]
    _ = -(ι i * (ι i * ι j)) := by simp [mul_neg]

private theorem anticomm_biv_right {i j : Fin 5} (hij : i ≠ j) :
    (ι i * ι j) * ι j = -(ι j * (ι i * ι j)) := by
  have hsq : ι j * ι j = algebraMap ℝ PGA (Q311 (e5vec j)) := e_sq j
  have hL : (ι i * ι j) * ι j = algebraMap ℝ PGA (Q311 (e5vec j)) * ι i := by
    calc (ι i * ι j) * ι j
        = ι i * (ι j * ι j) := by rw [mul_assoc]
      _ = ι i * algebraMap ℝ PGA (Q311 (e5vec j)) := by rw [hsq]
      _ = algebraMap ℝ PGA (Q311 (e5vec j)) * ι i :=
            (Algebra.commutes (Q311 (e5vec j)) (ι i)).symm
  have hR : ι j * (ι i * ι j) = -(algebraMap ℝ PGA (Q311 (e5vec j)) * ι i) := by
    have hij' : ι j * ι i = -(ι i * ι j) := e_mul_anticomm hij.symm
    calc ι j * (ι i * ι j)
        = (ι j * ι i) * ι j := by rw [mul_assoc]
      _ = (-(ι i * ι j)) * ι j := by rw [hij']
      _ = -(ι i * (ι j * ι j)) := by simp [mul_assoc]
      _ = -(ι i * algebraMap ℝ PGA (Q311 (e5vec j))) := by rw [hsq]
      _ = -(algebraMap ℝ PGA (Q311 (e5vec j)) * ι i) := by
            rw [Algebra.commutes (Q311 (e5vec j)) (ι i)]
  calc (ι i * ι j) * ι j
      = algebraMap ℝ PGA (Q311 (e5vec j)) * ι i := hL
    _ = -(-(algebraMap ℝ PGA (Q311 (e5vec j)) * ι i)) := by simp
    _ = -(ι j * (ι i * ι j)) := by rw [← hR]

theorem cartanGen_commute_axis (a i : Fin 3) :
    Commute (spatialGen a) (cartanGen a i) := by
  fin_cases a <;> fin_cases i
  · -- e1 with cyclic 0 = e3 e2
    simpa [spatialGen, cartanGen, cyclic] using
      (commute_biv_vec (by decide : (3 : Fin 5) ≠ 2)
        (by decide : (1 : Fin 5) ≠ 3) (by decide : (1 : Fin 5) ≠ 2)).symm
  · -- e1 with hyperbolic 1 = e0 e2
    simpa [spatialGen, cartanGen, hyperbolic] using
      (commute_biv_vec (by decide : (0 : Fin 5) ≠ 2)
        (by decide : (1 : Fin 5) ≠ 0) (by decide : (1 : Fin 5) ≠ 2)).symm
  · -- e1 with hyperbolic 2 = e0 e3
    simpa [spatialGen, cartanGen, hyperbolic] using
      (commute_biv_vec (by decide : (0 : Fin 5) ≠ 3)
        (by decide : (1 : Fin 5) ≠ 0) (by decide : (1 : Fin 5) ≠ 3)).symm
  · -- e2 with cyclic 1 = e1 e3
    simpa [spatialGen, cartanGen, cyclic] using
      (commute_biv_vec (by decide : (1 : Fin 5) ≠ 3)
        (by decide : (2 : Fin 5) ≠ 1) (by decide : (2 : Fin 5) ≠ 3)).symm
  · -- e2 with hyperbolic 2 = e0 e3
    simpa [spatialGen, cartanGen, hyperbolic] using
      (commute_biv_vec (by decide : (0 : Fin 5) ≠ 3)
        (by decide : (2 : Fin 5) ≠ 0) (by decide : (2 : Fin 5) ≠ 3)).symm
  · -- e2 with hyperbolic 0 = e0 e1
    simpa [spatialGen, cartanGen, hyperbolic] using
      (commute_biv_vec (by decide : (0 : Fin 5) ≠ 1)
        (by decide : (2 : Fin 5) ≠ 0) (by decide : (2 : Fin 5) ≠ 1)).symm
  · -- e3 with cyclic 2 = e2 e1
    simpa [spatialGen, cartanGen, cyclic] using
      (commute_biv_vec (by decide : (2 : Fin 5) ≠ 1)
        (by decide : (3 : Fin 5) ≠ 2) (by decide : (3 : Fin 5) ≠ 1)).symm
  · -- e3 with hyperbolic 0 = e0 e1
    simpa [spatialGen, cartanGen, hyperbolic] using
      (commute_biv_vec (by decide : (0 : Fin 5) ≠ 1)
        (by decide : (3 : Fin 5) ≠ 0) (by decide : (3 : Fin 5) ≠ 1)).symm
  · -- e3 with hyperbolic 1 = e0 e2
    simpa [spatialGen, cartanGen, hyperbolic] using
      (commute_biv_vec (by decide : (0 : Fin 5) ≠ 2)
        (by decide : (3 : Fin 5) ≠ 0) (by decide : (3 : Fin 5) ≠ 2)).symm

theorem chargedGen_anticomm_axis (a i : Fin 3) :
    spatialGen a * chargedGen a i = -(chargedGen a i * spatialGen a) := by
  have hneg {x y : PGA} (h : y * x = -(x * y)) : x * y = -(y * x) := by
    rw [h, neg_neg]
  fin_cases a <;> fin_cases i
  · -- e1 with hyperbolic 0 = e0 e1 (right factor)
    simpa [spatialGen, chargedGen, hyperbolic] using
      hneg (anticomm_biv_right (by decide : (0 : Fin 5) ≠ 1))
  · -- e1 with cyclic 1 = e1 e3 (left factor)
    simpa [spatialGen, chargedGen, cyclic] using
      hneg (anticomm_biv_left (by decide : (1 : Fin 5) ≠ 3))
  · -- e1 with cyclic 2 = e2 e1 (right factor)
    simpa [spatialGen, chargedGen, cyclic] using
      hneg (anticomm_biv_right (by decide : (2 : Fin 5) ≠ 1))
  · -- e2 with hyperbolic 1 = e0 e2
    simpa [spatialGen, chargedGen, hyperbolic] using
      hneg (anticomm_biv_right (by decide : (0 : Fin 5) ≠ 2))
  · -- e2 with cyclic 2 = e2 e1
    simpa [spatialGen, chargedGen, cyclic] using
      hneg (anticomm_biv_left (by decide : (2 : Fin 5) ≠ 1))
  · -- e2 with cyclic 0 = e3 e2
    simpa [spatialGen, chargedGen, cyclic] using
      hneg (anticomm_biv_right (by decide : (3 : Fin 5) ≠ 2))
  · -- e3 with hyperbolic 2 = e0 e3
    simpa [spatialGen, chargedGen, hyperbolic] using
      hneg (anticomm_biv_right (by decide : (0 : Fin 5) ≠ 3))
  · -- e3 with cyclic 0 = e3 e2
    simpa [spatialGen, chargedGen, cyclic] using
      hneg (anticomm_biv_left (by decide : (3 : Fin 5) ≠ 2))
  · -- e3 with cyclic 1 = e1 e3
    simpa [spatialGen, chargedGen, cyclic] using
      hneg (anticomm_biv_right (by decide : (1 : Fin 5) ≠ 3))

/-! ### Cartan $\mathfrak{so}(2,1)$ brackets -/

/-- \([B_a, E_{a+1}] = 2 E_{a+2}\). -/
theorem commutator_cartan_K_P1 (a : Fin 3) :
    commutator (cartanGen a 0) (cartanGen a 1) = (2 : ℝ) • cartanGen a 2 := by
  fin_cases a
  · change commutator (cyclic 0) (hyperbolic 1) = (2 : ℝ) • hyperbolic 2
    rw [commutator_neg]
    simp [commutator_hyperbolic_cyclic]
  · change commutator (cyclic 1) (hyperbolic 2) = (2 : ℝ) • hyperbolic 0
    rw [commutator_neg]
    simp [commutator_hyperbolic_cyclic]
  · change commutator (cyclic 2) (hyperbolic 0) = (2 : ℝ) • hyperbolic 1
    rw [commutator_neg]
    simp [commutator_hyperbolic_cyclic]

/-- \([B_a, E_{a+2}] = -2 E_{a+1}\). -/
theorem commutator_cartan_K_P2 (a : Fin 3) :
    commutator (cartanGen a 0) (cartanGen a 2) = -((2 : ℝ) • cartanGen a 1) := by
  fin_cases a
  · change commutator (cyclic 0) (hyperbolic 2) = -((2 : ℝ) • hyperbolic 1)
    rw [commutator_neg]
    simp [commutator_hyperbolic_cyclic]
  · change commutator (cyclic 1) (hyperbolic 0) = -((2 : ℝ) • hyperbolic 2)
    rw [commutator_neg]
    simp [commutator_hyperbolic_cyclic]
  · change commutator (cyclic 2) (hyperbolic 1) = -((2 : ℝ) • hyperbolic 0)
    rw [commutator_neg]
    simp [commutator_hyperbolic_cyclic]

/-- \([E_{a+1}, E_{a+2}] = -2 B_a\). -/
theorem commutator_cartan_P1_P2 (a : Fin 3) :
    commutator (cartanGen a 1) (cartanGen a 2) = -((2 : ℝ) • cartanGen a 0) := by
  fin_cases a
  · simp [cartanGen, commutator_hyperbolic_hyperbolic_cyclic]
  · simp [cartanGen, commutator_hyperbolic_hyperbolic_cyclic]
  · simp [cartanGen, commutator_hyperbolic_hyperbolic_cyclic]

/-- The charged bracket \([E_a, B_{a+1}]\) leaks into the Cartan triple. -/
theorem charged_bracket_is_cartan (a : Fin 3) :
    commutator (chargedGen a 0) (chargedGen a 1) = (2 : ℝ) • cartanGen a 2 := by
  fin_cases a
  · simp [chargedGen, cartanGen, commutator_hyperbolic_cyclic]
  · simp [chargedGen, cartanGen, commutator_hyperbolic_cyclic]
  · simp [chargedGen, cartanGen, commutator_hyperbolic_cyclic]

/-- The charged triple is not Lie-closed: its first bracket commutes with the
chirality axis, whereas every charged generator anticommutes. -/
theorem charged_triple_not_lie_closed (a : Fin 3) :
    ¬ (spatialGen a *
          commutator (chargedGen a 0) (chargedGen a 1) =
        -(commutator (chargedGen a 0) (chargedGen a 1) * spatialGen a)) := by
  rw [charged_bracket_is_cartan]
  intro hanti
  have hc : Commute (spatialGen a) (cartanGen a 2) := cartanGen_commute_axis a 2
  have hY :
      spatialGen a * ((2 : ℝ) • cartanGen a 2) =
        - (spatialGen a * ((2 : ℝ) • cartanGen a 2)) := by
    calc spatialGen a * ((2 : ℝ) • cartanGen a 2)
        = - (((2 : ℝ) • cartanGen a 2) * spatialGen a) := hanti
      _ = - (spatialGen a * ((2 : ℝ) • cartanGen a 2)) := by
            rw [mul_smul_comm, smul_mul_assoc, hc.eq]
  have h0 : spatialGen a * ((2 : ℝ) • cartanGen a 2) = 0 := by
    have := eq_neg_iff_add_eq_zero.mp hY
    have : (2 : ℝ) • (spatialGen a * ((2 : ℝ) • cartanGen a 2)) = 0 := by
      simpa [two_smul] using this
    exact (smul_eq_zero.mp this).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have hX : spatialGen a * cartanGen a 2 = 0 := by
    have : (2 : ℝ) • (spatialGen a * cartanGen a 2) = 0 := by
      simpa [smul_mul_assoc] using h0
    exact (smul_eq_zero.mp this).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have hcart : cartanGen a 2 = 0 := by
    have : cartanGen a 2 * (spatialGen a * spatialGen a) = 0 := by
      rw [← mul_assoc, ← hc.eq, hX, zero_mul]
    rwa [spatialGen_sq, mul_one] at this
  have : (1 : PGA) = 0 := by
    rw [← (cartanGen_sq a).2.2, hcart, mul_zero]
  have hℝ : (1 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hℝ

/-- Duality exchanges Cartan with charged, up to signs. -/
theorem dual_cartanGen (a : Fin 3) :
    dual (cartanGen a 0) = chargedGen a 0 ∧
      dual (cartanGen a 1) = -chargedGen a 1 ∧
        dual (cartanGen a 2) = -chargedGen a 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cartanGen, chargedGen, dual_cyclic]
  · simp [cartanGen, chargedGen, dual_hyperbolic]
  · simp [cartanGen, chargedGen, dual_hyperbolic]

/-- Dual-rotor cyclic generators satisfy the quaternion table \(IJ=K\). -/
theorem dual_rotor_quaternion :
    cyclic 0 * cyclic 1 = cyclic 2 ∧
      cyclic 1 * cyclic 2 = cyclic 0 ∧
        cyclic 2 * cyclic 0 = cyclic 1 :=
  ⟨cyclic_zero_mul_one, cyclic_one_mul_two, cyclic_two_mul_zero⟩

end Gravity

end DstDiophantine
