import DstDiophantine.Algebra.QuadraticForm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One-generator coordinate torsion

A constant generator `K` of the Minkowski Lie algebra and a 1-jet `d`
determine the coordinate torsion

`T^ρ_{μν} = d_μ K^ρ_ν - d_ν K^ρ_μ`.

The generator is recovered from six coefficients, the boosts `(t,x)`, `(t,y)`,
`(t,z)` and the rotations `(x,y)`, `(x,z)`, `(y,z)`. For every such generator
and every jet, the teleparallel quadratic vanishes. Two generators with
independent jets are not covered: that sum need not vanish.
-/

namespace DstDiophantine

namespace Gravity

namespace PlaneTorsion

open Finset

/-- `K` is infinitesimal Minkowski: `η_ρρ K^ρ_ν + η_νν K^ν_ρ = 0`. -/
def MinkowskiAntisym (K : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ ρ ν, w31 ρ * K ρ ν + w31 ν * K ν ρ = 0

/-- Six coefficients: boosts on axes `0,1,2`, then rotations in planes
`(x,y)`, `(x,z)`, `(y,z)`. -/
def soK (c : Fin 6 → ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 1 => c 0
  | 1, 0 => c 0
  | 0, 2 => c 1
  | 2, 0 => c 1
  | 0, 3 => c 2
  | 3, 0 => c 2
  | 1, 2 => c 3
  | 2, 1 => -c 3
  | 1, 3 => c 4
  | 3, 1 => -c 4
  | 2, 3 => c 5
  | 3, 2 => -c 5
  | _, _ => 0

/-- Independent entries of an antisymmetric generator. -/
def soCoeff (K : Fin 4 → Fin 4 → ℝ) : Fin 6 → ℝ
  | 0 => K 0 1
  | 1 => K 0 2
  | 2 => K 0 3
  | 3 => K 1 2
  | 4 => K 1 3
  | 5 => K 2 3

theorem w31_sq (ρ : Fin 4) : w31 ρ * w31 ρ = 1 := by
  fin_cases ρ <;> simp [w31]

theorem w31_ne_zero (ρ : Fin 4) : w31 ρ ≠ 0 := by
  fin_cases ρ <;> simp [w31]

theorem minkowskiAntisym_diag {K : Fin 4 → Fin 4 → ℝ} (h : MinkowskiAntisym K) (ρ : Fin 4) :
    K ρ ρ = 0 := by
  have hρ := h ρ ρ
  fin_cases ρ <;> simp [w31] at hρ ⊢ <;> linarith

theorem minkowskiAntisym_swap {K : Fin 4 → Fin 4 → ℝ} (h : MinkowskiAntisym K) (ρ ν : Fin 4) :
    K ν ρ = -(w31 ν * w31 ρ * K ρ ν) := by
  have hρν := h ρ ν
  have h1 : w31 ν * K ν ρ = -(w31 ρ * K ρ ν) := by linarith
  have h2 := congrArg (fun t : ℝ => w31 ν * t) h1
  rw [← mul_assoc, w31_sq, one_mul] at h2
  simpa [mul_assoc, mul_left_comm, mul_comm] using h2

theorem soK_minkowskiAntisym (c : Fin 6 → ℝ) : MinkowskiAntisym (soK c) := by
  intro ρ ν
  fin_cases ρ <;> fin_cases ν <;> simp [soK, w31]

theorem soK_of_antisym {K : Fin 4 → Fin 4 → ℝ} (h : MinkowskiAntisym K) (ρ ν : Fin 4) :
    K ρ ν = soK (soCoeff K) ρ ν := by
  fin_cases ρ <;> fin_cases ν
  · rw [minkowskiAntisym_diag h]; rfl
  · rfl
  · rfl
  · rfl
  · rw [minkowskiAntisym_swap h]; simp [soK, soCoeff, w31]
  · rw [minkowskiAntisym_diag h]; rfl
  · rfl
  · rfl
  · rw [minkowskiAntisym_swap h]; simp [soK, soCoeff, w31]
  · rw [minkowskiAntisym_swap h]; simp [soK, soCoeff, w31]
  · rw [minkowskiAntisym_diag h]; rfl
  · rfl
  · rw [minkowskiAntisym_swap h]; simp [soK, soCoeff, w31]
  · rw [minkowskiAntisym_swap h]; simp [soK, soCoeff, w31]
  · rw [minkowskiAntisym_swap h]; simp [soK, soCoeff, w31]
  · rw [minkowskiAntisym_diag h]; rfl

/-- Coordinate torsion of one generator. -/
def genTorsion (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  d μ * K ρ ν - d ν * K ρ μ

/-- `T_{ρμν} = η_{ρρ} T^ρ_{μν}`. -/
def genTdown (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * genTorsion K d ρ μ ν

/-- `T^{ρμν}`, indices raised by `η`. -/
def genTup (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * w31 μ * w31 ν * genTdown K d ρ μ ν

/-- Trace `T_ρ = T^σ_{ρσ}`. -/
def genTrace (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ : Fin 4) : ℝ :=
  ∑ σ : Fin 4, genTorsion K d σ ρ σ

/-- Raised trace `T^ρ = η^{ρρ} T_ρ`. -/
def genTraceUp (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ : Fin 4) : ℝ :=
  w31 ρ * genTrace K d ρ

/-- `¼ T_{ρμν}T^{ρμν}`. -/
def genSquare (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, genTdown K d ρ μ ν * genTup K d ρ μ ν

/-- `T_{ρμν}T^{νμρ}`. -/
def genCross (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, genTdown K d ρ μ ν * genTup K d ν μ ρ

/-- `T_ρ T^ρ`. -/
def genTraceContr (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, genTrace K d ρ * genTraceUp K d ρ

/-- Teleparallel scalar of a one-generator jet. -/
noncomputable def genTeleparallel (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) : ℝ :=
  (1 / 4) * genSquare K d + (1 / 2) * genCross K d - genTraceContr K d

theorem genTeleparallel_eq_cleared (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genTeleparallel K d =
      (1 / 4) * (genSquare K d + 2 * genCross K d - 4 * genTraceContr K d) := by
  unfold genTeleparallel
  ring

/-- Numerator of the teleparallel scalar. Vanishing of this is vanishing of `T`. -/
def genCleared (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) : ℝ :=
  genSquare K d + 2 * genCross K d - 4 * genTraceContr K d

private def unitCoeff (i : Fin 6) : Fin 6 → ℝ :=
  fun j => if j = i then 1 else 0

set_option maxHeartbeats 400000 in
-- Each of the six generators expands to a degree-4 polynomial before `ring`.
private theorem genCleared_unit (i : Fin 6) (d : Fin 4 → ℝ) :
    genCleared (soK (unitCoeff i)) d = 0 := by
  fin_cases i <;>
    simp only [genCleared, genSquare, genCross, genTraceContr, genTrace, genTraceUp, genTdown,
      genTup, genTorsion, Fin.sum_univ_four, unitCoeff, soK, w31] <;>
    ring

/-- Two-coefficient jets are the pairs needed for a null generator and for the
quadratic polarisation. `i` and `j` are arbitrary, including equals. -/
private def pairCoeff (i j : Fin 6) : Fin 6 → ℝ :=
  fun k => if k = i then 1 else if k = j then 1 else 0

set_option maxHeartbeats 2000000 in
-- Each ordered pair of generators expands to that same degree-4 normal form.
private theorem genCleared_pair (i j : Fin 6) (d : Fin 4 → ℝ) :
    genCleared (soK (pairCoeff i j)) d = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [genCleared, genSquare, genCross, genTraceContr, genTrace, genTraceUp, genTdown,
      genTup, genTorsion, Fin.sum_univ_four, pairCoeff, soK, w31] <;>
    ring

def kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun ρ ν => a * K ρ ν

def kAdd (K L : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun ρ ν => K ρ ν + L ρ ν

theorem genTorsion_kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTorsion (kSmul a K) d ρ μ ν = a * genTorsion K d ρ μ ν := by
  simp [genTorsion, kSmul]; ring

theorem genTdown_kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTdown (kSmul a K) d ρ μ ν = a * genTdown K d ρ μ ν := by
  simp [genTdown, genTorsion_kSmul]; ring

theorem genTup_kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTup (kSmul a K) d ρ μ ν = a * genTup K d ρ μ ν := by
  simp [genTup, genTdown_kSmul]; ring

theorem genTrace_kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ : Fin 4) :
    genTrace (kSmul a K) d ρ = a * genTrace K d ρ := by
  simp only [genTrace, genTorsion_kSmul, ← Finset.mul_sum]

theorem genTraceUp_kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ : Fin 4) :
    genTraceUp (kSmul a K) d ρ = a * genTraceUp K d ρ := by
  simp [genTraceUp, genTrace_kSmul]; ring

private theorem sum3_factor (a : ℝ) (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, a * f ρ μ ν) =
      a * ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, f ρ μ ν := by
  simp_rw [← Finset.mul_sum]

theorem genSquare_kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genSquare (kSmul a K) d = a ^ 2 * genSquare K d := by
  unfold genSquare
  simp_rw [genTdown_kSmul, genTup_kSmul]
  have hmul : ∀ ρ μ ν,
      (a * genTdown K d ρ μ ν) * (a * genTup K d ρ μ ν) =
        a ^ 2 * (genTdown K d ρ μ ν * genTup K d ρ μ ν) := by
    intro ρ μ ν; ring
  simp_rw [hmul]
  exact sum3_factor _ _

theorem genCross_kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genCross (kSmul a K) d = a ^ 2 * genCross K d := by
  unfold genCross
  simp_rw [genTdown_kSmul, genTup_kSmul]
  have hmul : ∀ ρ μ ν,
      (a * genTdown K d ρ μ ν) * (a * genTup K d ν μ ρ) =
        a ^ 2 * (genTdown K d ρ μ ν * genTup K d ν μ ρ) := by
    intro ρ μ ν; ring
  simp_rw [hmul]
  exact sum3_factor _ _

theorem genTraceContr_kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genTraceContr (kSmul a K) d = a ^ 2 * genTraceContr K d := by
  unfold genTraceContr
  simp_rw [genTrace_kSmul, genTraceUp_kSmul]
  have hmul : ∀ ρ, (a * genTrace K d ρ) * (a * genTraceUp K d ρ) =
      a ^ 2 * (genTrace K d ρ * genTraceUp K d ρ) := by
    intro ρ; ring
  simp_rw [hmul, ← Finset.mul_sum]

theorem genCleared_kSmul (a : ℝ) (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genCleared (kSmul a K) d = a ^ 2 * genCleared K d := by
  unfold genCleared
  rw [genSquare_kSmul, genCross_kSmul, genTraceContr_kSmul]
  ring

theorem genTorsion_kAdd (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTorsion (kAdd K L) d ρ μ ν = genTorsion K d ρ μ ν + genTorsion L d ρ μ ν := by
  simp [genTorsion, kAdd]; ring

theorem genTdown_kAdd (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTdown (kAdd K L) d ρ μ ν = genTdown K d ρ μ ν + genTdown L d ρ μ ν := by
  simp [genTdown, genTorsion_kAdd]; ring

theorem genTup_kAdd (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTup (kAdd K L) d ρ μ ν = genTup K d ρ μ ν + genTup L d ρ μ ν := by
  simp [genTup, genTdown_kAdd]; ring

theorem genTrace_kAdd (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ : Fin 4) :
    genTrace (kAdd K L) d ρ = genTrace K d ρ + genTrace L d ρ := by
  simp only [genTrace, genTorsion_kAdd, Finset.sum_add_distrib]

theorem genTraceUp_kAdd (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ : Fin 4) :
    genTraceUp (kAdd K L) d ρ = genTraceUp K d ρ + genTraceUp L d ρ := by
  simp [genTraceUp, genTrace_kAdd]; ring

private def dotDown (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, genTdown K d ρ μ ν * genTup L d ρ μ ν

private def dotCross (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, genTdown K d ρ μ ν * genTup L d ν μ ρ

private def dotTrace (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, genTrace K d ρ * genTraceUp L d ρ

private theorem genSquare_kAdd (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genSquare (kAdd K L) d = genSquare K d + genSquare L d + dotDown K L d + dotDown L K d := by
  unfold genSquare dotDown
  simp_rw [genTdown_kAdd, genTup_kAdd, add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem genCross_kAdd (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genCross (kAdd K L) d = genCross K d + genCross L d + dotCross K L d + dotCross L K d := by
  unfold genCross dotCross
  simp_rw [genTdown_kAdd, genTup_kAdd, add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem genTraceContr_kAdd (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genTraceContr (kAdd K L) d =
      genTraceContr K d + genTraceContr L d + dotTrace K L d + dotTrace L K d := by
  unfold genTraceContr dotTrace
  simp_rw [genTrace_kAdd, genTraceUp_kAdd, add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- Cross term of the cleared quadratic, bilinear in the two generators. -/
def genMix (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) : ℝ :=
  dotDown K L d + dotDown L K d + 2 * (dotCross K L d + dotCross L K d) -
    4 * (dotTrace K L d + dotTrace L K d)

theorem genCleared_kAdd (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genCleared (kAdd K L) d = genCleared K d + genCleared L d + genMix K L d := by
  unfold genCleared genMix
  rw [genSquare_kAdd, genCross_kAdd, genTraceContr_kAdd]
  ring

theorem soK_kAdd (c e : Fin 6 → ℝ) (ρ ν : Fin 4) :
    soK (fun k => c k + e k) ρ ν = kAdd (soK c) (soK e) ρ ν := by
  fin_cases ρ <;> fin_cases ν <;> simp [soK, kAdd]
  all_goals ring

theorem pairCoeff_eq_add {i j : Fin 6} (hij : i ≠ j) :
    pairCoeff i j = fun k => unitCoeff i k + unitCoeff j k := by
  funext k
  unfold pairCoeff unitCoeff
  by_cases hki : k = i <;> by_cases hkj : k = j
  · subst hki
    exact (hij hkj).elim
  · subst hki
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hkj]
    ring
  · subst hkj
    rw [ite_eq_right hki, ite_eq_right hki, ite_eq_left rfl]
    ring
  · rw [ite_eq_right hki, ite_eq_right hki, ite_eq_right hkj]
    ring

theorem genMix_unit {i j : Fin 6} (hij : i ≠ j) (d : Fin 4 → ℝ) :
    genMix (soK (unitCoeff i)) (soK (unitCoeff j)) d = 0 := by
  have hfun : kAdd (soK (unitCoeff i)) (soK (unitCoeff j)) = soK (pairCoeff i j) := by
    funext ρ ν
    rw [← soK_kAdd, pairCoeff_eq_add hij]
  have hexpand := genCleared_kAdd (soK (unitCoeff i)) (soK (unitCoeff j)) d
  rw [hfun, genCleared_pair, genCleared_unit, genCleared_unit] at hexpand
  linarith

theorem genMix_kSmul (a b : ℝ) (K L : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genMix (kSmul a K) (kSmul b L) d = (a * b) * genMix K L d := by
  unfold genMix dotDown dotCross dotTrace
  simp_rw [genTdown_kSmul, genTup_kSmul, genTrace_kSmul, genTraceUp_kSmul]
  simp_rw [show ∀ (p q x y : ℝ), (p * x) * (q * y) = (p * q) * (x * y) by intros; ring]
  simp_rw [← Finset.mul_sum]
  ring

theorem soK_eq_sum (c : Fin 6 → ℝ) (ρ ν : Fin 4) :
    soK c ρ ν =
      kAdd (kSmul (c 0) (soK (unitCoeff 0)))
        (kAdd (kSmul (c 1) (soK (unitCoeff 1)))
          (kAdd (kSmul (c 2) (soK (unitCoeff 2)))
            (kAdd (kSmul (c 3) (soK (unitCoeff 3)))
              (kAdd (kSmul (c 4) (soK (unitCoeff 4)))
                (kSmul (c 5) (soK (unitCoeff 5))))))) ρ ν := by
  fin_cases ρ <;> fin_cases ν <;> simp [soK, kAdd, kSmul, unitCoeff]

theorem genMix_kAdd_right (A B C : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) :
    genMix A (kAdd B C) d = genMix A B d + genMix A C d := by
  unfold genMix dotDown dotCross dotTrace
  simp_rw [genTdown_kAdd, genTup_kAdd, genTrace_kAdd, genTraceUp_kAdd, mul_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem genCleared_soK (c : Fin 6 → ℝ) (d : Fin 4 → ℝ) : genCleared (soK c) d = 0 := by
  let X : Fin 6 → (Fin 4 → Fin 4 → ℝ) := fun i => kSmul (c i) (soK (unitCoeff i))
  have hX : ∀ i, genCleared (X i) d = 0 := by
    intro i
    simp only [X, genCleared_kSmul, genCleared_unit, mul_zero]
  have hmix : ∀ i j, i ≠ j → genMix (X i) (X j) d = 0 := by
    intro i j hij
    simp only [X, genMix_kSmul, genMix_unit hij, mul_zero]
  have hfun : soK c =
      kAdd (X 0) (kAdd (X 1) (kAdd (X 2) (kAdd (X 3) (kAdd (X 4) (X 5))))) := by
    funext ρ ν
    simpa [X] using soK_eq_sum c ρ ν
  rw [hfun]
  have h45 : genCleared (kAdd (X 4) (X 5)) d = 0 := by
    rw [genCleared_kAdd, hX, hX, hmix 4 5 (by decide)]; ring
  have h345 : genCleared (kAdd (X 3) (kAdd (X 4) (X 5))) d = 0 := by
    rw [genCleared_kAdd, hX, h45, genMix_kAdd_right, hmix 3 4 (by decide),
      hmix 3 5 (by decide)]; ring
  have h2345 : genCleared (kAdd (X 2) (kAdd (X 3) (kAdd (X 4) (X 5)))) d = 0 := by
    rw [genCleared_kAdd, hX, h345, genMix_kAdd_right, genMix_kAdd_right,
      hmix 2 3 (by decide), hmix 2 4 (by decide), hmix 2 5 (by decide)]; ring
  have h12345 :
      genCleared (kAdd (X 1) (kAdd (X 2) (kAdd (X 3) (kAdd (X 4) (X 5))))) d = 0 := by
    rw [genCleared_kAdd, hX, h2345, genMix_kAdd_right, genMix_kAdd_right, genMix_kAdd_right,
      hmix 1 2 (by decide), hmix 1 3 (by decide), hmix 1 4 (by decide),
      hmix 1 5 (by decide)]; ring
  rw [genCleared_kAdd, hX, h12345, genMix_kAdd_right, genMix_kAdd_right, genMix_kAdd_right,
    genMix_kAdd_right, hmix 0 1 (by decide), hmix 0 2 (by decide), hmix 0 3 (by decide),
    hmix 0 4 (by decide), hmix 0 5 (by decide)]
  ring

/-- Every one-generator jet has vanishing teleparallel scalar. -/
theorem genTeleparallel_eq_zero {K : Fin 4 → Fin 4 → ℝ} (h : MinkowskiAntisym K)
    (d : Fin 4 → ℝ) : genTeleparallel K d = 0 := by
  have hK : K = soK (soCoeff K) := by
    funext ρ ν
    exact soK_of_antisym h ρ ν
  rw [hK, genTeleparallel_eq_cleared]
  change (1 / 4) * genCleared (soK (soCoeff K)) d = 0
  rw [genCleared_soK, mul_zero]

theorem genTorsion_eq_zero_of_eq (K : Fin 4 → Fin 4 → ℝ) (d : Fin 4 → ℝ) (ρ μ : Fin 4) :
    genTorsion K d ρ μ μ = 0 := by
  simp [genTorsion]

end PlaneTorsion

end Gravity

end DstDiophantine
