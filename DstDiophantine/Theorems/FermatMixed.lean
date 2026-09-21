import DstDiophantine.Embedding.FermatMotor
import DstDiophantine.Theorems.Fermat
import DstDiophantine.Algebra.MotorGroup
import DstDiophantine.Algebra.Sandwich
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Dual-axis Fermat motor slices (real Lᵖ comparison)

Closes the geometric dichotomy used by the dual-axis programme:

* `n = 2` positive solutions are pure cyclic (`α = 0`);
* `n ≥ 3` positive solutions are mixed (`α > 0` and `β ∈ (0, π/2)`).

The mixed seed leaks the additive null axis \(N_1\) into the time-null
generator \(N_0\) at first order, and the same leak reappears as the second
jet on \(N_3\). Those identities sit on the embedding axis itself; they do
**not** yet mention `powerSumMotor = 1`. Unconditional classical FLT is
**not** claimed.
-/

namespace DstDiophantine

namespace Theorems

open _root_.DstDiophantine.Embedding Real
open Amplification Motor Sandwich Generators MotorGroup PGA Operations
open CliffordAlgebra NormedSpace

private theorem natAbs_coe_eq_coe_of_pos {z : ℤ} (hz : 0 < z) :
    (z.natAbs : ℝ) = (z : ℝ) := by
  have h : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg (le_of_lt hz)
  calc (z.natAbs : ℝ) = ((z.natAbs : ℤ) : ℝ) := rfl
    _ = (z : ℝ) := by rw [h]

/-! ### Real Lᵖ comparison on the positive quadrant -/

/--
For `0 < x,y` and `n ≥ 3`, if `xⁿ + yⁿ = 1` then both coordinates lie in
`(0,1)`, hence `tⁿ < t²` and the Euclidean radius exceeds `1`.
-/
theorem fermat_unit_lp_radius_gt_one {x y : ℝ} {n : ℕ}
    (hn : 3 ≤ n) (hx : 0 < x) (hy : 0 < y)
    (h : x ^ n + y ^ n = 1) :
    1 < x ^ 2 + y ^ 2 := by
  have hn0 : n ≠ 0 := ne_of_gt (Nat.succ_le_iff.mp (Nat.le_trans (by decide : 1 ≤ 3) hn))
  have hx1 : x < 1 := by
    have : x ^ n < 1 := by
      have hypos : 0 < y ^ n := pow_pos hy n
      linarith [h, hypos]
    exact (pow_lt_one_iff_of_nonneg hx.le hn0).mp this
  have hy1 : y < 1 := by
    have : y ^ n < 1 := by
      have hxpos : 0 < x ^ n := pow_pos hx n
      linarith [h, hxpos]
    exact (pow_lt_one_iff_of_nonneg hy.le hn0).mp this
  have hn2 : 2 ≤ n := Nat.le_trans (by decide : 2 ≤ 3) hn
  have htail_ne : n - 2 ≠ 0 :=
    ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : 2 < 3) hn))
  have hxpow : x ^ n < x ^ 2 := by
    have hfac : x ^ n = x ^ 2 * x ^ (n - 2) := by
      rw [← pow_add, Nat.add_sub_of_le hn2]
    rw [hfac]
    have htail : x ^ (n - 2) < 1 := pow_lt_one₀ hx.le hx1 htail_ne
    exact mul_lt_of_lt_one_right (sq_pos_of_pos hx) htail
  have hypow : y ^ n < y ^ 2 := by
    have hfac : y ^ n = y ^ 2 * y ^ (n - 2) := by
      rw [← pow_add, Nat.add_sub_of_le hn2]
    rw [hfac]
    have htail : y ^ (n - 2) < 1 := pow_lt_one₀ hy.le hy1 htail_ne
    exact mul_lt_of_lt_one_right (sq_pos_of_pos hy) htail
  linarith [h, hxpow, hypow]

/-! ### Integer slices -/

theorem fermatBoost_eq_zero_of_pythagorean {a b c : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ 2 + b ^ 2 = c ^ 2) :
    IsPureCyclicFermatMotor a b c (ne_of_gt hc) := by
  refine (isPureCyclic_iff_pythagorean (ne_of_gt hc) (Or.inl (ne_of_gt ha))).mpr ?_
  have haR := natAbs_coe_eq_coe_of_pos ha
  have hbR := natAbs_coe_eq_coe_of_pos hb
  have hcR := natAbs_coe_eq_coe_of_pos hc
  have h' : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 = (c : ℝ) ^ 2 := by exact_mod_cast hsol
  rwa [haR, hbR, hcR]

theorem pythagorean_of_fermatBoost_eq_zero {a b c : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : IsPureCyclicFermatMotor a b c (ne_of_gt hc)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  have hR := (isPureCyclic_iff_pythagorean (ne_of_gt hc) (Or.inl (ne_of_gt ha))).mp h
  have haR := natAbs_coe_eq_coe_of_pos ha
  have hbR := natAbs_coe_eq_coe_of_pos hb
  have hcR := natAbs_coe_eq_coe_of_pos hc
  have : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 = (c : ℝ) ^ 2 := by
    rwa [← haR, ← hbR, ← hcR]
  exact_mod_cast this

/-- Positive Pythagorean triples are exactly the pure-cyclic Fermat motors. -/
theorem fermatBoost_eq_zero_iff_pythagorean {a b c : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsPureCyclicFermatMotor a b c (ne_of_gt hc) ↔ a ^ 2 + b ^ 2 = c ^ 2 :=
  ⟨pythagorean_of_fermatBoost_eq_zero ha hb hc,
    fermatBoost_eq_zero_of_pythagorean ha hb hc⟩

/-- Degree-`n ≥ 3` positive solutions force a strictly positive radius boost. -/
theorem fermatBoost_pos_of_sol {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    0 < fermatBoost a b c (ne_of_gt hc) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have haAbs := natAbs_coe_eq_coe_of_pos ha
  have hbAbs := natAbs_coe_eq_coe_of_pos hb
  have hcAbs := natAbs_coe_eq_coe_of_pos hc
  set x : ℝ := (a : ℝ) / c
  set y : ℝ := (b : ℝ) / c
  have hx : 0 < x := div_pos haR hcR
  have hy : 0 < y := div_pos hbR hcR
  have hunit : x ^ n + y ^ n = 1 := by
    have hsolR : (a : ℝ) ^ n + (b : ℝ) ^ n = (c : ℝ) ^ n := by exact_mod_cast hsol
    have hcne : (c : ℝ) ≠ 0 := ne_of_gt hcR
    calc x ^ n + y ^ n
        = ((a : ℝ) / c) ^ n + ((b : ℝ) / c) ^ n := rfl
      _ = (a : ℝ) ^ n / (c : ℝ) ^ n + (b : ℝ) ^ n / (c : ℝ) ^ n := by
          simp [div_pow]
      _ = ((a : ℝ) ^ n + (b : ℝ) ^ n) / (c : ℝ) ^ n := by rw [← add_div]
      _ = (c : ℝ) ^ n / (c : ℝ) ^ n := by rw [hsolR]
      _ = 1 := div_self (pow_ne_zero n hcne)
  have hrad := fermat_unit_lp_radius_gt_one hn hx hy hunit
  have hdiv : (1 : ℝ) < ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (c : ℝ) ^ 2 := by
    have : x ^ 2 + y ^ 2 = ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (c : ℝ) ^ 2 := by
      simp [x, y, div_pow, add_div]
    rwa [← this]
  have hsq : (c : ℝ) ^ 2 < (a : ℝ) ^ 2 + (b : ℝ) ^ 2 :=
    (one_lt_div (sq_pos_of_pos hcR)).mp hdiv
  have hL2 : (c.natAbs : ℝ) < fermatL2 a b := by
    rw [hcAbs]
    unfold fermatL2
    rw [haAbs, hbAbs]
    have hnn : 0 ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    exact (lt_sqrt (le_of_lt hcR)).mpr hsq
  exact (fermatBoost_pos_iff (ne_of_gt hc) (Or.inl (ne_of_gt ha))).mpr hL2

/-- Degree-`n ≥ 3` positive solutions sit in the mixed dual-axis seat. -/
theorem isMixedFermatMotor_of_sol {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    IsMixedFermatMotor a b c (ne_of_gt ha) (ne_of_gt hc) :=
  ⟨fermatBoost_pos_of_sol hn ha hb hc hsol,
    fermatAngle_pos_of_b_ne (ne_of_gt ha) (ne_of_gt hb),
    fermatAngle_lt_half_pi a b (ne_of_gt ha)⟩

/-! ### Sandwich / commutator connection (geometric, independent of FLT) -/

theorem commutator_fermatTorsion_null3 (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 3) =
      fermatAngle a b ha • null 1 := by
  rw [omegaTorsion_fermatTorsion, commutator_add_left, commutator_smul_left,
    commutator_smul_left, commutator_hyperbolic0_null3, commutator_cyclic_null]
  have hR : (3 : Fin 4) = cyclicRight (1 : Fin 3) := rfl
  have hL : cyclicLeft (1 : Fin 3) = (1 : Fin 4) := rfl
  simp [hR, hL]
  ring_nf
  module

theorem commutator_fermatBoost_null3 (a b c : ℤ) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatBoostSeed a b c hc)) (null 3) = 0 := by
  rw [fermatBoostSeed, omegaTorsion_pureBoost, commutator_smul_left,
    commutator_hyperbolic0_null3, smul_zero]

/-- Infinitesimal sandwich defect: mixed Fermat seeds move `N₃`, while a pure
axis-0 boost leaves it inert. -/
theorem commutator_fermatTorsion_null3_ne_pureBoost {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 3) ≠
      Generators.commutator (omegaTorsion (fermatBoostSeed a b c hc)) (null 3) := by
  rw [commutator_fermatTorsion_null3, commutator_fermatBoost_null3]
  intro hz
  have hβ : fermatAngle a b ha ≠ 0 := ne_of_gt h.2.1
  exact null_one_ne_zero ((smul_eq_zero.mp hz).resolve_left hβ)

/-! ### First jet on the integer axis \(N_1\) (temporal leak) -/

private theorem commutator_cyclic1_null1 :
    commutator (cyclic 1) (null 1) = (-2 : ℝ) • null 3 := by
  rw [commutator_cyclic_null]
  have hne : (1 : Fin 4) ≠ cyclicRight (1 : Fin 3) := by decide
  have heq : (1 : Fin 4) = cyclicLeft (1 : Fin 3) := rfl
  rw [ite_eq_right hne, ite_eq_left heq]
  rfl

private theorem commutator_cyclic1_null3 :
    commutator (cyclic 1) (null 3) = (2 : ℝ) • null 1 := by
  rw [commutator_cyclic_null]
  have heq : (3 : Fin 4) = cyclicRight (1 : Fin 3) := rfl
  rw [ite_eq_left heq]
  rfl

/-- Cyclic Fermat factor rotates the additive axis: \([\Omega_\beta,N_1]=-\beta N_3\). -/
theorem commutator_fermatAngle_null1 (a b : ℤ) (ha : a ≠ 0) :
    Generators.commutator (omegaTorsion (fermatAngleSeed a b ha)) (null 1) =
      -fermatAngle a b ha • null 3 := by
  rw [fermatAngleSeed, omegaTorsion_pureRotation1, commutator_smul_left,
    commutator_cyclic1_null1]
  module

/-- Radial Fermat boost mixes the additive axis into time: \([\Omega_\alpha,N_1]=\alpha N_0\). -/
theorem commutator_fermatBoost_null1 (a b c : ℤ) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatBoostSeed a b c hc)) (null 1) =
      fermatBoost a b c hc • null 0 := by
  rw [fermatBoostSeed, omegaTorsion_pureBoost, commutator_smul_left,
    commutator_hyperbolic0_null1]
  module

/-- Mixed Fermat seed on the integer translator axis:
\([\Omega,N_1]=\alpha N_0-\beta N_3\). -/
theorem commutator_fermatTorsion_null1 (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 1) =
      fermatBoost a b c hc • null 0 - fermatAngle a b ha • null 3 := by
  rw [omegaTorsion_fermatTorsion, commutator_add_left, commutator_smul_left,
    commutator_smul_left, commutator_hyperbolic0_null1, commutator_cyclic1_null1]
  module

/-- The mixed first jet on \(N_1\) differs from the pure cyclic jet by \(\alpha N_0\). -/
theorem commutator_fermatTorsion_null1_ne_cyclic {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 1) ≠
      Generators.commutator (omegaTorsion (fermatAngleSeed a b ha)) (null 1) := by
  rw [commutator_fermatTorsion_null1, commutator_fermatAngle_null1]
  intro heq
  have : fermatBoost a b c hc • null 0 = 0 := by
    have h' := congrArg (fun z => z + fermatAngle a b ha • null 3) heq
    simpa [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero] using h'
  exact null_ne_zero 0 ((smul_eq_zero.mp this).resolve_left (ne_of_gt h.1))

/-- One-parameter sandwich groups of mixed vs cyclic Fermat seeds disagree on
the integer axis \(N_1\). -/
theorem exists_sandwich_fermat_ne_cyclic_null1 {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc) :
    ∃ t : ℝ,
      sandwich (exp (t • omegaTorsion (fermatTorsion a b c ha hc))) (null 1) ≠
        sandwich (exp (t • omegaTorsion (fermatAngleSeed a b ha))) (null 1) := by
  by_contra! hforall
  have hf := hasDerivAt_sandwich_exp_smul
    (omegaTorsion_reverse (fermatTorsion a b c ha hc)) (null 1)
  have hg := hasDerivAt_sandwich_exp_smul
    (omegaTorsion_reverse (fermatAngleSeed a b ha)) (null 1)
  have hfun :
      (fun t : ℝ =>
          sandwich (exp (t • omegaTorsion (fermatTorsion a b c ha hc))) (null 1)) =
        fun t : ℝ =>
          sandwich (exp (t • omegaTorsion (fermatAngleSeed a b ha))) (null 1) :=
    funext hforall
  rw [hfun] at hf
  exact commutator_fermatTorsion_null1_ne_cyclic ha hc h (hf.unique hg)

/-! ### Second jet on the cyclic plane \(N_3\) (feedback into time) -/

theorem commutator_fermatAngle_null3 (a b : ℤ) (ha : a ≠ 0) :
    Generators.commutator (omegaTorsion (fermatAngleSeed a b ha)) (null 3) =
      fermatAngle a b ha • null 1 := by
  rw [fermatAngleSeed, omegaTorsion_pureRotation1, commutator_smul_left,
    commutator_cyclic1_null3]
  module

theorem commutator_fermatAngle_null3_two (a b : ℤ) (ha : a ≠ 0) :
    Generators.commutator (omegaTorsion (fermatAngleSeed a b ha))
      (Generators.commutator (omegaTorsion (fermatAngleSeed a b ha)) (null 3)) =
      -(fermatAngle a b ha) ^ 2 • null 3 := by
  rw [commutator_fermatAngle_null3, commutator_smul_right, commutator_fermatAngle_null1]
  module

/-- Second nested bracket on \(N_3\): \([\Omega,[\Omega,N_3]]=\alpha\beta N_0-\beta^2 N_3\). -/
theorem commutator_fermatTorsion_null3_two (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc))
      (Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 3)) =
      (fermatBoost a b c hc * fermatAngle a b ha) • null 0 -
        (fermatAngle a b ha) ^ 2 • null 3 := by
  rw [commutator_fermatTorsion_null3, commutator_smul_right,
    commutator_fermatTorsion_null1]
  module

/-- Mixed second jet on \(N_3\) differs from the pure cyclic jet by \(\alpha\beta N_0\). -/
theorem commutator_fermatTorsion_null3_two_ne_cyclic {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc))
        (Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc))
          (null 3)) ≠
      Generators.commutator (omegaTorsion (fermatAngleSeed a b ha))
        (Generators.commutator (omegaTorsion (fermatAngleSeed a b ha))
          (null 3)) := by
  rw [commutator_fermatTorsion_null3_two, commutator_fermatAngle_null3_two]
  intro heq
  have : (fermatBoost a b c hc * fermatAngle a b ha) • null 0 = 0 := by
    have h' := congrArg (fun z => z + (fermatAngle a b ha) ^ 2 • null 3) heq
    simpa [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero] using h'
  have hcoeff : fermatBoost a b c hc * fermatAngle a b ha ≠ 0 :=
    mul_ne_zero (ne_of_gt h.1) (ne_of_gt h.2.1)
  exact null_ne_zero 0 ((smul_eq_zero.mp this).resolve_left hcoeff)

/-- The mixed sandwich 2-jet on \(N_3\) is \(\alpha\beta N_0-\beta^2 N_3\). -/
theorem iteratedDeriv_two_sandwich_fermatTorsion_null3
    (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    iteratedDeriv 2
      (fun t : ℝ =>
        sandwich (exp (t • omegaTorsion (fermatTorsion a b c ha hc))) (null 3)) 0 =
      (fermatBoost a b c hc * fermatAngle a b ha) • null 0 -
        (fermatAngle a b ha) ^ 2 • null 3 := by
  rw [iteratedDeriv_two_sandwich_exp_smul
    (omegaTorsion_reverse (fermatTorsion a b c ha hc)),
    commutator_fermatTorsion_null3_two]

theorem sandwich_fermatBoost_null3 (a b c : ℤ) (hc : c ≠ 0) :
    sandwich (rotorTorsion (fermatBoostSeed a b c hc)) (null 3) = null 3 :=
  sandwich_pureBoost_null3 (fermatBoost a b c hc)

theorem sandwich_fermatAngle_null3 (a b : ℤ) (ha : a ≠ 0) :
    sandwich (rotorTorsion (fermatAngleSeed a b ha)) (null 3) =
      Real.sin (fermatAngle a b ha) • null 1 +
        Real.cos (fermatAngle a b ha) • null 3 :=
  sandwich_pureRotation1_null3 (fermatAngle a b ha)

/-- The cyclic Fermat factor rotates `N₃`; a pure boost does not. -/
theorem sandwich_fermatAngle_null3_ne_pureBoost {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hβ : 0 < fermatAngle a b ha) :
    sandwich (rotorTorsion (fermatAngleSeed a b ha)) (null 3) ≠
      sandwich (rotorTorsion (fermatBoostSeed a b c hc)) (null 3) := by
  rw [sandwich_fermatBoost_null3]
  simpa [fermatAngleSeed] using
    sandwich_pureRotation1_null3_ne_of_sin (ne_of_gt (fermatAngle_sin_pos ha hβ))

/-- Every Fermat torsion rotor still conjugates translators to translators. -/
theorem exists_sandwich_fermatTorsion_expTrans (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0)
    (p : TransParams) :
    ∃ q : TransParams,
      sandwich (fermatMotorRotor a b c ha hc) (expTrans p) = expTrans q :=
  exists_sandwich_rotorTorsion_expTrans (fermatTorsion a b c ha hc) p

/-- The one-parameter sandwich groups of a mixed Fermat seed and of its
pure-boost part disagree on `N₃`. -/
theorem exists_sandwich_fermat_ne_pureBoost {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc) :
    ∃ t : ℝ,
      sandwich (exp (t • omegaTorsion (fermatTorsion a b c ha hc))) (null 3) ≠
        sandwich (exp (t • omegaTorsion (fermatBoostSeed a b c hc))) (null 3) := by
  by_contra! hforall
  have hf := hasDerivAt_sandwich_exp_smul
    (omegaTorsion_reverse (fermatTorsion a b c ha hc)) (null 3)
  have hg := hasDerivAt_sandwich_exp_smul
    (omegaTorsion_reverse (fermatBoostSeed a b c hc)) (null 3)
  have hfun :
      (fun t : ℝ =>
          sandwich (exp (t • omegaTorsion (fermatTorsion a b c ha hc))) (null 3)) =
        fun t : ℝ =>
          sandwich (exp (t • omegaTorsion (fermatBoostSeed a b c hc))) (null 3) :=
    funext hforall
  rw [hfun] at hf
  exact commutator_fermatTorsion_null3_ne_pureBoost ha hc h (hf.unique hg)

/-! ### Live residual (sandwich / commutator attack; unproved) -/

/--
**Live residual** (dual-axis programme).

A mixed dual-axis Fermat motor cannot coexist with a positive degree-`n ≥ 3`
power sum. Attack points: sandwich defect of the cyclic rotor on the null
translator, and/or the nonzero axis interference
`interfere axis0Boost axis1Rotation ≠ 0`. Height amplification and single-axis
modular winding are **not** the intended hooks.

Does **not** claim unconditional classical FLT.
-/
def FermatMixedMotorResidual : Prop :=
  ∀ (a b c : ℤ) (n : ℕ) (_hn : 3 ≤ n) (ha : 0 < a) (_hb : 0 < b) (hc : 0 < c),
    IsMixedFermatMotor a b c (ne_of_gt ha) (ne_of_gt hc) →
      ¬ a ^ n + b ^ n = c ^ n

/-- Conditional positive classical FLT from the dual-axis residual. -/
theorem fermat_pos_of_mixed_motor_residual
    (hres : FermatMixedMotorResidual) :
    ∀ (a b c : ℤ) (n : ℕ), 3 ≤ n → 0 < a → 0 < b → 0 < c →
      ¬ (a ^ n + b ^ n = c ^ n) := by
  intro a b c n hn ha hb hc hsol
  exact hres a b c n hn ha hb hc (isMixedFermatMotor_of_sol hn ha hb hc hsol) hsol

/-- Mathlib `FermatLastTheorem` from the dual-axis residual (ℕ form). -/
theorem FermatLastTheorem_of_mixed_motor_residual
    (hres : FermatMixedMotorResidual) : FermatLastTheorem := by
  intro n hn a b c ha hb hc hsol
  have haZ : (0 : ℤ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)
  have hbZ : (0 : ℤ) < b := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)
  have hcZ : (0 : ℤ) < c := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
  have hsolZ : (a : ℤ) ^ n + (b : ℤ) ^ n = (c : ℤ) ^ n := by exact_mod_cast hsol
  exact fermat_pos_of_mixed_motor_residual hres a b c n hn haZ hbZ hcZ hsolZ

end Theorems

end DstDiophantine
