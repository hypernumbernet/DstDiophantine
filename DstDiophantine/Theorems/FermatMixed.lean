import DstDiophantine.Embedding.FermatMotor
import DstDiophantine.Embedding.NullTranslator
import DstDiophantine.Theorems.Fermat
import DstDiophantine.Algebra.MotorGroup
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.PGA.Normed
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dual-axis Fermat motor slices (real Lᵖ comparison)

Closes the geometric dichotomy used by the dual-axis programme:

* `n = 2` positive solutions are pure cyclic (`α = 0`);
* `n ≥ 3` positive solutions are mixed (`α > 0` and `β ∈ (0, π/2)`).

The mixed seed leaks the additive null axis \(N_1\) into the time-null
generator \(N_0\) at first order. On a positive solution the dual-axis
characteristic is elliptic (\(\beta^2>\alpha^2\)), so the finite sandwich of
\(N_1\) is a harmonic oscillator whose time-null remainder is a strictly
positive multiple of \(N_0\) precisely when \(\alpha>0\). Those identities sit
on the embedding axis itself; they do **not** yet mention
`powerSumMotor = 1`. Unconditional classical FLT is **not** claimed.
-/

namespace DstDiophantine

namespace Theorems

open _root_.DstDiophantine.Embedding Real
open Amplification Motor Sandwich Generators MotorGroup PGA Operations Invariant
open CliffordAlgebra NormedSpace PGANormed

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

/-! ### Sandwich / commutator connection (geometric, independent of FLT)

The mixed seed is the sum of a radial boost and an axis-1 rotation. Brackets
are linear, so the jets on \(N_1\) and \(N_3\) assemble from the two factors.
-/

/-! #### First jet and finite sandwich on \(N_3\) -/

theorem commutator_fermatBoost_null3 (a b c : ℤ) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatBoostSeed a b c hc)) (null 3) = 0 := by
  rw [fermatBoostSeed, omegaTorsion_pureBoost, commutator_smul_left,
    commutator_hyperbolic0_null3, smul_zero]

theorem commutator_fermatAngle_null3 (a b : ℤ) (ha : a ≠ 0) :
    Generators.commutator (omegaTorsion (fermatAngleSeed a b ha)) (null 3) =
      fermatAngle a b ha • null 1 := by
  rw [fermatAngleSeed, omegaTorsion_pureRotation1, commutator_smul_left,
    commutator_cyclic1_null3]
  module

/-- Mixed first jet on the cyclic-plane translator: \([\Omega,N_3]=\beta N_1\). -/
theorem commutator_fermatTorsion_null3 (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 3) =
      fermatAngle a b ha • null 1 := by
  rw [omegaTorsion_fermatTorsion_add, commutator_add_left,
    commutator_fermatBoost_null3, commutator_fermatAngle_null3, zero_add]

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

/-- The one-parameter sandwich groups of a mixed Fermat seed and of its
pure-boost part disagree on `N₃`. -/
theorem exists_sandwich_fermat_ne_pureBoost {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc) :
    ∃ t : ℝ,
      sandwich (exp (t • omegaTorsion (fermatTorsion a b c ha hc))) (null 3) ≠
        sandwich (exp (t • omegaTorsion (fermatBoostSeed a b c hc))) (null 3) :=
  exists_sandwich_exp_ne_of_commutator_ne
    (omegaTorsion_reverse (fermatTorsion a b c ha hc))
    (omegaTorsion_reverse (fermatBoostSeed a b c hc))
    (commutator_fermatTorsion_null3_ne_pureBoost ha hc h)

/-! #### First jet on the integer axis \(N_1\) (temporal leak) -/

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
  rw [omegaTorsion_fermatTorsion_add, commutator_add_left,
    commutator_fermatBoost_null1, commutator_fermatAngle_null1, neg_smul,
    sub_eq_add_neg]

/-- Radial boost of the time translator: \([\Omega_\alpha,N_0]=\alpha N_1\). -/
theorem commutator_fermatBoost_null0 (a b c : ℤ) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatBoostSeed a b c hc)) (null 0) =
      fermatBoost a b c hc • null 1 := by
  rw [fermatBoostSeed, omegaTorsion_pureBoost, commutator_smul_left,
    commutator_hyperbolic0_null0]
  module

/-- Axis-1 rotation leaves the time translator inert. -/
theorem commutator_fermatAngle_null0 (a b : ℤ) (ha : a ≠ 0) :
    Generators.commutator (omegaTorsion (fermatAngleSeed a b ha)) (null 0) = 0 := by
  rw [fermatAngleSeed, omegaTorsion_pureRotation1, commutator_smul_left,
    commutator_cyclic1_null0, smul_zero]

/-- Mixed first jet on the time translator: \([\Omega,N_0]=\alpha N_1\). -/
theorem commutator_fermatTorsion_null0 (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 0) =
      fermatBoost a b c hc • null 1 := by
  rw [omegaTorsion_fermatTorsion_add, commutator_add_left,
    commutator_fermatBoost_null0, commutator_fermatAngle_null0, add_zero]

/-- Second nested bracket on the integer axis:
\([\Omega,[\Omega,N_1]]=(\alpha^2-\beta^2)N_1\). -/
theorem commutator_fermatTorsion_null1_two (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc))
      (Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 1)) =
      (fermatBoost a b c hc ^ 2 - fermatAngle a b ha ^ 2) • null 1 := by
  rw [commutator_fermatTorsion_null1, sub_eq_add_neg, ← neg_smul,
    commutator_add_right, commutator_smul_right, commutator_smul_right,
    commutator_fermatTorsion_null0, commutator_fermatTorsion_null3]
  module

private theorem commutator_fermatTorsion_null1_ne_cyclic {a b c : ℤ}
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
        sandwich (exp (t • omegaTorsion (fermatAngleSeed a b ha))) (null 1) :=
  exists_sandwich_exp_ne_of_commutator_ne
    (omegaTorsion_reverse (fermatTorsion a b c ha hc))
    (omegaTorsion_reverse (fermatAngleSeed a b ha))
    (commutator_fermatTorsion_null1_ne_cyclic ha hc h)

/-! #### Second jet on \(N_3\) (feedback into time) -/

/-- Second nested bracket on \(N_3\): \([\Omega,[\Omega,N_3]]=\alpha\beta N_0-\beta^2 N_3\). -/
theorem commutator_fermatTorsion_null3_two (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc))
      (Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 3)) =
      (fermatBoost a b c hc * fermatAngle a b ha) • null 0 -
        (fermatAngle a b ha) ^ 2 • null 3 := by
  rw [commutator_fermatTorsion_null3, commutator_smul_right,
    commutator_fermatTorsion_null1]
  module

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

/-- Every Fermat torsion rotor still conjugates translators to translators. -/
theorem exists_sandwich_fermatTorsion_expTrans (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0)
    (p : TransParams) :
    ∃ q : TransParams,
      sandwich (fermatMotorRotor a b c ha hc) (expTrans p) = expTrans q :=
  exists_sandwich_rotorTorsion_expTrans (fermatTorsion a b c ha hc) p

/-! ### Elliptic characteristic on a positive solution -/

/-- Dual-axis frequency \(\omega=\sqrt{\beta^2-\alpha^2}\). -/
noncomputable def fermatMixedFreq (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) : ℝ :=
  Real.sqrt (fermatAngle a b ha ^ 2 - fermatBoost a b c hc ^ 2)

theorem J_fermatTorsion (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    J (fermatTorsion a b c ha hc) =
      (fermatBoost a b c hc ^ 2 - fermatAngle a b ha ^ 2) / 2 := by
  rw [J_coef]
  simp [fermatTorsion]
  ring

private theorem half_log_one_add_sq_le_arctan {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.log (1 + t ^ 2) / 2 ≤ Real.arctan t := by
  let f : ℝ → ℝ := fun x => 2 * Real.arctan x - Real.log (1 + x ^ 2)
  let f' : ℝ → ℝ := fun x => 2 * (1 - x) / (1 + x ^ 2)
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ x, HasDerivAt f (f' x) x := by
    intro x
    have hxpos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x :=
      (hasDerivAt_pow (2 : ℕ) x).congr_deriv (by simp)
    have harg : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      have hfun : (fun y : ℝ => 1 + y ^ 2) = (fun _ => (1 : ℝ)) + fun y => y ^ 2 := by
        funext y; simp
      rw [hfun]
      exact ((hasDerivAt_const x (1 : ℝ)).add hsq).congr_deriv (by simp)
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2))
        (1 / (1 + x ^ 2) * (2 * x)) x := by
      have h := (Real.hasDerivAt_log (ne_of_gt hxpos)).comp x harg
      exact h.congr_deriv (by field_simp)
    have hartan : HasDerivAt (fun y : ℝ => 2 * Real.arctan y)
        (2 * (1 / (1 + x ^ 2))) x :=
      (Real.hasDerivAt_arctan x).const_mul 2
    have hfun : f = (fun y => 2 * Real.arctan y) - fun y => Real.log (1 + y ^ 2) := by
      funext y; rfl
    rw [hfun]
    exact (hartan.sub hlog).congr_deriv (by simp [f']; field_simp)
  have hf_nonneg : 0 ≤ f t := by
    by_cases ht : t = 0
    · subst ht; simp [f]
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
      have hcont : ContinuousOn f (Set.Icc (0 : ℝ) t) :=
        fun x _ => (hderiv x).continuousAt.continuousWithinAt
      obtain ⟨c, hc, hmean⟩ :=
        exists_hasDerivAt_eq_slope f f' htpos hcont fun x _ => hderiv x
      have hf'c : 0 ≤ f' c := by
        have : c < 1 := lt_of_lt_of_le hc.2 ht1
        exact div_nonneg (by nlinarith) (by nlinarith [sq_nonneg c])
      have hfrac : 0 ≤ (f t - f 0) / (t - 0) := by
        rwa [← hmean]
      have hfrac' : 0 ≤ f t / t := by simpa [hf0] using hfrac
      have : 0 * t ≤ f t := (le_div_iff₀ htpos).mp hfrac'
      simpa using this
  have : 0 ≤ 2 * Real.arctan t - Real.log (1 + t ^ 2) := hf_nonneg
  linarith

private theorem fermatBoost_sq_add_lt_two_sq {a b c : ℤ} {n : ℕ}
    (hn : 1 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    (a : ℝ) ^ 2 + (b : ℝ) ^ 2 < 2 * (c : ℝ) ^ 2 := by
  have ha_lt := fermat_pos_lt hn ha hb hc hsol
  have hb_lt : b < c :=
    fermat_pos_lt hn hb ha hc (by rwa [add_comm] at hsol)
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast (le_of_lt ha)
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast (le_of_lt hb)
  have h1 : (a : ℝ) ^ 2 < (c : ℝ) ^ 2 :=
    pow_lt_pow_left₀ (by exact_mod_cast ha_lt) haR (by decide : (2 : ℕ) ≠ 0)
  have h2 : (b : ℝ) ^ 2 < (c : ℝ) ^ 2 :=
    pow_lt_pow_left₀ (by exact_mod_cast hb_lt) hbR (by decide : (2 : ℕ) ≠ 0)
  linarith

private theorem fermatBoost_lt_half_log_two {a b c : ℤ} {n : ℕ}
    (hn : 1 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    fermatBoost a b c (ne_of_gt hc) < Real.log 2 / 2 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hsq := fermatBoost_sq_add_lt_two_sq hn ha hb hc hsol
  have hL2 : fermatL2 a b = Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
    unfold fermatL2
    rw [natAbs_coe_eq_coe_of_pos ha, natAbs_coe_eq_coe_of_pos hb]
  have hcAbs : (c.natAbs : ℝ) = (c : ℝ) := natAbs_coe_eq_coe_of_pos hc
  have harg : fermatL2 a b / (c.natAbs : ℝ) < Real.sqrt 2 := by
    rw [hL2, hcAbs, div_lt_iff₀ hcR]
    have hnn : 0 ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hrt : 0 ≤ Real.sqrt 2 * (c : ℝ) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hcR)
    rw [Real.sqrt_lt hnn hrt]
    have : (Real.sqrt 2 * (c : ℝ)) ^ 2 = 2 * (c : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
    rwa [this]
  have hpos : 0 < fermatL2 a b / (c.natAbs : ℝ) := by
    exact div_pos (fermatL2_pos (Or.inl (ne_of_gt ha)))
      (Nat.cast_pos.mpr (Int.natAbs_pos.mpr (ne_of_gt hc)))
  have hlog := Real.log_lt_log hpos harg
  have hsqrt : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
    rw [Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  unfold fermatBoost
  rwa [hsqrt] at hlog

theorem fermatBoost_lt_fermatAngle {a b c : ℤ} {n : ℕ}
    (hn : 1 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    fermatBoost a b c (ne_of_gt hc) < fermatAngle a b (ne_of_gt ha) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have ha_lt := fermat_pos_lt hn ha hb hc hsol
  by_cases hba : b ≤ a
  · set t : ℝ := (b : ℝ) / a
    have ht0 : 0 ≤ t := div_nonneg (le_of_lt hbR) (le_of_lt haR)
    have ht1 : t ≤ 1 := (div_le_one haR).mpr (by exact_mod_cast hba)
    have hc_gt_a : (a : ℝ) < c := by exact_mod_cast ha_lt
    have hL2 : fermatL2 a b = Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
      unfold fermatL2
      rw [natAbs_coe_eq_coe_of_pos ha, natAbs_coe_eq_coe_of_pos hb]
    have hnum : 0 < fermatL2 a b := fermatL2_pos (Or.inl (ne_of_gt ha))
    have hstrict : fermatL2 a b / (c.natAbs : ℝ) < fermatL2 a b / a := by
      rw [natAbs_coe_eq_coe_of_pos hc]
      exact div_lt_div_of_pos_left hnum haR hc_gt_a
    have hL2a : fermatL2 a b / a = Real.sqrt (1 + t ^ 2) := by
      have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt haR
      calc fermatL2 a b / a
          = Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / a := by rw [hL2]
        _ = Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / Real.sqrt ((a : ℝ) ^ 2) := by
            rw [Real.sqrt_sq (le_of_lt haR)]
        _ = Real.sqrt (((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (a : ℝ) ^ 2) := by
            exact (Real.sqrt_div (add_nonneg (sq_nonneg _) (sq_nonneg _)) _).symm
        _ = Real.sqrt (1 + ((b : ℝ) / a) ^ 2) := by
            congr 1
            field_simp [ha_ne]
        _ = Real.sqrt (1 + t ^ 2) := by
            simp [t]
    have hlog_lt : Real.log (fermatL2 a b / (c.natAbs : ℝ)) <
        Real.log (Real.sqrt (1 + t ^ 2)) :=
      Real.log_lt_log (div_pos hnum (Nat.cast_pos.mpr (Int.natAbs_pos.mpr (ne_of_gt hc))))
        (hL2a ▸ hstrict)
    have hhalf : Real.log (Real.sqrt (1 + t ^ 2)) = Real.log (1 + t ^ 2) / 2 :=
      Real.log_sqrt (by nlinarith [sq_nonneg t])
    have hle := half_log_one_add_sq_le_arctan ht0 ht1
    have hβ : fermatAngle a b (ne_of_gt ha) = Real.arctan t := by
      unfold fermatAngle t
      rw [natAbs_coe_eq_coe_of_pos ha, natAbs_coe_eq_coe_of_pos hb]
    unfold fermatBoost
    rw [hβ]
    linarith [hlog_lt, hhalf, hle]
  · have hlt : a < b := lt_of_not_ge hba
    have hβ : Real.pi / 4 < fermatAngle a b (ne_of_gt ha) := by
      unfold fermatAngle
      rw [natAbs_coe_eq_coe_of_pos ha, natAbs_coe_eq_coe_of_pos hb]
      have : (1 : ℝ) < (b : ℝ) / a := (one_lt_div haR).mpr (by exact_mod_cast hlt)
      have hart : Real.arctan 1 < Real.arctan ((b : ℝ) / a) :=
        (Real.arctan_lt_arctan_iff).mpr this
      rwa [Real.arctan_one] at hart
    have hα := fermatBoost_lt_half_log_two hn ha hb hc hsol
    have hlog : Real.log 2 / 2 < Real.pi / 4 := by
      have : Real.log 2 < 1 := by
        have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          (by norm_num)
        norm_num at h ⊢
        exact h
      nlinarith [Real.pi_gt_three]
    linarith

theorem fermatMixedFreq_pos {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    0 < fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc) := by
  unfold fermatMixedFreq
  refine Real.sqrt_pos.mpr ?_
  have hn1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 3) hn
  have hα := fermatBoost_pos_of_sol hn ha hb hc hsol
  have hlt := fermatBoost_lt_fermatAngle hn1 ha hb hc hsol
  have hβ : 0 ≤ fermatAngle a b (ne_of_gt ha) :=
    fermatAngle_nonneg a b (ne_of_gt ha)
  nlinarith [hlt, hβ, hα]

private theorem fermatMixedFreq_lt_angle {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc) <
      fermatAngle a b (ne_of_gt ha) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 3) hn
  have hα := fermatBoost_pos_of_sol hn ha hb hc hsol
  have hβ : 0 < fermatAngle a b (ne_of_gt ha) :=
    fermatAngle_pos_of_b_ne (ne_of_gt ha) (ne_of_gt hb)
  have hlt := fermatBoost_lt_fermatAngle hn1 ha hb hc hsol
  unfold fermatMixedFreq
  set α := fermatBoost a b c (ne_of_gt hc)
  set β := fermatAngle a b (ne_of_gt ha)
  have hnn : 0 ≤ β ^ 2 - α ^ 2 := by nlinarith [hlt, le_of_lt hβ]
  have hsq : β ^ 2 - α ^ 2 < β ^ 2 := by nlinarith [sq_pos_of_pos hα]
  have hsqrt := Real.sqrt_lt_sqrt hnn hsq
  have hβsq : Real.sqrt (β ^ 2) = β := Real.sqrt_sq (le_of_lt hβ)
  rwa [hβsq] at hsqrt

/-! ### Finite elliptic sandwich of \(N_1\) -/

private noncomputable def pgaCoord (i : BasisIndex) : PGA →ₗ[ℝ] ℝ where
  toFun x := vectorBasis.repr x i
  map_add' x y := by simp
  map_smul' r x := by simp

private theorem hasDerivAt_pgaCoord {f : ℝ → PGA} {f' : PGA} {t : ℝ}
    (hf : HasDerivAt f f' t) (i : BasisIndex) :
    HasDerivAt (fun s => pgaCoord i (f s)) (pgaCoord i f') t := by
  refine ((hasDerivAt_const t
      (LinearMap.toContinuousLinearMap (pgaCoord i))).clm_apply hf).congr_deriv ?_
  change (0 : PGA →L[ℝ] ℝ) (f t) + pgaCoord i f' = pgaCoord i f'
  simp

private theorem oscillator_eval {y y' : ℝ → ℝ} {ω : ℝ} (hω : 0 < ω)
    (hy : ∀ t, HasDerivAt y (y' t) t)
    (hy2 : ∀ t, HasDerivAt y' (-ω ^ 2 * y t) t) (t : ℝ) :
    y t = y 0 * Real.cos (ω * t) + y' 0 * Real.sin (ω * t) / ω := by
  let c0 := y 0
  let c1 := y' 0
  let z : ℝ → ℝ := fun s =>
    y s - c0 * Real.cos (ω * s) - c1 * Real.sin (ω * s) / ω
  let z' : ℝ → ℝ := fun s =>
    y' s + c0 * ω * Real.sin (ω * s) - c1 * Real.cos (ω * s)
  have hω0 : ω ≠ 0 := ne_of_gt hω
  have hz0 : z 0 = 0 := by
    simp [z, c0, Real.cos_zero, Real.sin_zero]
  have hz'0 : z' 0 = 0 := by
    simp [z', c1, Real.sin_zero, Real.cos_zero]
  have hmul (s : ℝ) : HasDerivAt (fun u => ω * u) ω s :=
    ((hasDerivAt_id s).const_mul ω).congr_deriv (by simp)
  have hcos (s : ℝ) :
      HasDerivAt (fun u => Real.cos (ω * u)) (-Real.sin (ω * s) * ω) s :=
    (hmul s).cos
  have hsin (s : ℝ) :
      HasDerivAt (fun u => Real.sin (ω * u)) (Real.cos (ω * s) * ω) s :=
    (hmul s).sin
  have hz (s : ℝ) : HasDerivAt z (z' s) s := by
    have h1 := (hcos s).const_mul c0
    have h2 := ((hsin s).div_const ω).const_mul c1
    have hfun :
        z = (y - fun u => c0 * Real.cos (ω * u)) -
          fun u => c1 * (Real.sin (ω * u) / ω) := by
      funext u; simp [z, mul_div_assoc]
    rw [hfun]
    exact (((hy s).sub h1).sub h2).congr_deriv (by simp [z']; field_simp [hω0])
  have hz2 (s : ℝ) : HasDerivAt z' (-ω ^ 2 * z s) s := by
    have h1 := (hsin s).const_mul (c0 * ω)
    have h2 := (hcos s).const_mul c1
    have hfun :
        z' = (y' + fun u => c0 * ω * Real.sin (ω * u)) -
          fun u => c1 * Real.cos (ω * u) := by
      funext u; simp [z']
    rw [hfun]
    exact (((hy2 s).add h1).sub h2).congr_deriv (by simp [z]; field_simp [hω0]; ring)
  let E : ℝ → ℝ := fun s => z' s ^ 2 + ω ^ 2 * z s ^ 2
  have hE0 : E 0 = 0 := by simp [E, hz0, hz'0]
  have hE' (s : ℝ) : HasDerivAt E 0 s := by
    have hsqz' : HasDerivAt (fun u => z' u ^ 2) (2 * z' s * (-ω ^ 2 * z s)) s := by
      have hfun : (fun u => z' u ^ 2) = z' * z' := by
        funext u; simp [pow_two]
      rw [hfun]
      exact ((hz2 s).mul (hz2 s)).congr_deriv (by ring)
    have hsqz : HasDerivAt (fun u => z u ^ 2) (2 * z s * z' s) s := by
      have hfun : (fun u => z u ^ 2) = z * z := by
        funext u; simp [pow_two]
      rw [hfun]
      exact ((hz s).mul (hz s)).congr_deriv (by ring)
    have hfun : E = (fun u => z' u ^ 2) + fun u => ω ^ 2 * z u ^ 2 := by
      funext u; simp [E]
    rw [hfun]
    exact (hsqz'.add (hsqz.const_mul (ω ^ 2))).congr_deriv (by ring)
  have hconst : E t = E 0 :=
    is_const_of_deriv_eq_zero (fun u => (hE' u).differentiableAt)
      (fun u => (hE' u).deriv) t 0
  have hE : E t = 0 := hconst.trans hE0
  have hz_eq : z t = 0 := by
    have hEu : z' t ^ 2 + ω ^ 2 * z t ^ 2 = 0 := by simpa [E] using hE
    have hωsq : 0 < ω ^ 2 := pow_pos hω 2
    have hzsq : z t ^ 2 = 0 := by
      nlinarith [hEu, sq_nonneg (z' t), hωsq]
    exact (sq_eq_zero_iff).mp hzsq
  simp [z] at hz_eq
  linarith [hz_eq]

theorem sandwich_fermatTorsion_null1_elliptic {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hω : 0 < fermatMixedFreq a b c ha hc) (t : ℝ) :
    sandwich (exp (t • omegaTorsion (fermatTorsion a b c ha hc))) (null 1) =
      Real.cos (fermatMixedFreq a b c ha hc * t) • null 1 +
        (Real.sin (fermatMixedFreq a b c ha hc * t) / fermatMixedFreq a b c ha hc) •
          (fermatBoost a b c hc • null 0 - fermatAngle a b ha • null 3) := by
  set Ω := omegaTorsion (fermatTorsion a b c ha hc)
  set α := fermatBoost a b c hc
  set β := fermatAngle a b ha
  set ω := fermatMixedFreq a b c ha hc
  set v1 := α • null 0 - β • null 3
  have hΩ : reverse Ω = -Ω := omegaTorsion_reverse (fermatTorsion a b c ha hc)
  have hcomm1 := commutator_fermatTorsion_null1 a b c ha hc
  have hcomm2 := commutator_fermatTorsion_null1_two a b c ha hc
  have hkap : α ^ 2 - β ^ 2 = -ω ^ 2 := by
    have hnn : 0 ≤ β ^ 2 - α ^ 2 := (Real.sqrt_pos.mp hω).le
    simp only [ω, fermatMixedFreq, α, β]
    rw [Real.sq_sqrt hnn]
    ring
  let f : ℝ → PGA := fun s => sandwich (exp (s • Ω)) (null 1)
  let g : ℝ → PGA := fun s => sandwich (exp (s • Ω)) v1
  have hf (s : ℝ) : HasDerivAt f (g s) s := by
    have hder := hasDerivAt_sandwich_exp_smul_at hΩ (null 1) s
    refine hder.congr_deriv ?_
    rw [hcomm1]
  have hg (s : ℝ) : HasDerivAt g ((α ^ 2 - β ^ 2) • f s) s := by
    have hder := hasDerivAt_sandwich_exp_smul_at hΩ v1 s
    have hv : commutator Ω v1 = (α ^ 2 - β ^ 2) • null 1 := by
      have hinner : commutator Ω (null 1) = v1 := by
        simpa [Ω, v1, α, β] using hcomm1
      simpa [Ω, α, β, hinner] using hcomm2
    refine hder.congr_deriv ?_
    rw [hv, sandwich_smul]
  have hgom (s : ℝ) : HasDerivAt g (-ω ^ 2 • f s) s :=
    (hg s).congr_deriv (by rw [hkap])
  let cand : ℝ → PGA := fun s =>
    Real.cos (ω * s) • null 1 + (Real.sin (ω * s) / ω) • v1
  have hcoords (i : BasisIndex) :
      pgaCoord i (f t) = pgaCoord i (cand t) := by
    let yi : ℝ → ℝ := fun s => pgaCoord i (f s)
    let yi' : ℝ → ℝ := fun s => pgaCoord i (g s)
    have hyi (s : ℝ) : HasDerivAt yi (yi' s) s :=
      hasDerivAt_pgaCoord (hf s) i
    have hyi2 (s : ℝ) : HasDerivAt yi' (-ω ^ 2 * yi s) s := by
      have h := hasDerivAt_pgaCoord (hgom s) i
      simpa [yi, map_smul, smul_eq_mul] using h
    have heval := oscillator_eval hω hyi hyi2 t
    have hyi0 : yi 0 = pgaCoord i (null 1) := by
      simp [yi, f, zero_smul, NormedSpace.exp_zero, sandwich_one]
    have hyi'0 : yi' 0 = pgaCoord i v1 := by
      simp [yi', g, zero_smul, NormedSpace.exp_zero, sandwich_one]
    have hcand : pgaCoord i (cand t) =
        pgaCoord i (null 1) * Real.cos (ω * t) +
          pgaCoord i v1 * Real.sin (ω * t) / ω := by
      simp [cand, map_add, map_smul, smul_eq_mul]
      ring
    simp only [yi, yi'] at heval hyi0 hyi'0
    rw [heval, hyi0, hyi'0, hcand]
  apply (LinearEquiv.injective vectorBasis.repr)
  ext i
  simpa [pgaCoord, f, cand, map_add, map_smul, smul_eq_mul] using hcoords i

/-- Time-null remainder of the finite sandwich of the integer axis. -/
theorem sandwich_fermatTorsion_null1_timeRemainder {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hω : 0 < fermatMixedFreq a b c ha hc) (t : ℝ) :
    sandwich (exp (t • omegaTorsion (fermatTorsion a b c ha hc))) (null 1) -
        Real.cos (fermatMixedFreq a b c ha hc * t) • null 1 +
          (Real.sin (fermatMixedFreq a b c ha hc * t) /
            fermatMixedFreq a b c ha hc * fermatAngle a b ha) • null 3 =
      (fermatBoost a b c hc * Real.sin (fermatMixedFreq a b c ha hc * t) /
        fermatMixedFreq a b c ha hc) • null 0 := by
  rw [sandwich_fermatTorsion_null1_elliptic ha hc hω t]
  module

/-- On a mixed elliptic seat the time-null remainder at unit time is nonzero. -/
private theorem sandwich_fermatTorsion_null1_time_ne_zero {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc)
    (hω : 0 < fermatMixedFreq a b c ha hc)
    (hωπ : fermatMixedFreq a b c ha hc < Real.pi) :
    sandwich (fermatMotorRotor a b c ha hc) (null 1) -
        Real.cos (fermatMixedFreq a b c ha hc) • null 1 +
          (Real.sin (fermatMixedFreq a b c ha hc) /
            fermatMixedFreq a b c ha hc * fermatAngle a b ha) • null 3 ≠ 0 := by
  have hrot : fermatMotorRotor a b c ha hc =
      exp (omegaTorsion (fermatTorsion a b c ha hc)) := rfl
  have ht := sandwich_fermatTorsion_null1_timeRemainder ha hc hω (1 : ℝ)
  simp only [hrot, one_smul, mul_one] at ht ⊢
  rw [ht]
  intro hz
  have hα : fermatBoost a b c hc ≠ 0 := ne_of_gt h.1
  have hsin : Real.sin (fermatMixedFreq a b c ha hc) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hω hωπ)
  have hcoeff :
      fermatBoost a b c hc * Real.sin (fermatMixedFreq a b c ha hc) /
        fermatMixedFreq a b c ha hc ≠ 0 :=
    div_ne_zero (mul_ne_zero hα hsin) (ne_of_gt hω)
  exact null_ne_zero 0 ((smul_eq_zero.mp hz).resolve_left hcoeff)

theorem sandwich_fermatTorsion_null1_time_ne_zero_of_sol {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    sandwich (fermatMotorRotor a b c (ne_of_gt ha) (ne_of_gt hc)) (null 1) -
        Real.cos (fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc)) • null 1 +
          (Real.sin (fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc)) /
            fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc) *
              fermatAngle a b (ne_of_gt ha)) • null 3 ≠ 0 := by
  have hmix := isMixedFermatMotor_of_sol hn ha hb hc hsol
  have hω := fermatMixedFreq_pos hn ha hb hc hsol
  have hωπ : fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc) < Real.pi :=
    lt_trans (fermatMixedFreq_lt_angle hn ha hb hc hsol)
      (lt_trans (fermatAngle_lt_half_pi a b (ne_of_gt ha))
        (by nlinarith [Real.pi_pos]))
  exact sandwich_fermatTorsion_null1_time_ne_zero (ne_of_gt ha) (ne_of_gt hc)
    hmix hω hωπ

/-! ### Live residual (sandwich / commutator attack; unproved) -/

/--
**Live residual** (dual-axis programme).

A mixed dual-axis Fermat motor cannot coexist with a positive degree-`n ≥ 3`
power sum. The finite elliptic sandwich of \(N_1\) already isolates a
nonzero time-null remainder on any mixed seed; the residual is to promote
that remainder to an incompatibility with \(a^n+b^n=c^n\). Height
amplification and single-axis modular winding are **not** the intended hooks.

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
