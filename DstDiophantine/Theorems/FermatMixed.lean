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
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
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
positive multiple of \(N_0\) precisely when \(\alpha>0\). The power sum of
positive bases is the scalar `exp(n α) (cos β ^ n + sin β ^ n)` on that seat.
Equal positive real legs realise the scalar with `α > 0`, so the relation
survives over `ℝ`. Neither positive integer base divides the other. On a
positive integer solution the excess `a² + b² - c²` is a positive integer,
so the boost equals `½ log(1 + (a²+b²-c²)/c²)` and is at least
`½ log(1 + 1/c²)`. For an odd prime exponent dividing none of three coprime
positive bases, `a + b`, `c - a`, and `c - b` are pairwise coprime pure `n`th
powers summing to `2c`, with positive roots. The quotient of the power sum
by `a + b` is a pure `n`th power coprime to that sum. The third base is the
product of the root of `a + b` and the root of that quotient, both greater
than one.
Unconditional classical FLT is **not** claimed.
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

/-! ### Power sum as a scalar on the dual-axis seat -/

private theorem fermatL2_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    fermatL2 a b = Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
  unfold fermatL2
  rw [natAbs_coe_eq_coe_of_pos ha, natAbs_coe_eq_coe_of_pos hb]

private theorem fermat_hypot_div {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (1 + ((b : ℝ) / a) ^ 2) = fermatL2 a b / a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt haR
  rw [fermatL2_of_pos ha hb]
  have hnn : 0 ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc Real.sqrt (1 + ((b : ℝ) / a) ^ 2)
      = Real.sqrt (((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (a : ℝ) ^ 2) := by
        congr 1
        field_simp [ha_ne]
    _ = Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / Real.sqrt ((a : ℝ) ^ 2) := by
        exact Real.sqrt_div hnn _
    _ = Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / a := by
        rw [Real.sqrt_sq haR.le]

theorem fermatAngle_cos_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    Real.cos (fermatAngle a b (ne_of_gt ha)) = (a : ℝ) / fermatL2 a b := by
  have ha_ne : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  unfold fermatAngle
  rw [natAbs_coe_eq_coe_of_pos ha, natAbs_coe_eq_coe_of_pos hb, Real.cos_arctan,
    fermat_hypot_div ha hb]
  field_simp [ha_ne, (fermatL2_pos (Or.inl (ne_of_gt ha))).ne']

theorem fermatAngle_sin_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    Real.sin (fermatAngle a b (ne_of_gt ha)) = (b : ℝ) / fermatL2 a b := by
  have ha_ne : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  unfold fermatAngle
  rw [natAbs_coe_eq_coe_of_pos ha, natAbs_coe_eq_coe_of_pos hb, Real.sin_arctan,
    fermat_hypot_div ha hb]
  field_simp [ha_ne, (fermatL2_pos (Or.inl (ne_of_gt ha))).ne']

theorem fermat_exp_boost_of_pos {a b c : ℤ} (ha : 0 < a) (hc : 0 < c) :
    Real.exp (fermatBoost a b c (ne_of_gt hc)) = fermatL2 a b / (c : ℝ) := by
  have hpos : 0 < fermatL2 a b / (c.natAbs : ℝ) :=
    div_pos (fermatL2_pos (Or.inl (ne_of_gt ha)))
      (Nat.cast_pos.mpr (Int.natAbs_pos.mpr (ne_of_gt hc)))
  unfold fermatBoost
  rw [Real.exp_log hpos, natAbs_coe_eq_coe_of_pos hc]

/--
For positive bases the power-sum ratio is the dual-axis scalar
`exp(n α) (cos β ^ n + sin β ^ n)`.
-/
theorem fermat_polar_ratio {a b c : ℤ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((a : ℝ) ^ n + (b : ℝ) ^ n) / (c : ℝ) ^ n =
      Real.exp (n * fermatBoost a b c (ne_of_gt hc)) *
        (Real.cos (fermatAngle a b (ne_of_gt ha)) ^ n +
          Real.sin (fermatAngle a b (ne_of_gt ha)) ^ n) := by
  set α := fermatBoost a b c (ne_of_gt hc)
  set β := fermatAngle a b (ne_of_gt ha)
  set r := fermatL2 a b
  have hr : 0 < r := fermatL2_pos (Or.inl (ne_of_gt ha))
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  have ha_eq : (a : ℝ) = r * Real.cos β := by
    rw [fermatAngle_cos_of_pos ha hb]
    exact (mul_div_cancel₀ (a : ℝ) hr.ne').symm
  have hb_eq : (b : ℝ) = r * Real.sin β := by
    rw [fermatAngle_sin_of_pos ha hb]
    exact (mul_div_cancel₀ (b : ℝ) hr.ne').symm
  have hexp : Real.exp α = r / (c : ℝ) := fermat_exp_boost_of_pos ha hc
  calc ((a : ℝ) ^ n + (b : ℝ) ^ n) / (c : ℝ) ^ n
      = ((r * Real.cos β) ^ n + (r * Real.sin β) ^ n) / (c : ℝ) ^ n := by
        rw [ha_eq, hb_eq]
    _ = (r ^ n * (Real.cos β ^ n + Real.sin β ^ n)) / (c : ℝ) ^ n := by
        simp [mul_pow, mul_add]
    _ = (r / (c : ℝ)) ^ n * (Real.cos β ^ n + Real.sin β ^ n) := by
        set s := Real.cos β ^ n + Real.sin β ^ n
        rw [div_eq_mul_inv, mul_assoc, mul_left_comm (r ^ n) s, ← mul_assoc,
          ← div_eq_mul_inv, div_pow]
        ring
    _ = Real.exp α ^ n * (Real.cos β ^ n + Real.sin β ^ n) := by rw [hexp]
    _ = Real.exp (n * α) * (Real.cos β ^ n + Real.sin β ^ n) := by
        rw [Real.exp_nat_mul]

theorem fermat_solution_iff_polar {a b c : ℤ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ n + b ^ n = c ^ n ↔
      Real.exp (n * fermatBoost a b c (ne_of_gt hc)) *
        (Real.cos (fermatAngle a b (ne_of_gt ha)) ^ n +
          Real.sin (fermatAngle a b (ne_of_gt ha)) ^ n) = 1 := by
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  constructor
  · intro hsol
    have hR : (a : ℝ) ^ n + (b : ℝ) ^ n = (c : ℝ) ^ n := by exact_mod_cast hsol
    rw [← fermat_polar_ratio ha hb hc, hR, div_self (pow_ne_zero n hc0)]
  · intro h
    have hR : (a : ℝ) ^ n + (b : ℝ) ^ n = (c : ℝ) ^ n := by
      have hratio := fermat_polar_ratio (n := n) ha hb hc
      rw [h] at hratio
      simpa [one_mul] using (div_eq_iff (pow_ne_zero n hc0)).mp hratio
    exact_mod_cast hR

/-- Equal positive real legs solve the degree-`n` equation and carry a positive boost. -/
theorem equal_leg_real_boost_pos {n : ℕ} (hn : 3 ≤ n) :
    let c : ℝ := 2 ^ ((1 : ℝ) / n)
    0 < c ∧ (1 : ℝ) ^ n + (1 : ℝ) ^ n = c ^ n ∧
      0 < Real.log (Real.sqrt 2 / c) := by
  intro c
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hpow : c ^ n = 2 := by
    have hre : c ^ (n : ℝ) = (2 : ℝ) := by
      dsimp [c]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have : (1 : ℝ) / n * n = 1 := by field_simp
      rw [this, Real.rpow_one]
    have hnat : c ^ (n : ℝ) = c ^ n := by
      rw [← Real.rpow_natCast]
    rw [← hnat, hre]
  refine ⟨hc, ?_, ?_⟩
  · simp [hpow, one_pow]
    norm_num
  · have hsqrt : Real.sqrt 2 = 2 ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
    have harg : Real.sqrt 2 / c = 2 ^ ((1 : ℝ) / 2 - 1 / n) := by
      rw [hsqrt]
      dsimp [c]
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    have hposexp : 0 < (1 : ℝ) / 2 - 1 / n := by
      have hlt : (1 : ℝ) / n < 1 / 2 := by
        refine (div_lt_div_iff₀ hn0 (by norm_num)).mpr ?_
        norm_num
        exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 2 < 3) hn)
      linarith
    rw [harg, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    exact mul_pos hposexp (Real.log_pos (by norm_num))

/-! ### Integral constraints -/

private theorem nat_pow_add_one_lt_succ_pow {k n : ℕ} (hk : 0 < k) (hn : 3 ≤ n) :
    k ^ n + 1 < (k + 1) ^ n := by
  by_cases hk1 : k = 1
  · subst hk1
    have h8 : 8 ≤ 2 ^ n := by
      simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn : 2 ^ 3 ≤ 2 ^ n)
    rw [show (1 + 1) ^ n = 2 ^ n by rfl, one_pow]
    omega
  · have hk2 : 2 ≤ k := by omega
    have hn' : (n - 1) + 1 = n := by omega
    have hstep : k ^ (n - 1) * (k + 1) ≤ (k + 1) ^ n := by
      have hpow : (k + 1) ^ ((n - 1) + 1) = (k + 1) ^ (n - 1) * (k + 1) :=
        Nat.pow_succ _ _
      rw [hn'] at hpow
      rw [hpow]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ k) (n - 1))
    have hexp : k ^ (n - 1) * (k + 1) = k ^ n + k ^ (n - 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      have : k ^ (n - 1) * k = k ^ n := by
        have hmul : k ^ (n - 1) * k = k ^ (n - 1).succ := (Nat.pow_succ k (n - 1)).symm
        have hsucc : (n - 1).succ = n := by rw [Nat.succ_eq_add_one, hn']
        rw [hmul, hsucc]
      rw [this]
    have hge : 2 ≤ k ^ (n - 1) := by
      calc 2
          = 2 ^ 1 := by simp
        _ ≤ 2 ^ (n - 1) :=
            Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ n - 1)
        _ ≤ k ^ (n - 1) := Nat.pow_le_pow_left hk2 (n - 1)
    have : k ^ n + 1 < k ^ n + k ^ (n - 1) := by omega
    exact this.trans_le (by rwa [hexp] at hstep)

/-- If one positive base divides the other, degree `n ≥ 3` has no solution in `ℕ`. -/
theorem not_nat_pow_add_pow_eq_pow_of_dvd {a b c n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hdvd : a ∣ b) :
    a ^ n + b ^ n ≠ c ^ n := by
  intro hsol
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 < k := by
    have : 0 < a * k := by simpa [hk] using hb
    exact Nat.pos_of_mul_pos_left this
  have hmul : a ^ n * (1 + k ^ n) = c ^ n := by
    have hfac : a ^ n + (a * k) ^ n = a ^ n * (1 + k ^ n) := by
      rw [mul_pow]
      ring
    rw [hk, hfac] at hsol
    exact hsol
  let d := Nat.gcd a c
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨a1, ha1⟩ := Nat.gcd_dvd_left a c
  obtain ⟨c1, hc1⟩ := Nat.gcd_dvd_right a c
  have ha1_eq : a = d * a1 := ha1
  have hc1_eq : c = d * c1 := hc1
  have hcancel : a1 ^ n * (1 + k ^ n) = c1 ^ n := by
    have hsub : (d * a1) ^ n * (1 + k ^ n) = (d * c1) ^ n := by
      simpa [ha1_eq, hc1_eq] using hmul
    rw [mul_pow, mul_pow, mul_assoc] at hsub
    exact Nat.mul_left_cancel (pow_pos hd_pos n) hsub
  have hcop : Nat.Coprime a1 c1 := by
    have hgcd : Nat.gcd a1 c1 = 1 :=
      Nat.mul_left_cancel hd_pos <| by
        calc d * Nat.gcd a1 c1
            = Nat.gcd (d * a1) (d * c1) := (Nat.gcd_mul_left d a1 c1).symm
          _ = Nat.gcd a c := by rw [← ha1_eq, ← hc1_eq]
          _ = d := rfl
          _ = d * 1 := (mul_one d).symm
    exact hgcd
  have ha1_one : a1 = 1 := by
    have hcopn : Nat.Coprime (a1 ^ n) (c1 ^ n) := hcop.pow n n
    have hdvd_pow : a1 ^ n ∣ c1 ^ n := ⟨1 + k ^ n, hcancel.symm⟩
    have hdvd_one : a1 ^ n ∣ 1 := by
      rw [← hcopn.gcd_eq_one]
      exact Nat.dvd_gcd (dvd_refl _) hdvd_pow
    have hone : a1 ^ n = 1 := Nat.eq_one_of_dvd_one hdvd_one
    have ha1_ne : a1 ≠ 0 := by
      intro h0
      simp [h0, zero_pow (by omega : n ≠ 0)] at hone
    have ha1_le : a1 ≤ 1 := by
      by_contra hgt
      have h2 : 2 ≤ a1 := by omega
      have : 8 ≤ a1 ^ n := by
        calc 8
            = 2 ^ 3 := by decide
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
          _ ≤ a1 ^ n := Nat.pow_le_pow_left h2 n
      omega
    omega
  have hunit : 1 + k ^ n = c1 ^ n := by simpa [ha1_one, one_pow] using hcancel
  have hk_lt : k < c1 := by
    have : k ^ n < c1 ^ n := by
      rw [← hunit]
      exact Nat.lt_add_of_pos_left (by decide : 0 < 1)
    exact lt_of_pow_lt_pow_left₀ n (Nat.zero_le _) this
  have hsmall : (k + 1) ^ n ≤ k ^ n + 1 := by
    calc (k + 1) ^ n
        ≤ c1 ^ n := Nat.pow_le_pow_left (Nat.succ_le_of_lt hk_lt) n
      _ = k ^ n + 1 := by rw [← hunit, Nat.add_comm]
  exact absurd hsmall (not_le_of_gt (nat_pow_add_one_lt_succ_pow hk0 hn))

/-- On a positive integer solution of degree `n ≥ 3`, `c² < a² + b²`. -/
theorem fermat_sq_excess_pos {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    c ^ 2 < a ^ 2 + b ^ 2 := by
  have hα := fermatBoost_pos_of_sol hn ha hb hc hsol
  have hcmp :=
    (fermatBoost_pos_iff (ne_of_gt hc) (Or.inl (ne_of_gt ha))).mp hα
  rw [fermatL2_of_pos ha hb, natAbs_coe_eq_coe_of_pos hc] at hcmp
  have hc0 : (0 : ℝ) ≤ c := by exact_mod_cast hc.le
  have hsq : (c : ℝ) ^ 2 < (a : ℝ) ^ 2 + (b : ℝ) ^ 2 :=
    (Real.lt_sqrt hc0).mp hcmp
  exact_mod_cast hsq

/-- For positive bases the boost is the half-logarithm of the normalised excess. -/
theorem fermatBoost_eq_half_log_excess {a b c : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    fermatBoost a b c (ne_of_gt hc) =
      Real.log (1 + ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 2) / 2 := by
  have hL := fermatL2_of_pos ha hb
  have hS : 0 < (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by positivity
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hα : fermatBoost a b c (ne_of_gt hc) =
      Real.log (Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / c) := by
    unfold fermatBoost
    rw [hL, natAbs_coe_eq_coe_of_pos hc]
  rw [hα, Real.log_div (Real.sqrt_pos.mpr hS).ne' hc0.ne', Real.log_sqrt hS.le]
  have hlogsq : Real.log ((c : ℝ) ^ 2) = 2 * Real.log (c : ℝ) := by
    rw [Real.log_pow, Nat.cast_ofNat]
  have hdiv : Real.log ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) - Real.log ((c : ℝ) ^ 2) =
      Real.log (((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (c : ℝ) ^ 2) := by
    rw [Real.log_div hS.ne' (pow_ne_zero 2 hc0.ne')]
  have harg : ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (c : ℝ) ^ 2 =
      1 + ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 2 := by
    have hden : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
    calc ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (c : ℝ) ^ 2
        = ((c : ℝ) ^ 2 + ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2)) / (c : ℝ) ^ 2 := by
          congr 1
          ring
      _ = (c : ℝ) ^ 2 / (c : ℝ) ^ 2 +
          ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 2 := by
          rw [add_div]
      _ = 1 + ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 2 := by
          rw [div_self hden]
  calc Real.log ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / 2 - Real.log (c : ℝ)
      = Real.log ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / 2 - Real.log ((c : ℝ) ^ 2) / 2 := by
        rw [hlogsq]; ring
    _ = (Real.log ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) - Real.log ((c : ℝ) ^ 2)) / 2 := by ring
    _ = Real.log (((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (c : ℝ) ^ 2) / 2 := by rw [hdiv]
    _ = Real.log (1 + ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 2) / 2 := by
        rw [harg]

/-- On a positive integer solution the boost is at least `½ log(1 + 1/c²)`. -/
theorem fermatBoost_ge_half_log_one_over_sq {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    Real.log (1 + 1 / (c : ℝ) ^ 2) / 2 ≤ fermatBoost a b c (ne_of_gt hc) := by
  have hlt := fermat_sq_excess_pos hn ha hb hc hsol
  have hEint : (1 : ℤ) ≤ a ^ 2 + b ^ 2 - c ^ 2 := by omega
  have hE : (1 : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2 := by
    exact_mod_cast hEint
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hfrac :
      1 / (c : ℝ) ^ 2 ≤
        ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hE (sq_nonneg _)
  have hpos : 0 < 1 + 1 / (c : ℝ) ^ 2 := by positivity
  have hle : 1 + 1 / (c : ℝ) ^ 2 ≤
      1 + ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 2 := by
    simpa using add_le_add_left hfrac 1
  have hlog := Real.log_le_log hpos hle
  rw [fermatBoost_eq_half_log_excess ha hb hc]
  exact div_le_div_of_nonneg_right hlog (by norm_num : (0 : ℝ) ≤ 2)

theorem not_fermat_pos_of_dvd_leg {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (_hc : 0 < c)
    (hdvd : a ∣ b) :
    a ^ n + b ^ n ≠ c ^ n := by
  intro hsol
  have haN : 0 < a.natAbs := Int.natAbs_pos.mpr ha.ne'
  have hbN : 0 < b.natAbs := Int.natAbs_pos.mpr hb.ne'
  have ha' : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha.le
  have hb' : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb.le
  have hc' : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg (le_of_lt _hc)
  have hdvdN : a.natAbs ∣ b.natAbs := by
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : 0 ≤ k := by nlinarith [ha, hb, hk]
    refine ⟨k.natAbs, ?_⟩
    exact Nat.cast_injective <| by
      calc (b.natAbs : ℤ)
          = b := hb'
        _ = a * k := hk
        _ = (a.natAbs : ℤ) * (k.natAbs : ℤ) := by rw [ha', Int.natAbs_of_nonneg hk0]
        _ = (a.natAbs * k.natAbs : ℕ) := by norm_cast
  have hsolN : a.natAbs ^ n + b.natAbs ^ n = c.natAbs ^ n := by
    have : (a.natAbs : ℤ) ^ n + (b.natAbs : ℤ) ^ n = (c.natAbs : ℤ) ^ n := by
      rw [ha', hb', hc', hsol]
    exact_mod_cast this
  exact not_nat_pow_add_pow_eq_pow_of_dvd hn haN hbN hdvdN hsolN

/--
Odd prime exponent, coprime positive bases, exponent dividing none of the three
bases: `a + b = m^n`, `(a^n + b^n)/(a + b) = t^n`, and `c = m * t`, with
`m` and `t` coprime and `m > 1`.
-/
theorem fermat_odd_prime_leg_sum_pow {a b c n : ℕ}
    (hp : Nat.Prime n) (hodd : Odd n)
    (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b)
    (hnd : ¬ n ∣ a * b * c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    ∃ m t : ℕ, 1 < m ∧ 0 < t ∧ Nat.Coprime m t ∧
      a + b = m ^ n ∧ (a ^ n + b ^ n) / (a + b) = t ^ n ∧ c = m * t := by
  have hdiv : a + b ∣ a ^ n + b ^ n := hodd.nat_add_dvd_pow_add_pow a b
  obtain ⟨q, hq⟩ := hdiv
  have hq_sol : (a + b) * q = c ^ n := by rw [← hq, hsol]
  have hab0 : 0 < a + b := Nat.add_pos_left ha b
  have hgcd : Nat.gcd (a + b) q = 1 := by
    by_contra hne
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hp_ab : p ∣ a + b := Nat.dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    have hp_q : p ∣ q := Nat.dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    have hgeom := geom_sum₂_mul (a : ℤ) (-(b : ℤ)) n
    have hneg : (-(b : ℤ)) ^ n = -((b : ℤ) ^ n) := Odd.neg_pow hodd _
    have hfactor :
        (∑ i ∈ Finset.range n, (a : ℤ) ^ i * (-(b : ℤ)) ^ (n - 1 - i)) * ((a : ℤ) + b) =
          (a : ℤ) ^ n + (b : ℤ) ^ n := by
      have hsub : (a : ℤ) - (-(b : ℤ)) = (a : ℤ) + b := by ring
      have hrhs : (a : ℤ) ^ n - (-(b : ℤ)) ^ n = (a : ℤ) ^ n + (b : ℤ) ^ n := by
        rw [hneg]; ring
      rw [← hsub, ← hrhs]
      simpa [mul_comm] using hgeom
    have hsum_eq :
        (∑ i ∈ Finset.range n, (a : ℤ) ^ i * (-(b : ℤ)) ^ (n - 1 - i)) = q := by
      have hmulZ :
          (∑ i ∈ Finset.range n, (a : ℤ) ^ i * (-(b : ℤ)) ^ (n - 1 - i)) *
            ((a + b : ℕ) : ℤ) = ((a + b : ℕ) : ℤ) * q := by
        calc
          (∑ i ∈ Finset.range n, (a : ℤ) ^ i * (-(b : ℤ)) ^ (n - 1 - i)) *
              ((a + b : ℕ) : ℤ)
              = (a : ℤ) ^ n + (b : ℤ) ^ n := by simpa using hfactor
          _ = ((a + b : ℕ) : ℤ) * q := by exact_mod_cast hq
      have hneZ : ((a + b : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hab0.ne'
      have hmulZ' :
          (∑ i ∈ Finset.range n, (a : ℤ) ^ i * (-(b : ℤ)) ^ (n - 1 - i)) * ((a + b : ℕ) : ℤ) =
            (q : ℤ) * ((a + b : ℕ) : ℤ) := by
        rw [hmulZ, mul_comm]
      exact mul_right_cancel₀ hneZ hmulZ'
    have hcong : (q : ZMod p) = (n : ZMod p) * (a : ZMod p) ^ (n - 1) := by
      have hbZ : (b : ZMod p) = - (a : ZMod p) := by
        have hsum0 : ((a + b : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff (a + b) p).mpr hp_ab
        have : (a : ZMod p) + (b : ZMod p) = 0 := by simpa using hsum0
        exact eq_neg_of_add_eq_zero_right (by simpa [add_comm] using this)
      have hcoe : (q : ZMod p) =
          ∑ i ∈ Finset.range n,
            (((a : ℤ) ^ i * (-(b : ℤ)) ^ (n - 1 - i) : ℤ) : ZMod p) := by
        have hcast := congrArg (fun z : ℤ => (z : ZMod p)) hsum_eq.symm
        simpa [Int.cast_sum, Int.cast_mul, Int.cast_pow] using hcast
      refine hcoe.trans ?_
      refine Eq.trans (Finset.sum_congr rfl ?_) (geom_sum₂_self (a : ZMod p) n)
      intro i _
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_natCast]
      have hnegb : -(b : ZMod p) = (a : ZMod p) := by rw [hbZ, neg_neg]
      rw [hnegb]
    have hp_na : p ∣ n * a ^ (n - 1) :=
      (ZMod.natCast_eq_zero_iff (n * a ^ (n - 1)) p).mp <| by
        have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).mpr hp_q
        rw [Nat.cast_mul, Nat.cast_pow, ← hcong, hq0]
    have hp_n : p ∣ n := by
      rcases hpprime.dvd_mul.mp hp_na with hp_n | hp_pow
      · exact hp_n
      · have hpa : p ∣ a := hpprime.dvd_of_dvd_pow hp_pow
        have hpb : p ∣ b := by
          rcases hp_ab with ⟨u, hu⟩
          rcases hpa with ⟨v, hv⟩
          have hvu : v ≤ u := by
            have hle : p * v ≤ p * u := by
              rw [← hv, ← hu]
              exact Nat.le_add_right a b
            exact Nat.le_of_mul_le_mul_left hle hpprime.pos
          refine ⟨u - v, ?_⟩
          calc b
              = a + b - a := by omega
            _ = p * u - p * v := by rw [hu, hv]
            _ = p * (u - v) := (Nat.mul_sub p u v).symm
        have hpg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
        rw [hcop.gcd_eq_one] at hpg
        exact absurd hpg hpprime.not_dvd_one
    have hp_eq : p = n := (Nat.prime_dvd_prime_iff_eq hpprime hp).mp hp_n
    have hn_ab : n ∣ a + b := by simpa [hp_eq] using hp_ab
    have hn_c : n ∣ c := hp.dvd_of_dvd_pow <| by
      have : n ∣ c ^ n := by
        rw [← hq_sol]
        exact dvd_mul_of_dvd_left hn_ab q
      simpa [hp_eq] using this
    exact hnd (dvd_mul_of_dvd_right hn_c (a * b))
  have hunit_ab : IsUnit (Nat.gcd (a + b) q) := by
    rw [hgcd]
    exact isUnit_one
  obtain ⟨m, hm⟩ := exists_eq_pow_of_mul_eq_pow hunit_ab hq_sol
  have hcomm : q * (a + b) = c ^ n := by rw [mul_comm, hq_sol]
  have hunit_q : IsUnit (Nat.gcd q (a + b)) := by
    rw [Nat.gcd_comm, hgcd]
    exact isUnit_one
  obtain ⟨t, ht⟩ := exists_eq_pow_of_mul_eq_pow hunit_q hcomm
  have hm_pow : a + b = m ^ n := hm
  have ht_pow : q = t ^ n := ht
  have hc_pow : c ^ n = (m * t) ^ n := by
    rw [← hq_sol, hm_pow, ht_pow, mul_pow]
  have hn0 : 0 < n := hp.pos
  have hc_eq : c = m * t := Nat.pow_left_injective hn0.ne' hc_pow
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_eq : m = 0 := Nat.eq_zero_of_not_pos hm0
    have : a + b = 0 := by simpa [hm_eq, zero_pow hn0.ne'] using hm_pow
    omega
  have ht_pos : 0 < t := by
    have hq_pos : 0 < q := by
      have hc_pos : 0 < c := by
        apply Nat.pos_of_ne_zero
        intro hc0
        have hzero : a ^ n + b ^ n = 0 := by simpa [hc0, zero_pow hn0.ne'] using hsol
        have : a ^ n = 0 := by omega
        exact (pow_pos ha n).ne' this
      have : 0 < (a + b) * q := by rw [hq_sol]; exact pow_pos hc_pos n
      exact Nat.pos_of_mul_pos_left this
    by_contra ht0
    have ht_eq : t = 0 := Nat.eq_zero_of_not_pos ht0
    have : q = 0 := by simpa [ht_eq, zero_pow hn0.ne'] using ht_pow
    omega
  have hm_gt : 1 < m := by
    have hm1 : m ≠ 1 := by
      intro hm1
      have : a + b = 1 := by simpa [hm1, one_pow] using hm_pow
      omega
    omega
  have hcopmt : Nat.Coprime m t := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpm : p ∣ m := Nat.dvd_trans hpdvd (Nat.gcd_dvd_left m t)
    have hpt : p ∣ t := Nat.dvd_trans hpdvd (Nat.gcd_dvd_right m t)
    have hp_ab : p ∣ a + b := by
      rw [hm_pow]
      exact dvd_pow hpm hn0.ne'
    have hp_q : p ∣ q := by
      rw [ht_pow]
      exact dvd_pow hpt hn0.ne'
    have hpg : p ∣ Nat.gcd (a + b) q := Nat.dvd_gcd hp_ab hp_q
    rw [hgcd] at hpg
    exact hpprime.not_dvd_one hpg
  refine ⟨m, t, hm_gt, ht_pos, hcopmt, hm_pow, ?_, hc_eq⟩
  · have hdivq : a ^ n + b ^ n = q * (a + b) := by
      simpa [Nat.mul_comm] using hq
    rw [Nat.div_eq_of_eq_mul_left hab0 hdivq, ht_pow]

private theorem fermat_gcd_sum_sub {a b c n : ℕ}
    (_hn : n ≠ 0) (hodd : Odd n) (hcop : Nat.Coprime a b)
    (hsol : a ^ n + b ^ n = c ^ n) (hbc : b < c) :
    Nat.gcd (a + b) (c - b) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hp_ab : p ∣ a + b := Nat.dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hp_cb : p ∣ c - b := Nat.dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have hdiff0 : ((c - b : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (c - b) p).mpr hp_cb
  have hsum0 : ((a + b : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (a + b) p).mpr hp_ab
  have hb_eq : (b : ZMod p) = (c : ZMod p) := by
    have hsub : ((c - b : ℕ) : ZMod p) = (c : ZMod p) - (b : ZMod p) :=
      Nat.cast_sub hbc.le
    have h0 : (c : ZMod p) - (b : ZMod p) = 0 := by simpa [hsub] using hdiff0
    exact (sub_eq_zero.mp h0).symm
  have ha_eq : (a : ZMod p) = - (b : ZMod p) := by
    have : (a : ZMod p) + (b : ZMod p) = 0 := by simpa using hsum0
    exact eq_neg_of_add_eq_zero_left this
  have hsolZ : (a : ZMod p) ^ n + (b : ZMod p) ^ n = (c : ZMod p) ^ n := by
    simpa [Nat.cast_add, Nat.cast_pow] using congrArg (fun k : ℕ => (k : ZMod p)) hsol
  have hx : (- (b : ZMod p)) ^ n + (b : ZMod p) ^ n = (b : ZMod p) ^ n := by
    simpa [ha_eq, hb_eq] using hsolZ
  rw [Odd.neg_pow hodd (b : ZMod p)] at hx
  have hb0 : (b : ZMod p) ^ n = 0 := by
    have hx0 : (0 : ZMod p) = (b : ZMod p) ^ n := by simpa using hx
    exact hx0.symm
  have hpb : p ∣ b := by
    have hpow0 : ((b ^ n : ℕ) : ZMod p) = 0 := by simpa [Nat.cast_pow] using hb0
    exact hp.dvd_of_dvd_pow ((ZMod.natCast_eq_zero_iff (b ^ n) p).mp hpow0)
  have hpa : p ∣ a := by
    have ha0 : (a : ZMod p) ^ n = 0 := by
      rw [ha_eq, Odd.neg_pow hodd, hb0, neg_zero]
    have hpow0 : ((a ^ n : ℕ) : ZMod p) = 0 := by simpa [Nat.cast_pow] using ha0
    exact hp.dvd_of_dvd_pow ((ZMod.natCast_eq_zero_iff (a ^ n) p).mp hpow0)
  have hpg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
  rw [hcop.gcd_eq_one] at hpg
  exact hp.not_dvd_one hpg

private theorem fermat_gcd_two_diffs {a b c n : ℕ}
    (_hn : n ≠ 0) (hcop : Nat.Coprime a b)
    (hsol : a ^ n + b ^ n = c ^ n) (hac : a < c) (hbc : b < c) :
    Nat.gcd (c - a) (c - b) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hp_ca : p ∣ c - a := Nat.dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hp_cb : p ∣ c - b := Nat.dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have ha_eq : (a : ZMod p) = (c : ZMod p) := by
    have hzero : ((c - a : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (c - a) p).mpr hp_ca
    have hsub : ((c - a : ℕ) : ZMod p) = (c : ZMod p) - (a : ZMod p) :=
      Nat.cast_sub hac.le
    have h0 : (c : ZMod p) - (a : ZMod p) = 0 := by simpa [hsub] using hzero
    exact (sub_eq_zero.mp h0).symm
  have hb_eq : (b : ZMod p) = (c : ZMod p) := by
    have hzero : ((c - b : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (c - b) p).mpr hp_cb
    have hsub : ((c - b : ℕ) : ZMod p) = (c : ZMod p) - (b : ZMod p) :=
      Nat.cast_sub hbc.le
    have h0 : (c : ZMod p) - (b : ZMod p) = 0 := by simpa [hsub] using hzero
    exact (sub_eq_zero.mp h0).symm
  have hsolZ : (a : ZMod p) ^ n + (b : ZMod p) ^ n = (c : ZMod p) ^ n := by
    simpa [Nat.cast_add, Nat.cast_pow] using congrArg (fun k : ℕ => (k : ZMod p)) hsol
  have hx : (a : ZMod p) ^ n + (a : ZMod p) ^ n = (a : ZMod p) ^ n := by
    simpa [ha_eq, hb_eq] using hsolZ
  have ha0 : (a : ZMod p) ^ n = 0 :=
    add_left_cancel <| by
      calc (a : ZMod p) ^ n + (a : ZMod p) ^ n
          = (a : ZMod p) ^ n := hx
        _ = (a : ZMod p) ^ n + 0 := (add_zero _).symm
  have hpa : p ∣ a := by
    have hpow0 : ((a ^ n : ℕ) : ZMod p) = 0 := by simpa [Nat.cast_pow] using ha0
    exact hp.dvd_of_dvd_pow ((ZMod.natCast_eq_zero_iff (a ^ n) p).mp hpow0)
  have hpb : p ∣ b := by
    have hb0 : (b : ZMod p) ^ n = 0 := by rw [hb_eq, ← ha_eq, ha0]
    have hpow0 : ((b ^ n : ℕ) : ZMod p) = 0 := by simpa [Nat.cast_pow] using hb0
    exact hp.dvd_of_dvd_pow ((ZMod.natCast_eq_zero_iff (b ^ n) p).mp hpow0)
  have hpg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
  rw [hcop.gcd_eq_one] at hpg
  exact hp.not_dvd_one hpg

private theorem fermat_gcd_diff_quot {a b c n : ℕ}
    (hp : Nat.Prime n) (_ha : 0 < a) (_hb : 0 < b) (hcop : Nat.Coprime a b)
    (hna : ¬ n ∣ a) (hsol : a ^ n + b ^ n = c ^ n) (hbc : b < c) :
    Nat.gcd (c - b) (∑ i ∈ Finset.range n, b ^ i * c ^ (n - 1 - i)) = 1 := by
  set Q := ∑ i ∈ Finset.range n, b ^ i * c ^ (n - 1 - i)
  by_contra hne
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hp_cb : p ∣ c - b := Nat.dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hp_Q : p ∣ Q := Nat.dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have hb_eq : (b : ZMod p) = (c : ZMod p) := by
    have hzero : ((c - b : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (c - b) p).mpr hp_cb
    have hsub : ((c - b : ℕ) : ZMod p) = (c : ZMod p) - (b : ZMod p) :=
      Nat.cast_sub hbc.le
    have h0 : (c : ZMod p) - (b : ZMod p) = 0 := by simpa [hsub] using hzero
    exact (sub_eq_zero.mp h0).symm
  have hQ : (Q : ZMod p) = (n : ZMod p) * (b : ZMod p) ^ (n - 1) := by
    have hcoe : (Q : ZMod p) =
        ∑ i ∈ Finset.range n, (b : ZMod p) ^ i * (c : ZMod p) ^ (n - 1 - i) := by
      simp [Q, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
    rw [hcoe]
    have hsum :
        ∑ i ∈ Finset.range n, (b : ZMod p) ^ i * (c : ZMod p) ^ (n - 1 - i) =
          ∑ i ∈ Finset.range n, (b : ZMod p) ^ i * (b : ZMod p) ^ (n - 1 - i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hb_eq]
    rw [hsum, geom_sum₂_self]
  have hp_nb : p ∣ n * b ^ (n - 1) :=
    (ZMod.natCast_eq_zero_iff (n * b ^ (n - 1)) p).mp <| by
      have hQ0 : (Q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff Q p).mpr hp_Q
      rw [Nat.cast_mul, Nat.cast_pow, ← hQ, hQ0]
  rcases hpprime.dvd_mul.mp hp_nb with hp_n | hp_pow
  · have hp_eq : p = n := (Nat.prime_dvd_prime_iff_eq hpprime hp).mp hp_n
    have hn_cb : n ∣ c - b := by simpa [hp_eq] using hp_cb
    have ha0 : (a : ZMod n) ^ n = 0 := by
      have hsolZ : (a : ZMod n) ^ n + (b : ZMod n) ^ n = (c : ZMod n) ^ n := by
        simpa [Nat.cast_add, Nat.cast_pow] using congrArg (fun k : ℕ => (k : ZMod n)) hsol
      have hb_c : (b : ZMod n) = (c : ZMod n) := by
        have hzero : ((c - b : ℕ) : ZMod n) = 0 :=
          (ZMod.natCast_eq_zero_iff (c - b) n).mpr hn_cb
        have hsub : ((c - b : ℕ) : ZMod n) = (c : ZMod n) - (b : ZMod n) :=
          Nat.cast_sub hbc.le
        have h0 : (c : ZMod n) - (b : ZMod n) = 0 := by simpa [hsub] using hzero
        exact (sub_eq_zero.mp h0).symm
      have hsum : (a : ZMod n) ^ n + (c : ZMod n) ^ n = (c : ZMod n) ^ n := by
        simpa [hb_c] using hsolZ
      exact add_right_cancel <| by
        rw [zero_add]
        exact hsum
    exact hna <| by
      have hpow0 : ((a ^ n : ℕ) : ZMod n) = 0 := by simpa [Nat.cast_pow] using ha0
      exact hp.dvd_of_dvd_pow ((ZMod.natCast_eq_zero_iff (a ^ n) n).mp hpow0)
  · have hpb : p ∣ b := hpprime.dvd_of_dvd_pow hp_pow
    have hpc : p ∣ c := by
      have hc : (c - b) + b = c := Nat.sub_add_cancel hbc.le
      rw [← hc]
      exact dvd_add hp_cb hpb
    have hpan : p ∣ a ^ n := by
      have hcbn : p ∣ c ^ n := dvd_pow hpc hp.ne_zero
      have hpbn : p ∣ b ^ n := dvd_pow hpb hp.ne_zero
      have hsum : p ∣ b ^ n + a ^ n := by
        rw [add_comm, hsol]
        exact hcbn
      exact (Nat.dvd_add_right hpbn).mp hsum
    have hpa : p ∣ a := hpprime.dvd_of_dvd_pow hpan
    have hpg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
    rw [hcop.gcd_eq_one] at hpg
    exact hpprime.not_dvd_one hpg

/--
Odd prime exponent, coprime positive bases, exponent dividing none of them:
`a + b`, `c - a`, and `c - b` are pairwise coprime pure `n`th powers summing
to `2c`, with positive roots. The quotient of the power sum by `a + b` is
a pure `n`th power coprime to that sum. The third base is the product of the
root of `a + b` and the root of that quotient, both greater than one.
-/
theorem fermat_odd_prime_three_powers {a b c n : ℕ}
    (hp : Nat.Prime n) (hodd : Odd n)
    (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b)
    (hnd : ¬ n ∣ a * b * c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    ∃ p q r t : ℕ, 1 < p ∧ 0 < q ∧ 0 < r ∧ 1 < t ∧
      Nat.Coprime p q ∧ Nat.Coprime p r ∧ Nat.Coprime q r ∧ Nat.Coprime p t ∧
      a + b = p ^ n ∧ c - a = q ^ n ∧ c - b = r ^ n ∧
      p ^ n + q ^ n + r ^ n = 2 * c ∧
      (a ^ n + b ^ n) / (a + b) = t ^ n ∧ c = p * t := by
  have hna : ¬ n ∣ a := fun h => hnd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) c)
  have hbc : b < c := by
    have hpow : b ^ n < c ^ n := by
      have : b ^ n < a ^ n + b ^ n := Nat.lt_add_of_pos_left (pow_pos ha n)
      rwa [hsol] at this
    exact lt_of_pow_lt_pow_left₀ n (Nat.zero_le _) hpow
  have hac : a < c := by
    have hpow : a ^ n < c ^ n := by
      have : a ^ n < a ^ n + b ^ n := Nat.lt_add_of_pos_right (pow_pos hb n)
      rwa [hsol] at this
    exact lt_of_pow_lt_pow_left₀ n (Nat.zero_le _) hpow
  obtain ⟨p, t, hpgt, ht0, hcoppt, hp_pow, ht_pow, hc_eq⟩ :=
    fermat_odd_prime_leg_sum_pow hp hodd ha hb hcop hnd hsol
  have ht : 1 < t := by
    have ht_ne : t ≠ 1 := by
      intro ht1
      have hdiv : a + b ∣ a ^ n + b ^ n := hodd.nat_add_dvd_pow_add_pow a b
      have hquot : (a ^ n + b ^ n) / (a + b) = 1 := by simpa [ht1, one_pow] using ht_pow
      have hsum_eq : a ^ n + b ^ n = a + b := by
        rw [← Nat.mul_div_cancel' hdiv, hquot, mul_one]
      by_cases ha1 : a = 1
      · by_cases hb1 : b = 1
        · have hc2 : c ^ n = 2 := by
            have h2 : 1 ^ n + 1 ^ n = c ^ n := by simpa [ha1, hb1] using hsol
            simpa using h2.symm
          have hcpos : 0 < c := Nat.pos_of_ne_zero fun hc0 => by
            simp [hc0, hp.ne_zero, zero_pow] at hc2
          rcases Nat.lt_or_ge c 2 with hc1 | hc2le
          · have : c = 1 := by omega
            simp [this, one_pow] at hc2
          · have h4 : 4 ≤ c ^ n := by
              calc 4
                  = 2 ^ 2 := by decide
                _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hp.two_le
                _ ≤ c ^ n := Nat.pow_le_pow_left hc2le n
            omega
        · have hb2 : 2 ≤ b := by omega
          have hb_pow : b + b ≤ b ^ n := by
            calc b + b
                = 2 * b := by rw [two_mul]
              _ ≤ b * b := Nat.mul_le_mul_right b hb2
              _ = b ^ 2 := by rw [pow_two, mul_comm]
              _ ≤ b ^ n := Nat.pow_le_pow_right hb hp.two_le
          rw [ha1, one_pow] at hsum_eq
          omega
      · have ha2 : 2 ≤ a := by omega
        have ha_pow : a + a ≤ a ^ n := by
          calc a + a
              = 2 * a := by rw [two_mul]
            _ ≤ a * a := Nat.mul_le_mul_right a ha2
            _ = a ^ 2 := by rw [pow_two]
            _ ≤ a ^ n := Nat.pow_le_pow_right ha hp.two_le
        have hb_le : b ≤ b ^ n := by
          calc b
              = b ^ 1 := (pow_one b).symm
            _ ≤ b ^ n := Nat.pow_le_pow_right hb hp.one_le
        omega
    omega
  have hgcd_ab_cb := fermat_gcd_sum_sub hp.ne_zero hodd hcop hsol hbc
  have hgcd_ab_ca : Nat.gcd (a + b) (c - a) = 1 := by
    simpa [Nat.add_comm] using
      fermat_gcd_sum_sub hp.ne_zero hodd hcop.symm (by simpa [Nat.add_comm] using hsol) hac
  have hgcd_diffs := fermat_gcd_two_diffs hp.ne_zero hcop hsol hac hbc
  have hQgcd_b := fermat_gcd_diff_quot hp ha hb hcop hna hsol hbc
  have hQgcd_a :=
    fermat_gcd_diff_quot hp hb ha hcop.symm
      (fun h => hnd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) c))
      (by simpa [add_comm] using hsol) hac
  let Qb := ∑ i ∈ Finset.range n, b ^ i * c ^ (n - 1 - i)
  let Qa := ∑ i ∈ Finset.range n, a ^ i * c ^ (n - 1 - i)
  have hprod_b : (c - b) * Qb = a ^ n := by
    have hgeom := geom_sum₂_mul_of_le hbc.le n
    have hmul : Qb * (c - b) = a ^ n := by
      rw [show Qb * (c - b) =
          (∑ i ∈ Finset.range n, b ^ i * c ^ (n - 1 - i)) * (c - b) from rfl, hgeom]
      exact Nat.sub_eq_of_eq_add hsol.symm
    rwa [Nat.mul_comm] at hmul
  have hunit_b : IsUnit (Nat.gcd (c - b) Qb) := by
    rw [hQgcd_b]
    exact isUnit_one
  obtain ⟨r, hr⟩ := exists_eq_pow_of_mul_eq_pow hunit_b hprod_b
  have hprod_a : (c - a) * Qa = b ^ n := by
    have hgeom := geom_sum₂_mul_of_le hac.le n
    have hmul : Qa * (c - a) = b ^ n := by
      rw [show Qa * (c - a) =
          (∑ i ∈ Finset.range n, a ^ i * c ^ (n - 1 - i)) * (c - a) from rfl, hgeom]
      exact Nat.sub_eq_of_eq_add <| by
        calc c ^ n
            = a ^ n + b ^ n := hsol.symm
          _ = b ^ n + a ^ n := by rw [Nat.add_comm]
    rwa [Nat.mul_comm] at hmul
  have hunit_a : IsUnit (Nat.gcd (c - a) Qa) := by
    rw [hQgcd_a]
    exact isUnit_one
  obtain ⟨q, hq⟩ := exists_eq_pow_of_mul_eq_pow hunit_a hprod_a
  have hq_pos : 0 < q := by
    have hpos : 0 < c - a := Nat.sub_pos_of_lt hac
    have : 0 < q ^ n := by simpa [hq] using hpos
    exact Nat.pos_of_ne_zero fun hq0 => by simp [hq0, hp.ne_zero, zero_pow] at this
  have hr_pos : 0 < r := by
    have hpos : 0 < c - b := Nat.sub_pos_of_lt hbc
    have : 0 < r ^ n := by simpa [hr] using hpos
    exact Nat.pos_of_ne_zero fun hr0 => by simp [hr0, hp.ne_zero, zero_pow] at this
  have hcop_pq : Nat.Coprime p q := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨g, hg, hgdvd⟩ := Nat.exists_prime_and_dvd hne
    have hgp : g ∣ p ^ n := dvd_pow (Nat.dvd_trans hgdvd (Nat.gcd_dvd_left _ _)) hp.ne_zero
    have hgq : g ∣ q ^ n := dvd_pow (Nat.dvd_trans hgdvd (Nat.gcd_dvd_right _ _)) hp.ne_zero
    have hpg : g ∣ Nat.gcd (a + b) (c - a) := by
      rw [hp_pow, hq]
      exact Nat.dvd_gcd hgp hgq
    rw [hgcd_ab_ca] at hpg
    exact hg.not_dvd_one hpg
  have hcop_pr : Nat.Coprime p r := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨g, hg, hgdvd⟩ := Nat.exists_prime_and_dvd hne
    have hgp : g ∣ p ^ n := dvd_pow (Nat.dvd_trans hgdvd (Nat.gcd_dvd_left _ _)) hp.ne_zero
    have hgr : g ∣ r ^ n := dvd_pow (Nat.dvd_trans hgdvd (Nat.gcd_dvd_right _ _)) hp.ne_zero
    have hpg : g ∣ Nat.gcd (a + b) (c - b) := by
      rw [hp_pow, hr]
      exact Nat.dvd_gcd hgp hgr
    rw [hgcd_ab_cb] at hpg
    exact hg.not_dvd_one hpg
  have hcop_qr : Nat.Coprime q r := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨g, hg, hgdvd⟩ := Nat.exists_prime_and_dvd hne
    have hgq : g ∣ q ^ n := dvd_pow (Nat.dvd_trans hgdvd (Nat.gcd_dvd_left _ _)) hp.ne_zero
    have hgr : g ∣ r ^ n := dvd_pow (Nat.dvd_trans hgdvd (Nat.gcd_dvd_right _ _)) hp.ne_zero
    have hpg : g ∣ Nat.gcd (c - a) (c - b) := by
      rw [hq, hr]
      exact Nat.dvd_gcd hgq hgr
    rw [hgcd_diffs] at hpg
    exact hg.not_dvd_one hpg
  have hsum2 : p ^ n + q ^ n + r ^ n = 2 * c := by
    rw [← hp_pow, ← hq, ← hr]
    have hca : a + (c - a) = c := Nat.add_sub_cancel' hac.le
    have hcb : b + (c - b) = c := Nat.add_sub_cancel' hbc.le
    calc a + b + (c - a) + (c - b)
        = a + (c - a) + b + (c - b) := by
          rw [Nat.add_assoc a b (c - a), Nat.add_comm b (c - a),
            ← Nat.add_assoc a (c - a) b]
        _ = (a + (c - a)) + (b + (c - b)) := by
          rw [← Nat.add_assoc (a + (c - a)) b (c - b)]
        _ = c + c := by rw [hca, hcb]
        _ = 2 * c := by rw [two_mul]
  refine ⟨p, q, r, t, hpgt, hq_pos, hr_pos, ht, hcop_pq, hcop_pr, hcop_qr, hcoppt,
    hp_pow, hq, hr, hsum2, ht_pow, hc_eq⟩

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
