import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Invariant
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Faraday bivector in the dual-rotor 6-space

## Paper boundary (do **not** claim)

Maxwell's equations are **not** derived. The identification of the Faraday
bivector with a laboratory electromagnetic field is a working hypothesis.
This module records coefficient-level identities on the same six generators
that carry the dual-rotor torsion.

No theorem asserts a derivation of Maxwell or of the Lorentz force from the
DST action. Helicity drive of \(J\) is not a theorem. Phase-dependent
circular-wave identities live in `CircularPolarization`.

## What is proved

* The Faraday coefficients \((E_a,B_a)\) live in the same 6-generator space
  as \(\Omega_{\mathrm{biv}}\): usual (boost, \(i\Gamma\)) plus dual
  (rotation, \(\Gamma\)). Section 10's single symbol \(F_{\mathrm{dual}}\)
  that mixes \(E\) and \(B\) is the *full* Faraday bivector; Section 12's
  split \(F_{\mathrm{usual}}\leftrightarrow\mathbf{E}\),
  \(F_{\mathrm{dual}}\leftrightarrow\mathbf{B}\) is the compatible
  decomposition.
* Duality \(X\mapsto Xi\) sends \((E,B)\mapsto(B,-E)\).
* On that identification the torsional scalar is the Faraday quadratic
  \(J=\tfrac12(E^2-B^2)\), with unsigned mass \(M=\tfrac12(E^2+B^2)\).
  Null fields \(E^2=B^2\) have \(J=0\); a circular snapshot with
  \(|\sigma|=1\) is null and has \(E\cdot B=0\), yet \(M=E_0^2>0\) if
  \(E_0\neq 0\).
* Hodge duality has period 4 and sends \(J\mapsto -J\), \(E\cdot B\mapsto -E\cdot B\),
  preserving \(M\). The usual--dual parameter swap \((\alpha,\beta)\mapsto(\beta,\alpha)\)
  also sends \(J\mapsto -J\) but has period 2 and is not Hodge. Laboratory
  \(T:(E,B)\mapsto(E,-B)\) preserves \(J\) and is neither map.
* Superposition of Faraday coefficients is componentwise: \(J\) of a sum
  is \(J(p)+J(q)\) plus the interference \(\mathbf{E}_p\cdot\mathbf{E}_q
  -\mathbf{B}_p\cdot\mathbf{B}_q\).
* First-order sandwich increment is the commutator \(\Omega X-X\Omega\).
  On a rest particle a pure electric generator produces a spatial kick
  and every magnetic generator produces none, so the dual Faraday summand
  never kicks a rest frame. On a \(y\)-velocity a pure \(B_x\) generator
  produces a \(z\)-kick; the paper wedge vanishes on that moving case.
  The outer product \(F\wedge X\) is therefore not the Lorentz increment.
* On the Minkowski vector \(X=e_0+v\) the same commutator of the Faraday
  bivector is the 4-vector \((E\cdot v)\,e_0+(E-v\times B)\). That is the
  Lorentz 4-force of the laboratory time-reversed field \((E,-B)\); the
  coefficient 3-force \(q(E+v\times B)\) differs by the sign of \(B\).
  Maxwell is not derived; this is kinematics of the written sandwich.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations Motor RelativeRotor Invariant

/-! ### Faraday coefficients in the torsion 6-space -/

@[ext]
structure FaradayParams where
  E : Fin 3 → ℝ
  B : Fin 3 → ℝ

instance : Add FaradayParams where
  add p q := ⟨fun a => p.E a + q.E a, fun a => p.B a + q.B a⟩

@[simp] theorem add_E (p q : FaradayParams) (a : Fin 3) :
    (p + q).E a = p.E a + q.E a :=
  rfl

@[simp] theorem add_B (p q : FaradayParams) (a : Fin 3) :
    (p + q).B a = p.B a + q.B a :=
  rfl

/-- Section 12 split: \(E\) on boost generators, \(B\) on rotation generators. -/
def toTorsion (p : FaradayParams) : TorsionParams where
  alpha := p.E
  beta := p.B

noncomputable def faradayUsual (p : FaradayParams) : PGA :=
  omegaUsual (toTorsion p)

noncomputable def faradayDual (p : FaradayParams) : PGA :=
  omegaDual (toTorsion p)

/-- Full Faraday bivector (Section 10's written \(F_{\mathrm{dual}}\)). -/
noncomputable def faraday (p : FaradayParams) : PGA :=
  omegaTorsion (toTorsion p)

theorem faraday_eq_add (p : FaradayParams) :
    faraday p = faradayUsual p + faradayDual p :=
  omegaTorsion_eq_add (toTorsion p)

/-- Section 10 and Section 12 name the same 6-space. -/
theorem paper_sec10_Fdual_is_full_faraday (p : FaradayParams) :
    faraday p = faradayUsual p + faradayDual p :=
  faraday_eq_add p

/-! ### Dual map: \((E,B)\mapsto(B,-E)\) -/

def dualFaradayParams (p : FaradayParams) : FaradayParams where
  E := p.B
  B := fun a => -p.E a

private theorem dual_smul (c : ℝ) (x : PGA) : dual (c • x) = c • dual x := by
  simp [dual]

private theorem dual_add (x y : PGA) : dual (x + y) = dual x + dual y := by
  simp [dual, add_mul]

private theorem dual_sum (f : Fin 3 → PGA) :
    dual (∑ a : Fin 3, f a) = ∑ a : Fin 3, dual (f a) := by
  simp [dual, Finset.sum_mul]

private theorem dual_faraday_term (p : FaradayParams) (a : Fin 3) :
    dual ((p.E a / 2) • hyperbolic a + (p.B a / 2) • cyclic a) =
      (p.B a / 2) • hyperbolic a + (-p.E a / 2) • cyclic a := by
  calc dual ((p.E a / 2) • hyperbolic a + (p.B a / 2) • cyclic a)
      = (p.E a / 2) • dual (hyperbolic a) + (p.B a / 2) • dual (cyclic a) := by
        rw [dual_add, dual_smul, dual_smul]
    _ = (p.E a / 2) • (-cyclic a) + (p.B a / 2) • hyperbolic a := by
        rw [dual_hyperbolic, dual_cyclic]
    _ = -((p.E a / 2) • cyclic a) + (p.B a / 2) • hyperbolic a := by
        rw [smul_neg]
    _ = (-(p.E a / 2)) • cyclic a + (p.B a / 2) • hyperbolic a := by
        rw [neg_smul]
    _ = (p.B a / 2) • hyperbolic a + (-p.E a / 2) • cyclic a := by
        rw [neg_div, add_comm]

theorem dual_faraday (p : FaradayParams) :
    dual (faraday p) = faraday (dualFaradayParams p) := by
  unfold faraday toTorsion dualFaradayParams omegaTorsion
  rw [dual_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simpa using dual_faraday_term p a

/-! ### Quadratic invariants \(J\), \(M\), and \(E\cdot B\) -/

def energySq (p : FaradayParams) : ℝ :=
  ∑ a : Fin 3, p.E a ^ 2

def magneticSq (p : FaradayParams) : ℝ :=
  ∑ a : Fin 3, p.B a ^ 2

def faradayDot (p : FaradayParams) : ℝ :=
  ∑ a : Fin 3, p.E a * p.B a

theorem energySq_nonneg (p : FaradayParams) : 0 ≤ energySq p :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem J_faraday (p : FaradayParams) :
    J (toTorsion p) = (1 / 2) * (energySq p - magneticSq p) := by
  rw [J_coef]
  simp only [toTorsion, energySq, magneticSq, Finset.sum_sub_distrib]

theorem mass_faraday (p : FaradayParams) :
    mass (toTorsion p) = (1 / 2) * (energySq p + magneticSq p) := by
  rw [mass_coef]
  simp only [toTorsion, energySq, magneticSq, Finset.sum_add_distrib]

theorem J_eq_zero_of_energy_eq_magnetic {p : FaradayParams}
    (h : energySq p = magneticSq p) :
    J (toTorsion p) = 0 := by
  rw [J_faraday, h, sub_self, mul_zero]

theorem mass_eq_energySq_of_null {p : FaradayParams}
    (h : energySq p = magneticSq p) :
    mass (toTorsion p) = energySq p := by
  rw [mass_faraday, h]
  ring

theorem mass_pos_of_null {p : FaradayParams}
    (h : energySq p = magneticSq p) (hE : energySq p ≠ 0) :
    0 < mass (toTorsion p) :=
  (mass_eq_energySq_of_null h).symm ▸ lt_of_le_of_ne (energySq_nonneg p) hE.symm

/-- Interference of two Faraday configurations:
\(\mathbf{E}_p\cdot\mathbf{E}_q-\mathbf{B}_p\cdot\mathbf{B}_q\). -/
def faradayCross (p q : FaradayParams) : ℝ :=
  (∑ a : Fin 3, p.E a * q.E a) - (∑ a : Fin 3, p.B a * q.B a)

theorem energySq_add (p q : FaradayParams) :
    energySq (p + q) =
      energySq p + energySq q + 2 * ∑ a : Fin 3, p.E a * q.E a := by
  unfold energySq
  simp only [add_E, Fin.sum_univ_three]
  ring

theorem magneticSq_add (p q : FaradayParams) :
    magneticSq (p + q) =
      magneticSq p + magneticSq q + 2 * ∑ a : Fin 3, p.B a * q.B a := by
  unfold magneticSq
  simp only [add_B, Fin.sum_univ_three]
  ring

theorem J_add (p q : FaradayParams) :
    J (toTorsion (p + q)) =
      J (toTorsion p) + J (toTorsion q) + faradayCross p q := by
  rw [J_faraday, J_faraday, J_faraday, energySq_add, magneticSq_add]
  unfold faradayCross
  simp only [Fin.sum_univ_three]
  ring

/-! ### Hodge dual, usual--dual swap, and laboratory \(T\) -/

/-- Sign flip of both coefficient 3-vectors. -/
def negFaradayParams (p : FaradayParams) : FaradayParams where
  E := fun a => -p.E a
  B := fun a => -p.B a

/-- Usual--dual parameter swap \((\alpha,\beta)\mapsto(\beta,\alpha)\). Period 2. -/
def swapFaradayParams (p : FaradayParams) : FaradayParams where
  E := p.B
  B := p.E

/-- Laboratory time reversal \((E,B)\mapsto(E,-B)\). Period 2. -/
def timeReverseFaradayParams (p : FaradayParams) : FaradayParams where
  E := p.E
  B := fun a => -p.B a

theorem toTorsion_swap (p : FaradayParams) :
    toTorsion (swapFaradayParams p) = daggerParams (toTorsion p) :=
  rfl

theorem energySq_dual (p : FaradayParams) :
    energySq (dualFaradayParams p) = magneticSq p :=
  rfl

theorem magneticSq_dual (p : FaradayParams) :
    magneticSq (dualFaradayParams p) = energySq p := by
  simp [magneticSq, energySq, dualFaradayParams]

theorem energySq_timeReverse (p : FaradayParams) :
    energySq (timeReverseFaradayParams p) = energySq p :=
  rfl

theorem magneticSq_timeReverse (p : FaradayParams) :
    magneticSq (timeReverseFaradayParams p) = magneticSq p := by
  simp [magneticSq, timeReverseFaradayParams]

theorem dualFaradayParams_sq (p : FaradayParams) :
    dualFaradayParams (dualFaradayParams p) = negFaradayParams p := by
  ext a <;> simp [dualFaradayParams, negFaradayParams]

theorem negFaradayParams_sq (p : FaradayParams) :
    negFaradayParams (negFaradayParams p) = p := by
  ext a <;> simp [negFaradayParams]

theorem dualFaradayParams_four (p : FaradayParams) :
    dualFaradayParams
        (dualFaradayParams (dualFaradayParams (dualFaradayParams p))) = p := by
  rw [dualFaradayParams_sq, dualFaradayParams_sq, negFaradayParams_sq]

theorem swapFaradayParams_sq (p : FaradayParams) :
    swapFaradayParams (swapFaradayParams p) = p := by
  ext a <;> rfl

theorem timeReverseFaradayParams_sq (p : FaradayParams) :
    timeReverseFaradayParams (timeReverseFaradayParams p) = p := by
  ext a <;> simp [timeReverseFaradayParams]

theorem faraday_neg (p : FaradayParams) :
    faraday (negFaradayParams p) = -faraday p := by
  unfold faraday toTorsion negFaradayParams omegaTorsion
  simp only [neg_div]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext a
  simp [neg_add_rev, add_comm]

theorem dual_dual_faraday (p : FaradayParams) :
    dual (dual (faraday p)) = -faraday p := by
  rw [dual_faraday, dual_faraday, dualFaradayParams_sq, faraday_neg]

theorem J_dualFaraday (p : FaradayParams) :
    J (toTorsion (dualFaradayParams p)) = -J (toTorsion p) := by
  rw [J_faraday, J_faraday, energySq_dual, magneticSq_dual]
  ring

theorem mass_dualFaraday (p : FaradayParams) :
    mass (toTorsion (dualFaradayParams p)) = mass (toTorsion p) := by
  rw [mass_faraday, mass_faraday, energySq_dual, magneticSq_dual]
  ring

theorem faradayDot_dual (p : FaradayParams) :
    faradayDot (dualFaradayParams p) = -faradayDot p := by
  simp only [faradayDot, dualFaradayParams, Fin.sum_univ_three]
  ring

theorem J_swapFaraday (p : FaradayParams) :
    J (toTorsion (swapFaradayParams p)) = -J (toTorsion p) := by
  rw [toTorsion_swap, J_dagger]

theorem mass_swapFaraday (p : FaradayParams) :
    mass (toTorsion (swapFaradayParams p)) = mass (toTorsion p) := by
  rw [toTorsion_swap, mass_dagger]

theorem J_timeReverse (p : FaradayParams) :
    J (toTorsion (timeReverseFaradayParams p)) = J (toTorsion p) := by
  rw [J_faraday, J_faraday, energySq_timeReverse, magneticSq_timeReverse]

theorem faradayDot_timeReverse (p : FaradayParams) :
    faradayDot (timeReverseFaradayParams p) = -faradayDot p := by
  simp only [faradayDot, timeReverseFaradayParams, Fin.sum_univ_three]
  ring

/-! ### Coefficient Lorentz 3-force (STA bookkeeping, not a DST derivation) -/

def cross (u v : Fin 3 → ℝ) : Fin 3 → ℝ
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

def lorentzForce (q : ℝ) (p : FaradayParams) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun a => q * (p.E a + cross v p.B a)

def lorentzPower (q : ℝ) (p : FaradayParams) (v : Fin 3 → ℝ) : ℝ :=
  q * ∑ a : Fin 3, p.E a * v a

def restVelocity : Fin 3 → ℝ := fun _ => 0

def pureE (Ex : ℝ) : FaradayParams where
  E := fun
    | 0 => Ex
    | _ => 0
  B := fun _ => 0

def pureB (Bx : ℝ) : FaradayParams where
  E := fun _ => 0
  B := fun
    | 0 => Bx
    | _ => 0

/-- Helicity snapshot of a \(z\)-propagating circular wave at one instant:
\(E=E_0\hat x\), \(B=\sigma E_0\hat y\) (units \(c=1\)). -/
def circularSnapshot (σ E0 : ℝ) : FaradayParams where
  E := fun
    | 0 => E0
    | _ => 0
  B := fun
    | 1 => σ * E0
    | _ => 0

def yVelocity (vy : ℝ) : Fin 3 → ℝ
  | 1 => vy
  | _ => 0

theorem circularSnapshot_dot (σ E0 : ℝ) :
    faradayDot (circularSnapshot σ E0) = 0 := by
  simp [faradayDot, circularSnapshot, Fin.sum_univ_three]

theorem circularSnapshot_energy (σ E0 : ℝ) :
    energySq (circularSnapshot σ E0) = E0 ^ 2 := by
  simp [energySq, circularSnapshot, Fin.sum_univ_three]

theorem circularSnapshot_magnetic (σ E0 : ℝ) :
    magneticSq (circularSnapshot σ E0) = (σ * E0) ^ 2 := by
  simp [magneticSq, circularSnapshot, Fin.sum_univ_three]

theorem circularSnapshot_energy_eq_magnetic {σ E0 : ℝ} (hσ : σ ^ 2 = 1) :
    energySq (circularSnapshot σ E0) = magneticSq (circularSnapshot σ E0) := by
  rw [circularSnapshot_energy, circularSnapshot_magnetic, mul_pow, hσ, one_mul]

theorem circularSnapshot_J {σ E0 : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (circularSnapshot σ E0)) = 0 :=
  J_eq_zero_of_energy_eq_magnetic (circularSnapshot_energy_eq_magnetic hσ)

theorem circularSnapshot_null {σ E0 : ℝ} (hσ : σ ^ 2 = 1) :
    energySq (circularSnapshot σ E0) = magneticSq (circularSnapshot σ E0) ∧
      J (toTorsion (circularSnapshot σ E0)) = 0 ∧
      faradayDot (circularSnapshot σ E0) = 0 :=
  ⟨circularSnapshot_energy_eq_magnetic hσ, circularSnapshot_J hσ,
    circularSnapshot_dot σ E0⟩

theorem circularSnapshot_mass_eq {σ E0 : ℝ} (hσ : σ ^ 2 = 1) :
    mass (toTorsion (circularSnapshot σ E0)) = E0 ^ 2 := by
  rw [mass_eq_energySq_of_null (circularSnapshot_energy_eq_magnetic hσ),
    circularSnapshot_energy]

theorem circularSnapshot_mass_pos {σ E0 : ℝ} (hσ : σ ^ 2 = 1) (hE : E0 ≠ 0) :
    0 < mass (toTorsion (circularSnapshot σ E0)) := by
  refine mass_pos_of_null (circularSnapshot_energy_eq_magnetic hσ) ?_
  rw [circularSnapshot_energy]
  exact pow_ne_zero 2 hE

theorem ne_of_E_ne {p q : FaradayParams} {a : Fin 3} (h : p.E a ≠ q.E a) : p ≠ q :=
  fun hp => h (hp ▸ rfl)

theorem ne_of_B_ne {p q : FaradayParams} {a : Fin 3} (h : p.B a ≠ q.B a) : p ≠ q :=
  fun hp => h (hp ▸ rfl)

/-- On a pure magnetic field Hodge dual and the parameter swap coincide. -/
theorem dual_eq_swap_of_pureB (Bx : ℝ) :
    dualFaradayParams (pureB Bx) = swapFaradayParams (pureB Bx) := by
  ext a <;> fin_cases a <;> simp [dualFaradayParams, swapFaradayParams, pureB]

/-- On a pure electric field they differ by the sign of the dual image. -/
theorem dual_ne_swap_of_pureE :
    dualFaradayParams (pureE 1) ≠ swapFaradayParams (pureE 1) :=
  ne_of_B_ne (a := 0)
    (by simp [dualFaradayParams, swapFaradayParams, pureE]; norm_num)

theorem dual_ne_timeReverse_of_pureE :
    dualFaradayParams (pureE 1) ≠ timeReverseFaradayParams (pureE 1) :=
  ne_of_E_ne (a := 0) (by simp [dualFaradayParams, timeReverseFaradayParams, pureE])

theorem swap_ne_timeReverse_of_pureE :
    swapFaradayParams (pureE 1) ≠ timeReverseFaradayParams (pureE 1) :=
  ne_of_E_ne (a := 0) (by simp [swapFaradayParams, timeReverseFaradayParams, pureE])

theorem lorentzForce_rest_pureB (q Bx : ℝ) :
    lorentzForce q (pureB Bx) restVelocity = fun _ => 0 := by
  funext a
  unfold lorentzForce restVelocity pureB cross
  fin_cases a <;> simp

theorem lorentzForce_rest_pureE (q Ex : ℝ) :
    lorentzForce q (pureE Ex) restVelocity 0 = q * Ex ∧
      lorentzForce q (pureE Ex) restVelocity 1 = 0 ∧
      lorentzForce q (pureE Ex) restVelocity 2 = 0 := by
  unfold lorentzForce restVelocity pureE cross
  simp

theorem lorentzPower_rest (q : ℝ) (p : FaradayParams) :
    lorentzPower q p restVelocity = 0 := by
  unfold lorentzPower restVelocity
  simp

theorem lorentzForce_pureB_yVelocity (q Bx vy : ℝ) :
    lorentzForce q (pureB Bx) (yVelocity vy) 2 = -(q * vy * Bx) ∧
      lorentzForce q (pureB Bx) (yVelocity vy) 0 = 0 ∧
      lorentzForce q (pureB Bx) (yVelocity vy) 1 = 0 := by
  unfold lorentzForce yVelocity pureB cross
  simp
  ring

/-! ### First-order sandwich increment versus the paper wedge -/

/-- First-order increment of \(RX\widetilde R\) at \(R=1+\varepsilon\Omega\). -/
noncomputable def sandwichIncrement (Ω X : PGA) : PGA :=
  Ω * X - X * Ω

/-- Outer product used by the paper's \(F\wedge X\). -/
noncomputable def paperWedgeIncrement (Ω X : PGA) : PGA :=
  (1 / 2 : ℝ) • (Ω * X + X * Ω)

private theorem half_smul_eq_zero {y : PGA}
    (h : (1 / 2 : ℝ) • y = 0) : y = 0 := by
  have : (2 : ℝ) • ((1 / 2 : ℝ) • y) = (2 : ℝ) • 0 := by rw [h]
  simpa [smul_smul] using this

private theorem cyclic0_mul_ι0 :
    cyclic 0 * ι 0 = ι 0 * cyclic 0 := by
  unfold cyclic
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  calc ι 3 * ι 2 * ι 0
      = ι 3 * (ι 2 * ι 0) := by simp [mul_assoc]
    _ = ι 3 * (-(ι 0 * ι 2)) := by rw [h20]
    _ = -((ι 3 * ι 0) * ι 2) := by simp [mul_neg, mul_assoc]
    _ = -((-(ι 0 * ι 3)) * ι 2) := by rw [h30]
    _ = ι 0 * (ι 3 * ι 2) := by simp [mul_assoc]
    _ = ι 0 * cyclic 0 := rfl

theorem sandwichIncrement_rest_pureB :
    sandwichIncrement (cyclic 0) (ι 0) = 0 := by
  unfold sandwichIncrement
  rw [cyclic0_mul_ι0]
  simp

private theorem cyclic1_mul_ι0 :
    cyclic 1 * ι 0 = ι 0 * cyclic 1 := by
  unfold cyclic
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc ι 1 * ι 3 * ι 0
      = ι 1 * (ι 3 * ι 0) := by simp [mul_assoc]
    _ = ι 1 * (-(ι 0 * ι 3)) := by rw [h30]
    _ = -((ι 1 * ι 0) * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -((-(ι 0 * ι 1)) * ι 3) := by rw [h10]
    _ = ι 0 * (ι 1 * ι 3) := by simp [mul_assoc]
    _ = ι 0 * cyclic 1 := rfl

private theorem cyclic2_mul_ι0 :
    cyclic 2 * ι 0 = ι 0 * cyclic 2 := by
  unfold cyclic
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  calc ι 2 * ι 1 * ι 0
      = ι 2 * (ι 1 * ι 0) := by simp [mul_assoc]
    _ = ι 2 * (-(ι 0 * ι 1)) := by rw [h10]
    _ = -((ι 2 * ι 0) * ι 1) := by simp [mul_neg, mul_assoc]
    _ = -((-(ι 0 * ι 2)) * ι 1) := by rw [h20]
    _ = ι 0 * (ι 2 * ι 1) := by simp [mul_assoc]
    _ = ι 0 * cyclic 2 := rfl

/-- Every magnetic generator commutes with the rest frame \(e_0\). -/
theorem sandwichIncrement_rest_cyclic (a : Fin 3) :
    sandwichIncrement (cyclic a) (ι 0) = 0 := by
  match a with
  | 0 => exact sandwichIncrement_rest_pureB
  | 1 =>
    unfold sandwichIncrement
    rw [cyclic1_mul_ι0]
    simp
  | 2 =>
    unfold sandwichIncrement
    rw [cyclic2_mul_ι0]
    simp

theorem sandwichIncrement_add (Ω₁ Ω₂ X : PGA) :
    sandwichIncrement (Ω₁ + Ω₂) X =
      sandwichIncrement Ω₁ X + sandwichIncrement Ω₂ X := by
  simp only [sandwichIncrement, mul_add, add_mul]
  abel

theorem sandwichIncrement_smul (c : ℝ) (Ω X : PGA) :
    sandwichIncrement (c • Ω) X = c • sandwichIncrement Ω X := by
  simp [sandwichIncrement, Algebra.smul_mul_assoc, smul_sub]

private theorem sandwichIncrement_sum_fin3 (f : Fin 3 → PGA) (X : PGA) :
    sandwichIncrement (∑ a, f a) X = ∑ a, sandwichIncrement (f a) X := by
  simp [Fin.sum_univ_three, sandwichIncrement_add]

/-- The dual Faraday summand never kicks a rest frame at first order. -/
theorem sandwichIncrement_rest_faradayDual (p : FaradayParams) :
    sandwichIncrement (faradayDual p) (ι 0) = 0 := by
  unfold faradayDual toTorsion omegaDual
  rw [sandwichIncrement_sum_fin3]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [sandwichIncrement_smul, sandwichIncrement_rest_cyclic]
  simp

private theorem hyperbolic0_mul_ι0 :
    hyperbolic 0 * ι 0 = ι 1 := by
  unfold hyperbolic
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc ι 0 * ι 1 * ι 0
      = ι 0 * (ι 1 * ι 0) := by simp [mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 1)) := by rw [h10]
    _ = -((ι 0 * ι 0) * ι 1) := by simp [mul_neg, mul_assoc]
    _ = -(algebraMap ℝ PGA (-1 : ℝ) * ι 1) := by rw [e0_sq]
    _ = ι 1 := by simp [map_neg]

private theorem ι0_mul_hyperbolic0 :
    ι 0 * hyperbolic 0 = -ι 1 := by
  unfold hyperbolic
  calc ι 0 * (ι 0 * ι 1)
      = (ι 0 * ι 0) * ι 1 := by simp [mul_assoc]
    _ = algebraMap ℝ PGA (-1 : ℝ) * ι 1 := by rw [e0_sq]
    _ = -ι 1 := by simp [map_neg]

theorem sandwichIncrement_rest_pureE :
    sandwichIncrement (hyperbolic 0) (ι 0) = (2 : ℝ) • ι 1 := by
  unfold sandwichIncrement
  rw [hyperbolic0_mul_ι0, ι0_mul_hyperbolic0]
  simp [two_smul]

private theorem e2_sq' : ι 2 * ι 2 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (2 : Fin 5)

private theorem e3_sq' : ι 3 * ι 3 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (3 : Fin 5)

private theorem cyclic0_mul_ι2 :
    cyclic 0 * ι 2 = ι 3 := by
  unfold cyclic
  calc ι 3 * ι 2 * ι 2
      = ι 3 * (ι 2 * ι 2) := by simp [mul_assoc]
    _ = ι 3 * (1 : PGA) := by rw [e2_sq']
    _ = ι 3 := by simp

private theorem ι2_mul_cyclic0 :
    ι 2 * cyclic 0 = -ι 3 := by
  unfold cyclic
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  calc ι 2 * (ι 3 * ι 2)
      = (ι 2 * ι 3) * ι 2 := by simp [mul_assoc]
    _ = (-(ι 3 * ι 2)) * ι 2 := by rw [h23]
    _ = -(ι 3 * (ι 2 * ι 2)) := by simp [mul_assoc]
    _ = -(ι 3 * (1 : PGA) ) := by rw [e2_sq']
    _ = -ι 3 := by simp

/-- A \(y\)-velocity against a pure \(B_x\) generator produces a \(z\)-kick. -/
theorem sandwichIncrement_moving_pureB :
    sandwichIncrement (cyclic 0) (ι 2) = (2 : ℝ) • ι 3 := by
  unfold sandwichIncrement
  rw [cyclic0_mul_ι2, ι2_mul_cyclic0]
  simp [two_smul]

theorem paperWedge_moving_pureB :
    paperWedgeIncrement (cyclic 0) (ι 2) = 0 := by
  unfold paperWedgeIncrement
  rw [cyclic0_mul_ι2, ι2_mul_cyclic0]
  simp

theorem sandwichIncrement_moving_pureB_ne_zero :
    sandwichIncrement (cyclic 0) (ι 2) ≠ 0 := by
  rw [sandwichIncrement_moving_pureB]
  intro h
  have hι : ι 3 = 0 := by
    apply half_smul_eq_zero
    simpa [smul_smul] using congrArg (fun z => (1 / 2 : ℝ) • z) h
  have : (1 : PGA) = 0 := by rw [← e3_sq', hι, mul_zero]
  exact one_ne_zero this

/-- On a moving magnetic rest-frame the commutator is the kick and the wedge
vanishes — the opposite of the rest-magnetic case. -/
theorem sandwich_moving_pureB_ne_wedge :
    sandwichIncrement (cyclic 0) (ι 2) = (2 : ℝ) • ι 3 ∧
      paperWedgeIncrement (cyclic 0) (ι 2) = 0 :=
  ⟨sandwichIncrement_moving_pureB, paperWedge_moving_pureB⟩

/-- The rest-magnetic blade squares against its reverse to \(-1\). -/
private theorem rest_magnetic_blade_sq :
    (ι 0 * cyclic 0) * (ι 2 * ι 3 * ι 0) = (-1 : PGA) := by
  unfold cyclic
  calc ι 0 * (ι 3 * ι 2) * (ι 2 * ι 3 * ι 0)
      = ι 0 * ι 3 * (ι 2 * ι 2) * ι 3 * ι 0 := by simp [mul_assoc]
    _ = ι 0 * ι 3 * ι 3 * ι 0 := by simp [e2_sq']
    _ = ι 0 * (ι 3 * ι 3) * ι 0 := by simp [mul_assoc]
    _ = ι 0 * ι 0 := by simp [e3_sq']
    _ = algebraMap ℝ PGA (-1 : ℝ) := e0_sq
    _ = (-1 : PGA) := by simp

theorem paperWedge_rest_pureB_ne_zero :
    paperWedgeIncrement (cyclic 0) (ι 0) ≠ 0 := by
  intro h
  have hsum : cyclic 0 * ι 0 + ι 0 * cyclic 0 = 0 :=
    half_smul_eq_zero h
  have htwice : (2 : ℝ) • (ι 0 * cyclic 0) = 0 := by
    rw [two_smul]
    rwa [cyclic0_mul_ι0] at hsum
  have hblade : ι 0 * cyclic 0 = 0 := by
    have := congrArg (fun z => (1 / 2 : ℝ) • z) htwice
    simpa [smul_smul] using this
  have hneg : (-1 : PGA) = 0 := by
    rw [← rest_magnetic_blade_sq, hblade, zero_mul]
  have : (1 : PGA) = 0 := by
    simpa using congrArg (fun z => -z) hneg
  exact one_ne_zero this

theorem paper_wedge_ne_lorentz_increment :
    sandwichIncrement (cyclic 0) (ι 0) = 0 ∧
      paperWedgeIncrement (cyclic 0) (ι 0) ≠ 0 :=
  ⟨sandwichIncrement_rest_pureB, paperWedge_rest_pureB_ne_zero⟩

/-! ### Sandwich increment is the Lorentz 4-force of \((E,-B)\) -/

theorem sandwichIncrement_add_right (Ω X Y : PGA) :
    sandwichIncrement Ω (X + Y) =
      sandwichIncrement Ω X + sandwichIncrement Ω Y := by
  simp [sandwichIncrement, mul_add, add_mul, sub_eq_add_neg]
  abel

theorem sandwichIncrement_smul_right (Ω : PGA) (c : ℝ) (X : PGA) :
    sandwichIncrement Ω (c • X) = c • sandwichIncrement Ω X := by
  simp [sandwichIncrement, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]

/-- Spatial frame vector \(e_{a+1}\). -/
noncomputable def spatialVec : Fin 3 → PGA
  | 0 => ι 1
  | 1 => ι 2
  | 2 => ι 3

/-- Non-relativistic Minkowski vector \(e_0+v\). -/
noncomputable def minkowskiVec (v : Fin 3 → ℝ) : PGA :=
  ι 0 + v 0 • ι 1 + v 1 • ι 2 + v 2 • ι 3

/-- Spatial sandwich kick \(E-v\times B\). -/
def sandwichForce (p : FaradayParams) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun a => p.E a - cross v p.B a

/-- Written 4-kick of the sandwich: \((E\cdot v)\,e_0+(E-v\times B)\). -/
noncomputable def lorentzKick (p : FaradayParams) (v : Fin 3 → ℝ) : PGA :=
  lorentzPower 1 p v • ι 0 +
    sandwichForce p v 0 • ι 1 +
    sandwichForce p v 1 • ι 2 +
    sandwichForce p v 2 • ι 3

theorem hyperbolic_eq_ι0_mul_spatial (a : Fin 3) :
    hyperbolic a = ι 0 * spatialVec a := by
  fin_cases a <;> rfl

private theorem spatial_sq (a : Fin 3) :
    spatialVec a * spatialVec a = (1 : PGA) := by
  fin_cases a
  · exact e1_sq
  · change ι 2 * ι 2 = 1
    simpa [Q311_e5vec, w311] using e_sq (2 : Fin 5)
  · change ι 3 * ι 3 = 1
    simpa [Q311_e5vec, w311] using e_sq (3 : Fin 5)

private theorem spatial_ι0_anticomm (a : Fin 3) :
    spatialVec a * ι 0 = -(ι 0 * spatialVec a) := by
  fin_cases a <;> exact e_mul_anticomm (by decide)

private theorem spatial_anticomm {a b : Fin 3} (h : a ≠ b) :
    spatialVec a * spatialVec b = -(spatialVec b * spatialVec a) := by
  fin_cases a <;> fin_cases b <;>
    (first | cases h rfl | exact e_mul_anticomm (by decide))

private theorem hyperbolic_mul_ι0 (a : Fin 3) :
    hyperbolic a * ι 0 = spatialVec a := by
  rw [hyperbolic_eq_ι0_mul_spatial]
  have hanti := spatial_ι0_anticomm a
  calc ι 0 * spatialVec a * ι 0
      = ι 0 * (spatialVec a * ι 0) := by simp [mul_assoc]
    _ = ι 0 * (-(ι 0 * spatialVec a)) := by rw [hanti]
    _ = -((ι 0 * ι 0) * spatialVec a) := by simp [mul_neg, mul_assoc]
    _ = -((algebraMap ℝ PGA (-1 : ℝ)) * spatialVec a) := by rw [e0_sq]
    _ = spatialVec a := by simp [map_neg]

private theorem ι0_mul_hyperbolic (a : Fin 3) :
    ι 0 * hyperbolic a = -spatialVec a := by
  rw [hyperbolic_eq_ι0_mul_spatial]
  calc ι 0 * (ι 0 * spatialVec a)
      = (ι 0 * ι 0) * spatialVec a := by simp [mul_assoc]
    _ = algebraMap ℝ PGA (-1 : ℝ) * spatialVec a := by rw [e0_sq]
    _ = -spatialVec a := by simp [map_neg]

theorem sandwichIncrement_rest_hyperbolic (a : Fin 3) :
    sandwichIncrement (hyperbolic a) (ι 0) = (2 : ℝ) • spatialVec a := by
  unfold sandwichIncrement
  rw [hyperbolic_mul_ι0, ι0_mul_hyperbolic]
  simp [two_smul]

private theorem hyperbolic_mul_own_spatial (a : Fin 3) :
    hyperbolic a * spatialVec a = ι 0 := by
  rw [hyperbolic_eq_ι0_mul_spatial]
  calc ι 0 * spatialVec a * spatialVec a
      = ι 0 * (spatialVec a * spatialVec a) := by simp [mul_assoc]
    _ = ι 0 * (1 : PGA) := by rw [spatial_sq]
    _ = ι 0 := by simp

private theorem own_spatial_mul_hyperbolic (a : Fin 3) :
    spatialVec a * hyperbolic a = -ι 0 := by
  rw [hyperbolic_eq_ι0_mul_spatial]
  have hanti := spatial_ι0_anticomm a
  calc spatialVec a * (ι 0 * spatialVec a)
      = (spatialVec a * ι 0) * spatialVec a := by simp [mul_assoc]
    _ = (-(ι 0 * spatialVec a)) * spatialVec a := by rw [hanti]
    _ = -(ι 0 * (spatialVec a * spatialVec a)) := by simp [mul_assoc]
    _ = -(ι 0 * (1 : PGA)) := by rw [spatial_sq]
    _ = -ι 0 := by simp

theorem sandwichIncrement_hyperbolic_own (a : Fin 3) :
    sandwichIncrement (hyperbolic a) (spatialVec a) = (2 : ℝ) • ι 0 := by
  unfold sandwichIncrement
  rw [hyperbolic_mul_own_spatial, own_spatial_mul_hyperbolic]
  simp [two_smul]

theorem sandwichIncrement_hyperbolic_off {a b : Fin 3} (h : a ≠ b) :
    sandwichIncrement (hyperbolic a) (spatialVec b) = 0 := by
  unfold sandwichIncrement
  rw [hyperbolic_eq_ι0_mul_spatial]
  have hba := spatial_ι0_anticomm b
  have hab := spatial_anticomm h
  have hsum : spatialVec a * spatialVec b + spatialVec b * spatialVec a = 0 := by
    rw [hab]; simp
  calc ι 0 * spatialVec a * spatialVec b - spatialVec b * (ι 0 * spatialVec a)
      = ι 0 * (spatialVec a * spatialVec b) -
          (spatialVec b * ι 0) * spatialVec a := by simp [mul_assoc]
    _ = ι 0 * (spatialVec a * spatialVec b) -
          (-(ι 0 * spatialVec b)) * spatialVec a := by rw [hba]
    _ = ι 0 * (spatialVec a * spatialVec b) +
          (ι 0 * spatialVec b) * spatialVec a := by simp [sub_eq_add_neg]
    _ = ι 0 * (spatialVec a * spatialVec b + spatialVec b * spatialVec a) := by
        simp [mul_add, mul_assoc]
    _ = ι 0 * 0 := by rw [hsum]
    _ = 0 := by simp

theorem sandwichIncrement_hyperbolic_spatial (a b : Fin 3) :
    sandwichIncrement (hyperbolic a) (spatialVec b) =
      if a = b then (2 : ℝ) • ι 0 else 0 := by
  split_ifs with h
  · subst h; exact sandwichIncrement_hyperbolic_own a
  · exact sandwichIncrement_hyperbolic_off h

/-! #### Cyclic generators on spatial vectors: \(2\,\hat e_a\times\hat e_b\) -/

private theorem cyclic0_mul_ι1 :
    cyclic 0 * ι 1 = ι 1 * cyclic 0 := by
  unfold cyclic
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  calc ι 3 * ι 2 * ι 1
      = ι 3 * (ι 2 * ι 1) := by simp [mul_assoc]
    _ = ι 3 * (-(ι 1 * ι 2)) := by rw [h21]
    _ = -((ι 3 * ι 1) * ι 2) := by simp [mul_neg, mul_assoc]
    _ = -((-(ι 1 * ι 3)) * ι 2) := by rw [h31]
    _ = ι 1 * (ι 3 * ι 2) := by simp [mul_assoc]
    _ = ι 1 * cyclic 0 := rfl

theorem sandwichIncrement_cyclic0_ι1 :
    sandwichIncrement (cyclic 0) (ι 1) = 0 := by
  unfold sandwichIncrement
  rw [cyclic0_mul_ι1]
  simp

private theorem cyclic0_mul_ι3 :
    cyclic 0 * ι 3 = -ι 2 := by
  unfold cyclic
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  calc ι 3 * ι 2 * ι 3
      = ι 3 * (ι 2 * ι 3) := by simp [mul_assoc]
    _ = ι 3 * (-(ι 3 * ι 2)) := by rw [h23]
    _ = -((ι 3 * ι 3) * ι 2) := by simp [mul_neg, mul_assoc]
    _ = -((1 : PGA) * ι 2) := by rw [e3_sq']
    _ = -ι 2 := by simp

private theorem ι3_mul_cyclic0 :
    ι 3 * cyclic 0 = ι 2 := by
  unfold cyclic
  calc ι 3 * (ι 3 * ι 2)
      = (ι 3 * ι 3) * ι 2 := by simp [mul_assoc]
    _ = (1 : PGA) * ι 2 := by rw [e3_sq']
    _ = ι 2 := by simp

theorem sandwichIncrement_cyclic0_ι3 :
    sandwichIncrement (cyclic 0) (ι 3) = -((2 : ℝ) • ι 2) := by
  unfold sandwichIncrement
  rw [cyclic0_mul_ι3, ι3_mul_cyclic0]
  simp [two_smul, sub_eq_add_neg]

private theorem cyclic1_mul_ι1 :
    cyclic 1 * ι 1 = -ι 3 := by
  unfold cyclic
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  calc ι 1 * ι 3 * ι 1
      = ι 1 * (ι 3 * ι 1) := by simp [mul_assoc]
    _ = ι 1 * (-(ι 1 * ι 3)) := by rw [h31]
    _ = -((ι 1 * ι 1) * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -((1 : PGA) * ι 3) := by rw [e1_sq]
    _ = -ι 3 := by simp

private theorem ι1_mul_cyclic1 :
    ι 1 * cyclic 1 = ι 3 := by
  unfold cyclic
  calc ι 1 * (ι 1 * ι 3)
      = (ι 1 * ι 1) * ι 3 := by simp [mul_assoc]
    _ = (1 : PGA) * ι 3 := by rw [e1_sq]
    _ = ι 3 := by simp

theorem sandwichIncrement_cyclic1_ι1 :
    sandwichIncrement (cyclic 1) (ι 1) = -((2 : ℝ) • ι 3) := by
  unfold sandwichIncrement
  rw [cyclic1_mul_ι1, ι1_mul_cyclic1]
  simp [two_smul, sub_eq_add_neg]

private theorem cyclic1_mul_ι2 :
    cyclic 1 * ι 2 = ι 2 * cyclic 1 := by
  unfold cyclic
  have h12 : ι 1 * ι 2 = -(ι 2 * ι 1) := e_mul_anticomm (by decide)
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  calc ι 1 * ι 3 * ι 2
      = ι 1 * (ι 3 * ι 2) := by simp [mul_assoc]
    _ = ι 1 * (-(ι 2 * ι 3)) := by rw [h32]
    _ = -((ι 1 * ι 2) * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -((-(ι 2 * ι 1)) * ι 3) := by rw [h12]
    _ = ι 2 * (ι 1 * ι 3) := by simp [mul_assoc]
    _ = ι 2 * cyclic 1 := rfl

theorem sandwichIncrement_cyclic1_ι2 :
    sandwichIncrement (cyclic 1) (ι 2) = 0 := by
  unfold sandwichIncrement
  rw [cyclic1_mul_ι2]
  simp

private theorem cyclic1_mul_ι3 :
    cyclic 1 * ι 3 = ι 1 := by
  unfold cyclic
  calc ι 1 * ι 3 * ι 3
      = ι 1 * (ι 3 * ι 3) := by simp [mul_assoc]
    _ = ι 1 * (1 : PGA) := by rw [e3_sq']
    _ = ι 1 := by simp

private theorem ι3_mul_cyclic1 :
    ι 3 * cyclic 1 = -ι 1 := by
  unfold cyclic
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  calc ι 3 * (ι 1 * ι 3)
      = (ι 3 * ι 1) * ι 3 := by simp [mul_assoc]
    _ = (-(ι 1 * ι 3)) * ι 3 := by rw [h31]
    _ = -(ι 1 * (ι 3 * ι 3)) := by simp [mul_assoc]
    _ = -(ι 1 * (1 : PGA)) := by rw [e3_sq']
    _ = -ι 1 := by simp

theorem sandwichIncrement_cyclic1_ι3 :
    sandwichIncrement (cyclic 1) (ι 3) = (2 : ℝ) • ι 1 := by
  unfold sandwichIncrement
  rw [cyclic1_mul_ι3, ι3_mul_cyclic1]
  simp [two_smul]

private theorem cyclic2_mul_ι1 :
    cyclic 2 * ι 1 = ι 2 := by
  unfold cyclic
  calc ι 2 * ι 1 * ι 1
      = ι 2 * (ι 1 * ι 1) := by simp [mul_assoc]
    _ = ι 2 * (1 : PGA) := by rw [e1_sq]
    _ = ι 2 := by simp

private theorem ι1_mul_cyclic2 :
    ι 1 * cyclic 2 = -ι 2 := by
  unfold cyclic
  have h12 : ι 1 * ι 2 = -(ι 2 * ι 1) := e_mul_anticomm (by decide)
  calc ι 1 * (ι 2 * ι 1)
      = (ι 1 * ι 2) * ι 1 := by simp [mul_assoc]
    _ = (-(ι 2 * ι 1)) * ι 1 := by rw [h12]
    _ = -(ι 2 * (ι 1 * ι 1)) := by simp [mul_assoc]
    _ = -(ι 2 * (1 : PGA)) := by rw [e1_sq]
    _ = -ι 2 := by simp

theorem sandwichIncrement_cyclic2_ι1 :
    sandwichIncrement (cyclic 2) (ι 1) = (2 : ℝ) • ι 2 := by
  unfold sandwichIncrement
  rw [cyclic2_mul_ι1, ι1_mul_cyclic2]
  simp [two_smul]

private theorem cyclic2_mul_ι2 :
    cyclic 2 * ι 2 = -ι 1 := by
  unfold cyclic
  have h12 : ι 1 * ι 2 = -(ι 2 * ι 1) := e_mul_anticomm (by decide)
  calc ι 2 * ι 1 * ι 2
      = ι 2 * (ι 1 * ι 2) := by simp [mul_assoc]
    _ = ι 2 * (-(ι 2 * ι 1)) := by rw [h12]
    _ = -((ι 2 * ι 2) * ι 1) := by simp [mul_neg, mul_assoc]
    _ = -((1 : PGA) * ι 1) := by rw [e2_sq']
    _ = -ι 1 := by simp

private theorem ι2_mul_cyclic2 :
    ι 2 * cyclic 2 = ι 1 := by
  unfold cyclic
  calc ι 2 * (ι 2 * ι 1)
      = (ι 2 * ι 2) * ι 1 := by simp [mul_assoc]
    _ = (1 : PGA) * ι 1 := by rw [e2_sq']
    _ = ι 1 := by simp

theorem sandwichIncrement_cyclic2_ι2 :
    sandwichIncrement (cyclic 2) (ι 2) = -((2 : ℝ) • ι 1) := by
  unfold sandwichIncrement
  rw [cyclic2_mul_ι2, ι2_mul_cyclic2]
  simp [two_smul, sub_eq_add_neg]

private theorem cyclic2_mul_ι3 :
    cyclic 2 * ι 3 = ι 3 * cyclic 2 := by
  unfold cyclic
  have h13 : ι 1 * ι 3 = -(ι 3 * ι 1) := e_mul_anticomm (by decide)
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  calc ι 2 * ι 1 * ι 3
      = ι 2 * (ι 1 * ι 3) := by simp [mul_assoc]
    _ = ι 2 * (-(ι 3 * ι 1)) := by rw [h13]
    _ = -((ι 2 * ι 3) * ι 1) := by simp [mul_neg, mul_assoc]
    _ = -((-(ι 3 * ι 2)) * ι 1) := by rw [h23]
    _ = ι 3 * (ι 2 * ι 1) := by simp [mul_assoc]
    _ = ι 3 * cyclic 2 := rfl

theorem sandwichIncrement_cyclic2_ι3 :
    sandwichIncrement (cyclic 2) (ι 3) = 0 := by
  unfold sandwichIncrement
  rw [cyclic2_mul_ι3]
  simp

theorem sandwichIncrement_cyclic_spatial (a b : Fin 3) :
    sandwichIncrement (cyclic a) (spatialVec b) =
      match a, b with
      | 0, 0 => 0
      | 0, 1 => (2 : ℝ) • ι 3
      | 0, 2 => -((2 : ℝ) • ι 2)
      | 1, 0 => -((2 : ℝ) • ι 3)
      | 1, 1 => 0
      | 1, 2 => (2 : ℝ) • ι 1
      | 2, 0 => (2 : ℝ) • ι 2
      | 2, 1 => -((2 : ℝ) • ι 1)
      | 2, 2 => 0 := by
  fin_cases a <;> fin_cases b
  · exact sandwichIncrement_cyclic0_ι1
  · exact sandwichIncrement_moving_pureB
  · exact sandwichIncrement_cyclic0_ι3
  · exact sandwichIncrement_cyclic1_ι1
  · exact sandwichIncrement_cyclic1_ι2
  · exact sandwichIncrement_cyclic1_ι3
  · exact sandwichIncrement_cyclic2_ι1
  · exact sandwichIncrement_cyclic2_ι2
  · exact sandwichIncrement_cyclic2_ι3

private theorem smul_two_spatial (c : ℝ) (x : PGA) :
    (c / 2) • ((2 : ℝ) • x) = c • x := by
  rw [smul_smul]
  ring_nf

private theorem smul_two_spatial_neg (c : ℝ) (x : PGA) :
    (c / 2) • (-((2 : ℝ) • x)) = -(c • x) := by
  rw [smul_neg, smul_two_spatial]

theorem sandwichIncrement_rest_faradayUsual (p : FaradayParams) :
    sandwichIncrement (faradayUsual p) (ι 0) =
      p.E 0 • ι 1 + p.E 1 • ι 2 + p.E 2 • ι 3 := by
  unfold faradayUsual toTorsion omegaUsual
  rw [sandwichIncrement_sum_fin3]
  simp only [sandwichIncrement_smul, sandwichIncrement_rest_hyperbolic]
  simp [spatialVec, Fin.sum_univ_three, smul_two_spatial]

theorem sandwichIncrement_rest_faraday (p : FaradayParams) :
    sandwichIncrement (faraday p) (ι 0) =
      p.E 0 • ι 1 + p.E 1 • ι 2 + p.E 2 • ι 3 := by
  rw [faraday_eq_add, sandwichIncrement_add, sandwichIncrement_rest_faradayDual,
    add_zero, sandwichIncrement_rest_faradayUsual]

theorem sandwichIncrement_faradayUsual_spatial (p : FaradayParams) (b : Fin 3) :
    sandwichIncrement (faradayUsual p) (spatialVec b) = p.E b • ι 0 := by
  unfold faradayUsual toTorsion omegaUsual
  rw [sandwichIncrement_sum_fin3]
  simp only [sandwichIncrement_smul, sandwichIncrement_hyperbolic_spatial]
  fin_cases b <;> simp [smul_two_spatial]

private theorem sandwichIncrement_faradayDual_spatial0 (p : FaradayParams) :
    sandwichIncrement (faradayDual p) (spatialVec 0) =
      p.B 2 • ι 2 - p.B 1 • ι 3 := by
  unfold faradayDual toTorsion omegaDual spatialVec
  rw [sandwichIncrement_sum_fin3]
  simp only [sandwichIncrement_smul, Fin.sum_univ_three]
  rw [sandwichIncrement_cyclic0_ι1, sandwichIncrement_cyclic1_ι1,
    sandwichIncrement_cyclic2_ι1, smul_zero, smul_two_spatial_neg,
    smul_two_spatial]
  module

private theorem sandwichIncrement_faradayDual_spatial1 (p : FaradayParams) :
    sandwichIncrement (faradayDual p) (spatialVec 1) =
      p.B 0 • ι 3 - p.B 2 • ι 1 := by
  unfold faradayDual toTorsion omegaDual spatialVec
  rw [sandwichIncrement_sum_fin3]
  simp only [sandwichIncrement_smul, Fin.sum_univ_three]
  rw [sandwichIncrement_moving_pureB, sandwichIncrement_cyclic1_ι2,
    sandwichIncrement_cyclic2_ι2, smul_zero, smul_two_spatial,
    smul_two_spatial_neg]
  module

private theorem sandwichIncrement_faradayDual_spatial2 (p : FaradayParams) :
    sandwichIncrement (faradayDual p) (spatialVec 2) =
      p.B 1 • ι 1 - p.B 0 • ι 2 := by
  unfold faradayDual toTorsion omegaDual spatialVec
  rw [sandwichIncrement_sum_fin3]
  simp only [sandwichIncrement_smul, Fin.sum_univ_three]
  rw [sandwichIncrement_cyclic0_ι3, sandwichIncrement_cyclic1_ι3,
    sandwichIncrement_cyclic2_ι3, smul_zero, smul_two_spatial_neg,
    smul_two_spatial]
  module

theorem sandwichIncrement_faradayDual_spatial (p : FaradayParams) (b : Fin 3) :
    sandwichIncrement (faradayDual p) (spatialVec b) =
      -(cross (fun i => if i = b then (1 : ℝ) else 0) p.B 0) • ι 1 +
        -(cross (fun i => if i = b then (1 : ℝ) else 0) p.B 1) • ι 2 +
        -(cross (fun i => if i = b then (1 : ℝ) else 0) p.B 2) • ι 3 := by
  fin_cases b <;>
    (simp [cross, sandwichIncrement_faradayDual_spatial0,
      sandwichIncrement_faradayDual_spatial1,
      sandwichIncrement_faradayDual_spatial2, sub_eq_add_neg] <;> try abel)

theorem sandwichIncrement_faraday_spatial (p : FaradayParams) (b : Fin 3) :
    sandwichIncrement (faraday p) (spatialVec b) =
      p.E b • ι 0 +
        sandwichIncrement (faradayDual p) (spatialVec b) := by
  rw [faraday_eq_add, sandwichIncrement_add, sandwichIncrement_faradayUsual_spatial]

theorem minkowskiVec_eq (v : Fin 3 → ℝ) :
    minkowskiVec v = ι 0 + v 0 • spatialVec 0 + v 1 • spatialVec 1 +
      v 2 • spatialVec 2 := by
  simp [minkowskiVec, spatialVec]

theorem sandwichIncrement_faraday_minkowski (p : FaradayParams) (v : Fin 3 → ℝ) :
    sandwichIncrement (faraday p) (minkowskiVec v) = lorentzKick p v := by
  rw [minkowskiVec_eq]
  simp only [sandwichIncrement_add_right, sandwichIncrement_smul_right]
  rw [sandwichIncrement_rest_faraday, sandwichIncrement_faraday_spatial,
    sandwichIncrement_faraday_spatial, sandwichIncrement_faraday_spatial]
  rw [sandwichIncrement_faradayDual_spatial, sandwichIncrement_faradayDual_spatial,
    sandwichIncrement_faradayDual_spatial]
  unfold lorentzKick sandwichForce lorentzPower
  simp [cross, Fin.sum_univ_three]
  module

theorem sandwichForce_eq_lorentzForce_timeReverse (p : FaradayParams)
    (v : Fin 3 → ℝ) :
    sandwichForce p v = lorentzForce 1 (timeReverseFaradayParams p) v := by
  funext a
  fin_cases a <;> simp [sandwichForce, lorentzForce, timeReverseFaradayParams, cross]
  <;> ring

theorem lorentzPower_timeReverse (p : FaradayParams) (v : Fin 3 → ℝ) :
    lorentzPower 1 (timeReverseFaradayParams p) v = lorentzPower 1 p v :=
  rfl

theorem sandwichIncrement_rest_eq_lorentzKick (p : FaradayParams) :
    sandwichIncrement (faraday p) (minkowskiVec restVelocity) =
      lorentzKick p restVelocity :=
  sandwichIncrement_faraday_minkowski p restVelocity

theorem lorentzKick_rest (p : FaradayParams) :
    lorentzKick p restVelocity = p.E 0 • ι 1 + p.E 1 • ι 2 + p.E 2 • ι 3 := by
  unfold lorentzKick sandwichForce lorentzPower restVelocity
  simp [cross]

theorem sandwichIncrement_rest_faraday_eq_E (p : FaradayParams) :
    sandwichIncrement (faraday p) (ι 0) =
      sandwichIncrement (faraday p) (minkowskiVec restVelocity) := by
  have h : minkowskiVec restVelocity = ι 0 := by
    simp [minkowskiVec, restVelocity]
  rw [h]

end Gravity

end DstDiophantine
