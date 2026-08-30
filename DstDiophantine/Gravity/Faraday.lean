import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.Generators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Faraday bivector in the dual-rotor 6-space

## Paper boundary (do **not** claim)

Maxwell's equations are **not** derived. The identification of the Faraday
bivector with a laboratory electromagnetic field is a working hypothesis.
This module records coefficient-level identities on the same six generators
that carry the dual-rotor torsion.

No theorem asserts a derivation of Maxwell or of the Lorentz force from the
DST action.

## What is proved

* The Faraday coefficients \((E_a,B_a)\) live in the same 6-generator space
  as \(\Omega_{\mathrm{biv}}\): usual (boost, \(i\Gamma\)) plus dual
  (rotation, \(\Gamma\)). Section 10's single symbol \(F_{\mathrm{dual}}\)
  that mixes \(E\) and \(B\) is the *full* Faraday bivector; Section 12's
  split \(F_{\mathrm{usual}}\leftrightarrow\mathbf{E}\),
  \(F_{\mathrm{dual}}\leftrightarrow\mathbf{B}\) is the compatible
  decomposition.
* Duality \(X\mapsto Xi\) sends \((E,B)\mapsto(B,-E)\).
* First-order sandwich increment is the commutator \(\Omega X-X\Omega\).
  On a rest particle a pure electric generator produces a spatial kick
  and a pure magnetic generator produces none, matching the STA Lorentz
  3-force. The paper's outer product \(F\wedge X\) is nonzero on that
  magnetic rest case, so it is not the Lorentz increment.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations Motor RelativeRotor
open CliffordAlgebra (reverse)

/-! ### Faraday coefficients in the torsion 6-space -/

structure FaradayParams where
  E : Fin 3 → ℝ
  B : Fin 3 → ℝ

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
        have h : -(p.E a / 2) = -p.E a / 2 := by ring
        rw [h, add_comm]

theorem dual_faraday (p : FaradayParams) :
    dual (faraday p) = faraday (dualFaradayParams p) := by
  unfold faraday toTorsion dualFaradayParams omegaTorsion
  rw [dual_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simpa using dual_faraday_term p a

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

/-! ### First-order sandwich increment versus the paper wedge -/

/-- First-order increment of \(RX\widetilde R\) at \(R=1+\varepsilon\Omega\). -/
noncomputable def sandwichIncrement (Ω X : PGA) : PGA :=
  Ω * X - X * Ω

/-- Outer product used by the paper's \(F\wedge X\). -/
noncomputable def paperWedgeIncrement (Ω X : PGA) : PGA :=
  (1 / 2 : ℝ) • (Ω * X + X * Ω)

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

private theorem half_smul_eq_zero {y : PGA}
    (h : (1 / 2 : ℝ) • y = 0) : y = 0 := by
  have : (2 : ℝ) • ((1 / 2 : ℝ) • y) = (2 : ℝ) • 0 := by rw [h]
  simpa [smul_smul] using this

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

end Gravity

end DstDiophantine
