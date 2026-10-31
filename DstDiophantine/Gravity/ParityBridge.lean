import DstDiophantine.Gravity.BaryonAsymmetry
import DstDiophantine.Gravity.ChiralSpectrum
import DstDiophantine.Gravity.CircularPolarization
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Parity, the bridge, and the two disorders

## Paper boundary (do **not** claim)

No baryon current, no Sakharov identity, and no derivation of \(\eta\).
Spatial inversion is not charge conjugation, and the bridge is not
\(\mathrm{CP}\).

## What is proved

* Spatial inversion negates every spatial generator and exchanges the two
  chirality projectors of every axis.
* On Faraday coefficients it acts by \((E,B)\mapsto(-E,B)\). It preserves
  \(J\) and \(M\), and it flips \(E\cdot B\) and the beam component of
  \(E\times B\). A pure-sector field has \(E\cdot B=0\). A boost excess is
  pure electric; a rotation excess is pure magnetic.
* The bridge anticommutes with inversion: \(P(Xi)=-(PX)i\). One order of
  the composition is the usual--dual swap \((E,B)\mapsto(B,E)\); the other
  is the global sign of that swap. The swap reverses \(J\), preserves
  \(E\cdot B\), and flips the beam component.
* Inversion composed with laboratory time reversal is that global sign.
  \(J\), \(E\cdot B\), and the beam component are invariant under it.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations Invariant Logic Motor

/-! ### Inversion exchanges the projectors -/

theorem spatialParity_spatialGen (a : Fin 3) :
    spatialParity (spatialGen a) = -spatialGen a := by
  fin_cases a <;>
    simp [spatialGen, spatialParity_ι, spatialSign_one, spatialSign_two,
      spatialSign_three]

theorem spatialParity_chiralityRAxis (a : Fin 3) :
    spatialParity (chiralityRAxis a) = chiralityLAxis a := by
  unfold chiralityRAxis chiralityLAxis half
  rw [map_mul, map_add, map_one, spatialParity_spatialGen,
    AlgHom.commutes spatialParity (1 / 2)]
  abel_nf

theorem spatialParity_chiralityLAxis (a : Fin 3) :
    spatialParity (chiralityLAxis a) = chiralityRAxis a := by
  unfold chiralityLAxis chiralityRAxis half
  rw [map_mul, map_sub, map_one, spatialParity_spatialGen,
    AlgHom.commutes spatialParity (1 / 2)]
  abel_nf

/-! ### The bridge anticommutes with inversion -/

theorem spatialParity_dual (x : PGA) :
    spatialParity (dual x) = -dual (spatialParity x) := by
  unfold dual
  rw [map_mul, spatialParity_pseudoscalar, mul_neg]

/-! ### Inversion on Faraday coefficients -/

/-- Spatial inversion on the six-space: \((E,B)\mapsto(-E,B)\). -/
def parityFaradayParams (p : FaradayParams) : FaradayParams where
  E := fun a => -p.E a
  B := p.B

theorem spatialParity_faraday (p : FaradayParams) :
    spatialParity (faraday p) = faraday (parityFaradayParams p) := by
  unfold faraday toTorsion parityFaradayParams omegaTorsion
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_add, map_smul, map_smul, spatialParity_hyperbolic, spatialParity_cyclic]
  simp only [smul_neg, neg_smul, neg_div]

theorem energySq_parity (p : FaradayParams) :
    energySq (parityFaradayParams p) = energySq p := by
  unfold energySq parityFaradayParams
  simp only [Fin.sum_univ_three, neg_sq]

theorem magneticSq_parity (p : FaradayParams) :
    magneticSq (parityFaradayParams p) = magneticSq p := by
  rfl

theorem J_parityFaraday (p : FaradayParams) :
    J (toTorsion (parityFaradayParams p)) = J (toTorsion p) := by
  rw [J_faraday, J_faraday, energySq_parity, magneticSq_parity]

theorem mass_parityFaraday (p : FaradayParams) :
    mass (toTorsion (parityFaradayParams p)) = mass (toTorsion p) := by
  rw [mass_faraday, mass_faraday, energySq_parity, magneticSq_parity]

theorem faradayDot_parity (p : FaradayParams) :
    faradayDot (parityFaradayParams p) = -faradayDot p := by
  simp only [faradayDot, parityFaradayParams, Fin.sum_univ_three]
  ring

theorem poyntingZ_parity (p : FaradayParams) :
    poyntingZ (parityFaradayParams p) = -poyntingZ p := by
  simp [poyntingZ, cross, parityFaradayParams]
  ring

/-! ### A pure sector carries no \(E\cdot B\) -/

theorem faradayDot_pureElectric (E : Fin 3 → ℝ) :
    faradayDot ({ E := E, B := fun _ => 0 } : FaradayParams) = 0 := by
  simp [faradayDot]

theorem faradayDot_pureMagnetic (B : Fin 3 → ℝ) :
    faradayDot ({ E := fun _ => 0, B := B } : FaradayParams) = 0 := by
  simp [faradayDot]

theorem toTorsion_boostExcess (δ : ℝ) (dir : Fin 3 → ℝ) :
    toTorsion ({ E := fun a => δ * dir a, B := fun _ => 0 } : FaradayParams) =
      boostAlong δ dir :=
  rfl

theorem toTorsion_rotationExcess (δ : ℝ) (dir : Fin 3 → ℝ) :
    toTorsion ({ E := fun _ => 0, B := fun a => δ * dir a } : FaradayParams) =
      rotationAlong δ dir :=
  rfl

theorem faradayDot_boostAlong (δ : ℝ) (dir : Fin 3 → ℝ) :
    faradayDot ({ E := fun a => δ * dir a, B := fun _ => 0 } : FaradayParams) = 0 :=
  faradayDot_pureElectric _

theorem faradayDot_rotationAlong (δ : ℝ) (dir : Fin 3 → ℝ) :
    faradayDot ({ E := fun _ => 0, B := fun a => δ * dir a } : FaradayParams) = 0 :=
  faradayDot_pureMagnetic _

/-! ### Inversion composed with the bridge is the sector swap -/

theorem dual_parity_eq_swap (p : FaradayParams) :
    dualFaradayParams (parityFaradayParams p) = swapFaradayParams p := by
  ext a <;> simp [dualFaradayParams, parityFaradayParams, swapFaradayParams]

theorem parity_dual_eq_neg_swap (p : FaradayParams) :
    parityFaradayParams (dualFaradayParams p) =
      negFaradayParams (swapFaradayParams p) := by
  ext a <;> simp [parityFaradayParams, dualFaradayParams, negFaradayParams,
    swapFaradayParams]

theorem faradayDot_swap (p : FaradayParams) :
    faradayDot (swapFaradayParams p) = faradayDot p := by
  simp only [faradayDot, swapFaradayParams, Fin.sum_univ_three]
  ring

theorem poyntingZ_swap (p : FaradayParams) :
    poyntingZ (swapFaradayParams p) = -poyntingZ p := by
  simp [poyntingZ, cross, swapFaradayParams]
  ring

theorem J_negFaraday (p : FaradayParams) :
    J (toTorsion (negFaradayParams p)) = J (toTorsion p) := by
  rw [J_faraday, J_faraday]
  simp only [energySq, magneticSq, negFaradayParams, Fin.sum_univ_three, neg_sq]

theorem mass_negFaraday (p : FaradayParams) :
    mass (toTorsion (negFaradayParams p)) = mass (toTorsion p) := by
  rw [mass_faraday, mass_faraday]
  simp only [energySq, magneticSq, negFaradayParams, Fin.sum_univ_three, neg_sq]

theorem faradayDot_neg (p : FaradayParams) :
    faradayDot (negFaradayParams p) = faradayDot p := by
  simp only [faradayDot, negFaradayParams, Fin.sum_univ_three]
  ring

theorem poyntingZ_neg (p : FaradayParams) :
    poyntingZ (negFaradayParams p) = poyntingZ p := by
  simp [poyntingZ, cross, negFaradayParams]

/-! ### Inversion with laboratory time reversal is the global sign -/

theorem parity_timeReverse_eq_neg (p : FaradayParams) :
    parityFaradayParams (timeReverseFaradayParams p) = negFaradayParams p := by
  ext a <;> simp [parityFaradayParams, timeReverseFaradayParams, negFaradayParams]

theorem timeReverse_parity_eq_neg (p : FaradayParams) :
    timeReverseFaradayParams (parityFaradayParams p) = negFaradayParams p := by
  ext a <;> simp [parityFaradayParams, timeReverseFaradayParams, negFaradayParams]

end Gravity

end DstDiophantine
