import DstDiophantine.Gravity.CompactS3
import DstDiophantine.Gravity.NullRotation
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# One exponential, two limits

Off a common axis, `J_ε = B⁺₀ + √(1+ε²) B⁻₁` squares to `-ε²`. At `ε = 0` it is
the null generator. One closed form covers every real `ε`:

`exp(t J_ε) = cos(ε t) + (t sinc(ε t)) J_ε`.

For `ε ≠ 0` this equals `-1` precisely when `cos(ε t) = -1`, first at
`t = π/ε`. There `sinc` vanishes, and so does the equidistant Jacobian. As
`ε → 0⁺` the parameter `π/ε` recedes to infinity, `sinc(ε t) → 1`, and at each
fixed `t` the exponential tends to the parabolic rotor. The commutator of
`J_ε` with the null line vanishes if and only if `ε = 0`. The sandwich by the
exponential tends to the null rotation: the null line stays fixed, and `e₁`
is carried along it.

## Not claimed

* A position operator, or an uncertainty relation.
* That the light cone and the three-sphere are the same manifold.
* A derivation of `a₀`, of proper acceleration, or of a laboratory coupling.
-/

namespace DstDiophantine

namespace Gravity

open CliffordAlgebra (reverse)
open PGA Generators Motor Operations Sandwich
open Real hiding exp
open Filter Topology NormedSpace

/-- Off-axis generator `B⁺₀ + √(1+ε²) B⁻₁`. Squares to `-ε²`. -/
noncomputable def contractedGen (ε : ℝ) : PGA :=
  hyperbolic 0 + Real.sqrt (1 + ε ^ 2) • cyclic 1

/-- Half-angle parameters of `contractedGen`. -/
noncomputable def contractedParams (ε : ℝ) : Operations.TorsionParams where
  alpha := fun a => if a = 0 then 2 else 0
  beta := fun a => if a = 1 then 2 * Real.sqrt (1 + ε ^ 2) else 0

theorem contractedGen_sq (ε : ℝ) :
    contractedGen ε * contractedGen ε = (-(ε ^ 2)) • (1 : PGA) := by
  have hsq : (Real.sqrt (1 + ε ^ 2)) ^ 2 = 1 + ε ^ 2 :=
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + ε ^ 2)
  have h :=
    offAxis_scaled_sq (by decide : (0 : Fin 3) ≠ 1) (1 : ℝ) (Real.sqrt (1 + ε ^ 2))
  simp only [one_smul] at h
  rw [contractedGen, h, one_pow, hsq]
  congr 1
  ring

theorem contractedGen_zero : contractedGen 0 = parabolicGen := by
  simp [contractedGen, parabolicGen, Real.sqrt_one]

theorem omegaTorsion_contractedParams (ε : ℝ) :
    omegaTorsion (contractedParams ε) = contractedGen ε := by
  rw [omegaTorsion, Fin.sum_univ_three, contractedGen]
  simp [contractedParams, one_smul, zero_smul, add_zero, zero_add]

theorem continuous_contractedGen : Continuous contractedGen := by
  have hpow : Continuous (fun ε : ℝ => ε ^ 2) := (continuous_pow 2).comp continuous_id
  have hsqrt : Continuous (fun ε : ℝ => Real.sqrt (1 + ε ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add hpow)
  have hvec : Continuous (fun ε : ℝ => Real.sqrt (1 + ε ^ 2) • (cyclic 1 : PGA)) :=
    continuous_smul.comp (hsqrt.prodMk continuous_const)
  have hfun : contractedGen = fun ε => (hyperbolic 0 : PGA) +
      Real.sqrt (1 + ε ^ 2) • cyclic 1 := rfl
  rw [hfun]
  exact continuous_const.add hvec

/-- Unit generator `J_ε / ε`, for `ε ≠ 0`. Squares to `-1`. -/
noncomputable def contractedUnit (ε : ℝ) : PGA :=
  (1 / ε) • contractedGen ε

private theorem smul_mul_smul (c d : ℝ) (u v : PGA) :
    (c • u) * (d • v) = (c * d) • (u * v) := by
  rw [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm d c]

theorem contractedUnit_sq {ε : ℝ} (hε : ε ≠ 0) :
    contractedUnit ε * contractedUnit ε = -1 := by
  unfold contractedUnit
  rw [smul_mul_smul, contractedGen_sq, smul_smul]
  have : (1 / ε) * (1 / ε) * (-(ε ^ 2)) = (-1 : ℝ) := by
    field_simp [hε]
  rw [this, neg_one_smul]

theorem reverse_contractedGen (ε : ℝ) :
    reverse (contractedGen ε) = -contractedGen ε := by
  rw [contractedGen, map_add, map_smul, hyperbolic_reverse, cyclic_reverse, smul_neg]
  abel

theorem reverse_contractedUnit (ε : ℝ) :
    reverse (contractedUnit ε) = -contractedUnit ε := by
  unfold contractedUnit
  rw [map_smul, reverse_contractedGen, smul_neg]

/-- Elliptic closed form, `ε ≠ 0`. -/
theorem exp_contractedGen_closed {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    exp (t • contractedGen ε) =
      Real.cos (ε * t) • (1 : PGA) +
        (Real.sin (ε * t) / ε) • contractedGen ε := by
  have hscale : (ε * t) • contractedUnit ε = t • contractedGen ε := by
    unfold contractedUnit
    rw [smul_smul]
    congr 1
    field_simp [hε]
  rw [← hscale, exp_of_sq_neg_one (contractedUnit_sq hε)]
  unfold contractedUnit
  rw [smul_smul]
  congr 1
  field_simp [hε]

private theorem bivectorCoeff_eq {ε t : ℝ} (hε : ε ≠ 0) :
    Real.sin (ε * t) / ε = t * Real.sinc (ε * t) := by
  by_cases ht : ε * t = 0
  · have ht0 : t = 0 := (mul_eq_zero.mp ht).resolve_left hε
    simp [ht0, Real.sinc_zero]
  · rw [Real.sinc_of_ne_zero ht, div_eq_iff hε]
    rw [mul_comm (t * (Real.sin (ε * t) / (ε * t))) ε, ← mul_assoc]
    exact (mul_div_cancel₀ _ ht).symm

/-- One formula for the elliptic rotors and for the null rotor at `ε = 0`. -/
theorem exp_contractedGen_formula (ε t : ℝ) :
    exp (t • contractedGen ε) =
      Real.cos (ε * t) • (1 : PGA) +
        (t * Real.sinc (ε * t)) • contractedGen ε := by
  by_cases hε : ε = 0
  · subst hε
    rw [contractedGen_zero, exp_of_sq_zero parabolicGen_sq]
    simp [Real.cos_zero, Real.sinc_zero]
  · rw [exp_contractedGen_closed hε, bivectorCoeff_eq hε]

/-- At parameter `π/ε` the exponential is the antipodal rotor `-1`. -/
theorem exp_contractedGen_antipode {ε : ℝ} (hε : ε ≠ 0) :
    exp ((Real.pi / ε) • contractedGen ε) = -1 := by
  rw [exp_contractedGen_closed hε]
  have hθ : ε * (Real.pi / ε) = Real.pi := by field_simp [hε]
  rw [hθ, Real.cos_pi, Real.sin_pi]
  simp

private theorem cos_sin_unit_eq_neg_one_iff (ε θ : ℝ) :
    Real.cos θ • (1 : PGA) + Real.sin θ • contractedUnit ε = -1 ↔
      Real.cos θ = -1 := by
  constructor
  · intro h
    set U : PGA := contractedUnit ε
    have hrevU : reverse U = -U := reverse_contractedUnit ε
    have hrev :
        reverse (Real.cos θ • (1 : PGA) + Real.sin θ • U) =
          Real.cos θ • (1 : PGA) - Real.sin θ • U := by
      rw [map_add, map_smul, map_smul, CliffordAlgebra.reverse.map_one, hrevU, smul_neg]
      abel
    have hminus : Real.cos θ • (1 : PGA) - Real.sin θ • U = -1 := by
      rw [← hrev, h, map_neg, CliffordAlgebra.reverse.map_one]
    have hsum :
        (Real.cos θ • (1 : PGA) + Real.sin θ • U) +
            (Real.cos θ • (1 : PGA) - Real.sin θ • U) =
          (-1 : PGA) + -1 := by
      rw [h, hminus]
    have hleft : (2 * Real.cos θ) • (1 : PGA) =
        (Real.cos θ • (1 : PGA) + Real.sin θ • U) +
          (Real.cos θ • (1 : PGA) - Real.sin θ • U) := by
      rw [mul_smul, two_smul]
      abel
    have hright : (-1 : PGA) + -1 = (-2 : ℝ) • (1 : PGA) := by
      calc (-1 : PGA) + -1 = -((1 : PGA) + 1) := by abel
        _ = -((2 : ℝ) • (1 : PGA)) := by rw [two_smul]
        _ = (-2 : ℝ) • (1 : PGA) := by rw [neg_smul]
    have hcoef : (2 * Real.cos θ) • (1 : PGA) = (-2 : ℝ) • 1 := by
      rw [hleft, hsum, hright]
    have hmap :
        algebraMap ℝ PGA (2 * Real.cos θ) = algebraMap ℝ PGA (-2) := by
      simpa [Algebra.algebraMap_eq_smul_one] using hcoef
    have hnum : 2 * Real.cos θ = -2 :=
      FaithfulSMul.algebraMap_injective (R := ℝ) (A := PGA) hmap
    linarith
  · intro hcos
    have hsq := Real.sin_sq_add_cos_sq θ
    rw [hcos] at hsq
    have hsin0 : Real.sin θ ^ 2 = 0 := by linarith
    have hsin : Real.sin θ = 0 := sq_eq_zero_iff.mp hsin0
    rw [hcos, hsin]
    simp

/-- The exponential meets the antipode exactly on `cos(ε t) = -1`. -/
theorem exp_contractedGen_eq_neg_one_iff {ε t : ℝ} (hε : ε ≠ 0) :
    exp (t • contractedGen ε) = -1 ↔ Real.cos (ε * t) = -1 := by
  rw [exp_contractedGen_closed hε]
  have hunit :
      (Real.sin (ε * t) / ε) • contractedGen ε =
        Real.sin (ε * t) • contractedUnit ε := by
    unfold contractedUnit
    rw [smul_smul]
    congr 1
    field_simp [hε]
  rw [hunit]
  exact cos_sin_unit_eq_neg_one_iff ε (ε * t)

/-- The antipodal parameter recedes to infinity as the curvature tends to zero. -/
theorem antipodalParam_tendsto :
    Tendsto (fun ε : ℝ => Real.pi / ε) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  rw [tendsto_atTop]
  intro b
  by_cases hb : b ≤ 0
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hpos : (0 : ℝ) < ε := hε
    have : (0 : ℝ) < Real.pi / ε := div_pos Real.pi_pos hpos
    linarith
  · have hb0 : (0 : ℝ) < b := lt_of_not_ge hb
    have hδ : (0 : ℝ) < Real.pi / b := div_pos Real.pi_pos hb0
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / b) ∈ nhdsWithin 0 (Set.Ioi 0) := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Iio (Real.pi / b), isOpen_Iio, hδ, ?_⟩
      intro ε ⟨hlt, hpos⟩
      exact ⟨hpos, hlt⟩
    filter_upwards [hmem] with ε hε
    have hεpos : (0 : ℝ) < ε := hε.1
    have hlt : b * ε < Real.pi := by
      have hdiv : ε < Real.pi / b := hε.2
      rw [lt_div_iff₀ hb0] at hdiv
      rwa [mul_comm] at hdiv
    exact le_of_lt (by rwa [lt_div_iff₀ hεpos])

theorem exp_contractedGen_zero (t : ℝ) :
    exp (t • contractedGen 0) = parabolicRotor t := by
  rw [contractedGen_zero, parabolicRotor, exp_of_sq_zero parabolicGen_sq]

/-- At fixed parameter the elliptic exponential contracts to the null rotor. -/
theorem exp_contractedGen_tendsto (t : ℝ) :
    Tendsto (fun ε => exp (t • contractedGen ε)) (nhds 0) (nhds (parabolicRotor t)) := by
  have hcont : Continuous (fun ε => t • contractedGen ε) :=
    continuous_contractedGen.const_smul t
  have hgen : Tendsto (fun ε => t • contractedGen ε) (nhds 0) (nhds (t • parabolicGen)) := by
    simpa [contractedGen_zero] using hcont.tendsto 0
  have h0 : exp (t • parabolicGen) = parabolicRotor t := by
    rw [← contractedGen_zero, exp_contractedGen_zero]
  simpa [h0] using hgen.exp

theorem sinc_tendsto (t : ℝ) :
    Tendsto (fun ε => Real.sinc (ε * t)) (nhds 0) (nhds 1) := by
  have hcont : Continuous (fun ε => Real.sinc (ε * t)) :=
    Real.continuous_sinc.comp (continuous_id.mul continuous_const)
  simpa [Real.sinc_zero] using hcont.tendsto 0

theorem sinc_pi : Real.sinc Real.pi = 0 := by
  rw [Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi, zero_div]

theorem compactJacobian_eq_sinc_sq {x : ℝ} (hx : x ≠ 0) :
    compactJacobian x = Real.sinc x ^ 2 := by
  unfold compactJacobian
  rw [Real.sinc_of_ne_zero hx]
  field_simp [hx]

theorem compactJacobian_antipode : compactJacobian Real.pi = 0 := by
  rw [compactJacobian_eq_sinc_sq Real.pi_ne_zero, sinc_pi]
  norm_num

/-- Infinitesimal displacement of the null line. It vanishes only at `ε = 0`. -/
theorem lorentzAct_contracted_nullLine (ε : ℝ) :
    KillingAxis.lorentzAct (contractedParams ε) nullLineVec =
      ![0, 2 * (1 - Real.sqrt (1 + ε ^ 2)), 0, 0] := by
  funext i
  fin_cases i <;>
    simp [KillingAxis.lorentzAct, contractedParams, nullLineVec, Matrix.cons_val_zero,
      Matrix.cons_val_one];
    ring_nf

theorem commutator_contracted_nullLine (ε : ℝ) :
    Generators.commutator (contractedGen ε) (minkowskiVector nullLineVec) =
      (2 * (1 - Real.sqrt (1 + ε ^ 2))) • ι 1 := by
  rw [← omegaTorsion_contractedParams,
    KillingAxis.commutator_omegaTorsion_minkowskiVector,
    lorentzAct_contracted_nullLine, KillingAxis.minkowskiVector_vec]
  module

theorem commutator_contracted_nullLine_eq_zero_iff (ε : ℝ) :
    Generators.commutator (contractedGen ε) (minkowskiVector nullLineVec) = 0 ↔ ε = 0 := by
  rw [commutator_contracted_nullLine]
  constructor
  · intro h
    have hι : (ι 1 : PGA) ≠ 0 := by
      intro h0
      have hsq := e1_sq
      rw [h0, zero_mul] at hsq
      exact one_ne_zero hsq.symm
    have hc : 2 * (1 - Real.sqrt (1 + ε ^ 2)) = 0 :=
      (smul_eq_zero.mp h).resolve_right hι
    have hsqrt : Real.sqrt (1 + ε ^ 2) = 1 := by
      have hdiff : 1 - Real.sqrt (1 + ε ^ 2) = 0 :=
        (mul_eq_zero.mp hc).resolve_left two_ne_zero
      linarith
    have hsqε : 1 + ε ^ 2 = 1 := by
      have hnn : (0 : ℝ) ≤ 1 + ε ^ 2 := by positivity
      rw [← Real.sq_sqrt hnn, hsqrt]
      norm_num
    have : ε ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp this
  · intro hε
    simp [hε, Real.sqrt_one]

private theorem continuous_reverse : Continuous (reverse : PGA → PGA) :=
  (reverse : PGA →ₗ[ℝ] PGA).continuous_of_finiteDimensional

private theorem continuous_sandwich_left (v : PGA) :
    Continuous (fun m : PGA => sandwich m v) := by
  unfold sandwich
  exact ((continuous_mul.comp (continuous_id.prodMk continuous_const)).mul
    (continuous_reverse.comp continuous_id))

/-- The null line, read through the contracting family, stays fixed in the limit. -/
theorem sandwich_contracted_tendsto_nullLine (t : ℝ) :
    Tendsto (fun ε => sandwich (exp (t • contractedGen ε)) (ι 0 - ι 3))
      (nhds 0) (nhds (ι 0 - ι 3)) := by
  have hsand :=
    ((continuous_sandwich_left (ι 0 - ι 3)).tendsto (parabolicRotor t)).comp
      (exp_contractedGen_tendsto t)
  simp only [Function.comp_def, parabolicRotor] at hsand
  rwa [sandwich_parabolic_fixedNull t] at hsand

/-- The transverse vector is carried along the null line in the same limit. -/
theorem sandwich_contracted_tendsto_screen (t : ℝ) :
    Tendsto (fun ε => sandwich (exp (t • contractedGen ε)) (ι 1))
      (nhds 0) (nhds (ι 1 + (2 * t) • (ι 0 - ι 3))) := by
  have hsand :=
    ((continuous_sandwich_left (ι 1)).tendsto (parabolicRotor t)).comp
      (exp_contractedGen_tendsto t)
  simp only [Function.comp_def, parabolicRotor] at hsand
  rwa [sandwich_parabolic_e1_shear t] at hsand

end Gravity

end DstDiophantine
