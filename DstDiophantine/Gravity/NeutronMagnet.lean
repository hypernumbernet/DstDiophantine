import DstDiophantine.Gravity.ChiralityStabilizer
import DstDiophantine.Gravity.EMControl

/-!
# Neutron spin and the charge-silent magnet

## Paper boundary (do **not** claim)

The ratio \(\mu_n/\mu_p=-2/3\), the weights \(4/3\) and \(-1/3\), a moment in
nuclear magnetons, \(g_A/g_V\), and a V--A coupling are **not** derived.
The electromagnetic label is not a Faraday coefficient.

## What is proved

* On \(J=0\) the magnetic square equals the electric square, and both equal
  the unsigned mass. A positive mass on that locus is therefore magnetic.
  Vanishing dual angles on the locus force the mass to vanish. Each square
  contributes half the mass.
* The substitution \(\theta\mapsto\theta+eA\) with \(e=0\) is the identity.
  The dual rotor depends on the dual angles alone.
* A dual phase \(2\pi\) supported on one axis sends that rotor to \(-1\).
  A dual phase \(4\pi\) restores the identity. The parallel magnetic
  generator is a rotor and is the unique direction in its plane with the
  parallel electric generator that preserves the axis.
* At rest the dual Faraday summand gives no sandwich kick. The same
  generator kicks a moving frame.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations RelativeRotor Invariant Motor NormedSpace
open scoped Real

/-! ### Balance forces a magnet -/

theorem magneticSq_eq_energySq_of_balanced {p : FaradayParams}
    (hJ : J (toTorsion p) = 0) :
    magneticSq p = energySq p := by
  have h : (1 / 2) * (energySq p - magneticSq p) = 0 := by
    rw [← J_faraday, hJ]
  have hsub : energySq p - magneticSq p = 0 :=
    (mul_eq_zero.mp h).resolve_left (by norm_num)
  linarith

theorem mass_eq_magneticSq_of_balanced {p : FaradayParams}
    (hJ : J (toTorsion p) = 0) :
    mass (toTorsion p) = magneticSq p := by
  rw [mass_faraday, magneticSq_eq_energySq_of_balanced hJ]
  ring

theorem mass_eq_energySq_of_balanced {p : FaradayParams}
    (hJ : J (toTorsion p) = 0) :
    mass (toTorsion p) = energySq p := by
  rw [mass_eq_magneticSq_of_balanced hJ, magneticSq_eq_energySq_of_balanced hJ]

/-- Each square contributes half the unsigned mass on the balanced locus. -/
theorem balanced_shares {p : FaradayParams} (hJ : J (toTorsion p) = 0) :
    (1 / 2) * magneticSq p = mass (toTorsion p) / 2 ∧
      (1 / 2) * energySq p = mass (toTorsion p) / 2 := by
  have hM := mass_eq_magneticSq_of_balanced hJ
  have hE := mass_eq_energySq_of_balanced hJ
  constructor <;> linarith

theorem magneticSq_pos_of_balanced {p : FaradayParams}
    (hJ : J (toTorsion p) = 0) (hM : 0 < mass (toTorsion p)) :
    0 < magneticSq p := by
  rw [← mass_eq_magneticSq_of_balanced hJ]
  exact hM

/-- A balanced configuration with every dual angle silent has no mass. -/
theorem mass_zero_of_balanced_silent {p : TorsionParams}
    (hJ : J p = 0) (hβ : ∀ a, p.beta a = 0) :
    mass p = 0 := by
  rw [mass_eq_zero_iff]
  intro a
  have hprod : (1 / 2) * ∑ b : Fin 3, (p.alpha b ^ 2 - p.beta b ^ 2) = 0 := by
    rw [← J_coef, hJ]
  have hsum : ∑ b : Fin 3, (p.alpha b ^ 2 - p.beta b ^ 2) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (by norm_num)
  have hnn : ∀ b ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ p.alpha b ^ 2 - p.beta b ^ 2 := by
    intro b _
    simp [hβ b, sq_nonneg]
  have hterm : p.alpha a ^ 2 - p.beta a ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum a (Finset.mem_univ a)
  have hα : p.alpha a = 0 := by
    have : p.alpha a ^ 2 = 0 := by simpa [hβ a] using hterm
    exact sq_eq_zero_iff.mp this
  exact ⟨hα, hβ a⟩

/-! ### A silent charge does not move the magnet -/

theorem coupleA_zero_label (p : TorsionParams) (A : Fin 3 → ℝ) :
    coupleA p 0 A = p := by
  refine torsionParams_ext ?_ ?_
  · funext a
    simp
  · funext a
    simp

theorem rotorDual_eq_of_beta_eq {p q : TorsionParams} (h : p.beta = q.beta) :
    rotorDual p = rotorDual q := by
  simp [rotorDual, omegaDual, h]

/-! ### Half-angle spin of one axis -/

theorem exp_cyclic_pi (a : Fin 3) :
    exp (Real.pi • cyclic a) = -1 := by
  rw [exp_of_sq_neg_one (cyclic_sq a), Real.cos_pi, Real.sin_pi]
  simp

theorem exp_cyclic_two_pi (a : Fin 3) :
    exp ((2 * Real.pi) • cyclic a) = 1 := by
  rw [exp_of_sq_neg_one (cyclic_sq a), Real.cos_two_pi, Real.sin_two_pi]
  simp

theorem omegaDual_single_axis (a : Fin 3) (β : ℝ) (p : TorsionParams)
    (h : ∀ b, p.beta b = if b = a then β else 0) :
    omegaDual p = (β / 2) • cyclic a := by
  unfold omegaDual
  fin_cases a
  · have h0 : p.beta 0 = β := by simpa using h 0
    have h1 : p.beta 1 = 0 := by simpa using h 1
    have h2 : p.beta 2 = 0 := by simpa using h 2
    simp [Fin.sum_univ_three, h0, h1, h2]
  · have h0 : p.beta 0 = 0 := by simpa using h 0
    have h1 : p.beta 1 = β := by simpa using h 1
    have h2 : p.beta 2 = 0 := by simpa using h 2
    simp [Fin.sum_univ_three, h0, h1, h2]
  · have h0 : p.beta 0 = 0 := by simpa using h 0
    have h1 : p.beta 1 = 0 := by simpa using h 1
    have h2 : p.beta 2 = β := by simpa using h 2
    simp [Fin.sum_univ_three, h0, h1, h2]

/-- A dual phase \(2\pi\) on one axis sends the dual rotor to \(-1\). -/
theorem rotorDual_single_axis_two_pi (a : Fin 3) (p : TorsionParams)
    (h : ∀ b, p.beta b = if b = a then 2 * Real.pi else 0) :
    rotorDual p = -1 := by
  rw [rotorDual, omegaDual_single_axis a (2 * Real.pi) p h]
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [hhalf]
  exact exp_cyclic_pi a

/-- A dual phase \(4\pi\) on one axis restores the identity. -/
theorem rotorDual_single_axis_four_pi (a : Fin 3) (p : TorsionParams)
    (h : ∀ b, p.beta b = if b = a then 4 * Real.pi else 0) :
    rotorDual p = 1 := by
  rw [rotorDual, omegaDual_single_axis a (4 * Real.pi) p h]
  have hhalf : (4 * Real.pi) / 2 = 2 * Real.pi := by ring
  rw [hhalf]
  exact exp_cyclic_two_pi a

theorem parallel_magnet_is_rotor (a : Fin 3) :
    cyclic a * CliffordAlgebra.reverse (cyclic a) = 1 :=
  cyclic_is_rotor a

theorem parallel_electric_not_rotor (a : Fin 3) :
    hyperbolic a * CliffordAlgebra.reverse (hyperbolic a) = -1 :=
  hyperbolic_reverse_mul a

theorem axis_held_iff_electric_coeff_zero (a : Fin 3) (cB cE : ℝ) :
    Commute (spatialGen a) (cB • cyclic a + cE • hyperbolic a) ↔ cE = 0 :=
  commute_neutral_axis_iff a cB cE

/-! ### The magnet does not push a body at rest -/

theorem magnet_rest_kick (p : FaradayParams) :
    sandwichIncrement (faradayDual p) (ι 0) = 0 :=
  sandwichIncrement_rest_faradayDual p

theorem magnet_moving_kick :
    sandwichIncrement (cyclic 0) (ι 2) ≠ 0 :=
  sandwichIncrement_moving_pureB_ne_zero

theorem electric_rest_kick :
    sandwichIncrement (hyperbolic 0) (ι 0) ≠ 0 := by
  rw [sandwichIncrement_rest_pureE]
  intro h
  have hι : ι 1 = 0 :=
    (smul_eq_zero.mp h).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  exact spatialGen_ne_zero 0 (by simpa [spatialGen] using hι)

end Gravity

end DstDiophantine
