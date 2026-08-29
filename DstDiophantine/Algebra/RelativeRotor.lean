import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Sandwich
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Relative rotor and same-axis factorisation

The paper writes a six-parameter exponential as `R_usual R_dual` and takes
the vacuum condition to be `R_dual = R_usual†`, yielding `Ω = 1`. Both
claims need the algebra of `G(3,1,1)`.

## Proved

* Same-axis generators commute, so a *one-axis* exponential factorises.
* Distinct-axis generators need not commute, so the unrestricted
  six-parameter factorisation is not justified by same-axis commutators.
* Defining `Ω = R_usual† R_dual`, one has `Ω = 1` if and only if
  `R_dual = R_usual` (unitarity), not `R_dual = R_usual†`.
* On a single axis the written condition `R_dual = R_usual†` forces the
  usual half-rapidity through `sinh(α/2) = 0`.
* `J = 0` does not imply `Ω = 1`: a balanced massive one-axis seed has
  vanishing `J` with a nontrivial relative rotor.

## Not claimed

* `exp(ω_usual + ω_dual) = exp(ω_usual) exp(ω_dual)` for a general
  three-axis configuration.
-/

namespace DstDiophantine

open CliffordAlgebra PGA Generators Operations Motor Amplification Invariant
open NormedSpace

namespace RelativeRotor

/-! ### Usual / dual generators and rotors -/

/-- Usual-sector bivector `∑ (αₐ/2) B⁺ₐ`. -/
noncomputable def omegaUsual (p : TorsionParams) : PGA :=
  ∑ a : Fin 3, (p.alpha a / 2) • hyperbolic a

/-- Dual-sector bivector `∑ (βₐ/2) B⁻ₐ`. -/
noncomputable def omegaDual (p : TorsionParams) : PGA :=
  ∑ a : Fin 3, (p.beta a / 2) • cyclic a

theorem omegaTorsion_eq_add (p : TorsionParams) :
    omegaTorsion p = omegaUsual p + omegaDual p := by
  simp only [omegaTorsion, omegaUsual, omegaDual, ← Finset.sum_add_distrib]

theorem omegaUsual_reverse (p : TorsionParams) :
    reverse (omegaUsual p) = -omegaUsual p := by
  simp only [omegaUsual, map_sum, map_smul, hyperbolic_reverse]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext a
  simp [smul_neg]

theorem omegaDual_reverse (p : TorsionParams) :
    reverse (omegaDual p) = -omegaDual p := by
  simp only [omegaDual, map_sum, map_smul, cyclic_reverse]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext a
  simp [smul_neg]

/-- Usual rotor `R_usual = exp(Ω_usual)`. -/
noncomputable def rotorUsual (p : TorsionParams) : PGA :=
  exp (omegaUsual p)

/-- Dual rotor `R_dual = exp(Ω_dual)`. -/
noncomputable def rotorDual (p : TorsionParams) : PGA :=
  exp (omegaDual p)

/-- Relative mismatch rotor `Ω = R_usual† R_dual`. -/
noncomputable def relativeRotor (p : TorsionParams) : PGA :=
  reverse (rotorUsual p) * rotorDual p

theorem rotorUsual_unitary (p : TorsionParams) :
    rotorUsual p * reverse (rotorUsual p) = 1 := by
  dsimp [rotorUsual]
  rw [reverse_exp_of_reverse_neg (omegaUsual_reverse p)]
  rw [← exp_add_of_commute (Commute.neg_right (Commute.refl (omegaUsual p)))]
  simp

theorem rotorDual_unitary (p : TorsionParams) :
    rotorDual p * reverse (rotorDual p) = 1 := by
  dsimp [rotorDual]
  rw [reverse_exp_of_reverse_neg (omegaDual_reverse p)]
  rw [← exp_add_of_commute (Commute.neg_right (Commute.refl (omegaDual p)))]
  simp

/-- `Ω = 1` if and only if the two rotors coincide. -/
theorem relativeRotor_eq_one_iff (p : TorsionParams) :
    relativeRotor p = 1 ↔ rotorDual p = rotorUsual p := by
  constructor
  · intro h
    have hmul := congrArg (fun z : PGA => rotorUsual p * z) h
    simp only [relativeRotor, mul_one, ← mul_assoc, rotorUsual_unitary, one_mul] at hmul
    exact hmul
  · intro h
    rw [relativeRotor, h]
    exact reverse_mul_of_mul_reverse (rotorUsual_unitary p)

/-! ### Same-axis commutators and one-axis factorisation -/

theorem commute_hyperbolic_cyclic_same (a : Fin 3) :
    Commute (hyperbolic a) (cyclic a) :=
  sub_eq_zero.mp (commutator_hyperbolic_cyclic_same a)

/-- One-axis mixed configuration: boost and dual rotation on axis `0`. -/
def axisParams (α β : ℝ) : TorsionParams where
  alpha := fun a => if a = 0 then α else 0
  beta := fun a => if a = 0 then β else 0

theorem omegaUsual_axisParams (α β : ℝ) :
    omegaUsual (axisParams α β) = (α / 2) • hyperbolic 0 := by
  simp [omegaUsual, axisParams, Fin.sum_univ_three]

theorem omegaDual_axisParams (α β : ℝ) :
    omegaDual (axisParams α β) = (β / 2) • cyclic 0 := by
  simp [omegaDual, axisParams, Fin.sum_univ_three]

theorem omegaTorsion_axisParams (α β : ℝ) :
    omegaTorsion (axisParams α β) =
      (α / 2) • hyperbolic 0 + (β / 2) • cyclic 0 := by
  rw [omegaTorsion_eq_add, omegaUsual_axisParams, omegaDual_axisParams]

theorem commute_omegaUsual_omegaDual_axis (α β : ℝ) :
    Commute (omegaUsual (axisParams α β)) (omegaDual (axisParams α β)) := by
  rw [omegaUsual_axisParams, omegaDual_axisParams]
  exact ((commute_hyperbolic_cyclic_same 0).smul_left (α / 2)).smul_right (β / 2)

/-- On a single axis the combined exponential factorises. -/
theorem rotorTorsion_axis_factor (α β : ℝ) :
    rotorTorsion (axisParams α β) =
      rotorUsual (axisParams α β) * rotorDual (axisParams α β) := by
  rw [rotorTorsion, rotorUsual, rotorDual, omegaTorsion_eq_add]
  exact exp_add_of_commute (commute_omegaUsual_omegaDual_axis α β)

theorem rotorUsual_axis_closed (α β : ℝ) :
    rotorUsual (axisParams α β) =
      Real.cosh (α / 2) • (1 : PGA) + Real.sinh (α / 2) • hyperbolic 0 := by
  rw [rotorUsual, omegaUsual_axisParams, exp_of_sq_one (hyperbolic_sq 0)]

theorem rotorDual_axis_closed (α β : ℝ) :
    rotorDual (axisParams α β) =
      Real.cos (β / 2) • (1 : PGA) + Real.sin (β / 2) • cyclic 0 := by
  rw [rotorDual, omegaDual_axisParams, exp_of_sq_neg_one (cyclic_sq 0)]

theorem reverse_rotorUsual_axis (α β : ℝ) :
    reverse (rotorUsual (axisParams α β)) =
      Real.cosh (α / 2) • (1 : PGA) - Real.sinh (α / 2) • hyperbolic 0 := by
  rw [rotorUsual_axis_closed, map_add, map_smul, map_smul, reverse.map_one,
    hyperbolic_reverse, smul_neg]
  abel

/-- The paper's unrestricted commutator `[iΓ_a, Γ_b] = 0` fails off-axis. -/
theorem paper_unrestricted_commutator_false :
    commutator (hyperbolic 0) (cyclic 1) ≠ 0 :=
  commutator_hyperbolic0_cyclic1_ne_zero

/-! ### Linear independence of same-axis generators -/

private theorem smul_mul_smul (c d : ℝ) (x y : PGA) :
    (c • x) * (d • y) = (c * d) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem cyclic_ne_smul_hyperbolic (a : Fin 3) (c : ℝ) :
    cyclic a ≠ c • hyperbolic a := by
  intro h
  have hsq : cyclic a * cyclic a = (c • hyperbolic a) * (c • hyperbolic a) :=
    congrArg (fun z : PGA => z * z) h
  have hR : (c • hyperbolic a) * (c • hyperbolic a) = (c * c) • (1 : PGA) := by
    rw [smul_mul_smul, hyperbolic_sq a]
  have hPGA : (-1 : PGA) = (c * c) • (1 : PGA) := by
    rw [← cyclic_sq a, hsq, hR]
  have hmap : algebraMap ℝ PGA (-1) = algebraMap ℝ PGA (c * c) := by
    simpa [Algebra.smul_def, map_neg, map_one] using hPGA
  have hc : (-1 : ℝ) = c * c :=
    FaithfulSMul.algebraMap_injective (R := ℝ) (A := PGA) hmap
  nlinarith [sq_nonneg c]

theorem hyperbolic0_ne_zero : hyperbolic 0 ≠ 0 := by
  intro h
  have : (1 : PGA) = 0 := by rw [← hyperbolic_sq 0, h, mul_zero]
  have hR : (1 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hR

/-- If `sD • B⁻ + sU • B⁺` vanishes, both coefficients vanish. -/
private theorem axis_bivector_span_eq_zero {sD sU : ℝ}
    (h : sD • cyclic 0 + sU • hyperbolic 0 = 0) :
    sD = 0 ∧ sU = 0 := by
  have heq : sD • cyclic 0 = -(sU • hyperbolic 0) :=
    eq_neg_of_add_eq_zero_left h
  by_cases hsD : sD = 0
  · refine ⟨hsD, ?_⟩
    have : sU • hyperbolic 0 = 0 := by
      have h' := heq
      simp only [hsD, zero_smul, zero_eq_neg] at h'
      exact h'
    exact (smul_eq_zero.mp this).resolve_right hyperbolic0_ne_zero
  · have hscal : cyclic 0 = ((-sU) / sD) • hyperbolic 0 := by
      have hcongr := congrArg (fun z : PGA => sD⁻¹ • z) heq
      have hL : sD⁻¹ • (sD • cyclic 0) = cyclic 0 := by
        simp [smul_smul, inv_mul_cancel₀ hsD]
      have hR : sD⁻¹ • -(sU • hyperbolic 0) = ((-sU) / sD) • hyperbolic 0 := by
        simp [smul_neg, smul_smul, div_eq_inv_mul, mul_comm]
      calc
        cyclic 0 = sD⁻¹ • (sD • cyclic 0) := hL.symm
        _ = sD⁻¹ • -(sU • hyperbolic 0) := hcongr
        _ = ((-sU) / sD) • hyperbolic 0 := hR
    exact (cyclic_ne_smul_hyperbolic 0 ((-sU) / sD) hscal).elim

/-- Compare a dual closed form with a usual closed form (either sign of the boost). -/
private theorem closed_forms_bivector
    {cD sD cU sU : ℝ}
    (h : cD • (1 : PGA) + sD • cyclic 0 = cU • (1 : PGA) + sU • hyperbolic 0) :
    sD = 0 ∧ sU = 0 := by
  have hsum :
      (cD - cU) • (1 : PGA) + sD • cyclic 0 + (-sU) • hyperbolic 0 = 0 := by
    have hsub :
        (cD • (1 : PGA) + sD • cyclic 0) -
          (cU • (1 : PGA) + sU • hyperbolic 0) = 0 :=
      sub_eq_zero.mpr h
    convert hsub using 1
    module
  have hexp :
      reverse ((cD - cU) • (1 : PGA) + sD • cyclic 0 + (-sU) • hyperbolic 0) =
        (cD - cU) • (1 : PGA) + sD • (-cyclic 0) +
          (-sU) • (-hyperbolic 0) := by
    simp [map_add, map_smul, reverse.map_one, cyclic_reverse, hyperbolic_reverse]
  have hrev' :
      (cD - cU) • (1 : PGA) + (-sD) • cyclic 0 + sU • hyperbolic 0 = 0 := by
    have : reverse
        ((cD - cU) • (1 : PGA) + sD • cyclic 0 + (-sU) • hyperbolic 0) = 0 := by
      rw [hsum, map_zero]
    rw [hexp] at this
    convert this using 1
    module
  have hsub := congrArg₂ (· - ·) hsum hrev'
  have hbiv : (2 : ℝ) • (sD • cyclic 0 + (-sU) • hyperbolic 0) = 0 := by
    convert hsub using 1
    · module
    · simp
  have hcomb : sD • cyclic 0 + (-sU) • hyperbolic 0 = 0 :=
    (smul_eq_zero.mp hbiv).resolve_left (by norm_num)
  have hb := axis_bivector_span_eq_zero hcomb
  exact ⟨hb.1, by simpa using hb.2⟩

/-! ### Paper vacuum condition `R_dual = R_usual†` -/

/-- Written vacuum synchronisation `R_dual = R_usual†`. -/
def PaperVacuumSync (p : TorsionParams) : Prop :=
  rotorDual p = reverse (rotorUsual p)

theorem relativeRotor_of_paperVacuumSync {p : TorsionParams}
    (h : PaperVacuumSync p) :
    relativeRotor p = reverse (rotorUsual p) * reverse (rotorUsual p) := by
  simp only [relativeRotor, PaperVacuumSync] at h ⊢
  rw [h]

/-- Under the written condition, `Ω = 1` holds iff `(R_usual†)² = 1`. -/
theorem relativeRotor_eq_one_of_paperVacuumSync {p : TorsionParams}
    (h : PaperVacuumSync p) :
    relativeRotor p = 1 ↔ reverse (rotorUsual p) * reverse (rotorUsual p) = 1 := by
  rw [relativeRotor_of_paperVacuumSync h]

/-- On one axis, `R_dual = R_usual†` forces both bivector coefficients to vanish. -/
theorem paperVacuumSync_axis {α β : ℝ}
    (h : PaperVacuumSync (axisParams α β)) :
    Real.sinh (α / 2) = 0 ∧ Real.sin (β / 2) = 0 := by
  unfold PaperVacuumSync at h
  rw [rotorDual_axis_closed, reverse_rotorUsual_axis] at h
  have h' :
      Real.cos (β / 2) • (1 : PGA) + Real.sin (β / 2) • cyclic 0 =
        Real.cosh (α / 2) • (1 : PGA) + (-Real.sinh (α / 2)) • hyperbolic 0 := by
    simpa [sub_eq_add_neg, smul_neg] using h
  have hb := closed_forms_bivector h'
  exact ⟨by simpa using hb.2, hb.1⟩

theorem axisParams_pureBoost (φ : ℝ) : axisParams φ 0 = pureBoost φ := by
  dsimp [axisParams, pureBoost]
  congr <;> funext a <;> fin_cases a <;> simp

/-- A nontrivial one-axis boost does not satisfy the written vacuum condition. -/
theorem not_paperVacuumSync_pureBoost {φ : ℝ} (hφ : Real.sinh (φ / 2) ≠ 0) :
    ¬ PaperVacuumSync (pureBoost φ) := by
  intro h
  have h' : PaperVacuumSync (axisParams φ 0) := by rwa [axisParams_pureBoost]
  exact hφ (paperVacuumSync_axis h').1

/-! ### `J = 0` versus `Ω = 1` -/

theorem J_axisParams (α β : ℝ) :
    J (axisParams α β) = (1 / 2) * (α ^ 2 - β ^ 2) := by
  rw [J_coef]
  simp [axisParams]

theorem mass_axisParams (α β : ℝ) :
    mass (axisParams α β) = (1 / 2) * (α ^ 2 + β ^ 2) := by
  rw [mass_coef]
  simp [axisParams, Fin.sum_univ_three]

theorem J_axisParams_balanced (t : ℝ) : J (axisParams t t) = 0 := by
  rw [J_axisParams]; ring

theorem mass_axisParams_balanced {t : ℝ} (ht : t ≠ 0) :
    0 < mass (axisParams t t) := by
  rw [mass_axisParams]
  nlinarith [sq_pos_of_ne_zero ht]

/-- Balanced one-axis rotors coincide only if the hyperbolic coefficient vanishes. -/
theorem balanced_axis_rotors_ne {t : ℝ} (ht : Real.sinh (t / 2) ≠ 0) :
    rotorDual (axisParams t t) ≠ rotorUsual (axisParams t t) := by
  intro h
  have heq :
      Real.cos (t / 2) • (1 : PGA) + Real.sin (t / 2) • cyclic 0 =
        Real.cosh (t / 2) • (1 : PGA) + Real.sinh (t / 2) • hyperbolic 0 := by
    simpa [rotorDual_axis_closed, rotorUsual_axis_closed] using h
  exact ht (closed_forms_bivector heq).2

/-- `J = 0` does not force the relative rotor to be the identity. -/
theorem J_zero_not_relativeRotor_one :
    ∃ p : TorsionParams, J p = 0 ∧ 0 < mass p ∧ relativeRotor p ≠ 1 := by
  refine ⟨axisParams 1 1, J_axisParams_balanced 1, mass_axisParams_balanced (by norm_num), ?_⟩
  intro h
  have hrot := (relativeRotor_eq_one_iff _).mp h
  have hs : Real.sinh ((1 : ℝ) / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).ne'
  exact balanced_axis_rotors_ne hs hrot

end RelativeRotor

end DstDiophantine
