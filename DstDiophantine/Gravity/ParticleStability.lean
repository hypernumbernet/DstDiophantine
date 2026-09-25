import DstDiophantine.Gravity.DualControl
import DstDiophantine.Gravity.DualRotorFlow
import DstDiophantine.Gravity.NewtonFromLight
import DstDiophantine.Gravity.SI
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false

/-!
# Stability of the proton and the electron

Kinematic protection of a balanced massive seed, together with the
external SI comparisons that say the structures around these particles
cannot pay their rest energies.

## What is proved

* Usual-only motion cannot reach the vacuum from a positive dual budget.
  On a balanced massive seed both budgets equal the unsigned mass, so
  neither channel alone reaches the vacuum, and a vacuum image must
  move both.
* The written one-axis flow with vanishing mismatch, mismatch rate, and
  common velocity keeps both angles fixed. A nonzero mismatch rate
  leaves that value.
* On the SI stand-ins, \(1836 < m_p/m_e < 1837\). One hundred times the
  empirical binding per nucleon, and twenty optical wells, each lie
  below the proton rest energy. Hydrogen ionisation is exactly
  \(\alpha^2/2\) of the electron rest energy, and that fraction lies in
  \((2,3)\times 10^{-5}\). Equivalently the rest energy is between
  \(3\times 10^4\) and \(5\times 10^4\) hydrogen ionisations. The
  gravitational heights satisfy
  \(N_*^2(m_e)/N_*^2(m_p) > 3\times 10^6\).

## Not claimed

No lifetime, no baryon-number selection rule, and no derivation of
\(m_p\) or \(m_e\). The mass ratio and the two payment comparisons use
external CODATA-style inputs.
-/

namespace DstDiophantine

namespace Gravity

open Operations Invariant Admissible SI

/-! ### Single-channel obstruction -/

theorem usual_only_not_vacuum_of_dual_pos {p q : TorsionParams}
    (hβ : q.beta = p.beta)
    (hD : ∑ a : Fin 3, p.beta a ^ 2 ≠ 0)
    (hM : mass q = 0) : False := by
  rw [← hβ] at hD
  exact hD <| Finset.sum_eq_zero fun a _ => by
    simp [((mass_eq_zero_iff q).mp hM a).2]

/-- On the balanced locus each rapidity budget equals the unsigned mass. -/
theorem balanced_budgets_eq_mass {p : TorsionParams} (hJ : J p = 0) :
    ∑ a : Fin 3, p.alpha a ^ 2 = mass p ∧
      ∑ a : Fin 3, p.beta a ^ 2 = mass p := by
  constructor
  · have := J_add_mass p
    linarith
  · have := mass_sub_J p
    linarith

theorem balanced_massive_not_dual_only_vacuum {p q : TorsionParams}
    (hJ : J p = 0) (hM : 0 < mass p) (hα : q.alpha = p.alpha)
    (hq : mass q = 0) : False := by
  have hU : ∑ a : Fin 3, p.alpha a ^ 2 ≠ 0 := by
    have := (balanced_budgets_eq_mass hJ).1
    linarith
  exact dual_only_not_vacuum_of_usual_pos hα hU hq

theorem balanced_massive_not_usual_only_vacuum {p q : TorsionParams}
    (hJ : J p = 0) (hM : 0 < mass p) (hβ : q.beta = p.beta)
    (hq : mass q = 0) : False := by
  have hD : ∑ a : Fin 3, p.beta a ^ 2 ≠ 0 := by
    have := (balanced_budgets_eq_mass hJ).2
    linarith
  exact usual_only_not_vacuum_of_dual_pos hβ hD hq

/-- Reaching the vacuum from a balanced massive seed moves both budgets. -/
theorem vacuum_moves_both_budgets {p q : TorsionParams}
    (hJ : J p = 0) (hM : 0 < mass p) (hq : mass q = 0) :
    q.alpha ≠ p.alpha ∧ q.beta ≠ p.beta := by
  constructor
  · intro hα
    exact balanced_massive_not_dual_only_vacuum hJ hM hα hq
  · intro hβ
    exact balanced_massive_not_usual_only_vacuum hJ hM hβ hq

/-! ### Written rest point -/

theorem written_frozen_balance_fixed (σ₀ m t : ℝ) :
    writtenDelta 0 0 t = 0 ∧
      writtenSigma σ₀ 0 m 0 0 t = σ₀ ∧
        writtenUsual σ₀ 0 m 0 0 t = σ₀ / 2 ∧
          writtenDual σ₀ 0 m 0 0 t = σ₀ / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [writtenDelta, affineMismatch]
  · simp [writtenSigma, cubicRapidity]
  · simp [writtenUsual, usualFrom, writtenSigma, writtenDelta, affineMismatch, cubicRapidity]
  · simp [writtenDual, dualFrom, writtenSigma, writtenDelta, affineMismatch, cubicRapidity]

theorem written_mismatch_rate_leaves {ν t : ℝ} (hν : ν ≠ 0) (ht : t ≠ 0) :
    writtenDelta 0 ν t ≠ writtenDelta 0 ν 0 := by
  simp [writtenDelta, affineMismatch, hν, ht]

/-! ### Rest-energy comparisons (external SI stand-ins) -/

def protonElectronMassRatio : ℚ := protonMassApprox / electronMassApprox

def protonElectronMassRatio_num : ℕ :=
  protonMassMantissa * 10 ^ electronMassScale

def protonElectronMassRatio_den : ℕ :=
  electronMassMantissa * 10 ^ protonMassScale

theorem protonElectronMassRatio_eq_num_div_den :
    protonElectronMassRatio =
      (protonElectronMassRatio_num : ℚ) / protonElectronMassRatio_den := by
  unfold protonElectronMassRatio protonMassApprox electronMassApprox
    protonElectronMassRatio_num protonElectronMassRatio_den
  simp only [Nat.cast_mul, Nat.cast_pow]
  field_simp
  ring

private theorem protonElectronMassRatio_den_pos :
    (0 : ℚ) < (protonElectronMassRatio_den : ℚ) := by
  unfold protonElectronMassRatio_den electronMassMantissa protonMassScale
  norm_num

theorem protonElectronMassRatio_bounds :
    (1836 : ℚ) < protonElectronMassRatio ∧
      protonElectronMassRatio < (1837 : ℚ) := by
  rw [protonElectronMassRatio_eq_num_div_den]
  have hden := protonElectronMassRatio_den_pos
  constructor
  · have hnat : 1836 * protonElectronMassRatio_den <
        protonElectronMassRatio_num := by
      unfold protonElectronMassRatio_num protonElectronMassRatio_den
        protonMassMantissa electronMassScale electronMassMantissa protonMassScale
      native_decide
    rw [lt_div_iff₀ hden]
    exact_mod_cast hnat
  · have hnat : protonElectronMassRatio_num <
        1837 * protonElectronMassRatio_den := by
      unfold protonElectronMassRatio_num protonElectronMassRatio_den
        protonMassMantissa electronMassScale electronMassMantissa protonMassScale
      native_decide
    rw [div_lt_iff₀ hden]
    exact_mod_cast hnat

theorem proton_rest_exceeds_hundred_bindings :
    (100 : ℚ) * bindingEnergyPerNucleonMeVApprox < protonMassMeVApprox := by
  unfold bindingEnergyPerNucleonMeVApprox protonMassMeVApprox
    bindingEnergyPerNucleonMeVMantissa bindingEnergyPerNucleonMeVScale
    protonMassMeVMantissa protonMassMeVScale
  norm_num

theorem proton_rest_exceeds_twenty_wells :
    (20 : ℚ) * nuclearWellDepthMeVApprox < protonMassMeVApprox := by
  unfold nuclearWellDepthMeVApprox protonMassMeVApprox
    protonMassMeVMantissa protonMassMeVScale
  norm_num

theorem hydrogen_ionisation_frac :
    hydrogenIonisationApprox /
        (electronMassApprox * speedOfLight ^ 2) =
      fineStructureApprox ^ 2 / 2 := by
  unfold hydrogenIonisationApprox
  field_simp [electronMassApprox_pos.ne', speedOfLight_pos.ne']

theorem hydrogen_ionisation_frac_bounds :
    (2 : ℚ) / 10 ^ 5 < fineStructureApprox ^ 2 / 2 ∧
      fineStructureApprox ^ 2 / 2 < (3 : ℚ) / 10 ^ 5 := by
  unfold fineStructureApprox fineStructureMantissa fineStructureScale
  norm_num

/-- Rest energy measured in hydrogen ionisations: \(3\times 10^4<2/\alpha^2<5\times 10^4\). -/
theorem hydrogen_ionisations_per_rest_bounds :
    (3 : ℚ) * 10 ^ 4 < 2 / fineStructureApprox ^ 2 ∧
      2 / fineStructureApprox ^ 2 < (5 : ℚ) * 10 ^ 4 := by
  have h := hydrogen_ionisation_frac_bounds
  have hpos : (0 : ℚ) < fineStructureApprox ^ 2 / 2 := lt_trans (by norm_num) h.1
  have hinv_hi : (10 : ℚ) ^ 5 / 3 < 2 / fineStructureApprox ^ 2 := by
    have hrec := one_div_lt_one_div_of_lt hpos h.2
    simpa [one_div_div] using hrec
  have hinv_lo : 2 / fineStructureApprox ^ 2 < (10 : ℚ) ^ 5 / 2 := by
    have hrec := one_div_lt_one_div_of_lt (by norm_num : (0 : ℚ) < (2 : ℚ) / 10 ^ 5) h.1
    simpa [one_div_div] using hrec
  refine ⟨lt_trans (by norm_num) hinv_hi, ?_⟩
  exact lt_of_lt_of_eq hinv_lo (by norm_num)

theorem gravitational_height_electron_over_proton :
    (3 : ℚ) * 10 ^ 6 <
      impliedNsq electronMassApprox / impliedNsq protonMassApprox := by
  have he := impliedNsq_electron_bounds.1
  have hp_hi := impliedNsq_proton_bounds.2
  have hp_lo := impliedNsq_proton_bounds.1
  have hp_pos : (0 : ℚ) < impliedNsq protonMassApprox :=
    lt_trans (by norm_num) hp_lo
  have hfloor : (3 : ℚ) * 10 ^ 6 <
      impliedNsq electronMassApprox / (10 : ℚ) ^ 39 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℚ) < (10 : ℚ) ^ 39)]
    have : (3 : ℚ) * 10 ^ 6 * (10 : ℚ) ^ 39 = (3 : ℚ) * 10 ^ 45 := by norm_num
    linarith
  have he_pos : (0 : ℚ) < impliedNsq electronMassApprox :=
    lt_trans (by norm_num) he
  have hcomp : impliedNsq electronMassApprox / (10 : ℚ) ^ 39 <
      impliedNsq electronMassApprox / impliedNsq protonMassApprox := by
    exact div_lt_div_of_pos_left he_pos hp_pos hp_hi
  exact lt_trans hfloor hcomp

end Gravity

end DstDiophantine
