import DstDiophantine.Gravity.SI
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vacuum-wavelength window on the SI stand-ins

The photon wavelength of an energy, and the rational stand-in that replaces
\(\pi\) by a twenty-digit bracket. A positive numerator and denominator then
carry a rational inequality between those brackets up to the real wavelength.
-/

namespace DstDiophantine

namespace Gravity

open Real SI

/-- Vacuum wavelength \(2\pi\hbar c/E\) of an energy, in metres. -/
noncomputable def vacuumWavelength (energy : ℝ) : ℝ :=
  2 * π * (hbarApprox : ℝ) * (speedOfLight : ℝ) / energy

/-- Twenty-digit lower bracket for \(\pi\). -/
def piDigitLo : ℚ := 314159265358979323846 / (10 : ℚ) ^ 20

/-- Twenty-digit upper bracket for \(\pi\). -/
def piDigitHi : ℚ := 314159265358979323847 / (10 : ℚ) ^ 20

/-- Wavelength stand-in with \(\pi\) replaced by a rational bracket `p`. -/
def standInWavelength (num den : ℕ) (p : ℚ) : ℚ :=
  (num : ℚ) * p * hbarApprox /
    ((den : ℚ) * electronMassApprox * speedOfLight * fineStructureApprox ^ 2)

private theorem piDigitLo_lt_pi : (314159265358979323846 : ℝ) / 10 ^ 20 < π := by
  have heq : (314159265358979323846 : ℝ) / 10 ^ 20 =
      (3.14159265358979323846 : ℝ) := by norm_num
  linarith [pi_gt_d20]

private theorem piDigitHi_gt_pi : π < (314159265358979323847 : ℝ) / 10 ^ 20 := by
  have heq : (314159265358979323847 : ℝ) / 10 ^ 20 =
      (3.14159265358979323847 : ℝ) := by norm_num
  linarith [pi_lt_d20]

private theorem closed_factor_pos {num den : ℕ} (hnum : 0 < num) (hden : 0 < den) :
    (0 : ℝ) < (num : ℝ) * (hbarApprox : ℝ) /
      ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
        (fineStructureApprox : ℝ) ^ 2) := by
  have hnum' : (0 : ℝ) < (num : ℝ) := by exact_mod_cast hnum
  have hden' : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hh : (0 : ℝ) < (hbarApprox : ℝ) := by exact_mod_cast hbarApprox_pos
  have hm : (0 : ℝ) < (electronMassApprox : ℝ) := by exact_mod_cast electronMassApprox_pos
  have hc : (0 : ℝ) < (speedOfLight : ℝ) := by exact_mod_cast speedOfLight_pos
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) ^ 2 := by
    exact pow_pos (by exact_mod_cast fineStructureApprox_pos) 2
  positivity

/-- A rational window on the \(\pi\)-brackets is a real window on the wavelength. -/
theorem ratioWavelength_bounds {num den : ℕ} {lo hi : ℚ}
    (hnum : 0 < num) (hden : 0 < den)
    (hlo : lo < standInWavelength num den piDigitLo)
    (hhi : standInWavelength num den piDigitHi < hi) :
    (lo : ℝ) <
        (num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) ∧
      (num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) <
        (hi : ℝ) := by
  have hfac := closed_factor_pos hnum hden
  have hloR : (lo : ℝ) <
      (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
        ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
    have hcast : (lo : ℝ) < (standInWavelength num den piDigitLo : ℝ) := by
      exact_mod_cast hlo
    have heq : (standInWavelength num den piDigitLo : ℝ) =
        (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) := by
      unfold standInWavelength piDigitLo
      push_cast
      ring
    exact lt_of_lt_of_eq hcast heq
  have hhiR :
      (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) <
        (hi : ℝ) := by
    have heq :
        (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) =
          (standInWavelength num den piDigitHi : ℝ) := by
      unfold standInWavelength piDigitHi
      push_cast
      ring
    have hcast : (standInWavelength num den piDigitHi : ℝ) < (hi : ℝ) := by
      exact_mod_cast hhi
    exact lt_of_eq_of_lt heq hcast
  constructor
  · refine lt_trans hloR ?_
    calc (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)
        = ((num : ℝ) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2)) *
            ((314159265358979323846 : ℝ) / 10 ^ 20) := by ring
      _ < ((num : ℝ) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2)) * π :=
          mul_lt_mul_of_pos_left piDigitLo_lt_pi hfac
      _ = (num : ℝ) * π * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) := by ring
  · refine lt_trans ?_ hhiR
    calc (num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)
        = ((num : ℝ) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2)) * π := by ring
      _ < ((num : ℝ) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2)) *
            ((314159265358979323847 : ℝ) / 10 ^ 20) :=
          mul_lt_mul_of_pos_left piDigitHi_gt_pi hfac
      _ = (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) := by ring

/-- The same window after multiplying by a factor bracketed around \((\rho+1)/\rho\). -/
theorem ratioFactor_bounds {num den : ℕ} {lo hi flo fhi : ℚ} {ρ : ℝ}
    (hnum : 0 < num) (hden : 0 < den)
    (hflo : (0 : ℚ) < flo) (hfhi : (0 : ℚ) < fhi)
    (hfacLo : (flo : ℝ) < (ρ + 1) / ρ)
    (hfacHi : (ρ + 1) / ρ < (fhi : ℝ))
    (hlo : lo < standInWavelength num den piDigitLo * flo)
    (hhi : standInWavelength num den piDigitHi * fhi < hi) :
    (lo : ℝ) <
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((ρ + 1) / ρ) ∧
      ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((ρ + 1) / ρ) <
        (hi : ℝ) := by
  have hfac := closed_factor_pos hnum hden
  have hpos : (0 : ℝ) < (num : ℝ) * π * (hbarApprox : ℝ) /
      ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
        (fineStructureApprox : ℝ) ^ 2) := by
    have hrew : (num : ℝ) * π * (hbarApprox : ℝ) /
        ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) =
        ((num : ℝ) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * π := by ring
    rw [hrew]
    exact mul_pos hfac pi_pos
  have hlowPos : (0 : ℝ) < (flo : ℝ) := by exact_mod_cast hflo
  have hhighPos : (0 : ℝ) < (fhi : ℝ) := by exact_mod_cast hfhi
  have hloR : (lo : ℝ) <
      (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
        ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) * (flo : ℝ) := by
    let q : ℚ := standInWavelength num den piDigitLo * flo
    have hcast : (lo : ℝ) < (q : ℝ) := by
      dsimp only [q]
      exact_mod_cast hlo
    have heq : (q : ℝ) =
        (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) * (flo : ℝ) := by
      unfold q standInWavelength piDigitLo
      push_cast
      ring
    exact lt_of_lt_of_eq hcast heq
  have hhiR :
      (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) * (fhi : ℝ) <
        (hi : ℝ) := by
    let q : ℚ := standInWavelength num den piDigitHi * fhi
    have heq :
        (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * (fhi : ℝ) =
          (q : ℝ) := by
      unfold q standInWavelength piDigitHi
      push_cast
      ring
    have hcast : (q : ℝ) < (hi : ℝ) := by
      dsimp only [q]
      exact_mod_cast hhi
    exact lt_of_eq_of_lt heq hcast
  constructor
  · have hendpoint : (lo : ℝ) <
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * (flo : ℝ) := by
      refine lt_trans hloR ?_
      calc (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * (flo : ℝ)
          = ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((314159265358979323846 : ℝ) / 10 ^ 20) * (flo : ℝ) := by ring
        _ < ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π * (flo : ℝ) := by
            have hmul := mul_lt_mul_of_pos_left piDigitLo_lt_pi hfac
            exact mul_lt_mul_of_pos_right hmul hlowPos
        _ = (num : ℝ) * π * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) * (flo : ℝ) := by ring
    exact lt_of_lt_of_le hendpoint (mul_le_mul_of_nonneg_left hfacLo.le hpos.le)
  · have hendpoint :
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * (fhi : ℝ) <
          (hi : ℝ) := by
      refine lt_trans ?_ hhiR
      calc (num : ℝ) * π * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * (fhi : ℝ)
          = ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π * (fhi : ℝ) := by ring
        _ < ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((314159265358979323847 : ℝ) / 10 ^ 20) * (fhi : ℝ) := by
            have hmul := mul_lt_mul_of_pos_left piDigitHi_gt_pi hfac
            exact mul_lt_mul_of_pos_right hmul hhighPos
        _ = (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) * (fhi : ℝ) := by ring
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hfacHi.le hpos.le) hendpoint

end Gravity

end DstDiophantine
