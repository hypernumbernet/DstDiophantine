import DstDiophantine.Gravity.HydrogenAlpha
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Representative lines on the outer plateau

## Paper boundary (do **not** claim)

The radius law is an input, and so is its hydrogenic extension
\(r_n=n^2 a_0/Z\). Nothing here derives either law from \(\gamma_s=0\).
There is no fine-structure splitting and no selection rule. The
electromagnetic length is the reduced Compton wavelength. The picometre
windows are consequences of those inputs together with the SI stand-ins;
they are not an independent measurement.

## What is proved

On the stand-ins, the fixed-proton vacuum wavelengths of the steps
\(2\to 1\), \(4\to 2\), \(5\to 2\), and \(4\to 3\) lie strictly between
\(121502\) and \(121503\), \(486009\) and \(486010\), \(433936\) and
\(433937\), and \(1874606\) and \(1874607\) picometres. Shared inertia, for
every mass ratio strictly between \(1836\) and \(1837\), places them
strictly between \(121568\) and \(121569\), \(486273\) and \(486274\),
\(434172\) and \(434174\), and \(1875626\) and \(1875628\) picometres.
With the nucleus fixed, charge two shortens the first and the last by
four, into \(30375\)–\(30376\) and \(468651\)–\(468652\) picometres.
-/

namespace DstDiophantine

namespace Gravity

open Real SI

/-! ### Photon wavelength -/

noncomputable def vacuumWavelength (energy : ℝ) : ℝ :=
  2 * π * (hbarApprox : ℝ) * (speedOfLight : ℝ) / energy

def piDigitLo : ℚ := 314159265358979323846 / (10 : ℚ) ^ 20

def piDigitHi : ℚ := 314159265358979323847 / (10 : ℚ) ^ 20

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

private theorem ratioWavelength_bounds {num den : ℕ} {lo hi : ℚ}
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

private theorem ratioShared_bounds {num den : ℕ} {lo hi : ℚ} {ρ : ℝ}
    (hnum : 0 < num) (hden : 0 < den)
    (hρlo : (1836 : ℝ) < ρ) (hρhi : ρ < 1837)
    (hlo : lo < standInWavelength num den piDigitLo * (1838 / 1837))
    (hhi : standInWavelength num den piDigitHi * (1837 / 1836) < hi) :
    (lo : ℝ) <
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((ρ + 1) / ρ) ∧
      ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((ρ + 1) / ρ) <
        (hi : ℝ) := by
  obtain ⟨hfacLo, hfacHi⟩ := massRatio_lengthens hρlo hρhi
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
  have hloR : (lo : ℝ) <
      (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
        ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) * ((1838 : ℝ) / 1837) := by
    let q : ℚ := standInWavelength num den piDigitLo * (1838 / 1837)
    have hcast : (lo : ℝ) < (q : ℝ) := by
      exact_mod_cast hlo
    have heq : (q : ℝ) =
        (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) * ((1838 : ℝ) / 1837) := by
      unfold q standInWavelength piDigitLo
      push_cast
      ring
    exact lt_of_lt_of_eq hcast heq
  have hhiR :
      (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) * ((1837 : ℝ) / 1836) <
        (hi : ℝ) := by
    let q : ℚ := standInWavelength num den piDigitHi * (1837 / 1836)
    have heq :
        (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((1837 : ℝ) / 1836) =
          (q : ℝ) := by
      unfold q standInWavelength piDigitHi
      push_cast
      ring
    have hcast : (q : ℝ) < (hi : ℝ) := by
      exact_mod_cast hhi
    exact lt_of_eq_of_lt heq hcast
  constructor
  · have hendpoint : (lo : ℝ) <
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((1838 : ℝ) / 1837) := by
      refine lt_trans hloR ?_
      calc (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((1838 : ℝ) / 1837)
          = ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((314159265358979323846 : ℝ) / 10 ^ 20) * ((1838 : ℝ) / 1837) := by ring
        _ < ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π * ((1838 : ℝ) / 1837) := by
            have hmul := mul_lt_mul_of_pos_left piDigitLo_lt_pi hfac
            exact mul_lt_mul_of_pos_right hmul (by norm_num : (0 : ℝ) < (1838 : ℝ) / 1837)
        _ = (num : ℝ) * π * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) * ((1838 : ℝ) / 1837) := by ring
    exact lt_of_lt_of_le hendpoint (mul_le_mul_of_nonneg_left hfacLo.le hpos.le)
  · have hendpoint :
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((1837 : ℝ) / 1836) <
          (hi : ℝ) := by
      refine lt_trans ?_ hhiR
      calc (num : ℝ) * π * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((1837 : ℝ) / 1836)
          = ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π * ((1837 : ℝ) / 1836) := by ring
        _ < ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((314159265358979323847 : ℝ) / 10 ^ 20) * ((1837 : ℝ) / 1836) := by
            have hmul := mul_lt_mul_of_pos_left piDigitHi_gt_pi hfac
            exact mul_lt_mul_of_pos_right hmul (by norm_num : (0 : ℝ) < (1837 : ℝ) / 1836)
        _ = (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) * ((1837 : ℝ) / 1836) := by ring
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hfacHi.le hpos.le) hendpoint

/-! ### Rational windows. `field_simp` clears the stand-ins. -/

private theorem lyman_fixed_lo_rat :
    (121502 : ℚ) / 10 ^ 12 < standInWavelength 16 3 piDigitLo := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem lyman_fixed_hi_rat :
    standInWavelength 16 3 piDigitHi < (121503 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem lyman_shared_lo_rat :
    (121568 : ℚ) / 10 ^ 12 < standInWavelength 16 3 piDigitLo * (1838 / 1837) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem lyman_shared_hi_rat :
    standInWavelength 16 3 piDigitHi * (1837 / 1836) < (121569 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hBeta_fixed_lo_rat :
    (486009 : ℚ) / 10 ^ 12 < standInWavelength 64 3 piDigitLo := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hBeta_fixed_hi_rat :
    standInWavelength 64 3 piDigitHi < (486010 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hBeta_shared_lo_rat :
    (486273 : ℚ) / 10 ^ 12 < standInWavelength 64 3 piDigitLo * (1838 / 1837) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hBeta_shared_hi_rat :
    standInWavelength 64 3 piDigitHi * (1837 / 1836) < (486274 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hGamma_fixed_lo_rat :
    (433936 : ℚ) / 10 ^ 12 < standInWavelength 400 21 piDigitLo := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hGamma_fixed_hi_rat :
    standInWavelength 400 21 piDigitHi < (433937 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hGamma_shared_lo_rat :
    (434172 : ℚ) / 10 ^ 12 < standInWavelength 400 21 piDigitLo * (1838 / 1837) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hGamma_shared_hi_rat :
    standInWavelength 400 21 piDigitHi * (1837 / 1836) < (434174 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem paschen_fixed_lo_rat :
    (1874606 : ℚ) / 10 ^ 12 < standInWavelength 576 7 piDigitLo := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem paschen_fixed_hi_rat :
    standInWavelength 576 7 piDigitHi < (1874607 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem paschen_shared_lo_rat :
    (1875626 : ℚ) / 10 ^ 12 < standInWavelength 576 7 piDigitLo * (1838 / 1837) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem paschen_shared_hi_rat :
    standInWavelength 576 7 piDigitHi * (1837 / 1836) < (1875628 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

/-! ### Closed forms -/

private theorem lyman_wavelength_eq :
    vacuumWavelength (bohrEnergyDiff 1 2) =
      16 * π * (hbarApprox : ℝ) /
        (3 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength
  rw [bohrEnergyDiff_lymanAlpha]
  simp only [hydrogenIonisationApprox]
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring_nf

private theorem hBeta_wavelength_eq :
    vacuumWavelength (bohrEnergyDiff 2 4) =
      64 * π * (hbarApprox : ℝ) /
        (3 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength
  rw [bohrEnergyDiff_hBeta]
  simp only [hydrogenIonisationApprox]
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring_nf

private theorem hGamma_wavelength_eq :
    vacuumWavelength (bohrEnergyDiff 2 5) =
      400 * π * (hbarApprox : ℝ) /
        (21 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength
  rw [bohrEnergyDiff_hGamma]
  simp only [hydrogenIonisationApprox]
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring_nf

private theorem paschen_wavelength_eq :
    vacuumWavelength (bohrEnergyDiff 3 4) =
      576 * π * (hbarApprox : ℝ) /
        (7 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength
  rw [bohrEnergyDiff_paschenAlpha]
  simp only [hydrogenIonisationApprox]
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring_nf

/-! ### Hydrogen windows -/

theorem lymanWavelength_bounds :
    (121502 : ℝ) / 10 ^ 12 < vacuumWavelength (bohrEnergyDiff 1 2) ∧
      vacuumWavelength (bohrEnergyDiff 1 2) < (121503 : ℝ) / 10 ^ 12 := by
  rw [lyman_wavelength_eq]
  convert ratioWavelength_bounds (by norm_num) (by norm_num)
      lyman_fixed_lo_rat lyman_fixed_hi_rat using 2 <;>
    push_cast <;> ring

theorem lyman_shared_wavelength {ρ : ℝ} (hlo : (1836 : ℝ) < ρ) (hhi : ρ < 1837) :
    (121568 : ℝ) / 10 ^ 12 <
      vacuumWavelength (bohrEnergyDiff 1 2) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (bohrEnergyDiff 1 2) * ((ρ + 1) / ρ) <
        (121569 : ℝ) / 10 ^ 12 := by
  rw [lyman_wavelength_eq]
  convert ratioShared_bounds (by norm_num) (by norm_num) hlo hhi
      lyman_shared_lo_rat lyman_shared_hi_rat using 2 <;>
    push_cast <;> ring

theorem lyman_proton_share :
    (121568 : ℝ) / 10 ^ 12 <
      vacuumWavelength (bohrEnergyDiff 1 2) *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) ∧
      vacuumWavelength (bohrEnergyDiff 1 2) *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) <
        (121569 : ℝ) / 10 ^ 12 := by
  have h := protonElectronMassRatio_bounds
  exact lyman_shared_wavelength (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem hBetaWavelength_bounds :
    (486009 : ℝ) / 10 ^ 12 < vacuumWavelength (bohrEnergyDiff 2 4) ∧
      vacuumWavelength (bohrEnergyDiff 2 4) < (486010 : ℝ) / 10 ^ 12 := by
  rw [hBeta_wavelength_eq]
  convert ratioWavelength_bounds (by norm_num) (by norm_num)
      hBeta_fixed_lo_rat hBeta_fixed_hi_rat using 2 <;>
    push_cast <;> ring

theorem hBeta_shared_wavelength {ρ : ℝ} (hlo : (1836 : ℝ) < ρ) (hhi : ρ < 1837) :
    (486273 : ℝ) / 10 ^ 12 <
      vacuumWavelength (bohrEnergyDiff 2 4) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (bohrEnergyDiff 2 4) * ((ρ + 1) / ρ) <
        (486274 : ℝ) / 10 ^ 12 := by
  rw [hBeta_wavelength_eq]
  convert ratioShared_bounds (by norm_num) (by norm_num) hlo hhi
      hBeta_shared_lo_rat hBeta_shared_hi_rat using 2 <;>
    push_cast <;> ring

theorem hBeta_proton_share :
    (486273 : ℝ) / 10 ^ 12 <
      vacuumWavelength (bohrEnergyDiff 2 4) *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) ∧
      vacuumWavelength (bohrEnergyDiff 2 4) *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) <
        (486274 : ℝ) / 10 ^ 12 := by
  have h := protonElectronMassRatio_bounds
  exact hBeta_shared_wavelength (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem hGammaWavelength_bounds :
    (433936 : ℝ) / 10 ^ 12 < vacuumWavelength (bohrEnergyDiff 2 5) ∧
      vacuumWavelength (bohrEnergyDiff 2 5) < (433937 : ℝ) / 10 ^ 12 := by
  rw [hGamma_wavelength_eq]
  convert ratioWavelength_bounds (by norm_num) (by norm_num)
      hGamma_fixed_lo_rat hGamma_fixed_hi_rat using 2 <;>
    push_cast <;> ring

theorem hGamma_shared_wavelength {ρ : ℝ} (hlo : (1836 : ℝ) < ρ) (hhi : ρ < 1837) :
    (434172 : ℝ) / 10 ^ 12 <
      vacuumWavelength (bohrEnergyDiff 2 5) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (bohrEnergyDiff 2 5) * ((ρ + 1) / ρ) <
        (434174 : ℝ) / 10 ^ 12 := by
  rw [hGamma_wavelength_eq]
  convert ratioShared_bounds (by norm_num) (by norm_num) hlo hhi
      hGamma_shared_lo_rat hGamma_shared_hi_rat using 2 <;>
    push_cast <;> ring

theorem hGamma_proton_share :
    (434172 : ℝ) / 10 ^ 12 <
      vacuumWavelength (bohrEnergyDiff 2 5) *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) ∧
      vacuumWavelength (bohrEnergyDiff 2 5) *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) <
        (434174 : ℝ) / 10 ^ 12 := by
  have h := protonElectronMassRatio_bounds
  exact hGamma_shared_wavelength (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem paschenWavelength_bounds :
    (1874606 : ℝ) / 10 ^ 12 < vacuumWavelength (bohrEnergyDiff 3 4) ∧
      vacuumWavelength (bohrEnergyDiff 3 4) < (1874607 : ℝ) / 10 ^ 12 := by
  rw [paschen_wavelength_eq]
  convert ratioWavelength_bounds (by norm_num) (by norm_num)
      paschen_fixed_lo_rat paschen_fixed_hi_rat using 2 <;>
    push_cast <;> ring

theorem paschen_shared_wavelength {ρ : ℝ} (hlo : (1836 : ℝ) < ρ) (hhi : ρ < 1837) :
    (1875626 : ℝ) / 10 ^ 12 <
      vacuumWavelength (bohrEnergyDiff 3 4) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (bohrEnergyDiff 3 4) * ((ρ + 1) / ρ) <
        (1875628 : ℝ) / 10 ^ 12 := by
  rw [paschen_wavelength_eq]
  convert ratioShared_bounds (by norm_num) (by norm_num) hlo hhi
      paschen_shared_lo_rat paschen_shared_hi_rat using 2 <;>
    push_cast <;> ring

theorem paschen_proton_share :
    (1875626 : ℝ) / 10 ^ 12 <
      vacuumWavelength (bohrEnergyDiff 3 4) *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) ∧
      vacuumWavelength (bohrEnergyDiff 3 4) *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) <
        (1875628 : ℝ) / 10 ^ 12 := by
  have h := protonElectronMassRatio_bounds
  exact paschen_shared_wavelength (by exact_mod_cast h.1) (by exact_mod_cast h.2)

/-! ### Charge two, nucleus fixed -/

private theorem chargeTwo_quarter {n m : ℕ} (hE : bohrEnergyDiff n m ≠ 0) :
    vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff n m) =
      vacuumWavelength (bohrEnergyDiff n m) / 4 := by
  unfold vacuumWavelength
  field_simp [hE]
  ring

private theorem lyman_energy_ne :
    bohrEnergyDiff 1 2 ≠ 0 := by
  rw [bohrEnergyDiff_lymanAlpha]
  exact mul_ne_zero (by norm_num) (by exact_mod_cast hydrogenIonisationApprox_pos.ne')

private theorem paschen_energy_ne :
    bohrEnergyDiff 3 4 ≠ 0 := by
  rw [bohrEnergyDiff_paschenAlpha]
  exact mul_ne_zero (by norm_num) (by exact_mod_cast hydrogenIonisationApprox_pos.ne')

theorem heLyman_wavelength_bounds :
    (30375 : ℝ) / 10 ^ 12 < vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 1 2) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 1 2) < (30376 : ℝ) / 10 ^ 12 := by
  rw [chargeTwo_quarter lyman_energy_ne]
  have hparent := lymanWavelength_bounds
  have h4 : (0 : ℝ) < 4 := by norm_num
  constructor
  · rw [lt_div_iff₀ h4]
    calc (30375 : ℝ) / 10 ^ 12 * 4
        = (121500 : ℝ) / 10 ^ 12 := by ring
      _ < (121502 : ℝ) / 10 ^ 12 := by norm_num
      _ < vacuumWavelength (bohrEnergyDiff 1 2) := hparent.1
  · rw [div_lt_iff₀ h4]
    calc vacuumWavelength (bohrEnergyDiff 1 2)
        < (121503 : ℝ) / 10 ^ 12 := hparent.2
      _ < (121504 : ℝ) / 10 ^ 12 := by norm_num
      _ = (30376 : ℝ) / 10 ^ 12 * 4 := by ring

theorem heVisible_wavelength_bounds :
    (468651 : ℝ) / 10 ^ 12 < vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 3 4) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 3 4) < (468652 : ℝ) / 10 ^ 12 := by
  rw [chargeTwo_quarter paschen_energy_ne]
  have hparent := paschenWavelength_bounds
  have h4 : (0 : ℝ) < 4 := by norm_num
  constructor
  · rw [lt_div_iff₀ h4]
    calc (468651 : ℝ) / 10 ^ 12 * 4
        = (1874604 : ℝ) / 10 ^ 12 := by ring
      _ < (1874606 : ℝ) / 10 ^ 12 := by norm_num
      _ < vacuumWavelength (bohrEnergyDiff 3 4) := hparent.1
  · rw [div_lt_iff₀ h4]
    calc vacuumWavelength (bohrEnergyDiff 3 4)
        < (1874607 : ℝ) / 10 ^ 12 := hparent.2
      _ < (1874608 : ℝ) / 10 ^ 12 := by norm_num
      _ = (468652 : ℝ) / 10 ^ 12 * 4 := by ring

end Gravity

end DstDiophantine
