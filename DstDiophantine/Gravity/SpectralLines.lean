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
four, into \(30375\)–\(30376\) and \(468651\)–\(468652\) picometres. The same
charge on doubled shells reproduces a hydrogen difference exactly:
\(4\to 2\), \(6\to 4\), \(8\to 4\), and \(10\to 4\) have the Lyman \(\alpha\),
\(\mathrm{H}\alpha\), \(\mathrm{H}\beta\), and \(\mathrm{H}\gamma\)
wavelengths. Shared inertia, for every helium-nucleus mass ratio strictly
between \(7294\) and \(7295\), places those four strictly between \(121518\)
and \(121519\), \(656202\) and \(656203\), \(486075\) and \(486076\), and
\(433996\) and \(433997\) picometres, each short of the hydrogen line that
carries a proton mass ratio strictly between \(1836\) and \(1837\).
With the nucleus fixed, charge eleven places the steps \(2\to 1\) and
\(4\to 3\) strictly between \(1004151\) and \(1004152\), and between
\(15492615\) and \(15492616\), in units of \(10^{-15}\,\mathrm{m}\).
The same charge on shells scaled by eleven reproduces a hydrogen
difference exactly: \(22\to 11\), \(33\to 22\), \(44\to 22\), and
\(55\to 22\) have the Lyman \(\alpha\), \(\mathrm{H}\alpha\),
\(\mathrm{H}\beta\), and \(\mathrm{H}\gamma\) wavelengths. Shared
inertia, for every sodium-nucleus mass ratio strictly between \(41896\)
and \(41897\), places those four strictly between \(121505\) and
\(121506\), \(656127\) and \(656128\), \(486020\) and \(486021\), and
\(433947\) and \(433948\) picometres, each short of the hydrogen line
that carries a proton mass ratio strictly between \(1836\) and \(1837\).
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

private theorem heliumMass_lengthens {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (7296 : ℝ) / 7295 < (ρ + 1) / ρ ∧ (ρ + 1) / ρ < (7295 : ℝ) / 7294 := by
  have hρ : 0 < ρ := by linarith
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) hρ]
    linarith
  · rw [div_lt_div_iff₀ hρ (by norm_num)]
    linarith

private theorem ratioHelium_bounds {num den : ℕ} {lo hi : ℚ} {ρ : ℝ}
    (hnum : 0 < num) (hden : 0 < den)
    (hρlo : (7294 : ℝ) < ρ) (hρhi : ρ < 7295)
    (hlo : lo < standInWavelength num den piDigitLo * (7296 / 7295))
    (hhi : standInWavelength num den piDigitHi * (7295 / 7294) < hi) :
    (lo : ℝ) <
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((ρ + 1) / ρ) ∧
      ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((ρ + 1) / ρ) <
        (hi : ℝ) := by
  obtain ⟨hfacLo, hfacHi⟩ := heliumMass_lengthens hρlo hρhi
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
          (fineStructureApprox : ℝ) ^ 2) * ((7296 : ℝ) / 7295) := by
    let q : ℚ := standInWavelength num den piDigitLo * (7296 / 7295)
    have hcast : (lo : ℝ) < (q : ℝ) := by
      exact_mod_cast hlo
    have heq : (q : ℝ) =
        (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) * ((7296 : ℝ) / 7295) := by
      unfold q standInWavelength piDigitLo
      push_cast
      ring
    exact lt_of_lt_of_eq hcast heq
  have hhiR :
      (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) * ((7295 : ℝ) / 7294) <
        (hi : ℝ) := by
    let q : ℚ := standInWavelength num den piDigitHi * (7295 / 7294)
    have heq :
        (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((7295 : ℝ) / 7294) =
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
            (fineStructureApprox : ℝ) ^ 2)) * ((7296 : ℝ) / 7295) := by
      refine lt_trans hloR ?_
      calc (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((7296 : ℝ) / 7295)
          = ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((314159265358979323846 : ℝ) / 10 ^ 20) * ((7296 : ℝ) / 7295) := by ring
        _ < ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π * ((7296 : ℝ) / 7295) := by
            have hmul := mul_lt_mul_of_pos_left piDigitLo_lt_pi hfac
            exact mul_lt_mul_of_pos_right hmul (by norm_num : (0 : ℝ) < (7296 : ℝ) / 7295)
        _ = (num : ℝ) * π * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) * ((7296 : ℝ) / 7295) := by ring
    exact lt_of_lt_of_le hendpoint (mul_le_mul_of_nonneg_left hfacLo.le hpos.le)
  · have hendpoint :
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((7295 : ℝ) / 7294) <
          (hi : ℝ) := by
      refine lt_trans ?_ hhiR
      calc (num : ℝ) * π * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((7295 : ℝ) / 7294)
          = ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π * ((7295 : ℝ) / 7294) := by ring
        _ < ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((314159265358979323847 : ℝ) / 10 ^ 20) * ((7295 : ℝ) / 7294) := by
            have hmul := mul_lt_mul_of_pos_left piDigitHi_gt_pi hfac
            exact mul_lt_mul_of_pos_right hmul (by norm_num : (0 : ℝ) < (7295 : ℝ) / 7294)
        _ = (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) * ((7295 : ℝ) / 7294) := by ring
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

private theorem heMatchLyman_lo_rat :
    (121518 : ℚ) / 10 ^ 12 < standInWavelength 16 3 piDigitLo * (7296 / 7295) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem heMatchLyman_hi_rat :
    standInWavelength 16 3 piDigitHi * (7295 / 7294) < (121519 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem heMatchAlpha_lo_rat :
    (656202 : ℚ) / 10 ^ 12 < standInWavelength 144 5 piDigitLo * (7296 / 7295) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem heMatchAlpha_hi_rat :
    standInWavelength 144 5 piDigitHi * (7295 / 7294) < (656203 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem heMatchBeta_lo_rat :
    (486075 : ℚ) / 10 ^ 12 < standInWavelength 64 3 piDigitLo * (7296 / 7295) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem heMatchBeta_hi_rat :
    standInWavelength 64 3 piDigitHi * (7295 / 7294) < (486076 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem heMatchGamma_lo_rat :
    (433996 : ℚ) / 10 ^ 12 < standInWavelength 400 21 piDigitLo * (7296 / 7295) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem heMatchGamma_hi_rat :
    standInWavelength 400 21 piDigitHi * (7295 / 7294) < (433997 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

/-! ### Closed forms -/

private theorem hAlpha_wavelength_eq :
    vacuumWavelength (bohrEnergyDiff 2 3) =
      144 * π * (hbarApprox : ℝ) /
        (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength
  rw [bohrEnergyDiff_hAlpha]
  simp only [hydrogenIonisationApprox]
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring_nf

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

/-! ### Charge two -/

theorem chargeTwo_doubled {n m : ℕ} (hn : 0 < n) (hm : n < m) :
    (2 : ℝ) ^ 2 * bohrEnergyDiff (2 * n) (2 * m) = bohrEnergyDiff n m := by
  unfold bohrEnergyDiff
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (hn.trans hm).ne'
  field_simp [hn', hm']

private theorem doubled_wavelength {n m a b : ℕ} (hn : 0 < n) (hm : n < m)
    (ha : 2 * n = a) (hb : 2 * m = b) :
    vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff a b) =
      vacuumWavelength (bohrEnergyDiff n m) := by
  have h := chargeTwo_doubled hn hm
  rw [ha, hb] at h
  exact congrArg vacuumWavelength h

theorem heMatchLyman_fixed :
    vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 2 4) =
      vacuumWavelength (bohrEnergyDiff 1 2) :=
  doubled_wavelength (n := 1) (m := 2) (a := 2) (b := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem heMatchAlpha_fixed :
    vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 6) =
      vacuumWavelength (bohrEnergyDiff 2 3) :=
  doubled_wavelength (n := 2) (m := 3) (a := 4) (b := 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem heMatchBeta_fixed :
    vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 8) =
      vacuumWavelength (bohrEnergyDiff 2 4) :=
  doubled_wavelength (n := 2) (m := 4) (a := 4) (b := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem heMatchGamma_fixed :
    vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 10) =
      vacuumWavelength (bohrEnergyDiff 2 5) :=
  doubled_wavelength (n := 2) (m := 5) (a := 4) (b := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem heMatchLyman_shared {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (121518 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 2 4) * ((ρ + 1) / ρ) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 2 4) * ((ρ + 1) / ρ) <
        (121519 : ℝ) / 10 ^ 12 := by
  rw [heMatchLyman_fixed, lyman_wavelength_eq]
  convert ratioHelium_bounds (by norm_num) (by norm_num) hlo hhi
      heMatchLyman_lo_rat heMatchLyman_hi_rat using 2 <;>
    push_cast <;> ring

theorem heMatchAlpha_shared {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (656202 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 6) * ((ρ + 1) / ρ) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 6) * ((ρ + 1) / ρ) <
        (656203 : ℝ) / 10 ^ 12 := by
  rw [heMatchAlpha_fixed, hAlpha_wavelength_eq]
  convert ratioHelium_bounds (by norm_num) (by norm_num) hlo hhi
      heMatchAlpha_lo_rat heMatchAlpha_hi_rat using 2 <;>
    push_cast <;> ring

theorem heMatchBeta_shared {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (486075 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 8) * ((ρ + 1) / ρ) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 8) * ((ρ + 1) / ρ) <
        (486076 : ℝ) / 10 ^ 12 := by
  rw [heMatchBeta_fixed, hBeta_wavelength_eq]
  convert ratioHelium_bounds (by norm_num) (by norm_num) hlo hhi
      heMatchBeta_lo_rat heMatchBeta_hi_rat using 2 <;>
    push_cast <;> ring

theorem heMatchGamma_shared {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (433996 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 10) * ((ρ + 1) / ρ) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 10) * ((ρ + 1) / ρ) <
        (433997 : ℝ) / 10 ^ 12 := by
  rw [heMatchGamma_fixed, hGamma_wavelength_eq]
  convert ratioHelium_bounds (by norm_num) (by norm_num) hlo hhi
      heMatchGamma_lo_rat heMatchGamma_hi_rat using 2 <;>
    push_cast <;> ring

theorem heMatchLyman_nucleus :
    (121518 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 2 4) *
        (((alphaElectronMassRatio : ℝ) + 1) / (alphaElectronMassRatio : ℝ)) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 2 4) *
        (((alphaElectronMassRatio : ℝ) + 1) / (alphaElectronMassRatio : ℝ)) <
        (121519 : ℝ) / 10 ^ 12 := by
  have h := alphaElectronMassRatio_bounds
  exact heMatchLyman_shared (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem heMatchAlpha_nucleus :
    (656202 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 6) *
        (((alphaElectronMassRatio : ℝ) + 1) / (alphaElectronMassRatio : ℝ)) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 6) *
        (((alphaElectronMassRatio : ℝ) + 1) / (alphaElectronMassRatio : ℝ)) <
        (656203 : ℝ) / 10 ^ 12 := by
  have h := alphaElectronMassRatio_bounds
  exact heMatchAlpha_shared (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem heMatchBeta_nucleus :
    (486075 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 8) *
        (((alphaElectronMassRatio : ℝ) + 1) / (alphaElectronMassRatio : ℝ)) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 8) *
        (((alphaElectronMassRatio : ℝ) + 1) / (alphaElectronMassRatio : ℝ)) <
        (486076 : ℝ) / 10 ^ 12 := by
  have h := alphaElectronMassRatio_bounds
  exact heMatchBeta_shared (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem heMatchGamma_nucleus :
    (433996 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 10) *
        (((alphaElectronMassRatio : ℝ) + 1) / (alphaElectronMassRatio : ℝ)) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 10) *
        (((alphaElectronMassRatio : ℝ) + 1) / (alphaElectronMassRatio : ℝ)) <
        (433997 : ℝ) / 10 ^ 12 := by
  have h := alphaElectronMassRatio_bounds
  exact heMatchGamma_shared (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem heMatch_short_of_hydrogen {ρ σ : ℝ}
    (hρlo : (7294 : ℝ) < ρ) (hρhi : ρ < 7295)
    (hσlo : (1836 : ℝ) < σ) (hσhi : σ < 1837) :
    vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 2 4) * ((ρ + 1) / ρ) <
        vacuumWavelength (bohrEnergyDiff 1 2) * ((σ + 1) / σ) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 6) * ((ρ + 1) / ρ) <
        hAlphaWavelength * ((σ + 1) / σ) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 8) * ((ρ + 1) / ρ) <
        vacuumWavelength (bohrEnergyDiff 2 4) * ((σ + 1) / σ) ∧
      vacuumWavelength ((2 : ℝ) ^ 2 * bohrEnergyDiff 4 10) * ((ρ + 1) / ρ) <
        vacuumWavelength (bohrEnergyDiff 2 5) * ((σ + 1) / σ) := by
  have hLy := heMatchLyman_shared hρlo hρhi
  have hA := heMatchAlpha_shared hρlo hρhi
  have hB := heMatchBeta_shared hρlo hρhi
  have hG := heMatchGamma_shared hρlo hρhi
  have kLy := lyman_shared_wavelength hσlo hσhi
  have kA := hAlpha_shared_wavelength hσlo hσhi
  have kB := hBeta_shared_wavelength hσlo hσhi
  have kG := hGamma_shared_wavelength hσlo hσhi
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lt_trans hLy.2
      (lt_trans (by norm_num : (121519 : ℝ) / 10 ^ 12 < (121568 : ℝ) / 10 ^ 12) kLy.1)
  · exact lt_trans hA.2
      (lt_trans (by norm_num : (656203 : ℝ) / 10 ^ 12 < (656469 : ℝ) / 10 ^ 12) kA.1)
  · exact lt_trans hB.2
      (lt_trans (by norm_num : (486076 : ℝ) / 10 ^ 12 < (486273 : ℝ) / 10 ^ 12) kB.1)
  · exact lt_trans hG.2
      (lt_trans (by norm_num : (433997 : ℝ) / 10 ^ 12 < (434172 : ℝ) / 10 ^ 12) kG.1)

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

/-! ### Charge eleven -/

private theorem sodiumMass_lengthens {ρ : ℝ} (hlo : (41896 : ℝ) < ρ) (hhi : ρ < 41897) :
    (41898 : ℝ) / 41897 < (ρ + 1) / ρ ∧ (ρ + 1) / ρ < (41897 : ℝ) / 41896 := by
  have hρ : 0 < ρ := by linarith
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) hρ]
    linarith
  · rw [div_lt_div_iff₀ hρ (by norm_num)]
    linarith

private theorem ratioSodium_bounds {num den : ℕ} {lo hi : ℚ} {ρ : ℝ}
    (hnum : 0 < num) (hden : 0 < den)
    (hρlo : (41896 : ℝ) < ρ) (hρhi : ρ < 41897)
    (hlo : lo < standInWavelength num den piDigitLo * (41898 / 41897))
    (hhi : standInWavelength num den piDigitHi * (41897 / 41896) < hi) :
    (lo : ℝ) <
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((ρ + 1) / ρ) ∧
      ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((ρ + 1) / ρ) <
        (hi : ℝ) := by
  obtain ⟨hfacLo, hfacHi⟩ := sodiumMass_lengthens hρlo hρhi
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
  have hlowPos : (0 : ℝ) < (41898 : ℝ) / 41897 := by norm_num
  have hhighPos : (0 : ℝ) < (41897 : ℝ) / 41896 := by norm_num
  have hloR : (lo : ℝ) <
      (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
        ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) * ((41898 : ℝ) / 41897) := by
    let q : ℚ := standInWavelength num den piDigitLo * (41898 / 41897)
    have hcast : (lo : ℝ) < (q : ℝ) := by
      dsimp only [q]
      exact_mod_cast hlo
    have heq : (q : ℝ) =
        (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) * ((41898 : ℝ) / 41897) := by
      unfold q standInWavelength piDigitLo
      push_cast
      ring
    exact lt_of_lt_of_eq hcast heq
  have hhiR :
      (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2) * ((41897 : ℝ) / 41896) <
        (hi : ℝ) := by
    let q : ℚ := standInWavelength num den piDigitHi * (41897 / 41896)
    have heq :
        (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((41897 : ℝ) / 41896) =
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
            (fineStructureApprox : ℝ) ^ 2)) * ((41898 : ℝ) / 41897) := by
      refine lt_trans hloR ?_
      calc (num : ℝ) * ((314159265358979323846 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((41898 : ℝ) / 41897)
          = ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((314159265358979323846 : ℝ) / 10 ^ 20) *
              ((41898 : ℝ) / 41897) := by ring
        _ < ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π *
              ((41898 : ℝ) / 41897) := by
            have hmul := mul_lt_mul_of_pos_left piDigitLo_lt_pi hfac
            exact mul_lt_mul_of_pos_right hmul hlowPos
        _ = (num : ℝ) * π * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) *
              ((41898 : ℝ) / 41897) := by ring
    exact lt_of_lt_of_le hendpoint (mul_le_mul_of_nonneg_left hfacLo.le hpos.le)
  · have hendpoint :
        ((num : ℝ) * π * (hbarApprox : ℝ) /
          ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * ((41897 : ℝ) / 41896) <
          (hi : ℝ) := by
      refine lt_trans ?_ hhiR
      calc (num : ℝ) * π * (hbarApprox : ℝ) /
            ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((41897 : ℝ) / 41896)
          = ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π *
              ((41897 : ℝ) / 41896) := by ring
        _ < ((num : ℝ) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((314159265358979323847 : ℝ) / 10 ^ 20) *
              ((41897 : ℝ) / 41896) := by
            have hmul := mul_lt_mul_of_pos_left piDigitHi_gt_pi hfac
            exact mul_lt_mul_of_pos_right hmul hhighPos
        _ = (num : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) * (hbarApprox : ℝ) /
              ((den : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) *
              ((41897 : ℝ) / 41896) := by ring
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hfacHi.le hpos.le) hendpoint

theorem chargeIndex_scaled {Z n m : ℕ} (hZ : 0 < Z) (hn : 0 < n) (hm : n < m) :
    (Z : ℝ) ^ 2 * bohrEnergyDiff (Z * n) (Z * m) = bohrEnergyDiff n m := by
  unfold bohrEnergyDiff
  simp only [Nat.cast_mul]
  have hZ' : (Z : ℝ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (hn.trans hm).ne'
  field_simp [hZ', hn', hm']

private theorem scaled_wavelength {Z n m a b : ℕ}
    (hZ : 0 < Z) (hn : 0 < n) (hm : n < m)
    (ha : Z * n = a) (hb : Z * m = b) :
    vacuumWavelength ((Z : ℝ) ^ 2 * bohrEnergyDiff a b) =
      vacuumWavelength (bohrEnergyDiff n m) := by
  have h := chargeIndex_scaled hZ hn hm
  rw [ha, hb] at h
  exact congrArg vacuumWavelength h

private theorem chargeEleven_div {E : ℝ} (hE : E ≠ 0) :
    vacuumWavelength ((11 : ℝ) ^ 2 * E) = vacuumWavelength E / 121 := by
  unfold vacuumWavelength
  field_simp [hE]
  ring

private theorem naLyman_wavelength_eq :
    vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 1 2) =
      16 * π * (hbarApprox : ℝ) /
        (363 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  rw [chargeEleven_div lyman_energy_ne, lyman_wavelength_eq]
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  field_simp [hm, hc, hα]
  ring

private theorem naVisible_wavelength_eq :
    vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 3 4) =
      576 * π * (hbarApprox : ℝ) /
        (847 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  rw [chargeEleven_div paschen_energy_ne, paschen_wavelength_eq]
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  field_simp [hm, hc, hα]
  ring

private theorem naLyman_fixed_lo_rat :
    (1004151 : ℚ) / 10 ^ 15 < standInWavelength 16 363 piDigitLo := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naLyman_fixed_hi_rat :
    standInWavelength 16 363 piDigitHi < (1004152 : ℚ) / 10 ^ 15 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naVisible_fixed_lo_rat :
    (15492615 : ℚ) / 10 ^ 15 < standInWavelength 576 847 piDigitLo := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naVisible_fixed_hi_rat :
    standInWavelength 576 847 piDigitHi < (15492616 : ℚ) / 10 ^ 15 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

theorem naLyman_wavelength_bounds :
    (1004151 : ℝ) / 10 ^ 15 < vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 1 2) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 1 2) <
        (1004152 : ℝ) / 10 ^ 15 := by
  rw [naLyman_wavelength_eq]
  convert ratioWavelength_bounds (by norm_num) (by norm_num)
      naLyman_fixed_lo_rat naLyman_fixed_hi_rat using 2 <;>
    push_cast <;> ring

theorem naVisible_wavelength_bounds :
    (15492615 : ℝ) / 10 ^ 15 <
        vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 3 4) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 3 4) <
        (15492616 : ℝ) / 10 ^ 15 := by
  rw [naVisible_wavelength_eq]
  convert ratioWavelength_bounds (by norm_num) (by norm_num)
      naVisible_fixed_lo_rat naVisible_fixed_hi_rat using 2 <;>
    push_cast <;> ring

theorem naMatchLyman_fixed :
    vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 11 22) =
      vacuumWavelength (bohrEnergyDiff 1 2) :=
  scaled_wavelength (Z := 11) (n := 1) (m := 2) (a := 11) (b := 22)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem naMatchAlpha_fixed :
    vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 33) =
      vacuumWavelength (bohrEnergyDiff 2 3) :=
  scaled_wavelength (Z := 11) (n := 2) (m := 3) (a := 22) (b := 33)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem naMatchBeta_fixed :
    vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 44) =
      vacuumWavelength (bohrEnergyDiff 2 4) :=
  scaled_wavelength (Z := 11) (n := 2) (m := 4) (a := 22) (b := 44)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem naMatchGamma_fixed :
    vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 55) =
      vacuumWavelength (bohrEnergyDiff 2 5) :=
  scaled_wavelength (Z := 11) (n := 2) (m := 5) (a := 22) (b := 55)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem naMatchLyman_lo_rat :
    (121505 : ℚ) / 10 ^ 12 < standInWavelength 16 3 piDigitLo * (41898 / 41897) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naMatchLyman_hi_rat :
    standInWavelength 16 3 piDigitHi * (41897 / 41896) < (121506 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naMatchAlpha_lo_rat :
    (656127 : ℚ) / 10 ^ 12 < standInWavelength 144 5 piDigitLo * (41898 / 41897) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naMatchAlpha_hi_rat :
    standInWavelength 144 5 piDigitHi * (41897 / 41896) < (656128 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naMatchBeta_lo_rat :
    (486020 : ℚ) / 10 ^ 12 < standInWavelength 64 3 piDigitLo * (41898 / 41897) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naMatchBeta_hi_rat :
    standInWavelength 64 3 piDigitHi * (41897 / 41896) < (486021 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naMatchGamma_lo_rat :
    (433947 : ℚ) / 10 ^ 12 < standInWavelength 400 21 piDigitLo * (41898 / 41897) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem naMatchGamma_hi_rat :
    standInWavelength 400 21 piDigitHi * (41897 / 41896) < (433948 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

theorem naMatchLyman_shared {ρ : ℝ} (hlo : (41896 : ℝ) < ρ) (hhi : ρ < 41897) :
    (121505 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 11 22) * ((ρ + 1) / ρ) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 11 22) * ((ρ + 1) / ρ) <
        (121506 : ℝ) / 10 ^ 12 := by
  rw [naMatchLyman_fixed, lyman_wavelength_eq]
  convert ratioSodium_bounds (by norm_num) (by norm_num) hlo hhi
      naMatchLyman_lo_rat naMatchLyman_hi_rat using 2 <;>
    push_cast <;> ring

theorem naMatchAlpha_shared {ρ : ℝ} (hlo : (41896 : ℝ) < ρ) (hhi : ρ < 41897) :
    (656127 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 33) * ((ρ + 1) / ρ) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 33) * ((ρ + 1) / ρ) <
        (656128 : ℝ) / 10 ^ 12 := by
  rw [naMatchAlpha_fixed, hAlpha_wavelength_eq]
  convert ratioSodium_bounds (by norm_num) (by norm_num) hlo hhi
      naMatchAlpha_lo_rat naMatchAlpha_hi_rat using 2 <;>
    push_cast <;> ring

theorem naMatchBeta_shared {ρ : ℝ} (hlo : (41896 : ℝ) < ρ) (hhi : ρ < 41897) :
    (486020 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 44) * ((ρ + 1) / ρ) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 44) * ((ρ + 1) / ρ) <
        (486021 : ℝ) / 10 ^ 12 := by
  rw [naMatchBeta_fixed, hBeta_wavelength_eq]
  convert ratioSodium_bounds (by norm_num) (by norm_num) hlo hhi
      naMatchBeta_lo_rat naMatchBeta_hi_rat using 2 <;>
    push_cast <;> ring

theorem naMatchGamma_shared {ρ : ℝ} (hlo : (41896 : ℝ) < ρ) (hhi : ρ < 41897) :
    (433947 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 55) * ((ρ + 1) / ρ) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 55) * ((ρ + 1) / ρ) <
        (433948 : ℝ) / 10 ^ 12 := by
  rw [naMatchGamma_fixed, hGamma_wavelength_eq]
  convert ratioSodium_bounds (by norm_num) (by norm_num) hlo hhi
      naMatchGamma_lo_rat naMatchGamma_hi_rat using 2 <;>
    push_cast <;> ring

theorem naMatchLyman_nucleus :
    (121505 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 11 22) *
        (((sodiumElectronMassRatio : ℝ) + 1) / (sodiumElectronMassRatio : ℝ)) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 11 22) *
        (((sodiumElectronMassRatio : ℝ) + 1) / (sodiumElectronMassRatio : ℝ)) <
        (121506 : ℝ) / 10 ^ 12 := by
  have h := sodiumElectronMassRatio_bounds
  exact naMatchLyman_shared (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem naMatchAlpha_nucleus :
    (656127 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 33) *
        (((sodiumElectronMassRatio : ℝ) + 1) / (sodiumElectronMassRatio : ℝ)) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 33) *
        (((sodiumElectronMassRatio : ℝ) + 1) / (sodiumElectronMassRatio : ℝ)) <
        (656128 : ℝ) / 10 ^ 12 := by
  have h := sodiumElectronMassRatio_bounds
  exact naMatchAlpha_shared (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem naMatchBeta_nucleus :
    (486020 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 44) *
        (((sodiumElectronMassRatio : ℝ) + 1) / (sodiumElectronMassRatio : ℝ)) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 44) *
        (((sodiumElectronMassRatio : ℝ) + 1) / (sodiumElectronMassRatio : ℝ)) <
        (486021 : ℝ) / 10 ^ 12 := by
  have h := sodiumElectronMassRatio_bounds
  exact naMatchBeta_shared (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem naMatchGamma_nucleus :
    (433947 : ℝ) / 10 ^ 12 <
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 55) *
        (((sodiumElectronMassRatio : ℝ) + 1) / (sodiumElectronMassRatio : ℝ)) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 55) *
        (((sodiumElectronMassRatio : ℝ) + 1) / (sodiumElectronMassRatio : ℝ)) <
        (433948 : ℝ) / 10 ^ 12 := by
  have h := sodiumElectronMassRatio_bounds
  exact naMatchGamma_shared (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem naMatch_short_of_hydrogen {ρ σ : ℝ}
    (hρlo : (41896 : ℝ) < ρ) (hρhi : ρ < 41897)
    (hσlo : (1836 : ℝ) < σ) (hσhi : σ < 1837) :
    vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 11 22) * ((ρ + 1) / ρ) <
        vacuumWavelength (bohrEnergyDiff 1 2) * ((σ + 1) / σ) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 33) * ((ρ + 1) / ρ) <
        hAlphaWavelength * ((σ + 1) / σ) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 44) * ((ρ + 1) / ρ) <
        vacuumWavelength (bohrEnergyDiff 2 4) * ((σ + 1) / σ) ∧
      vacuumWavelength ((11 : ℝ) ^ 2 * bohrEnergyDiff 22 55) * ((ρ + 1) / ρ) <
        vacuumWavelength (bohrEnergyDiff 2 5) * ((σ + 1) / σ) := by
  have hLy := naMatchLyman_shared hρlo hρhi
  have hA := naMatchAlpha_shared hρlo hρhi
  have hB := naMatchBeta_shared hρlo hρhi
  have hG := naMatchGamma_shared hρlo hρhi
  have kLy := lyman_shared_wavelength hσlo hσhi
  have kA := hAlpha_shared_wavelength hσlo hσhi
  have kB := hBeta_shared_wavelength hσlo hσhi
  have kG := hGamma_shared_wavelength hσlo hσhi
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lt_trans hLy.2
      (lt_trans (by norm_num : (121506 : ℝ) / 10 ^ 12 < (121568 : ℝ) / 10 ^ 12) kLy.1)
  · exact lt_trans hA.2
      (lt_trans (by norm_num : (656128 : ℝ) / 10 ^ 12 < (656469 : ℝ) / 10 ^ 12) kA.1)
  · exact lt_trans hB.2
      (lt_trans (by norm_num : (486021 : ℝ) / 10 ^ 12 < (486273 : ℝ) / 10 ^ 12) kB.1)
  · exact lt_trans hG.2
      (lt_trans (by norm_num : (433948 : ℝ) / 10 ^ 12 < (434172 : ℝ) / 10 ^ 12) kG.1)

end Gravity

end DstDiophantine
