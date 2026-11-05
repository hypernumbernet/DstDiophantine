import DstDiophantine.Gravity.HydrogenAlpha
import DstDiophantine.Gravity.LineWindow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Representative lines on the outer plateau

## Paper boundary (do **not** claim)

The radius law \(r_n=n^2 a_0\) is an input. Nothing here derives it from
\(\gamma_s=0\). There is no fine-structure splitting and no selection rule.
The electromagnetic length is the reduced Compton wavelength. The picometre
windows are consequences of that input together with the SI stand-ins;
they are not an independent measurement. The series is hydrogen, one proton
and one electron. The line of any other nucleus is not read by scaling
these steps.

## What is proved

On the stand-ins, the fixed-proton vacuum wavelengths of the steps
\(2\to 1\), \(4\to 2\), \(5\to 2\), and \(4\to 3\) lie strictly between
\(121502\) and \(121503\), \(486009\) and \(486010\), \(433936\) and
\(433937\), and \(1874606\) and \(1874607\) picometres. Shared inertia, for
every mass ratio strictly between \(1836\) and \(1837\), places them
strictly between \(121568\) and \(121569\), \(486273\) and \(486274\),
\(434172\) and \(434174\), and \(1875626\) and \(1875628\) picometres.
-/

namespace DstDiophantine

namespace Gravity

open Real SI

/-! ### Shared-inertia window -/

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
  have hfacLo' : ((1838 / 1837 : ℚ) : ℝ) < (ρ + 1) / ρ := by
    convert hfacLo using 1; norm_num
  have hfacHi' : (ρ + 1) / ρ < ((1837 / 1836 : ℚ) : ℝ) := by
    convert hfacHi using 1; norm_num
  exact ratioFactor_bounds hnum hden (by norm_num) (by norm_num)
    hfacLo' hfacHi' hlo hhi

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

/-- A Bohr difference equal to `a/b` of the ionisation has vacuum wavelength
`4b/a` times \(\pi\hbar/(m_e c\alpha^2)\). -/
private theorem vacuumWavelength_of_fraction {n m a b : ℕ}
    (h : bohrEnergyDiff n m =
      ((a : ℝ) / (b : ℝ)) * (hydrogenIonisationApprox : ℝ))
    (ha : a ≠ 0) (hb : b ≠ 0) :
    vacuumWavelength (bohrEnergyDiff n m) =
      (4 * (b : ℝ)) * π * (hbarApprox : ℝ) /
        ((a : ℝ) * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength
  rw [h]
  simp only [hydrogenIonisationApprox]
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  push_cast
  field_simp [hm, hc, hα, ha', hb']
  ring_nf

private theorem lyman_wavelength_eq :
    vacuumWavelength (bohrEnergyDiff 1 2) =
      16 * π * (hbarApprox : ℝ) /
        (3 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  rw [vacuumWavelength_of_fraction (n := 1) (m := 2) (a := 3) (b := 4)
    bohrEnergyDiff_lymanAlpha (by norm_num) (by norm_num)]
  ring

private theorem hBeta_wavelength_eq :
    vacuumWavelength (bohrEnergyDiff 2 4) =
      64 * π * (hbarApprox : ℝ) /
        (3 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  rw [vacuumWavelength_of_fraction (n := 2) (m := 4) (a := 3) (b := 16)
    bohrEnergyDiff_hBeta (by norm_num) (by norm_num)]
  ring

private theorem hGamma_wavelength_eq :
    vacuumWavelength (bohrEnergyDiff 2 5) =
      400 * π * (hbarApprox : ℝ) /
        (21 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  rw [vacuumWavelength_of_fraction (n := 2) (m := 5) (a := 21) (b := 100)
    bohrEnergyDiff_hGamma (by norm_num) (by norm_num)]
  ring

private theorem paschen_wavelength_eq :
    vacuumWavelength (bohrEnergyDiff 3 4) =
      576 * π * (hbarApprox : ℝ) /
        (7 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  rw [vacuumWavelength_of_fraction (n := 3) (m := 4) (a := 7) (b := 144)
    bohrEnergyDiff_paschenAlpha (by norm_num) (by norm_num)]
  ring

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


end Gravity

end DstDiophantine
