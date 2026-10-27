import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# SI / CODATA bookkeeping for the DST gravity chart

**External inputs only.** These rationals are *not* derived from the double
spacetime algebra. The DST action writes \(G\) as a coupling constant in
\(S = (c^4/(16\pi G))\int J\,d^4x\); the present module records CODATA-style
placeholders so that exploratory numerical comparisons in `NewtonFromLight`,
`CoulombFromDual`, `ElectronShell`, `CompactS3`, and `NuclearLayer` can be
machine-checked without `Float`.

Units (SI): \(c\) in m/s, \(\hbar\) in J·s, \(G\) in m³·kg⁻¹·s⁻², masses in kg,
elementary charge in C. Fine-structure \(\alpha\) is dimensionless.
Galaxy-scale inputs: \(M_\odot\) in kg, kpc in m, MOND \(a_0\) in m/s².
Nuclear-scale inputs: fm, MeV, pion/proton mass in MeV, saturation density,
binding energy per nucleon (all external; not derived).

Mantissas are exposed as `ℕ` so cleared-denominator witnesses can reuse them
without duplicating decimal literals.

The electromagnetic force scale is the single observational product
\(ke^{2}=\alpha\hbar c\) (`coulombScale`). There is no second decimal for
that scale. The Coulomb prefactor is \(k=\alpha\hbar c/e^{2}\). Bohr
\(a_0=\hbar/(m_e c\alpha)\) and ionisation \(E_I=\tfrac12 m_e c^2\alpha^2\)
are the same inputs, and they avoid an independent \(\varepsilon_0\).

The shared lattice floor \(\varepsilon_N=16/(3N^2)\) lives here so both
`NewtonFromLight` and `CoulombFromDual` can reuse it without cross-import.
-/

namespace DstDiophantine

namespace Gravity

namespace SI

/-- Exact SI definition of the speed of light (m/s). -/
def speedOfLightNat : ℕ := 299792458

def speedOfLight : ℚ := speedOfLightNat

/-- Mantissa of \(\hbar \approx 1.054571817\times 10^{-34}\) J·s. -/
def hbarMantissa : ℕ := 1054571817

/-- Scale: \(\hbar =\) `hbarMantissa` `/ 10^hbarScale`. -/
def hbarScale : ℕ := 43

def hbarApprox : ℚ := hbarMantissa / (10 : ℚ) ^ hbarScale

/-- Mantissa of \(G \approx 6.67430\times 10^{-11}\) m³·kg⁻¹·s⁻². -/
def GMantissa : ℕ := 667430

def GScale : ℕ := 16

def GApprox : ℚ := GMantissa / (10 : ℚ) ^ GScale

/-- Mantissa of \(m_e \approx 9.1093837015\times 10^{-31}\) kg. -/
def electronMassMantissa : ℕ := 91093837015

def electronMassScale : ℕ := 41

def electronMassApprox : ℚ :=
  electronMassMantissa / (10 : ℚ) ^ electronMassScale

/-- Mantissa of \(m_p \approx 1.67262192369\times 10^{-27}\) kg. -/
def protonMassMantissa : ℕ := 167262192369

def protonMassScale : ℕ := 38

def protonMassApprox : ℚ :=
  protonMassMantissa / (10 : ℚ) ^ protonMassScale

theorem speedOfLight_pos : (0 : ℚ) < speedOfLight := by
  unfold speedOfLight speedOfLightNat; norm_num

theorem hbarApprox_pos : (0 : ℚ) < hbarApprox := by
  unfold hbarApprox hbarMantissa hbarScale; norm_num

theorem GApprox_pos : (0 : ℚ) < GApprox := by
  unfold GApprox GMantissa GScale; norm_num

theorem electronMassApprox_pos : (0 : ℚ) < electronMassApprox := by
  unfold electronMassApprox electronMassMantissa electronMassScale; norm_num

theorem protonMassApprox_pos : (0 : ℚ) < protonMassApprox := by
  unfold protonMassApprox protonMassMantissa protonMassScale; norm_num

/-- \(\hbar c\) in SI (J·m). -/
def hbarC : ℚ := hbarApprox * speedOfLight

theorem hbarC_pos : (0 : ℚ) < hbarC :=
  mul_pos hbarApprox_pos speedOfLight_pos

/-! ### Shared discrete lattice floor (both gravity and EM hypotheses) -/

/-- Dimensionless discrete height \(\varepsilon_N = 16/(3N^2)\).
Used by `NewtonFromLight` (\(G_{\mathrm{hyp}}\)) and `CoulombFromDual`
(\(\alpha_{\mathrm{hyp}}\)); not derived from the dual-rotor algebra. -/
def epsN (N : ℕ) : ℚ := 16 / (3 * (N : ℚ) ^ 2)

theorem epsN_pos {N : ℕ} (hN : 0 < N) : (0 : ℚ) < epsN N := by
  unfold epsN
  have : (0 : ℚ) < (N : ℚ) := Nat.cast_pos.mpr hN
  exact div_pos (by norm_num) (mul_pos (by norm_num) (pow_pos this 2))

/-! ### Electromagnetism (external inputs + π-free algebra) -/

/-- Exact SI 2019 elementary charge \(e = 1.602176634\times 10^{-19}\) C. -/
def elementaryChargeMantissa : ℕ := 1602176634

def elementaryChargeScale : ℕ := 28

def elementaryCharge : ℚ :=
  elementaryChargeMantissa / (10 : ℚ) ^ elementaryChargeScale

/-- Mantissa of \(\alpha \approx 7.2973525693\times 10^{-3}\) (CODATA). -/
def fineStructureMantissa : ℕ := 72973525693

def fineStructureScale : ℕ := 13

def fineStructureApprox : ℚ :=
  fineStructureMantissa / (10 : ℚ) ^ fineStructureScale

theorem elementaryCharge_pos : (0 : ℚ) < elementaryCharge := by
  unfold elementaryCharge elementaryChargeMantissa elementaryChargeScale; norm_num

theorem fineStructureApprox_pos : (0 : ℚ) < fineStructureApprox := by
  unfold fineStructureApprox fineStructureMantissa fineStructureScale; norm_num

/-- Electromagnetic pair scale \(ke^{2}=\alpha\hbar c\) (J·m).
The single observational definition of the force scale. -/
def coulombScale : ℚ := fineStructureApprox * hbarC

/-- Coulomb prefactor \(k = \alpha\,\hbar c / e^2\) (N·m²/C²). -/
def coulombKApprox : ℚ :=
  coulombScale / elementaryCharge ^ 2

theorem coulombScale_eq_k_e_sq :
    coulombKApprox * elementaryCharge ^ 2 = coulombScale := by
  unfold coulombKApprox
  field_simp [elementaryCharge_pos.ne']

/-- Bohr radius stand-in \(a_0 = \hbar / (m_e c \alpha)\) (m). -/
def bohrRadiusApprox : ℚ :=
  hbarApprox / (electronMassApprox * speedOfLight * fineStructureApprox)

/-- Hydrogen ionisation energy stand-in \(E_I = \tfrac12 m_e c^2 \alpha^2\) (J). -/
def hydrogenIonisationApprox : ℚ :=
  (1 / 2) * electronMassApprox * speedOfLight ^ 2 * fineStructureApprox ^ 2

theorem coulombScale_pos : (0 : ℚ) < coulombScale := by
  unfold coulombScale
  exact mul_pos fineStructureApprox_pos hbarC_pos

theorem coulombKApprox_pos : (0 : ℚ) < coulombKApprox := by
  unfold coulombKApprox
  exact div_pos coulombScale_pos (pow_pos elementaryCharge_pos 2)

theorem bohrRadiusApprox_pos : (0 : ℚ) < bohrRadiusApprox := by
  unfold bohrRadiusApprox
  exact div_pos hbarApprox_pos
    (mul_pos (mul_pos electronMassApprox_pos speedOfLight_pos) fineStructureApprox_pos)

theorem hydrogenIonisationApprox_pos : (0 : ℚ) < hydrogenIonisationApprox := by
  unfold hydrogenIonisationApprox
  refine mul_pos (mul_pos (mul_pos ?_ electronMassApprox_pos)
      (pow_pos speedOfLight_pos 2)) (pow_pos fineStructureApprox_pos 2)
  norm_num

/-! ### Galaxy-scale external inputs (CompactS3; not derived) -/

/-- Mantissa of \(M_\odot \approx 1.98847\times 10^{30}\) kg. -/
def solarMassMantissa : ℕ := 198847

def solarMassScale : ℕ := 5

/-- \(M_\odot\) stand-in: mantissa × \(10^{30}\) / \(10^{\mathrm{scale}}\). -/
def solarMassApprox : ℚ :=
  solarMassMantissa * (10 : ℚ) ^ 30 / (10 : ℚ) ^ solarMassScale

/-- Mantissa of \(1\,\mathrm{kpc} \approx 3.085677581\times 10^{19}\) m. -/
def kiloparsecMantissa : ℕ := 3085677581

def kiloparsecScale : ℕ := 9

def kiloparsecApprox : ℚ :=
  kiloparsecMantissa * (10 : ℚ) ^ 19 / (10 : ℚ) ^ kiloparsecScale

/-- Paper MOND acceleration \(a_0 = 1.2\times 10^{-10}\) m/s². -/
def mondAccelMantissa : ℕ := 12

def mondAccelScale : ℕ := 11

def mondAccelApprox : ℚ :=
  mondAccelMantissa / (10 : ℚ) ^ mondAccelScale

/-- Paper Milky-Way baryonic mass coefficient \(6\times 10^{10}\,M_\odot\). -/
def milkyWayMassCoeff : ℕ := 6 * 10 ^ 10

def milkyWayMassApprox : ℚ := milkyWayMassCoeff * solarMassApprox

theorem solarMassApprox_pos : (0 : ℚ) < solarMassApprox := by
  unfold solarMassApprox solarMassMantissa solarMassScale; norm_num

theorem kiloparsecApprox_pos : (0 : ℚ) < kiloparsecApprox := by
  unfold kiloparsecApprox kiloparsecMantissa kiloparsecScale; norm_num

theorem mondAccelApprox_pos : (0 : ℚ) < mondAccelApprox := by
  unfold mondAccelApprox mondAccelMantissa mondAccelScale; norm_num

theorem milkyWayMassApprox_pos : (0 : ℚ) < milkyWayMassApprox := by
  unfold milkyWayMassApprox milkyWayMassCoeff
  exact mul_pos (by norm_num) solarMassApprox_pos

/-! ### Nuclear-scale external inputs (NuclearLayer; not derived) -/

/-- Exact SI femtometer \(1\,\mathrm{fm} = 10^{-15}\) m. -/
def femtometerApprox : ℚ := 1 / (10 : ℚ) ^ 15

/-- \(1\,\mathrm{MeV} = 10^6 e\) joules (2019 SI elementary charge). -/
def MeVApprox : ℚ :=
  elementaryCharge * (10 : ℚ) ^ 6

/-- \(ke^{2}=\alpha\hbar c\) in MeV·fm. Same product as `coulombScale`. -/
def coulombMeVFm : ℚ :=
  coulombScale / (MeVApprox * femtometerApprox)

/-- Numerator of `coulombMeVFm` after clearing powers of ten. -/
def coulombMeVFm_num : ℕ :=
  fineStructureMantissa * hbarMantissa * speedOfLightNat

/-- Denominator of `coulombMeVFm` after clearing powers of ten. -/
def coulombMeVFm_den : ℕ :=
  elementaryChargeMantissa * 10 ^ 19

theorem coulombMeVFm_eq_num_div_den :
    coulombMeVFm = (coulombMeVFm_num : ℚ) / coulombMeVFm_den := by
  unfold coulombMeVFm coulombScale hbarC hbarApprox MeVApprox femtometerApprox
    fineStructureApprox elementaryCharge
  unfold coulombMeVFm_num coulombMeVFm_den
  unfold fineStructureMantissa fineStructureScale hbarMantissa hbarScale
    speedOfLight speedOfLightNat elementaryChargeMantissa elementaryChargeScale
  field_simp
  ring

private theorem coulombMeVFm_den_pos : (0 : ℚ) < (coulombMeVFm_den : ℚ) := by
  unfold coulombMeVFm_den elementaryChargeMantissa
  norm_num

/-- On the SI stand-ins, \(1.439964 < \alpha\hbar c < 1.439965\) MeV·fm. -/
theorem coulombMeVFm_bounds :
    (1439964 : ℚ) / 10 ^ 6 < coulombMeVFm ∧
      coulombMeVFm < (1439965 : ℚ) / 10 ^ 6 := by
  rw [coulombMeVFm_eq_num_div_den]
  have hden := coulombMeVFm_den_pos
  constructor
  · have hnat : 1439964 * coulombMeVFm_den < coulombMeVFm_num * 10 ^ 6 := by
      unfold coulombMeVFm_num coulombMeVFm_den fineStructureMantissa
        hbarMantissa speedOfLightNat elementaryChargeMantissa
      native_decide
    rw [div_lt_div_iff₀ (by norm_num) hden]
    exact_mod_cast hnat
  · have hnat : coulombMeVFm_num * 10 ^ 6 < 1439965 * coulombMeVFm_den := by
      unfold coulombMeVFm_num coulombMeVFm_den fineStructureMantissa
        hbarMantissa speedOfLightNat elementaryChargeMantissa
      native_decide
    rw [div_lt_div_iff₀ hden (by norm_num)]
    exact_mod_cast hnat

theorem coulombMeVFm_pos : (0 : ℚ) < coulombMeVFm :=
  lt_trans (by norm_num) coulombMeVFm_bounds.1

/-- Mantissa of charged-pion mass \(\approx 139.57039\) MeV/\(c^2\). -/
def pionMassMeVMantissa : ℕ := 13957039

def pionMassMeVScale : ℕ := 5

def pionMassMeVApprox : ℚ :=
  pionMassMeVMantissa / (10 : ℚ) ^ pionMassMeVScale

/-- Mantissa of proton mass \(\approx 938.272088\) MeV/\(c^2\) (CODATA-style). -/
def protonMassMeVMantissa : ℕ := 938272088

def protonMassMeVScale : ℕ := 6

def protonMassMeVApprox : ℚ :=
  protonMassMeVMantissa / (10 : ℚ) ^ protonMassMeVScale

/-- Empirical nuclear saturation density \(n_0 = 0.16\,\mathrm{fm}^{-3}\). -/
def saturationDensityFm3Mantissa : ℕ := 16

def saturationDensityFm3Scale : ℕ := 2

def saturationDensityFm3Approx : ℚ :=
  saturationDensityFm3Mantissa / (10 : ℚ) ^ saturationDensityFm3Scale

/-- Empirical nuclear radius coefficient \(r_0 = 1.2\) fm. -/
def nuclearRadiusCoeffFmMantissa : ℕ := 12

def nuclearRadiusCoeffFmScale : ℕ := 1

def nuclearRadiusCoeffFmApprox : ℚ :=
  nuclearRadiusCoeffFmMantissa / (10 : ℚ) ^ nuclearRadiusCoeffFmScale

/-- Empirical binding energy per nucleon near \(^{56}\mathrm{Fe}\): \(8.8\) MeV. -/
def bindingEnergyPerNucleonMeVMantissa : ℕ := 88

def bindingEnergyPerNucleonMeVScale : ℕ := 1

def bindingEnergyPerNucleonMeVApprox : ℚ :=
  bindingEnergyPerNucleonMeVMantissa /
    (10 : ℚ) ^ bindingEnergyPerNucleonMeVScale

/-- Optical-model well depth stand-in \(45\) MeV (external; not BE/\(A\)). -/
def nuclearWellDepthMeVApprox : ℚ := 45

/-! ### Nucleon-nucleon sign radii and charge radii (external) -/

/-- A separation inside the repulsive core. The quoted core scale is
`1/2` fm; `2/5` fm lies strictly inside it. -/
def nnCoreInteriorFm : ℚ := 2 / 5

/-- Quoted repulsive-core scale, `1/2` fm. -/
def nnCoreScaleFm : ℚ := 1 / 2

/-- Inner edge of the attractive interval of a realistic nucleon-nucleon
potential, `1` fm. -/
def nnAttractionRadiusFm : ℚ := 1

/-- Angeli--Marinova lower edge: central value minus the quoted uncertainty. -/
def deuteronChargeRadiusFmLower : ℚ := 21333 / 10000

def he4ChargeRadiusFmLower : ℚ := 16727 / 10000

def oxygen16ChargeRadiusFmLower : ℚ := 26939 / 10000

def calcium40ChargeRadiusFmLower : ℚ := 34757 / 10000

def calcium48ChargeRadiusFmLower : ℚ := 34751 / 10000

def lead208ChargeRadiusFmLower : ℚ := 54999 / 10000

theorem femtometerApprox_pos : (0 : ℚ) < femtometerApprox := by
  unfold femtometerApprox; norm_num

theorem MeVApprox_pos : (0 : ℚ) < MeVApprox := by
  unfold MeVApprox
  exact mul_pos elementaryCharge_pos (by norm_num)

theorem pionMassMeVApprox_pos : (0 : ℚ) < pionMassMeVApprox := by
  unfold pionMassMeVApprox pionMassMeVMantissa pionMassMeVScale; norm_num

theorem protonMassMeVApprox_pos : (0 : ℚ) < protonMassMeVApprox := by
  unfold protonMassMeVApprox protonMassMeVMantissa protonMassMeVScale; norm_num

theorem saturationDensityFm3Approx_pos :
    (0 : ℚ) < saturationDensityFm3Approx := by
  unfold saturationDensityFm3Approx saturationDensityFm3Mantissa
    saturationDensityFm3Scale
  norm_num

theorem nuclearRadiusCoeffFmApprox_pos :
    (0 : ℚ) < nuclearRadiusCoeffFmApprox := by
  unfold nuclearRadiusCoeffFmApprox nuclearRadiusCoeffFmMantissa
    nuclearRadiusCoeffFmScale
  norm_num

theorem bindingEnergyPerNucleonMeVApprox_pos :
    (0 : ℚ) < bindingEnergyPerNucleonMeVApprox := by
  unfold bindingEnergyPerNucleonMeVApprox bindingEnergyPerNucleonMeVMantissa
    bindingEnergyPerNucleonMeVScale
  norm_num

theorem nuclearWellDepthMeVApprox_pos :
    (0 : ℚ) < nuclearWellDepthMeVApprox := by
  unfold nuclearWellDepthMeVApprox; norm_num

theorem nnCoreInteriorFm_pos : (0 : ℚ) < nnCoreInteriorFm := by
  unfold nnCoreInteriorFm; norm_num

theorem nnCoreScaleFm_pos : (0 : ℚ) < nnCoreScaleFm := by
  unfold nnCoreScaleFm; norm_num

theorem nnAttractionRadiusFm_pos : (0 : ℚ) < nnAttractionRadiusFm := by
  unfold nnAttractionRadiusFm; norm_num

theorem chargeRadiusLower_gt_one :
    (1 : ℚ) < deuteronChargeRadiusFmLower ∧
      (1 : ℚ) < he4ChargeRadiusFmLower ∧
      (1 : ℚ) < oxygen16ChargeRadiusFmLower ∧
      (1 : ℚ) < calcium40ChargeRadiusFmLower ∧
      (1 : ℚ) < calcium48ChargeRadiusFmLower ∧
      (1 : ℚ) < lead208ChargeRadiusFmLower := by
  unfold deuteronChargeRadiusFmLower he4ChargeRadiusFmLower
    oxygen16ChargeRadiusFmLower calcium40ChargeRadiusFmLower
    calcium48ChargeRadiusFmLower lead208ChargeRadiusFmLower
  norm_num

end SI

end Gravity

end DstDiophantine
