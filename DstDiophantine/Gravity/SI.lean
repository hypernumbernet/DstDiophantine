import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# SI / CODATA bookkeeping for the DST gravity chart

**External inputs only.** These rationals are *not* derived from the double
spacetime algebra. The DST action writes \(G\) as a coupling constant in
\(S = (c^4/(16\pi G))\int J\,d^4x\); the present module records CODATA-style
placeholders so that exploratory numerical comparisons in `NewtonFromLight`,
`CoulombFromDual`, and `ElectronShell` can be machine-checked without `Float`.

Units (SI): \(c\) in m/s, \(\hbar\) in J·s, \(G\) in m³·kg⁻¹·s⁻², masses in kg,
elementary charge in C. Fine-structure \(\alpha\) is dimensionless.

Mantissas are exposed as `ℕ` so cleared-denominator witnesses can reuse them
without duplicating decimal literals.

Electromagnetic stand-ins avoid \(\pi\) (no independent \(\varepsilon_0\) or
\(R_\infty\)): Coulomb \(k=\alpha\,\hbar c/e^2\), Bohr \(a_0=\hbar/(m_e c\alpha)\),
ionisation \(E_I=\tfrac12 m_e c^2\alpha^2\).

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

/-- Coulomb constant stand-in \(k = \alpha\,\hbar c / e^2\) (N·m²/C²). -/
def coulombKApprox : ℚ :=
  fineStructureApprox * hbarC / elementaryCharge ^ 2

/-- Bohr radius stand-in \(a_0 = \hbar / (m_e c \alpha)\) (m). -/
def bohrRadiusApprox : ℚ :=
  hbarApprox / (electronMassApprox * speedOfLight * fineStructureApprox)

/-- Hydrogen ionisation energy stand-in \(E_I = \tfrac12 m_e c^2 \alpha^2\) (J). -/
def hydrogenIonisationApprox : ℚ :=
  (1 / 2) * electronMassApprox * speedOfLight ^ 2 * fineStructureApprox ^ 2

theorem coulombKApprox_pos : (0 : ℚ) < coulombKApprox := by
  unfold coulombKApprox
  exact div_pos (mul_pos fineStructureApprox_pos hbarC_pos)
    (pow_pos elementaryCharge_pos 2)

theorem bohrRadiusApprox_pos : (0 : ℚ) < bohrRadiusApprox := by
  unfold bohrRadiusApprox
  exact div_pos hbarApprox_pos
    (mul_pos (mul_pos electronMassApprox_pos speedOfLight_pos) fineStructureApprox_pos)

theorem hydrogenIonisationApprox_pos : (0 : ℚ) < hydrogenIonisationApprox := by
  unfold hydrogenIonisationApprox
  refine mul_pos (mul_pos (mul_pos ?_ electronMassApprox_pos)
      (pow_pos speedOfLight_pos 2)) (pow_pos fineStructureApprox_pos 2)
  norm_num

end SI

end Gravity

end DstDiophantine
