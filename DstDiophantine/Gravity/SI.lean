import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# SI / CODATA bookkeeping for the DST gravity chart

**External inputs only.** These rationals are *not* derived from the double
spacetime algebra. The DST action writes \(G\) as a coupling constant in
\(S = (c^4/(16\pi G))\int J\,d^4x\); the present module records CODATA-style
placeholders so that exploratory numerical comparisons in `NewtonFromLight`
can be machine-checked without `Float`.

Units (SI): \(c\) in m/s, \(\hbar\) in J·s, \(G\) in m³·kg⁻¹·s⁻², masses in kg.

Mantissas are exposed as `ℕ` so cleared-denominator witnesses can reuse them
without duplicating decimal literals.
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

end SI

end Gravity

end DstDiophantine
