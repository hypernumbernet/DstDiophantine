import DstDiophantine.Gravity.ElectronLength
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The alpha–gold head-on distance and the electromagnetic length

## Paper boundary (do **not** claim)

The Coulomb constant `k e² = 1.439964` MeV fm, the alpha energy `7.69` MeV,
and the gold charge `79` are external inputs. The head-on distance is the
laboratory-frame Coulomb value `2 Z k e² / E`. No cross section, deflection,
or half-life is computed here; those are numerical results of the paper.

## What is proved

* The head-on distance lies in `(29, 30)` fm.
* Repulsion in the outer well at that distance forces `ℓ < 57` fm.
* The first node of `ℏ/(m_e c)` lies outside that distance, so under that
  length the distance is not in the outer well.
-/

namespace DstDiophantine

namespace Gravity

open Real

/-- `k e²` in MeV fm (external stand-in). -/
def coulombMeVFm : ℚ := 1439964 / 1000000

/-- Alpha kinetic energy of the Geiger–Marsden source, `7.69` MeV (external). -/
def alphaGoldEnergyMeV : ℚ := 769 / 100

/-- Gold nuclear charge (external). -/
def goldCharge : ℚ := 79

/-- Laboratory-frame Coulomb head-on distance `2 Z k e² / E`, in fm. -/
def alphaGoldClosestFm : ℚ := 2 * goldCharge * coulombMeVFm / alphaGoldEnergyMeV

theorem alphaGoldClosest_window :
    (29 : ℚ) < alphaGoldClosestFm ∧ alphaGoldClosestFm < 30 := by
  unfold alphaGoldClosestFm goldCharge coulombMeVFm alphaGoldEnergyMeV
  constructor <;> norm_num

theorem alphaGoldClosest_pos : (0 : ℚ) < alphaGoldClosestFm :=
  lt_trans (by norm_num) alphaGoldClosest_window.1

/-- Repulsion in the outer well at the head-on distance forces `ℓ < 57` fm. -/
theorem rutherford_outerWell_ell_lt {ℓ : ℝ}
    (hwell : ℓ / (2 * resonanceRoot1) < (alphaGoldClosestFm : ℝ)) :
    ℓ < 57 := by
  have hpos : (0 : ℝ) < (alphaGoldClosestFm : ℝ) := by
    exact_mod_cast alphaGoldClosest_pos
  have h := outerWell_ell_lt_nineteen_tenths hpos hwell
  have h30 : (alphaGoldClosestFm : ℝ) < 30 := by
    exact_mod_cast alphaGoldClosest_window.2
  linarith

/-- The head-on distance in metres lies strictly below `2032×10⁻¹⁶` m. -/
theorem alphaGoldClosest_meter_lt :
    (alphaGoldClosestFm : ℝ) / 10 ^ 15 < (2032 : ℝ) / 10 ^ 16 := by
  have h30 : (alphaGoldClosestFm : ℝ) < 30 := by
    exact_mod_cast alphaGoldClosest_window.2
  have hp : (0 : ℝ) < 10 ^ 16 := by positivity
  rw [div_lt_div_iff₀ (by positivity) hp]
  calc (alphaGoldClosestFm : ℝ) * 10 ^ 16
      < 30 * 10 ^ 16 := mul_lt_mul_of_pos_right h30 hp
    _ < 2032 * 10 ^ 15 := by norm_num

/-- The first node of `ℏ/(m_e c)` lies outside the head-on distance. -/
theorem ellRep_node_beyond_alphaGold :
    (alphaGoldClosestFm : ℝ) / 10 ^ 15 < (ellRep : ℝ) / (2 * resonanceRoot1) :=
  lt_trans alphaGoldClosest_meter_lt ellRep_node_meter_window.1

/-- Under `ℏ/(m_e c)` the head-on distance is not in the outer well. -/
theorem ellRep_not_outerWell_alphaGold :
    ¬ ((ellRep : ℝ) / (2 * resonanceRoot1) < (alphaGoldClosestFm : ℝ) / 10 ^ 15) := by
  intro h
  have := ellRep_node_beyond_alphaGold
  linarith

/-- `ℏ/(m_e c)` lies above the alpha–gold cap `57` fm. -/
theorem ellRep_gt_rutherford_cap : (57 : ℝ) / 10 ^ 15 < (ellRep : ℝ) := by
  have h : ((3861 : ℚ) / 10 ^ 16 : ℝ) < ((ellRep : ℚ) : ℝ) := by
    exact_mod_cast ellRep_meter_window.1
  have h' : (57 : ℝ) / 10 ^ 15 < (3861 : ℝ) / 10 ^ 16 := by norm_num
  have h'' : (3861 : ℝ) / 10 ^ 16 < (ellRep : ℝ) := by
    simpa [Rat.cast_div, Rat.cast_pow, Nat.cast_ofNat] using h
  linarith

end Gravity

end DstDiophantine
