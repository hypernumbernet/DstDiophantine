import DstDiophantine.Gravity.Rutherford
import DstDiophantine.Gravity.SI
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Both channels at once

## Paper boundary (do **not** claim)

`G`, the masses, `α`, `ℏ`, and `c` are external inputs. The windows
`ℓ_E < 387` fm and `a₀ > 52917` fm, and `λ_π < 71/50` fm, are the same
external comparisons used for the length rule. Nothing here derives a
spectrum, a binding, or a force-free radius where the two interference
factors have opposite signs.

## What is proved

An electron and a proton exert both terms at every separation. For an
unlike pair, wherever the two factors have the same sign, the two terms
point the same way and the separation-increasing force does not vanish.
At a separation above `52917` fm, read with `ℓ_E < 387` fm and
`λ_π < 71/50` fm, both phases lie in `[0, 1/40]` and both factors are
positive. The ratio of the mass term to the charge term there lies
strictly between `440/10^42` and `442/10^42`. The prefactor
`G m_e m_p/(k e²)` itself lies strictly between `4407/10^43` and
`4408/10^43`.
-/

namespace DstDiophantine

namespace Gravity

open Real SI

/-- Separation-increasing force of a massive charged pair.
`κ` is `G m₁ m₂` and `coul` is `k q₁ q₂`. -/
noncomputable def pairChannelForce (κ coul γG γE r : ℝ) : ℝ :=
  -κ / (γG * r ^ 2) + coul / (γE * r ^ 2)

theorem channel_term_ne_zero {c γ r : ℝ} (hc : c ≠ 0) (hγ : γ ≠ 0) (hr : r ≠ 0) :
    c / (γ * r ^ 2) ≠ 0 :=
  div_ne_zero hc (mul_ne_zero hγ (pow_ne_zero 2 hr))

/-- Unlike charges on a common sign: both terms point the same way.
Positive factors give two attractions; negative factors give two repulsions. -/
theorem unlike_same_sign_no_zero {κ coul γG γE r : ℝ}
    (hκ : 0 < κ) (hc : coul < 0) (hr : r ≠ 0)
    (hG : 0 < γG) (hE : 0 < γE) :
    -κ / (γG * r ^ 2) < 0 ∧ coul / (γE * r ^ 2) < 0 ∧
      pairChannelForce κ coul γG γE r < 0 := by
  have hdenG : 0 < γG * r ^ 2 := by positivity
  have hdenE : 0 < γE * r ^ 2 := by positivity
  have hm : -κ / (γG * r ^ 2) < 0 := div_neg_of_neg_of_pos (by linarith) hdenG
  have he : coul / (γE * r ^ 2) < 0 := div_neg_of_neg_of_pos hc hdenE
  refine ⟨hm, he, ?_⟩
  unfold pairChannelForce
  linarith

theorem unlike_both_negative_no_zero {κ coul γG γE r : ℝ}
    (hκ : 0 < κ) (hc : coul < 0) (hr : r ≠ 0)
    (hG : γG < 0) (hE : γE < 0) :
    0 < -κ / (γG * r ^ 2) ∧ 0 < coul / (γE * r ^ 2) ∧
      0 < pairChannelForce κ coul γG γE r := by
  have hdenG : γG * r ^ 2 < 0 := by
    have : 0 < r ^ 2 := by positivity
    exact mul_neg_of_neg_of_pos hG this
  have hdenE : γE * r ^ 2 < 0 := by
    have : 0 < r ^ 2 := by positivity
    exact mul_neg_of_neg_of_pos hE this
  have hm : 0 < -κ / (γG * r ^ 2) := div_pos_of_neg_of_neg (by linarith) hdenG
  have he : 0 < coul / (γE * r ^ 2) := div_pos_of_neg_of_neg hc hdenE
  refine ⟨hm, he, ?_⟩
  unfold pairChannelForce
  linarith

/-! ### The mass-to-charge prefactor -/

/-- `G m_e m_p / (k e²)`, using `k e² = α ℏ c`. External stand-in. -/
def electronProtonGravToCoulomb : ℚ :=
  GApprox * electronMassApprox * protonMassApprox /
    (fineStructureApprox * hbarApprox * speedOfLight)

def electronProtonGravToCoulomb_num : ℕ :=
  GMantissa * electronMassMantissa * protonMassMantissa

def electronProtonGravToCoulomb_den : ℕ :=
  10 ^ 39 * fineStructureMantissa * hbarMantissa * speedOfLightNat

theorem electronProtonGravToCoulomb_eq_num_div_den :
    electronProtonGravToCoulomb =
      (electronProtonGravToCoulomb_num : ℚ) / electronProtonGravToCoulomb_den := by
  unfold electronProtonGravToCoulomb electronProtonGravToCoulomb_num
    electronProtonGravToCoulomb_den
  unfold GApprox electronMassApprox protonMassApprox
    fineStructureApprox hbarApprox speedOfLight
  unfold GMantissa GScale electronMassMantissa electronMassScale
    protonMassMantissa protonMassScale
    fineStructureMantissa fineStructureScale
    hbarMantissa hbarScale speedOfLightNat
  field_simp
  simp only [Nat.cast_mul, Nat.cast_pow]
  ring

private theorem electronProtonGravToCoulomb_den_pos :
    (0 : ℚ) < electronProtonGravToCoulomb_den := by
  unfold electronProtonGravToCoulomb_den fineStructureMantissa hbarMantissa
    speedOfLightNat
  norm_num

theorem electronProtonGravToCoulomb_bounds :
    (4407 / 10 ^ 43 : ℚ) < electronProtonGravToCoulomb ∧
      electronProtonGravToCoulomb < 4408 / 10 ^ 43 := by
  rw [electronProtonGravToCoulomb_eq_num_div_den]
  have hden := electronProtonGravToCoulomb_den_pos
  constructor
  · have hnat : 4407 * electronProtonGravToCoulomb_den <
        electronProtonGravToCoulomb_num * 10 ^ 43 := by
      unfold electronProtonGravToCoulomb_num electronProtonGravToCoulomb_den
        GMantissa electronMassMantissa protonMassMantissa
        fineStructureMantissa hbarMantissa speedOfLightNat
      norm_num
    rw [div_lt_div_iff₀ (by norm_num) hden]
    exact_mod_cast hnat
  · have hnat : electronProtonGravToCoulomb_num * 10 ^ 43 <
        4408 * electronProtonGravToCoulomb_den := by
      unfold electronProtonGravToCoulomb_num electronProtonGravToCoulomb_den
        GMantissa electronMassMantissa protonMassMantissa
        fineStructureMantissa hbarMantissa speedOfLightNat
      norm_num
    rw [div_lt_div_iff₀ hden (by norm_num)]
    exact_mod_cast hnat

private theorem plateau_fraction_lo :
    (440 : ℚ) / 10 ^ 42 < (4407 / 10 ^ 43) * (15987 / 16000) := by
  norm_num

private theorem plateau_fraction_hi :
    (4408 / 10 ^ 43) * ((16000 : ℚ) / 15987) < 442 / 10 ^ 42 := by
  norm_num

/-! ### Plateau at the Bohr radius -/

theorem phase_le_one_fortieth {ℓ r : ℝ} (hℓ0 : 0 < ℓ) (hℓ : ℓ < 387) (hr : 52917 < r) :
    0 ≤ ℓ / (2 * r) ∧ ℓ / (2 * r) ≤ 1 / 40 := by
  have hr0 : 0 < r := by linarith
  refine ⟨div_nonneg hℓ0.le (by positivity), ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- On `0 ≤ x ≤ 1/40`, `15987/16000 ≤ γ_s(x) ≤ 1`. -/
theorem gammaWindow_of_le_one_fortieth {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 40) :
    (15987 / 16000 : ℝ) ≤ gammaSEqual x ∧ gammaSEqual x ≤ 1 := by
  have h := invGamma_dev_le hx0 hx1
  have hone : (1 : ℝ) ≤ 1 / gammaSEqual x := by linarith [h.1]
  have hup : 1 / gammaSEqual x ≤ (16000 : ℝ) / 15987 := by
    have : (1 : ℝ) + 13 / 15987 = 16000 / 15987 := by norm_num
    linarith [h.2]
  have hpos : 0 < gammaSEqual x := by
    have hinv : 0 < 1 / gammaSEqual x := by linarith
    exact inv_pos.mp (by simpa [one_div] using hinv)
  refine ⟨?_, (one_le_div hpos).mp hone⟩
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 16000)]
  have hmul : (1 : ℝ) ≤ (16000 / 15987) * gammaSEqual x := (div_le_iff₀ hpos).mp hup
  have hscaled := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 15987)
  have hr : 15987 * ((16000 / 15987) * gammaSEqual x) = 16000 * gammaSEqual x := by
    field_simp
  linarith

/-- At a hydrogenic separation the mass term is a fraction of the charge term
strictly between `4.40×10⁻⁴⁰` and `4.42×10⁻⁴⁰`. -/
theorem bohr_mass_fraction {ℓE ℓG a : ℝ}
    (hE0 : 0 < ℓE) (hE : ℓE < 387)
    (hG0 : 0 < ℓG) (hG : ℓG < 71 / 50)
    (ha : 52917 < a) :
    (440 : ℝ) / 10 ^ 42 <
        (electronProtonGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) / gammaSEqual (ℓG / (2 * a)) ∧
      (electronProtonGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) / gammaSEqual (ℓG / (2 * a)) <
        442 / 10 ^ 42 := by
  have hGlt : ℓG < 387 := by
    have : (71 / 50 : ℝ) < 387 := by norm_num
    linarith
  have hEa := phase_le_one_fortieth hE0 hE ha
  have hGa := phase_le_one_fortieth hG0 hGlt ha
  have hEw := gammaWindow_of_le_one_fortieth hEa.1 hEa.2
  have hGw := gammaWindow_of_le_one_fortieth hGa.1 hGa.2
  set γE : ℝ := gammaSEqual (ℓE / (2 * a))
  set γG : ℝ := gammaSEqual (ℓG / (2 * a))
  have hEp : 0 < γE := lt_of_lt_of_le (by norm_num) hEw.1
  have hGp : 0 < γG := lt_of_lt_of_le (by norm_num) hGw.1
  set ρ : ℝ := (electronProtonGravToCoulomb : ℝ)
  have hρlo : (4407 / 10 ^ 43 : ℝ) < ρ := by
    refine lt_of_eq_of_lt ?_ (Rat.cast_lt.mpr electronProtonGravToCoulomb_bounds.1)
    norm_num
  have hρhi : ρ < (4408 / 10 ^ 43 : ℝ) := by
    refine lt_of_lt_of_eq (Rat.cast_lt.mpr electronProtonGravToCoulomb_bounds.2) ?_
    norm_num
  have hρpos : 0 < ρ := by
    have : (0 : ℝ) < 4407 / 10 ^ 43 := by norm_num
    linarith
  have hdiv_hi : γE / γG ≤ (16000 : ℝ) / 15987 := by
    rw [div_le_div_iff₀ hGp (by norm_num)]
    have hGscaled : (15987 : ℝ) ≤ γG * 16000 := by
      have := hGw.1
      rwa [div_le_iff₀ (by norm_num : (0 : ℝ) < 16000)] at this
    nlinarith [hEw.2]
  have hdiv_lo : (15987 : ℝ) / 16000 ≤ γE / γG := by
    rw [div_le_div_iff₀ (by norm_num) hGp]
    have hEscaled : (15987 : ℝ) ≤ γE * 16000 := by
      have := hEw.1
      rwa [div_le_iff₀ (by norm_num : (0 : ℝ) < 16000)] at this
    nlinarith [hGw.2]
  have hloR : (440 : ℝ) / 10 ^ 42 < (4407 / 10 ^ 43) * (15987 / 16000) := by
    refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq (Rat.cast_lt.mpr plateau_fraction_lo) ?_)
    · norm_num
    · norm_num
  have hhiR : (4408 / 10 ^ 43 : ℝ) * ((16000 : ℝ) / 15987) < 442 / 10 ^ 42 := by
    refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq (Rat.cast_lt.mpr plateau_fraction_hi) ?_)
    · norm_num
    · norm_num
  have hmpos : 0 < (15987 : ℝ) / 16000 := by norm_num
  have hMpos : 0 < (16000 : ℝ) / 15987 := by norm_num
  constructor
  · have h1 : (4407 / 10 ^ 43) * (15987 / 16000) < ρ * (15987 / 16000) :=
      mul_lt_mul_of_pos_right hρlo hmpos
    have h2 : ρ * (15987 / 16000) ≤ ρ * (γE / γG) :=
      mul_le_mul_of_nonneg_left hdiv_lo hρpos.le
    have hprod : ρ * (γE / γG) = ρ * γE / γG := by ring
    linarith
  · have h1 : ρ * (γE / γG) ≤ ρ * (16000 / 15987) :=
      mul_le_mul_of_nonneg_left hdiv_hi hρpos.le
    have h2 : ρ * ((16000 : ℝ) / 15987) < (4408 / 10 ^ 43) * (16000 / 15987) :=
      mul_lt_mul_of_pos_right hρhi hMpos
    have hprod : ρ * (γE / γG) = ρ * γE / γG := by ring
    linarith

end Gravity

end DstDiophantine
