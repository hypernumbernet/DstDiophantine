import DstDiophantine.Gravity.Rutherford
import DstDiophantine.Gravity.SI
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Both channels at once

Where the two interference factors share a sign, the separation-increasing
force of an unlike pair does not vanish. The vanishing condition itself does
not mention the separation: once the two interference factors are fixed, either
every positive radius is a zero or none is. \(G\), the masses, \(\alpha\),
\(\hbar\), and \(c\) are inputs; no spectrum, binding, or opposite-sign
force-free radius is derived.
-/

namespace DstDiophantine

namespace Gravity

open Real SI

/-- Separation-increasing force of a massive charged pair. `κ` is `G m₁ m₂` and `coul` is
`k q₁ q₂`. -/
noncomputable def pairChannelForce (κ coul γG γE r : ℝ) : ℝ :=
  -κ / (γG * r ^ 2) + coul / (γE * r ^ 2)

theorem channel_term_ne_zero {c γ r : ℝ} (hc : c ≠ 0) (hγ : γ ≠ 0) (hr : r ≠ 0) :
    c / (γ * r ^ 2) ≠ 0 :=
  div_ne_zero hc (mul_ne_zero hγ (pow_ne_zero 2 hr))

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

/-- Vanishing does not depend on the separation. A zero of `pairChannelForce` therefore does not
select a radius. -/
theorem pairChannelForce_eq_zero_iff {κ coul γG γE r : ℝ}
    (hr : r ≠ 0) (hG : γG ≠ 0) (hE : γE ≠ 0) :
    pairChannelForce κ coul γG γE r = 0 ↔ κ * γE = coul * γG := by
  unfold pairChannelForce
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hdenG : γG * r ^ 2 ≠ 0 := mul_ne_zero hG hr2
  have hdenE : γE * r ^ 2 ≠ 0 := mul_ne_zero hE hr2
  have hfac : -κ * (γE * r ^ 2) + γG * r ^ 2 * coul =
      (-κ * γE + coul * γG) * r ^ 2 := by ring
  rw [div_add_div _ _ hdenG hdenE, div_eq_zero_iff, hfac]
  constructor
  · intro h
    rcases h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact absurd h hr2
    · exact absurd h (mul_ne_zero hdenG hdenE)
  · intro h
    refine Or.inl ?_
    have hzero : -κ * γE + coul * γG = 0 := by linarith
    rw [hzero, zero_mul]

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

/-- `G m_e m_p / (k e²)`, with `k e² = α ℏ c`. -/
def electronProtonGravToCoulomb : ℚ :=
  GApprox * electronMassApprox * protonMassApprox / coulombScale

theorem electronProtonGravToCoulomb_scale :
    fineStructureApprox * hbarApprox * speedOfLight = coulombScale := by
  unfold coulombScale hbarC
  ring

def electronProtonGravToCoulomb_num : ℕ :=
  GMantissa * electronMassMantissa * protonMassMantissa

def electronProtonGravToCoulomb_den : ℕ :=
  10 ^ 39 * fineStructureMantissa * hbarMantissa * speedOfLightNat

theorem electronProtonGravToCoulomb_eq_num_div_den :
    electronProtonGravToCoulomb =
      (electronProtonGravToCoulomb_num : ℚ) / electronProtonGravToCoulomb_den := by
  unfold electronProtonGravToCoulomb electronProtonGravToCoulomb_num
    electronProtonGravToCoulomb_den
  unfold GApprox electronMassApprox protonMassApprox coulombScale hbarC
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

/-- \(ke^{2}/(G m_p^{2})\) with the same observational scale. -/
def protonCoulombOverNewton : ℚ :=
  coulombScale / (GApprox * protonMassApprox ^ 2)

/-- \(G m_p^{2}/(ke^{2})\). -/
def protonNewtonOverCoulomb : ℚ :=
  GApprox * protonMassApprox ^ 2 / coulombScale

def protonCoulombOverNewton_num : ℕ :=
  fineStructureMantissa * hbarMantissa * speedOfLightNat

def protonCoulombOverNewton_den : ℕ :=
  GMantissa * protonMassMantissa ^ 2

theorem protonCoulombOverNewton_eq_num_div_den :
    protonCoulombOverNewton =
      (protonCoulombOverNewton_num : ℚ) * 10 ^ 36 / protonCoulombOverNewton_den := by
  unfold protonCoulombOverNewton coulombScale hbarC hbarApprox fineStructureApprox
    GApprox protonMassApprox protonCoulombOverNewton_num protonCoulombOverNewton_den
  unfold fineStructureMantissa fineStructureScale hbarMantissa hbarScale
    speedOfLight speedOfLightNat GMantissa GScale protonMassMantissa protonMassScale
  field_simp
  ring

theorem protonNewtonOverCoulomb_eq_num_div_den :
    protonNewtonOverCoulomb =
      (protonCoulombOverNewton_den : ℚ) /
        ((protonCoulombOverNewton_num : ℚ) * 10 ^ 36) := by
  unfold protonNewtonOverCoulomb coulombScale hbarC hbarApprox fineStructureApprox
    GApprox protonMassApprox protonCoulombOverNewton_num protonCoulombOverNewton_den
  unfold fineStructureMantissa fineStructureScale hbarMantissa hbarScale
    speedOfLight speedOfLightNat GMantissa GScale protonMassMantissa protonMassScale
  field_simp
  ring

theorem proton_scales_inv :
    protonCoulombOverNewton * protonNewtonOverCoulomb = 1 := by
  unfold protonCoulombOverNewton protonNewtonOverCoulomb
  field_simp [coulombScale_pos.ne', GApprox_pos.ne', protonMassApprox_pos.ne']

private theorem protonCoulombOverNewton_den_pos :
    (0 : ℚ) < protonCoulombOverNewton_den := by
  unfold protonCoulombOverNewton_den GMantissa protonMassMantissa
  norm_num

theorem protonCoulombOverNewton_bounds :
    (12355 / 10000 : ℚ) * 10 ^ 36 < protonCoulombOverNewton ∧
      protonCoulombOverNewton < (12356 / 10000) * 10 ^ 36 := by
  rw [protonCoulombOverNewton_eq_num_div_den]
  have hden := protonCoulombOverNewton_den_pos
  constructor
  · rw [lt_div_iff₀ hden]
    have hnat : 12355 * protonCoulombOverNewton_den <
        protonCoulombOverNewton_num * 10 ^ 4 := by
      unfold protonCoulombOverNewton_num protonCoulombOverNewton_den
        fineStructureMantissa hbarMantissa speedOfLightNat GMantissa protonMassMantissa
      native_decide
    have hcast : (12355 : ℚ) * protonCoulombOverNewton_den <
        (protonCoulombOverNewton_num : ℚ) * 10 ^ 4 := by exact_mod_cast hnat
    have hmul := mul_lt_mul_of_pos_left hcast
      (by norm_num : (0 : ℚ) < 10 ^ 32)
    have hl : (12355 : ℚ) * protonCoulombOverNewton_den * 10 ^ 32 =
        (12355 / 10000) * 10 ^ 36 * protonCoulombOverNewton_den := by ring
    have hr : (protonCoulombOverNewton_num : ℚ) * 10 ^ 4 * 10 ^ 32 =
        (protonCoulombOverNewton_num : ℚ) * 10 ^ 36 := by ring
    linarith
  · rw [div_lt_iff₀ hden]
    have hnat : protonCoulombOverNewton_num * 10 ^ 4 <
        12356 * protonCoulombOverNewton_den := by
      unfold protonCoulombOverNewton_num protonCoulombOverNewton_den
        fineStructureMantissa hbarMantissa speedOfLightNat GMantissa protonMassMantissa
      native_decide
    have hcast : (protonCoulombOverNewton_num : ℚ) * 10 ^ 4 <
        (12356 : ℚ) * protonCoulombOverNewton_den := by exact_mod_cast hnat
    have hmul := mul_lt_mul_of_pos_left hcast
      (by norm_num : (0 : ℚ) < 10 ^ 32)
    have hl : (protonCoulombOverNewton_num : ℚ) * 10 ^ 4 * 10 ^ 32 =
        (protonCoulombOverNewton_num : ℚ) * 10 ^ 36 := by ring
    have hr : (12356 : ℚ) * protonCoulombOverNewton_den * 10 ^ 32 =
        (12356 / 10000) * 10 ^ 36 * protonCoulombOverNewton_den := by ring
    linarith

theorem protonNewtonOverCoulomb_bounds :
    (8093 : ℚ) / 10 ^ 40 < protonNewtonOverCoulomb ∧
      protonNewtonOverCoulomb < 8094 / 10 ^ 40 := by
  rw [protonNewtonOverCoulomb_eq_num_div_den]
  have hden : (0 : ℚ) < (protonCoulombOverNewton_num : ℚ) * 10 ^ 36 := by
    unfold protonCoulombOverNewton_num fineStructureMantissa hbarMantissa
      speedOfLightNat
    positivity
  constructor
  · rw [lt_div_iff₀ hden]
    have hclear : (8093 : ℚ) / 10 ^ 40 *
          ((protonCoulombOverNewton_num : ℚ) * 10 ^ 36) =
        (8093 : ℚ) * protonCoulombOverNewton_num / 10 ^ 4 := by ring
    rw [hclear, div_lt_iff₀ (by norm_num)]
    have hnat : 8093 * protonCoulombOverNewton_num <
        protonCoulombOverNewton_den * 10 ^ 4 := by
      unfold protonCoulombOverNewton_num protonCoulombOverNewton_den
        fineStructureMantissa hbarMantissa speedOfLightNat GMantissa protonMassMantissa
      native_decide
    exact_mod_cast hnat
  · rw [div_lt_iff₀ hden]
    have hclear : (8094 : ℚ) / 10 ^ 40 *
          ((protonCoulombOverNewton_num : ℚ) * 10 ^ 36) =
        (8094 : ℚ) * protonCoulombOverNewton_num / 10 ^ 4 := by ring
    rw [hclear, lt_div_iff₀ (by norm_num)]
    have hnat : protonCoulombOverNewton_den * 10 ^ 4 <
        8094 * protonCoulombOverNewton_num := by
      unfold protonCoulombOverNewton_num protonCoulombOverNewton_den
        fineStructureMantissa hbarMantissa speedOfLightNat GMantissa protonMassMantissa
      native_decide
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
