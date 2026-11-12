import DstDiophantine.Gravity.BothChannels
import DstDiophantine.Gravity.ElectronOrbit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Electron exclusion: electric repulsion, gravitational attraction, and a short pole

## Paper boundary (do **not** claim)

`G`, the masses, `α`, `ℏ`, and `c` are external inputs. The windows
`ℓ_E < 387` fm, `ℓ_G < 19/10` fm, `a₀ > 52917` fm, and `1/2 < r₁ < 1` fm
are external comparisons. Nothing here derives a spectrum, a binding, or
the spin-statistics theorem. The reading of the gravitational pole as
exclusion is not a theorem of this file.

## What is proved

* `2.400×10⁻⁴³ < G m_e²/(k e²) < 2.401×10⁻⁴³`.
* Above the Bohr radius, with those length windows, two electrons repel
  electrically and attract gravitationally. The gravitational term is a
  fraction of the electric term strictly between `2398/10⁴⁶` and
  `2404/10⁴⁶`, and the separation-increasing force stays positive.
* Inside the first node, while the phase is still below `1`, that outward
  gravitational force exceeds the scale `k e²/r²` only for a fractional
  depth `ε < 1.64×10⁻⁴³`. Such a depth exists.
* For `0 < r₁ < 1`, that depth is a separation smaller than a radius above
  `52917` by more than `3×10⁴⁷`.
-/

namespace DstDiophantine

namespace Gravity

open Real SI Set

/-! ### The electron–electron prefactor -/

/-- `G m_e² / (k e²)`, with `k e² = α ℏ c`. -/
def electronElectronGravToCoulomb : ℚ :=
  GApprox * electronMassApprox ^ 2 / coulombScale

def electronElectronGravToCoulomb_num : ℕ :=
  GMantissa * electronMassMantissa ^ 2

def electronElectronGravToCoulomb_den : ℕ :=
  10 ^ 42 * fineStructureMantissa * hbarMantissa * speedOfLightNat

theorem electronElectronGravToCoulomb_eq_num_div_den :
    electronElectronGravToCoulomb =
      (electronElectronGravToCoulomb_num : ℚ) / electronElectronGravToCoulomb_den := by
  unfold electronElectronGravToCoulomb electronElectronGravToCoulomb_num
    electronElectronGravToCoulomb_den
  unfold GApprox electronMassApprox coulombScale hbarC
    fineStructureApprox hbarApprox speedOfLight
  unfold GMantissa GScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale
    hbarMantissa hbarScale speedOfLightNat
  field_simp
  simp only [Nat.cast_mul, Nat.cast_pow]
  ring

private theorem electronElectronGravToCoulomb_den_pos :
    (0 : ℚ) < electronElectronGravToCoulomb_den := by
  unfold electronElectronGravToCoulomb_den fineStructureMantissa hbarMantissa
    speedOfLightNat
  norm_num

theorem electronElectronGravToCoulomb_bounds :
    (2400 / 10 ^ 46 : ℚ) < electronElectronGravToCoulomb ∧
      electronElectronGravToCoulomb < 2401 / 10 ^ 46 := by
  rw [electronElectronGravToCoulomb_eq_num_div_den]
  have hden := electronElectronGravToCoulomb_den_pos
  constructor
  · have hnat : 2400 * electronElectronGravToCoulomb_den <
        electronElectronGravToCoulomb_num * 10 ^ 46 := by
      unfold electronElectronGravToCoulomb_num electronElectronGravToCoulomb_den
        GMantissa electronMassMantissa fineStructureMantissa hbarMantissa
        speedOfLightNat
      norm_num
    rw [div_lt_div_iff₀ (by norm_num) hden]
    exact_mod_cast hnat
  · have hnat : electronElectronGravToCoulomb_num * 10 ^ 46 <
        2401 * electronElectronGravToCoulomb_den := by
      unfold electronElectronGravToCoulomb_num electronElectronGravToCoulomb_den
        GMantissa electronMassMantissa fineStructureMantissa hbarMantissa
        speedOfLightNat
      norm_num
    rw [div_lt_div_iff₀ hden (by norm_num)]
    exact_mod_cast hnat

private theorem shell_fraction_lo :
    (2398 : ℚ) / 10 ^ 46 < (2400 / 10 ^ 46) * (15987 / 16000) := by
  norm_num

private theorem shell_fraction_hi :
    (2401 / 10 ^ 46 : ℚ) * ((16000 : ℚ) / 15987) < 2404 / 10 ^ 46 := by
  norm_num

/-! ### A shell separation -/

/-- Above the Bohr radius, two electrons repel electrically and attract
gravitationally, and the gravitational term is a fraction of the electric
term strictly between `2.398×10⁻⁴³` and `2.404×10⁻⁴³`. -/
theorem shell_electron_grav_fraction {ℓE ℓG a : ℝ}
    (hE0 : 0 < ℓE) (hE : ℓE < 387)
    (hG0 : 0 < ℓG) (hG : ℓG < 19 / 10)
    (ha : 52917 < a) :
    (2398 : ℝ) / 10 ^ 46 <
        (electronElectronGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) / gammaSEqual (ℓG / (2 * a)) ∧
      (electronElectronGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) / gammaSEqual (ℓG / (2 * a)) <
        2404 / 10 ^ 46 := by
  have hGlt : ℓG < 387 := by
    have : (19 / 10 : ℝ) < 387 := by norm_num
    linarith
  have hEa := phase_le_one_fortieth hE0 hE ha
  have hGa := phase_le_one_fortieth hG0 hGlt ha
  have hEw := gammaWindow_of_le_one_fortieth hEa.1 hEa.2
  have hGw := gammaWindow_of_le_one_fortieth hGa.1 hGa.2
  set γE : ℝ := gammaSEqual (ℓE / (2 * a))
  set γG : ℝ := gammaSEqual (ℓG / (2 * a))
  have hEp : 0 < γE := lt_of_lt_of_le (by norm_num) hEw.1
  have hGp : 0 < γG := lt_of_lt_of_le (by norm_num) hGw.1
  set ρ : ℝ := (electronElectronGravToCoulomb : ℝ)
  have hρlo : (2400 / 10 ^ 46 : ℝ) < ρ := by
    refine lt_of_eq_of_lt ?_ (Rat.cast_lt.mpr electronElectronGravToCoulomb_bounds.1)
    norm_num
  have hρhi : ρ < (2401 / 10 ^ 46 : ℝ) := by
    refine lt_of_lt_of_eq (Rat.cast_lt.mpr electronElectronGravToCoulomb_bounds.2) ?_
    norm_num
  have hρpos : 0 < ρ := by
    have : (0 : ℝ) < 2400 / 10 ^ 46 := by norm_num
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
  have hloR : (2398 : ℝ) / 10 ^ 46 < (2400 / 10 ^ 46) * (15987 / 16000) := by
    refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq (Rat.cast_lt.mpr shell_fraction_lo) ?_)
    · norm_num
    · norm_num
  have hhiR : (2401 / 10 ^ 46 : ℝ) * ((16000 : ℝ) / 15987) < 2404 / 10 ^ 46 := by
    refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq (Rat.cast_lt.mpr shell_fraction_hi) ?_)
    · norm_num
    · norm_num
  have hmpos : 0 < (15987 : ℝ) / 16000 := by norm_num
  have hMpos : 0 < (16000 : ℝ) / 15987 := by norm_num
  constructor
  · have h1 : (2400 / 10 ^ 46) * (15987 / 16000) < ρ * (15987 / 16000) :=
      mul_lt_mul_of_pos_right hρlo hmpos
    have h2 : ρ * (15987 / 16000) ≤ ρ * (γE / γG) :=
      mul_le_mul_of_nonneg_left hdiv_lo hρpos.le
    have hprod : ρ * (γE / γG) = ρ * γE / γG := by ring
    linarith
  · have h1 : ρ * (γE / γG) ≤ ρ * (16000 / 15987) :=
      mul_le_mul_of_nonneg_left hdiv_hi hρpos.le
    have h2 : ρ * ((16000 : ℝ) / 15987) < (2401 / 10 ^ 46) * (16000 / 15987) :=
      mul_lt_mul_of_pos_right hρhi hMpos
    have hprod : ρ * (γE / γG) = ρ * γE / γG := by ring
    linarith

/-- At that separation the electric term increases the separation, the
gravitational term decreases it, and the sum increases it. -/
theorem shell_electron_net_repels {ℓE ℓG a coul r : ℝ}
    (hE0 : 0 < ℓE) (hE : ℓE < 387)
    (hG0 : 0 < ℓG) (hG : ℓG < 19 / 10)
    (ha : 52917 < a) (hc : 0 < coul) (hr : r ≠ 0) :
    0 < coul / (gammaSEqual (ℓE / (2 * a)) * r ^ 2) ∧
      -(electronElectronGravToCoulomb : ℝ) * coul /
          (gammaSEqual (ℓG / (2 * a)) * r ^ 2) < 0 ∧
        0 < pairChannelForce
          ((electronElectronGravToCoulomb : ℝ) * coul) coul
          (gammaSEqual (ℓG / (2 * a))) (gammaSEqual (ℓE / (2 * a))) r := by
  have hfrac := shell_electron_grav_fraction hE0 hE hG0 hG ha
  set γE : ℝ := gammaSEqual (ℓE / (2 * a))
  set γG : ℝ := gammaSEqual (ℓG / (2 * a))
  set ρ : ℝ := (electronElectronGravToCoulomb : ℝ)
  have hEp : 0 < γE := by
    have hGlt : ℓG < 387 := by
      have : (19 / 10 : ℝ) < 387 := by norm_num
      linarith
    have hEa := phase_le_one_fortieth hE0 hE ha
    have hEw := gammaWindow_of_le_one_fortieth hEa.1 hEa.2
    exact lt_of_lt_of_le (by norm_num) hEw.1
  have hGp : 0 < γG := by
    have hGlt : ℓG < 387 := by
      have : (19 / 10 : ℝ) < 387 := by norm_num
      linarith
    have hGa := phase_le_one_fortieth hG0 hGlt ha
    have hGw := gammaWindow_of_le_one_fortieth hGa.1 hGa.2
    exact lt_of_lt_of_le (by norm_num) hGw.1
  have hdenE : 0 < γE * r ^ 2 := by positivity
  have hdenG : 0 < γG * r ^ 2 := by positivity
  have hfrac1 : ρ * γE / γG < 1 := by
    have : (2404 : ℝ) / 10 ^ 46 < 1 := by norm_num
    linarith [hfrac.2]
  have he : 0 < coul / (γE * r ^ 2) := div_pos hc hdenE
  have hρpos : 0 < ρ := by
    have : (0 : ℝ) < 2400 / 10 ^ 46 := by norm_num
    exact lt_trans this (by
      refine lt_of_eq_of_lt ?_ (Rat.cast_lt.mpr electronElectronGravToCoulomb_bounds.1)
      norm_num)
  have hm : -ρ * coul / (γG * r ^ 2) < 0 := by
    refine div_neg_of_neg_of_pos ?_ hdenG
    nlinarith
  have hsame : -(ρ * coul) / (γG * r ^ 2) = -ρ * coul / (γG * r ^ 2) := by ring
  refine ⟨he, by linarith, ?_⟩
  unfold pairChannelForce
  rw [hsame]
  have hcmp : ρ * coul / (γG * r ^ 2) < coul / (γE * r ^ 2) := by
    rw [div_lt_div_iff₀ hdenG hdenE]
    have hcross : ρ * γE < γG := by
      rwa [div_lt_one hGp] at hfrac1
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    have hmul : ρ * γE * (coul * r ^ 2) < γG * (coul * r ^ 2) :=
      mul_lt_mul_of_pos_right hcross (mul_pos hc hr2)
    nlinarith
  have hgoal : 0 < coul / (γE * r ^ 2) - ρ * coul / (γG * r ^ 2) :=
    sub_pos.mpr hcmp
  have heq : -ρ * coul / (γG * r ^ 2) + coul / (γE * r ^ 2) =
      coul / (γE * r ^ 2) - ρ * coul / (γG * r ^ 2) := by ring
  linarith

/-! ### The first node, from inside -/

private theorem one_le_cosh (y : ℝ) : 1 ≤ cosh y :=
  Real.one_le_cosh y

private theorem hasDerivAt_sinhSubId (t : ℝ) :
    HasDerivAt (fun s : ℝ => sinh s - s) (cosh t - 1) t :=
  (hasDerivAt_sinh t).sub (hasDerivAt_id t)

private theorem sinh_ge_id {y : ℝ} (hy : 0 ≤ y) : y ≤ sinh y := by
  let f : ℝ → ℝ := fun s => sinh s - s
  have hmono : MonotoneOn f (Icc 0 y) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 y)
      (by continuity : Continuous f).continuousOn
      (fun t _ => (hasDerivAt_sinhSubId t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hasDerivAt_sinhSubId t).deriv]
        exact sub_nonneg.mpr (one_le_cosh t))
  have hle := hmono ⟨le_rfl, hy⟩ ⟨hy, le_rfl⟩ hy
  have h0 : f 0 = 0 := by simp [f]
  simpa [f, h0] using hle

private theorem hasDerivAt_coshQuad (t : ℝ) :
    HasDerivAt (fun s : ℝ => cosh s - 1 - s ^ 2 / 2) (sinh t - t) t := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa [pow_one] using hasDerivAt_pow 2 t
  have h := (hasDerivAt_cosh t).sub
    ((hasDerivAt_const t (1 : ℝ)).add (h2.div_const 2))
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with s
  simp only [Pi.sub_apply, Pi.add_apply]
  ring_nf

private theorem cosh_ge_quadratic {y : ℝ} (hy : 0 ≤ y) :
    1 + y ^ 2 / 2 ≤ cosh y := by
  let f : ℝ → ℝ := fun s => cosh s - 1 - s ^ 2 / 2
  have hmono : MonotoneOn f (Icc 0 y) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 y)
      (by continuity : Continuous f).continuousOn
      (fun t _ => (hasDerivAt_coshQuad t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hasDerivAt_coshQuad t).deriv]
        linarith [sinh_ge_id ht.1.le])
  have hle := hmono ⟨le_rfl, hy⟩ ⟨hy, le_rfl⟩ hy
  have h0 : f 0 = 0 := by simp [f]
  have hf : f y = cosh y - 1 - y ^ 2 / 2 := rfl
  linarith [hle]

private theorem hasDerivAt_sinhCubic (t : ℝ) :
    HasDerivAt (fun s : ℝ => sinh s - s - s ^ 3 / 6) (cosh t - 1 - t ^ 2 / 2) t := by
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 3 t
  have h := (hasDerivAt_sinh t).sub
    ((hasDerivAt_id t).add (h3.div_const 6))
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with s
  simp only [Pi.sub_apply, Pi.add_apply, id_eq]
  ring_nf

private theorem sinh_ge_cubic {y : ℝ} (hy : 0 ≤ y) :
    y + y ^ 3 / 6 ≤ sinh y := by
  let f : ℝ → ℝ := fun s => sinh s - s - s ^ 3 / 6
  have hmono : MonotoneOn f (Icc 0 y) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 y)
      (by continuity : Continuous f).continuousOn
      (fun t _ => (hasDerivAt_sinhCubic t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hasDerivAt_sinhCubic t).deriv]
        linarith [cosh_ge_quadratic ht.1.le])
  have hle := hmono ⟨le_rfl, hy⟩ ⟨hy, le_rfl⟩ hy
  have h0 : f 0 = 0 := by simp [f]
  have hf : f y = sinh y - y - y ^ 3 / 6 := rfl
  linarith [hle]

private theorem hasDerivAt_coshQuartic (t : ℝ) :
    HasDerivAt (fun s : ℝ => cosh s - 1 - s ^ 2 / 2 - s ^ 4 / 24)
      (sinh t - t - t ^ 3 / 6) t := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa [pow_one] using hasDerivAt_pow 2 t
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 4 t
  have h := (hasDerivAt_cosh t).sub
    (((hasDerivAt_const t (1 : ℝ)).add (h2.div_const 2)).add (h4.div_const 24))
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with s
  simp only [Pi.sub_apply, Pi.add_apply]
  ring_nf

private theorem cosh_ge_quartic {y : ℝ} (hy : 0 ≤ y) :
    1 + y ^ 2 / 2 + y ^ 4 / 24 ≤ cosh y := by
  let f : ℝ → ℝ := fun s => cosh s - 1 - s ^ 2 / 2 - s ^ 4 / 24
  have hmono : MonotoneOn f (Icc 0 y) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 y)
      (by continuity : Continuous f).continuousOn
      (fun t _ => (hasDerivAt_coshQuartic t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hasDerivAt_coshQuartic t).deriv]
        linarith [sinh_ge_cubic ht.1.le])
  have hle := hmono ⟨le_rfl, hy⟩ ⟨hy, le_rfl⟩ hy
  have h0 : f 0 = 0 := by simp [f]
  have hf : f y = cosh y - 1 - y ^ 2 / 2 - y ^ 4 / 24 := rfl
  linarith [hle]

private theorem sqrt_two_lt_ninetyNine_seventieths : sqrt 2 < (99 : ℝ) / 70 := by
  have hsq : (sqrt 2) ^ 2 < ((99 : ℝ) / 70) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  exact (sq_lt_sq₀ (sqrt_nonneg _) (by norm_num)).mp hsq

private theorem strictMonoOn_cosh_nonneg : StrictMonoOn cosh (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) continuous_cosh.continuousOn fun x hx => by
    rw [interior_Ici] at hx
    rw [congrFun Real.deriv_cosh x]
    exact sinh_pos_iff.mpr hx

/-- The linear coefficient at the first node exceeds `22/15`. -/
theorem firstNode_slope_gt_twentyTwo_fifteenths :
    (22 : ℝ) / 15 < nodeSlopeLo * resonanceRoot1 := by
  have hwin := resonanceRoot1_sharp_bounds
  have hroot : 0 < resonanceRoot1 := lt_trans (by positivity) hwin.1
  have hslope : 0 < nodeSlopeLo := nodeSlopeLo_pos
  have hcoeff : (π / (2 * sqrt 2)) * cosh (π / 4) = (π / 4) * nodeSlopeLo := by
    unfold nodeSlopeLo
    rw [sin_pi_div_four]
    have hs : (sqrt 2) ^ 2 = 2 := sq_sqrt (by norm_num)
    field_simp [hs]
    rw [hs]
    norm_num
  have hpi : (314 : ℝ) / 100 < π := by
    have : (314 : ℝ) / 100 = 3.14 := by norm_num
    linarith [pi_gt_d2]
  have hy0 : (0 : ℝ) ≤ 314 / 400 := by norm_num
  have hcosh0 : 1 + (314 / 400) ^ 2 / 2 + (314 / 400) ^ 4 / 24 ≤ cosh (314 / 400) :=
    cosh_ge_quartic hy0
  have hyπ : (314 : ℝ) / 400 < π / 4 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have : (314 : ℝ) / 400 * 4 = 314 / 100 := by ring
    linarith [hpi]
  have hcosh : cosh (314 / 400) < cosh (π / 4) := by
    have hπ4 : (0 : ℝ) ≤ π / 4 := le_of_lt (div_pos pi_pos (by norm_num))
    exact strictMonoOn_cosh_nonneg (by norm_num) hπ4 hyπ
  have hden : 0 < 2 * sqrt 2 := by positivity
  have hdenHi : 0 < 2 * ((99 : ℝ) / 70) := by norm_num
  have hsqrt : 2 * sqrt 2 < 2 * ((99 : ℝ) / 70) :=
    mul_lt_mul_of_pos_left sqrt_two_lt_ninetyNine_seventieths (by norm_num)
  have hquot : (314 : ℝ) / 100 / (2 * ((99 : ℝ) / 70)) < π / (2 * sqrt 2) := by
    rw [div_lt_div_iff₀ hdenHi hden]
    have hstep1 : (314 : ℝ) / 100 * (2 * sqrt 2) < (314 : ℝ) / 100 * (2 * ((99 : ℝ) / 70)) :=
      mul_lt_mul_of_pos_left hsqrt (by norm_num)
    have hstep2 : (314 : ℝ) / 100 * (2 * ((99 : ℝ) / 70)) < π * (2 * ((99 : ℝ) / 70)) :=
      mul_lt_mul_of_pos_right hpi hdenHi
    linarith
  have htaylor : (0 : ℝ) < 1 + (314 / 400) ^ 2 / 2 + (314 / 400) ^ 4 / 24 := by
    norm_num
  have hL : (314 : ℝ) / 100 / (2 * ((99 : ℝ) / 70)) *
        (1 + (314 / 400) ^ 2 / 2 + (314 / 400) ^ 4 / 24) <
      (π / (2 * sqrt 2)) * cosh (π / 4) := by
    have h1 : (314 : ℝ) / 100 / (2 * ((99 : ℝ) / 70)) *
          (1 + (314 / 400) ^ 2 / 2 + (314 / 400) ^ 4 / 24) <
        π / (2 * sqrt 2) * (1 + (314 / 400) ^ 2 / 2 + (314 / 400) ^ 4 / 24) :=
      mul_lt_mul_of_pos_right hquot htaylor
    have hcoshT : 1 + (314 / 400) ^ 2 / 2 + (314 / 400) ^ 4 / 24 < cosh (π / 4) :=
      lt_of_le_of_lt hcosh0 hcosh
    have h2 : π / (2 * sqrt 2) * (1 + (314 / 400) ^ 2 / 2 + (314 / 400) ^ 4 / 24) <
        π / (2 * sqrt 2) * cosh (π / 4) :=
      mul_lt_mul_of_pos_left hcoshT (div_pos pi_pos hden)
    exact lt_trans h1 h2
  have hrat : (22 : ℝ) / 15 < (314 : ℝ) / 100 / (2 * ((99 : ℝ) / 70)) *
      (1 + (314 / 400) ^ 2 / 2 + (314 / 400) ^ 4 / 24) := by
    norm_num
  have hprod : (π / 4) * nodeSlopeLo < resonanceRoot1 * nodeSlopeLo :=
    mul_lt_mul_of_pos_right hwin.1 hslope
  linarith [hcoeff, hL]

/-- Just inside the first node, and still below phase `1`, the factor is a
negative multiple of the phase gap, between the two comparison slopes. -/
theorem gammaSEqual_linear_inside {x : ℝ} (hx : x ∈ Ioo resonanceRoot1 1) :
    nodeSlopeLo * (x - resonanceRoot1) < -gammaSEqual x ∧
      -gammaSEqual x < nodeSlopeHi * (x - resonanceRoot1) := by
  have hx1 : π / 4 < resonanceRoot1 := resonanceRoot1_sharp_bounds.1
  have hxlt : resonanceRoot1 < x := hx.1
  let D := Icc resonanceRoot1 x
  have hD : Convex ℝ D := convex_Icc _ _
  have hxD : x ∈ D := ⟨hxlt.le, le_rfl⟩
  have hyD : resonanceRoot1 ∈ D := ⟨le_rfl, hxlt.le⟩
  have hint : ∀ ξ ∈ interior D, -nodeSlopeHi < deriv gammaSEqual ξ ∧
      deriv gammaSEqual ξ < -nodeSlopeLo := by
    intro ξ hξ
    rw [interior_Icc] at hξ
    exact deriv_gammaSEqual_slope_bounds
      ⟨lt_trans hx1 hξ.1, lt_trans hξ.2 hx.2⟩
  have hcont : ContinuousOn gammaSEqual D := continuous_gammaSEqual.continuousOn
  have hdiff : DifferentiableOn ℝ gammaSEqual (interior D) :=
    gammaSEqual_differentiable.differentiableOn
  have hlo := hD.image_sub_lt_mul_sub_of_deriv_lt hcont hdiff
    (fun ξ hξ => (hint ξ hξ).2) resonanceRoot1 hyD x hxD hxlt
  have hhi := hD.mul_sub_lt_image_sub_of_lt_deriv hcont hdiff
    (fun ξ hξ => (hint ξ hξ).1) resonanceRoot1 hyD x hxD hxlt
  rw [resonanceRoot1_gammaSEqual_zero] at hlo hhi
  constructor
  · linarith
  · linarith

/-- Phase at fractional depth `ε` inside the first node: `r = r₁ (1-ε)`. -/
noncomputable def phaseAtDepth (ε : ℝ) : ℝ :=
  resonanceRoot1 / (1 - ε)

theorem phaseAtDepth_mem {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 - resonanceRoot1) :
    phaseAtDepth ε ∈ Ioo resonanceRoot1 1 := by
  have hx1 : 0 < resonanceRoot1 := lt_trans (by positivity) resonanceRoot1_sharp_bounds.1
  have hden : 0 < 1 - ε := by linarith [resonanceRoot1_sharp_bounds.2]
  unfold phaseAtDepth
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hden]
    nlinarith
  · rw [div_lt_iff₀ hden]
    nlinarith

theorem phaseAtDepth_gap {ε : ℝ} (_hε : 0 < ε) (hε1 : ε < 1) :
    phaseAtDepth ε - resonanceRoot1 = resonanceRoot1 * ε / (1 - ε) := by
  have hden : 1 - ε ≠ 0 := by linarith
  unfold phaseAtDepth
  field_simp [hden]
  ring

private theorem depth_cut :
    (2401 : ℚ) * 15 / (22 * 10 ^ 46) < (164 : ℚ) / 100 / 10 ^ 43 := by
  norm_num

/-- While the phase is still below `1`, the outward gravitational force of two
electrons exceeds `k e²/r²` only for a fractional depth strictly less than
`1.64×10⁻⁴³`. -/
theorem grav_excess_depth {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 - resonanceRoot1)
    (hexcess : (electronElectronGravToCoulomb : ℝ) > -gammaSEqual (phaseAtDepth ε)) :
    ε < (164 : ℝ) / 100 / 10 ^ 43 := by
  have hroot : 0 < resonanceRoot1 := lt_trans (by positivity) resonanceRoot1_sharp_bounds.1
  have hεlt1 : ε < 1 := by linarith [hε1, hroot]
  have hden : 0 < 1 - ε := by linarith
  have hmem := phaseAtDepth_mem hε hε1
  have hlin := (gammaSEqual_linear_inside hmem).1
  have hgap := phaseAtDepth_gap hε hεlt1
  have hρ : (electronElectronGravToCoulomb : ℝ) < (2401 : ℝ) / 10 ^ 46 := by
    refine lt_of_lt_of_eq (Rat.cast_lt.mpr electronElectronGravToCoulomb_bounds.2) ?_
    norm_num
  have hslope : (22 : ℝ) / 15 < nodeSlopeLo * resonanceRoot1 :=
    firstNode_slope_gt_twentyTwo_fifteenths
  have hprod : (22 : ℝ) / 15 * (ε / (1 - ε)) < (2401 : ℝ) / 10 ^ 46 := by
    have habs : nodeSlopeLo * resonanceRoot1 * ε / (1 - ε) <
        (electronElectronGravToCoulomb : ℝ) := by
      have h := hlin
      rw [hgap] at h
      have hrew : nodeSlopeLo * (resonanceRoot1 * ε / (1 - ε)) =
          nodeSlopeLo * resonanceRoot1 * ε / (1 - ε) := by ring
      linarith
    have hleft : (22 : ℝ) / 15 * (ε / (1 - ε)) <
        nodeSlopeLo * resonanceRoot1 * (ε / (1 - ε)) :=
      mul_lt_mul_of_pos_right hslope (div_pos hε hden)
    have hrew : nodeSlopeLo * resonanceRoot1 * (ε / (1 - ε)) =
        nodeSlopeLo * resonanceRoot1 * ε / (1 - ε) := by ring
    linarith
  have hfrac : ε / (1 - ε) < (2401 : ℝ) / 10 ^ 46 / ((22 : ℝ) / 15) := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 22 / 15)]
    linarith [hprod]
  have hcut : (2401 : ℝ) / 10 ^ 46 / ((22 : ℝ) / 15) < (164 : ℝ) / 100 / 10 ^ 43 := by
    have hrat : (2401 : ℝ) * 15 / (22 * 10 ^ 46) < (164 : ℝ) / 100 / 10 ^ 43 := by
      refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq (Rat.cast_lt.mpr depth_cut) ?_)
      · norm_num
      · norm_num
    have hrew : (2401 : ℝ) / 10 ^ 46 / ((22 : ℝ) / 15) =
        (2401 : ℝ) * 15 / (22 * 10 ^ 46) := by
      field_simp
    linarith
  have hεδ : ε < ε / (1 - ε) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  linarith

/-- The excess is attained: some fractional depth below `1.64×10⁻⁴³` makes the
outward force larger than `k e²/r²`. -/
theorem exists_grav_excess_depth :
    ∃ ε : ℝ, 0 < ε ∧ ε < (164 : ℝ) / 100 / 10 ^ 43 ∧
      ε < 1 - resonanceRoot1 ∧
        (electronElectronGravToCoulomb : ℝ) > -gammaSEqual (phaseAtDepth ε) := by
  have hmid : (2400 / 10 ^ 46 : ℝ) < (electronElectronGravToCoulomb : ℝ) := by
    refine lt_of_eq_of_lt ?_ (Rat.cast_lt.mpr electronElectronGravToCoulomb_bounds.1)
    norm_num
  have hρpos : (0 : ℝ) < electronElectronGravToCoulomb :=
    lt_trans (by norm_num : (0 : ℝ) < 2400 / 10 ^ 46) hmid
  have hx1 : resonanceRoot1 < 1 := resonanceRoot1_sharp_bounds.2
  have hπ : resonanceRoot1 < π := lt_trans hx1 (by linarith [pi_gt_three])
  have hcont : ContinuousAt gammaSEqual resonanceRoot1 :=
    continuous_gammaSEqual.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hclose⟩ := hcont _ hρpos
  have hroom : 0 < min (δ / 2) ((1 - resonanceRoot1) / 2) := by
    have : 0 < 1 - resonanceRoot1 := by linarith
    positivity
  set x : ℝ := resonanceRoot1 + min (δ / 2) ((1 - resonanceRoot1) / 2) with hxdef
  have hxlt1 : x < 1 := by
    have hmin : min (δ / 2) ((1 - resonanceRoot1) / 2) ≤ (1 - resonanceRoot1) / 2 :=
      min_le_right _ _
    linarith
  have hxgt : resonanceRoot1 < x := by linarith
  have hdist : dist x resonanceRoot1 < δ := by
    rw [Real.dist_eq]
    have hsub : x - resonanceRoot1 = min (δ / 2) ((1 - resonanceRoot1) / 2) := by
      rw [hxdef]
      ring
    rw [hsub, abs_of_pos hroom]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith [hδ])
  have hγ : dist (gammaSEqual x) (gammaSEqual resonanceRoot1) <
      (electronElectronGravToCoulomb : ℝ) := hclose hdist
  rw [resonanceRoot1_gammaSEqual_zero, Real.dist_eq] at hγ
  have hxπ : x < π := by linarith [hxlt1, pi_gt_three]
  have hneg : gammaSEqual x < 0 :=
    gammaSEqual_neg_right_of_first_node ⟨hxgt, hxπ⟩
  have habs : -gammaSEqual x < (electronElectronGravToCoulomb : ℝ) := by
    have : |gammaSEqual x| < (electronElectronGravToCoulomb : ℝ) := by simpa using hγ
    rwa [abs_of_neg hneg] at this
  set ε : ℝ := 1 - resonanceRoot1 / x with hεdef
  have hx0 : 0 < x := lt_trans (lt_trans (by positivity) resonanceRoot1_sharp_bounds.1) hxgt
  have hε0 : 0 < ε := by
    have : resonanceRoot1 / x < 1 := by
      rw [div_lt_one hx0]
      exact hxgt
    linarith
  have hroot : 0 < resonanceRoot1 := lt_trans (by positivity) resonanceRoot1_sharp_bounds.1
  have hε1 : ε < 1 - resonanceRoot1 := by
    have hdiv : resonanceRoot1 < resonanceRoot1 / x := by
      rw [lt_div_iff₀ hx0]
      nlinarith [hxgt, hroot]
    linarith
  have hphase : phaseAtDepth ε = x := by
    unfold phaseAtDepth
    have hden : 1 - ε = resonanceRoot1 / x := by
      rw [hεdef]
      ring
    rw [hden]
    field_simp [hroot.ne', hx0.ne']
  refine ⟨ε, hε0, ?_, hε1, ?_⟩
  · exact grav_excess_depth hε0 hε1 (by simpa [hphase] using habs)
  · simpa [hphase] using habs

/-- A node below `1` fm and a fractional depth below `1.64×10⁻⁴³` is a
separation smaller than a radius above `52917` by more than `3×10⁴⁷`. -/
theorem grav_depth_below_bohr {r₁ a ε : ℝ}
    (hr0 : 0 < r₁) (hr1 : r₁ < 1) (ha : 52917 < a)
    (hε0 : 0 ≤ ε) (hε : ε < (164 : ℝ) / 100 / 10 ^ 43) :
    a / (ε * r₁) > 3 * 10 ^ 47 ∨ ε = 0 := by
  rcases eq_or_lt_of_le hε0 with rfl | hεpos
  · exact Or.inr rfl
  · left
    have hwidth : ε * r₁ < (164 : ℝ) / 100 / 10 ^ 43 := by
      have : ε * r₁ < ε * 1 := by nlinarith
      linarith
    have hscale : (164 : ℝ) / 100 / 10 ^ 43 * (3 * 10 ^ 47) < 52917 := by
      norm_num
    have hwidthA : ε * r₁ * (3 * 10 ^ 47) < a := by
      have hpos : (0 : ℝ) < 3 * 10 ^ 47 := by norm_num
      have : ε * r₁ * (3 * 10 ^ 47) <
          ((164 : ℝ) / 100 / 10 ^ 43) * (3 * 10 ^ 47) :=
        mul_lt_mul_of_pos_right hwidth hpos
      linarith
    have hposw : 0 < ε * r₁ := by positivity
    rw [gt_iff_lt, lt_div_iff₀ hposw]
    linarith

end Gravity

end DstDiophantine
