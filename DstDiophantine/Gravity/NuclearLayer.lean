import DstDiophantine.Gravity.SI
import DstDiophantine.Gravity.ElectronShell
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false

/-!
# Nuclear torsional layers (strong-force scale)

## Paper boundary (do **not** claim)

Sec.~nuclear identifies the strong force with layered gravitational repulsion
at nuclear densities and quotes empirical scales (fm, MeV, \(A\gtrsim 300\)).
This module machine-checks SI stand-in windows and equal-scale diagnostics.
It does **not** derive nuclear couplings from the dual-rotor algebra.

No theorem asserts `dst_derives_alpha_s`, `dst_derives_lambdaN`, or
`dst_derives_Amax`. QCD \(\alpha_s\) is **not** paired with `epsN` (the paper
rejects colour charge as torsional charge; copying the EM hypothesis would
break that narrative). The numerical cutoff \(A\sim 300\) remains an underived
heuristic, as in `discrete-dual-spacetime.tex`.

## What is proved

* \(\hbar c \in (197,198)\) MeV·fm on the SI stand-ins.
* Pion Compton wavelength \(\lambda_\pi \in (1,2)\) fm; proton Compton
  \(\lambda_p \in (1/5,3/10)\) fm (does **not** match the 1–2 fm outer layer).
* Equal-scale layer radii \(r_n=\ell/(2x_n)\) satisfy
  \(r_2/r_1 \in (1/(3\pi),1/\pi)\); a hard-core \(0.5\) fm is compatible with
  an outer \(r_1\in(1,2)\) fm but is not forced.
* Labelled pion–\(\ell\) hypothesis: \(\lambda_\pi/2 < r_1 < \lambda_\pi\);
  the paper's lower bound \(1\) fm is not forced by this alone.
* Saturation density \(\rho_0 \in (2,3)\times 10^{14}\) g/cm³;
  paper \(10^{18}\) as an in-nucleus value is rejected.
* Empirical BE/\(A \in (7,9)\) MeV; paper \(40\)–\(50\) MeV as BE/\(A\) is
  rejected (optical well depth is a separate external label).
* Gravity fine-structure \(\alpha_G = G m_p^2/\hbar c \in (10^{-39},10^{-38})\);
  not to be identified with \(O(1)\) nuclear strength or with `epsN 1`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

/-! ### Cleared-denominator helpers -/

private theorem rat_div_gt
    {num den k : ℕ} (hden : (0 : ℚ) < den) (hnat : k * den < num) :
    (k : ℚ) < (num : ℚ) / den := by
  rw [lt_div_iff₀ hden]
  exact_mod_cast hnat

private theorem rat_div_lt
    {num den k : ℕ} (hden : (0 : ℚ) < den) (hnat : num < k * den) :
    (num : ℚ) / den < (k : ℚ) := by
  rw [div_lt_iff₀ hden]
  exact_mod_cast hnat

/-! ### \(\hbar c\) in MeV·fm -/

/-- \(\hbar c\) in MeV·fm on the SI stand-ins. -/
def hbarC_MeVfm : ℚ :=
  hbarC / (MeVApprox * femtometerApprox)

def hbarC_MeVfm_num : ℕ := hbarMantissa * speedOfLightNat

def hbarC_MeVfm_den : ℕ := elementaryChargeMantissa * 10 ^ 6

theorem hbarC_MeVfm_eq_num_div_den :
    hbarC_MeVfm = (hbarC_MeVfm_num : ℚ) / (hbarC_MeVfm_den : ℚ) := by
  unfold hbarC_MeVfm hbarC hbarApprox MeVApprox femtometerApprox
  unfold elementaryCharge hbarC_MeVfm_num hbarC_MeVfm_den
  unfold hbarMantissa hbarScale speedOfLight speedOfLightNat
    elementaryChargeMantissa elementaryChargeScale
  field_simp
  ring

private theorem hbarC_MeVfm_den_pos : (0 : ℚ) < (hbarC_MeVfm_den : ℚ) := by
  unfold hbarC_MeVfm_den elementaryChargeMantissa
  norm_num

theorem hbarC_MeVfm_bounds :
    (197 : ℚ) < hbarC_MeVfm ∧ hbarC_MeVfm < (198 : ℚ) := by
  rw [hbarC_MeVfm_eq_num_div_den]
  refine ⟨rat_div_gt hbarC_MeVfm_den_pos ?_, rat_div_lt hbarC_MeVfm_den_pos ?_⟩
  · unfold hbarC_MeVfm_num hbarC_MeVfm_den hbarMantissa speedOfLightNat
      elementaryChargeMantissa
    native_decide
  · unfold hbarC_MeVfm_num hbarC_MeVfm_den hbarMantissa speedOfLightNat
      elementaryChargeMantissa
    native_decide

/-! ### Compton wavelengths -/

/-- Pion Compton wavelength \(\lambda_\pi = \hbar c / (m_\pi c^2)\) in fm. -/
def pionComptonFm : ℚ := hbarC_MeVfm / pionMassMeVApprox

def pionComptonFm_num : ℕ := hbarC_MeVfm_num * 10 ^ pionMassMeVScale

def pionComptonFm_den : ℕ := hbarC_MeVfm_den * pionMassMeVMantissa

theorem pionComptonFm_eq_num_div_den :
    pionComptonFm = (pionComptonFm_num : ℚ) / (pionComptonFm_den : ℚ) := by
  unfold pionComptonFm pionMassMeVApprox
  rw [hbarC_MeVfm_eq_num_div_den]
  unfold pionComptonFm_num pionComptonFm_den
  field_simp
  simp only [Nat.cast_mul, Nat.cast_pow]
  ring

private theorem pionComptonFm_den_pos : (0 : ℚ) < (pionComptonFm_den : ℚ) := by
  unfold pionComptonFm_den hbarC_MeVfm_den elementaryChargeMantissa
    pionMassMeVMantissa
  norm_num

/-- Window: \(1 < \lambda_\pi < 2\) fm (overlaps the paper's outer-layer band). -/
theorem pionComptonFm_bounds :
    (1 : ℚ) < pionComptonFm ∧ pionComptonFm < (2 : ℚ) := by
  rw [pionComptonFm_eq_num_div_den]
  refine ⟨rat_div_gt pionComptonFm_den_pos ?_,
    rat_div_lt pionComptonFm_den_pos ?_⟩
  · unfold pionComptonFm_num pionComptonFm_den hbarC_MeVfm_num hbarC_MeVfm_den
      hbarMantissa speedOfLightNat elementaryChargeMantissa
      pionMassMeVMantissa pionMassMeVScale
    native_decide
  · unfold pionComptonFm_num pionComptonFm_den hbarC_MeVfm_num hbarC_MeVfm_den
      hbarMantissa speedOfLightNat elementaryChargeMantissa
      pionMassMeVMantissa pionMassMeVScale
    native_decide

theorem pionComptonFm_lt_nine_fifths : pionComptonFm < (9 / 5 : ℚ) := by
  rw [pionComptonFm_eq_num_div_den]
  have hden := pionComptonFm_den_pos
  have hnat : 5 * pionComptonFm_num < 9 * pionComptonFm_den := by
    unfold pionComptonFm_num pionComptonFm_den hbarC_MeVfm_num hbarC_MeVfm_den
      hbarMantissa speedOfLightNat elementaryChargeMantissa
      pionMassMeVMantissa pionMassMeVScale
    native_decide
  have : (pionComptonFm_num : ℚ) / pionComptonFm_den < (9 : ℚ) / 5 := by
    rw [div_lt_div_iff₀ hden (by norm_num)]
    exact_mod_cast hnat
  simpa using this

/-- Proton Compton wavelength \(\lambda_p = \hbar c / (m_p c^2)\) in fm. -/
def protonComptonFm : ℚ := hbarC_MeVfm / protonMassMeVApprox

def protonComptonFm_num : ℕ := hbarC_MeVfm_num * 10 ^ protonMassMeVScale

def protonComptonFm_den : ℕ := hbarC_MeVfm_den * protonMassMeVMantissa

theorem protonComptonFm_eq_num_div_den :
    protonComptonFm =
      (protonComptonFm_num : ℚ) / (protonComptonFm_den : ℚ) := by
  unfold protonComptonFm protonMassMeVApprox
  rw [hbarC_MeVfm_eq_num_div_den]
  unfold protonComptonFm_num protonComptonFm_den
  field_simp
  simp only [Nat.cast_mul, Nat.cast_pow]
  ring

private theorem protonComptonFm_den_pos :
    (0 : ℚ) < (protonComptonFm_den : ℚ) := by
  unfold protonComptonFm_den hbarC_MeVfm_den elementaryChargeMantissa
    protonMassMeVMantissa
  norm_num

/-- Window: \(1/5 < \lambda_p < 3/10\) fm — **not** the 1–2 fm outer layer. -/
theorem protonComptonFm_bounds :
    (1 / 5 : ℚ) < protonComptonFm ∧ protonComptonFm < (3 / 10 : ℚ) := by
  rw [protonComptonFm_eq_num_div_den]
  have hden := protonComptonFm_den_pos
  constructor
  · have hnat : protonComptonFm_den < 5 * protonComptonFm_num := by
      unfold protonComptonFm_num protonComptonFm_den hbarC_MeVfm_num
        hbarC_MeVfm_den hbarMantissa speedOfLightNat elementaryChargeMantissa
        protonMassMeVMantissa protonMassMeVScale
      native_decide
    have : (1 : ℚ) / 5 < (protonComptonFm_num : ℚ) / protonComptonFm_den := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 5) hden]
      exact_mod_cast hnat
    simpa using this
  · have hnat : 10 * protonComptonFm_num < 3 * protonComptonFm_den := by
      unfold protonComptonFm_num protonComptonFm_den hbarC_MeVfm_num
        hbarC_MeVfm_den hbarMantissa speedOfLightNat elementaryChargeMantissa
        protonMassMeVMantissa protonMassMeVScale
      native_decide
    have : (protonComptonFm_num : ℚ) / protonComptonFm_den < (3 : ℚ) / 10 := by
      rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℚ) < 10)]
      exact_mod_cast hnat
    simpa using this

theorem protonCompton_ne_outer_layer_band :
    ¬ ((1 : ℚ) < protonComptonFm ∧ protonComptonFm < (2 : ℚ)) := by
  intro h
  have hhi := protonComptonFm_bounds.2
  have : protonComptonFm < (1 : ℚ) := lt_trans hhi (by norm_num)
  exact absurd h.1 (not_lt.mpr this.le)

/-! ### Equal-scale layer radius ratios -/

/-- Equal-scale layer radius \(r = \ell / (2x)\). -/
noncomputable def equalScaleLayerRadius (ℓ x : ℝ) : ℝ := ℓ / (2 * x)

theorem equalScaleLayerRadius_ratio
    (ℓ x₁ x₂ : ℝ) (hℓ : ℓ ≠ 0) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) :
    equalScaleLayerRadius ℓ x₂ / equalScaleLayerRadius ℓ x₁ = x₁ / x₂ := by
  unfold equalScaleLayerRadius
  field_simp [hℓ, hx₁, hx₂]

/-- If \(x_1\in(1/2,1)\) and \(x_2\in(\pi,3\pi/2)\), then
\(r_2/r_1 = x_1/x_2 \in (1/(3\pi), 1/\pi)\). -/
theorem equalScale_layer_ratio_bounds
    {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ Ioo (1 / 2 : ℝ) 1)
    (hx₂ : x₂ ∈ Ioo π (3 * π / 2)) :
    x₁ / x₂ ∈ Ioo (1 / (3 * π)) (1 / π) := by
  simp only [mem_Ioo] at hx₁ hx₂ ⊢
  have hx₂pos : (0 : ℝ) < x₂ := lt_trans pi_pos hx₂.1
  have hπpos : (0 : ℝ) < π := pi_pos
  constructor
  · -- 1/(3π) < x₁/x₂ ↔ x₂ < 3π · x₁
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) hπpos) hx₂pos]
    calc (1 : ℝ) * x₂ = x₂ := one_mul _
      _ < 3 * π / 2 := hx₂.2
      _ = (1 / 2) * (3 * π) := by ring
      _ < x₁ * (3 * π) :=
          mul_lt_mul_of_pos_right hx₁.1 (mul_pos (by norm_num) hπpos)
  · -- x₁/x₂ < 1/π ↔ x₁ · π < x₂
    rw [div_lt_div_iff₀ hx₂pos hπpos]
    calc x₁ * π < 1 * π := mul_lt_mul_of_pos_right hx₁.2 hπpos
      _ = π := one_mul _
      _ < 1 * x₂ := by simpa using hx₂.1

/-- Compatibility (not uniqueness): outer \(r_1\in(1,2)\) fm and a ratio in
\((1/(3\pi),1/\pi)\) can place \(r_2\) at \(1/2\) fm. -/
theorem hardCore_half_fm_compatible :
    ∃ r₁ ratio : ℝ,
      r₁ ∈ Ioo (1 : ℝ) 2 ∧
        ratio ∈ Ioo (1 / (3 * π)) (1 / π) ∧
        r₁ * ratio = (1 / 2 : ℝ) := by
  -- \(r_1 = 15/8\), \(\mathrm{ratio} = 4/15\): product \(1/2\);
  -- \(4/15 \approx 0.267 \in (1/(3\pi), 1/\pi)\) using only \(\pi\in(3,4)\).
  refine ⟨(15 / 8 : ℝ), (4 / 15 : ℝ), ?_, ?_, by norm_num⟩
  · simp only [mem_Ioo]; constructor <;> norm_num
  · simp only [mem_Ioo]
    constructor
    · -- 1/(3π) < 4/15 ↔ 15 < 12π ↔ 5/4 < π
      have : (1 : ℝ) / (3 * π) < 4 / 15 := by
        rw [div_lt_div_iff₀ (mul_pos (by norm_num) pi_pos) (by norm_num)]
        nlinarith [pi_gt_three]
      exact this
    · -- 4/15 < 1/π ↔ 4π < 15 ↔ π < 15/4 (use π < 3.15)
      have : (4 : ℝ) / 15 < 1 / π := by
        rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 15) pi_pos]
        nlinarith [pi_lt_d2]
      exact this

/-! ### Labelled pion–\(\ell\) hypothesis -/

/-- Working hypothesis (not a derivation): \(\ell = \lambda_\pi\). -/
noncomputable def pionLambdaHyp_r1 (x₁ : ℝ) : ℝ :=
  equalScaleLayerRadius (pionComptonFm : ℝ) x₁

theorem pionLambdaHyp_r1_bounds {x₁ : ℝ}
    (hx : x₁ ∈ Ioo (1 / 2 : ℝ) 1) :
    (pionComptonFm : ℝ) / 2 < pionLambdaHyp_r1 x₁ ∧
      pionLambdaHyp_r1 x₁ < (pionComptonFm : ℝ) := by
  unfold pionLambdaHyp_r1 equalScaleLayerRadius
  simp only [mem_Ioo] at hx
  have hxpos : (0 : ℝ) < x₁ := lt_trans (by norm_num) hx.1
  have hπ : (0 : ℝ) < (pionComptonFm : ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < 1) pionComptonFm_bounds.1)
  constructor
  · have : (pionComptonFm : ℝ) / 2 < pionComptonFm / (2 * x₁) := by
      rw [div_lt_div_iff₀ (by norm_num) (mul_pos (by norm_num) hxpos)]
      nlinarith [hx.2]
    exact this
  · have : (pionComptonFm : ℝ) / (2 * x₁) < pionComptonFm := by
      rw [div_lt_iff₀ (mul_pos (by norm_num) hxpos)]
      nlinarith [hx.1, hπ]
    exact this

/-- Paper outer-layer lower bound \(1\) fm is not forced by the pion–\(\ell\)
hypothesis alone. -/
theorem paper_outer_layer_1fm_not_forced_by_pionLambda :
    ∃ x₁ : ℝ, x₁ ∈ Ioo (1 / 2 : ℝ) 1 ∧ pionLambdaHyp_r1 x₁ < 1 := by
  refine ⟨(9 / 10 : ℝ), ?_, ?_⟩
  · simp only [mem_Ioo]; constructor <;> norm_num
  · unfold pionLambdaHyp_r1 equalScaleLayerRadius
    have hℓ : (↑pionComptonFm : ℝ) < ↑(9 / 5 : ℚ) := by
      exact_mod_cast pionComptonFm_lt_nine_fifths
    calc (↑pionComptonFm : ℝ) / (2 * (9 / 10 : ℝ))
        = (↑pionComptonFm : ℝ) * (5 / 9) := by ring
      _ < ↑(9 / 5 : ℚ) * (5 / 9) :=
          mul_lt_mul_of_pos_right hℓ (by norm_num)
      _ = 1 := by norm_num

/-! ### Saturation density -/

/-- Mass density \(\rho_0 = n_0 m_p\) in g/cm³ on the SI stand-ins. -/
def saturationDensity_g_cm3 : ℚ :=
  saturationDensityFm3Approx / femtometerApprox ^ 3 * protonMassApprox / 1000

/-- Exact integer: \(16 \times m_p^{\mathrm{mantissa}} \times 100\). -/
def saturationDensity_g_cm3_nat : ℕ :=
  saturationDensityFm3Mantissa * protonMassMantissa * 100

theorem saturationDensity_g_cm3_eq_nat :
    saturationDensity_g_cm3 = (saturationDensity_g_cm3_nat : ℚ) := by
  unfold saturationDensity_g_cm3 saturationDensity_g_cm3_nat
  unfold saturationDensityFm3Approx femtometerApprox protonMassApprox
  unfold saturationDensityFm3Mantissa saturationDensityFm3Scale
    protonMassMantissa protonMassScale
  field_simp
  ring

theorem saturationDensity_g_cm3_bounds :
    (2 : ℚ) * 10 ^ 14 < saturationDensity_g_cm3 ∧
      saturationDensity_g_cm3 < (3 : ℚ) * 10 ^ 14 := by
  rw [saturationDensity_g_cm3_eq_nat]
  unfold saturationDensity_g_cm3_nat saturationDensityFm3Mantissa
    protonMassMantissa
  constructor <;> norm_num

/-- Paper claim \(\sim 10^{18}\) g/cm³ as an in-nucleus density is false on
the saturation stand-in. -/
theorem paper_density_1e18_false :
    saturationDensity_g_cm3 ≠ (10 : ℚ) ^ 18 := by
  rw [saturationDensity_g_cm3_eq_nat]
  unfold saturationDensity_g_cm3_nat saturationDensityFm3Mantissa
    protonMassMantissa
  norm_num

theorem paper_density_1e18_outside_saturation_window :
    ¬ ((2 : ℚ) * 10 ^ 14 < (10 : ℚ) ^ 18 ∧
        (10 : ℚ) ^ 18 < (3 : ℚ) * 10 ^ 14) := by
  intro h
  have : (10 : ℚ) ^ 18 < (3 : ℚ) * 10 ^ 14 := h.2
  norm_num at this

/-! ### Binding energy per nucleon vs optical well depth -/

theorem bindingEnergyPerNucleonMeV_bounds :
    (7 : ℚ) < bindingEnergyPerNucleonMeVApprox ∧
      bindingEnergyPerNucleonMeVApprox < (9 : ℚ) := by
  unfold bindingEnergyPerNucleonMeVApprox bindingEnergyPerNucleonMeVMantissa
    bindingEnergyPerNucleonMeVScale
  constructor <;> norm_num

/-- Paper \(\sim 40\)–\(50\) MeV “per nucleon” is **not** BE/\(A\). -/
theorem paper_binding_40_50_as_BE_A_false :
    ¬ ((40 : ℚ) ≤ bindingEnergyPerNucleonMeVApprox ∧
        bindingEnergyPerNucleonMeVApprox ≤ 50) := by
  intro h
  have hhi := bindingEnergyPerNucleonMeV_bounds.2
  have : bindingEnergyPerNucleonMeVApprox < 40 := lt_trans hhi (by norm_num)
  exact absurd h.1 (not_le.mpr this)

/-- Optical well depth \(45\) MeV lies in the paper's \(40\)–\(50\) MeV band
(separate external label, not BE/\(A\)). -/
theorem nuclearWellDepth_in_40_50 :
    (40 : ℚ) ≤ nuclearWellDepthMeVApprox ∧
      nuclearWellDepthMeVApprox ≤ 50 := by
  unfold nuclearWellDepthMeVApprox
  constructor <;> norm_num

/-! ### Gravity fine-structure \(\alpha_G\) -/

/-- \(\alpha_G = G m_p^2 / (\hbar c)\) (dimensionless). -/
def alphaG : ℚ := GApprox * protonMassApprox ^ 2 / hbarC

def alphaG_num : ℕ := GMantissa * protonMassMantissa ^ 2

def alphaG_den : ℕ := 10 ^ 49 * hbarMantissa * speedOfLightNat

theorem alphaG_eq_num_div_den :
    alphaG = (alphaG_num : ℚ) / (alphaG_den : ℚ) := by
  unfold alphaG alphaG_num alphaG_den
  unfold GApprox protonMassApprox hbarC hbarApprox speedOfLight
  unfold GMantissa GScale protonMassMantissa protonMassScale
    hbarMantissa hbarScale speedOfLightNat
  field_simp
  simp only [Nat.cast_mul, Nat.cast_pow]
  ring

private theorem alphaG_den_pos : (0 : ℚ) < (alphaG_den : ℚ) := by
  unfold alphaG_den hbarMantissa speedOfLightNat
  norm_num

/-- Window: \(10^{-39} < \alpha_G < 10^{-38}\). -/
theorem alphaG_bounds :
    (1 : ℚ) / 10 ^ 39 < alphaG ∧ alphaG < (1 : ℚ) / 10 ^ 38 := by
  rw [alphaG_eq_num_div_den]
  have hden := alphaG_den_pos
  constructor
  · have hnat : alphaG_den < alphaG_num * 10 ^ 39 := by
      unfold alphaG_num alphaG_den GMantissa protonMassMantissa
        hbarMantissa speedOfLightNat
      native_decide
    have : (1 : ℚ) / 10 ^ 39 < (alphaG_num : ℚ) / alphaG_den := by
      rw [div_lt_div_iff₀ (by norm_num) hden]
      exact_mod_cast hnat
    simpa using this
  · have hnat : alphaG_num * 10 ^ 38 < alphaG_den := by
      unfold alphaG_num alphaG_den GMantissa protonMassMantissa
        hbarMantissa speedOfLightNat
      native_decide
    have : (alphaG_num : ℚ) / alphaG_den < (1 : ℚ) / 10 ^ 38 := by
      rw [div_lt_div_iff₀ hden (by norm_num)]
      exact_mod_cast hnat
    simpa using this

/-- \(\alpha_G\) is not \(O(1)\); naive Newton gravity is not the nuclear force. -/
theorem alphaG_ne_order_one : alphaG < 1 := by
  have h := alphaG_bounds.2
  exact lt_trans h (by norm_num)

/-- Lattice floor at \(N=1\) must not be identified with nuclear coupling. -/
theorem epsN_one_ne_nuclear_order :
    epsN 1 = (16 : ℚ) / 3 ∧ (1 : ℚ) < epsN 1 := by
  constructor
  · unfold epsN; norm_num
  · unfold epsN; norm_num

/-- Reuse equal-scale \(\Theta(1/n)\) from `ElectronShell` (gravitational channel
shares \(\gamma_s\)). Absolute fm/MeV scales need external \(\ell\). -/
theorem nuclear_equalScale_radius_O_of_one_over_n
    (ℓ : ℝ) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ resonanceBranch n) (hℓ : 0 < ℓ) :
    ℓ / (2 * x) < ℓ / (2 * (n : ℝ) * π) :=
  equalScale_radius_O_of_one_over_n ℓ n hn x hx hℓ

end Gravity

end DstDiophantine
