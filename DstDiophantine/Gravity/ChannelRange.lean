import DstDiophantine.Gravity.DualImage
import DstDiophantine.Gravity.CliffordParallel

/-!
# Gravitational and electromagnetic compactification ranges

Both channels read the same dual-image enhancement \(\eta(x)=x\coth x\).
The gravitational channel is organized on a galactic compactification radius
\(R\); the electromagnetic channel is read on a larger radius \(\Lambda\).

On \(0<r\le R\) the electromagnetic fractional departure from inverse-square
obeys \(0<\eta(r/\Lambda)-1<(R/\Lambda)^2/3\). At the gravitational
compactification radius the gravitational departure lies in \((0.31,0.32)\).
When \(0<R<\Lambda\), the ratio of those fractional departures exceeds
\((93/100)(\Lambda/R)^2\).

Reading \(\Lambda\) as the Hubble length, for \(8\le R\le 9\) and
\(67\le H_0\le 74\), the patch radius stands to \(\Lambda\) strictly between
\(1.787\times 10^{-6}\) and \(2.222\times 10^{-6}\). Throughout the patch the
equidistant Jacobian on that sphere differs from \(1\) by less than
\(1.646\times 10^{-12}\), and the electromagnetic fraction lies under the same
figure. At the patch edge the gravitational fraction exceeds the
electromagnetic one by more than \(1.8836\times 10^{11}\).

\(\Lambda\) is an input, as \(a_0\) is. No theorem asserts `dst_derives_lambda`.
The comparison is of fractional departures from each channel's own
inverse-square law. It does not subtract the Coulomb coupling from \(G\).
-/

namespace DstDiophantine

namespace Gravity

/-- Across a patch \(0<r\le R\), the electromagnetic fractional excess over
its own inverse-square law is positive and strictly less than \((R/\Lambda)^2/3\). -/
theorem emExcess_pos_lt_patch {r R Λ : ℝ} (hr : 0 < r) (hR : 0 < R) (hΛ : 0 < Λ)
    (hrR : r ≤ R) :
    0 < dualEnhancement (r / Λ) - 1 ∧
      dualEnhancement (r / Λ) - 1 < (R / Λ) ^ 2 / 3 := by
  have hx : 0 < r / Λ := div_pos hr hΛ
  have hpos : 0 < dualEnhancement (r / Λ) - 1 := by
    linarith [one_lt_dualEnhancement hx]
  have hlt : dualEnhancement (r / Λ) - 1 < (r / Λ) ^ 2 / 3 := by
    linarith [dualEnhancement_lt_one_add_sq_div_three hx]
  have hle : (r / Λ) ^ 2 / 3 ≤ (R / Λ) ^ 2 / 3 := by
    have hsq : (r / Λ) ^ 2 ≤ (R / Λ) ^ 2 := by
      rw [sq, sq]
      exact mul_le_mul (div_le_div_of_nonneg_right hrR hΛ.le)
        (div_le_div_of_nonneg_right hrR hΛ.le) (div_nonneg hr.le hΛ.le) (div_pos hR hΛ).le
    exact div_le_div_of_nonneg_right hsq (by norm_num)
  exact ⟨hpos, hlt.trans_le hle⟩

/-- At one gravitational compactification radius the fractional excess over
inverse-square lies between \(0.31\) and \(0.32\). -/
theorem gravExcess_one_bounds :
    (31 / 100 : ℝ) < dualEnhancement 1 - 1 ∧ dualEnhancement 1 - 1 < 32 / 100 := by
  obtain ⟨hlo, hhi⟩ := dualEnhancement_one_bounds
  constructor <;> linarith

/-- At \(r=R<\Lambda\), the ratio of the gravitational fractional excess to the
electromagnetic one exceeds \((93/100)(\Lambda/R)^2\). -/
theorem excess_ratio_at_compactification {R Λ : ℝ} (hR : 0 < R) (hΛR : R < Λ) :
    (93 / 100 : ℝ) * (Λ / R) ^ 2 <
      (dualEnhancement 1 - 1) / (dualEnhancement (R / Λ) - 1) := by
  have hΛ : 0 < Λ := hR.trans hΛR
  obtain ⟨hden, hdenLt⟩ := emExcess_pos_lt_patch hR hR hΛ le_rfl
  have hupper : 0 < (R / Λ) ^ 2 / 3 := hden.trans hdenLt
  have hnum : (31 / 100 : ℝ) < dualEnhancement 1 - 1 := gravExcess_one_bounds.1
  have hlargerNum :
      (31 / 100 : ℝ) / (dualEnhancement (R / Λ) - 1) <
        (dualEnhancement 1 - 1) / (dualEnhancement (R / Λ) - 1) := by
    gcongr
  have hsmallerDen :
      (31 / 100 : ℝ) / ((R / Λ) ^ 2 / 3) <
        (31 / 100 : ℝ) / (dualEnhancement (R / Λ) - 1) := by
    gcongr
  have hrew :
      (93 / 100 : ℝ) * (Λ / R) ^ 2 = (31 / 100) / ((R / Λ) ^ 2 / 3) := by
    field_simp
    ring
  exact hrew.trans_lt (hsmallerDen.trans hlargerNum)

/-- In the external Milky-Way and Hubble window, the patch is a fraction of the
Hubble length between `1.787×10⁻⁶` and `2.222×10⁻⁶`. Throughout the patch the
equidistant Jacobian on that sphere differs from `1` by less than
`1.646×10⁻¹²`, and so does the electromagnetic fractional excess. At the edge
the gravitational fraction exceeds the electromagnetic one by more than
`1.8836×10¹¹`. `H₀` is an input. -/
theorem hubble_patch_reading {r R H : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hRlo : (8 : ℝ) ≤ R) (hRhi : R ≤ 9)
    (hHlo : (67 : ℝ) ≤ H) (hHhi : H ≤ 74) :
    (1787 : ℝ) / 10 ^ 9 < R / ((SI.speedOfLight : ℝ) / H) ∧
      R / ((SI.speedOfLight : ℝ) / H) < 2222 / 10 ^ 9 ∧
      0 < 1 - compactJacobian (r / ((SI.speedOfLight : ℝ) / H)) ∧
      1 - compactJacobian (r / ((SI.speedOfLight : ℝ) / H)) < 1646 / 10 ^ 15 ∧
      dualEnhancement (r / ((SI.speedOfLight : ℝ) / H)) - 1 < 1646 / 10 ^ 15 ∧
      (18836 : ℝ) * 10 ^ 7 <
        (dualEnhancement 1 - 1) /
          (dualEnhancement (R / ((SI.speedOfLight : ℝ) / H)) - 1) := by
  set Λ : ℝ := (SI.speedOfLight : ℝ) / H
  have hratio := CliffordParallel.hubble_patch_ratio hRlo hRhi hHlo hHhi
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hRlo
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num) hHlo
  have hc : (0 : ℝ) < SI.speedOfLight := by
    rw [CliffordParallel.speedOfLight_coe]
    norm_num
  have hΛ : 0 < Λ := div_pos hc hHpos
  have hχ : 0 < R / Λ := div_pos hRpos hΛ
  have hχhi : R / Λ < (2222 : ℝ) / 10 ^ 9 := hratio.2
  have hRltΛ : R < Λ := by
    rw [← div_lt_one hΛ]
    exact hχhi.trans (by norm_num)
  have hrΛ : 0 < r / Λ := div_pos hr hΛ
  have hrle : r / Λ ≤ R / Λ := div_le_div_of_nonneg_right hrR hΛ.le
  have hr1 : r / Λ ≤ 1 := hrle.trans (hχhi.le.trans (by norm_num))
  have hdef := jacobian_deficit_lt_sq_div_three hrΛ hr1
  have hχcap : (R / Λ) ^ 2 / 3 < ((2222 : ℝ) / 10 ^ 9) ^ 2 / 3 := by
    have hsq : (R / Λ) ^ 2 < ((2222 : ℝ) / 10 ^ 9) ^ 2 :=
      (sq_lt_sq).mpr (by rwa [abs_of_pos hχ, abs_of_pos (show (0 : ℝ) < 2222 / 10 ^ 9 by norm_num)])
    exact div_lt_div_of_pos_right hsq (by norm_num)
  have hceil : ((2222 : ℝ) / 10 ^ 9) ^ 2 / 3 < (1646 : ℝ) / 10 ^ 15 := by
    norm_num
  have hcap : (R / Λ) ^ 2 / 3 < (1646 : ℝ) / 10 ^ 15 := hχcap.trans hceil
  have hχr : (r / Λ) ^ 2 / 3 ≤ (R / Λ) ^ 2 / 3 := by
    have hsq : (r / Λ) ^ 2 ≤ (R / Λ) ^ 2 := by
      rw [sq, sq]
      exact mul_le_mul hrle hrle (div_nonneg hr.le hΛ.le) (div_nonneg hRpos.le hΛ.le)
    exact div_le_div_of_nonneg_right hsq (by norm_num)
  obtain ⟨_, hem⟩ := emExcess_pos_lt_patch hr hRpos hΛ hrR
  have hfloor_shape : (18836 : ℝ) * 10 ^ 7 <
      (93 / 100) * (((2222 : ℝ) / 10 ^ 9)⁻¹) ^ 2 := by
    norm_num
  have hrecip : ((2222 : ℝ) / 10 ^ 9)⁻¹ < (R / Λ)⁻¹ :=
    (inv_lt_inv₀ (by norm_num) hχ).mpr hχhi
  have hinvR : (R / Λ)⁻¹ = Λ / R := by field_simp
  have hsqΛ : (((2222 : ℝ) / 10 ^ 9)⁻¹) ^ 2 < (Λ / R) ^ 2 := by
    rw [← hinvR]
    exact (sq_lt_sq).mpr <| by
      rwa [abs_of_pos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2222 / 10 ^ 9)),
        abs_of_pos (inv_pos.mpr hχ)]
  have hmul : (93 / 100 : ℝ) * (((2222 : ℝ) / 10 ^ 9)⁻¹) ^ 2 <
      (93 / 100) * (Λ / R) ^ 2 := by
    gcongr
  have hratioEx := excess_ratio_at_compactification hRpos hRltΛ
  refine ⟨hratio.1, hχhi, hdef.1, ?_, ?_, ?_⟩
  · exact (hdef.2.trans_le hχr).trans hcap
  · exact hem.trans hcap
  · exact hfloor_shape.trans (hmul.trans hratioEx)

end Gravity

end DstDiophantine
