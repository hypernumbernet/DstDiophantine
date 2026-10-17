import DstDiophantine.Gravity.DualImage

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

end Gravity

end DstDiophantine
