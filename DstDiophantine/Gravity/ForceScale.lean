import DstDiophantine.Gravity.NewtonFromLight
import DstDiophantine.Gravity.CoulombFromDual

set_option linter.style.native false

/-!
# Which scale one compactification produces

## Paper boundary (do **not** claim)

No theorem asserts `dst_derives_G` or `dst_derives_alpha`. The integer \(N\)
is not derived. What follows is the scale that reading produces, once \(N^2\)
is the Planck ratio \((m_P/m)^2=\hbar c/(G m^2)\).

## The scale

On that reading the nonzero normalized floor is exactly
\[
\frac{16}{3}\,\alpha_G(m),\qquad \alpha_G(m)=\frac{G m^2}{\hbar c}.
\]
It is a gravitational scale. It is not the electromagnetic constant.

On the SI stand-ins the electron has
\[
\frac{17}{10}\times 10^{-45}
  < \alpha_G(m_e)
  < \frac{177}{100}\times 10^{-45},
\]
and the electromagnetic constant exceeds the resulting floor by a factor
strictly between \(7.7\times 10^{41}\) and \(8.1\times 10^{41}\).

Forcing the floor to equal the electromagnetic constant asks for an integer
whose square lies in \((729,732)\), between \(27\) and \(28\). The integer
that matches \(\alpha_G(m_e)\) itself has square in \((3\times 10^{45},\,4\times 10^{45})\).
The two squares are not one compactification.
-/

namespace DstDiophantine

namespace Gravity

open SI

/-- Gravitational fine-structure constant \(\alpha_G(m)=G m^2/(\hbar c)\). -/
def alphaGOf (m : ℚ) : ℚ :=
  GApprox * m ^ 2 / hbarC

/-- Planck-mass ratio squared \((m_P/m)^2=\hbar c/(G m^2)\). -/
def planckRatioSq (m : ℚ) : ℚ :=
  hbarC / (GApprox * m ^ 2)

/-- Nonzero floor at the Planck ratio: \((16/3)\,\alpha_G(m)\). -/
def planckFloor (m : ℚ) : ℚ :=
  (16 / 3) * alphaGOf m

theorem alphaGOf_mul_planckRatioSq {m : ℚ} (hm : m ≠ 0) (hG : GApprox ≠ 0) :
    alphaGOf m * planckRatioSq m = 1 := by
  unfold alphaGOf planckRatioSq
  field_simp [hm, hG, hbarC_pos.ne']

theorem impliedNsq_eq_sixteen_thirds_planck {m : ℚ}
    (hm : m ≠ 0) (hG : GApprox ≠ 0) :
    impliedNsq m = (16 / 3) * planckRatioSq m := by
  unfold impliedNsq planckRatioSq
  field_simp [hm, hG, hbarC_pos.ne']

theorem alphaGOf_eq_sixteen_thirds_div_implied {m : ℚ}
    (hm : m ≠ 0) (hG : GApprox ≠ 0) :
    alphaGOf m = (16 / 3) / impliedNsq m := by
  have hrel := impliedNsq_eq_sixteen_thirds_planck hm hG
  have hprod := alphaGOf_mul_planckRatioSq hm hG
  have hpr : planckRatioSq m ≠ 0 := by
    intro h
    simp [h] at hprod
  calc alphaGOf m
      = 1 / planckRatioSq m := by
        rw [eq_div_iff hpr]
        exact hprod
    _ = (16 / 3) / ((16 / 3) * planckRatioSq m) := by
        field_simp
    _ = (16 / 3) / impliedNsq m := by
        rw [← hrel]

theorem planckFloor_eq_sixteen_sq_div_implied {m : ℚ}
    (hm : m ≠ 0) (hG : GApprox ≠ 0) :
    planckFloor m = 256 / (9 * impliedNsq m) := by
  unfold planckFloor
  rw [alphaGOf_eq_sixteen_thirds_div_implied hm hG]
  have himp : impliedNsq m ≠ 0 := by
    rw [impliedNsq_eq_sixteen_thirds_planck hm hG]
    have hpr : planckRatioSq m ≠ 0 := by
      intro h
      have hprod := alphaGOf_mul_planckRatioSq hm hG
      simp [h] at hprod
    exact mul_ne_zero (by norm_num) hpr
  field_simp [himp]
  ring

theorem em_over_planckFloor_eq {m : ℚ} (hm : m ≠ 0) (hG : GApprox ≠ 0) :
    fineStructureApprox / planckFloor m =
      fineStructureApprox * (9 * impliedNsq m) / 256 := by
  have hfloor : planckFloor m ≠ 0 := by
    unfold planckFloor alphaGOf
    exact mul_ne_zero (by norm_num)
      (div_ne_zero (mul_ne_zero hG (pow_ne_zero 2 hm)) hbarC_pos.ne')
  rw [planckFloor_eq_sixteen_sq_div_implied hm hG]
  field_simp [hfloor]

/-- The electron's gravitational fine-structure constant on the SI stand-ins. -/
theorem electron_alphaGOf_bounds :
    (17 / 10 : ℚ) / 10 ^ 45 < alphaGOf electronMassApprox ∧
      alphaGOf electronMassApprox < (177 / 100) / 10 ^ 45 := by
  have hm : electronMassApprox ≠ 0 := ne_of_gt electronMassApprox_pos
  have hG : GApprox ≠ 0 := ne_of_gt GApprox_pos
  rw [alphaGOf_eq_sixteen_thirds_div_implied hm hG]
  obtain ⟨hlo, hhi⟩ := impliedNsq_electron_between_55_56_e22_sq
  have h55 : (55 : ℚ) ^ 2 = 3025 := by norm_num
  have h56 : (56 : ℚ) ^ 2 = 3136 := by norm_num
  rw [h55] at hlo
  rw [h56] at hhi
  have himp : 0 < impliedNsq electronMassApprox := lt_trans (by positivity) hlo
  constructor
  · have hgt : (16 / 3) / (3136 * 10 ^ 42) <
        (16 / 3) / impliedNsq electronMassApprox := by
      gcongr
    refine lt_trans ?_ hgt
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    norm_num
  · have hlt : (16 / 3) / impliedNsq electronMassApprox <
        (16 / 3) / (3025 * 10 ^ 42) := by
      gcongr
    refine hlt.trans ?_
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    norm_num

/-- The electromagnetic constant over the electron's Planck floor. -/
theorem electron_em_over_floor_bounds :
    (77 : ℚ) * 10 ^ 40 < fineStructureApprox / planckFloor electronMassApprox ∧
      fineStructureApprox / planckFloor electronMassApprox < (81 : ℚ) * 10 ^ 40 := by
  have hm : electronMassApprox ≠ 0 := ne_of_gt electronMassApprox_pos
  have hG : GApprox ≠ 0 := ne_of_gt GApprox_pos
  rw [em_over_planckFloor_eq hm hG]
  obtain ⟨hlo, hhi⟩ := impliedNsq_electron_between_55_56_e22_sq
  have h55 : (55 : ℚ) ^ 2 = 3025 := by norm_num
  have h56 : (56 : ℚ) ^ 2 = 3136 := by norm_num
  rw [h55] at hlo
  rw [h56] at hhi
  have hα : 0 < fineStructureApprox := fineStructureApprox_pos
  constructor
  · have hgt : fineStructureApprox * (9 * (3025 * 10 ^ 42)) / 256 <
        fineStructureApprox * (9 * impliedNsq electronMassApprox) / 256 := by
      gcongr
    refine lt_trans ?_ hgt
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  · have hlt : fineStructureApprox * (9 * impliedNsq electronMassApprox) / 256 <
        fineStructureApprox * (9 * (3136 * 10 ^ 42)) / 256 := by
      gcongr
    refine hlt.trans ?_
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num

/-- The integer that matches the electromagnetic constant is not the electron's
Planck ratio. -/
theorem em_matching_square_lt_electron_gravitational :
    impliedNsqEM < impliedNsq electronMassApprox := by
  exact lt_trans impliedNsqEM_bounds.2
    (lt_trans (by norm_num : (732 : ℚ) < 3 * 10 ^ 45) impliedNsq_electron_bounds.1)

end Gravity

end DstDiophantine
