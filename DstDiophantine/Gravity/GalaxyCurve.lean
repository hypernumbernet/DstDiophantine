import DstDiophantine.Gravity.DualImage
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false

/-!
# Spherical dwarfs and disk galaxies

Small galaxies are spherical: the stars fill a ball, with no preferred plane.
Outside that ball the dual curve is the point-mass law of the whole baryonic
mass, whatever the arrangement inside. A heavier galaxy settles into a disk;
the same acceleration relation is then read off the Newtonian curve of the disk.

On the SI stand-ins, for a dwarf of mass \(4\times 10^8\,M_\odot\):

* \(50.2 < v_\infty < 50.3\,\mathrm{km/s}\) and
  \(0.6816\,\mathrm{kpc} < R < 0.6817\,\mathrm{kpc}\), so
  \(2.04\,\mathrm{kpc} < 3R < 2.05\,\mathrm{kpc}\) and
  \(2.141\,\mathrm{kpc} < \pi R < 2.142\,\mathrm{kpc}\).
* If the baryons lie inside a ball of radius \(0.8\,\mathrm{kpc}\), the
  speed at the surface lies between \(55.2\) and \(55.3\,\mathrm{km/s}\),
  at \(2\,\mathrm{kpc}\) between \(50.38\) and \(50.39\,\mathrm{km/s}\), and
  at \(4\,\mathrm{kpc}\) again between \(50.2\) and \(50.3\,\mathrm{km/s}\).
  The circular specific angular momentum there is larger than at the surface
  by a factor strictly between \(4.53\) and \(4.56\), while the radius is
  larger by five.

A low-surface-brightness mass \(3\times 10^9\,M_\odot\) has
\(83.1 < v_\infty < 83.2\,\mathrm{km/s}\).

\(a_0\) and \(G\) are external inputs. No theorem asserts `dst_derives_a0`.
-/

namespace DstDiophantine

namespace Gravity

open Real Finset SI

lemma exp_between {x lo hi : ℝ} {n : ℕ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hn : 0 < n)
    (hlo : lo < (∑ m ∈ range n, x ^ m / m.factorial) -
      x ^ n * (n.succ / (n.factorial * n)))
    (hhi : (∑ m ∈ range n, x ^ m / m.factorial) +
      x ^ n * (n.succ / (n.factorial * n)) < hi) :
    lo < exp x ∧ exp x < hi := by
  have hx : |x| ≤ 1 := by rwa [abs_of_nonneg hx0]
  have h := exp_bound hx hn
  rw [abs_of_nonneg hx0, abs_sub_le_iff] at h
  obtain ⟨hup, hdn⟩ := h
  constructor <;> linarith

/-! ### Masses and asymptotic speeds -/

def dwarfMassCoeff : ℕ := 4 * 10 ^ 8

def dwarfMassApprox : ℚ := dwarfMassCoeff * solarMassApprox

def lsbMassCoeff : ℕ := 3 * 10 ^ 9

def lsbMassApprox : ℚ := lsbMassCoeff * solarMassApprox

/-- \(GMa_0\) for the dwarf stand-in, in m⁴/s⁴. -/
def dwarfFlatSpeedFourth : ℚ :=
  GApprox * dwarfMassApprox * mondAccelApprox

/-- \(GMa_0\) for the low-surface-brightness stand-in, in m⁴/s⁴. -/
def lsbFlatSpeedFourth : ℚ :=
  GApprox * lsbMassApprox * mondAccelApprox

theorem dwarfFlatSpeedFourth_bounds :
    ((502 * 10 ^ 2 : ℚ)) ^ 4 < dwarfFlatSpeedFourth ∧
      dwarfFlatSpeedFourth < ((503 * 10 ^ 2 : ℚ)) ^ 4 := by
  unfold dwarfFlatSpeedFourth dwarfMassApprox dwarfMassCoeff GApprox mondAccelApprox
    solarMassApprox GMantissa GScale solarMassMantissa solarMassScale
    mondAccelMantissa mondAccelScale
  norm_num

theorem lsbFlatSpeedFourth_bounds :
    ((831 * 10 ^ 2 : ℚ)) ^ 4 < lsbFlatSpeedFourth ∧
      lsbFlatSpeedFourth < ((832 * 10 ^ 2 : ℚ)) ^ 4 := by
  unfold lsbFlatSpeedFourth lsbMassApprox lsbMassCoeff GApprox mondAccelApprox
    solarMassApprox GMantissa GScale solarMassMantissa solarMassScale
    mondAccelMantissa mondAccelScale
  norm_num

/-! ### Compactification radius -/

def dwarfRsqOverKpc2 : ℚ :=
  GApprox * dwarfMassApprox / mondAccelApprox / kiloparsecApprox ^ 2

def dwarfRsqOverKpc2_num : ℕ :=
  GMantissa * dwarfMassCoeff * solarMassMantissa *
    10 ^ (30 + mondAccelScale + 2 * kiloparsecScale)

def dwarfRsqOverKpc2_den : ℕ :=
  10 ^ GScale * 10 ^ solarMassScale * mondAccelMantissa *
    kiloparsecMantissa ^ 2 * 10 ^ 38

theorem dwarfRsqOverKpc2_eq_num_div_den :
    dwarfRsqOverKpc2 =
      (dwarfRsqOverKpc2_num : ℚ) / (dwarfRsqOverKpc2_den : ℚ) := by
  unfold dwarfRsqOverKpc2 dwarfMassApprox solarMassApprox kiloparsecApprox
    GApprox mondAccelApprox dwarfRsqOverKpc2_num dwarfRsqOverKpc2_den
  unfold GMantissa GScale solarMassMantissa solarMassScale
    mondAccelMantissa mondAccelScale kiloparsecMantissa kiloparsecScale
    dwarfMassCoeff
  field_simp
  ring

private theorem dwarfRsqOverKpc2_den_pos :
    (0 : ℚ) < (dwarfRsqOverKpc2_den : ℚ) := by
  unfold dwarfRsqOverKpc2_den GScale solarMassScale mondAccelMantissa kiloparsecMantissa
  norm_num

theorem dwarfRsqOverKpc2_bounds :
    ((6816 / 10000 : ℚ)) ^ 2 < dwarfRsqOverKpc2 ∧
      dwarfRsqOverKpc2 < ((6817 / 10000 : ℚ)) ^ 2 := by
  rw [dwarfRsqOverKpc2_eq_num_div_den]
  have hden := dwarfRsqOverKpc2_den_pos
  have hden10 : (0 : ℚ) < (10000 : ℚ) ^ 2 := by norm_num
  constructor
  · rw [lt_div_iff₀ hden]
    have hrew : ((6816 / 10000 : ℚ) ^ 2) * dwarfRsqOverKpc2_den =
        ((6816 : ℚ) ^ 2 * dwarfRsqOverKpc2_den) / 10000 ^ 2 := by field_simp
    rw [hrew, div_lt_iff₀ hden10]
    exact_mod_cast (by
      unfold dwarfRsqOverKpc2_num dwarfRsqOverKpc2_den
      unfold GMantissa GScale solarMassMantissa solarMassScale
        mondAccelMantissa mondAccelScale kiloparsecMantissa kiloparsecScale
        dwarfMassCoeff
      native_decide :
        6816 ^ 2 * dwarfRsqOverKpc2_den < dwarfRsqOverKpc2_num * 10000 ^ 2)
  · rw [div_lt_iff₀ hden]
    have hrew : ((6817 / 10000 : ℚ) ^ 2) * dwarfRsqOverKpc2_den =
        ((6817 : ℚ) ^ 2 * dwarfRsqOverKpc2_den) / 10000 ^ 2 := by field_simp
    rw [hrew, lt_div_iff₀ hden10]
    exact_mod_cast (by
      unfold dwarfRsqOverKpc2_num dwarfRsqOverKpc2_den
      unfold GMantissa GScale solarMassMantissa solarMassScale
        mondAccelMantissa mondAccelScale kiloparsecMantissa kiloparsecScale
        dwarfMassCoeff
      native_decide :
        dwarfRsqOverKpc2_num * 10000 ^ 2 < 6817 ^ 2 * dwarfRsqOverKpc2_den)

noncomputable def dwarfROverKpc : ℝ :=
  sqrt (dwarfRsqOverKpc2 : ℝ)

theorem dwarfROverKpc_bounds :
    (6816 / 10000 : ℝ) < dwarfROverKpc ∧ dwarfROverKpc < 6817 / 10000 := by
  have ⟨hlo, hhi⟩ := dwarfRsqOverKpc2_bounds
  have hlo' : ((6816 / 10000 : ℚ) ^ 2 : ℝ) < (dwarfRsqOverKpc2 : ℝ) := mod_cast hlo
  have hhi' : (dwarfRsqOverKpc2 : ℝ) < ((6817 / 10000 : ℚ) ^ 2 : ℝ) := mod_cast hhi
  unfold dwarfROverKpc
  constructor
  · rw [lt_sqrt (by norm_num)]
    convert hlo' using 1
    norm_num
  · rw [sqrt_lt' (by norm_num)]
    convert hhi' using 1
    norm_num

theorem dwarfThreeR_bounds :
    (204 / 100 : ℝ) < 3 * dwarfROverKpc ∧ 3 * dwarfROverKpc < 205 / 100 := by
  have ⟨hlo, hhi⟩ := dwarfROverKpc_bounds
  constructor <;> linarith

theorem dwarfAntipode_bounds :
    (2141 / 1000 : ℝ) < π * dwarfROverKpc ∧ π * dwarfROverKpc < 2142 / 1000 := by
  have ⟨hlo, hhi⟩ := dwarfROverKpc_bounds
  have hp := pi_gt_d4
  have hp' := pi_lt_d4
  have hRpos : (0 : ℝ) < dwarfROverKpc := lt_trans (by norm_num) hlo
  constructor
  · calc
      (2141 / 1000 : ℝ) < 3.1415 * (6816 / 10000) := by norm_num
      _ < 3.1415 * dwarfROverKpc := mul_lt_mul_of_pos_left hlo (by norm_num)
      _ < π * dwarfROverKpc := mul_lt_mul_of_pos_right hp hRpos
  · calc
      π * dwarfROverKpc < 3.1416 * dwarfROverKpc := mul_lt_mul_of_pos_right hp' hRpos
      _ < 3.1416 * (6817 / 10000) := mul_lt_mul_of_pos_left hhi (by norm_num)
      _ < 2142 / 1000 := by norm_num

/-! ### Speed outside a ball -/

/-- Squared circular speed of a point mass on the dual lattice, in (m/s)²,
read at a radius of `aKpc` kiloparsecs on the dwarf stand-in. -/
noncomputable def dwarfPointSpeedSq (aKpc : ℝ) : ℝ :=
  sqrt (dwarfFlatSpeedFourth : ℝ) *
    (cosh (aKpc / dwarfROverKpc) / sinh (aKpc / dwarfROverKpc))

private lemma coth_mem_of_exp_bounds {x A B : ℝ} (hx : 0 < x) (hA1 : 1 < A)
    (_hAB : A < B) (hlo : A < exp (2 * x)) (hhi : exp (2 * x) < B) :
    1 + 2 / (B - 1) < cosh x / sinh x ∧ cosh x / sinh x < 1 + 2 / (A - 1) := by
  have hexp : 1 < exp (2 * x) := lt_trans hA1 hlo
  rw [coth_eq_one_add hx.ne']
  have hdiv : ∀ {u v : ℝ}, 1 < u → u < v → 2 / (v - 1) < 2 / (u - 1) := by
    intro u v hu huv
    have hupos : 0 < u - 1 := by linarith
    have hvpos : 0 < v - 1 := by linarith
    rw [div_lt_div_iff₀ hvpos hupos]
    nlinarith
  constructor
  · have := hdiv (lt_trans hA1 hlo) hhi
    linarith
  · have := hdiv hA1 hlo
    linarith

private lemma fourth_of_coth {flat cLo cHi lo hi c : ℝ}
    (hflat : 0 < flat) (hc0 : 0 < cLo) (hc : cLo < c) (hc' : c < cHi)
    (hlo : lo < flat * cLo ^ 2) (hhi : flat * cHi ^ 2 < hi) :
    lo < flat * c ^ 2 ∧ flat * c ^ 2 < hi := by
  have hsq : cLo ^ 2 < c ^ 2 := by nlinarith
  have hsq' : c ^ 2 < cHi ^ 2 := by nlinarith
  constructor
  · have : flat * cLo ^ 2 < flat * c ^ 2 := mul_lt_mul_of_pos_left hsq hflat
    linarith
  · have : flat * c ^ 2 < flat * cHi ^ 2 := mul_lt_mul_of_pos_left hsq' hflat
    linarith

private lemma exp_sq_bounds :
    (2.7182818283 : ℝ) ^ 2 < exp 1 ^ 2 ∧ exp 1 ^ 2 < (2.7182818286 : ℝ) ^ 2 := by
  have hlo := exp_one_gt_d9
  have hhi := exp_one_lt_d9
  constructor <;> nlinarith

private lemma exp_347_bounds :
    (14148 / 10000 : ℝ) < exp (347 / 1000) ∧ exp (347 / 1000) < 14149 / 10000 := by
  refine exp_between (x := 347 / 1000) (n := 12) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_348_bounds :
    (14162 / 10000 : ℝ) < exp (348 / 1000) ∧ exp (348 / 1000) < 14163 / 10000 := by
  refine exp_between (x := 348 / 1000) (n := 12) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_867_bounds :
    (23797 / 10000 : ℝ) < exp (867 / 1000) ∧ exp (867 / 1000) < 23798 / 10000 := by
  refine exp_between (x := 867 / 1000) (n := 14) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_869_bounds :
    (23845 / 10000 : ℝ) < exp (869 / 1000) ∧ exp (869 / 1000) < 23846 / 10000 := by
  refine exp_between (x := 869 / 1000) (n := 14) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma dwarf_x_bounds {a lo hi : ℝ} (hlo : 0 < lo) (ha : 0 < a)
    (hxlo : lo < dwarfROverKpc) (hxhi : dwarfROverKpc < hi) :
    a / hi < a / dwarfROverKpc ∧ a / dwarfROverKpc < a / lo := by
  have hR : 0 < dwarfROverKpc := lt_trans hlo hxlo
  constructor
  · exact div_lt_div_of_pos_left ha hR hxhi
  · exact div_lt_div_of_pos_left ha hlo hxlo

private lemma surface_delta_bounds :
    (347 / 1000 : ℝ) < 2 * ((4 / 5) / dwarfROverKpc) - 2 ∧
      2 * ((4 / 5) / dwarfROverKpc) - 2 < 348 / 1000 := by
  have ⟨hRlo, hRhi⟩ := dwarfROverKpc_bounds
  have ⟨hxlo, hxhi⟩ :=
    dwarf_x_bounds (a := 4 / 5) (lo := 6816 / 10000) (hi := 6817 / 10000)
      (by norm_num) (by norm_num) hRlo hRhi
  have h1 : (8000 / 6817 : ℝ) < (4 / 5) / dwarfROverKpc := by
    convert hxlo using 1
    norm_num
  have h2 : (4 / 5) / dwarfROverKpc < 8000 / 6816 := by
    convert hxhi using 1
    norm_num
  have h3 : (347 / 1000 : ℝ) < 2 * (8000 / 6817) - 2 := by norm_num
  have h4 : 2 * (8000 / 6816) - 2 < (348 / 1000 : ℝ) := by norm_num
  constructor <;> linarith

theorem dwarfSurfaceSpeed_bounds :
    ((552 * 10 ^ 2) ^ 4 : ℝ) < dwarfPointSpeedSq (4 / 5) ^ 2 ∧
      dwarfPointSpeedSq (4 / 5) ^ 2 < ((553 * 10 ^ 2) ^ 4 : ℝ) := by
  set x : ℝ := (4 / 5) / dwarfROverKpc
  have ⟨hδlo, hδhi⟩ := surface_delta_bounds
  have hx : 0 < x := by
    have hR : (0 : ℝ) < dwarfROverKpc := lt_trans (by norm_num) dwarfROverKpc_bounds.1
    exact div_pos (by norm_num) hR
  have hexpδ_lo : exp (347 / 1000) < exp (2 * x - 2) := (exp_lt_exp).mpr hδlo
  have hexpδ_hi : exp (2 * x - 2) < exp (348 / 1000) := (exp_lt_exp).mpr hδhi
  have h347 := exp_347_bounds
  have h348 := exp_348_bounds
  have hesq := exp_sq_bounds
  have hmul_lo : (14148 / 10000 : ℝ) * (2.7182818283 : ℝ) ^ 2 <
      exp (2 * x - 2) * exp 1 ^ 2 := by
    have hL : (14148 / 10000 : ℝ) < exp (2 * x - 2) := lt_trans h347.1 hexpδ_lo
    have hR : (2.7182818283 : ℝ) ^ 2 < exp 1 ^ 2 := hesq.1
    have hLp : (0 : ℝ) < 14148 / 10000 := by norm_num
    have hRp : (0 : ℝ) < (2.7182818283 : ℝ) ^ 2 := by positivity
    exact (mul_lt_mul_of_pos_right hL hRp).trans (mul_lt_mul_of_pos_left hR (lt_trans hLp hL))
  have hmul_hi : exp (2 * x - 2) * exp 1 ^ 2 <
      (14163 / 10000 : ℝ) * (2.7182818286 : ℝ) ^ 2 := by
    have hL : exp (2 * x - 2) < 14163 / 10000 := lt_trans hexpδ_hi h348.2
    have hR : exp 1 ^ 2 < (2.7182818286 : ℝ) ^ 2 := hesq.2
    have hposE : (0 : ℝ) < exp 1 ^ 2 := by positivity
    exact (mul_lt_mul_of_pos_right hL hposE).trans
      (mul_lt_mul_of_pos_left hR (by norm_num))
  have htwo : exp (2 * x) = exp (2 * x - 2) * exp 1 ^ 2 := by
    calc
      exp (2 * x) = exp ((2 * x - 2) + 2) := by congr 1; ring
      _ = exp (2 * x - 2) * exp 2 := exp_add _ _
      _ = exp (2 * x - 2) * (exp 1 * exp 1) := by
        congr 1
        rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
      _ = exp (2 * x - 2) * exp 1 ^ 2 := by ring
  rw [← htwo] at hmul_lo hmul_hi
  have hAeq : (14148 / 10000 : ℝ) * (2.7182818283 : ℝ) ^ 2 =
      (14148 / 10000) * (27182818283 / 10000000000) ^ 2 := by norm_num
  have hBeq : (14163 / 10000 : ℝ) * (2.7182818286 : ℝ) ^ 2 =
      (14163 / 10000) * (27182818286 / 10000000000) ^ 2 := by norm_num
  rw [hAeq] at hmul_lo
  rw [hBeq] at hmul_hi
  have hc := coth_mem_of_exp_bounds hx (by norm_num)
    (by norm_num : (14148 / 10000 : ℝ) * (27182818283 / 10000000000) ^ 2 <
      (14163 / 10000) * (27182818286 / 10000000000) ^ 2) hmul_lo hmul_hi
  have hflat_pos : (0 : ℝ) < (dwarfFlatSpeedFourth : ℝ) := by
    have := dwarfFlatSpeedFourth_bounds.1
    exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < (502 * 10 ^ 2) ^ 4) this)
  unfold dwarfPointSpeedSq
  have hsq : (sqrt (dwarfFlatSpeedFourth : ℝ) *
      (cosh x / sinh x)) ^ 2 =
      (dwarfFlatSpeedFourth : ℝ) * (cosh x / sinh x) ^ 2 := by
    rw [mul_pow, sq_sqrt hflat_pos.le]
  rw [hsq]
  refine fourth_of_coth hflat_pos (by norm_num) hc.1 hc.2 ?_ ?_
  · unfold dwarfFlatSpeedFourth dwarfMassApprox dwarfMassCoeff GApprox mondAccelApprox
      solarMassApprox GMantissa GScale solarMassMantissa solarMassScale
      mondAccelMantissa mondAccelScale
    norm_num
  · unfold dwarfFlatSpeedFourth dwarfMassApprox dwarfMassCoeff GApprox mondAccelApprox
      solarMassApprox GMantissa GScale solarMassMantissa solarMassScale
      mondAccelMantissa mondAccelScale
    norm_num

private lemma exp_pow_five_bounds :
    (2.7182818283 : ℝ) ^ 5 < exp 1 ^ 5 ∧ exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 := by
  have hlo := exp_one_gt_d9
  have hhi := exp_one_lt_d9
  constructor
  · exact pow_lt_pow_left₀ hlo (by norm_num) (by decide)
  · exact pow_lt_pow_left₀ hhi (exp_pos 1).le (by decide)

private lemma twoKpc_delta_bounds :
    (867 / 1000 : ℝ) < 2 * (2 / dwarfROverKpc) - 5 ∧
      2 * (2 / dwarfROverKpc) - 5 < 869 / 1000 := by
  have ⟨hRlo, hRhi⟩ := dwarfROverKpc_bounds
  have ⟨hxlo, hxhi⟩ :=
    dwarf_x_bounds (a := 2) (lo := 6816 / 10000) (hi := 6817 / 10000)
      (by norm_num) (by norm_num) hRlo hRhi
  have h1 : (20000 / 6817 : ℝ) < 2 / dwarfROverKpc := by
    convert hxlo using 1
    norm_num
  have h2 : 2 / dwarfROverKpc < 20000 / 6816 := by
    convert hxhi using 1
    norm_num
  have h3 : (867 / 1000 : ℝ) < 2 * (20000 / 6817) - 5 := by norm_num
  have h4 : 2 * (20000 / 6816) - 5 < (869 / 1000 : ℝ) := by norm_num
  constructor <;> linarith

theorem dwarfTwoKpcSpeed_bounds :
    ((50380 : ℕ) ^ 4 : ℝ) < dwarfPointSpeedSq 2 ^ 2 ∧
      dwarfPointSpeedSq 2 ^ 2 < ((50390 : ℕ) ^ 4 : ℝ) := by
  set x : ℝ := 2 / dwarfROverKpc
  have ⟨hδlo, hδhi⟩ := twoKpc_delta_bounds
  have hx : 0 < x := by
    have hR : (0 : ℝ) < dwarfROverKpc := lt_trans (by norm_num) dwarfROverKpc_bounds.1
    exact div_pos (by norm_num) hR
  have hexpδ_lo : exp (867 / 1000) < exp (2 * x - 5) := (exp_lt_exp).mpr hδlo
  have hexpδ_hi : exp (2 * x - 5) < exp (869 / 1000) := (exp_lt_exp).mpr hδhi
  have h867 := exp_867_bounds
  have h869 := exp_869_bounds
  have he5 := exp_pow_five_bounds
  have hmul_lo : (23797 / 10000 : ℝ) * (2.7182818283 : ℝ) ^ 5 <
      exp (2 * x - 5) * exp 1 ^ 5 := by
    have hL : (23797 / 10000 : ℝ) < exp (2 * x - 5) := lt_trans h867.1 hexpδ_lo
    have hRp : (0 : ℝ) < (2.7182818283 : ℝ) ^ 5 := by positivity
    exact (mul_lt_mul_of_pos_right hL hRp).trans
      (mul_lt_mul_of_pos_left he5.1 (lt_trans (by norm_num) hL))
  have hmul_hi : exp (2 * x - 5) * exp 1 ^ 5 <
      (23846 / 10000 : ℝ) * (2.7182818286 : ℝ) ^ 5 := by
    have hL : exp (2 * x - 5) < 23846 / 10000 := lt_trans hexpδ_hi h869.2
    have hposE : (0 : ℝ) < exp 1 ^ 5 := by positivity
    exact (mul_lt_mul_of_pos_right hL hposE).trans
      (mul_lt_mul_of_pos_left he5.2 (by norm_num))
  have htwo : exp (2 * x) = exp (2 * x - 5) * exp 1 ^ 5 := by
    calc
      exp (2 * x) = exp ((2 * x - 5) + 5) := by congr 1; ring
      _ = exp (2 * x - 5) * exp 5 := exp_add _ _
      _ = exp (2 * x - 5) * exp 1 ^ 5 := by
        congr 1
        rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, exp_nat_mul]
  rw [← htwo] at hmul_lo hmul_hi
  have hAeq : (23797 / 10000 : ℝ) * (2.7182818283 : ℝ) ^ 5 =
      (23797 / 10000) * (27182818283 / 10000000000) ^ 5 := by norm_num
  have hBeq : (23846 / 10000 : ℝ) * (2.7182818286 : ℝ) ^ 5 =
      (23846 / 10000) * (27182818286 / 10000000000) ^ 5 := by norm_num
  rw [hAeq] at hmul_lo
  rw [hBeq] at hmul_hi
  have hc := coth_mem_of_exp_bounds hx (by norm_num)
    (by norm_num : (23797 / 10000 : ℝ) * (27182818283 / 10000000000) ^ 5 <
      (23846 / 10000) * (27182818286 / 10000000000) ^ 5) hmul_lo hmul_hi
  have hflat_pos : (0 : ℝ) < (dwarfFlatSpeedFourth : ℝ) := by
    have := dwarfFlatSpeedFourth_bounds.1
    exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < (502 * 10 ^ 2) ^ 4) this)
  unfold dwarfPointSpeedSq
  have hsq : (sqrt (dwarfFlatSpeedFourth : ℝ) * (cosh x / sinh x)) ^ 2 =
      (dwarfFlatSpeedFourth : ℝ) * (cosh x / sinh x) ^ 2 := by
    rw [mul_pow, sq_sqrt hflat_pos.le]
  rw [hsq]
  refine fourth_of_coth hflat_pos (by norm_num) hc.1 hc.2 ?_ ?_
  · unfold dwarfFlatSpeedFourth dwarfMassApprox dwarfMassCoeff GApprox mondAccelApprox
      solarMassApprox GMantissa GScale solarMassMantissa solarMassScale
      mondAccelMantissa mondAccelScale
    norm_num
  · unfold dwarfFlatSpeedFourth dwarfMassApprox dwarfMassCoeff GApprox mondAccelApprox
      solarMassApprox GMantissa GScale solarMassMantissa solarMassScale
      mondAccelMantissa mondAccelScale
    norm_num

theorem dwarfFourKpcSpeed_bounds :
    ((502 * 10 ^ 2) ^ 4 : ℝ) < dwarfPointSpeedSq 4 ^ 2 ∧
      dwarfPointSpeedSq 4 ^ 2 < ((503 * 10 ^ 2) ^ 4 : ℝ) := by
  set x : ℝ := 4 / dwarfROverKpc
  have ⟨hRlo, _⟩ := dwarfROverKpc_bounds
  have ⟨hxlo, _⟩ :=
    dwarf_x_bounds (a := 4) (lo := 6816 / 10000) (hi := 6817 / 10000)
      (by norm_num) (by norm_num) hRlo (dwarfROverKpc_bounds.2)
  have hx : 0 < x := by
    have hR : (0 : ℝ) < dwarfROverKpc := lt_trans (by norm_num) hRlo
    exact div_pos (by norm_num) hR
  have hδ : (735 / 1000 : ℝ) < 2 * x - 11 := by
    have h1 : (40000 / 6817 : ℝ) < x := by
      convert hxlo using 1
      norm_num
    have h2 : (735 / 1000 : ℝ) < 2 * (40000 / 6817) - 11 := by norm_num
    linarith
  have hlog : log 2 < (735 / 1000 : ℝ) := by
    have := log_two_lt_d9
    norm_num at this
    linarith
  have hexp2 : (2 : ℝ) < exp (735 / 1000) := by
    have := (exp_lt_exp).mpr hlog
    rwa [exp_log (by norm_num : (0 : ℝ) < 2)] at this
  have hexpδ : exp (735 / 1000) < exp (2 * x - 11) := (exp_lt_exp).mpr hδ
  have he1 : (27 / 10 : ℝ) < exp 1 := by
    have := exp_one_gt_d9
    norm_num at this
    linarith
  have he11 : (27 / 10 : ℝ) ^ 11 < exp 1 ^ 11 :=
    pow_lt_pow_left₀ he1 (by norm_num) (by decide)
  have hfloor : (2001 : ℝ) < 2 * (27 / 10) ^ 11 := by norm_num
  have htwo : exp (2 * x) = exp (2 * x - 11) * exp 1 ^ 11 := by
    calc
      exp (2 * x) = exp ((2 * x - 11) + 11) := by congr 1; ring
      _ = exp (2 * x - 11) * exp 11 := exp_add _ _
      _ = exp (2 * x - 11) * exp 1 ^ 11 := by
        congr 1
        rw [show (11 : ℝ) = (11 : ℕ) * 1 by norm_num, exp_nat_mul]
  have hexp : (2001 : ℝ) < exp (2 * x) := by
    rw [htwo]
    have hδ2 : (2 : ℝ) < exp (2 * x - 11) := lt_trans hexp2 hexpδ
    have hpos : (0 : ℝ) < exp 1 ^ 11 := by positivity
    have hstep : 2 * (27 / 10) ^ 11 < exp (2 * x - 11) * (27 / 10) ^ 11 :=
      mul_lt_mul_of_pos_right hδ2 (by positivity)
    have hstep2 : exp (2 * x - 11) * (27 / 10) ^ 11 < exp (2 * x - 11) * exp 1 ^ 11 :=
      mul_lt_mul_of_pos_left he11 (lt_trans (by norm_num) hδ2)
    linarith
  have hc : cosh x / sinh x < 1001 / 1000 := by
    rw [coth_eq_one_add hx.ne']
    have hpos : 0 < exp (2 * x) - 1 := by linarith
    have hdiv : 2 / (exp (2 * x) - 1) < 2 / 2000 := by
      rw [div_lt_div_iff₀ hpos (by norm_num)]
      linarith
    linarith
  have hgt : 1 < cosh x / sinh x := by
    rw [coth_eq_one_add hx.ne']
    have : 0 < 2 / (exp (2 * x) - 1) := by
      have : 0 < exp (2 * x) - 1 := by linarith
      positivity
    linarith
  have hflat_pos : (0 : ℝ) < (dwarfFlatSpeedFourth : ℝ) := by
    have := dwarfFlatSpeedFourth_bounds.1
    exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < (502 * 10 ^ 2) ^ 4) this)
  unfold dwarfPointSpeedSq
  have hsq : (sqrt (dwarfFlatSpeedFourth : ℝ) * (cosh x / sinh x)) ^ 2 =
      (dwarfFlatSpeedFourth : ℝ) * (cosh x / sinh x) ^ 2 := by
    rw [mul_pow, sq_sqrt hflat_pos.le]
  rw [hsq]
  refine fourth_of_coth hflat_pos (by norm_num) hgt hc ?_ ?_
  · have hlt : ((502 * 10 ^ 2) ^ 4 : ℝ) < (dwarfFlatSpeedFourth : ℝ) := by
      exact_mod_cast dwarfFlatSpeedFourth_bounds.1
    calc
      ((502 * 10 ^ 2) ^ 4 : ℝ) < (dwarfFlatSpeedFourth : ℝ) := hlt
      _ = (dwarfFlatSpeedFourth : ℝ) * (1 : ℝ) ^ 2 := by ring
  · unfold dwarfFlatSpeedFourth dwarfMassApprox dwarfMassCoeff GApprox mondAccelApprox
      solarMassApprox GMantissa GScale solarMassMantissa solarMassScale
      mondAccelMantissa mondAccelScale
    norm_num

/-! ### From a random aggregate to a larger orbit

Outside the ball the circular specific angular momentum is \(a\,v(a)\).
It increases strictly with radius (`strictMonoOn_dualSpecificAngMomSq`), so a
fluctuation that sets its value sets the radius. On the dwarf stand-in the
step from the surface of the \(0.8\,\mathrm{kpc}\) ball to \(4\,\mathrm{kpc}\)
multiplies the radius by five and the specific angular momentum by a factor
between \(4.53\) and \(4.56\).
-/

noncomputable def dwarfCircSpeed (aKpc : ℝ) : ℝ :=
  sqrt (dwarfPointSpeedSq aKpc)

noncomputable def dwarfSpecificAngMom (aKpc : ℝ) : ℝ :=
  aKpc * dwarfCircSpeed aKpc

private lemma dwarfPointSpeedSq_pos {a : ℝ} (ha : 0 < a) : 0 < dwarfPointSpeedSq a := by
  unfold dwarfPointSpeedSq
  have hR : (0 : ℝ) < dwarfROverKpc := lt_trans (by norm_num) dwarfROverKpc_bounds.1
  have hflat : (0 : ℝ) < (dwarfFlatSpeedFourth : ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < (502 * 10 ^ 2) ^ 4)
      dwarfFlatSpeedFourth_bounds.1)
  exact mul_pos (sqrt_pos.mpr hflat)
    (div_pos (cosh_pos _) (sinh_pos_iff.mpr (div_pos ha hR)))

private lemma dwarfCircSpeed_pos {a : ℝ} (ha : 0 < a) : 0 < dwarfCircSpeed a := by
  unfold dwarfCircSpeed
  exact sqrt_pos.mpr (dwarfPointSpeedSq_pos ha)

private lemma dwarfCircSpeed_fourth {a : ℝ} (ha : 0 ≤ dwarfPointSpeedSq a) :
    dwarfCircSpeed a ^ 4 = dwarfPointSpeedSq a ^ 2 := by
  unfold dwarfCircSpeed
  calc
    (sqrt (dwarfPointSpeedSq a)) ^ 4 = (sqrt (dwarfPointSpeedSq a)) ^ (2 * 2) := by norm_num
    _ = ((sqrt (dwarfPointSpeedSq a)) ^ 2) ^ 2 := by rw [pow_mul]
    _ = dwarfPointSpeedSq a ^ 2 := by rw [sq_sqrt ha]

private lemma dwarfCircSpeed_of_fourth {a lo hi : ℝ} (ha : 0 < a) (hlo : 0 ≤ lo)
    (hhi : 0 ≤ hi)
    (hbounds : lo ^ 4 < dwarfPointSpeedSq a ^ 2 ∧ dwarfPointSpeedSq a ^ 2 < hi ^ 4) :
    lo < dwarfCircSpeed a ∧ dwarfCircSpeed a < hi := by
  have hpos : 0 ≤ dwarfCircSpeed a := (dwarfCircSpeed_pos ha).le
  have h4 := dwarfCircSpeed_fourth (dwarfPointSpeedSq_pos ha).le
  constructor
  · refine (pow_lt_pow_iff_left₀ hlo hpos (by decide : (4 : ℕ) ≠ 0)).mp ?_
    rw [h4]
    exact hbounds.1
  · refine (pow_lt_pow_iff_left₀ hpos hhi (by decide : (4 : ℕ) ≠ 0)).mp ?_
    rw [h4]
    exact hbounds.2

theorem dwarfSurfaceCircSpeed_bounds :
    (552 * 10 ^ 2 : ℝ) < dwarfCircSpeed (4 / 5) ∧
      dwarfCircSpeed (4 / 5) < 553 * 10 ^ 2 :=
  dwarfCircSpeed_of_fourth (by norm_num) (by norm_num) (by norm_num) dwarfSurfaceSpeed_bounds

theorem dwarfFourKpcCircSpeed_bounds :
    (502 * 10 ^ 2 : ℝ) < dwarfCircSpeed 4 ∧ dwarfCircSpeed 4 < 503 * 10 ^ 2 :=
  dwarfCircSpeed_of_fourth (by norm_num) (by norm_num) (by norm_num) dwarfFourKpcSpeed_bounds

theorem dwarfAngMom_ratio_bounds :
    (453 / 100 : ℝ) < dwarfSpecificAngMom 4 / dwarfSpecificAngMom (4 / 5) ∧
      dwarfSpecificAngMom 4 / dwarfSpecificAngMom (4 / 5) < 456 / 100 := by
  have h08 := dwarfSurfaceCircSpeed_bounds
  have h4 := dwarfFourKpcCircSpeed_bounds
  have hp08 := dwarfCircSpeed_pos (by norm_num : (0 : ℝ) < 4 / 5)
  have hratio : dwarfSpecificAngMom 4 / dwarfSpecificAngMom (4 / 5) =
      5 * dwarfCircSpeed 4 / dwarfCircSpeed (4 / 5) := by
    unfold dwarfSpecificAngMom
    field_simp
  rw [hratio]
  have hlo : (453 / 100 : ℝ) < 5 * (502 * 10 ^ 2) / (553 * 10 ^ 2) := by norm_num
  have hhi : 5 * (503 * 10 ^ 2) / (552 * 10 ^ 2) < (456 / 100 : ℝ) := by norm_num
  constructor
  · calc
      (453 / 100 : ℝ) < 5 * (502 * 10 ^ 2) / (553 * 10 ^ 2) := hlo
      _ < 5 * dwarfCircSpeed 4 / dwarfCircSpeed (4 / 5) := by
        rw [div_lt_div_iff₀ (by norm_num) hp08]
        nlinarith [h4.1, h08.2]
  · calc
      5 * dwarfCircSpeed 4 / dwarfCircSpeed (4 / 5) <
          5 * (503 * 10 ^ 2) / (552 * 10 ^ 2) := by
        rw [div_lt_div_iff₀ hp08 (by norm_num)]
        nlinarith [h4.2, h08.1]
      _ < 456 / 100 := hhi

end Gravity

end DstDiophantine
