import DstDiophantine.Gravity.ElectronOrbit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The covalent square

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. Nothing here produces a Bohr spectrum, a
dissociation energy, or a value of `G`.

## What is proved

* On the square the axial and cylindrical factors reduce to one balance
  `squareBalance x = γ(√2 x) - 2√2 γ(x)`, with `x = ℓ/(2R)`.
* That balance is strictly negative throughout the outer well.
* While the proton separation and the electron separation both lie in the
  outer well, the midplane pair has no equilibrium at any ratio of those
  separations. Opposite signs of the two interference factors likewise give
  no equilibrium.
* The second node lies below `4`. Every square whose diagonal and side both
  lie in the first repulsive shell therefore has its phase in `(π/4, π)`.
* On that shell the balance is strictly increasing, and it changes sign between
  `3/2` and `8/5`. There is exactly one such square, and both interference
  factors are negative there.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Finset

/-! ### Balance and elementary bounds -/

noncomputable def squareBalance (x : ℝ) : ℝ :=
  gammaSEqual (sqrt 2 * x) - 2 * sqrt 2 * gammaSEqual x

noncomputable def shellPair (x : ℝ) : ℝ :=
  cosh x * sin x

noncomputable def balanceWeight (x : ℝ) : ℝ :=
  x * (tanh x + cos x / sin x)

noncomputable def sinLo (a b : ℝ) : ℝ := a - a ^ 3 / 6 - b ^ 5 / 100

noncomputable def sinHi (b : ℝ) : ℝ := b - b ^ 3 / 6 + b ^ 5 / 100

noncomputable def cosLo (b : ℝ) : ℝ := 1 - b ^ 2 / 2 - b ^ 4 * (5 / 96)

noncomputable def cosHi (a b : ℝ) : ℝ := 1 - a ^ 2 / 2 + b ^ 4 * (5 / 96)

noncomputable def gammaLower (E1 dLo sLo : ℝ) : ℝ :=
  E1 / 2 * dLo + sLo / (2 * E1)

noncomputable def gammaUpper (E0 dHi sHi : ℝ) : ℝ :=
  E0 / 2 * dHi + sHi / (2 * E0)

lemma continuous_squareBalance : Continuous squareBalance := by
  unfold squareBalance
  exact (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).sub
    (continuous_const.mul continuous_gammaSEqual)

lemma sqrt_two_bounds : (140 / 99 : ℝ) < sqrt 2 ∧ sqrt 2 < 99 / 70 := by
  constructor
  · rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 140 / 99)]
    exact (sqrt_lt_sqrt_iff (by positivity)).mpr (by norm_num)
  · rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 99 / 70)]
    exact (sqrt_lt_sqrt_iff (by positivity)).mpr (by norm_num)

lemma two_sqrt_two_bounds : (280 / 99 : ℝ) < 2 * sqrt 2 ∧ 2 * sqrt 2 < 99 / 35 := by
  obtain ⟨hlo, hhi⟩ := sqrt_two_bounds
  constructor <;> linarith

lemma sqrt_two_lt_two : sqrt 2 < 2 := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), sqrt_lt_sqrt_iff (by positivity)]
  norm_num

lemma one_lt_sqrt_two : (1 : ℝ) < sqrt 2 := by
  rw [show (1 : ℝ) = sqrt 1 by simp, sqrt_lt_sqrt_iff (by positivity)]
  norm_num

lemma gammaSEqual_exp (x : ℝ) :
    gammaSEqual x =
      (exp x / 2) * (cos x - sin x) + (exp (-x) / 2) * (cos x + sin x) := by
  unfold gammaSEqual
  rw [cosh_eq, sinh_eq]
  ring

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

lemma exp_half_bounds : (164 / 100 : ℝ) < exp (1 / 2) ∧ exp (1 / 2) < 165 / 100 := by
  refine exp_between (x := 1 / 2) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma exp_two_fifths_lt : exp (2 / 5) < 3 / 2 := by
  exact (exp_between (x := 2 / 5) (lo := 0) (hi := 3 / 2) (n := 8)
    (by norm_num) (by norm_num) (by decide) (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])).2

lemma exp_four_fifths_lt : exp (4 / 5) < 223 / 100 := by
  exact (exp_between (x := 4 / 5) (lo := 0) (hi := 223 / 100) (n := 10)
    (by norm_num) (by norm_num) (by decide) (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])).2

lemma exp_three_fifths_bounds :
    (1822 / 1000 : ℝ) < exp (3 / 5) ∧ exp (3 / 5) < 1823 / 1000 := by
  refine exp_between (x := 3 / 5) (n := 10) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma exp_four_over_thirtythree_bounds :
    (1128 / 1000 : ℝ) < exp (4 / 33) ∧ exp (4 / 33) < 1129 / 1000 := by
  refine exp_between (x := 4 / 33) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma exp_fortySix_over_oneSevenFive_bounds :
    (13 / 10 : ℝ) < exp (46 / 175) ∧ exp (46 / 175) < 1301 / 1000 := by
  refine exp_between (x := 46 / 175) (n := 10) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

lemma sin_mem_bounds {x a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hx : a ≤ x) (hxb : x ≤ b) :
    sinLo a b ≤ sin x ∧ sin x ≤ sinHi b := by
  have hx0 : 0 ≤ x := le_trans ha hx
  have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact le_trans hxb hb
  have h := sin_bound hxabs
  rw [abs_of_nonneg hx0, abs_sub_le_iff] at h
  obtain ⟨hup, hdn⟩ := h
  have hp : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ 1 → u - u ^ 3 / 6 ≤ v - v ^ 3 / 6 := by
    intro u v hu huv hv
    have hdiff : (v - v ^ 3 / 6) - (u - u ^ 3 / 6) =
        (v - u) * (1 - (v ^ 2 + v * u + u ^ 2) / 6) := by ring
    have hquad : v ^ 2 + v * u + u ^ 2 ≤ 3 := by nlinarith
    nlinarith
  have hpow5 : x ^ 5 ≤ b ^ 5 := pow_le_pow_left₀ hx0 hxb 5
  have hpow5a : a ^ 5 ≤ b ^ 5 := pow_le_pow_left₀ ha (le_trans hx hxb) 5
  constructor
  · have hpa : a - a ^ 3 / 6 ≤ x - x ^ 3 / 6 := hp ha hx (le_trans hxb hb)
    dsimp [sinLo]
    linarith
  · have hpb : x - x ^ 3 / 6 ≤ b - b ^ 3 / 6 := hp hx0 hxb hb
    dsimp [sinHi]
    linarith

lemma cos_mem_bounds {x a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hx : a ≤ x) (hxb : x ≤ b) :
    cosLo b ≤ cos x ∧ cos x ≤ cosHi a b := by
  have hx0 : 0 ≤ x := le_trans ha hx
  have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact le_trans hxb hb
  have h := cos_bound hxabs
  rw [abs_of_nonneg hx0, abs_sub_le_iff] at h
  obtain ⟨hup, hdn⟩ := h
  have hpow4 : x ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ hx0 hxb 4
  have hsq : x ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hx0 hxb 2
  have hsqa : a ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ha hx 2
  constructor
  · dsimp [cosLo]
    linarith
  · dsimp [cosHi]
    linarith

lemma gamma_parts_bounds {x E0 E1 dLo dHi sLo sHi : ℝ}
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1)
    (hDlo : dLo ≤ cos x - sin x) (hDhi : cos x - sin x ≤ dHi) (hdHi : dHi < 0)
    (hSlo : sLo ≤ cos x + sin x) (hShi : cos x + sin x ≤ sHi) (hsLo : 0 < sLo) :
    gammaLower E1 dLo sLo ≤ gammaSEqual x ∧ gammaSEqual x ≤ gammaUpper E0 dHi sHi := by
  rw [gammaSEqual_exp]
  have hinv : 1 / E1 ≤ exp (-x) := by
    simpa [exp_neg] using one_div_le_one_div_of_le (exp_pos x) hE1
  have hinv0 : exp (-x) ≤ 1 / E0 := by
    simpa [exp_neg] using one_div_le_one_div_of_le hE0 hE
  have hSpos : 0 ≤ cos x + sin x := le_trans (le_of_lt hsLo) hSlo
  constructor
  · dsimp [gammaLower]
    have hAD : E1 / 2 * dLo ≤ exp x / 2 * (cos x - sin x) := by nlinarith
    have hmul : (1 / E1) * sLo ≤ exp (-x) * (cos x + sin x) :=
      mul_le_mul hinv hSlo (le_of_lt hsLo) (exp_pos (-x)).le
    have heq : sLo / (2 * E1) = ((1 / E1) * sLo) / 2 := by ring
    have hBS : sLo / (2 * E1) ≤ exp (-x) / 2 * (cos x + sin x) := by
      rw [heq]
      linarith
    linarith
  · dsimp [gammaUpper]
    have hAD : exp x / 2 * (cos x - sin x) ≤ E0 / 2 * dHi := by nlinarith
    have hShi0 : 0 ≤ sHi := le_trans hSpos hShi
    have hmul : exp (-x) * (cos x + sin x) ≤ (1 / E0) * sHi :=
      mul_le_mul hinv0 hShi hSpos (by positivity)
    have hBS : exp (-x) / 2 * (cos x + sin x) ≤ sHi / (2 * E0) := by
      have heq : sHi / (2 * E0) = ((1 / E0) * sHi) / 2 := by ring
      linarith
    linarith

lemma gamma_before {x ε a b E0 E1 : ℝ} (hx : x = π / 2 - ε)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hεa : a ≤ ε) (hεb : ε ≤ b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1)
    (hDhi : sinHi b - cosLo b < 0) (hSlo : 0 < sinLo a b + cosLo b) :
    gammaLower E1 (sinLo a b - cosHi a b) (sinLo a b + cosLo b) ≤ gammaSEqual x ∧
      gammaSEqual x ≤ gammaUpper E0 (sinHi b - cosLo b) (sinHi b + cosHi a b) := by
  have hsin := sin_mem_bounds ha hb hεa hεb
  have hcos := cos_mem_bounds ha hb hεa hεb
  have hsinx : sin x = cos ε := by rw [hx, sin_pi_div_two_sub]
  have hcosx : cos x = sin ε := by rw [hx, cos_pi_div_two_sub]
  apply gamma_parts_bounds hE0 hE hE1
  · rw [hsinx, hcosx]; linarith [hsin.1, hcos.2]
  · rw [hsinx, hcosx]; linarith [hsin.2, hcos.1, hDhi]
  · exact hDhi
  · rw [hsinx, hcosx]; linarith [hsin.1, hcos.1]
  · rw [hsinx, hcosx]; linarith [hsin.2, hcos.2]
  · exact hSlo

lemma gamma_after {x ε a b E0 E1 : ℝ} (hx : x = π / 2 + ε)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hεa : a ≤ ε) (hεb : ε ≤ b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1)
    (hDhi : -(sinLo a b + cosLo b) < 0) (hSlo : 0 < -sinHi b + cosLo b) :
    gammaLower E1 (-(sinHi b + cosHi a b)) (-sinHi b + cosLo b) ≤ gammaSEqual x ∧
      gammaSEqual x ≤
        gammaUpper E0 (-(sinLo a b + cosLo b)) (-sinLo a b + cosHi a b) := by
  have hsin := sin_mem_bounds ha hb hεa hεb
  have hcos := cos_mem_bounds ha hb hεa hεb
  have hsinx : sin x = cos ε := by rw [hx, add_comm, sin_add_pi_div_two]
  have hcosx : cos x = -sin ε := by rw [hx, add_comm, cos_add_pi_div_two]
  apply gamma_parts_bounds hE0 hE hE1
  · rw [hsinx, hcosx]; linarith [hsin.2, hcos.2]
  · rw [hsinx, hcosx]; linarith [hsin.1, hcos.1]
  · exact hDhi
  · rw [hsinx, hcosx]; linarith [hsin.2, hcos.1]
  · rw [hsinx, hcosx]; linarith [hsin.1, hcos.2]
  · exact hSlo

/-! ### Square geometry -/

noncomputable def covalentAxial (ℓ R ρ : ℝ) : ℝ :=
  let rEp := sqrt ((R / 2) ^ 2 + ρ ^ 2)
  1 / (gammaSEqual (ℓ / (2 * R)) * R ^ 2) -
    R / (gammaSEqual (ℓ / (2 * rEp)) * rEp ^ 3)

noncomputable def covalentRadial (ℓ R ρ : ℝ) : ℝ :=
  let rEe := 2 * ρ
  let rEp := sqrt ((R / 2) ^ 2 + ρ ^ 2)
  1 / (gammaSEqual (ℓ / (2 * rEe)) * rEe ^ 2) -
    2 * ρ / (gammaSEqual (ℓ / (2 * rEp)) * rEp ^ 3)

lemma sqrt_two_cube : (sqrt 2) ^ 3 = 2 * sqrt 2 := by
  rw [pow_succ, pow_two, mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma div_sqrt_two_cube (R : ℝ) : (R / sqrt 2) ^ 3 = R ^ 3 / (2 * sqrt 2) := by
  rw [div_pow, sqrt_two_cube]

lemma square_ep {R : ℝ} (hR : 0 < R) :
    sqrt ((R / 2) ^ 2 + (R / 2) ^ 2) = R / sqrt 2 := by
  have hs : (sqrt 2) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hsum : (R / 2) ^ 2 + (R / 2) ^ 2 = (R / sqrt 2) ^ 2 := by
    field_simp [(sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
    nlinarith [hs]
  rw [hsum, sqrt_sq (div_nonneg hR.le (sqrt_nonneg _))]

lemma square_side_phase {ℓ R : ℝ} (hR : 0 < R) :
    ℓ / (2 * (R / sqrt 2)) = sqrt 2 * (ℓ / (2 * R)) := by
  have hs : sqrt 2 ≠ 0 := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hR.ne', hs]

lemma covalentAxial_square {ℓ R : ℝ} (hR : 0 < R) :
    covalentAxial ℓ R (R / 2) =
      (1 / R ^ 2) * (1 / gammaSEqual (ℓ / (2 * R)) -
        2 * sqrt 2 / gammaSEqual (sqrt 2 * (ℓ / (2 * R)))) := by
  unfold covalentAxial
  have hr := square_ep hR
  have hphase := square_side_phase (ℓ := ℓ) hR
  simp only [hr, hphase]
  have hs : sqrt 2 ≠ 0 := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [div_sqrt_two_cube]
  field_simp [hR.ne', hs]

lemma covalentRadial_square {ℓ R : ℝ} (hR : 0 < R) :
    covalentRadial ℓ R (R / 2) =
      (1 / R ^ 2) * (1 / gammaSEqual (ℓ / (2 * R)) -
        2 * sqrt 2 / gammaSEqual (sqrt 2 * (ℓ / (2 * R)))) := by
  unfold covalentRadial
  have hr := square_ep hR
  have hphase := square_side_phase (ℓ := ℓ) hR
  simp only [hr, hphase, show (2 : ℝ) * (R / 2) = R by ring]
  have hs : sqrt 2 ≠ 0 := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [div_sqrt_two_cube]
  field_simp [hR.ne', hs]

theorem covalent_square_components {ℓ R : ℝ} (hR : 0 < R) :
    covalentAxial ℓ R (R / 2) = covalentRadial ℓ R (R / 2) := by
  rw [covalentAxial_square hR, covalentRadial_square hR]

theorem square_factor_zero_iff {x : ℝ}
    (h1 : gammaSEqual x ≠ 0) (h2 : gammaSEqual (sqrt 2 * x) ≠ 0) :
    1 / gammaSEqual x - 2 * sqrt 2 / gammaSEqual (sqrt 2 * x) = 0 ↔
      squareBalance x = 0 := by
  unfold squareBalance
  constructor
  · intro h
    field_simp [h1, h2] at h
    linarith
  · intro h
    field_simp [h1, h2]
    linarith

theorem covalent_square_equilibrium {ℓ R : ℝ} (hR : 0 < R)
    (hγ : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγs : gammaSEqual (sqrt 2 * (ℓ / (2 * R))) ≠ 0) :
    covalentAxial ℓ R (R / 2) = 0 ∧ covalentRadial ℓ R (R / 2) = 0 ↔
      squareBalance (ℓ / (2 * R)) = 0 := by
  have heq : covalentAxial ℓ R (R / 2) = covalentRadial ℓ R (R / 2) :=
    covalent_square_components hR
  have hax := covalentAxial_square (ℓ := ℓ) (R := R) hR
  have hfac : 1 / R ^ 2 ≠ (0 : ℝ) := by positivity
  constructor
  · rintro ⟨hax0, -⟩
    rw [hax, mul_eq_zero] at hax0
    rcases hax0 with h0 | h0
    · exact absurd h0 hfac
    · exact (square_factor_zero_iff hγ hγs).mp h0
  · intro hbal
    have h0 := (square_factor_zero_iff hγ hγs).mpr hbal
    refine ⟨?_, ?_⟩
    · rw [hax, h0, mul_zero]
    · rw [← heq, hax, h0, mul_zero]

/-! ### No square while the diagonal is in the outer well -/

theorem squareBalance_neg_of_outer {x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1) :
    squareBalance x < 0 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hspos : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have hxlt : sqrt 2 * x < sqrt 2 * 1 :=
    mul_lt_mul_of_pos_left (lt_trans hx1 resonanceRoot1_sharp_bounds.2) hspos
  have hside : sqrt 2 * x < π := by
    have h1 : sqrt 2 * 1 = sqrt 2 := by ring
    linarith [sqrt_two_lt_two, pi_gt_three, h1, hxlt]
  have hlt : x < sqrt 2 * x := by nlinarith [one_lt_sqrt_two, hx0]
  have hxI : x ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
    constructor
    · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
      rw [hzero]
      exact hx0.le
    · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
      rw [hzero, zero_add]
      linarith
  have hyI : sqrt 2 * x ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
    constructor
    · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
      rw [hzero]
      exact (mul_pos hspos hx0).le
    · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
      rw [hzero, zero_add]
      exact hside.le
  have hγ : gammaSEqual (sqrt 2 * x) < gammaSEqual x :=
    strictAntiOn_gammaSEqual_even 0 hxI hyI hlt
  have hpos : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node ⟨hx0, hx1⟩
  have hfac : (1 : ℝ) < 2 * sqrt 2 := by linarith [sqrt_two_bounds.1]
  unfold squareBalance
  nlinarith

/-! ### Any aspect ratio in the outer well -/

private lemma evenInterval_of_lt_firstNode {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) resonanceRoot1) :
    t ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
  obtain ⟨ht0, ht1⟩ := ht
  have htπ : t < π :=
    lt_trans ht1 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
  constructor
  · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
    rw [hzero]
    exact ht0.le
  · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
    rw [hzero, zero_add]
    exact htπ.le

/-- Vanishing of both midplane forces forces the interference factors at the
proton separation and the electron separation to stand in the ratio `s^3`. -/
theorem midplane_gamma_ratio {ℓ R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hγR : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγee : gammaSEqual (ℓ / (2 * (2 * ρ))) ≠ 0)
    (hFz : covalentAxial ℓ R ρ = 0) (hFr : covalentRadial ℓ R ρ = 0) :
    gammaSEqual (ℓ / (2 * R)) / gammaSEqual (ℓ / (2 * (2 * ρ))) = (2 * ρ / R) ^ 3 := by
  unfold covalentAxial at hFz
  unfold covalentRadial at hFr
  dsimp only at hFz hFr
  set rEp : ℝ := sqrt ((R / 2) ^ 2 + ρ ^ 2)
  set γR : ℝ := gammaSEqual (ℓ / (2 * R))
  set γee : ℝ := gammaSEqual (ℓ / (2 * (2 * ρ)))
  set γep : ℝ := gammaSEqual (ℓ / (2 * rEp))
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  have hdenR : γR * R ^ 2 ≠ 0 := mul_ne_zero hγR hR2
  have hleft : 1 / (γR * R ^ 2) ≠ 0 := div_ne_zero one_ne_zero hdenR
  have hFz' : 1 / (γR * R ^ 2) = R / (γep * rEp ^ 3) := by linarith
  have hdenEp : γep * rEp ^ 3 ≠ 0 := by
    intro h0
    have hzero : R / (γep * rEp ^ 3) = 0 := by simp [h0]
    exact hleft (hFz'.trans hzero)
  have hrEp : 0 < rEp := by
    dsimp [rEp]
    positivity
  have hγep : γep ≠ 0 := left_ne_zero_of_mul hdenEp
  have hR3 : γep * rEp ^ 3 = γR * R ^ 3 := by
    have hmul := congrArg (fun t => t * ((γR * R ^ 2) * (γep * rEp ^ 3))) hFz'
    field_simp [hγR, hR.ne', hγep, hrEp.ne'] at hmul
    linarith
  have hrEe : (2 : ℝ) * ρ ≠ 0 := mul_ne_zero (by norm_num) hρ.ne'
  have hdenEe : γee * (2 * ρ) ^ 2 ≠ 0 := mul_ne_zero hγee (pow_ne_zero 2 hrEe)
  have hFr' : 1 / (γee * (2 * ρ) ^ 2) = 2 * ρ / (γep * rEp ^ 3) := by linarith
  have hEe : γep * rEp ^ 3 = 2 * ρ * γee * (2 * ρ) ^ 2 := by
    have hmul := congrArg (fun t => t * ((γee * (2 * ρ) ^ 2) * (γep * rEp ^ 3))) hFr'
    field_simp [hγee, hρ.ne', hγep, hrEp.ne'] at hmul
    linarith
  have hEq : γR * R ^ 3 = γee * (8 * ρ ^ 3) := by
    calc
      γR * R ^ 3 = γep * rEp ^ 3 := hR3.symm
      _ = 2 * ρ * γee * (2 * ρ) ^ 2 := hEe
      _ = γee * (8 * ρ ^ 3) := by ring
  have hR3ne : R ^ 3 ≠ 0 := pow_ne_zero 3 hR.ne'
  have hdiv : γR / γee = (2 * ρ / R) ^ 3 := by
    have hpow : (2 * ρ / R) ^ 3 = 8 * ρ ^ 3 / R ^ 3 := by
      field_simp [hR.ne']
      ring
    rw [hpow]
    field_simp [hγee, hR3ne]
    linarith
  simpa [γR, γee] using hdiv

theorem no_midplane_opposite_gamma {ℓ R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hγR : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγee : gammaSEqual (ℓ / (2 * (2 * ρ))) ≠ 0)
    (hopp : gammaSEqual (ℓ / (2 * R)) * gammaSEqual (ℓ / (2 * (2 * ρ))) < 0) :
    ¬ (covalentAxial ℓ R ρ = 0 ∧ covalentRadial ℓ R ρ = 0) := by
  intro h
  obtain ⟨hFz, hFr⟩ := h
  have hratio := midplane_gamma_ratio hR hρ hγR hγee hFz hFr
  have hspos : 0 < (2 * ρ / R) ^ 3 := by positivity
  have hquot : gammaSEqual (ℓ / (2 * R)) / gammaSEqual (ℓ / (2 * (2 * ρ))) < 0 :=
    div_neg_iff.mpr (mul_neg_iff.mp hopp)
  linarith

/-- While the proton separation and the electron separation both lie in the
outer well, the midplane pair has no equilibrium at any aspect ratio. -/
theorem no_midplane_outer_equilibrium {ℓ R ρ : ℝ}
    (hℓ : 0 < ℓ) (hR : 0 < R) (hρ : 0 < ρ)
    (hRwell : ℓ / (2 * R) ∈ Ioo (0 : ℝ) resonanceRoot1)
    (hEwell : ℓ / (2 * (2 * ρ)) ∈ Ioo (0 : ℝ) resonanceRoot1) :
    ¬ (covalentAxial ℓ R ρ = 0 ∧ covalentRadial ℓ R ρ = 0) := by
  intro h
  obtain ⟨hFz, hFr⟩ := h
  set x : ℝ := ℓ / (2 * R)
  set y : ℝ := ℓ / (2 * (2 * ρ))
  have hx : x ∈ Ioo (0 : ℝ) resonanceRoot1 := hRwell
  have hy : y ∈ Ioo (0 : ℝ) resonanceRoot1 := hEwell
  have hγx : gammaSEqual x ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode hx.1.le hx.2).ne'
  have hγy : gammaSEqual y ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode hy.1.le hy.2).ne'
  have hratio := midplane_gamma_ratio (ℓ := ℓ) (R := R) (ρ := ρ) hR hρ hγx hγy hFz hFr
  have hposx : 0 < gammaSEqual x := gammaSEqual_pos_of_lt_firstNode hx.1.le hx.2
  have hposy : 0 < gammaSEqual y := gammaSEqual_pos_of_lt_firstNode hy.1.le hy.2
  have hs : 2 * ρ / R = x / y := by
    dsimp [x, y]
    field_simp [hℓ.ne', hR.ne', hρ.ne']
  have hcube : gammaSEqual x / gammaSEqual y = (x / y) ^ 3 := by
    simpa [x, y, hs] using hratio
  have hxI := evenInterval_of_lt_firstNode hx
  have hyI := evenInterval_of_lt_firstNode hy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hγ : gammaSEqual y < gammaSEqual x :=
      strictAntiOn_gammaSEqual_even 0 hxI hyI hlt
    have hleft : 1 < gammaSEqual x / gammaSEqual y := by
      rw [one_lt_div hposy]
      exact hγ
    have ht0 : 0 < x / y := div_pos hx.1 hy.1
    have ht1 : x / y < 1 := (div_lt_one hy.1).mpr hlt
    have hright : (x / y) ^ 3 < 1 := by
      have hsq : (x / y) ^ 2 < 1 := by nlinarith
      have hcu : (x / y) ^ 3 < x / y := by nlinarith
      linarith
    linarith
  · have hρsq : ρ = R / 2 := by
      have hxy : ℓ / (2 * R) = ℓ / (2 * (2 * ρ)) := by simpa [x, y] using heq
      field_simp [hℓ.ne', hR.ne', hρ.ne'] at hxy
      linarith
    have hax := covalentAxial_square (ℓ := ℓ) (R := R) hR
    rw [hρsq] at hFz
    rw [hax] at hFz
    have hR2 : (1 / R ^ 2) ≠ (0 : ℝ) := by positivity
    have hfac : 1 / gammaSEqual (ℓ / (2 * R)) -
        2 * sqrt 2 / gammaSEqual (sqrt 2 * (ℓ / (2 * R))) = 0 :=
      (mul_eq_zero.mp hFz).resolve_left hR2
    by_cases hside : gammaSEqual (sqrt 2 * x) = 0
    · have hzero : 1 / gammaSEqual (ℓ / (2 * R)) = 0 := by
        simpa [x, hside, div_zero] using hfac
      have hpos : 0 < 1 / gammaSEqual (ℓ / (2 * R)) := one_div_pos.mpr hposx
      linarith
    · have hiff := square_factor_zero_iff (x := ℓ / (2 * R)) hγx (by simpa [x] using hside)
      have hbal0 : squareBalance (ℓ / (2 * R)) = 0 := hiff.mp hfac
      exact (squareBalance_neg_of_outer hx).ne (by simpa [x] using hbal0)
  · have hγ : gammaSEqual x < gammaSEqual y :=
      strictAntiOn_gammaSEqual_even 0 hyI hxI hgt
    have hleft : gammaSEqual x / gammaSEqual y < 1 := by
      rw [div_lt_one hposy]
      exact hγ
    have ht1 : 1 < x / y := (one_lt_div hy.1).mpr hgt
    have hright : 1 < (x / y) ^ 3 := by
      have hsq : 1 < (x / y) ^ 2 := by nlinarith
      have hcu : x / y < (x / y) ^ 3 := by nlinarith
      linarith
    linarith

/-! ### The second node lies below 4 -/

lemma sin_cos_four_gap :
    (1 / 12 : ℝ) < sin (4 - π) - cos (4 - π) := by
  let a : ℝ := 4 - 3.141593
  let b : ℝ := 4 - 3.141592
  have hπlo : 3.141592 < π := pi_gt_d6
  have hπhi : π < 3.141593 := pi_lt_d6
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : b ≤ 1 := by dsimp [b]; linarith
  have hεa : a ≤ 4 - π := by dsimp [a]; linarith
  have hεb : 4 - π ≤ b := by dsimp [b]; linarith
  obtain ⟨hsinlo, -⟩ := sin_mem_bounds ha hb hεa hεb
  obtain ⟨-, hcoshi⟩ := cos_mem_bounds ha hb hεa hεb
  have hcmp : (1 / 12 : ℝ) <
      (a - a ^ 3 / 6 - b ^ 5 / 100) - (1 - a ^ 2 / 2 + b ^ 4 * (5 / 96)) := by
    dsimp [a, b]
    norm_num
  have hsinlo' : a - a ^ 3 / 6 - b ^ 5 / 100 ≤ sin (4 - π) := by
    simpa [sinLo] using hsinlo
  have hcoshi' : cos (4 - π) ≤ 1 - a ^ 2 / 2 + b ^ 4 * (5 / 96) := by
    simpa [cosHi] using hcoshi
  linarith

theorem gammaSEqual_four_pos : 0 < gammaSEqual 4 := by
  have hgap := sin_cos_four_gap
  have hsum : sin (4 - π) + cos (4 - π) ≤ 2 := by
    nlinarith [sin_le_one (4 - π), cos_le_one (4 - π)]
  rw [gammaSEqual_exp]
  have hsin4 : sin 4 = -sin (4 - π) := by
    conv_lhs => rw [show (4 : ℝ) = (4 - π) + π by ring]
    rw [sin_add_pi]
  have hcos4 : cos 4 = -cos (4 - π) := by
    conv_lhs => rw [show (4 : ℝ) = (4 - π) + π by ring]
    rw [cos_add_pi]
  rw [hsin4, hcos4]
  have hE : (27 / 10 : ℝ) < exp 1 := by linarith [exp_one_gt_d9]
  have hE4 : (27 / 10) ^ 4 < exp 4 := by
    have : exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
    rw [this]
    exact pow_lt_pow_left₀ hE (by norm_num) (by norm_num)
  have hnum : (1 : ℝ) < (27 / 10) ^ 4 / 24 := by norm_num
  have hneg : exp (-4) < 1 := by
    rw [← exp_zero]
    exact exp_strictMono (by norm_num)
  have hfirst : exp 4 / 24 < exp 4 / 2 * (sin (4 - π) - cos (4 - π)) := by
    nlinarith [exp_pos 4, hgap]
  have hsec : exp (-4) / 2 * (sin (4 - π) + cos (4 - π)) ≤ exp (-4) := by
    nlinarith [hsum, exp_pos (-4)]
  have hbase : 0 < exp 4 / 24 - exp (-4) := by
    have hdiv : (27 / 10) ^ 4 / 24 < exp 4 / 24 := by
      exact div_lt_div_of_pos_right hE4 (by norm_num)
    linarith [hnum, hneg, hdiv]
  have hposγ : 0 < exp 4 / 2 * (sin (4 - π) - cos (4 - π)) -
      exp (-4) / 2 * (sin (4 - π) + cos (4 - π)) := by
    linarith [hfirst, hsec, hbase]
  convert hposγ using 1
  ring

theorem branchNode_one_lt_four : branchNode 1 < 4 := by
  have hzero : gammaSEqual (branchNode 1) = 0 := (branchNode_spec 1).2
  have hmono := strictMonoOn_gammaSEqual_odd 0
  by_contra hge
  have hle : 4 ≤ branchNode 1 := not_lt.mp hge
  have h4 : (4 : ℝ) ∈ Icc (((2 * 0 + 1 : ℕ) : ℝ) * π) (((2 * 0 + 1 : ℕ) : ℝ) * π + π) := by
    constructor
    · have : (((2 * 0 + 1 : ℕ) : ℝ) * π) = π := by norm_num
      rw [this]
      linarith [pi_lt_four]
    · have : (((2 * 0 + 1 : ℕ) : ℝ) * π + π) = 2 * π := by
        norm_num
        ring
      rw [this]
      linarith [pi_gt_three]
  have hnode : branchNode 1 ∈ Icc (((2 * 0 + 1 : ℕ) : ℝ) * π)
      (((2 * 0 + 1 : ℕ) : ℝ) * π + π) := by
    have hmem := (branchNode_spec 1).1
    have hlo : (((2 * 0 + 1 : ℕ) : ℝ) * π) = (1 : ℝ) * π := by norm_num
    rw [hlo]
    have hmem' : branchNode 1 ∈ Ioo ((1 : ℝ) * π) ((1 : ℝ) * π + π) := by
      simpa [Nat.cast_one] using hmem
    exact Ioo_subset_Icc_self hmem'
  have hγ4 : gammaSEqual 4 ≤ 0 := by
    rcases eq_or_lt_of_le hle with hEq | hlt
    · rw [hEq, hzero]
    · have hltγ := hmono h4 hnode hlt
      rw [hzero] at hltγ
      exact hltγ.le
  exact not_lt_of_ge hγ4 gammaSEqual_four_pos

/-! ### The weight that keeps the balance increasing -/

lemma tanh_strictMono : StrictMono tanh := by
  intro a b hab
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
  have hden_a := cosh_pos a
  have hden_b := cosh_pos b
  rw [div_lt_div_iff₀ hden_a hden_b]
  have : 0 < sinh (b - a) := sinh_pos_iff.mpr (sub_pos.mpr hab)
  rw [sinh_sub] at this
  linarith

lemma cot_lt_cot {a b : ℝ} (ha : 0 < a) (hb : b < π) (hab : a < b) :
    cos b / sin b < cos a / sin a := by
  have hsin_a : 0 < sin a := sin_pos_of_pos_of_lt_pi ha (lt_trans hab hb)
  have hsin_b : 0 < sin b := sin_pos_of_pos_of_lt_pi (lt_trans ha hab) hb
  rw [div_lt_div_iff₀ hsin_b hsin_a]
  have hsub : sin (a - b) < 0 := by
    have hba : 0 < b - a := sub_pos.mpr hab
    have hbaπ : b - a < π := by linarith
    have hpos : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi hba hbaπ
    rw [← neg_sub, sin_neg]
    linarith
  have hId : sin (a - b) = sin a * cos b - cos a * sin b := sin_sub a b
  linarith


lemma tanh_two_mul (x : ℝ) :
    tanh x = (exp (2 * x) - 1) / (exp (2 * x) + 1) := by
  rw [tanh_eq, exp_neg]
  field_simp [(exp_pos x).ne']
  have : exp (2 * x) = exp x * exp x := by
    rw [two_mul, exp_add]
  rw [this]
  ring

lemma tanh_lt_of_exp_lt {x E : ℝ} (hE : 1 < E) (hx : exp (2 * x) < E) :
    tanh x < (E - 1) / (E + 1) := by
  rw [tanh_two_mul]
  have hpos : 0 < exp (2 * x) + 1 := by positivity
  have hEpos : 0 < E + 1 := by linarith
  rw [div_lt_div_iff₀ hpos hEpos]
  nlinarith

lemma tanh_one_lt : tanh 1 < 4 / 5 := by
  have hE : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
  have h2 : exp 2 < 9 := by
    have : exp 2 = exp 1 * exp 1 := by
      rw [← exp_add]
      norm_num
    nlinarith [exp_pos 1, hE]
  have hlt := tanh_lt_of_exp_lt (x := 1) (E := 9) (by norm_num) (by simpa [two_mul] using h2)
  have hfrac : ((9 : ℝ) - 1) / (9 + 1) = 4 / 5 := by norm_num
  linarith

lemma tanh_six_fifths_lt : tanh (6 / 5) < 6 / 7 := by
  have hE : exp 1 < 2.7182818286 := exp_one_lt_d9
  have hprod : exp (12 / 5) < 2.7182818286 ^ 2 * (3 / 2) := by
    have hid : exp (12 / 5) = exp 1 ^ 2 * exp (2 / 5) := by
      have : (12 / 5 : ℝ) = 1 + 1 + 2 / 5 := by norm_num
      rw [this, exp_add, exp_add]
      ring
    nlinarith [exp_pos 1, exp_pos (2 / 5), hE, exp_two_fifths_lt]
  have h13 : 2.7182818286 ^ 2 * (3 / 2) < (13 : ℝ) := by norm_num
  have hlt := tanh_lt_of_exp_lt (x := 6 / 5) (E := 13) (by norm_num)
    (by simpa [show (2 : ℝ) * (6 / 5) = 12 / 5 by norm_num] using lt_trans hprod h13)
  have hfrac : ((13 : ℝ) - 1) / (13 + 1) = 6 / 7 := by norm_num
  linarith

lemma tanh_seven_fifths_lt : tanh (7 / 5) < 9 / 10 := by
  have hE : exp 1 < 2.7182818286 := exp_one_lt_d9
  have hprod : exp (14 / 5) < 2.7182818286 ^ 2 * (223 / 100) := by
    have hid : exp (14 / 5) = exp 1 ^ 2 * exp (4 / 5) := by
      have : (14 / 5 : ℝ) = 1 + 1 + 4 / 5 := by norm_num
      rw [this, exp_add, exp_add]
      ring
    nlinarith [exp_pos 1, exp_pos (4 / 5), hE, exp_four_fifths_lt]
  have h19 : 2.7182818286 ^ 2 * (223 / 100) < (19 : ℝ) := by norm_num
  have hlt := tanh_lt_of_exp_lt (x := 7 / 5) (E := 19) (by norm_num)
    (by simpa [show (2 : ℝ) * (7 / 5) = 14 / 5 by norm_num] using lt_trans hprod h19)
  have hfrac : ((19 : ℝ) - 1) / (19 + 1) = 9 / 10 := by norm_num
  linarith

lemma tanh_three_halves_lt : tanh (3 / 2) < 19 / 20 := by
  have hE : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
  have h3 : exp 3 < 27 := by
    have hid : exp 3 = exp 1 ^ 3 := by
      rw [← exp_nat_mul]
      norm_num
    have hpow : exp 1 ^ 3 < (3 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hE (exp_pos _).le (by norm_num)
    have h27 : (3 : ℝ) ^ 3 = 27 := by norm_num
    linarith
  have hlt := tanh_lt_of_exp_lt (x := 3 / 2) (E := 39) (by norm_num)
    (by simpa [show (2 : ℝ) * (3 / 2) = 3 by norm_num] using
      lt_trans h3 (by norm_num : (27 : ℝ) < 39))
  have hfrac : ((39 : ℝ) - 1) / (39 + 1) = 19 / 20 := by norm_num
  linarith

lemma tan_gt_halfpi_sub {θ b c : ℝ} (hδ0 : 0 < π / 2 - θ) (hb : π / 2 - θ ≤ b)
    (hb1 : b ≤ 1) (hc : 0 < c) (hcmp : c * sinHi b < cosLo b) :
    c < tan θ := by
  set δ := π / 2 - θ
  have hsin : sin δ ≤ sinHi b := (sin_mem_bounds hδ0.le hb1 le_rfl hb).2
  have hcos : cosLo b ≤ cos δ := (cos_mem_bounds hδ0.le hb1 le_rfl hb).1
  have hsinpos : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ0 (by linarith [pi_gt_three, hb, hb1])
  have hlt : c * sin δ < cos δ := by nlinarith
  have hsinθ : sin θ = cos δ := by
    have : θ = π / 2 - δ := by simp [δ]
    rw [this, sin_pi_div_two_sub]
  have hcosθ : cos θ = sin δ := by
    have : θ = π / 2 - δ := by simp [δ]
    rw [this, cos_pi_div_two_sub]
  rw [tan_eq_sin_div_cos, hsinθ, hcosθ]
  exact (lt_div_iff₀ hsinpos).mpr hlt

lemma tan_one_gt_three_halves : (3 / 2 : ℝ) < tan 1 := by
  have hcmp : (3 / 2 : ℝ) * sinHi (3.141593 / 2 - 1) < cosLo (3.141593 / 2 - 1) := by
    simp only [sinHi, cosLo]
    norm_num
  exact tan_gt_halfpi_sub (by linarith [pi_gt_three]) (by linarith [pi_lt_d6])
    (by norm_num) (by norm_num) hcmp

lemma tan_six_fifths_gt : (5 / 2 : ℝ) < tan (6 / 5) := by
  have hcmp : (5 / 2 : ℝ) * sinHi (3.141593 / 2 - 6 / 5) < cosLo (3.141593 / 2 - 6 / 5) := by
    simp only [sinHi, cosLo]
    norm_num
  exact tan_gt_halfpi_sub (by linarith [pi_gt_three]) (by linarith [pi_lt_d6])
    (by norm_num) (by norm_num) hcmp

lemma tan_seven_fifths_gt : (4 : ℝ) < tan (7 / 5) := by
  have hcmp : (4 : ℝ) * sinHi (3.141593 / 2 - 7 / 5) < cosLo (3.141593 / 2 - 7 / 5) := by
    simp only [sinHi, cosLo]
    norm_num
  exact tan_gt_halfpi_sub (by linarith [pi_gt_three]) (by linarith [pi_lt_d6])
    (by norm_num) (by norm_num) hcmp

lemma tan_three_halves_gt : (10 : ℝ) < tan (3 / 2) := by
  have hcmp : (10 : ℝ) * sinHi (3.141593 / 2 - 3 / 2) < cosLo (3.141593 / 2 - 3 / 2) := by
    simp only [sinHi, cosLo]
    norm_num
  exact tan_gt_halfpi_sub (by linarith [pi_gt_three]) (by linarith [pi_lt_d6])
    (by norm_num) (by norm_num) hcmp

lemma cot_of_tan {θ c : ℝ} (hc : 0 < c) (htan : c < tan θ)
    (hsin : 0 < sin θ) (hcos : 0 < cos θ) : cos θ / sin θ < 1 / c := by
  rw [tan_eq_sin_div_cos, lt_div_iff₀ hcos] at htan
  rw [div_lt_div_iff₀ hsin (by positivity)]
  linarith

lemma cot_one_lt : cos 1 / sin 1 < 1 / (3 / 2) :=
  cot_of_tan (by norm_num) tan_one_gt_three_halves
    (sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [pi_gt_three]))
    (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩)

lemma cot_six_fifths_lt : cos (6 / 5) / sin (6 / 5) < 1 / (5 / 2) :=
  cot_of_tan (by norm_num) tan_six_fifths_gt
    (sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [pi_gt_three]))
    (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩)

lemma cot_seven_fifths_lt : cos (7 / 5) / sin (7 / 5) < 1 / 4 :=
  cot_of_tan (by norm_num) tan_seven_fifths_gt
    (sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [pi_gt_three]))
    (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩)

lemma cot_three_halves_lt : cos (3 / 2) / sin (3 / 2) < 1 / 10 :=
  cot_of_tan (by norm_num) tan_three_halves_gt
    (sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [pi_gt_three]))
    (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩)

lemma cot_neg_of_shift {θ k a b : ℝ} (ha : 0 ≤ a) (hb1 : b ≤ 1)
    (hεa : a ≤ θ - π / 2) (hεb : θ - π / 2 ≤ b) (hk : 0 < k)
    (hcmp : cosHi a b < k * sinLo a b) (hlo : 0 < sinLo a b) (hcos : 0 < cosLo b) :
    cos θ / sin θ < -1 / k := by
  set ε := θ - π / 2
  have hsin := sin_mem_bounds ha hb1 hεa hεb
  have hcosb := cos_mem_bounds ha hb1 hεa hεb
  have hsinpos : 0 < sin ε := lt_of_lt_of_le hlo hsin.1
  have hcospos : 0 < cos ε := lt_of_lt_of_le hcos hcosb.1
  have hlt : cos ε < k * sin ε := by
    have hcosle : cos ε ≤ cosHi a b := hcosb.2
    have hsinle : k * sinLo a b ≤ k * sin ε := by nlinarith
    linarith
  have hsinθ : sin θ = cos ε := by
    have : θ = π / 2 + ε := by simp [ε]
    rw [this, add_comm, sin_add_pi_div_two]
  have hcosθ : cos θ = -sin ε := by
    have : θ = π / 2 + ε := by simp [ε]
    rw [this, add_comm, cos_add_pi_div_two]
  rw [hsinθ, hcosθ]
  have hposdiv : 1 / k < sin ε / cos ε := by
    rw [div_lt_div_iff₀ hk hcospos]
    linarith
  have : -(sin ε / cos ε) < -(1 / k) := neg_lt_neg hposdiv
  simpa [neg_div] using this

lemma cot_nine_fifths_lt : cos (9 / 5) / sin (9 / 5) < -1 / 5 := by
  have hcmp : cosHi (9 / 5 - 3.141593 / 2) (9 / 5 - 3.141592 / 2) <
      5 * sinLo (9 / 5 - 3.141593 / 2) (9 / 5 - 3.141592 / 2) := by
    simp only [cosHi, sinLo]
    norm_num
  have hlo : 0 < sinLo (9 / 5 - 3.141593 / 2) (9 / 5 - 3.141592 / 2) := by
    simp only [sinLo]
    norm_num
  have hcos : 0 < cosLo (9 / 5 - 3.141592 / 2) := by
    simp only [cosLo]
    norm_num
  exact cot_neg_of_shift (by norm_num) (by norm_num) (by linarith [pi_lt_d6])
    (by linarith [pi_gt_d6]) (by norm_num) hcmp hlo hcos

lemma cot_two_lt : cos 2 / sin 2 < -(2 / 5) := by
  have hcmp : cosHi (2 - 3.141593 / 2) (2 - 3.141592 / 2) <
      (5 / 2) * sinLo (2 - 3.141593 / 2) (2 - 3.141592 / 2) := by
    simp only [cosHi, sinLo]
    norm_num
  have hlo : 0 < sinLo (2 - 3.141593 / 2) (2 - 3.141592 / 2) := by
    simp only [sinLo]
    norm_num
  have hcos : 0 < cosLo (2 - 3.141592 / 2) := by
    simp only [cosLo]
    norm_num
  have h := cot_neg_of_shift (θ := 2) (k := 5 / 2)
    (a := 2 - 3.141593 / 2) (b := 2 - 3.141592 / 2)
    (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by norm_num) hcmp hlo hcos
  simpa [show (-1 : ℝ) / (5 / 2) = -(2 / 5) by norm_num] using h

lemma mem_gamma_Icc {x : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ π) :
    x ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
  constructor
  · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
    rw [hzero]
    exact hx0
  · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
    rw [hzero, zero_add]
    exact hxπ

theorem balanceWeight_lt {t : ℝ} (ht : t ∈ Ioo (π / 4) π) : balanceWeight t < 49 / 25 := by
  obtain ⟨ht0, htπ⟩ := ht
  have htan1 : tanh t < 1 := tanh_lt_one t
  have hcot_quarter : cos t / sin t < 1 := by
    have h := cot_lt_cot (by linarith [pi_pos] : (0 : ℝ) < π / 4) htπ ht0
    simpa [cos_pi_div_four, sin_pi_div_four] using h
  by_cases h45 : t ≤ 4 / 5
  · unfold balanceWeight
    have hsum : tanh t + cos t / sin t < 2 := by linarith
    nlinarith
  · have h45lt : 4 / 5 < t := not_le.mp h45
    by_cases h1 : t ≤ 1
    · have hth : tanh t < 4 / 5 := by
        rcases eq_or_lt_of_le h1 with rfl | hlt
        · exact tanh_one_lt
        · exact lt_trans (tanh_strictMono hlt) tanh_one_lt
      unfold balanceWeight
      nlinarith
    · have h1lt : 1 < t := not_le.mp h1
      by_cases h65 : t ≤ 6 / 5
      · have hth : tanh t < 6 / 7 := by
          rcases eq_or_lt_of_le h65 with rfl | hlt
          · exact tanh_six_fifths_lt
          · exact lt_trans (tanh_strictMono hlt) tanh_six_fifths_lt
        have hcot1 : cos 1 / sin 1 < 2 / 3 := by
          simpa [show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num] using cot_one_lt
        have hcot : cos t / sin t < 2 / 3 :=
          lt_trans (cot_lt_cot (by norm_num) (by linarith [pi_gt_three]) h1lt) hcot1
        unfold balanceWeight
        nlinarith
      · have h65lt : 6 / 5 < t := not_le.mp h65
        by_cases h75 : t ≤ 7 / 5
        · have hth : tanh t < 9 / 10 := by
            rcases eq_or_lt_of_le h75 with rfl | hlt
            · exact tanh_seven_fifths_lt
            · exact lt_trans (tanh_strictMono hlt) tanh_seven_fifths_lt
          have hcot65 : cos (6 / 5) / sin (6 / 5) < 2 / 5 := by
            simpa [show (1 : ℝ) / (5 / 2) = 2 / 5 by norm_num] using cot_six_fifths_lt
          have hcot : cos t / sin t < 2 / 5 :=
            lt_trans (cot_lt_cot (by norm_num) (by linarith [pi_gt_three]) h65lt) hcot65
          unfold balanceWeight
          nlinarith
        · have h75lt : 7 / 5 < t := not_le.mp h75
          by_cases h32 : t ≤ 3 / 2
          · have hth : tanh t < 19 / 20 := by
              rcases eq_or_lt_of_le h32 with rfl | hlt
              · exact tanh_three_halves_lt
              · exact lt_trans (tanh_strictMono hlt) tanh_three_halves_lt
            have hcot : cos t / sin t < 1 / 4 :=
              lt_trans (cot_lt_cot (by norm_num) (by linarith [pi_gt_three]) h75lt) cot_seven_fifths_lt
            unfold balanceWeight
            nlinarith
          · have h32lt : 3 / 2 < t := not_le.mp h32
            by_cases hhalf : t < π / 2
            · have hcot : cos t / sin t < 1 / 10 :=
                lt_trans (cot_lt_cot (by norm_num) (by linarith [pi_gt_three]) h32lt)
                  cot_three_halves_lt
              have ht8 : t < 8 / 5 := by linarith [pi_lt_d2]
              unfold balanceWeight
              nlinarith
            · have hhalfle : π / 2 ≤ t := not_lt.mp hhalf
              by_cases h95 : t ≤ 9 / 5
              · have hcot : cos t / sin t ≤ 0 := by
                  rcases eq_or_lt_of_le hhalfle with rfl | hlt
                  · simp [cos_pi_div_two, sin_pi_div_two]
                  · have hneg := cot_lt_cot (by linarith [pi_pos]) htπ hlt
                    have : cos (π / 2) / sin (π / 2) = 0 := by
                      simp [cos_pi_div_two, sin_pi_div_two]
                    linarith
                unfold balanceWeight
                nlinarith
              · have h95lt : 9 / 5 < t := not_le.mp h95
                by_cases h2 : t ≤ 2
                · have hcot : cos t / sin t < -1 / 5 :=
                    lt_trans
                      (cot_lt_cot (by norm_num : (0 : ℝ) < 9 / 5) htπ h95lt)
                      cot_nine_fifths_lt
                  unfold balanceWeight
                  nlinarith
                · have h2lt : 2 < t := not_le.mp h2
                  have hcot : cos t / sin t < -(2 / 5) :=
                    lt_trans (cot_lt_cot (by norm_num) htπ h2lt) cot_two_lt
                  have hπ : π < 22 / 7 := by linarith [pi_lt_d4]
                  unfold balanceWeight
                  nlinarith

/-! ### The balance increases through the shell -/

lemma continuous_shellPair : Continuous shellPair := by
  unfold shellPair
  exact continuous_cosh.mul continuous_sin

lemma shell_pair_pos {x : ℝ} (hx0 : 0 < x) (hxπ : x < π) : 0 < shellPair x := by
  unfold shellPair
  exact mul_pos (cosh_pos _) (sin_pos_of_pos_of_lt_pi hx0 hxπ)

lemma hasDerivAt_log_shell_exp {s : ℝ} (hsπ : exp s < π) :
    HasDerivAt (fun t => log (shellPair (exp t))) (balanceWeight (exp s)) s := by
  have hsin : 0 < sin (exp s) := sin_pos_of_pos_of_lt_pi (exp_pos s) hsπ
  have hpair : shellPair (exp s) ≠ 0 := (shell_pair_pos (exp_pos s) hsπ).ne'
  have hexp : HasDerivAt exp (exp s) s := Real.hasDerivAt_exp s
  have hcosh : HasDerivAt (fun t => cosh (exp t)) (sinh (exp s) * exp s) s :=
    (hasDerivAt_cosh (exp s)).comp s hexp
  have hsin' : HasDerivAt (fun t => sin (exp t)) (cos (exp s) * exp s) s :=
    (hasDerivAt_sin (exp s)).comp s hexp
  have hmul := hcosh.mul hsin'
  have hlog := hmul.log (by simpa [shellPair] using hpair)
  apply hlog.congr_deriv
  unfold balanceWeight
  simp only [Pi.mul_apply, tanh_eq_sinh_div_cosh]
  field_simp [(cosh_pos (exp s)).ne', hsin.ne']

lemma shellPair_lt_two {x : ℝ} (hx : π / 4 < x) (hy : sqrt 2 * x < π) :
    shellPair (sqrt 2 * x) < 2 * shellPair x := by
  have hx0 : 0 < x := by linarith [pi_pos]
  have hspos : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have hxy : x < sqrt 2 * x := by
    simpa [mul_one, mul_comm] using mul_lt_mul_of_pos_left one_lt_sqrt_two hx0
  have hxπ : x < π := lt_trans hxy hy
  let φ : ℝ → ℝ := fun s => log (shellPair (exp s))
  let φ' : ℝ → ℝ := fun s => balanceWeight (exp s)
  have hypos : 0 < sqrt 2 * x := mul_pos hspos hx0
  have hloglt : log x < log (sqrt 2 * x) := by
    rw [log_mul hspos.ne' hx0.ne']
    have : 0 < log (sqrt 2) := by
      rw [log_sqrt (by norm_num)]
      exact div_pos (log_pos (by norm_num)) (by norm_num)
    linarith
  have hin : ∀ s ∈ Icc (log x) (log (sqrt 2 * x)), exp s < π := by
    intro s hs
    have hle : exp s ≤ sqrt 2 * x := by
      have := exp_le_exp.mpr hs.2
      rwa [exp_log hypos] at this
    linarith
  have hcont : ContinuousOn φ (Icc (log x) (log (sqrt 2 * x))) := by
    refine ContinuousOn.log ((continuous_shellPair.comp continuous_exp).continuousOn.mono
      (subset_univ _)) ?_
    intro s hs
    exact (shell_pair_pos (exp_pos s) (hin s hs)).ne'
  have hder : ∀ s ∈ Ioo (log x) (log (sqrt 2 * x)), HasDerivAt φ (φ' s) s := by
    intro s hs
    exact hasDerivAt_log_shell_exp (hin s ⟨hs.1.le, hs.2.le⟩)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope φ φ' hloglt hcont hder
  have hcwt : balanceWeight (exp c) < 49 / 25 :=
    balanceWeight_lt ⟨by
      have : π / 4 < exp c := by
        have hle : x ≤ exp c := by
          have := exp_le_exp.mpr (le_of_lt hc.1)
          rwa [exp_log hx0] at this
        linarith
      exact this, hin c ⟨hc.1.le, hc.2.le⟩⟩
  have hgap : log (sqrt 2 * x) - log x = log 2 / 2 := by
    rw [log_mul hspos.ne' hx0.ne', log_sqrt (by norm_num)]
    ring
  have hφ : φ (log (sqrt 2 * x)) - φ (log x) =
      log (shellPair (sqrt 2 * x)) - log (shellPair x) := by
    simp [φ, exp_log hx0, exp_log hypos]
  have hstep : log (shellPair (sqrt 2 * x)) - log (shellPair x) < log 2 := by
    have hne : log (sqrt 2 * x) - log x ≠ 0 := sub_ne_zero.mpr hloglt.ne'
    have hslope' : φ (log (sqrt 2 * x)) - φ (log x) =
        φ' c * (log (sqrt 2 * x) - log x) := by
      have h := hslope
      rw [eq_div_iff hne] at h
      simpa [φ', mul_comm] using h.symm
    rw [← hφ, hslope', hgap]
    have hlog2 : 0 < log 2 := log_pos (by norm_num)
    have hmul : balanceWeight (exp c) * (log 2 / 2) < (49 / 25) * (log 2 / 2) := by
      nlinarith
    have hhalf : (49 / 25) * (log 2 / 2) = (49 / 50) * log 2 := by ring
    have hlt : (49 / 50) * log 2 < log 2 := by nlinarith
    linarith
  have hposx : 0 < shellPair x := shell_pair_pos hx0 hxπ
  have hposy : 0 < shellPair (sqrt 2 * x) := shell_pair_pos hypos hy
  rw [← log_div hposy.ne' hposx.ne'] at hstep
  have hratio : shellPair (sqrt 2 * x) / shellPair x < 2 :=
    (log_lt_log_iff (div_pos hposy hposx) (by norm_num)).mp hstep
  rwa [div_lt_iff₀ hposx] at hratio

lemma hasDerivAt_squareBalance (x : ℝ) :
    HasDerivAt squareBalance
      (2 * sqrt 2 * (2 * cosh x * sin x - cosh (sqrt 2 * x) * sin (sqrt 2 * x))) x := by
  have hγ : HasDerivAt gammaSEqual (-2 * cosh x * sin x) x := hasDerivAt_gammaSEqual x
  have hmul : HasDerivAt (fun t => sqrt 2 * t) (sqrt 2) x := by
    simpa using (hasDerivAt_id x).const_mul (sqrt 2)
  have hcomp : HasDerivAt (fun t => gammaSEqual (sqrt 2 * t))
      ((-2 * cosh (sqrt 2 * x) * sin (sqrt 2 * x)) * sqrt 2) x :=
    (hasDerivAt_gammaSEqual (sqrt 2 * x)).comp x hmul
  have hsub := hcomp.sub (hγ.const_mul (2 * sqrt 2))
  have hderiv :
      (-2 * cosh (sqrt 2 * x) * sin (sqrt 2 * x)) * sqrt 2 -
        2 * sqrt 2 * (-2 * cosh x * sin x) =
      2 * sqrt 2 * (2 * cosh x * sin x - cosh (sqrt 2 * x) * sin (sqrt 2 * x)) := by
    ring
  have hfun : (squareBalance : ℝ → ℝ) =
      fun t => gammaSEqual (sqrt 2 * t) - 2 * sqrt 2 * gammaSEqual t := by
    funext t
    rfl
  rw [hfun]
  exact hsub.congr_deriv hderiv

lemma shell_gap_pos {x : ℝ} (hx : π / 4 < x) (hxπ : x < π) (hy : sqrt 2 * x < 2 * π) :
    0 < 2 * cosh x * sin x - cosh (sqrt 2 * x) * sin (sqrt 2 * x) := by
  by_cases hπ : sqrt 2 * x < π
  · have hlt := shellPair_lt_two hx hπ
    unfold shellPair at hlt
    linarith
  · have hge : π ≤ sqrt 2 * x := not_lt.mp hπ
    have hsinx : 0 < sin x := sin_pos_of_pos_of_lt_pi (by linarith) hxπ
    have hsin_side : sin (sqrt 2 * x) ≤ 0 := by
      rcases eq_or_lt_of_le hge with hEq | hlt
      · rw [← hEq]
        simp
      · have hneg : sin (sqrt 2 * x) = -sin (sqrt 2 * x - π) := by
          conv_lhs => rw [show sqrt 2 * x = (sqrt 2 * x - π) + π by ring]
          rw [sin_add_pi]
        have hpos : 0 < sin (sqrt 2 * x - π) :=
          sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        linarith
    have hcosh : 0 < cosh (sqrt 2 * x) := cosh_pos _
    nlinarith [cosh_pos x]

lemma deriv_squareBalance_pos {x : ℝ}
    (hx : x ∈ Ioo resonanceRoot1 (branchNode 1 / sqrt 2)) :
    0 < deriv squareBalance x := by
  have hx1 : π / 4 < x := lt_trans resonanceRoot1_sharp_bounds.1 hx.1
  have hxnode : sqrt 2 * x < branchNode 1 := by
    have hs : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    have h := hx.2
    rw [lt_div_iff₀ hs] at h
    simpa [mul_comm] using h
  have hxπ : x < π := by
    have h4 : branchNode 1 < 4 := branchNode_one_lt_four
    have h2 : sqrt 2 * x < 4 := lt_trans hxnode h4
    have hsqrt : 4 / sqrt 2 < π := by
      have : (4 / sqrt 2) ^ 2 < π ^ 2 := by
        rw [div_pow, sq_sqrt (by norm_num)]
        have hπ : (8 : ℝ) < π ^ 2 := by nlinarith [pi_gt_three]
        norm_num
        linarith
      have hpos : 0 < 4 / sqrt 2 := by positivity
      exact lt_of_pow_lt_pow_left₀ 2 (by linarith [pi_pos]) this
    have hxlt : x < 4 / sqrt 2 := by
      rw [lt_div_iff₀ (sqrt_pos.mpr (by norm_num))]
      simpa [mul_comm] using h2
    linarith
  have hy2 : sqrt 2 * x < 2 * π := by
    have hmem := (branchNode_spec 1).1
    have hlt : branchNode 1 < 2 * π := by
      have := hmem.2
      simp only [Nat.cast_one, one_mul] at this
      linarith
    linarith
  have hder := hasDerivAt_squareBalance x
  rw [hder.deriv]
  have hgap := shell_gap_pos hx1 hxπ hy2
  have hs : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  nlinarith

theorem squareBalance_strictMonoOn_shell :
    StrictMonoOn squareBalance (Ioo resonanceRoot1 (branchNode 1 / sqrt 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) continuous_squareBalance.continuousOn ?_
  intro x hx
  exact deriv_squareBalance_pos (by simpa [interior_Ioo] using hx)

/-! ### The crossing between 3/2 and 8/5 -/

lemma gamma_three_halves_bounds :
    gammaLower (2.7182818286 * (165 / 100))
      (sinLo (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2) -
        cosHi (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2))
      (sinLo (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2) +
        cosLo (3.141593 / 2 - 3 / 2)) ≤ gammaSEqual (3 / 2) ∧
      gammaSEqual (3 / 2) ≤ gammaUpper (2.7182818283 * (164 / 100))
        (sinHi (3.141593 / 2 - 3 / 2) - cosLo (3.141593 / 2 - 3 / 2))
        (sinHi (3.141593 / 2 - 3 / 2) +
          cosHi (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2)) := by
  have hlo : 2.7182818283 * (164 / 100) < exp (3 / 2) := by
    have hid : exp (3 / 2) = exp 1 * exp (1 / 2) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, exp_add]
    nlinarith [exp_one_gt_d9, exp_half_bounds.1, exp_pos 1, exp_pos (1 / 2)]
  have hhi : exp (3 / 2) < 2.7182818286 * (165 / 100) := by
    have hid : exp (3 / 2) = exp 1 * exp (1 / 2) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_half_bounds.2, exp_pos 1]
  have hD : sinHi (3.141593 / 2 - 3 / 2) - cosLo (3.141593 / 2 - 3 / 2) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2) +
      cosLo (3.141593 / 2 - 3 / 2) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before (x := 3 / 2) (ε := π / 2 - 3 / 2)
    (a := 3.141592 / 2 - 3 / 2) (b := 3.141593 / 2 - 3 / 2)
    (E0 := 2.7182818283 * (164 / 100)) (E1 := 2.7182818286 * (165 / 100))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by norm_num) hlo.le hhi.le hD hS)

lemma gamma_seventy_thirtythree_upper :
    gammaSEqual (70 / 33) ≤
      gammaUpper (1128 / 1000 * 2.7182818283 ^ 2)
        (-(sinLo (70 / 33 - 3.141593 / 2) (70 / 33 - 3.141592 / 2) +
          cosLo (70 / 33 - 3.141592 / 2)))
        (-sinLo (70 / 33 - 3.141593 / 2) (70 / 33 - 3.141592 / 2) +
          cosHi (70 / 33 - 3.141593 / 2) (70 / 33 - 3.141592 / 2)) := by
  have hlo : 1128 / 1000 * 2.7182818283 ^ 2 < exp (70 / 33) := by
    have hid : exp (70 / 33) = exp (4 / 33) * exp 1 ^ 2 := by
      have : (70 / 33 : ℝ) = 4 / 33 + 1 + 1 := by norm_num
      rw [this, exp_add, exp_add]
      ring
    nlinarith [exp_four_over_thirtythree_bounds.1, exp_one_gt_d9, exp_pos (4 / 33), exp_pos 1]
  have hhi : exp (70 / 33) < 1129 / 1000 * 2.7182818286 ^ 2 := by
    have hid : exp (70 / 33) = exp (4 / 33) * exp 1 ^ 2 := by
      have : (70 / 33 : ℝ) = 4 / 33 + 1 + 1 := by norm_num
      rw [this, exp_add, exp_add]
      ring
    nlinarith [exp_four_over_thirtythree_bounds.2, exp_one_lt_d9, exp_pos 1]
  have hD : -(sinLo (70 / 33 - 3.141593 / 2) (70 / 33 - 3.141592 / 2) +
      cosLo (70 / 33 - 3.141592 / 2)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (70 / 33 - 3.141592 / 2) + cosLo (70 / 33 - 3.141592 / 2) := by
    simp only [sinHi, cosLo]; norm_num
  exact (gamma_after (x := 70 / 33) (ε := 70 / 33 - π / 2)
    (a := 70 / 33 - 3.141593 / 2) (b := 70 / 33 - 3.141592 / 2)
    (E0 := 1128 / 1000 * 2.7182818283 ^ 2) (E1 := 1129 / 1000 * 2.7182818286 ^ 2)
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by positivity) hlo.le hhi.le hD hS).2

theorem squareBalance_three_halves_neg : squareBalance (3 / 2) < 0 := by
  have hy : (70 / 33 : ℝ) < sqrt 2 * (3 / 2) := by
    have h := sqrt_two_bounds.1
    have : (70 / 33 : ℝ) = (3 / 2) * (140 / 99) := by norm_num
    nlinarith
  have hyπ : sqrt 2 * (3 / 2) < π := by
    have h := sqrt_two_bounds.2
    have : sqrt 2 * (3 / 2) < 3 := by nlinarith
    linarith [pi_gt_three]
  have h70π : (70 / 33 : ℝ) < π := by linarith [pi_gt_three]
  have hdec : gammaSEqual (sqrt 2 * (3 / 2)) < gammaSEqual (70 / 33) :=
    strictAntiOn_gammaSEqual_even 0 (mem_gamma_Icc (by norm_num) h70π.le)
      (mem_gamma_Icc (by positivity) hyπ.le) hy
  have hbounds := gamma_three_halves_bounds
  have hhi := gamma_seventy_thirtythree_upper
  have hcmp : gammaUpper (1128 / 1000 * 2.7182818283 ^ 2)
      (-(sinLo (70 / 33 - 3.141593 / 2) (70 / 33 - 3.141592 / 2) +
        cosLo (70 / 33 - 3.141592 / 2)))
      (-sinLo (70 / 33 - 3.141593 / 2) (70 / 33 - 3.141592 / 2) +
        cosHi (70 / 33 - 3.141593 / 2) (70 / 33 - 3.141592 / 2)) <
      (99 / 35) * gammaLower (2.7182818286 * (165 / 100))
        (sinLo (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2) -
          cosHi (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2))
        (sinLo (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2) +
          cosLo (3.141593 / 2 - 3 / 2)) := by
    simp only [gammaUpper, gammaLower, sinLo, cosLo, cosHi]
    norm_num
  have hγneg : gammaSEqual (3 / 2) < 0 := by
    have hnegU : gammaUpper (2.7182818283 * (164 / 100))
        (sinHi (3.141593 / 2 - 3 / 2) - cosLo (3.141593 / 2 - 3 / 2))
        (sinHi (3.141593 / 2 - 3 / 2) +
          cosHi (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2)) < 0 := by
      simp only [gammaUpper, sinHi, cosLo, cosHi]; norm_num
    linarith [hbounds.2]
  have hlo := hbounds.1
  have hA : 2 * sqrt 2 < 99 / 35 := two_sqrt_two_bounds.2
  have hP : (99 / 35) * gammaSEqual (3 / 2) < 2 * sqrt 2 * gammaSEqual (3 / 2) := by
    nlinarith
  unfold squareBalance
  linarith

lemma gamma_eight_fifths_upper :
    gammaSEqual (8 / 5) ≤
      gammaUpper (2.7182818283 * (1822 / 1000))
        (-(sinLo (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2) +
          cosLo (8 / 5 - 3.141592 / 2)))
        (-sinLo (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2) +
          cosHi (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2)) := by
  have hlo : 2.7182818283 * (1822 / 1000) < exp (8 / 5) := by
    have hid : exp (8 / 5) = exp 1 * exp (3 / 5) := by
      rw [show (8 / 5 : ℝ) = 1 + 3 / 5 by norm_num, exp_add]
    nlinarith [exp_one_gt_d9, exp_three_fifths_bounds.1, exp_pos 1, exp_pos (3 / 5)]
  have hhi : exp (8 / 5) < 2.7182818286 * (1823 / 1000) := by
    have hid : exp (8 / 5) = exp 1 * exp (3 / 5) := by
      rw [show (8 / 5 : ℝ) = 1 + 3 / 5 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_three_fifths_bounds.2, exp_pos 1]
  have hD : -(sinLo (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2) +
      cosLo (8 / 5 - 3.141592 / 2)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (8 / 5 - 3.141592 / 2) + cosLo (8 / 5 - 3.141592 / 2) := by
    simp only [sinHi, cosLo]; norm_num
  exact (gamma_after (x := 8 / 5) (ε := 8 / 5 - π / 2)
    (a := 8 / 5 - 3.141593 / 2) (b := 8 / 5 - 3.141592 / 2)
    (E0 := 2.7182818283 * (1822 / 1000)) (E1 := 2.7182818286 * (1823 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by norm_num) hlo.le hhi.le hD hS).2

lemma gamma_side_upper_lower :
    gammaLower (1301 / 1000 * 2.7182818286 ^ 2)
      (-(sinHi (396 / 175 - 3.141592 / 2) +
        cosHi (396 / 175 - 3.141593 / 2) (396 / 175 - 3.141592 / 2)))
      (-sinHi (396 / 175 - 3.141592 / 2) +
        cosLo (396 / 175 - 3.141592 / 2)) ≤ gammaSEqual (396 / 175) := by
  have hlo : 13 / 10 * 2.7182818283 ^ 2 < exp (396 / 175) := by
    have hid : exp (396 / 175) = exp (46 / 175) * exp 1 ^ 2 := by
      have : (396 / 175 : ℝ) = 46 / 175 + 1 + 1 := by norm_num
      rw [this, exp_add, exp_add]
      ring
    nlinarith [exp_fortySix_over_oneSevenFive_bounds.1, exp_one_gt_d9, exp_pos (46 / 175),
      exp_pos 1]
  have hhi : exp (396 / 175) < 1301 / 1000 * 2.7182818286 ^ 2 := by
    have hid : exp (396 / 175) = exp (46 / 175) * exp 1 ^ 2 := by
      have : (396 / 175 : ℝ) = 46 / 175 + 1 + 1 := by norm_num
      rw [this, exp_add, exp_add]
      ring
    nlinarith [exp_fortySix_over_oneSevenFive_bounds.2, exp_one_lt_d9, exp_pos 1]
  have hD : -(sinLo (396 / 175 - 3.141593 / 2) (396 / 175 - 3.141592 / 2) +
      cosLo (396 / 175 - 3.141592 / 2)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (396 / 175 - 3.141592 / 2) + cosLo (396 / 175 - 3.141592 / 2) := by
    simp only [sinHi, cosLo]; norm_num
  exact (gamma_after (x := 396 / 175) (ε := 396 / 175 - π / 2)
    (a := 396 / 175 - 3.141593 / 2) (b := 396 / 175 - 3.141592 / 2)
    (E0 := 13 / 10 * 2.7182818283 ^ 2) (E1 := 1301 / 1000 * 2.7182818286 ^ 2)
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by norm_num) hlo.le hhi.le hD hS).1

theorem squareBalance_eight_fifths_pos : 0 < squareBalance (8 / 5) := by
  have hy : sqrt 2 * (8 / 5) < 396 / 175 := by
    have h := sqrt_two_bounds.2
    have : (8 / 5 : ℝ) * (99 / 70) = 396 / 175 := by norm_num
    nlinarith
  have hy0 : 0 < sqrt 2 * (8 / 5) := by positivity
  have hyπ : sqrt 2 * (8 / 5) < π := by
    have : sqrt 2 * (8 / 5) < 3 := by
      have h := sqrt_two_bounds.2
      nlinarith
    linarith [pi_gt_three]
  have hUπ : (396 / 175 : ℝ) < π := by linarith [pi_gt_three]
  have hdec : gammaSEqual (396 / 175) < gammaSEqual (sqrt 2 * (8 / 5)) :=
    strictAntiOn_gammaSEqual_even 0 (mem_gamma_Icc hy0.le hyπ.le)
      (mem_gamma_Icc (by norm_num) hUπ.le) hy
  have hhi := gamma_eight_fifths_upper
  have hlo := gamma_side_upper_lower
  have hγneg : gammaSEqual (8 / 5) < 0 := by
    have hnegU : gammaUpper (2.7182818283 * (1822 / 1000))
        (-(sinLo (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2) +
          cosLo (8 / 5 - 3.141592 / 2)))
        (-sinLo (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2) +
          cosHi (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2)) < 0 := by
      simp only [gammaUpper, sinLo, cosLo, cosHi]; norm_num
    linarith
  have hcmp : (280 / 99) * gammaUpper (2.7182818283 * (1822 / 1000))
      (-(sinLo (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2) +
        cosLo (8 / 5 - 3.141592 / 2)))
      (-sinLo (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2) +
        cosHi (8 / 5 - 3.141593 / 2) (8 / 5 - 3.141592 / 2)) <
      gammaLower (1301 / 1000 * 2.7182818286 ^ 2)
        (-(sinHi (396 / 175 - 3.141592 / 2) +
          cosHi (396 / 175 - 3.141593 / 2) (396 / 175 - 3.141592 / 2)))
        (-sinHi (396 / 175 - 3.141592 / 2) + cosLo (396 / 175 - 3.141592 / 2)) := by
    simp only [gammaUpper, gammaLower, sinLo, sinHi, cosLo, cosHi]
    norm_num
  have hA : 280 / 99 < 2 * sqrt 2 := two_sqrt_two_bounds.1
  have hP : 2 * sqrt 2 * gammaSEqual (8 / 5) < (280 / 99) * gammaSEqual (8 / 5) := by
    nlinarith
  unfold squareBalance
  linarith

theorem exists_unique_square_shell :
    ∃! x : ℝ, x ∈ Ioo resonanceRoot1 (branchNode 1 / sqrt 2) ∧ squareBalance x = 0 := by
  have hnode : π < branchNode 1 := by
    simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1
  have h3 : (3 / 2 : ℝ) ∈ Ioo resonanceRoot1 (branchNode 1 / sqrt 2) := by
    refine ⟨by linarith [resonanceRoot1_sharp_bounds.2], ?_⟩
    have hs : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    rw [lt_div_iff₀ hs]
    have : sqrt 2 * (3 / 2) < 3 := by
      have h := sqrt_two_bounds.2
      nlinarith
    linarith [pi_gt_three, hnode]
  have h8 : (8 / 5 : ℝ) ∈ Ioo resonanceRoot1 (branchNode 1 / sqrt 2) := by
    refine ⟨by linarith [resonanceRoot1_sharp_bounds.2], ?_⟩
    have hs : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    rw [lt_div_iff₀ hs]
    have : sqrt 2 * (8 / 5) < 3 := by
      have h := sqrt_two_bounds.2
      nlinarith
    linarith [pi_gt_three, hnode]
  have hsub := intermediate_value_Ioo (by norm_num : (3 / 2 : ℝ) ≤ 8 / 5)
    continuous_squareBalance.continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (squareBalance (3 / 2)) (squareBalance (8 / 5)) :=
    ⟨squareBalance_three_halves_neg, squareBalance_eight_fifths_pos⟩
  obtain ⟨x, hxI, hx0⟩ := hsub h0
  have hxshell : x ∈ Ioo resonanceRoot1 (branchNode 1 / sqrt 2) :=
    ⟨lt_trans h3.1 hxI.1, lt_trans hxI.2 h8.2⟩
  refine ⟨x, ⟨hxshell, hx0⟩, ?_⟩
  intro y hy
  exact (squareBalance_strictMonoOn_shell.injOn hxshell hy.1 (by rw [hx0, hy.2])).symm

end Gravity

end DstDiophantine
