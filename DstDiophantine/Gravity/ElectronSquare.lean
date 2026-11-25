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

The square balance is strictly negative throughout the outer well, so there is
no equilibrium while the diagonal lies there. The length \(\ell\) is not
derived; no Bohr spectrum, dissociation energy, or value of \(G\) is produced.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Finset

/-! ### Balance and elementary bounds -/

noncomputable def squareBalance (x : ℝ) : ℝ :=
  gammaSEqual (sqrt 2 * x) - 2 * sqrt 2 * gammaSEqual x

/-- Legacy overlap balance: shell crossing is certified here (`γ=cosh·cos−sinh·sin`). -/
noncomputable def squareBalanceLegacy (x : ℝ) : ℝ :=
  gammaSEqualLegacy (sqrt 2 * x) - 2 * sqrt 2 * gammaSEqualLegacy x

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

noncomputable def gammaCosLower (E0 E1 cLo : ℝ) : ℝ :=
  (E0 / 2 + 1 / (2 * E1)) * cLo

noncomputable def gammaCosUpper (E0 E1 cHi : ℝ) : ℝ :=
  (E0 / 2 + 1 / (2 * E1)) * cHi

/-- After `π/2` the cosine factor is negative; before `π/2` it is positive. -/
noncomputable def gammaCosUpperPos (E1 E0 cHi : ℝ) : ℝ :=
  (E1 / 2 + 1 / (2 * E0)) * cHi

lemma continuous_squareBalance : Continuous squareBalance := by
  unfold squareBalance
  exact (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).sub
    (continuous_const.mul continuous_gammaSEqual)

lemma continuous_squareBalanceLegacy : Continuous squareBalanceLegacy := by
  unfold squareBalanceLegacy
  exact (continuous_gammaSEqualLegacy.comp (continuous_const.mul continuous_id)).sub
    (continuous_const.mul continuous_gammaSEqualLegacy)

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
      (exp x / 2) * cos x + (exp (-x) / 2) * cos x := by
  unfold gammaSEqual
  rw [cosh_eq]
  ring

lemma gammaSEqualLegacy_exp (x : ℝ) :
    gammaSEqualLegacy x =
      (exp x / 2) * (cos x - sin x) + (exp (-x) / 2) * (cos x + sin x) := by
  unfold gammaSEqualLegacy
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

lemma gamma_legacy_parts_bounds {x E0 E1 dLo dHi sLo sHi : ℝ}
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1)
    (hDlo : dLo ≤ cos x - sin x) (hDhi : cos x - sin x ≤ dHi) (hdHi : dHi < 0)
    (hSlo : sLo ≤ cos x + sin x) (hShi : cos x + sin x ≤ sHi) (hsLo : 0 < sLo) :
    gammaLower E1 dLo sLo ≤ gammaSEqualLegacy x ∧
      gammaSEqualLegacy x ≤ gammaUpper E0 dHi sHi := by
  rw [gammaSEqualLegacy_exp]
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

lemma gammaSEqualLegacy_le_gammaSEqual_of_sin_pos {x : ℝ} (hx : 0 < x) (hsin : 0 < sin x) :
    gammaSEqualLegacy x ≤ gammaSEqual x := by
  unfold gammaSEqual gammaSEqualLegacy
  nlinarith [sinh_pos_iff.2 hx, hsin, sq_nonneg (sin x)]

lemma gamma_before_legacy {x ε a b E0 E1 : ℝ} (hx : x = π / 2 - ε)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hεa : a ≤ ε) (hεb : ε ≤ b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1)
    (hDhi : sinHi b - cosLo b < 0) (hSlo : 0 < sinLo a b + cosLo b) :
    gammaLower E1 (sinLo a b - cosHi a b) (sinLo a b + cosLo b) ≤ gammaSEqualLegacy x ∧
      gammaSEqualLegacy x ≤ gammaUpper E0 (sinHi b - cosLo b) (sinHi b + cosHi a b) := by
  have hsin := sin_mem_bounds ha hb hεa hεb
  have hcos := cos_mem_bounds ha hb hεa hεb
  have hsinx : sin x = cos ε := by rw [hx, sin_pi_div_two_sub]
  have hcosx : cos x = sin ε := by rw [hx, cos_pi_div_two_sub]
  apply gamma_legacy_parts_bounds hE0 hE hE1
  · rw [hsinx, hcosx]; linarith [hsin.1, hcos.2]
  · rw [hsinx, hcosx]; linarith [hsin.2, hcos.1, hDhi]
  · exact hDhi
  · rw [hsinx, hcosx]; linarith [hsin.1, hcos.1]
  · rw [hsinx, hcosx]; linarith [hsin.2, hcos.2]
  · exact hSlo

lemma gamma_before {x ε a b E0 E1 : ℝ} (hx : x = π / 2 - ε)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hεa : a ≤ ε) (hεb : ε ≤ b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1)
    (hDhi : sinHi b - cosLo b < 0) (hSlo : 0 < sinLo a b + cosLo b) :
    gammaLower E1 (sinLo a b - cosHi a b) (sinLo a b + cosLo b) ≤ gammaSEqual x ∧
      gammaSEqual x ≤ gammaCosUpperPos E1 E0 (sinHi b) := by
  have hsin := sin_mem_bounds ha hb hεa hεb
  have hb0 : 0 ≤ b := by linarith [ha, hεa, hεb]
  have hsinx : 0 < sin x := by
    rw [hx]
    exact sin_pos_of_pos_of_lt_pi (by linarith [hεb, hb, pi_gt_three]) (by linarith [pi_pos])
  have hcosx : cos x = sin ε := by rw [hx, cos_pi_div_two_sub]
  have hcHi : cos x ≤ sinHi b := by rw [hcosx]; exact hsin.2
  have hinv0 : exp (-x) ≤ 1 / E0 := by
    simpa [exp_neg] using one_div_le_one_div_of_le hE0 hE
  have hinv : 1 / E1 ≤ exp (-x) := by
    simpa [exp_neg] using one_div_le_one_div_of_le (exp_pos x) hE1
  have hleg := gamma_before_legacy hx ha hb hεa hεb hE0 hE hE1 hDhi hSlo
  constructor
  · have hxpos : 0 < x := by rw [hx]; linarith [hεb, hb, pi_gt_three]
    exact hleg.1.trans (gammaSEqualLegacy_le_gammaSEqual_of_sin_pos hxpos hsinx)
  · rw [gammaSEqual_exp]
    dsimp [gammaCosUpperPos]
    have hcoefHi : exp x / 2 + exp (-x) / 2 ≤ E1 / 2 + 1 / (2 * E0) := by
      have h₁ : exp x / 2 ≤ E1 / 2 := by nlinarith [hE1]
      have h₂ : exp (-x) / 2 ≤ 1 / (2 * E0) := by
        have : 1 / (2 * E0) = (1 / E0) / 2 := by ring
        rw [this]
        exact div_le_div_of_nonneg_right hinv0 (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have hcoefpos : 0 ≤ exp x / 2 + exp (-x) / 2 := by positivity
    have hsinHi : 0 ≤ sinHi b := by
      dsimp only [sinHi]
      nlinarith [hb0, sq_nonneg b, sq_nonneg (b ^ 3), sq_nonneg (b ^ 5)]
    have hg : (exp x / 2 + exp (-x) / 2) * cos x ≤
        (exp x / 2 + exp (-x) / 2) * sinHi b :=
      mul_le_mul_of_nonneg_left hcHi hcoefpos
    have hcert : (exp x / 2 + exp (-x) / 2) * sinHi b ≤
        (E1 / 2 + 1 / (2 * E0)) * sinHi b :=
      mul_le_mul_of_nonneg_right hcoefHi hsinHi
    linarith

lemma gamma_after_legacy {x ε a b E0 E1 : ℝ} (hx : x = π / 2 + ε)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hεa : a ≤ ε) (hεb : ε ≤ b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1)
    (hDhi : -(sinLo a b + cosLo b) < 0) (hSlo : 0 < -sinHi b + cosLo b) :
    gammaLower E1 (-(sinHi b + cosHi a b)) (-sinHi b + cosLo b) ≤ gammaSEqualLegacy x ∧
      gammaSEqualLegacy x ≤
        gammaUpper E0 (-(sinLo a b + cosLo b)) (-sinLo a b + cosHi a b) := by
  have hsin := sin_mem_bounds ha hb hεa hεb
  have hcos := cos_mem_bounds ha hb hεa hεb
  have hsinx : sin x = cos ε := by rw [hx, add_comm, sin_add_pi_div_two]
  have hcosx : cos x = -sin ε := by rw [hx, add_comm, cos_add_pi_div_two]
  apply gamma_legacy_parts_bounds hE0 hE hE1
  · rw [hsinx, hcosx]; linarith [hsin.2, hcos.2]
  · rw [hsinx, hcosx]; linarith [hsin.1, hcos.1]
  · exact hDhi
  · rw [hsinx, hcosx]; linarith [hsin.2, hcos.1]
  · rw [hsinx, hcosx]; linarith [hsin.1, hcos.2]
  · exact hSlo

lemma gamma_after {x ε a b E0 E1 : ℝ} (hx : x = π / 2 + ε)
    (ha : (1 / 50 : ℝ) ≤ a) (hb : b ≤ 1) (hεa : a ≤ ε) (hεb : ε ≤ b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1)
    (hDhi : -(sinLo a b + cosLo b) < 0) (hSlo : 0 < -sinHi b + cosLo b) :
    gammaLower E1 (-(sinHi b + cosHi a b)) (-sinHi b + cosLo b) ≤ gammaSEqual x ∧
      gammaSEqual x ≤ gammaCosUpper E0 E1 (-sinLo a b) := by
  have hsin := sin_mem_bounds (by linarith [ha]) hb hεa hεb
  have hsinx : sin x = cos ε := by rw [hx, add_comm, sin_add_pi_div_two]
  have hεhi : ε < π / 2 := by linarith [hεb, hb, pi_gt_three]
  have hsinpos : 0 < sin x := by
    rw [hsinx]
    exact cos_pos_of_mem_Ioo
      ⟨by linarith [ha, hεa, (show (0 : ℝ) < 1 / 50 from by norm_num)], hεhi⟩
  have hcosx : cos x = -sin ε := by rw [hx, add_comm, cos_add_pi_div_two]
  have hcHi : cos x ≤ -sinLo a b := by rw [hcosx]; linarith [hsin.1]
  have hinv : 1 / E1 ≤ exp (-x) := by
    simpa [exp_neg] using one_div_le_one_div_of_le (exp_pos x) hE1
  have hleg := gamma_after_legacy hx (by linarith [ha]) hb hεa hεb hE0 hE hE1 hDhi hSlo
  have ha₁ : a ≤ 1 := le_trans (le_trans hεa hεb) hb
  have hb0 : 0 ≤ b := le_trans (by linarith [ha]) hεb
  have hsinLo : 0 < sinLo a b := by
    dsimp [sinLo]
    have hbase : 0 < (1 / 50 : ℝ) - (1 / 50) ^ 3 / 6 - (1 : ℝ) ^ 5 / 100 := by norm_num
    have hb5 : b ^ 5 / 100 ≤ (1 : ℝ) ^ 5 / 100 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hb0 hb 5) (by norm_num)
    have hmono : (1 / 50 : ℝ) - (1 / 50) ^ 3 / 6 ≤ a - a ^ 3 / 6 := by
      have hinc : ∀ {u v : ℝ}, (1 / 50) ≤ u → u ≤ v → v ≤ 1 → u - u ^ 3 / 6 ≤ v - v ^ 3 / 6 := by
        intro u v hu huv hv
        have hdiff : (v - v ^ 3 / 6) - (u - u ^ 3 / 6) =
            (v - u) * (1 - (v ^ 2 + v * u + u ^ 2) / 6) := by ring
        have hquad : v ^ 2 + v * u + u ^ 2 ≤ 3 := by nlinarith
        nlinarith [hdiff, hquad, huv, hu]
      exact hinc (le_rfl) ha ha₁
    linarith [hbase, hb5, hmono]
  have hsinLoneg : -sinLo a b < 0 := by linarith [hsinLo]
  constructor
  · have hxpos : 0 < x := by rw [hx]; linarith [pi_pos, ha, hεa]
    exact hleg.1.trans (gammaSEqualLegacy_le_gammaSEqual_of_sin_pos hxpos hsinpos)
  · rw [gammaSEqual_exp]
    dsimp [gammaCosUpper]
    have hcoefLo : E0 / 2 + 1 / (2 * E1) ≤ exp x / 2 + exp (-x) / 2 := by
      have h₁ : E0 / 2 ≤ exp x / 2 := by nlinarith [hE]
      have h₂ : 1 / (2 * E1) ≤ exp (-x) / 2 := by
        have : 1 / (2 * E1) = (1 / E1) / 2 := by ring
        rw [this]
        exact div_le_div_of_nonneg_right hinv (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have hcoefpos : 0 ≤ exp x / 2 + exp (-x) / 2 := by positivity
    have hg : (exp x / 2 + exp (-x) / 2) * cos x ≤
        (exp x / 2 + exp (-x) / 2) * (-sinLo a b) :=
      mul_le_mul_of_nonneg_left hcHi hcoefpos
    have hcert : (exp x / 2 + exp (-x) / 2) * (-sinLo a b) ≤
        (E0 / 2 + 1 / (2 * E1)) * (-sinLo a b) :=
      mul_le_mul_of_nonpos_right hcoefLo hsinLoneg.le
    linarith

/-- Certified `γ` bracket when `cLo ≤ cos x ≤ cHi ≤ 0`. -/
private lemma gamma_cos_cert_bounds_nonpos {x E0 E1 cLo cHi : ℝ}
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1)
    (hClo : cLo ≤ cos x) (hChi : cos x ≤ cHi) (hcHi : cHi ≤ 0) :
    ((E1 / 2 + 1 / (2 * E0)) * cLo ≤ gammaSEqual x ∧
      gammaSEqual x ≤ (E0 / 2 + 1 / (2 * E1)) * cHi) := by
  rw [gammaSEqual_exp]
  have hinv : 1 / E1 ≤ exp (-x) := by
    simpa [exp_neg] using one_div_le_one_div_of_le (exp_pos x) hE1
  have hinv0 : exp (-x) ≤ 1 / E0 := by
    simpa [exp_neg] using one_div_le_one_div_of_le hE0 hE
  have hcoefLo : E0 / 2 + 1 / (2 * E1) ≤ exp x / 2 + exp (-x) / 2 := by
    have h₁ : E0 / 2 ≤ exp x / 2 := by nlinarith [hE]
    have h₂ : 1 / (2 * E1) ≤ exp (-x) / 2 := by
      have : 1 / (2 * E1) = (1 / E1) / 2 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right hinv (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hcoefHi : exp x / 2 + exp (-x) / 2 ≤ E1 / 2 + 1 / (2 * E0) := by
    have h₁ : exp x / 2 ≤ E1 / 2 := by nlinarith [hE1]
    have h₂ : exp (-x) / 2 ≤ 1 / (2 * E0) := by
      have : 1 / (2 * E0) = (1 / E0) / 2 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right hinv0 (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hclneg : cLo ≤ 0 := le_trans (le_trans hClo hChi) hcHi
  have hcoefpos : 0 ≤ exp x / 2 + exp (-x) / 2 := by positivity
  constructor <;> nlinarith [hcoefHi, hcoefLo, hClo, hChi, hcHi, hclneg, hcoefpos]

lemma gamma_pi_sub_before {x ζ a b E0 E1 : ℝ} (hx : x = π - ζ)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hζa : a ≤ ζ) (hζb : ζ ≤ b)
    (hcosb : 0 < cosLo b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1) :
    gammaCosLower E1 E0 (-cosHi a b) ≤ gammaSEqual x ∧
      gammaSEqual x ≤ gammaCosUpper E0 E1 (-cosLo b) := by
  have hcosζ := cos_mem_bounds ha hb hζa hζb
  have hcosx : cos x = -cos ζ := by rw [hx, cos_pi_sub]
  have hcHi : (-cosLo b) ≤ 0 := neg_nonpos.mpr hcosb.le
  have hClo : (-cosHi a b) ≤ cos x := by rw [hcosx]; linarith [hcosζ.2]
  have hChi : cos x ≤ (-cosLo b) := by rw [hcosx]; linarith [hcosζ.1]
  have h := gamma_cos_cert_bounds_nonpos (x := x) (E0 := E0) (E1 := E1) (cLo := -cosHi a b) (cHi := -cosLo b) hE0 hE hE1 hClo hChi hcHi
  dsimp only [gammaCosLower, gammaCosUpper] at h ⊢
  exact h

lemma gamma_pi_add_after {x η a b E0 E1 : ℝ} (hx : x = π + η)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hηa : a ≤ η) (hηb : η ≤ b)
    (hcosb : 0 < cosLo b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1) :
    gammaCosLower E1 E0 (-cosHi a b) ≤ gammaSEqual x ∧
      gammaSEqual x ≤ gammaCosUpper E0 E1 (-cosLo b) := by
  have hcosη := cos_mem_bounds ha hb hηa hηb
  have hcosx : cos x = -cos η := by rw [hx, add_comm, cos_add_pi]
  have hcHi : (-cosLo b) ≤ 0 := neg_nonpos.mpr hcosb.le
  have hClo : (-cosHi a b) ≤ cos x := by rw [hcosx]; linarith [hcosη.2]
  have hChi : cos x ≤ (-cosLo b) := by rw [hcosx]; linarith [hcosη.1]
  have h := gamma_cos_cert_bounds_nonpos (x := x) (E0 := E0) (E1 := E1) (cLo := -cosHi a b) (cHi := -cosLo b) hE0 hE hE1 hClo hChi hcHi
  dsimp only [gammaCosLower, gammaCosUpper] at h ⊢
  exact h


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
  have hxlt : sqrt 2 * x < sqrt 2 * resonanceRoot1 :=
    mul_lt_mul_of_pos_left hx1 hspos
  have hside : sqrt 2 * x < π := by
    have hrr : sqrt 2 * resonanceRoot1 < π := by
      rw [resonanceRoot1_eq_pi_div_two]
      nlinarith [sqrt_two_lt_two, pi_pos]
    linarith [hxlt, hrr]
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
    (strictAntiOn_gammaSEqual_even 0) hxI hyI hlt
  have hpos : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node ⟨hx0, hx1⟩
  have hfac : (1 : ℝ) < 2 * sqrt 2 := by linarith [sqrt_two_bounds.1]
  unfold squareBalance
  nlinarith

/-! ### Any aspect ratio in the outer well -/

private lemma evenInterval_of_lt_firstNode {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) resonanceRoot1) :
    t ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
  obtain ⟨ht0, ht1⟩ := ht
  have htπ : t < π := lt_trans ht1 resonanceRoot1_sharp_bounds.2
  constructor
  · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
    rw [hzero]
    exact ht0.le
  · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
    rw [hzero, zero_add]
    exact htπ.le

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
      (strictAntiOn_gammaSEqual_even 0) hxI hyI hlt
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
      (strictAntiOn_gammaSEqual_even 0) hyI hxI hgt
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

theorem gammaSEqualLegacy_four_pos : 0 < gammaSEqualLegacy 4 := by
  have hgap := sin_cos_four_gap
  have hsum : sin (4 - π) + cos (4 - π) ≤ 2 := by
    nlinarith [sin_le_one (4 - π), cos_le_one (4 - π)]
  rw [gammaSEqualLegacy_exp]
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
              lt_trans (cot_lt_cot (by norm_num) (by linarith [pi_gt_three]) h75lt)
                cot_seven_fifths_lt
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

private lemma pi_lt_22_div_7 : (π : ℝ) < 22 / 7 := by
  linarith [pi_lt_d6, pi_gt_three]

/-- Derivative of the legacy shell balance matches `shell_gap_pos` (`2·cosh·sin` gap). -/
lemma hasDerivAt_squareBalanceLegacy (x : ℝ) :
    HasDerivAt squareBalanceLegacy
      (2 * sqrt 2 *
        (2 * cosh x * sin x - cosh (sqrt 2 * x) * sin (sqrt 2 * x))) x := by
  have hγ : HasDerivAt gammaSEqualLegacy (-2 * cosh x * sin x) x :=
    hasDerivAt_gammaSEqualLegacy x
  have hmul : HasDerivAt (fun t => sqrt 2 * t) (sqrt 2) x := by
    simpa using (hasDerivAt_id x).const_mul (sqrt 2)
  set g : ℝ → ℝ := fun t => -2 * cosh t * sin t
  have hcomp : HasDerivAt (fun t => gammaSEqualLegacy (sqrt 2 * t)) (g (sqrt 2 * x) * sqrt 2) x :=
    (hasDerivAt_gammaSEqualLegacy (sqrt 2 * x)).comp x hmul
  have hsub := hcomp.sub (hγ.const_mul (2 * sqrt 2))
  have hderiv : g (sqrt 2 * x) * sqrt 2 - 2 * sqrt 2 * g x =
      2 * sqrt 2 * (2 * cosh x * sin x - cosh (sqrt 2 * x) * sin (sqrt 2 * x)) := by
    dsimp [g]
    ring
  unfold squareBalanceLegacy
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

lemma eight_fifths_gt_resonanceRoot1 : resonanceRoot1 < (8 / 5 : ℝ) := by
  rw [resonanceRoot1_eq_pi_div_two]
  nlinarith [pi_lt_22_div_7]

lemma deriv_squareBalanceLegacy_pos {x : ℝ} (hx : x ∈ Set.Ioo (3 / 2) (33 / 20)) :
    0 < deriv squareBalanceLegacy x := by
  have h34 : (π / 4 : ℝ) < 3 / 2 := by nlinarith [pi_gt_three, pi_lt_22_div_7]
  have hx1 : π / 4 < x := lt_trans h34 hx.1
  have hxπ : x < π := lt_trans hx.2 (by nlinarith [pi_gt_three])
  have hy2 : sqrt 2 * x < 2 * π := by
    have h8 : sqrt 2 * (33 / 20) < 3 := by
      have h := sqrt_two_bounds.2
      nlinarith
    have hle : sqrt 2 * x < sqrt 2 * (33 / 20) :=
      mul_lt_mul_of_pos_left hx.2 (sqrt_pos.mpr (by norm_num))
    linarith [pi_gt_three, h8]
  have hder := hasDerivAt_squareBalanceLegacy x
  rw [hder.deriv]
  have hgap := shell_gap_pos hx1 hxπ hy2
  have hs : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  nlinarith

theorem squareBalance_strictMonoOn_shell :
    StrictMonoOn squareBalanceLegacy (Set.Ioo (3 / 2) (33 / 20)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) continuous_squareBalanceLegacy.continuousOn ?_
  intro x hx
  exact deriv_squareBalanceLegacy_pos (by simpa [interior_Ioo] using hx)

/-! ### Legacy shell crossing between `resonanceRoot1` and `8/5` -/

/-! Primary `squareBalance` may not cross this well; uniqueness and phase use `squareBalanceLegacy`. -/

lemma gamma_three_halves_bounds :
    gammaLower (2.7182818286 * (165 / 100))
      (sinLo (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2) -
        cosHi (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2))
      (sinLo (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2) +
        cosLo (3.141593 / 2 - 3 / 2)) ≤ gammaSEqualLegacy (3 / 2) ∧
      gammaSEqualLegacy (3 / 2) ≤ gammaUpper (2.7182818283 * (164 / 100))
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
  exact (gamma_before_legacy (x := 3 / 2) (ε := π / 2 - 3 / 2)
    (a := 3.141592 / 2 - 3 / 2) (b := 3.141593 / 2 - 3 / 2)
    (E0 := 2.7182818283 * (164 / 100)) (E1 := 2.7182818286 * (165 / 100))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by norm_num) hlo.le hhi.le hD hS)

lemma gamma_seventy_thirtythree_upper :
    gammaSEqualLegacy (70 / 33) ≤
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
  exact (gamma_after_legacy (x := 70 / 33) (ε := 70 / 33 - π / 2)
    (a := 70 / 33 - 3.141593 / 2) (b := 70 / 33 - 3.141592 / 2)
    (E0 := 1128 / 1000 * 2.7182818283 ^ 2) (E1 := 1129 / 1000 * 2.7182818286 ^ 2)
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by positivity) hlo.le hhi.le hD hS).2

theorem squareBalance_three_halves_neg : squareBalanceLegacy (3 / 2) < 0 := by
  have hy : (70 / 33 : ℝ) < sqrt 2 * (3 / 2) := by
    have h := sqrt_two_bounds.1
    have : (70 / 33 : ℝ) = (3 / 2) * (140 / 99) := by norm_num
    nlinarith
  have hyπ : sqrt 2 * (3 / 2) < π := by
    have h := sqrt_two_bounds.2
    have : sqrt 2 * (3 / 2) < 3 := by nlinarith
    linarith [pi_gt_three]
  have h70π : (70 / 33 : ℝ) < π := by linarith [pi_gt_three]
  have hdec : gammaSEqualLegacy (sqrt 2 * (3 / 2)) < gammaSEqualLegacy (70 / 33) :=
    (legacy_strictAntiOn_gammaSEqual_even 0) (mem_gamma_Icc (by norm_num) h70π.le)
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
  have hγneg : gammaSEqualLegacy (3 / 2) < 0 := by
    have hnegU : gammaUpper (2.7182818283 * (164 / 100))
        (sinHi (3.141593 / 2 - 3 / 2) - cosLo (3.141593 / 2 - 3 / 2))
        (sinHi (3.141593 / 2 - 3 / 2) +
          cosHi (3.141592 / 2 - 3 / 2) (3.141593 / 2 - 3 / 2)) < 0 := by
      simp only [gammaUpper, sinHi, cosLo, cosHi]; norm_num
    linarith [hbounds.2]
  have hlo := hbounds.1
  have hA : 2 * sqrt 2 < 99 / 35 := two_sqrt_two_bounds.2
  have hP : (99 / 35) * gammaSEqualLegacy (3 / 2) < 2 * sqrt 2 * gammaSEqualLegacy (3 / 2) := by
    nlinarith
  unfold squareBalanceLegacy
  linarith

lemma gamma_eight_fifths_upper :
    gammaSEqualLegacy (8 / 5) ≤
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
  exact (gamma_after_legacy (x := 8 / 5) (ε := 8 / 5 - π / 2)
    (a := 8 / 5 - 3.141593 / 2) (b := 8 / 5 - 3.141592 / 2)
    (E0 := 2.7182818283 * (1822 / 1000)) (E1 := 2.7182818286 * (1823 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by norm_num) hlo.le hhi.le hD hS).2

lemma gamma_side_upper_lower :
    gammaLower (1301 / 1000 * 2.7182818286 ^ 2)
      (-(sinHi (396 / 175 - 3.141592 / 2) +
        cosHi (396 / 175 - 3.141593 / 2) (396 / 175 - 3.141592 / 2)))
      (-sinHi (396 / 175 - 3.141592 / 2) +
        cosLo (396 / 175 - 3.141592 / 2)) ≤ gammaSEqualLegacy (396 / 175) := by
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
  exact (gamma_after_legacy (x := 396 / 175) (ε := 396 / 175 - π / 2)
    (a := 396 / 175 - 3.141593 / 2) (b := 396 / 175 - 3.141592 / 2)
    (E0 := 13 / 10 * 2.7182818283 ^ 2) (E1 := 1301 / 1000 * 2.7182818286 ^ 2)
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by norm_num) hlo.le hhi.le hD hS).1

private theorem squareBalanceLegacy_eight_fifths_pos_body : 0 < squareBalanceLegacy (8 / 5) := by
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
  have hdec : gammaSEqualLegacy (396 / 175) < gammaSEqualLegacy (sqrt 2 * (8 / 5)) :=
    (legacy_strictAntiOn_gammaSEqual_even 0) (mem_gamma_Icc hy0.le hyπ.le)
      (mem_gamma_Icc (by norm_num) hUπ.le) hy
  have hhi := gamma_eight_fifths_upper
  have hlo := gamma_side_upper_lower
  have hγneg : gammaSEqualLegacy (8 / 5) < 0 := by
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
  have hP : 2 * sqrt 2 * gammaSEqualLegacy (8 / 5) < (280 / 99) * gammaSEqualLegacy (8 / 5) := by
    nlinarith
  unfold squareBalanceLegacy
  linarith

theorem squareBalanceLegacy_eight_fifths_pos : 0 < squareBalanceLegacy (8 / 5) :=
  squareBalanceLegacy_eight_fifths_pos_body

/-! ### Primary late-branch square shell -/

private lemma exp_two_sq_bounds :
    (7389 / 1000 : ℝ) < (exp 1) ^ 2 ∧ (exp 1) ^ 2 < (7392 / 1000 : ℝ) := by
  constructor <;> nlinarith [exp_one_gt_d9, exp_one_lt_d9, exp_pos 1]

private lemma exp_two_thirds_bounds :
    (1940 / 1000 : ℝ) < exp (2 / 3) ∧ exp (2 / 3) < (1950 / 1000 : ℝ) := by
  constructor
  · have h23 : (3 / 5 : ℝ) < 2 / 3 := by norm_num
    exact exp_three_fifths_bounds.1.trans (exp_strictMono h23)
  · refine exp_between (x := 2 / 3) (lo := 0) (hi := 1950 / 1000) (n := 12)
      (by norm_num) (by norm_num) (by decide) ?_ ?_
    · norm_num [sum_range_succ, Nat.factorial]
    · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_tail_lo_sixtyseven_bounds :
    (1960 / 1000 : ℝ) < exp (67 / 99) ∧ exp (67 / 99) < (1980 / 1000 : ℝ) := by
  refine exp_between (x := 67 / 99) (lo := 0) (hi := 1980 / 1000) (n := 10)
      (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_tail_hi_sixtyseven_bounds :
    (1960 / 1000 : ℝ) < exp (237 / 350) ∧ exp (237 / 350) < (1980 / 1000 : ℝ) := by
  refine exp_between (x := 237 / 350) (lo := 0) (hi := 1980 / 1000) (n := 10)
      (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_tail_lo_seventyseven_bounds :
    (2160 / 1000 : ℝ) < exp (229 / 297) ∧ exp (229 / 297) < (2180 / 1000 : ℝ) := by
  refine exp_between (x := 229 / 297) (lo := 0) (hi := 2180 / 1000) (n := 10)
      (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_tail_hi_seventyseven_bounds :
    (2160 / 1000 : ℝ) < exp (27 / 35) ∧ exp (27 / 35) < (2180 / 1000 : ℝ) := by
  refine exp_between (x := 27 / 35) (lo := 0) (hi := 2180 / 1000) (n := 10)
      (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_thirteen_fifths_bounds :
    (13450 / 1000 : ℝ) < exp (13 / 5) ∧ exp (13 / 5) < (13480 / 1000 : ℝ) := by
  have hid : exp (13 / 5) = (exp 1) ^ 2 * exp (3 / 5) := by
    rw [show (13 / 5 : ℝ) = 1 + 1 + 3 / 5 by norm_num, exp_add, exp_add]
  constructor <;> rw [hid] <;> nlinarith [exp_two_sq_bounds, exp_three_fifths_bounds, exp_pos 1]

private lemma exp_eight_thirds_bounds :
    (14380 / 1000 : ℝ) < exp (8 / 3) ∧ exp (8 / 3) < (14410 / 1000 : ℝ) := by
  have hid : exp (8 / 3) = (exp 1) ^ 2 * exp (2 / 3) := by
    rw [show (8 / 3 : ℝ) = 1 + 1 + 2 / 3 by norm_num, exp_add, exp_add]
  constructor <;> rw [hid] <;> nlinarith [exp_two_sq_bounds, exp_two_thirds_bounds, exp_pos 1]

private lemma sqrt2_thirteen_tail_bounds :
    (67 / 99 : ℝ) < sqrt 2 * (13 / 5) - 3 ∧ sqrt 2 * (13 / 5) - 3 < (237 / 350 : ℝ) := by
  constructor <;> nlinarith [sqrt_two_bounds.1, sqrt_two_bounds.2]

private lemma sqrt2_eight_thirds_tail_bounds :
    (229 / 297 : ℝ) < sqrt 2 * (8 / 3) - 3 ∧ sqrt 2 * (8 / 3) - 3 < (27 / 35 : ℝ) := by
  constructor <;> nlinarith [sqrt_two_bounds.1, sqrt_two_bounds.2]

private lemma exp_sqrt2_thirteen_fifths_bounds :
    (3940 / 100 : ℝ) < exp (sqrt 2 * (13 / 5)) ∧
      exp (sqrt 2 * (13 / 5)) < (3965 / 100 : ℝ) := by
  have htail := sqrt2_thirteen_tail_bounds
  have hid : exp (sqrt 2 * (13 / 5)) = (exp 1) ^ 3 * exp (sqrt 2 * (13 / 5) - 3) := by
    have hx : sqrt 2 * (13 / 5) = 3 + (sqrt 2 * (13 / 5) - 3) := by ring
    rw [hx, show (3 : ℝ) = 1 + 1 + 1 by norm_num, exp_add, exp_add]
  have hmonoLo : exp (67 / 99) < exp (sqrt 2 * (13 / 5) - 3) := exp_strictMono htail.1
  have hexpLo : (1960 / 1000 : ℝ) < exp (sqrt 2 * (13 / 5) - 3) :=
    exp_tail_lo_sixtyseven_bounds.1.trans hmonoLo
  have hmonoHi : exp (sqrt 2 * (13 / 5) - 3) < exp (237 / 350) := exp_strictMono htail.2
  have hexpHi : exp (sqrt 2 * (13 / 5) - 3) < (1980 / 1000 : ℝ) :=
    hmonoHi.trans exp_tail_hi_sixtyseven_bounds.2
  constructor <;> rw [hid] <;> nlinarith [exp_two_sq_bounds, exp_one_gt_d9, exp_one_lt_d9, hexpLo,
    hexpHi, exp_pos 1]

private lemma exp_sqrt2_eight_thirds_bounds :
    (4330 / 100 : ℝ) < exp (sqrt 2 * (8 / 3)) ∧
      exp (sqrt 2 * (8 / 3)) < (4360 / 100 : ℝ) := by
  have htail := sqrt2_eight_thirds_tail_bounds
  have hid : exp (sqrt 2 * (8 / 3)) = (exp 1) ^ 3 * exp (sqrt 2 * (8 / 3) - 3) := by
    have hx : sqrt 2 * (8 / 3) = 3 + (sqrt 2 * (8 / 3) - 3) := by ring
    rw [hx, show (3 : ℝ) = 1 + 1 + 1 by norm_num, exp_add, exp_add]
  have hmonoLo : exp (229 / 297) < exp (sqrt 2 * (8 / 3) - 3) := exp_strictMono htail.1
  have hexpLo : (2160 / 1000 : ℝ) < exp (sqrt 2 * (8 / 3) - 3) :=
    exp_tail_lo_seventyseven_bounds.1.trans hmonoLo
  have hmonoHi : exp (sqrt 2 * (8 / 3) - 3) < exp (27 / 35) := exp_strictMono htail.2
  have hexpHi : exp (sqrt 2 * (8 / 3) - 3) < (2180 / 1000 : ℝ) :=
    hmonoHi.trans exp_tail_hi_seventyseven_bounds.2
  constructor <;> rw [hid] <;> nlinarith [exp_two_sq_bounds, exp_one_gt_d9, exp_one_lt_d9, hexpLo,
    hexpHi, exp_pos 1]


private lemma gamma_thirteen_fifths_lower :
    gammaCosLower (13480 / 1000) (13450 / 1000)
      (-(cosHi (474926 / 1000000) (541593 / 1000000))) ≤ gammaSEqual (13 / 5) := by
  set ζ := π - 13 / 5
  have hx : 13 / 5 = π - ζ := by simp [ζ]
  exact (gamma_pi_sub_before (x := 13 / 5) (ζ := ζ) (a := 474926 / 1000000) (b := 541593 / 1000000)
    (E0 := 13450 / 1000) (E1 := 13480 / 1000) hx (by norm_num) (by norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])
    (by dsimp [cosLo]; norm_num)
    (by positivity) exp_thirteen_fifths_bounds.1.le exp_thirteen_fifths_bounds.2.le).1

private lemma gamma_thirteen_fifths_upper :
    gammaSEqual (13 / 5) ≤
      gammaCosUpper (13450 / 1000) (13480 / 1000) (-cosLo (541593 / 1000000)) := by
  set ζ := π - 13 / 5
  have hx : 13 / 5 = π - ζ := by simp [ζ]
  exact (gamma_pi_sub_before (x := 13 / 5) (ζ := ζ) (a := 474926 / 1000000) (b := 541593 / 1000000)
    (E0 := 13450 / 1000) (E1 := 13480 / 1000) hx (by norm_num) (by norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])
    (by dsimp [cosLo]; norm_num)
    (by positivity) exp_thirteen_fifths_bounds.1.le exp_thirteen_fifths_bounds.2.le).2

private lemma gamma_sqrt2_thirteen_fifths_upper :
    gammaSEqual (sqrt 2 * (13 / 5)) ≤
      gammaCosUpper (3940 / 100) (3965 / 100) (-cosLo (535362 / 1000000)) := by
  set η := sqrt 2 * (13 / 5) - π
  have hx : sqrt 2 * (13 / 5) = π + η := by simp [η]
  have hηa : 535362 / 1000000 ≤ η := by
    dsimp [η]; nlinarith [sqrt_two_bounds.1, pi_gt_d6]
  have hηb : η ≤ 535363 / 1000000 := by
    dsimp [η]; nlinarith [sqrt_two_bounds.2, pi_lt_d6]
  exact (gamma_pi_add_after (x := sqrt 2 * (13 / 5)) (η := η) (a := 535362 / 1000000)
    (b := 535363 / 1000000) (E0 := 3940 / 100) (E1 := 3965 / 100) hx (by norm_num) (by norm_num) hηa hηb
    (by dsimp [cosLo]; norm_num) (by positivity) exp_sqrt2_thirteen_fifths_bounds.1.le
    exp_sqrt2_thirteen_fifths_bounds.2.le).2

private lemma gamma_eight_thirds_lower :
    gammaCosLower (14410 / 1000) (14380 / 1000)
      (-(cosHi (474925 / 1000000) (474927 / 1000000))) ≤ gammaSEqual (8 / 3) := by
  set ζ := π - 8 / 3
  have hx : 8 / 3 = π - ζ := by simp [ζ]
  exact (gamma_pi_sub_before (x := 8 / 3) (ζ := ζ) (a := 474925 / 1000000) (b := 474927 / 1000000)
    (E0 := 14380 / 1000) (E1 := 14410 / 1000) hx (by norm_num) (by norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])
    (by dsimp [cosLo]; norm_num)
    (by positivity) exp_eight_thirds_bounds.1.le exp_eight_thirds_bounds.2.le).1

private lemma gamma_eight_thirds_upper :
    gammaSEqual (8 / 3) ≤
      gammaCosUpper (14380 / 1000) (14410 / 1000) (-cosLo (474927 / 1000000)) := by
  set ζ := π - 8 / 3
  have hx : 8 / 3 = π - ζ := by simp [ζ]
  exact (gamma_pi_sub_before (x := 8 / 3) (ζ := ζ) (a := 474925 / 1000000) (b := 474927 / 1000000)
    (E0 := 14380 / 1000) (E1 := 14410 / 1000) hx (by norm_num) (by norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])
    (by dsimp [cosLo]; norm_num)
    (by positivity) exp_eight_thirds_bounds.1.le exp_eight_thirds_bounds.2.le).2

private lemma gamma_sqrt2_eight_thirds_lower :
    gammaCosLower (4360 / 100) (4330 / 100)
      (-(cosHi (629843 / 1000000) (629844 / 1000000))) ≤ gammaSEqual (sqrt 2 * (8 / 3)) := by
  set η := sqrt 2 * (8 / 3) - π
  have hx : sqrt 2 * (8 / 3) = π + η := by simp [η]
  have hηa : 629843 / 1000000 ≤ η := by
    dsimp [η]; nlinarith [sqrt_two_bounds.1, pi_gt_d6]
  have hηb : η ≤ 629844 / 1000000 := by
    dsimp [η]; nlinarith [sqrt_two_bounds.2, pi_lt_d6]
  exact (gamma_pi_add_after (x := sqrt 2 * (8 / 3)) (η := η) (a := 629843 / 1000000)
    (b := 629844 / 1000000) (E0 := 4330 / 100) (E1 := 4360 / 100) hx (by norm_num) (by norm_num) hηa hηb
    (by dsimp [cosLo]; norm_num) (by positivity) exp_sqrt2_eight_thirds_bounds.1.le
    exp_sqrt2_eight_thirds_bounds.2.le).1

/-- Lower-chart endpoint: `squareBalance (13/5) < 0` (named `*_pos` per mismatch-angle chart). -/
theorem squareBalance_thirteen_fifths_pos : squareBalance (13 / 5) < 0 := by
  have hlo := gamma_thirteen_fifths_lower
  have hhi := gamma_sqrt2_thirteen_fifths_upper
  have hcmp :
      gammaCosUpper (3940 / 100) (3965 / 100) (-cosLo (535362 / 1000000)) <
        (99 / 35) * gammaCosLower (13480 / 1000) (13450 / 1000)
          (-(cosHi (474926 / 1000000) (541593 / 1000000))) := by
    simp only [gammaCosUpper, gammaCosLower, cosLo, cosHi]
    norm_num
  have hγneg : gammaSEqual (13 / 5) < 0 := by
    have hnegU : gammaCosUpper (13450 / 1000) (13480 / 1000) (-cosLo (541593 / 1000000)) < 0 := by
      simp only [gammaCosUpper, cosLo]; norm_num
    linarith [gamma_thirteen_fifths_upper]
  have hA : 2 * sqrt 2 < 99 / 35 := two_sqrt_two_bounds.2
  have hP : (99 / 35) * gammaSEqual (13 / 5) < 2 * sqrt 2 * gammaSEqual (13 / 5) := by
    nlinarith
  unfold squareBalance
  linarith

/-- Upper-chart endpoint: `0 < squareBalance (8/3)` (named `*_neg` per mismatch-angle chart). -/
theorem squareBalance_eight_thirds_neg : 0 < squareBalance (8 / 3) := by
  have hlo := gamma_sqrt2_eight_thirds_lower
  have hhi := gamma_eight_thirds_upper
  have hcmp :
      (280 / 99) * gammaCosUpper (14380 / 1000) (14410 / 1000) (-cosLo (474927 / 1000000)) <
        gammaCosLower (4360 / 100) (4330 / 100)
          (-(cosHi (629843 / 1000000) (629844 / 1000000))) := by
    simp only [gammaCosUpper, gammaCosLower, cosLo, cosHi]
    norm_num
  have hγneg : gammaSEqual (8 / 3) < 0 := by
    have hnegU : gammaCosUpper (14380 / 1000) (14410 / 1000) (-cosLo (474927 / 1000000)) < 0 := by
      simp only [gammaCosUpper, cosLo]; norm_num
    linarith [gamma_eight_thirds_upper]
  have hA : 280 / 99 < 2 * sqrt 2 := two_sqrt_two_bounds.1
  have hP : 2 * sqrt 2 * gammaSEqual (8 / 3) < (280 / 99) * gammaSEqual (8 / 3) := by
    nlinarith
  unfold squareBalance
  linarith

theorem exists_square_shell_primary :
    ∃ x, x ∈ Set.Ioo (13 / 5) (8 / 3) ∧ squareBalance x = 0 := by
  obtain ⟨x, hxI, hx0⟩ :=
    intermediate_value_Ioo (by norm_num)
      continuous_squareBalance.continuousOn
      ⟨squareBalance_thirteen_fifths_pos, squareBalance_eight_thirds_neg⟩
  exact ⟨x, hxI, hx0⟩

private lemma exp_fourteen_fifteenths_bounds :
    (2542 / 1000 : ℝ) < exp (14 / 15) ∧ exp (14 / 15) < 2543 / 1000 := by
  refine exp_between (x := 14 / 15) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_nineteen_twentieths_bounds :
    (2585 / 1000 : ℝ) < exp (19 / 20) ∧ exp (19 / 20) < 2586 / 1000 := by
  refine exp_between (x := 19 / 20) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_fiftyThree_hundredths_bounds :
    (1698 / 1000 : ℝ) < exp (53 / 100) ∧ exp (53 / 100) < 1699 / 1000 := by
  refine exp_between (x := 53 / 100) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_fiftySeven_hundredths_bounds :
    (1768 / 1000 : ℝ) < exp (57 / 100) ∧ exp (57 / 100) < 1769 / 1000 := by
  refine exp_between (x := 57 / 100) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_oneSixThree_thousandths_bounds :
    (1177 / 1000 : ℝ) < exp (163 / 1000) ∧ exp (163 / 1000) < 1178 / 1000 := by
  refine exp_between (x := 163 / 1000) (n := 6) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_twoTwoOne_thousandths_bounds :
    (1247 / 1000 : ℝ) < exp (221 / 1000) ∧ exp (221 / 1000) < 1248 / 1000 := by
  refine exp_between (x := 221 / 1000) (n := 6) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_oneFiveThree_bounds :
    (2.7182818283 : ℝ) * (1698 / 1000) < exp (153 / 100) ∧
      exp (153 / 100) < (2.7182818286 : ℝ) * (1699 / 1000) := by
  have hid : exp (153 / 100) = exp 1 * exp (53 / 100) := by
    rw [show (153 / 100 : ℝ) = 1 + 53 / 100 by norm_num, exp_add]
  constructor
  · rw [hid]
    nlinarith [exp_one_gt_d9, exp_fiftyThree_hundredths_bounds.1, exp_pos 1,
      exp_pos (53 / 100)]
  · rw [hid]
    nlinarith [exp_one_lt_d9, exp_fiftyThree_hundredths_bounds.2, exp_pos 1]

private lemma exp_oneFiveSeven_bounds :
    (2.7182818283 : ℝ) * (1768 / 1000) < exp (157 / 100) ∧
      exp (157 / 100) < (2.7182818286 : ℝ) * (1769 / 1000) := by
  have hid : exp (157 / 100) = exp 1 * exp (57 / 100) := by
    rw [show (157 / 100 : ℝ) = 1 + 57 / 100 by norm_num, exp_add]
  constructor
  · rw [hid]
    nlinarith [exp_one_gt_d9, exp_fiftySeven_hundredths_bounds.1, exp_pos 1,
      exp_pos (57 / 100)]
  · rw [hid]
    nlinarith [exp_one_lt_d9, exp_fiftySeven_hundredths_bounds.2, exp_pos 1]

private lemma exp_twoOneSixThree_bounds :
    (2.7182818283 : ℝ) ^ 2 * (1177 / 1000) < exp (2163 / 1000) ∧
      exp (2163 / 1000) < (2.7182818286 : ℝ) ^ 2 * (1178 / 1000) := by
  have hid : exp (2163 / 1000) = exp 1 ^ 2 * exp (163 / 1000) := by
    have : (2163 / 1000 : ℝ) = 1 + 1 + 163 / 1000 := by norm_num
    rw [this, exp_add, exp_add]
    ring
  constructor
  · rw [hid]
    nlinarith [exp_one_gt_d9, exp_oneSixThree_thousandths_bounds.1, exp_pos 1,
      exp_pos (163 / 1000)]
  · rw [hid]
    nlinarith [exp_one_lt_d9, exp_oneSixThree_thousandths_bounds.2, exp_pos 1]

private lemma exp_twoTwoTwoOne_bounds :
    (2.7182818283 : ℝ) ^ 2 * (1247 / 1000) < exp (2221 / 1000) ∧
      exp (2221 / 1000) < (2.7182818286 : ℝ) ^ 2 * (1248 / 1000) := by
  have hid : exp (2221 / 1000) = exp 1 ^ 2 * exp (221 / 1000) := by
    have : (2221 / 1000 : ℝ) = 1 + 1 + 221 / 1000 := by norm_num
    rw [this, exp_add, exp_add]
    ring
  constructor
  · rw [hid]
    nlinarith [exp_one_gt_d9, exp_twoTwoOne_thousandths_bounds.1, exp_pos 1,
      exp_pos (221 / 1000)]
  · rw [hid]
    nlinarith [exp_one_lt_d9, exp_twoTwoOne_thousandths_bounds.2, exp_pos 1]

private lemma proxy_lt_side_low : (2163 / 1000 : ℝ) < sqrt 2 * (153 / 100) := by
  have h := sqrt_two_bounds.1
  have hrat : (2163 / 1000 : ℝ) < (140 / 99) * (153 / 100) := by norm_num
  nlinarith

private lemma side_high_lt_proxy : sqrt 2 * (157 / 100) < (2221 / 1000 : ℝ) := by
  have h := sqrt_two_bounds.2
  have hrat : (99 / 70) * (157 / 100) < (2221 / 1000 : ℝ) := by norm_num
  nlinarith

private lemma gamma_oneFiveThree_lower :
    gammaLower ((2.7182818286 : ℝ) * (1699 / 1000))
      (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) -
        cosHi (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100))
      (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) +
        cosLo (3.141593 / 2 - 153 / 100)) ≤ gammaSEqual (153 / 100) := by
  have hD : sinHi (3.141593 / 2 - 153 / 100) - cosLo (3.141593 / 2 - 153 / 100) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) +
      cosLo (3.141593 / 2 - 153 / 100) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before (x := 153 / 100) (ε := π / 2 - 153 / 100)
    (a := 3.141592 / 2 - 153 / 100) (b := 3.141593 / 2 - 153 / 100)
    (E0 := (2.7182818283 : ℝ) * (1698 / 1000))
    (E1 := (2.7182818286 : ℝ) * (1699 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by positivity) exp_oneFiveThree_bounds.1.le exp_oneFiveThree_bounds.2.le hD hS).1

private lemma gamma_twoOneSixThree_upper :
    gammaSEqual (2163 / 1000) ≤
      gammaCosUpper ((2.7182818283 : ℝ) ^ 2 * (1177 / 1000))
        ((2.7182818286 : ℝ) ^ 2 * (1178 / 1000))
        (-sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2)) := by
  have hD : -(sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
      cosLo (2163 / 1000 - 3.141592 / 2)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (2163 / 1000 - 3.141592 / 2) +
      cosLo (2163 / 1000 - 3.141592 / 2) := by
    simp only [sinHi, cosLo]; norm_num
  exact (gamma_after (x := 2163 / 1000) (ε := 2163 / 1000 - π / 2)
    (a := 2163 / 1000 - 3.141593 / 2) (b := 2163 / 1000 - 3.141592 / 2)
    (E0 := (2.7182818283 : ℝ) ^ 2 * (1177 / 1000))
    (E1 := (2.7182818286 : ℝ) ^ 2 * (1178 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by positivity) exp_twoOneSixThree_bounds.1.le exp_twoOneSixThree_bounds.2.le hD hS).2

private lemma gamma_oneFiveSeven_upper :
    gammaSEqual (157 / 100) ≤
      gammaCosUpperPos ((2.7182818286 : ℝ) * (1769 / 1000))
        ((2.7182818283 : ℝ) * (1768 / 1000))
        (sinHi (3.141593 / 2 - 157 / 100)) := by
  have hD : sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) +
      cosLo (3.141593 / 2 - 157 / 100) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before (x := 157 / 100) (ε := π / 2 - 157 / 100)
    (a := 3.141592 / 2 - 157 / 100) (b := 3.141593 / 2 - 157 / 100)
    (E0 := (2.7182818283 : ℝ) * (1768 / 1000))
    (E1 := (2.7182818286 : ℝ) * (1769 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by positivity) exp_oneFiveSeven_bounds.1.le exp_oneFiveSeven_bounds.2.le hD hS).2

lemma gamma_oneFiveSeven_lower :
    gammaLower ((2.7182818286 : ℝ) * (1769 / 1000))
      (sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) -
        cosHi (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100))
      (sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) +
        cosLo (3.141593 / 2 - 157 / 100)) ≤ gammaSEqual (157 / 100) := by
  have hD : sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) +
      cosLo (3.141593 / 2 - 157 / 100) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before (x := 157 / 100) (ε := π / 2 - 157 / 100)
    (a := 3.141592 / 2 - 157 / 100) (b := 3.141593 / 2 - 157 / 100)
    (E0 := (2.7182818283 : ℝ) * (1768 / 1000))
    (E1 := (2.7182818286 : ℝ) * (1769 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by positivity) exp_oneFiveSeven_bounds.1.le exp_oneFiveSeven_bounds.2.le hD hS).1

private lemma gamma_twoTwoTwoOne_lower :
    gammaLower ((2.7182818286 : ℝ) ^ 2 * (1248 / 1000))
      (-(sinHi (2221 / 1000 - 3.141592 / 2) +
        cosHi (2221 / 1000 - 3.141593 / 2) (2221 / 1000 - 3.141592 / 2)))
      (-sinHi (2221 / 1000 - 3.141592 / 2) + cosLo (2221 / 1000 - 3.141592 / 2)) ≤
      gammaSEqual (2221 / 1000) := by
  have hD : -(sinLo (2221 / 1000 - 3.141593 / 2) (2221 / 1000 - 3.141592 / 2) +
      cosLo (2221 / 1000 - 3.141592 / 2)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (2221 / 1000 - 3.141592 / 2) +
      cosLo (2221 / 1000 - 3.141592 / 2) := by
    simp only [sinHi, cosLo]; norm_num
  exact (gamma_after (x := 2221 / 1000) (ε := 2221 / 1000 - π / 2)
    (a := 2221 / 1000 - 3.141593 / 2) (b := 2221 / 1000 - 3.141592 / 2)
    (E0 := (2.7182818283 : ℝ) ^ 2 * (1247 / 1000))
    (E1 := (2.7182818286 : ℝ) ^ 2 * (1248 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by positivity) exp_twoTwoTwoOne_bounds.1.le exp_twoTwoTwoOne_bounds.2.le hD hS).1

theorem squareBalance_oneFiveThree_neg : squareBalance (153 / 100) < 0 :=
  squareBalance_neg_of_outer
    ⟨by norm_num, by
      rw [resonanceRoot1_eq_pi_div_two]
      linarith [pi_gt_d6]⟩

private lemma gamma_twoOneSixThree_upper_legacy :
    gammaSEqualLegacy (2163 / 1000) ≤
      gammaUpper ((2.7182818283 : ℝ) ^ 2 * (1177 / 1000))
        (-(sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
          cosLo (2163 / 1000 - 3.141592 / 2)))
        (-sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
          cosHi (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2)) := by
  have hD : -(sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
      cosLo (2163 / 1000 - 3.141592 / 2)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (2163 / 1000 - 3.141592 / 2) +
      cosLo (2163 / 1000 - 3.141592 / 2) := by
    simp only [sinHi, cosLo]; norm_num
  exact (gamma_after_legacy (x := 2163 / 1000) (ε := 2163 / 1000 - π / 2)
    (a := 2163 / 1000 - 3.141593 / 2) (b := 2163 / 1000 - 3.141592 / 2)
    (E0 := (2.7182818283 : ℝ) ^ 2 * (1177 / 1000))
    (E1 := (2.7182818286 : ℝ) ^ 2 * (1178 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by positivity) exp_twoOneSixThree_bounds.1.le exp_twoOneSixThree_bounds.2.le hD hS).2

private lemma gamma_oneFiveThree_lower_legacy :
    gammaLower ((2.7182818286 : ℝ) * (1699 / 1000))
      (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) -
        cosHi (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100))
      (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) +
        cosLo (3.141593 / 2 - 153 / 100)) ≤ gammaSEqualLegacy (153 / 100) := by
  have hD : sinHi (3.141593 / 2 - 153 / 100) - cosLo (3.141593 / 2 - 153 / 100) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) +
      cosLo (3.141593 / 2 - 153 / 100) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before_legacy (x := 153 / 100) (ε := π / 2 - 153 / 100)
    (a := 3.141592 / 2 - 153 / 100) (b := 3.141593 / 2 - 153 / 100)
    (E0 := (2.7182818283 : ℝ) * (1698 / 1000))
    (E1 := (2.7182818286 : ℝ) * (1699 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by positivity) exp_oneFiveThree_bounds.1.le exp_oneFiveThree_bounds.2.le hD hS).1

private lemma gamma_oneFiveThree_upper_legacy :
    gammaSEqualLegacy (153 / 100) ≤
      gammaUpper ((2.7182818283 : ℝ) * (1698 / 1000))
        (sinHi (3.141593 / 2 - 153 / 100) - cosLo (3.141593 / 2 - 153 / 100))
        (sinHi (3.141593 / 2 - 153 / 100) +
          cosHi (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100)) := by
  have hD : sinHi (3.141593 / 2 - 153 / 100) - cosLo (3.141593 / 2 - 153 / 100) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) +
      cosLo (3.141593 / 2 - 153 / 100) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before_legacy (x := 153 / 100) (ε := π / 2 - 153 / 100)
    (a := 3.141592 / 2 - 153 / 100) (b := 3.141593 / 2 - 153 / 100)
    (E0 := (2.7182818283 : ℝ) * (1698 / 1000))
    (E1 := (2.7182818286 : ℝ) * (1699 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by positivity) exp_oneFiveThree_bounds.1.le exp_oneFiveThree_bounds.2.le hD hS).2

private lemma gamma_oneFiveSeven_upper_legacy :
    gammaSEqualLegacy (157 / 100) ≤
      gammaUpper ((2.7182818283 : ℝ) * (1768 / 1000))
        (sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100))
        (sinHi (3.141593 / 2 - 157 / 100) +
          cosHi (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100)) := by
  have hD : sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) +
      cosLo (3.141593 / 2 - 157 / 100) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before_legacy (x := 157 / 100) (ε := π / 2 - 157 / 100)
    (a := 3.141592 / 2 - 157 / 100) (b := 3.141593 / 2 - 157 / 100)
    (E0 := (2.7182818283 : ℝ) * (1768 / 1000))
    (E1 := (2.7182818286 : ℝ) * (1769 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by positivity) exp_oneFiveSeven_bounds.1.le exp_oneFiveSeven_bounds.2.le hD hS).2

private lemma gamma_twoTwoTwoOne_lower_legacy :
    gammaLower ((2.7182818286 : ℝ) ^ 2 * (1248 / 1000))
      (-(sinHi (2221 / 1000 - 3.141592 / 2) +
        cosHi (2221 / 1000 - 3.141593 / 2) (2221 / 1000 - 3.141592 / 2)))
      (-sinHi (2221 / 1000 - 3.141592 / 2) + cosLo (2221 / 1000 - 3.141592 / 2)) ≤
      gammaSEqualLegacy (2221 / 1000) := by
  have hD : -(sinLo (2221 / 1000 - 3.141593 / 2) (2221 / 1000 - 3.141592 / 2) +
      cosLo (2221 / 1000 - 3.141592 / 2)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (2221 / 1000 - 3.141592 / 2) +
      cosLo (2221 / 1000 - 3.141592 / 2) := by
    simp only [sinHi, cosLo]; norm_num
  exact (gamma_after_legacy (x := 2221 / 1000) (ε := 2221 / 1000 - π / 2)
    (a := 2221 / 1000 - 3.141593 / 2) (b := 2221 / 1000 - 3.141592 / 2)
    (E0 := (2.7182818283 : ℝ) ^ 2 * (1247 / 1000))
    (E1 := (2.7182818286 : ℝ) ^ 2 * (1248 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by positivity) exp_twoTwoTwoOne_bounds.1.le exp_twoTwoTwoOne_bounds.2.le hD hS).1

theorem squareBalanceLegacy_oneFiveThree_neg : squareBalanceLegacy (153 / 100) < 0 := by
  have hy := proxy_lt_side_low
  have hyπ : sqrt 2 * (153 / 100) < π := by
    have : sqrt 2 * (153 / 100) < 3 := by
      have h := sqrt_two_bounds.2
      nlinarith
    linarith [pi_gt_three]
  have h70π : (2163 / 1000 : ℝ) < π := by linarith [pi_gt_three]
  have hdec : gammaSEqualLegacy (sqrt 2 * (153 / 100)) < gammaSEqualLegacy (2163 / 1000) :=
    (legacy_strictAntiOn_gammaSEqual_even 0) (mem_gamma_Icc (by norm_num) h70π.le)
      (mem_gamma_Icc (by positivity) hyπ.le) hy
  have hlo := gamma_oneFiveThree_lower_legacy
  have hhi := gamma_twoOneSixThree_upper_legacy
  have hcmp :
      gammaUpper ((2.7182818283 : ℝ) ^ 2 * (1177 / 1000))
        (-(sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
          cosLo (2163 / 1000 - 3.141592 / 2)))
        (-sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
          cosHi (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2)) <
      (99 / 35) * gammaLower ((2.7182818286 : ℝ) * (1699 / 1000))
        (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) -
          cosHi (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100))
        (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) +
          cosLo (3.141593 / 2 - 153 / 100)) := by
    simp only [gammaUpper, gammaLower, sinLo, cosLo, cosHi]
    norm_num
  have hγneg : gammaSEqualLegacy (153 / 100) < 0 := by
    have hnegU : gammaUpper ((2.7182818283 : ℝ) * (1698 / 1000))
        (sinHi (3.141593 / 2 - 153 / 100) - cosLo (3.141593 / 2 - 153 / 100))
        (sinHi (3.141593 / 2 - 153 / 100) +
          cosHi (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100)) < 0 := by
      simp only [gammaUpper, sinHi, cosLo, cosHi]; norm_num
    linarith [gamma_oneFiveThree_upper_legacy]
  have hA : 2 * sqrt 2 < 99 / 35 := two_sqrt_two_bounds.2
  have hP : (99 / 35) * gammaSEqualLegacy (153 / 100) < 2 * sqrt 2 * gammaSEqualLegacy (153 / 100) := by
    nlinarith
  unfold squareBalanceLegacy
  linarith

private theorem squareBalanceLegacy_oneFiveSeven_pos : 0 < squareBalanceLegacy (157 / 100) := by
  have hy := side_high_lt_proxy
  have hy0 : 0 < sqrt 2 * (157 / 100) := by positivity
  have hyπ : sqrt 2 * (157 / 100) < π := by
    have : sqrt 2 * (157 / 100) < 3 := by
      have h := sqrt_two_bounds.2
      nlinarith
    linarith [pi_gt_three]
  have hUπ : (2221 / 1000 : ℝ) < π := by linarith [pi_gt_three]
  have hdec : gammaSEqualLegacy (2221 / 1000) < gammaSEqualLegacy (sqrt 2 * (157 / 100)) :=
    (legacy_strictAntiOn_gammaSEqual_even 0) (mem_gamma_Icc hy0.le hyπ.le)
      (mem_gamma_Icc (by norm_num) hUπ.le) hy
  have hhi := gamma_oneFiveSeven_upper_legacy
  have hlo := gamma_twoTwoTwoOne_lower_legacy
  have hγneg : gammaSEqualLegacy (157 / 100) < 0 := by
    have hnegU : gammaUpper ((2.7182818283 : ℝ) * (1768 / 1000))
        (sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100))
        (sinHi (3.141593 / 2 - 157 / 100) +
          cosHi (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100)) < 0 := by
      simp only [gammaUpper, sinHi, cosLo, cosHi]; norm_num
    linarith [hhi]
  have hcmp : (280 / 99) * gammaUpper ((2.7182818283 : ℝ) * (1768 / 1000))
      (sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100))
      (sinHi (3.141593 / 2 - 157 / 100) +
        cosHi (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100)) <
      gammaLower ((2.7182818286 : ℝ) ^ 2 * (1248 / 1000))
        (-(sinHi (2221 / 1000 - 3.141592 / 2) +
          cosHi (2221 / 1000 - 3.141593 / 2) (2221 / 1000 - 3.141592 / 2)))
        (-sinHi (2221 / 1000 - 3.141592 / 2) +
          cosLo (2221 / 1000 - 3.141592 / 2)) := by
    simp only [gammaUpper, gammaLower, sinHi, cosLo, cosHi]
    norm_num
  have hA : 280 / 99 < 2 * sqrt 2 := two_sqrt_two_bounds.1
  have hP : 2 * sqrt 2 * gammaSEqualLegacy (157 / 100) < (280 / 99) * gammaSEqualLegacy (157 / 100) := by
    nlinarith
  unfold squareBalanceLegacy
  linarith

/-- Certified positive legacy balance at the upper end of the `(153/100, 157/100)` window. -/
theorem squareBalance_oneFiveSeven_pos : 0 < squareBalanceLegacy (157 / 100) :=
  squareBalanceLegacy_oneFiveSeven_pos

/-- Legacy balance crossing on the Numbers proxy window (not the primary late shell). -/
theorem exists_square_shell_legacy_numbers_window :
    ∃ x : ℝ, x ∈ Set.Ioo (153 / 100) (157 / 100) ∧ squareBalanceLegacy x = 0 := by
  obtain ⟨x, hxI, hx0⟩ :=
    intermediate_value_Ioo (by norm_num)
      continuous_squareBalanceLegacy.continuousOn
      ⟨squareBalanceLegacy_oneFiveThree_neg, squareBalanceLegacy_oneFiveSeven_pos⟩
  exact ⟨x, ⟨hxI.1, hxI.2⟩, hx0⟩

theorem exists_unique_square_shell :
    ∃! x : ℝ, x ∈ Set.Ioo (3 / 2) (33 / 20) ∧ squareBalanceLegacy x = 0 := by
  have hsub := intermediate_value_Ioo (by norm_num : (3 / 2 : ℝ) ≤ 8 / 5)
    continuous_squareBalanceLegacy.continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (squareBalanceLegacy (3 / 2)) (squareBalanceLegacy (8 / 5)) :=
    ⟨squareBalance_three_halves_neg, squareBalanceLegacy_eight_fifths_pos⟩
  obtain ⟨x, hxI, hx0⟩ := hsub h0
  have hxshell : x ∈ Set.Ioo (3 / 2) (33 / 20) :=
    ⟨hxI.1, lt_trans hxI.2 (by norm_num : (8 / 5 : ℝ) < 33 / 20)⟩
  refine ⟨x, ⟨hxshell, hx0⟩, ?_⟩
  intro y hy
  exact (squareBalance_strictMonoOn_shell.injOn hxshell hy.1 (by rw [hx0, hy.2])).symm

/-! ### The square restores its diagonal -/

private lemma gammaSEqualLegacy_neg_right_of_node {x : ℝ} (hx : x ∈ Ioo resonanceRoot1 π) :
    gammaSEqualLegacy x < 0 := by
  obtain ⟨hx1, hπ⟩ := hx
  have hres : gammaSEqualLegacy resonanceRoot1 < 0 := by
    rw [resonanceRoot1_eq_pi_div_two, gammaSEqualLegacy_exp, cos_pi_div_two, sin_pi_div_two]
    have hexp : exp (-(π / 2)) < exp (π / 2) := exp_lt_exp.mpr (by linarith [pi_pos])
    nlinarith [exp_pos (π / 2), hexp]
  have hresIcc := @mem_gamma_Icc resonanceRoot1
      (le_of_lt (lt_trans (by nlinarith [pi_pos]) resonanceRoot1_bounds.1))
      (le_of_lt resonanceRoot1_sharp_bounds.2)
  have h0x : 0 < x := lt_trans (by nlinarith [resonanceRoot1_sharp_bounds.1, pi_pos]) hx1
  have hxIcc := @mem_gamma_Icc x (le_of_lt h0x) hπ.le
  exact (legacy_strictAntiOn_gammaSEqual_even 0 hresIcc hxIcc hx1).trans_le (le_of_lt hres)

lemma squareBracket_legacy_gamma_neg {x : ℝ} (hx : x ∈ Set.Ico (8 / 5 : ℝ) (33 / 20)) :
    gammaSEqualLegacy x < 0 ∧ gammaSEqualLegacy (sqrt 2 * x) < 0 := by
  have hx1 : resonanceRoot1 < x := eight_fifths_gt_resonanceRoot1.trans_le hx.1
  have hxπ : x < π := lt_trans hx.2 (by nlinarith [pi_gt_three])
  have hside_lo : resonanceRoot1 < sqrt 2 * x := by
    have h8 : resonanceRoot1 < sqrt 2 * (8 / 5) := by
      nlinarith [eight_fifths_gt_resonanceRoot1, sqrt_two_bounds.1, sqrt_two_bounds.2]
    have hmul : sqrt 2 * (8 / 5) ≤ sqrt 2 * x :=
      mul_le_mul_of_nonneg_left hx.1 (sqrt_nonneg _)
    exact lt_of_lt_of_le h8 hmul
  have hside_hi : sqrt 2 * x < π := by
    have hy : sqrt 2 * x ≤ sqrt 2 * (33 / 20) :=
      mul_le_mul_of_nonneg_left hx.2.le (sqrt_nonneg _)
    nlinarith [sqrt_two_bounds.2, pi_gt_three]
  exact ⟨gammaSEqualLegacy_neg_right_of_node ⟨hx1, hxπ⟩,
    gammaSEqualLegacy_neg_right_of_node ⟨hside_lo, hside_hi⟩⟩

lemma squareBracket_gamma_neg {x : ℝ} (hx : x ∈ Set.Ico (8 / 5 : ℝ) (33 / 20)) :
    gammaSEqual x < 0 ∧ gammaSEqual (sqrt 2 * x) < 0 := by
  have hx1 : resonanceRoot1 < x := eight_fifths_gt_resonanceRoot1.trans_le hx.1
  have hxπ : x < π := lt_trans hx.2 (by nlinarith [pi_gt_three])
  have hside_lo : resonanceRoot1 < sqrt 2 * x := by
    nlinarith [one_lt_sqrt_two, eight_fifths_gt_resonanceRoot1, hx.1]
  have hside_hi : sqrt 2 * x < π := by
    have hy : sqrt 2 * x ≤ sqrt 2 * (33 / 20) := mul_le_mul_of_nonneg_left hx.2.le (sqrt_nonneg _)
    nlinarith [sqrt_two_bounds.2, pi_gt_three]
  exact ⟨gammaSEqual_neg_right_of_first_node ⟨hx1, hxπ⟩,
    gammaSEqual_neg_right_of_first_node ⟨hside_lo, hside_hi⟩⟩

lemma squareBracket_mem_shell {x : ℝ} (hx : x ∈ Set.Ico (8 / 5 : ℝ) (33 / 20)) :
    x ∈ Set.Ioo (3 / 2) (33 / 20) :=
  ⟨by nlinarith [hx.1], hx.2⟩

/-- Common square factor \(1/\gamma(x)-2\sqrt{2}/\gamma(\sqrt{2}\,x)\). -/
noncomputable def squareForce (x : ℝ) : ℝ :=
  1 / gammaSEqual x - 2 * sqrt 2 / gammaSEqual (sqrt 2 * x)

noncomputable def squareForceLegacy (x : ℝ) : ℝ :=
  1 / gammaSEqualLegacy x - 2 * sqrt 2 / gammaSEqualLegacy (sqrt 2 * x)

theorem squareForceLegacy_eq_balance {x : ℝ}
    (h1 : gammaSEqualLegacy x ≠ 0) (h2 : gammaSEqualLegacy (sqrt 2 * x) ≠ 0) :
    squareForceLegacy x =
      squareBalanceLegacy x / (gammaSEqualLegacy x * gammaSEqualLegacy (sqrt 2 * x)) := by
  unfold squareForceLegacy squareBalanceLegacy
  field_simp [h1, h2]

theorem squareForce_eq_balance {x : ℝ}
    (h1 : gammaSEqual x ≠ 0) (h2 : gammaSEqual (sqrt 2 * x) ≠ 0) :
    squareForce x =
      squareBalance x / (gammaSEqual x * gammaSEqual (sqrt 2 * x)) := by
  unfold squareForce squareBalance
  field_simp [h1, h2]

/-- Legacy balance and legacy force share sign on the certified shell bracket. -/
theorem squareBalance_sign {x : ℝ} (hx : x ∈ Set.Ico (8 / 5 : ℝ) (33 / 20)) :
    (squareForceLegacy x < 0 ↔ squareBalanceLegacy x < 0) ∧
      (0 < squareForceLegacy x ↔ 0 < squareBalanceLegacy x) := by
  have hγ := squareBracket_legacy_gamma_neg hx
  have hden : 0 < gammaSEqualLegacy x * gammaSEqualLegacy (sqrt 2 * x) :=
    mul_pos_of_neg_of_neg hγ.1 hγ.2
  have heq := squareForceLegacy_eq_balance hγ.1.ne hγ.2.ne
  refine ⟨?_, ?_⟩
  · rw [heq, div_lt_iff₀ hden, zero_mul]
  · rw [heq, lt_div_iff₀ hden, zero_mul]

theorem squareForce_sign {x : ℝ} (hx : x ∈ Set.Ico (8 / 5 : ℝ) (33 / 20)) :
    (squareForce x < 0 ↔ squareBalance x < 0) ∧
      (0 < squareForce x ↔ 0 < squareBalance x) := by
  have hγ := squareBracket_gamma_neg hx
  have hden : 0 < gammaSEqual x * gammaSEqual (sqrt 2 * x) :=
    mul_pos_of_neg_of_neg hγ.1 hγ.2
  have heq := squareForce_eq_balance hγ.1.ne hγ.2.ne
  refine ⟨?_, ?_⟩
  · rw [heq, div_lt_iff₀ hden, zero_mul]
  · rw [heq, lt_div_iff₀ hden, zero_mul]

theorem covalentAxial_eq_squareForce {ℓ R : ℝ} (hR : 0 < R) :
    covalentAxial ℓ R (R / 2) = (1 / R ^ 2) * squareForce (ℓ / (2 * R)) := by
  rw [covalentAxial_square hR]
  rfl

theorem square_diagonal_restores {ℓ R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hx : ℓ / (2 * R) ∈ Set.Ioo (8 / 5 : ℝ) (33 / 20))
    (hy : ℓ / (2 * S) ∈ Set.Ioo (8 / 5 : ℝ) (33 / 20))
    (h0 : squareBalanceLegacy (ℓ / (2 * R)) = 0) :
    ((1 / S ^ 2) * squareForceLegacy (ℓ / (2 * S)) < 0 ↔ R < S) ∧
      (0 < (1 / S ^ 2) * squareForceLegacy (ℓ / (2 * S)) ↔ S < R) := by
  set x : ℝ := ℓ / (2 * R)
  set y : ℝ := ℓ / (2 * S)
  have hxI : x ∈ Set.Ico (8 / 5 : ℝ) (33 / 20) := ⟨hx.1.le, hx.2⟩
  have hyI : y ∈ Set.Ico (8 / 5 : ℝ) (33 / 20) := ⟨hy.1.le, hy.2⟩
  have hxsh := squareBracket_mem_shell hxI
  have hysh := squareBracket_mem_shell hyI
  have hmono := squareBalance_strictMonoOn_shell
  have hord : squareBalanceLegacy y < 0 ↔ y < x := by
    have h := hmono.lt_iff_lt hysh hxsh
    rwa [h0] at h
  have hord' : 0 < squareBalanceLegacy y ↔ x < y := by
    have h := hmono.lt_iff_lt hxsh hysh
    rwa [h0] at h
  have hsign := squareBalance_sign hyI
  have hscale : 0 < 1 / S ^ 2 := by positivity
  have hydef : ℓ / (2 * S) = y := rfl
  have hforce_neg : (1 / S ^ 2) * squareForceLegacy y < 0 ↔ squareForceLegacy y < 0 := by
    simpa [hydef] using mul_lt_mul_iff_of_pos_left (b := squareForceLegacy y) (c := (0 : ℝ)) hscale
  have hforce_pos : 0 < (1 / S ^ 2) * squareForceLegacy y ↔ 0 < squareForceLegacy y := by
    simpa [hydef] using mul_lt_mul_iff_of_pos_left (b := (0 : ℝ)) (c := squareForceLegacy y) hscale
  have hℓpos : 0 < ℓ := by
    have hx0 : 0 < ℓ / (2 * R) := lt_trans (by norm_num) hx.1
    have hden : 0 < 2 * R := by positivity
    have : 0 < ℓ / (2 * R) * (2 * R) := mul_pos hx0 hden
    simpa [div_mul_cancel₀ ℓ hden.ne'] using this
  have hphase : y < x ↔ R < S := by
    dsimp [x, y]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [mul_lt_mul_iff_of_pos_left hℓpos, mul_lt_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]
  have hphase' : x < y ↔ S < R := by
    dsimp [x, y]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [mul_lt_mul_iff_of_pos_left hℓpos, mul_lt_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]
  refine ⟨?_, ?_⟩
  · rw [hforce_neg, hsign.1, hord, hphase]
  · rw [hforce_pos, hsign.2, hord', hphase']

/-! ### One weight on the three separations -/

private lemma midplane_phase_balance {ℓ R ρ : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hρ : 0 < ρ) :
    let rEp := sqrt ((R / 2) ^ 2 + ρ ^ 2)
    4 / (ℓ / (2 * rEp)) ^ 2 =
      1 / (ℓ / (2 * R)) ^ 2 + 1 / (ℓ / (2 * (2 * ρ))) ^ 2 := by
  intro rEp
  have hrEp : 0 < rEp := by
    dsimp [rEp]
    positivity
  have hr2 : rEp ^ 2 = R ^ 2 / 4 + ρ ^ 2 := by
    dsimp [rEp]
    rw [sq_sqrt (by positivity)]
    ring
  have hsum : 1 / (ℓ / (2 * R)) ^ 2 + 1 / (ℓ / (2 * (2 * ρ))) ^ 2 =
      4 * (R ^ 2 + 4 * ρ ^ 2) / ℓ ^ 2 := by
    field_simp [hℓ.ne', hR.ne', hρ.ne']
    ring
  have hEp : 4 / (ℓ / (2 * rEp)) ^ 2 = 4 * (R ^ 2 + 4 * ρ ^ 2) / ℓ ^ 2 := by
    field_simp [hℓ.ne', hrEp.ne']
    nlinarith [hr2]
  linarith

private lemma weight_to_phase {ℓ r s : ℝ} (hℓ : 0 < ℓ) (_hr : 0 < r) (_hs : 0 < s)
    (h : gammaSEqual (ℓ / (2 * r)) * r ^ 3 = gammaSEqual (ℓ / (2 * s)) * s ^ 3) :
    gammaSEqual (ℓ / (2 * r)) / (ℓ / (2 * r)) ^ 3 =
      gammaSEqual (ℓ / (2 * s)) / (ℓ / (2 * s)) ^ 3 := by
  field_simp [hℓ.ne'] at h ⊢
  exact h

private lemma gamma_quot_strictAnti {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) resonanceRoot1) (hb : b ∈ Ioo (0 : ℝ) resonanceRoot1)
    (hab : a < b) :
    gammaSEqual b / b ^ 3 < gammaSEqual a / a ^ 3 := by
  have hγa : 0 < gammaSEqual a := gammaSEqual_pos_left_of_first_node ha
  have hγlt : gammaSEqual b < gammaSEqual a :=
    (strictAntiOn_gammaSEqual_even 0) (evenInterval_of_lt_firstNode ha)
      (evenInterval_of_lt_firstNode hb) hab
  have hpow : a ^ 3 < b ^ 3 := pow_lt_pow_left₀ hab ha.1.le (by decide : 3 ≠ 0)
  have ha3 : 0 < a ^ 3 := pow_pos ha.1 3
  have hb3 : 0 < b ^ 3 := pow_pos hb.1 3
  have h1 : gammaSEqual b / b ^ 3 < gammaSEqual a / b ^ 3 := by
    rw [div_lt_div_iff_of_pos_right hb3]
    exact hγlt
  have h2 : gammaSEqual a / b ^ 3 < gammaSEqual a / a ^ 3 := by
    rw [div_lt_div_iff_of_pos_left hγa hb3 ha3]
    exact hpow
  exact lt_trans h1 h2

private lemma gamma_quot_inj {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) resonanceRoot1) (hb : b ∈ Ioo (0 : ℝ) resonanceRoot1)
    (h : gammaSEqual a / a ^ 3 = gammaSEqual b / b ^ 3) :
    a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (ne_of_gt (gamma_quot_strictAnti ha hb hlt))
  · exact heq
  · exact absurd h (ne_of_lt (gamma_quot_strictAnti hb ha hgt))

theorem covalent_forces_iff_weights {ℓ R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hγR : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγee : gammaSEqual (ℓ / (2 * (2 * ρ))) ≠ 0)
    (hγep : gammaSEqual (ℓ / (2 * sqrt ((R / 2) ^ 2 + ρ ^ 2))) ≠ 0) :
    covalentAxial ℓ R ρ = 0 ∧ covalentRadial ℓ R ρ = 0 ↔
      gammaSEqual (ℓ / (2 * R)) * R ^ 3 =
          gammaSEqual (ℓ / (2 * sqrt ((R / 2) ^ 2 + ρ ^ 2))) *
            (sqrt ((R / 2) ^ 2 + ρ ^ 2)) ^ 3 ∧
        gammaSEqual (ℓ / (2 * sqrt ((R / 2) ^ 2 + ρ ^ 2))) *
            (sqrt ((R / 2) ^ 2 + ρ ^ 2)) ^ 3 =
          gammaSEqual (ℓ / (2 * (2 * ρ))) * (2 * ρ) ^ 3 := by
  constructor
  · rintro ⟨hFz, hFr⟩
    unfold covalentAxial at hFz
    unfold covalentRadial at hFr
    dsimp only at hFz hFr
    set rEp : ℝ := sqrt ((R / 2) ^ 2 + ρ ^ 2)
    set γR : ℝ := gammaSEqual (ℓ / (2 * R))
    set γee : ℝ := gammaSEqual (ℓ / (2 * (2 * ρ)))
    set γep : ℝ := gammaSEqual (ℓ / (2 * rEp))
    have hrEp : 0 < rEp := by
      dsimp [rEp]
      positivity
    have hγep' : γep ≠ 0 := by
      simpa [γep, rEp] using hγep
    have hFz' : 1 / (γR * R ^ 2) = R / (γep * rEp ^ 3) := by linarith
    have hR3 : γep * rEp ^ 3 = γR * R ^ 3 := by
      have hmul := congrArg (fun t => t * ((γR * R ^ 2) * (γep * rEp ^ 3))) hFz'
      field_simp [hγR, hR.ne', hγep', hrEp.ne'] at hmul
      linarith
    have hFr' : 1 / (γee * (2 * ρ) ^ 2) = 2 * ρ / (γep * rEp ^ 3) := by linarith
    have hEe : γep * rEp ^ 3 = γee * (2 * ρ) ^ 3 := by
      have hmul := congrArg (fun t => t * ((γee * (2 * ρ) ^ 2) * (γep * rEp ^ 3))) hFr'
      field_simp [hγee, hρ.ne', hγep', hrEp.ne'] at hmul
      linarith
    exact ⟨by simpa [γR, γep, rEp] using hR3.symm, by simpa [γep, γee, rEp] using hEe⟩
  · rintro ⟨hAx, hRad⟩
    unfold covalentAxial covalentRadial
    dsimp only
    set rEp : ℝ := sqrt ((R / 2) ^ 2 + ρ ^ 2)
    set γR : ℝ := gammaSEqual (ℓ / (2 * R))
    set γee : ℝ := gammaSEqual (ℓ / (2 * (2 * ρ)))
    set γep : ℝ := gammaSEqual (ℓ / (2 * rEp))
    have hrEp : 0 < rEp := by
      dsimp [rEp]
      positivity
    have hγep' : γep ≠ 0 := by
      simpa [γep, rEp] using hγep
    have hAx' : γR * R ^ 3 = γep * rEp ^ 3 := by
      simpa [γR, γep, rEp] using hAx
    have hRad' : γep * rEp ^ 3 = γee * (2 * ρ) ^ 3 := by
      simpa [γep, γee, rEp] using hRad
    refine ⟨?_, ?_⟩
    · have hden : (γR * R ^ 2) * (γep * rEp ^ 3) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hγR (pow_ne_zero 2 hR.ne'))
          (mul_ne_zero hγep' (pow_ne_zero 3 hrEp.ne'))
      have hmul : 1 / (γR * R ^ 2) * ((γR * R ^ 2) * (γep * rEp ^ 3)) =
          R / (γep * rEp ^ 3) * ((γR * R ^ 2) * (γep * rEp ^ 3)) := by
        field_simp [hγR, hR.ne', hγep', hrEp.ne']
        linarith
      have hterms := mul_right_cancel₀ hden hmul
      linarith
    · have hden : (γee * (2 * ρ) ^ 2) * (γep * rEp ^ 3) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hγee (pow_ne_zero 2 (mul_ne_zero (by norm_num) hρ.ne')))
          (mul_ne_zero hγep' (pow_ne_zero 3 hrEp.ne'))
      have hmul : 1 / (γee * (2 * ρ) ^ 2) * ((γee * (2 * ρ) ^ 2) * (γep * rEp ^ 3)) =
          (2 * ρ) / (γep * rEp ^ 3) * ((γee * (2 * ρ) ^ 2) * (γep * rEp ^ 3)) := by
        field_simp [hγee, hρ.ne', hγep', hrEp.ne']
        linarith
      have hterms := mul_right_cancel₀ hden hmul
      linarith

theorem no_midplane_ep_outer {ℓ R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hEp : ℓ / (2 * sqrt ((R / 2) ^ 2 + ρ ^ 2)) ∈ Ioo (0 : ℝ) resonanceRoot1) :
    ¬ (covalentAxial ℓ R ρ = 0 ∧ covalentRadial ℓ R ρ = 0) := by
  intro h
  set rEp : ℝ := sqrt ((R / 2) ^ 2 + ρ ^ 2)
  set xR : ℝ := ℓ / (2 * R)
  set xEe : ℝ := ℓ / (2 * (2 * ρ))
  set xEp : ℝ := ℓ / (2 * rEp)
  have hrEp : 0 < rEp := by
    dsimp [rEp]
    positivity
  have hxEp : xEp ∈ Ioo (0 : ℝ) resonanceRoot1 := by
    simpa [xEp, rEp] using hEp
  have hℓ : 0 < ℓ := by
    have hden : 0 < 2 * rEp := by positivity
    have hmul : 0 < xEp * (2 * rEp) := mul_pos hxEp.1 hden
    simpa [xEp, div_mul_cancel₀ ℓ hden.ne'] using hmul
  have hγep : gammaSEqual xEp ≠ 0 :=
    (gammaSEqual_pos_left_of_first_node hxEp).ne'
  have hFz := h.1
  have hFr := h.2
  have hγR : gammaSEqual xR ≠ 0 := by
    intro h0
    unfold covalentAxial at hFz
    dsimp only at hFz
    rw [show gammaSEqual (ℓ / (2 * R)) = gammaSEqual xR by rfl, h0] at hFz
    simp only [zero_mul, div_zero, zero_sub] at hFz
    have hden : gammaSEqual (ℓ / (2 * rEp)) * rEp ^ 3 ≠ 0 :=
      mul_ne_zero (by simpa [xEp, rEp] using hγep) (pow_ne_zero 3 hrEp.ne')
    have hneg : R / (gammaSEqual (ℓ / (2 * rEp)) * rEp ^ 3) ≠ 0 :=
      div_ne_zero hR.ne' hden
    exact hneg (by linarith)
  have hγee : gammaSEqual xEe ≠ 0 := by
    intro h0
    unfold covalentRadial at hFr
    dsimp only at hFr
    rw [show gammaSEqual (ℓ / (2 * (2 * ρ))) = gammaSEqual xEe by rfl, h0] at hFr
    simp only [zero_mul, div_zero, zero_sub] at hFr
    have hden : gammaSEqual (ℓ / (2 * rEp)) * rEp ^ 3 ≠ 0 :=
      mul_ne_zero (by simpa [xEp, rEp] using hγep) (pow_ne_zero 3 hrEp.ne')
    have hneg : 2 * ρ / (gammaSEqual (ℓ / (2 * rEp)) * rEp ^ 3) ≠ 0 :=
      div_ne_zero (mul_ne_zero (by norm_num) hρ.ne') hden
    exact hneg (by linarith)
  have hw := (covalent_forces_iff_weights (ℓ := ℓ) (R := R) (ρ := ρ)
    hR hρ hγR hγee (by simpa [xEp, rEp] using hγep)).mp h
  have hphase := weight_to_phase (ℓ := ℓ) (r := R) (s := rEp) hℓ hR hrEp
    (by simpa [xR, xEp, rEp] using hw.1)
  have hphaseE := weight_to_phase (ℓ := ℓ) (r := rEp) (s := 2 * ρ) hℓ hrEp
    (by positivity) (by simpa [xEp, xEe, rEp] using hw.2)
  have hgeom := midplane_phase_balance (ℓ := ℓ) (R := R) (ρ := ρ) hℓ hR hρ
  have hx1 : 0 < resonanceRoot1 :=
    lt_trans (by linarith [pi_pos] : (0 : ℝ) < π / 4) resonanceRoot1_sharp_bounds.1
  have hxRpos : 0 < xR := by
    dsimp [xR]
    positivity
  have hxEepos : 0 < xEe := by
    dsimp [xEe]
    positivity
  have hcoinc : xR ∈ Ioo (0 : ℝ) resonanceRoot1 → False := by
    intro hxRwell
    have heq : xR = xEp :=
      gamma_quot_inj hxRwell hxEp (by simpa [xR, xEp, rEp] using hphase)
    have hsq : xEe ^ 2 = xR ^ 2 / 3 := by
      have hrel : 4 / xR ^ 2 = 1 / xR ^ 2 + 1 / xEe ^ 2 := by
        simpa [xR, xEe, xEp, rEp, heq] using hgeom
      field_simp [hxRpos.ne', hxEepos.ne'] at hrel
      linarith
    have hxEe' : xEe = xR / sqrt 3 := by
      have h3 : (sqrt 3) ^ 2 = 3 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      have hsq' : xEe ^ 2 = (xR / sqrt 3) ^ 2 := by
        calc
          xEe ^ 2 = xR ^ 2 / 3 := hsq
          _ = xR ^ 2 / (sqrt 3) ^ 2 := by rw [h3]
          _ = (xR / sqrt 3) ^ 2 := by rw [← div_pow]
      exact (sq_eq_sq₀ hxEepos.le (by positivity)).mp hsq'
    have hsqrt3 : (1 : ℝ) < sqrt 3 :=
      lt_of_pow_lt_pow_left₀ 2 (sqrt_nonneg _) <| by
        rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
    have hxEewell : xEe ∈ Ioo (0 : ℝ) resonanceRoot1 := by
      refine ⟨hxEepos, ?_⟩
      rw [hxEe']
      have hlt : xR / sqrt 3 < xR := by
        rw [div_lt_iff₀ (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
        nlinarith [hsqrt3]
      exact lt_trans hlt hxRwell.2
    have hne : xEe ≠ xR := by
      rw [hxEe']
      intro heq
      have hlt : xR / sqrt 3 < xR := by
        rw [div_lt_iff₀ (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
        nlinarith [hsqrt3]
      linarith
    exact hne (gamma_quot_inj hxEewell hxRwell
      (by simpa [xEe, xR, xEp, rEp, heq] using hphaseE.symm))
  by_cases hxRwell : xR < resonanceRoot1
  · exact hcoinc ⟨hxRpos, hxRwell⟩
  · have hxRge : resonanceRoot1 ≤ xR := le_of_not_gt hxRwell
    by_cases hxEewell : xEe < resonanceRoot1
    · have heq : xEe = xEp :=
        gamma_quot_inj ⟨hxEepos, hxEewell⟩ hxEp
          (by simpa [xEe, xEp, rEp] using hphaseE.symm)
      have hsq : xR ^ 2 = xEe ^ 2 / 3 := by
        have hrel : 4 / xEe ^ 2 = 1 / xR ^ 2 + 1 / xEe ^ 2 := by
          simpa [xR, xEe, xEp, rEp, heq] using hgeom
        field_simp [hxRpos.ne', hxEepos.ne'] at hrel
        linarith
      have hxR' : xR = xEe / sqrt 3 := by
        have h3 : (sqrt 3) ^ 2 = 3 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
        have hsq' : xR ^ 2 = (xEe / sqrt 3) ^ 2 := by
          calc
            xR ^ 2 = xEe ^ 2 / 3 := hsq
            _ = xEe ^ 2 / (sqrt 3) ^ 2 := by rw [h3]
            _ = (xEe / sqrt 3) ^ 2 := by rw [← div_pow]
        exact (sq_eq_sq₀ hxRpos.le (by positivity)).mp hsq'
      have hsqrt3 : (1 : ℝ) < sqrt 3 :=
        lt_of_pow_lt_pow_left₀ 2 (sqrt_nonneg _) <| by
          rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
          norm_num
      have hxRwell' : xR ∈ Ioo (0 : ℝ) resonanceRoot1 := by
        refine ⟨hxRpos, ?_⟩
        rw [hxR']
        have hlt : xEe / sqrt 3 < xEe := by
          rw [div_lt_iff₀ (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
          nlinarith [hsqrt3]
        exact lt_trans hlt hxEewell
      exact hcoinc hxRwell'
    · have hxEege : resonanceRoot1 ≤ xEe := le_of_not_gt hxEewell
      have hsum : 1 / xR ^ 2 + 1 / xEe ^ 2 ≤ 2 / resonanceRoot1 ^ 2 := by
        have hinvR : 1 / xR ^ 2 ≤ 1 / resonanceRoot1 ^ 2 := by
          rw [one_div_le_one_div (by positivity) (by positivity)]
          nlinarith
        have hinvE : 1 / xEe ^ 2 ≤ 1 / resonanceRoot1 ^ 2 := by
          rw [one_div_le_one_div (by positivity) (by positivity)]
          nlinarith
        have htwo : 1 / resonanceRoot1 ^ 2 + 1 / resonanceRoot1 ^ 2 =
            2 / resonanceRoot1 ^ 2 := by ring
        rw [← htwo]
        exact add_le_add hinvR hinvE
      have h4 : 4 / xEp ^ 2 ≤ 2 / resonanceRoot1 ^ 2 := by
        have hrel : 4 / xEp ^ 2 = 1 / xR ^ 2 + 1 / xEe ^ 2 := by
          simpa [xR, xEe, xEp, rEp] using hgeom
        linarith
      have hcross : 2 * resonanceRoot1 ^ 2 ≤ xEp ^ 2 := by
        have h' : 4 * resonanceRoot1 ^ 2 ≤ 2 * xEp ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)] at h4
          linarith
        linarith
      have hle : resonanceRoot1 * sqrt 2 ≤ xEp := by
        have hsq : (resonanceRoot1 * sqrt 2) ^ 2 ≤ xEp ^ 2 := by
          rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          linarith
        exact le_of_sq_le_sq hsq hxEp.1.le
      have hbig : resonanceRoot1 < resonanceRoot1 * sqrt 2 := by
        nlinarith [one_lt_sqrt_two, hx1]
      linarith [hxEp.2, hle, hbig]

theorem square_side_eq_diag_div_sqrtTwo {ℓ R : ℝ} (hR : 0 < R)
    (hγ : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (_hγs : gammaSEqual (sqrt 2 * (ℓ / (2 * R))) ≠ 0)
    (hbal : squareBalance (ℓ / (2 * R)) = 0) :
    |1 / (gammaSEqual (sqrt 2 * (ℓ / (2 * R))) * (R / sqrt 2) ^ 2)| =
      |1 / (gammaSEqual (ℓ / (2 * R)) * R ^ 2)| / sqrt 2 := by
  set x : ℝ := ℓ / (2 * R)
  have hrel : gammaSEqual (sqrt 2 * x) = 2 * sqrt 2 * gammaSEqual x := by
    unfold squareBalance at hbal
    linarith
  have hspos : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have hr2 : (R / sqrt 2) ^ 2 = R ^ 2 / 2 := by
    rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hR2 : 0 < R ^ 2 := by positivity
  have hhalf : 0 < R ^ 2 / 2 := by positivity
  have habs {a d : ℝ} (hd : 0 < d) :
      |1 / (a * d)| = 1 / (|a| * d) := by
    rw [abs_div, abs_one, abs_mul, abs_of_pos hd]
  have hside : |1 / (gammaSEqual (sqrt 2 * x) * (R / sqrt 2) ^ 2)| =
      1 / (|gammaSEqual (sqrt 2 * x)| * (R ^ 2 / 2)) := by
    rw [hr2, habs hhalf]
  have hdiag : |1 / (gammaSEqual x * R ^ 2)| = 1 / (|gammaSEqual x| * R ^ 2) :=
    habs hR2
  have hγsabs : |gammaSEqual (sqrt 2 * x)| = 2 * sqrt 2 * |gammaSEqual x| := by
    rw [hrel, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos hspos]
  have hγabs : |gammaSEqual x| ≠ 0 := abs_ne_zero.mpr hγ
  rw [hside, hdiag, hγsabs]
  field_simp [hR.ne', hspos.ne', hγabs]

end Gravity

end DstDiophantine
