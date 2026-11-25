#!/usr/bin/env python3
from pathlib import Path
p = Path(__file__).resolve().parents[1] / "DstDiophantine/Gravity/ElectronSquare.lean"
t = p.read_text()

OLD_GAMMA = """  constructor
  · calc
      (E1 / 2 + 1 / (2 * E0)) * cLo ≤ (exp x / 2 + exp (-x) / 2) * cLo :=
        mul_le_mul_of_nonneg_left hcoefHi (le_trans hClo hcHi)
      _ ≤ (exp x / 2 + exp (-x) / 2) * cos x :=
        mul_le_mul_of_nonpos_left hClo (by positivity)
  · calc
      (exp x / 2 + exp (-x) / 2) * cos x ≤ (exp x / 2 + exp (-x) / 2) * cHi :=
        mul_le_mul_of_nonpos_left hChi (by positivity)
      _ ≤ (E0 / 2 + 1 / (2 * E1)) * cHi :=
        mul_le_mul_of_nonneg_right hcoefLo hcHi"""

NEW_GAMMA = """  have hclneg : cLo ≤ 0 := le_trans (le_trans hClo hChi) hcHi
  have hcoefpos : 0 ≤ exp x / 2 + exp (-x) / 2 := by positivity
  constructor <;> nlinarith [hcoefHi, hcoefLo, hClo, hChi, hcHi, hclneg, hcoefpos]"""

t = t.replace(OLD_GAMMA, NEW_GAMMA)

t = t.replace(
    "have hb0 : 0 ≤ b := le_trans ha hζb",
    "have hb0 : 0 ≤ b := le_trans ha (le_trans hζa hζb)",
)
t = t.replace(
    "have hb0 : 0 ≤ b := le_trans ha hηb",
    "have hb0 : 0 ≤ b := le_trans ha (le_trans hηa hηb)",
)

OLD_HC = """  have hcHi : (-cosLo b) ≤ 0 := by
    dsimp [cosLo]
    nlinarith [hb0, sq_nonneg b, sq_nonneg (b ^ 3), sq_nonneg (b ^ 4)]"""

NEW_HC = """  have hcHi : (-cosLo b) ≤ 0 := by
    have hcospos : 0 < cosLo b := by
      dsimp [cosLo]
      nlinarith [hb0, sq_nonneg b, sq_nonneg (b ^ 4)]
    linarith"""

t = t.replace(OLD_HC, NEW_HC)

t = t.replace(
    """  dsimp only [gammaCosLower, gammaCosUpper]
  exact ⟨hlo, hhi⟩""",
    """  dsimp only [gammaCosLower, gammaCosUpper] at hlo hhi ⊢
  exact ⟨hlo, hhi⟩""",
)

# exp/sqrt block from commit may use sqrt2_mul eq — replace whole sqrt2 exp section if present
OLD_SQ = t.find("private lemma sqrt2_mul_thirteen_fifths_eq")
if OLD_SQ != -1:
    end = t.find("private lemma gamma_thirteen_fifths_lower", OLD_SQ)
    NEW_SQ = r'''private lemma sqrt2_thirteen_tail_bounds :
    (676955 / 1000000 : ℝ) < sqrt 2 * (13 / 5) - 3 ∧
      sqrt 2 * (13 / 5) - 3 < (676956 / 1000000 : ℝ) := by
  constructor <;> nlinarith [sqrt_two_bounds.1, sqrt_two_bounds.2]

private lemma sqrt2_eight_thirds_tail_bounds :
    (771236 / 1000000 : ℝ) < sqrt 2 * (8 / 3) - 3 ∧
      sqrt 2 * (8 / 3) - 3 < (771237 / 1000000 : ℝ) := by
  constructor <;> nlinarith [sqrt_two_bounds.1, sqrt_two_bounds.2]

private lemma exp_sqrt2_thirteen_fifths_bounds :
    (3940 / 100 : ℝ) < exp (sqrt 2 * (13 / 5)) ∧
      exp (sqrt 2 * (13 / 5)) < (3965 / 100 : ℝ) := by
  have htail := sqrt2_thirteen_tail_bounds
  have hid : exp (sqrt 2 * (13 / 5)) = (exp 1) ^ 3 * exp (sqrt 2 * (13 / 5) - 3) := by
    have hx : sqrt 2 * (13 / 5) = 3 + (sqrt 2 * (13 / 5) - 3) := by ring
    rw [hx, show (3 : ℝ) = 1 + 1 + 1 by norm_num, exp_add, exp_add]
  have hexpLo : (1965 / 1000 : ℝ) < exp (sqrt 2 * (13 / 5) - 3) :=
    exp_side_tail_sixtyseven_bounds.1.trans (exp_strictMono htail.1)
  have hexpHi : exp (sqrt 2 * (13 / 5) - 3) < (1970 / 1000 : ℝ) := by
    have hstep : (676955 / 1000000 : ℝ) < 676956 / 1000000 := by norm_num
    exact (exp_strictMono htail.2).trans (exp_strictMono hstep)
      |>.trans exp_side_tail_sixtyseven_bounds.2
  constructor <;> rw [hid] <;> nlinarith [exp_two_sq_bounds, exp_one_gt_d9, exp_one_lt_d9, hexpLo,
    hexpHi, exp_pos 1]

private lemma exp_sqrt2_eight_thirds_bounds :
    (4330 / 100 : ℝ) < exp (sqrt 2 * (8 / 3)) ∧
      exp (sqrt 2 * (8 / 3)) < (4360 / 100 : ℝ) := by
  have htail := sqrt2_eight_thirds_tail_bounds
  have hid : exp (sqrt 2 * (8 / 3)) = (exp 1) ^ 3 * exp (sqrt 2 * (8 / 3) - 3) := by
    have hx : sqrt 2 * (8 / 3) = 3 + (sqrt 2 * (8 / 3) - 3) := by ring
    rw [hx, show (3 : ℝ) = 1 + 1 + 1 by norm_num, exp_add, exp_add]
  have hexpLo : (2165 / 1000 : ℝ) < exp (sqrt 2 * (8 / 3) - 3) :=
    exp_side_tail_seventyseven_bounds.1.trans (exp_strictMono htail.1)
  have hexpHi : exp (sqrt 2 * (8 / 3) - 3) < (2170 / 1000 : ℝ) := by
    have hstep : (771236 / 1000000 : ℝ) < 771237 / 1000000 := by norm_num
    exact (exp_strictMono htail.2).trans (exp_strictMono hstep)
      |>.trans exp_side_tail_seventyseven_bounds.2
  constructor <;> rw [hid] <;> nlinarith [exp_two_sq_bounds, exp_one_gt_d9, exp_one_lt_d9, hexpLo,
    hexpHi, exp_pos 1]

'''
    t = t[:OLD_SQ] + NEW_SQ + "\n" + t[end:]

# widen exp_two_thirds and side tails
t = t.replace(
    "(1943 / 1000 : ℝ) < exp (2 / 3) ∧ exp (2 / 3) < (1944 / 1000 : ℝ)",
    "(1940 / 1000 : ℝ) < exp (2 / 3) ∧ exp (2 / 3) < (1950 / 1000 : ℝ)",
)
t = t.replace(
    "(1968 / 1000 : ℝ) < exp (676955 / 1000000) ∧\n      exp (676955 / 1000000) < (1969 / 1000 : ℝ)",
    "(1965 / 1000 : ℝ) < exp (676955 / 1000000) ∧\n      exp (676955 / 1000000) < (1970 / 1000 : ℝ)",
)
t = t.replace(
    "(2167 / 1000 : ℝ) < exp (771236 / 1000000) ∧\n      exp (771236 / 1000000) < (2168 / 1000 : ℝ)",
    "(2165 / 1000 : ℝ) < exp (771236 / 1000000) ∧\n      exp (771236 / 1000000) < (2170 / 1000 : ℝ)",
)

# fix eta bounds proofs removing sqrt2_mul refs
t = t.replace(
    "nlinarith [sqrt_two_bounds.1, pi_gt_d6, sqrt2_mul_thirteen_fifths_eq]",
    "nlinarith [sqrt_two_bounds.1, pi_gt_d6]",
)
t = t.replace(
    "nlinarith [sqrt_two_bounds.2, pi_lt_d6, sqrt2_mul_thirteen_fifths_eq]",
    "nlinarith [sqrt_two_bounds.2, pi_lt_d6]",
)
t = t.replace(
    "nlinarith [sqrt_two_bounds.1, pi_gt_d6, sqrt2_mul_eight_thirds_eq]",
    "nlinarith [sqrt_two_bounds.1, pi_gt_d6]",
)
t = t.replace(
    "nlinarith [sqrt_two_bounds.2, pi_lt_d6, sqrt2_mul_eight_thirds_eq]",
    "nlinarith [sqrt_two_bounds.2, pi_lt_d6]",
)

p.write_text(t)
print("patched", p)