#!/usr/bin/env python3
"""Restore primary square shell block and apply build fixes."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
p = ROOT / "DstDiophantine/Gravity/ElectronSquare.lean"

subprocess.run(
    ["git", "checkout", "origin/cursor/mismatch-angle-511f-wip", "--", str(p)],
    cwd=ROOT,
    check=True,
)

t = p.read_text()

# hcosb typing
t = t.replace("neg_nonpos.mpr hcosb\n", "neg_nonpos.mpr hcosb.le\n")

# remove broken cosLo_pos if present
t = t.replace(
    """private lemma cosLo_pos {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1) : 0 < cosLo b := by
  dsimp [cosLo]
  nlinarith [hb0, hb, sq_nonneg b, sq_nonneg (b ^ 4)]

""",
    "",
)

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

if OLD_GAMMA in t:
    t = t.replace(OLD_GAMMA, NEW_GAMMA)

t = t.replace(
    "have hcosx : cos x = -cos η := by rw [hx, cos_add_pi]",
    "have hcosx : cos x = -cos η := by rw [hx, add_comm, cos_add_pi]",
)

# primary exp block replacements
EXP_BLOCK = r'''private lemma exp_two_sq_bounds :
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

'''

start = t.find("private lemma exp_two_sq_bounds :")
end = t.find("private lemma gamma_thirteen_fifths_lower", start)
if start != -1 and end != -1:
    t = t[:start] + EXP_BLOCK + "\n" + t[end:]

# squareBalance endpoint proofs
OLD_135 = """theorem squareBalance_thirteen_fifths_pos : squareBalance (13 / 5) < 0 := by
  have hlo := gamma_thirteen_fifths_lower
  have hhi := gamma_sqrt2_thirteen_fifths_upper
  have hcmp :
      gammaCosUpper (3940 / 100) (3965 / 100) (-cosLo (535362 / 1000000)) <
        (99 / 35) * gammaCosLower (13480 / 1000) (13450 / 1000)
          (-(cosHi (474926 / 1000000) (541593 / 1000000))) := by
    simp only [gammaCosUpper, gammaCosLower, cosLo, cosHi]
    norm_num
  have hA : 2 * sqrt 2 < 99 / 35 := two_sqrt_two_bounds.2
  unfold squareBalance
  linarith"""

NEW_135 = """theorem squareBalance_thirteen_fifths_pos : squareBalance (13 / 5) < 0 := by
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
  linarith"""

OLD_83 = """theorem squareBalance_eight_thirds_neg : 0 < squareBalance (8 / 3) := by
  have hlo := gamma_sqrt2_eight_thirds_lower
  have hhi := gamma_eight_thirds_upper
  have hcmp :
      (280 / 99) * gammaCosUpper (14380 / 1000) (14410 / 1000) (-cosLo (474927 / 1000000)) <
        gammaCosLower (4360 / 100) (4330 / 100)
          (-(cosHi (629843 / 1000000) (629844 / 1000000))) := by
    simp only [gammaCosUpper, gammaCosLower, cosLo, cosHi]
    norm_num
  have hA : 280 / 99 < 2 * sqrt 2 := two_sqrt_two_bounds.1
  unfold squareBalance
  linarith"""

NEW_83 = """theorem squareBalance_eight_thirds_neg : 0 < squareBalance (8 / 3) := by
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
  linarith"""

t = t.replace(OLD_135, NEW_135)
t = t.replace(OLD_83, NEW_83)

# ensure hcosb on all gamma_pi calls (add if missing after second norm_num)
for pat, repl in [
    (
        "(by norm_num) (by norm_num)\n    (by dsimp [ζ]; linarith [pi_gt_d6])",
        "(by norm_num) (by norm_num)\n    (by dsimp [cosLo]; norm_num)\n    (by dsimp [ζ]; linarith [pi_gt_d6])",
    ),
    (
        "(by norm_num) (by norm_num)\n    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])",
        "(by norm_num) (by norm_num)\n    (by dsimp [cosLo]; norm_num)\n    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])",
    ),
]:
    if "(by dsimp [cosLo]; norm_num)" not in t:
        t = t.replace(pat, repl)

# fix duplicate hcosb if any
t = re.sub(
    r"\(by dsimp \[cosLo\]; norm_num\)\n    \(by dsimp \[cosLo\]; norm_num\)",
    "(by dsimp [cosLo]; norm_num)",
    t,
)

# gamma_pi_sub_before: hζa/hζb before hcosb
t = t.replace(
    """hx (by norm_num) (by norm_num)
    (by dsimp [cosLo]; norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])""",
    """hx (by norm_num) (by norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])
    (by dsimp [cosLo]; norm_num)""",
)

# gamma_pi_add_after: hηa/hηb before hcosb
t = t.replace(
    """hx (by norm_num) (by norm_num)
    (by dsimp [cosLo]; norm_num) hηa hηb""",
    """hx (by norm_num) (by norm_num) hηa hηb
    (by dsimp [cosLo]; norm_num)""",
)

p.write_text(t)
print("wrote", p, "lines", len(t.splitlines()))