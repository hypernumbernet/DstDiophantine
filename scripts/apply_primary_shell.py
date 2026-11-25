#!/usr/bin/env python3
"""Insert primary square-shell proofs into ElectronSquare.lean."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "DstDiophantine/Gravity/ElectronSquare.lean"
text = TARGET.read_text()

GAMMA_BLOCK = r'''
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
  constructor
  · calc
      (E1 / 2 + 1 / (2 * E0)) * cLo ≤ (exp x / 2 + exp (-x) / 2) * cLo :=
        mul_le_mul_of_nonneg_left hcoefHi (le_trans hClo hcHi)
      _ ≤ (exp x / 2 + exp (-x) / 2) * cos x :=
        mul_le_mul_of_nonpos_left hClo (by positivity)
  · calc
      (exp x / 2 + exp (-x) / 2) * cos x ≤ (exp x / 2 + exp (-x) / 2) * cHi :=
        mul_le_mul_of_nonpos_left hChi (by positivity)
      _ ≤ (E0 / 2 + 1 / (2 * E1)) * cHi :=
        mul_le_mul_of_nonneg_right hcoefLo hcHi

lemma gamma_pi_sub_before {x ζ a b E0 E1 : ℝ} (hx : x = π - ζ)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hζa : a ≤ ζ) (hζb : ζ ≤ b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1) :
    gammaCosLower E1 E0 (-cosHi a b) ≤ gammaSEqual x ∧
      gammaSEqual x ≤ gammaCosUpper E0 E1 (-cosLo b) := by
  have hcosζ := cos_mem_bounds ha hb hζa hζb
  have hb0 : 0 ≤ b := le_trans ha hζb
  have hcosx : cos x = -cos ζ := by rw [hx, cos_pi_sub]
  have hcHi : (-cosLo b) ≤ 0 := by
    dsimp [cosLo]
    nlinarith [hb0, sq_nonneg b, sq_nonneg (b ^ 3), sq_nonneg (b ^ 4)]
  have hClo : -cosHi a b ≤ cos x := by rw [hcosx]; linarith [hcosζ.2]
  have hChi : cos x ≤ -cosLo b := by rw [hcosx]; linarith [hcosζ.1]
  obtain ⟨hlo, hhi⟩ :=
    gamma_cos_cert_bounds_nonpos x E0 E1 (-cosHi a b) (-cosLo b) hE0 hE hE1 hClo hChi hcHi
  dsimp only [gammaCosLower, gammaCosUpper]
  exact ⟨hlo, hhi⟩

lemma gamma_pi_add_after {x η a b E0 E1 : ℝ} (hx : x = π + η)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hηa : a ≤ η) (hηb : η ≤ b)
    (hE0 : 0 < E0) (hE : E0 ≤ exp x) (hE1 : exp x ≤ E1) :
    gammaCosLower E1 E0 (-cosHi a b) ≤ gammaSEqual x ∧
      gammaSEqual x ≤ gammaCosUpper E0 E1 (-cosLo b) := by
  have hcosη := cos_mem_bounds ha hb hηa hηb
  have hb0 : 0 ≤ b := le_trans ha hηb
  have hcosx : cos x = -cos η := by rw [hx, cos_add_pi]
  have hcHi : (-cosLo b) ≤ 0 := by
    dsimp [cosLo]
    nlinarith [hb0, sq_nonneg b, sq_nonneg (b ^ 3), sq_nonneg (b ^ 4)]
  have hClo : -cosHi a b ≤ cos x := by rw [hcosx]; linarith [hcosη.2]
  have hChi : cos x ≤ -cosLo b := by rw [hcosx]; linarith [hcosη.1]
  obtain ⟨hlo, hhi⟩ :=
    gamma_cos_cert_bounds_nonpos x E0 E1 (-cosHi a b) (-cosLo b) hE0 hE hE1 hClo hChi hcHi
  dsimp only [gammaCosLower, gammaCosUpper]
  exact ⟨hlo, hhi⟩

'''

PRIMARY_BLOCK = r'''
private lemma exp_two_sq_bounds :
    (7389 / 1000 : ℝ) < (exp 1) ^ 2 ∧ (exp 1) ^ 2 < (7392 / 1000 : ℝ) := by
  constructor <;> nlinarith [exp_one_gt_d9, exp_one_lt_d9, exp_pos 1]

private lemma exp_two_thirds_bounds :
    (1943 / 1000 : ℝ) < exp (2 / 3) ∧ exp (2 / 3) < (1944 / 1000 : ℝ) := by
  refine exp_between (x := 2 / 3) (n := 10) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_side_tail_sixtyseven_bounds :
    (1968 / 1000 : ℝ) < exp (676955 / 1000000) ∧
      exp (676955 / 1000000) < (1969 / 1000 : ℝ) := by
  refine exp_between (x := 676955 / 1000000) (n := 10) (by norm_num) (by norm_num) (by decide)
    ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_side_tail_seventyseven_bounds :
    (2167 / 1000 : ℝ) < exp (771236 / 1000000) ∧
      exp (771236 / 1000000) < (2168 / 1000 : ℝ) := by
  refine exp_between (x := 771236 / 1000000) (n := 10) (by norm_num) (by norm_num) (by decide)
    ?_ ?_
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

private lemma sqrt2_mul_thirteen_fifths_eq : sqrt 2 * (13 / 5) = 3 + 676955 / 1000000 := by
  nlinarith [sqrt_two_bounds.1, sqrt_two_bounds.2]

private lemma sqrt2_mul_eight_thirds_eq : sqrt 2 * (8 / 3) = 3 + 771236 / 1000000 := by
  nlinarith [sqrt_two_bounds.1, sqrt_two_bounds.2]

private lemma exp_sqrt2_thirteen_fifths_bounds :
    (3940 / 100 : ℝ) < exp (sqrt 2 * (13 / 5)) ∧
      exp (sqrt 2 * (13 / 5)) < (3965 / 100 : ℝ) := by
  have hid : exp (sqrt 2 * (13 / 5)) = (exp 1) ^ 3 * exp (676955 / 1000000) := by
    rw [sqrt2_mul_thirteen_fifths_eq, show (3 : ℝ) = 1 + 1 + 1 by norm_num, exp_add, exp_add]
  constructor <;> rw [hid] <;> nlinarith [exp_two_sq_bounds, exp_one_gt_d9, exp_one_lt_d9,
    exp_side_tail_sixtyseven_bounds, exp_pos 1]

private lemma exp_sqrt2_eight_thirds_bounds :
    (4330 / 100 : ℝ) < exp (sqrt 2 * (8 / 3)) ∧
      exp (sqrt 2 * (8 / 3)) < (4360 / 100 : ℝ) := by
  have hid : exp (sqrt 2 * (8 / 3)) = (exp 1) ^ 3 * exp (771236 / 1000000) := by
    rw [sqrt2_mul_eight_thirds_eq, show (3 : ℝ) = 1 + 1 + 1 by norm_num, exp_add, exp_add]
  constructor <;> rw [hid] <;> nlinarith [exp_two_sq_bounds, exp_one_gt_d9, exp_one_lt_d9,
    exp_side_tail_seventyseven_bounds, exp_pos 1]

private lemma gamma_thirteen_fifths_lower :
    gammaCosLower (13480 / 1000) (13450 / 1000)
      (-(cosHi (474926 / 1000000) (541593 / 1000000))) ≤ gammaSEqual (13 / 5) := by
  set ζ := π - 13 / 5
  have hx : 13 / 5 = π - ζ := by simp [ζ]
  exact (gamma_pi_sub_before (x := 13 / 5) (ζ := ζ) (a := 474926 / 1000000) (b := 541593 / 1000000)
    (E0 := 13450 / 1000) (E1 := 13480 / 1000) hx (by norm_num) (by norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])
    (by positivity) exp_thirteen_fifths_bounds.1.le exp_thirteen_fifths_bounds.2.le).1

private lemma gamma_thirteen_fifths_upper :
    gammaSEqual (13 / 5) ≤
      gammaCosUpper (13450 / 1000) (13480 / 1000) (-cosLo (541593 / 1000000)) := by
  set ζ := π - 13 / 5
  have hx : 13 / 5 = π - ζ := by simp [ζ]
  exact (gamma_pi_sub_before (x := 13 / 5) (ζ := ζ) (a := 474926 / 1000000) (b := 541593 / 1000000)
    (E0 := 13450 / 1000) (E1 := 13480 / 1000) hx (by norm_num) (by norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])
    (by positivity) exp_thirteen_fifths_bounds.1.le exp_thirteen_fifths_bounds.2.le).2

private lemma gamma_sqrt2_thirteen_fifths_upper :
    gammaSEqual (sqrt 2 * (13 / 5)) ≤
      gammaCosUpper (3940 / 100) (3965 / 100) (-cosLo (535362 / 1000000)) := by
  set η := sqrt 2 * (13 / 5) - π
  have hx : sqrt 2 * (13 / 5) = π + η := by simp [η]
  have hηa : 535362 / 1000000 ≤ η := by
    dsimp [η]; nlinarith [sqrt_two_bounds.1, pi_gt_d6, sqrt2_mul_thirteen_fifths_eq]
  have hηb : η ≤ 535363 / 1000000 := by
    dsimp [η]; nlinarith [sqrt_two_bounds.2, pi_lt_d6, sqrt2_mul_thirteen_fifths_eq]
  exact (gamma_pi_add_after (x := sqrt 2 * (13 / 5)) (η := η) (a := 535362 / 1000000)
    (b := 535363 / 1000000) (E0 := 3940 / 100) (E1 := 3965 / 100) hx (by norm_num) (by norm_num)
    hηa hηb (by positivity) exp_sqrt2_thirteen_fifths_bounds.1.le
    exp_sqrt2_thirteen_fifths_bounds.2.le).2

private lemma gamma_eight_thirds_lower :
    gammaCosLower (14410 / 1000) (14380 / 1000)
      (-(cosHi (474925 / 1000000) (474927 / 1000000))) ≤ gammaSEqual (8 / 3) := by
  set ζ := π - 8 / 3
  have hx : 8 / 3 = π - ζ := by simp [ζ]
  exact (gamma_pi_sub_before (x := 8 / 3) (ζ := ζ) (a := 474925 / 1000000) (b := 474927 / 1000000)
    (E0 := 14380 / 1000) (E1 := 14410 / 1000) hx (by norm_num) (by norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])
    (by positivity) exp_eight_thirds_bounds.1.le exp_eight_thirds_bounds.2.le).1

private lemma gamma_eight_thirds_upper :
    gammaSEqual (8 / 3) ≤
      gammaCosUpper (14380 / 1000) (14410 / 1000) (-cosLo (474927 / 1000000)) := by
  set ζ := π - 8 / 3
  have hx : 8 / 3 = π - ζ := by simp [ζ]
  exact (gamma_pi_sub_before (x := 8 / 3) (ζ := ζ) (a := 474925 / 1000000) (b := 474927 / 1000000)
    (E0 := 14380 / 1000) (E1 := 14410 / 1000) hx (by norm_num) (by norm_num)
    (by dsimp [ζ]; linarith [pi_gt_d6]) (by dsimp [ζ]; linarith [pi_lt_d6])
    (by positivity) exp_eight_thirds_bounds.1.le exp_eight_thirds_bounds.2.le).2

private lemma gamma_sqrt2_eight_thirds_lower :
    gammaCosLower (4360 / 100) (4330 / 100)
      (-(cosHi (629843 / 1000000) (629844 / 1000000))) ≤ gammaSEqual (sqrt 2 * (8 / 3)) := by
  set η := sqrt 2 * (8 / 3) - π
  have hx : sqrt 2 * (8 / 3) = π + η := by simp [η]
  have hηa : 629843 / 1000000 ≤ η := by
    dsimp [η]; nlinarith [sqrt_two_bounds.1, pi_gt_d6, sqrt2_mul_eight_thirds_eq]
  have hηb : η ≤ 629844 / 1000000 := by
    dsimp [η]; nlinarith [sqrt_two_bounds.2, pi_lt_d6, sqrt2_mul_eight_thirds_eq]
  exact (gamma_pi_add_after (x := sqrt 2 * (8 / 3)) (η := η) (a := 629843 / 1000000)
    (b := 629844 / 1000000) (E0 := 4330 / 100) (E1 := 4360 / 100) hx (by norm_num) (by norm_num)
    hηa hηb (by positivity) exp_sqrt2_eight_thirds_bounds.1.le
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
  have hA : 2 * sqrt 2 < 99 / 35 := two_sqrt_two_bounds.2
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
  have hA : 280 / 99 < 2 * sqrt 2 := two_sqrt_two_bounds.1
  unfold squareBalance
  linarith

theorem exists_square_shell_primary :
    ∃ x, x ∈ Set.Ioo (13 / 5) (8 / 3) ∧ squareBalance x = 0 := by
  obtain ⟨x, hxI, hx0⟩ :=
    intermediate_value_Ioo (by norm_num)
      continuous_squareBalance.continuousOn
      ⟨squareBalance_thirteen_fifths_pos, squareBalance_eight_thirds_neg⟩
  exact ⟨x, hxI, hx0⟩

'''

ANCHOR1 = "    linarith\n\n/-! ### Square geometry -/"
ANCHOR2 = "/-! ### Primary late-branch square shell -/\n\n\n\n"
REPL2 = "/-! ### Primary late-branch square shell -/\n\n" + PRIMARY_BLOCK.strip() + "\n\n"

if GAMMA_BLOCK.strip() in text:
    print("gamma block already present")
else:
    if ANCHOR1 not in text:
        raise SystemExit("anchor1 not found")
    text = text.replace(ANCHOR1, "    linarith\n" + GAMMA_BLOCK + "\n/-! ### Square geometry -/", 1)

if "exists_square_shell_primary" in text:
    print("primary block already present")
else:
    if ANCHOR2 not in text and REPL2.split("\n\n", 1)[0] + "\n\n" not in text:
        # tolerate variable blank lines
        import re
        m = re.search(r"/-! ### Primary late-branch square shell -/\n+", text)
        if not m:
            raise SystemExit("anchor2 not found")
        text = text[:m.end()] + "\n" + PRIMARY_BLOCK.strip() + "\n\n" + text[m.end():].lstrip()
    else:
        text = text.replace(ANCHOR2, REPL2, 1)

TARGET.write_text(text)
print(f"wrote {TARGET} ({len(text.splitlines())} lines)")