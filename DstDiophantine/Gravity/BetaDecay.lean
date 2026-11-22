import DstDiophantine.Gravity.NuclearLayer
import DstDiophantine.Gravity.SignReversal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Neutron β decay as a replacement of rotor class

Replacing one rotor class preserves the factor count and the winding sum, and
raises the electromagnetic label by \(1\). The V--A coupling, the lifetime,
the spectrum, masses, and the moments in nuclear magnetons are not derived;
the weights \(4/3\) and \(-1/3\) are chart inputs.
-/

namespace DstDiophantine

namespace Gravity

open SI

/-! ### The quark-charge chart -/

theorem quarkChart_holds :
    2 * ((2 : ℚ) / 3) + ((-1 : ℚ) / 3) = 1 ∧
      (2 : ℚ) / 3 + 2 * ((-1 : ℚ) / 3) = 0 := by
  norm_num

theorem quarkChart_unique {u d : ℚ} (hp : 2 * u + d = 1) (hn : u + 2 * d = 0) :
    u = (2 : ℚ) / 3 ∧ d = (-1 : ℚ) / 3 := by
  have h3 : d * 3 = -1 := by linarith
  have h3' : ((-1 : ℚ) / 3) * 3 = -1 := by norm_num
  have hd : d = (-1 : ℚ) / 3 :=
    mul_right_cancel₀ (by norm_num : (3 : ℚ) ≠ 0) (h3.trans h3'.symm)
  refine ⟨?_, hd⟩
  linarith

theorem quarkChart_three_sums :
    3 * ((2 : ℚ) / 3) = 2 ∧
      2 * ((2 : ℚ) / 3) + ((-1 : ℚ) / 3) = 1 ∧
      (2 : ℚ) / 3 + 2 * ((-1 : ℚ) / 3) = 0 ∧
      3 * ((-1 : ℚ) / 3) = -1 := by
  norm_num

theorem quarkChart_mesons :
    (2 : ℚ) / 3 + -((-1 : ℚ) / 3) = 1 ∧ (2 : ℚ) / 3 + -((2 : ℚ) / 3) = 0 := by
  norm_num

theorem quarkChart_R :
    ((2 : ℚ) / 3) ^ 2 + ((-1 : ℚ) / 3) ^ 2 + ((-1 : ℚ) / 3) ^ 2 = (2 : ℚ) / 3 ∧
      3 * (((2 : ℚ) / 3) ^ 2 + ((-1 : ℚ) / 3) ^ 2 + ((-1 : ℚ) / 3) ^ 2) = 2 := by
  norm_num

/-! ### Chart moments -/

def chartMuP (μu μd : ℚ) : ℚ := (4 : ℚ) / 3 * μu - (1 : ℚ) / 3 * μd

def chartMuN (μu μd : ℚ) : ℚ := (4 : ℚ) / 3 * μd - (1 : ℚ) / 3 * μu

theorem chart_sum_identity (μu μd : ℚ) :
    chartMuP μu μd + chartMuN μu μd = μu + μd := by
  simp only [chartMuP, chartMuN]
  ring

theorem chart_diff_identity (μu μd : ℚ) :
    chartMuP μu μd - chartMuN μu μd = ((5 : ℚ) / 3) * (μu - μd) := by
  simp only [chartMuP, chartMuN]
  ring

theorem chart_moment_ratios {μu μd : ℚ} (h : μu = -2 * μd) (hd : μd ≠ 0) :
    chartMuN μu μd / chartMuP μu μd = (-2 : ℚ) / 3 ∧
      (chartMuP μu μd + chartMuN μu μd) / (chartMuP μu μd - chartMuN μu μd) =
        (1 : ℚ) / 5 := by
  have hp : chartMuP μu μd = -3 * μd := by
    simp only [chartMuP, h]
    ring
  have hn : chartMuN μu μd = 2 * μd := by
    simp only [chartMuN, h]
    ring
  have hd0 : chartMuP μu μd - chartMuN μu μd ≠ 0 := by
    rw [hp, hn]
    have hring : -3 * μd - 2 * μd = -5 * μd := by ring
    rw [hring]
    exact mul_ne_zero (by norm_num) hd
  constructor
  · rw [hp, hn]
    field_simp [hd]
  · rw [chart_sum_identity, chart_diff_identity, h]
    field_simp [hd, hd0]
    ring

/-! ### Measured moments on the CODATA rectangle -/

private theorem moment_corner_ratio_lo :
    (-137 : ℚ) / 200 < (-191305 : ℚ) / 279284 := by
  norm_num

private theorem moment_corner_ratio_hi :
    (-191303 : ℚ) / 279286 < (-171 : ℚ) / 250 := by
  norm_num

private theorem moment_corner_gap :
    (1 : ℚ) / 55 < (-2 : ℚ) / 3 - ((-191303 : ℚ) / 279286) ∧
      (-2 : ℚ) / 3 - ((-191305 : ℚ) / 279284) < (1 : ℚ) / 54 := by
  norm_num

private theorem moment_corner_sum_ratio :
    (9 : ℚ) / 50 <
        (1 + (-191305 : ℚ) / 279284) / (1 - (-191305 : ℚ) / 279284) ∧
      (1 + (-191303 : ℚ) / 279286) / (1 - (-191303 : ℚ) / 279286) <
        (19 : ℚ) / 100 := by
  norm_num

private theorem moment_corner_deficit :
    (1 : ℚ) / 80 <
        (1 : ℚ) / 5 -
          (1 + (-191303 : ℚ) / 279286) / (1 - (-191303 : ℚ) / 279286) ∧
      (1 : ℚ) / 5 -
          (1 + (-191305 : ℚ) / 279284) / (1 - (-191305 : ℚ) / 279284) <
        (1 : ℚ) / 70 := by
  norm_num

theorem ratio_between_corners {μp μn : ℚ}
    (hp0 : (279284 : ℚ) / 100000 < μp) (hp1 : μp < (279286 : ℚ) / 100000)
    (hn0 : (-191305 : ℚ) / 100000 < μn) (hn1 : μn < (-191303 : ℚ) / 100000) :
    (-191305 : ℚ) / 279284 < μn / μp ∧ μn / μp < (-191303 : ℚ) / 279286 := by
  have hppos : 0 < μp := by
    have : (0 : ℚ) < (279284 : ℚ) / 100000 := by norm_num
    linarith
  have hpLo : (0 : ℚ) < (279284 : ℚ) / 100000 := by norm_num
  have hpHi : (0 : ℚ) < (279286 : ℚ) / 100000 := by linarith
  have hrew : (-191305 : ℚ) / 100000 / ((279284 : ℚ) / 100000) =
      (-191305 : ℚ) / 279284 := by
    field_simp
  have hfloor : (-191305 : ℚ) / 279284 < μn / μp := by
    have h1 : (-191305 : ℚ) / 100000 / μp < μn / μp := by
      rw [div_lt_div_iff₀ hppos hppos]
      nlinarith
    have h2 : (-191305 : ℚ) / 279284 < (-191305 : ℚ) / 100000 / μp := by
      have hnLo : (-191305 : ℚ) / 100000 < 0 := by norm_num
      rw [← hrew, div_lt_div_iff₀ hpLo hppos]
      nlinarith
    linarith
  have hceilRew : (-191303 : ℚ) / 100000 / ((279286 : ℚ) / 100000) =
      (-191303 : ℚ) / 279286 := by
    field_simp
  have hceil : μn / μp < (-191303 : ℚ) / 279286 := by
    have h1 : μn / μp < (-191303 : ℚ) / 100000 / μp := by
      rw [div_lt_div_iff₀ hppos hppos]
      nlinarith
    have h2 : (-191303 : ℚ) / 100000 / μp < (-191303 : ℚ) / 279286 := by
      have hnHi : (-191303 : ℚ) / 100000 < 0 := by norm_num
      rw [← hceilRew, div_lt_div_iff₀ hppos hpHi]
      nlinarith
    linarith
  exact ⟨hfloor, hceil⟩

theorem measured_moment_ratio {μp μn : ℚ}
    (hp0 : (279284 : ℚ) / 100000 < μp) (hp1 : μp < (279286 : ℚ) / 100000)
    (hn0 : (-191305 : ℚ) / 100000 < μn) (hn1 : μn < (-191303 : ℚ) / 100000) :
    (-137 : ℚ) / 200 < μn / μp ∧ μn / μp < (-171 : ℚ) / 250 ∧
      (1 : ℚ) / 55 < (-2 : ℚ) / 3 - μn / μp ∧
        (-2 : ℚ) / 3 - μn / μp < (1 : ℚ) / 54 := by
  have h := ratio_between_corners hp0 hp1 hn0 hn1
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [moment_corner_ratio_lo, h.1]
  · linarith [moment_corner_ratio_hi, h.2]
  · linarith [moment_corner_gap.1, h.2]
  · linarith [moment_corner_gap.2, h.1]

theorem measured_sum_diff {μp μn : ℚ}
    (hp0 : (279284 : ℚ) / 100000 < μp) (hp1 : μp < (279286 : ℚ) / 100000)
    (hn0 : (-191305 : ℚ) / 100000 < μn) (hn1 : μn < (-191303 : ℚ) / 100000) :
    (87979 : ℚ) / 100000 < μp + μn ∧ μp + μn < (87983 : ℚ) / 100000 ∧
      (470587 : ℚ) / 100000 < μp - μn ∧ μp - μn < (470591 : ℚ) / 100000 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

private theorem sumRatio_mono {r₁ r₂ : ℚ} (h : r₁ < r₂)
    (hd1 : 0 < 1 - r₁) (hd2 : 0 < 1 - r₂) :
    (1 + r₁) / (1 - r₁) < (1 + r₂) / (1 - r₂) := by
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith

theorem measured_sum_ratio {μp μn : ℚ}
    (hp0 : (279284 : ℚ) / 100000 < μp) (hp1 : μp < (279286 : ℚ) / 100000)
    (hn0 : (-191305 : ℚ) / 100000 < μn) (hn1 : μn < (-191303 : ℚ) / 100000) :
    let ρ := (μp + μn) / (μp - μn)
    (9 : ℚ) / 50 < ρ ∧ ρ < (19 : ℚ) / 100 ∧
      (1 : ℚ) / 80 < (1 : ℚ) / 5 - ρ ∧ (1 : ℚ) / 5 - ρ < (1 : ℚ) / 70 := by
  intro ρ
  have hcorners := ratio_between_corners hp0 hp1 hn0 hn1
  have hppos : 0 < μp := by
    have : (0 : ℚ) < (279284 : ℚ) / 100000 := by norm_num
    linarith
  have hdpos : 0 < μp - μn := by linarith
  set r : ℚ := μn / μp
  have hrlo : (-191305 : ℚ) / 279284 < r := hcorners.1
  have hrhi : r < (-191303 : ℚ) / 279286 := hcorners.2
  have hdenLo : (0 : ℚ) < 1 - ((-191305 : ℚ) / 279284) := by norm_num
  have hdenHi : (0 : ℚ) < 1 - ((-191303 : ℚ) / 279286) := by norm_num
  have hden : 0 < 1 - r := by linarith
  have hrewrite : ρ = (1 + r) / (1 - r) := by
    have hμ : μp ≠ 0 := ne_of_gt hppos
    dsimp only [ρ, r]
    field_simp [hμ]
  have hflo := sumRatio_mono hrlo hdenLo hden
  have hfhi := sumRatio_mono hrhi hden hdenHi
  rw [hrewrite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [moment_corner_sum_ratio.1]
  · linarith [moment_corner_sum_ratio.2]
  · linarith [moment_corner_deficit.1]
  · linarith [moment_corner_deficit.2]

/-! ### Replacement of one class -/

inductive NucleonClass
  | proton
  | neutron
  deriving DecidableEq

namespace NucleonClass

/-- Baryon number is a label of the class, taken from the discrete companion. -/
def baryon : NucleonClass → ℕ
  | _ => 1

/-- Dual-phase winding is a label of the class. One nucleon is the case \(\ell=1\). -/
def winding : NucleonClass → ℕ
  | _ => 3

/-- Electromagnetic label in units of \(e\). The neutron is the case \(0\). -/
def emLabel : NucleonClass → ℤ
  | proton => 1
  | neutron => 0

def replace : NucleonClass → NucleonClass
  | proton => neutron
  | neutron => proton

theorem replace_winding (c : NucleonClass) : winding (replace c) = winding c := by
  cases c <;> rfl

theorem replace_baryon (c : NucleonClass) : baryon (replace c) = baryon c := by
  cases c <;> rfl

theorem replace_neutron_label : emLabel (replace neutron) = 1 := rfl

theorem replace_proton_label : emLabel (replace proton) = 0 := rfl

end NucleonClass

def totalWinding : List NucleonClass → ℕ
  | [] => 0
  | c :: xs => NucleonClass.winding c + totalWinding xs

def totalEm : List NucleonClass → ℤ
  | [] => 0
  | c :: xs => NucleonClass.emLabel c + totalEm xs

def replaceAt : List NucleonClass → ℕ → NucleonClass → List NucleonClass
  | [], _, _ => []
  | _ :: xs, 0, c => c :: xs
  | b :: xs, n + 1, c => b :: replaceAt xs n c

def nthIsNeutron : List NucleonClass → ℕ → Prop
  | [], _ => False
  | c :: _, 0 => c = .neutron
  | _ :: xs, n + 1 => nthIsNeutron xs n

theorem totalWinding_eq_three (xs : List NucleonClass) :
    totalWinding xs = 3 * xs.length := by
  induction xs with
  | nil => simp [totalWinding]
  | cons c xs ih =>
    simp only [totalWinding, NucleonClass.winding, List.length_cons, ih]
    rw [Nat.add_comm, Nat.mul_add, Nat.mul_one]

theorem replaceAt_length (xs : List NucleonClass) (i : ℕ) (c : NucleonClass) :
    (replaceAt xs i c).length = xs.length := by
  induction xs generalizing i with
  | nil => simp [replaceAt]
  | cons _ tail ih =>
    cases i with
    | zero => simp [replaceAt]
    | succ n => simp [replaceAt, ih n]

theorem replaceAt_winding (xs : List NucleonClass) (i : ℕ) (c : NucleonClass) :
    totalWinding (replaceAt xs i c) = totalWinding xs := by
  rw [totalWinding_eq_three, totalWinding_eq_three, replaceAt_length]

theorem charge_with_emission (xs : List NucleonClass) (i : ℕ)
    (h : nthIsNeutron xs i) :
    totalEm (replaceAt xs i .proton) + (-1) = totalEm xs := by
  induction xs generalizing i with
  | nil => simp [nthIsNeutron] at h
  | cons c xs ih =>
    cases i with
    | zero =>
      simp only [nthIsNeutron, replaceAt, totalEm, NucleonClass.emLabel] at h ⊢
      subst h
      ring
    | succ n =>
      simp only [nthIsNeutron, replaceAt, totalEm] at h ⊢
      have ih' := ih n h
      linarith

/-- When the extra Coulomb cost exceeds the free gap, the proton-richer product is heavier; both
quantities are inputs. -/
theorem reverse_opens_when_coulomb_exceeds {gap cost : ℚ} (hcost : gap < cost) :
    0 < cost - gap := by
  linarith

/-! ### The free gap, as an external window -/

theorem qValue_corners :
    (782 : ℚ) / 1000 < (12933 : ℚ) / 10000 - (51101 : ℚ) / 100000 ∧
      (12934 : ℚ) / 10000 - (51099 : ℚ) / 100000 < (783 : ℚ) / 1000 := by
  norm_num

theorem massRatio_corners :
    (5 : ℚ) / 2 < ((12933 : ℚ) / 10000) / ((51101 : ℚ) / 100000) ∧
      ((12934 : ℚ) / 10000) / ((51099 : ℚ) / 100000) < (38 : ℚ) / 15 := by
  norm_num

theorem gap_above_electron :
    (51101 : ℚ) / 100000 < (12933 : ℚ) / 10000 := by
  norm_num

theorem qValue_of_window {gap me : ℚ}
    (hg0 : (12933 : ℚ) / 10000 ≤ gap) (hg1 : gap ≤ (12934 : ℚ) / 10000)
    (he0 : (51099 : ℚ) / 100000 ≤ me) (he1 : me ≤ (51101 : ℚ) / 100000) :
    (782 : ℚ) / 1000 < gap - me ∧ gap - me < (783 : ℚ) / 1000 := by
  have hlo : (12933 : ℚ) / 10000 - (51101 : ℚ) / 100000 ≤ gap - me := by linarith
  have hhi : gap - me ≤ (12934 : ℚ) / 10000 - (51099 : ℚ) / 100000 := by linarith
  exact ⟨lt_of_lt_of_le qValue_corners.1 hlo, lt_of_le_of_lt hhi qValue_corners.2⟩

theorem massRatio_of_window {gap me : ℚ}
    (hg0 : (12933 : ℚ) / 10000 ≤ gap) (hg1 : gap ≤ (12934 : ℚ) / 10000)
    (he0 : (51099 : ℚ) / 100000 ≤ me) (he1 : me ≤ (51101 : ℚ) / 100000) :
    (5 : ℚ) / 2 < gap / me ∧ gap / me < (38 : ℚ) / 15 := by
  have hme : 0 < me := by
    have : (0 : ℚ) < (51099 : ℚ) / 100000 := by norm_num
    linarith
  have hmeHi : 0 < (51101 : ℚ) / 100000 := by norm_num
  have hmeLo : 0 < (51099 : ℚ) / 100000 := by norm_num
  have hgap : 0 < gap := by
    have : (0 : ℚ) < (12933 : ℚ) / 10000 := by norm_num
    linarith
  have hlo : ((12933 : ℚ) / 10000) / ((51101 : ℚ) / 100000) ≤ gap / me := by
    have h1 : ((12933 : ℚ) / 10000) / me ≤ gap / me := by
      rw [div_le_div_iff₀ hme hme]
      nlinarith
    have h2 : ((12933 : ℚ) / 10000) / ((51101 : ℚ) / 100000) ≤
        ((12933 : ℚ) / 10000) / me := by
      rw [div_le_div_iff₀ hmeHi hme]
      nlinarith
    linarith
  have hhi : gap / me ≤ ((12934 : ℚ) / 10000) / ((51099 : ℚ) / 100000) := by
    have h1 : gap / me ≤ ((12934 : ℚ) / 10000) / me := by
      rw [div_le_div_iff₀ hme hme]
      nlinarith
    have h2 : ((12934 : ℚ) / 10000) / me ≤
        ((12934 : ℚ) / 10000) / ((51099 : ℚ) / 100000) := by
      rw [div_le_div_iff₀ hme hmeLo]
      nlinarith
    linarith
  exact ⟨lt_of_lt_of_le massRatio_corners.1 hlo, lt_of_le_of_lt hhi massRatio_corners.2⟩

theorem free_replacement_open {gap me : ℚ}
    (hg0 : (12933 : ℚ) / 10000 ≤ gap) (he1 : me ≤ (51101 : ℚ) / 100000) :
    me < gap := by
  linarith [gap_above_electron]

theorem freeGap_lt_coulomb_at_reversal {r₁ gap : ℝ}
    (hr0 : 0 < r₁) (hr1 : r₁ < 1) (hgap : gap ≤ ((12934 : ℝ) / 10000)) :
    gap < (coulombMeVFm : ℝ) / r₁ := by
  have h := coulomb_at_reversal hr0 hr1
  have hlt : ((12934 : ℝ) / 10000) < (1294 : ℝ) / 1000 := by norm_num
  linarith

/-! ### The lifetime is not the inverse time of the gap -/

theorem hbar_over_c_lt :
    (198 : ℚ) / (((299 : ℚ) / 100) * 10 ^ 23) < ((663 : ℚ) / 100) / 10 ^ 22 := by
  norm_num

theorem compton_time_lt :
    (((663 : ℚ) / 100) / 10 ^ 22) / ((1293 : ℚ) / 1000) < (6 : ℚ) / 10 ^ 22 := by
  norm_num

theorem lifetime_over_compton :
    (10 : ℚ) ^ 24 < 870 / ((6 : ℚ) / 10 ^ 22) := by
  norm_num

theorem gap_above_1293 :
    (1293 : ℚ) / 1000 < (12933 : ℚ) / 10000 := by
  norm_num

theorem compton_time_of_bounds {ℏ gap : ℚ}
    (hℏ : ℏ < ((663 : ℚ) / 100) / 10 ^ 22) (hgap : (1293 : ℚ) / 1000 < gap) :
    ℏ / gap < (6 : ℚ) / 10 ^ 22 := by
  have hpos : 0 < gap := by
    have : (0 : ℚ) < (1293 : ℚ) / 1000 := by norm_num
    linarith
  have hstep : ℏ / gap < (((663 : ℚ) / 100) / 10 ^ 22) / ((1293 : ℚ) / 1000) := by
    have h1 : ℏ / gap < (((663 : ℚ) / 100) / 10 ^ 22) / gap := by
      rw [div_lt_div_iff₀ hpos hpos]
      nlinarith
    have h2 : (((663 : ℚ) / 100) / 10 ^ 22) / gap <
        (((663 : ℚ) / 100) / 10 ^ 22) / ((1293 : ℚ) / 1000) := by
      rw [div_lt_div_iff₀ hpos (by norm_num)]
      nlinarith
    linarith
  linarith [compton_time_lt]

theorem lifetime_ratio_of_bounds {τ t : ℚ}
    (hτ : 870 ≤ τ) (ht0 : 0 < t) (ht : t < (6 : ℚ) / 10 ^ 22) :
    10 ^ 24 < τ / t := by
  have htpos : 0 < (6 : ℚ) / 10 ^ 22 := by norm_num
  have h1 : 870 / ((6 : ℚ) / 10 ^ 22) < 870 / t := by
    rw [div_lt_div_iff₀ htpos ht0]
    nlinarith
  have h2 : 870 / t ≤ τ / t := by
    rw [div_le_div_iff₀ ht0 ht0]
    nlinarith
  linarith [lifetime_over_compton]

theorem speed_fm_above_paper :
    ((299 : ℚ) / 100) * 10 ^ 23 < (speedOfLightNat : ℚ) * 10 ^ 15 := by
  unfold speedOfLightNat
  norm_num

theorem si_hbar_meets_paper_bound :
    hbarC_MeVfm / ((speedOfLightNat : ℚ) * 10 ^ 15) < ((663 : ℚ) / 100) / 10 ^ 22 := by
  have hc := hbarC_MeVfm_bounds.2
  have hv := speed_fm_above_paper
  have hcpos : (0 : ℚ) < hbarC_MeVfm := lt_trans (by norm_num) hbarC_MeVfm_bounds.1
  have hvpos : (0 : ℚ) < (speedOfLightNat : ℚ) * 10 ^ 15 := by
    have : (0 : ℚ) < ((299 : ℚ) / 100) * 10 ^ 23 := by norm_num
    linarith
  have hden : (0 : ℚ) < ((299 : ℚ) / 100) * 10 ^ 23 := by norm_num
  have h1 : hbarC_MeVfm / ((speedOfLightNat : ℚ) * 10 ^ 15) <
      (198 : ℚ) / ((speedOfLightNat : ℚ) * 10 ^ 15) := by
    rw [div_lt_div_iff₀ hvpos hvpos]
    nlinarith
  have h2 : (198 : ℚ) / ((speedOfLightNat : ℚ) * 10 ^ 15) <
      (198 : ℚ) / (((299 : ℚ) / 100) * 10 ^ 23) := by
    rw [div_lt_div_iff₀ hvpos hden]
    nlinarith
  linarith [hbar_over_c_lt]

end Gravity

end DstDiophantine
