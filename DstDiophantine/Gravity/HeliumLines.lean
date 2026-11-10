import DstDiophantine.Gravity.ElectronCapacity
import DstDiophantine.Gravity.SpectralLines
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Helium lines on the outer plateau

## Paper boundary (do **not** claim)

Nothing here derives a radius from \(\gamma_s=0\). The radius \(a_0/Z\) is
not an input, and a charge-two line is not the proton-shared hydrogen
wavelength divided by four. There is no fine-structure splitting and no
selection rule. The electromagnetic length is the reduced Compton
wavelength. The picometre windows are consequences of the bookkeeping
together with the SI stand-ins.

The three-sphere cosines of `HeliumBody` are not these separations, and
they are not this energy.

## What is proved

* On the diameter the net force is inward throughout the outer well.
  The closure \(pr=n\hbar\) with that force reads
  \(x=(\alpha/(2n^2))\bigl(2/\gamma_s(x)-1/(4\gamma_s(x/2))\bigr)\).
  At \(\gamma_s=1\) the factor is \(7/4\) and the phase is \(7\alpha/(8n^2)\).
* Read at that phase, the two-electron circular energy is within one part
  in ten thousand of \(-49/(8n^2)\) of the hydrogen ionisation. Removing
  one electron, leaving the charge-two ground shell, is within one part
  in two thousand of \(17/8\). The step from diameter shell \(2\) to
  diameter shell \(1\) is within one part in ten thousand of \(147/32\).
* One electron and charge two has circular energy within one part in ten
  thousand of \(-4/n^2\). The steps \(2\to 1\), \(3\to 2\), \(4\to 2\),
  \(5\to 2\), and \(4\to 3\) are \(3\), \(5/9\), \(3/4\), \(21/25\), and
  \(7/36\), each within one part in ten thousand of that fraction.
  With the nucleus fixed their wavelengths are the hydrogen wavelengths of
  the same steps, divided by four. Sharing the helium nucleus, for every
  mass ratio strictly between \(7294\) and \(7295\), places them in the
  windows below, and dividing the proton-shared hydrogen wavelengths by
  four lands strictly above those windows.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

private lemma abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor <;> linarith [neg_abs_le a, neg_abs_le b, le_abs_self a, le_abs_self b]

private lemma abs_sub_le (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add a (-b)
  rw [abs_neg b] at h
  simpa [sub_eq_add_neg] using h

/-! ### Charge two, one electron -/

def ionPhase (n : ℕ) : ℚ :=
  fineStructureApprox / (n : ℚ) ^ 2

theorem ionPhase_mem {n : ℕ} (hn : 0 < n) :
    (ionPhase n : ℝ) ∈ Ioo (0 : ℝ) (1 / 100) := by
  refine ⟨?_, ?_⟩
  · unfold ionPhase
    exact_mod_cast div_pos fineStructureApprox_pos (pow_pos (Nat.cast_pos.mpr hn) 2)
  · have hle : ionPhase n ≤ fineStructureApprox := by
      unfold ionPhase
      have hn1 : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by
        have h1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1) h1 2
      have hden : (0 : ℚ) < (n : ℚ) ^ 2 := by positivity
      rw [div_le_iff₀ hden]
      exact le_mul_of_one_le_right fineStructureApprox_pos.le hn1
    have hα : (fineStructureApprox : ℝ) < 1 / 100 := by
      linarith [fineStructureApprox_lt_73_10000]
    exact lt_of_le_of_lt (by exact_mod_cast hle) hα

noncomputable def ionShell (n : ℕ) : ℝ :=
  (4 / (fineStructureApprox : ℝ)) * circEnergy (ionPhase n)

theorem ionShell_gap {n : ℕ} (hn : 0 < n) :
    |ionShell n + 4 / (n : ℝ) ^ 2| ≤
      (24 / 5) * (fineStructureApprox : ℝ) ^ 2 / (n : ℝ) ^ 6 := by
  have hx := ionPhase_mem hn
  have hgap := circEnergy_coulomb_gap hx
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hxphase : (ionPhase n : ℝ) = (fineStructureApprox : ℝ) / (n : ℝ) ^ 2 := by
    unfold ionPhase
    norm_cast
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hident : ionShell n + 4 / (n : ℝ) ^ 2 =
      (4 / (fineStructureApprox : ℝ)) * (circEnergy (ionPhase n) + (ionPhase n : ℝ)) := by
    unfold ionShell
    rw [hxphase]
    field_simp [hα.ne', hn']
  rw [hident, abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  refine le_trans (mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le) ?_
  rw [hxphase]
  field_simp [hα.ne', hn']
  ring_nf
  exact le_rfl

theorem ionShell_rel {n : ℕ} (hn : 0 < n) :
    |ionShell n + 4 / (n : ℝ) ^ 2| < (1 / 10000) * (4 / (n : ℝ) ^ 2) := by
  have hgap := ionShell_gap hn
  have hα := fineStructureApprox_lt_73_10000
  have hα0 : (0 : ℝ) ≤ (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos.le
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα hα0 (by norm_num)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hconst : (24 / 5) * ((73 : ℝ) / 10000) ^ 2 < 4 / 10000 := by norm_num
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 6 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ)) 4
      simpa using this
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (n : ℝ))
    simpa [pow_succ, pow_mul, mul_assoc, mul_left_comm, mul_comm] using this
  have hden : (0 : ℝ) < (n : ℝ) ^ 6 := by positivity
  calc |ionShell n + 4 / (n : ℝ) ^ 2|
      ≤ (24 / 5) * (fineStructureApprox : ℝ) ^ 2 / (n : ℝ) ^ 6 := hgap
    _ < (24 / 5) * ((73 : ℝ) / 10000) ^ 2 / (n : ℝ) ^ 6 := by
        gcongr
    _ ≤ (24 / 5) * ((73 : ℝ) / 10000) ^ 2 / (n : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (pow_pos hn' 2) hpow
    _ < (4 / 10000) / (n : ℝ) ^ 2 := by
        exact div_lt_div_of_pos_right hconst (pow_pos hn' 2)
    _ = (1 / 10000) * (4 / (n : ℝ) ^ 2) := by ring

/-- The closure \(x\gamma_s(x)=\alpha/n^2\) has one root in `(0, 1/100)`. -/
theorem exists_unique_ionClosure {n : ℕ} (hn : 0 < n) :
    ∃! x : ℝ, x ∈ Ioo (0 : ℝ) (1 / 100) ∧ phaseWeight x = (ionPhase n : ℝ) := by
  have hα : (fineStructureApprox : ℝ) < 73 / 10000 := fineStructureApprox_lt_73_10000
  have hdep := gammaDepart_le (x := 1 / 100) (by norm_num) (by norm_num)
  have hγ : (99989 / 100000 : ℝ) ≤ gammaSEqual (1 / 100) := by
    have hcalc : (1 : ℝ) - (11 / 10) * (1 / 100) ^ 2 = 99989 / 100000 := by norm_num
    linarith
  have hweight : (73 / 10000 : ℝ) < phaseWeight (1 / 100) := by
    unfold phaseWeight
    have hmul : (73 / 10000 : ℝ) < (1 / 100) * (99989 / 100000) := by norm_num
    exact lt_of_lt_of_le hmul (mul_le_mul_of_nonneg_left hγ (by norm_num))
  have hc : (ionPhase n : ℝ) < phaseWeight (1 / 100) := by
    have hle : (ionPhase n : ℝ) ≤ (fineStructureApprox : ℝ) := by
      have h := ionPhase_mem hn
      have hcast : (ionPhase n : ℝ) = (fineStructureApprox : ℝ) / (n : ℝ) ^ 2 := by
        unfold ionPhase; norm_cast
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h1 2
      rw [hcast]
      exact div_le_self (by exact_mod_cast fineStructureApprox_pos.le) hn1
    exact lt_of_le_of_lt hle (lt_trans hα hweight)
  have hc0 : 0 < (ionPhase n : ℝ) := (ionPhase_mem hn).1
  have hmem : (ionPhase n : ℝ) ∈ Ioo (phaseWeight 0) (phaseWeight (1 / 100)) := by
    refine ⟨?_, hc⟩
    simpa [phaseWeight_zero] using hc0
  obtain ⟨x, hx, hxeq⟩ :=
    intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 100)
      continuous_phaseWeight.continuousOn hmem
  refine ⟨x, ⟨hx, hxeq⟩, ?_⟩
  intro y hy
  have hxI : x ∈ Icc (0 : ℝ) (1 / 2) := ⟨hx.1.le, by linarith [hx.2]⟩
  have hyI : y ∈ Icc (0 : ℝ) (1 / 2) := ⟨hy.1.1.le, by linarith [hy.1.2]⟩
  exact (phaseWeight_strictMono_to_half.injOn hxI hyI (hxeq.trans hy.2.symm)).symm

theorem ionClosure_restoring {n : ℕ} (_hn : 0 < n) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (1 / 100)) :
    0 < circStable x ∧ x ≠ resonanceRoot1 := by
  have hwell : x ∈ Ioo (0 : ℝ) resonanceRoot1 := by
    refine ⟨hx.1, ?_⟩
    exact lt_trans hx.2 <| lt_trans (by linarith [pi_gt_three] : (1 / 100 : ℝ) < π / 4)
      resonanceRoot1_sharp_bounds.1
  obtain ⟨y, hy, _⟩ := exists_unique_circStable
  have hsign := circStable_outer_sign hwell hy.1 hy.2
  have hlt : x < y := by linarith [hx.2, hy.1.1]
  refine ⟨hsign.1.mpr hlt, ?_⟩
  intro h
  exact (ne_of_lt hwell.2) h

/-! ### The diameter -/

theorem diameterFactor_eq {x : ℝ}
    (hγ : gammaSEqual x ≠ 0) (hh : gammaSEqual (x / 2) ≠ 0) :
    -diameterOutward 2 x =
      2 / gammaSEqual x - 1 / (4 * gammaSEqual (x / 2)) := by
  unfold diameterOutward
  field_simp [hγ, hh]
  ring

theorem diameterFactor_at_zero : -diameterOutward 2 0 = 7 / 4 := by
  unfold diameterOutward
  simp [gammaSEqual_zero]
  norm_num

/-- Throughout the outer well the diameter pushes inward. -/
theorem diameter_inward {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    0 < -diameterOutward 2 x := by
  have hxhalf : x / 2 < x := by linarith [hx.1]
  have hx2 : x / 2 ∈ Ioo (0 : ℝ) resonanceRoot1 :=
    ⟨by linarith [hx.1], lt_trans hxhalf hx.2⟩
  have hγ := gammaSEqual_pos_left_of_first_node hx
  have hγh := gammaSEqual_pos_left_of_first_node hx2
  have hrootπ : resonanceRoot1 < π := by
    linarith [resonanceRoot1_sharp_bounds.2, pi_gt_three]
  have hlt : gammaSEqual x < gammaSEqual (x / 2) :=
    (strictAntiOn_gammaSEqual_even 0)
      (by simpa [Nat.cast_zero, zero_mul] using ⟨hx2.1.le, (lt_trans hx2.2 hrootπ).le⟩)
      (by simpa [Nat.cast_zero, zero_mul] using ⟨hx.1.le, (lt_trans hx.2 hrootπ).le⟩)
      hxhalf
  rw [diameterFactor_eq hγ.ne' hγh.ne', sub_pos]
  rw [div_lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hγh) hγ]
  nlinarith [hγh, hlt]

def diameterPhase (n : ℕ) : ℚ :=
  (7 / 8) * fineStructureApprox / (n : ℚ) ^ 2

theorem diameterPhase_eq {n : ℕ} (_hn : 0 < n) :
    (diameterPhase n : ℝ) =
      (7 / 4) * (fineStructureApprox : ℝ) / (2 * (n : ℝ) ^ 2) := by
  unfold diameterPhase
  push_cast
  ring

theorem diameterPhase_mem {n : ℕ} (hn : 0 < n) :
    (diameterPhase n : ℝ) ∈ Ioo (0 : ℝ) (1 / 100) := by
  have hx := ionPhase_mem hn
  have hrel : (diameterPhase n : ℝ) = (7 / 8) * (ionPhase n : ℝ) := by
    unfold diameterPhase ionPhase
    push_cast
    ring
  rw [hrel]
  refine ⟨mul_pos (by norm_num) hx.1, ?_⟩
  have h78 : (7 / 8 : ℝ) * (1 / 100) < 1 / 100 := by norm_num
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hx.2 (by norm_num)) (by norm_num)

noncomputable def diameterCircular (x : ℝ) : ℝ :=
  2 * x * (-diameterOutward 2 x) - 8 * layerAccum x + 2 * layerAccum (x / 2)

theorem diameterCircular_split {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 100)) :
    diameterCircular x + (7 / 2) * x =
      4 * (circEnergy x + x) - (circEnergy (x / 2) + x / 2) := by
  have hx2 : x / 2 ∈ Ioo (0 : ℝ) resonanceRoot1 := by
    refine ⟨by linarith [hx.1], ?_⟩
    exact lt_trans (by linarith [hx.2]) <|
      lt_trans (by linarith [pi_gt_three] : (1 / 100 : ℝ) < π / 4) resonanceRoot1_sharp_bounds.1
  have hx1 : x ∈ Ioo (0 : ℝ) resonanceRoot1 :=
    ⟨hx.1, lt_trans hx.2 <| lt_trans (by linarith [pi_gt_three] : (1 / 100 : ℝ) < π / 4)
      resonanceRoot1_sharp_bounds.1⟩
  have hγ := gammaSEqual_pos_left_of_first_node hx1
  have hγh := gammaSEqual_pos_left_of_first_node hx2
  unfold diameterCircular circEnergy
  rw [diameterFactor_eq hγ.ne' hγh.ne']
  field_simp [hγ.ne', hγh.ne']
  ring

theorem diameterCircular_gap {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 100)) :
    |diameterCircular x + (7 / 2) * x| ≤ (99 / 20) * x ^ 3 := by
  have hy : x / 2 ∈ Ioo (0 : ℝ) (1 / 100) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [diameterCircular_split hx]
  have habs : |4 * (circEnergy x + x) - (circEnergy (x / 2) + x / 2)| ≤
      4 * |circEnergy x + x| + |circEnergy (x / 2) + x / 2| := by
    calc |4 * (circEnergy x + x) - (circEnergy (x / 2) + x / 2)|
        ≤ |4 * (circEnergy x + x)| + |circEnergy (x / 2) + x / 2| :=
          abs_sub_le _ _
      _ = 4 * |circEnergy x + x| + |circEnergy (x / 2) + x / 2| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h4 := circEnergy_coulomb_gap hx
  have h2 := circEnergy_coulomb_gap hy
  have hbound : 4 * |circEnergy x + x| + |circEnergy (x / 2) + x / 2| ≤
      (99 / 20) * x ^ 3 := by
    have hy3 : (x / 2) ^ 3 = x ^ 3 / 8 := by ring
    calc 4 * |circEnergy x + x| + |circEnergy (x / 2) + x / 2|
        ≤ 4 * ((6 / 5) * x ^ 3) + (6 / 5) * (x / 2) ^ 3 := by
          gcongr
      _ = (99 / 20) * x ^ 3 := by rw [hy3]; ring
  exact le_trans habs hbound

noncomputable def diameterShell (n : ℕ) : ℝ :=
  (2 / (fineStructureApprox : ℝ)) * diameterCircular (diameterPhase n)

theorem diameterShell_gap {n : ℕ} (hn : 0 < n) :
    |diameterShell n + 49 / (8 * (n : ℝ) ^ 2)| ≤
      (33957 / 5120) * (fineStructureApprox : ℝ) ^ 2 / (n : ℝ) ^ 6 := by
  have hx := diameterPhase_mem hn
  have hgap := diameterCircular_gap hx
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hxphase := diameterPhase_eq hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hident : diameterShell n + 49 / (8 * (n : ℝ) ^ 2) =
      (2 / (fineStructureApprox : ℝ)) *
        (diameterCircular (diameterPhase n) + (7 / 2) * (diameterPhase n : ℝ)) := by
    unfold diameterShell
    rw [hxphase]
    field_simp [hα.ne', hn']
    ring
  rw [hident, abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  refine le_trans (mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le) ?_
  rw [hxphase]
  field_simp [hα.ne', hn']
  ring_nf
  exact le_rfl

theorem diameterShell_rel {n : ℕ} (hn : 0 < n) :
    |diameterShell n + 49 / (8 * (n : ℝ) ^ 2)| <
      (1 / 10000) * (49 / (8 * (n : ℝ) ^ 2)) := by
  have hgap := diameterShell_gap hn
  have hα := fineStructureApprox_lt_73_10000
  have hα0 : (0 : ℝ) ≤ (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos.le
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα hα0 (by norm_num)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hconst : (33957 / 5120) * ((73 : ℝ) / 10000) ^ 2 < 49 / 80000 := by norm_num
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 6 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (by exact_mod_cast hn : (1 : ℝ) ≤ (n : ℝ)) 4
      simpa using this
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (n : ℝ))
    simpa [pow_succ, pow_mul, mul_assoc, mul_left_comm, mul_comm] using this
  calc |diameterShell n + 49 / (8 * (n : ℝ) ^ 2)|
      ≤ (33957 / 5120) * (fineStructureApprox : ℝ) ^ 2 / (n : ℝ) ^ 6 := hgap
    _ < (33957 / 5120) * ((73 : ℝ) / 10000) ^ 2 / (n : ℝ) ^ 6 := by gcongr
    _ ≤ (33957 / 5120) * ((73 : ℝ) / 10000) ^ 2 / (n : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (pow_pos hn' 2) hpow
    _ < (49 / 80000) / (n : ℝ) ^ 2 := by
        exact div_lt_div_of_pos_right hconst (pow_pos hn' 2)
    _ = (1 / 10000) * (49 / (8 * (n : ℝ) ^ 2)) := by ring

/-! ### Bookkeeping differences -/

noncomputable def lineBook (a b : ℕ) : ℝ :=
  ((a : ℝ) / (b : ℝ)) * (hydrogenIonisationApprox : ℝ)

theorem lineBook_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < lineBook a b := by
  unfold lineBook
  exact mul_pos (div_pos (by exact_mod_cast ha) (by exact_mod_cast hb))
    (by exact_mod_cast hydrogenIonisationApprox_pos)

private theorem vacuum_scale {E k : ℝ} (hE : E ≠ 0) (hk : k ≠ 0) :
    vacuumWavelength (k * E) = vacuumWavelength E / k := by
  unfold vacuumWavelength
  field_simp [hE, hk]

theorem lineBook_ion_two_one : lineBook 3 1 = 4 * bohrEnergyDiff 1 2 := by
  unfold lineBook
  rw [bohrEnergyDiff_lymanAlpha]
  norm_num
  ring

theorem lineBook_ion_three_two : lineBook 5 9 = 4 * bohrEnergyDiff 2 3 := by
  unfold lineBook
  rw [bohrEnergyDiff_hAlpha]
  norm_num
  ring

theorem lineBook_ion_four_two : lineBook 3 4 = 4 * bohrEnergyDiff 2 4 := by
  unfold lineBook
  rw [bohrEnergyDiff_hBeta]
  norm_num
  ring

theorem lineBook_ion_five_two : lineBook 21 25 = 4 * bohrEnergyDiff 2 5 := by
  unfold lineBook
  rw [bohrEnergyDiff_hGamma]
  norm_num
  ring

theorem lineBook_ion_four_three : lineBook 7 36 = 4 * bohrEnergyDiff 3 4 := by
  unfold lineBook
  rw [bohrEnergyDiff_paschenAlpha]
  norm_num
  ring

theorem lineBook_removal : lineBook 17 8 = (17 / 6) * bohrEnergyDiff 1 2 := by
  unfold lineBook
  rw [bohrEnergyDiff_lymanAlpha]
  norm_num
  ring

theorem lineBook_diameter_step : lineBook 147 32 = (49 / 8) * bohrEnergyDiff 1 2 := by
  unfold lineBook
  rw [bohrEnergyDiff_lymanAlpha]
  norm_num
  ring

private theorem hydrogen_pos (n m : ℕ) (hn : 0 < n) (hm : m > n) :
    bohrEnergyDiff n m ≠ 0 := by
  unfold bohrEnergyDiff
  have hdiff : (1 : ℝ) / (n : ℝ) ^ 2 - 1 / (m : ℝ) ^ 2 ≠ 0 := by
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.lt_trans hn hm)
    have hlt : (n : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hsq : (n : ℝ) ^ 2 < (m : ℝ) ^ 2 := by
      exact pow_lt_pow_left₀ hlt (by exact_mod_cast hn.le) (by norm_num)
    have hinv : 1 / (m : ℝ) ^ 2 < 1 / (n : ℝ) ^ 2 := by
      exact one_div_lt_one_div_of_lt (pow_pos hn' 2) hsq
    linarith
  exact mul_ne_zero (by exact_mod_cast hydrogenIonisationApprox_pos.ne') hdiff

theorem ionWavelength_two_one :
    vacuumWavelength (lineBook 3 1) = vacuumWavelength (bohrEnergyDiff 1 2) / 4 := by
  rw [lineBook_ion_two_one, vacuum_scale]
  · exact hydrogen_pos 1 2 (by norm_num) (by norm_num)
  · norm_num

theorem ionWavelength_three_two :
    vacuumWavelength (lineBook 5 9) = vacuumWavelength (bohrEnergyDiff 2 3) / 4 := by
  rw [lineBook_ion_three_two, vacuum_scale]
  · exact hydrogen_pos 2 3 (by norm_num) (by norm_num)
  · norm_num

theorem ionWavelength_four_two :
    vacuumWavelength (lineBook 3 4) = vacuumWavelength (bohrEnergyDiff 2 4) / 4 := by
  rw [lineBook_ion_four_two, vacuum_scale]
  · exact hydrogen_pos 2 4 (by norm_num) (by norm_num)
  · norm_num

theorem ionWavelength_five_two :
    vacuumWavelength (lineBook 21 25) = vacuumWavelength (bohrEnergyDiff 2 5) / 4 := by
  rw [lineBook_ion_five_two, vacuum_scale]
  · exact hydrogen_pos 2 5 (by norm_num) (by norm_num)
  · norm_num

theorem ionWavelength_four_three :
    vacuumWavelength (lineBook 7 36) = vacuumWavelength (bohrEnergyDiff 3 4) / 4 := by
  rw [lineBook_ion_four_three, vacuum_scale]
  · exact hydrogen_pos 3 4 (by norm_num) (by norm_num)
  · norm_num

theorem removalWavelength_of_lyman :
    vacuumWavelength (lineBook 17 8) = vacuumWavelength (bohrEnergyDiff 1 2) * (6 / 17) := by
  have hE := hydrogen_pos 1 2 (by norm_num) (by norm_num)
  rw [lineBook_removal]
  unfold vacuumWavelength
  field_simp [hE]

theorem diameterWavelength_of_lyman :
    vacuumWavelength (lineBook 147 32) =
      vacuumWavelength (bohrEnergyDiff 1 2) * (8 / 49) := by
  have hE := hydrogen_pos 1 2 (by norm_num) (by norm_num)
  rw [lineBook_diameter_step]
  unfold vacuumWavelength
  field_simp [hE]

theorem alphaMassRatio_lengthens {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (7296 : ℝ) / 7295 < (ρ + 1) / ρ ∧ (ρ + 1) / ρ < (7295 : ℝ) / 7294 := by
  have hρ : 0 < ρ := by linarith
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) hρ]
    linarith
  · rw [div_lt_div_iff₀ hρ (by norm_num)]
    linarith

theorem ionFixed_two_one :
    (30375 : ℝ) / 10 ^ 12 < vacuumWavelength (lineBook 3 1) ∧
      vacuumWavelength (lineBook 3 1) < (30376 : ℝ) / 10 ^ 12 := by
  rw [ionWavelength_two_one]
  obtain ⟨hlo, hhi⟩ := lymanWavelength_bounds
  constructor
  · have h : (30375 : ℝ) / 10 ^ 12 < ((121502 : ℝ) / 10 ^ 12) / 4 := by norm_num
    exact lt_trans h ((div_lt_div_of_pos_right hlo (by norm_num)))
  · have h : ((121503 : ℝ) / 10 ^ 12) / 4 < (30376 : ℝ) / 10 ^ 12 := by norm_num
    exact lt_trans (div_lt_div_of_pos_right hhi (by norm_num)) h

theorem ionFixed_three_two :
    (164028 : ℝ) / 10 ^ 12 < vacuumWavelength (lineBook 5 9) ∧
      vacuumWavelength (lineBook 5 9) < (164029 : ℝ) / 10 ^ 12 := by
  have heq : vacuumWavelength (bohrEnergyDiff 2 3) = hAlphaWavelength := by
    symm
    simpa [vacuumWavelength] using hAlphaWavelength_eq_photon
  rw [ionWavelength_three_two, heq]
  obtain ⟨hlo, hhi⟩ := hAlphaWavelength_bounds
  constructor
  · have heq : (164028 : ℝ) / 10 ^ 12 = ((656112 : ℝ) / 10 ^ 12) / 4 := by norm_num
    rw [heq]
    exact div_lt_div_of_pos_right hlo (by norm_num)
  · have h : ((656113 : ℝ) / 10 ^ 12) / 4 < (164029 : ℝ) / 10 ^ 12 := by norm_num
    exact lt_trans (div_lt_div_of_pos_right hhi (by norm_num)) h

theorem ionFixed_four_two :
    (121502 : ℝ) / 10 ^ 12 < vacuumWavelength (lineBook 3 4) ∧
      vacuumWavelength (lineBook 3 4) < (121503 : ℝ) / 10 ^ 12 := by
  rw [ionWavelength_four_two]
  obtain ⟨hlo, hhi⟩ := hBetaWavelength_bounds
  constructor
  · have h : (121502 : ℝ) / 10 ^ 12 < ((486009 : ℝ) / 10 ^ 12) / 4 := by norm_num
    exact lt_trans h (div_lt_div_of_pos_right hlo (by norm_num))
  · have h : ((486010 : ℝ) / 10 ^ 12) / 4 < (121503 : ℝ) / 10 ^ 12 := by norm_num
    exact lt_trans (div_lt_div_of_pos_right hhi (by norm_num)) h

theorem ionFixed_five_two :
    (108484 : ℝ) / 10 ^ 12 < vacuumWavelength (lineBook 21 25) ∧
      vacuumWavelength (lineBook 21 25) < (108485 : ℝ) / 10 ^ 12 := by
  rw [ionWavelength_five_two]
  obtain ⟨hlo, hhi⟩ := hGammaWavelength_bounds
  constructor
  · have heq : (108484 : ℝ) / 10 ^ 12 = ((433936 : ℝ) / 10 ^ 12) / 4 := by norm_num
    rw [heq]
    exact div_lt_div_of_pos_right hlo (by norm_num)
  · have h : ((433937 : ℝ) / 10 ^ 12) / 4 < (108485 : ℝ) / 10 ^ 12 := by norm_num
    exact lt_trans (div_lt_div_of_pos_right hhi (by norm_num)) h

theorem ionFixed_four_three :
    (468651 : ℝ) / 10 ^ 12 < vacuumWavelength (lineBook 7 36) ∧
      vacuumWavelength (lineBook 7 36) < (468652 : ℝ) / 10 ^ 12 := by
  rw [ionWavelength_four_three]
  obtain ⟨hlo, hhi⟩ := paschenWavelength_bounds
  constructor
  · have h : (468651 : ℝ) / 10 ^ 12 < ((1874606 : ℝ) / 10 ^ 12) / 4 := by norm_num
    exact lt_trans h (div_lt_div_of_pos_right hlo (by norm_num))
  · have h : ((1874607 : ℝ) / 10 ^ 12) / 4 < (468652 : ℝ) / 10 ^ 12 := by norm_num
    exact lt_trans (div_lt_div_of_pos_right hhi (by norm_num)) h

theorem diameterFixed_step :
    (19837 : ℝ) / 10 ^ 12 < vacuumWavelength (lineBook 147 32) ∧
      vacuumWavelength (lineBook 147 32) < (19838 : ℝ) / 10 ^ 12 := by
  rw [diameterWavelength_of_lyman]
  obtain ⟨hlo, hhi⟩ := lymanWavelength_bounds
  constructor
  · have hnum : (19837 : ℝ) / 10 ^ 12 < ((121502 : ℝ) / 10 ^ 12) * (8 / 49) := by norm_num
    exact lt_trans hnum (mul_lt_mul_of_pos_right hlo (by norm_num))
  · have hnum : ((121503 : ℝ) / 10 ^ 12) * (8 / 49) < (19838 : ℝ) / 10 ^ 12 := by norm_num
    exact lt_trans (mul_lt_mul_of_pos_right hhi (by norm_num)) hnum

theorem removalFixed :
    (42883 : ℝ) / 10 ^ 12 < vacuumWavelength (lineBook 17 8) ∧
      vacuumWavelength (lineBook 17 8) < (42884 : ℝ) / 10 ^ 12 := by
  rw [removalWavelength_of_lyman]
  obtain ⟨hlo, hhi⟩ := lymanWavelength_bounds
  constructor
  · have hnum : (42883 : ℝ) / 10 ^ 12 < ((121502 : ℝ) / 10 ^ 12) * (6 / 17) := by norm_num
    exact lt_trans hnum (mul_lt_mul_of_pos_right hlo (by norm_num))
  · have hnum : ((121503 : ℝ) / 10 ^ 12) * (6 / 17) < (42884 : ℝ) / 10 ^ 12 := by norm_num
    exact lt_trans (mul_lt_mul_of_pos_right hhi (by norm_num)) hnum

theorem ionShared_two_one {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (30379 : ℝ) / 10 ^ 12 <
        vacuumWavelength (lineBook 3 1) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (lineBook 3 1) * ((ρ + 1) / ρ) <
        (30380 : ℝ) / 10 ^ 12 := by
  rw [ionWavelength_two_one]
  obtain ⟨hL, hH⟩ := lymanWavelength_bounds
  obtain ⟨hflo, hfhi⟩ := alphaMassRatio_lengthens hlo hhi
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hlam : 0 < vacuumWavelength (bohrEnergyDiff 1 2) / 4 :=
    div_pos (lt_trans (by norm_num) hL) h4
  constructor
  · have hbase : ((121502 : ℝ) / 10 ^ 12) / 4 * (7296 / 7295) >
        (30379 : ℝ) / 10 ^ 12 := by norm_num
    have hdiv : ((121502 : ℝ) / 10 ^ 12) / 4 <
        vacuumWavelength (bohrEnergyDiff 1 2) / 4 :=
      div_lt_div_of_pos_right hL h4
    have hmul : ((121502 : ℝ) / 10 ^ 12) / 4 * (7296 / 7295) <
        (vacuumWavelength (bohrEnergyDiff 1 2) / 4) * ((ρ + 1) / ρ) := by
      have h1 : ((121502 : ℝ) / 10 ^ 12) / 4 * (7296 / 7295) <
          (vacuumWavelength (bohrEnergyDiff 1 2) / 4) * (7296 / 7295) :=
        mul_lt_mul_of_pos_right hdiv (by norm_num)
      have h2 : (vacuumWavelength (bohrEnergyDiff 1 2) / 4) * (7296 / 7295) <
          (vacuumWavelength (bohrEnergyDiff 1 2) / 4) * ((ρ + 1) / ρ) :=
        mul_lt_mul_of_pos_left hflo hlam
      exact lt_trans h1 h2
    linarith
  · have hbase : ((121503 : ℝ) / 10 ^ 12) / 4 * (7295 / 7294) <
        (30380 : ℝ) / 10 ^ 12 := by norm_num
    have hdiv : vacuumWavelength (bohrEnergyDiff 1 2) / 4 <
        ((121503 : ℝ) / 10 ^ 12) / 4 :=
      div_lt_div_of_pos_right hH h4
    have hmul : (vacuumWavelength (bohrEnergyDiff 1 2) / 4) * ((ρ + 1) / ρ) <
        ((121503 : ℝ) / 10 ^ 12) / 4 * (7295 / 7294) := by
      have h1 : (vacuumWavelength (bohrEnergyDiff 1 2) / 4) * ((ρ + 1) / ρ) <
          (vacuumWavelength (bohrEnergyDiff 1 2) / 4) * (7295 / 7294) :=
        mul_lt_mul_of_pos_left hfhi hlam
      have h2 : (vacuumWavelength (bohrEnergyDiff 1 2) / 4) * (7295 / 7294) <
          ((121503 : ℝ) / 10 ^ 12) / 4 * (7295 / 7294) :=
        mul_lt_mul_of_pos_right hdiv (by norm_num)
      exact lt_trans h1 h2
    linarith

theorem ionShared_three_two {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (164050 : ℝ) / 10 ^ 12 <
        vacuumWavelength (lineBook 5 9) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (lineBook 5 9) * ((ρ + 1) / ρ) <
        (164051 : ℝ) / 10 ^ 12 := by
  have heq : vacuumWavelength (bohrEnergyDiff 2 3) = hAlphaWavelength := by
    symm
    simpa [vacuumWavelength] using hAlphaWavelength_eq_photon
  rw [ionWavelength_three_two, heq]
  obtain ⟨hL, hH⟩ := hAlphaWavelength_bounds
  obtain ⟨hflo, hfhi⟩ := alphaMassRatio_lengthens hlo hhi
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hlam : 0 < hAlphaWavelength / 4 := div_pos (lt_trans (by norm_num) hL) h4
  constructor
  · have hbase : ((656112 : ℝ) / 10 ^ 12) / 4 * (7296 / 7295) >
        (164050 : ℝ) / 10 ^ 12 := by norm_num
    have hdiv : ((656112 : ℝ) / 10 ^ 12) / 4 < hAlphaWavelength / 4 :=
      div_lt_div_of_pos_right hL h4
    have hmul : ((656112 : ℝ) / 10 ^ 12) / 4 * (7296 / 7295) <
        (hAlphaWavelength / 4) * ((ρ + 1) / ρ) := by
      exact lt_trans (mul_lt_mul_of_pos_right hdiv (by norm_num))
        (mul_lt_mul_of_pos_left hflo hlam)
    linarith
  · have hbase : ((656113 : ℝ) / 10 ^ 12) / 4 * (7295 / 7294) <
        (164051 : ℝ) / 10 ^ 12 := by norm_num
    have hdiv : hAlphaWavelength / 4 < ((656113 : ℝ) / 10 ^ 12) / 4 :=
      div_lt_div_of_pos_right hH h4
    have hmul : (hAlphaWavelength / 4) * ((ρ + 1) / ρ) <
        ((656113 : ℝ) / 10 ^ 12) / 4 * (7295 / 7294) := by
      exact lt_trans (mul_lt_mul_of_pos_left hfhi hlam)
        (mul_lt_mul_of_pos_right hdiv (by norm_num))
    linarith

/-! ### Shared windows that the hydrogen bracket does not pin to one picometre -/

private theorem ion_four_two_shared_lo_rat :
    (121518 : ℚ) / 10 ^ 12 < standInWavelength 16 3 piDigitLo * (7296 / 7295) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem ion_four_two_shared_hi_rat :
    standInWavelength 16 3 piDigitHi * (7295 / 7294) < (121519 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem ion_five_two_shared_lo_rat :
    (108499 : ℚ) / 10 ^ 12 < standInWavelength 100 21 piDigitLo * (7296 / 7295) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem ion_five_two_shared_hi_rat :
    standInWavelength 100 21 piDigitHi * (7295 / 7294) < (108500 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem ion_four_three_shared_lo_rat :
    (468715 : ℚ) / 10 ^ 12 < standInWavelength 144 7 piDigitLo * (7296 / 7295) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem ion_four_three_shared_hi_rat :
    standInWavelength 144 7 piDigitHi * (7295 / 7294) < (468716 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem removal_shared_lo_rat :
    (42889 : ℚ) / 10 ^ 12 < standInWavelength 32 17 piDigitLo * (7296 / 7295) := by
  unfold standInWavelength piDigitLo hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem removal_shared_hi_rat :
    standInWavelength 32 17 piDigitHi * (7295 / 7294) < (42890 : ℚ) / 10 ^ 12 := by
  unfold standInWavelength piDigitHi hbarApprox electronMassApprox fineStructureApprox
    speedOfLight hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem ion_four_two_wavelength_eq :
    vacuumWavelength (lineBook 3 4) =
      16 * π * (hbarApprox : ℝ) /
        (3 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength lineBook hydrogenIonisationApprox
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring_nf

private theorem ion_five_two_wavelength_eq :
    vacuumWavelength (lineBook 21 25) =
      100 * π * (hbarApprox : ℝ) /
        (21 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength lineBook hydrogenIonisationApprox
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring_nf

private theorem ion_four_three_wavelength_eq :
    vacuumWavelength (lineBook 7 36) =
      144 * π * (hbarApprox : ℝ) /
        (7 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength lineBook hydrogenIonisationApprox
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring_nf

private theorem removal_wavelength_eq :
    vacuumWavelength (lineBook 17 8) =
      32 * π * (hbarApprox : ℝ) /
        (17 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  unfold vacuumWavelength lineBook hydrogenIonisationApprox
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring_nf

theorem ionShared_four_two {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (121518 : ℝ) / 10 ^ 12 <
        vacuumWavelength (lineBook 3 4) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (lineBook 3 4) * ((ρ + 1) / ρ) <
        (121519 : ℝ) / 10 ^ 12 := by
  rw [ion_four_two_wavelength_eq]
  obtain ⟨hflo, hfhi⟩ := alphaMassRatio_lengthens hlo hhi
  have hfacLo : ((7296 / 7295 : ℚ) : ℝ) < (ρ + 1) / ρ := by
    convert hflo using 1; norm_num
  have hfacHi : (ρ + 1) / ρ < ((7295 / 7294 : ℚ) : ℝ) := by
    convert hfhi using 1; norm_num
  convert ratioFactor_bounds (num := 16) (den := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hfacLo hfacHi
      ion_four_two_shared_lo_rat ion_four_two_shared_hi_rat using 2 <;>
    push_cast <;> ring

theorem ionShared_five_two {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (108499 : ℝ) / 10 ^ 12 <
        vacuumWavelength (lineBook 21 25) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (lineBook 21 25) * ((ρ + 1) / ρ) <
        (108500 : ℝ) / 10 ^ 12 := by
  rw [ion_five_two_wavelength_eq]
  obtain ⟨hflo, hfhi⟩ := alphaMassRatio_lengthens hlo hhi
  have hfacLo : ((7296 / 7295 : ℚ) : ℝ) < (ρ + 1) / ρ := by
    convert hflo using 1; norm_num
  have hfacHi : (ρ + 1) / ρ < ((7295 / 7294 : ℚ) : ℝ) := by
    convert hfhi using 1; norm_num
  convert ratioFactor_bounds (num := 100) (den := 21) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hfacLo hfacHi
      ion_five_two_shared_lo_rat ion_five_two_shared_hi_rat using 2 <;>
    push_cast <;> ring

theorem ionShared_four_three {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (468715 : ℝ) / 10 ^ 12 <
        vacuumWavelength (lineBook 7 36) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (lineBook 7 36) * ((ρ + 1) / ρ) <
        (468716 : ℝ) / 10 ^ 12 := by
  rw [ion_four_three_wavelength_eq]
  obtain ⟨hflo, hfhi⟩ := alphaMassRatio_lengthens hlo hhi
  have hfacLo : ((7296 / 7295 : ℚ) : ℝ) < (ρ + 1) / ρ := by
    convert hflo using 1; norm_num
  have hfacHi : (ρ + 1) / ρ < ((7295 / 7294 : ℚ) : ℝ) := by
    convert hfhi using 1; norm_num
  convert ratioFactor_bounds (num := 144) (den := 7) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hfacLo hfacHi
      ion_four_three_shared_lo_rat ion_four_three_shared_hi_rat using 2 <;>
    push_cast <;> ring

theorem removalShared {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (42889 : ℝ) / 10 ^ 12 <
        vacuumWavelength (lineBook 17 8) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (lineBook 17 8) * ((ρ + 1) / ρ) <
        (42890 : ℝ) / 10 ^ 12 := by
  rw [removal_wavelength_eq]
  obtain ⟨hflo, hfhi⟩ := alphaMassRatio_lengthens hlo hhi
  have hfacLo : ((7296 / 7295 : ℚ) : ℝ) < (ρ + 1) / ρ := by
    convert hflo using 1; norm_num
  have hfacHi : (ρ + 1) / ρ < ((7295 / 7294 : ℚ) : ℝ) := by
    convert hfhi using 1; norm_num
  convert ratioFactor_bounds (num := 32) (den := 17) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hfacLo hfacHi
      removal_shared_lo_rat removal_shared_hi_rat using 2 <;>
    push_cast <;> ring

theorem diameterShared_step {ρ : ℝ} (hlo : (7294 : ℝ) < ρ) (hhi : ρ < 7295) :
    (19839 : ℝ) / 10 ^ 12 <
        vacuumWavelength (lineBook 147 32) * ((ρ + 1) / ρ) ∧
      vacuumWavelength (lineBook 147 32) * ((ρ + 1) / ρ) <
        (19840 : ℝ) / 10 ^ 12 := by
  rw [diameterWavelength_of_lyman]
  obtain ⟨hL, hH⟩ := lymanWavelength_bounds
  obtain ⟨hflo, hfhi⟩ := alphaMassRatio_lengthens hlo hhi
  have hlam : 0 < vacuumWavelength (bohrEnergyDiff 1 2) := lt_trans (by norm_num) hL
  have h8 : (0 : ℝ) < 8 / 49 := by norm_num
  constructor
  · have hbase : ((121502 : ℝ) / 10 ^ 12) * (8 / 49) * (7296 / 7295) >
        (19839 : ℝ) / 10 ^ 12 := by norm_num
    have h1 : ((121502 : ℝ) / 10 ^ 12) * (8 / 49) <
        vacuumWavelength (bohrEnergyDiff 1 2) * (8 / 49) :=
      mul_lt_mul_of_pos_right hL h8
    have h2 : vacuumWavelength (bohrEnergyDiff 1 2) * (8 / 49) * (7296 / 7295) <
        vacuumWavelength (bohrEnergyDiff 1 2) * (8 / 49) * ((ρ + 1) / ρ) :=
      mul_lt_mul_of_pos_left hflo (mul_pos hlam h8)
    have h3 : ((121502 : ℝ) / 10 ^ 12) * (8 / 49) * (7296 / 7295) <
        vacuumWavelength (bohrEnergyDiff 1 2) * (8 / 49) * (7296 / 7295) :=
      mul_lt_mul_of_pos_right h1 (by norm_num)
    linarith
  · have hbase : ((121503 : ℝ) / 10 ^ 12) * (8 / 49) * (7295 / 7294) <
        (19840 : ℝ) / 10 ^ 12 := by norm_num
    have h1 : vacuumWavelength (bohrEnergyDiff 1 2) * (8 / 49) <
        ((121503 : ℝ) / 10 ^ 12) * (8 / 49) :=
      mul_lt_mul_of_pos_right hH h8
    have h2 : vacuumWavelength (bohrEnergyDiff 1 2) * (8 / 49) * ((ρ + 1) / ρ) <
        vacuumWavelength (bohrEnergyDiff 1 2) * (8 / 49) * (7295 / 7294) :=
      mul_lt_mul_of_pos_left hfhi (mul_pos hlam h8)
    have h3 : vacuumWavelength (bohrEnergyDiff 1 2) * (8 / 49) * (7295 / 7294) <
        ((121503 : ℝ) / 10 ^ 12) * (8 / 49) * (7295 / 7294) :=
      mul_lt_mul_of_pos_right h1 (by norm_num)
    linarith

/-! ### The proton-shared line, divided by four, sits above -/

theorem protonShared_above_ion_two_one {ρp ρα : ℝ}
    (hp0 : (1836 : ℝ) < ρp) (hp1 : ρp < 1837)
    (ha0 : (7294 : ℝ) < ρα) (ha1 : ρα < 7295) :
    vacuumWavelength (lineBook 3 1) * ((ρα + 1) / ρα) <
      vacuumWavelength (bohrEnergyDiff 1 2) * ((ρp + 1) / ρp) / 4 := by
  have hhe := (ionShared_two_one ha0 ha1).2
  have hh := (lyman_shared_wavelength hp0 hp1).1
  have hnum : (30380 : ℝ) / 10 ^ 12 < ((121568 : ℝ) / 10 ^ 12) / 4 := by norm_num
  exact lt_trans hhe (lt_trans hnum (div_lt_div_of_pos_right hh (by norm_num)))

theorem protonShared_above_ion_three_two {ρp ρα : ℝ}
    (hp0 : (1836 : ℝ) < ρp) (hp1 : ρp < 1837)
    (ha0 : (7294 : ℝ) < ρα) (ha1 : ρα < 7295) :
    vacuumWavelength (lineBook 5 9) * ((ρα + 1) / ρα) <
      vacuumWavelength (bohrEnergyDiff 2 3) * ((ρp + 1) / ρp) / 4 := by
  have heq : vacuumWavelength (bohrEnergyDiff 2 3) = hAlphaWavelength := by
    symm
    simpa [vacuumWavelength] using hAlphaWavelength_eq_photon
  have hhe := (ionShared_three_two ha0 ha1).2
  have hh := (hAlpha_shared_wavelength hp0 hp1).1
  have hnum : (164051 : ℝ) / 10 ^ 12 < ((656469 : ℝ) / 10 ^ 12) / 4 := by norm_num
  rw [heq]
  exact lt_trans hhe (lt_trans hnum (div_lt_div_of_pos_right hh (by norm_num)))

theorem protonShared_above_ion_four_two {ρp ρα : ℝ}
    (hp0 : (1836 : ℝ) < ρp) (hp1 : ρp < 1837)
    (ha0 : (7294 : ℝ) < ρα) (ha1 : ρα < 7295) :
    vacuumWavelength (lineBook 3 4) * ((ρα + 1) / ρα) <
      vacuumWavelength (bohrEnergyDiff 2 4) * ((ρp + 1) / ρp) / 4 := by
  have hhe := (ionShared_four_two ha0 ha1).2
  have hh := (hBeta_shared_wavelength hp0 hp1).1
  have hnum : (121519 : ℝ) / 10 ^ 12 < ((486273 : ℝ) / 10 ^ 12) / 4 := by norm_num
  have hlam : vacuumWavelength (bohrEnergyDiff 2 4) * ((ρp + 1) / ρp) / 4 >
      ((486273 : ℝ) / 10 ^ 12) / 4 :=
    div_lt_div_of_pos_right hh (by norm_num)
  -- the shared theorem is about vacuumWavelength (bohrEnergyDiff 2 4)
  linarith

theorem protonShared_above_ion_five_two {ρp ρα : ℝ}
    (hp0 : (1836 : ℝ) < ρp) (hp1 : ρp < 1837)
    (ha0 : (7294 : ℝ) < ρα) (ha1 : ρα < 7295) :
    vacuumWavelength (lineBook 21 25) * ((ρα + 1) / ρα) <
      vacuumWavelength (bohrEnergyDiff 2 5) * ((ρp + 1) / ρp) / 4 := by
  have hhe := (ionShared_five_two ha0 ha1).2
  have hh := (hGamma_shared_wavelength hp0 hp1).1
  have hnum : (108500 : ℝ) / 10 ^ 12 < ((434172 : ℝ) / 10 ^ 12) / 4 := by norm_num
  exact lt_trans hhe (lt_trans hnum (div_lt_div_of_pos_right hh (by norm_num)))

theorem protonShared_above_ion_four_three {ρp ρα : ℝ}
    (hp0 : (1836 : ℝ) < ρp) (hp1 : ρp < 1837)
    (ha0 : (7294 : ℝ) < ρα) (ha1 : ρα < 7295) :
    vacuumWavelength (lineBook 7 36) * ((ρα + 1) / ρα) <
      vacuumWavelength (bohrEnergyDiff 3 4) * ((ρp + 1) / ρp) / 4 := by
  have hhe := (ionShared_four_three ha0 ha1).2
  have hh := (paschen_shared_wavelength hp0 hp1).1
  have hnum : (468716 : ℝ) / 10 ^ 12 < ((1875626 : ℝ) / 10 ^ 12) / 4 := by norm_num
  exact lt_trans hhe (lt_trans hnum (div_lt_div_of_pos_right hh (by norm_num)))

/-! ### Steps stay within a ten-thousandth. Removal, within a two-thousandth. -/

theorem ionStep_two_one :
    |ionShell 2 - ionShell 1 - 3| < (1 / 10000) * 3 := by
  have h1 := ionShell_gap (n := 1) (by norm_num)
  simp only [Nat.cast_one, one_pow, div_one] at h1
  have h2 := ionShell_gap (n := 2) (by norm_num)
  have hsplit : ionShell 2 - ionShell 1 - 3 =
      (ionShell 2 + 4 / (2 : ℝ) ^ 2) - (ionShell 1 + 4) := by
    ring
  rw [hsplit]
  have hα := fineStructureApprox_lt_73_10000
  have hα0 : (0 : ℝ) ≤ (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos.le
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα hα0 (by norm_num)
  have hsum : |ionShell 2 + 4 / (2 : ℝ) ^ 2| + |ionShell 1 + 4| <
      (1 / 10000) * 3 := by
    have h2' : |ionShell 2 + 4 / (2 : ℝ) ^ 2| ≤
        (24 / 5) * (fineStructureApprox : ℝ) ^ 2 / (2 : ℝ) ^ 6 := h2
    have hconst : (24 / 5) * ((73 : ℝ) / 10000) ^ 2 * (65 / 64) < (1 / 10000) * 3 := by
      norm_num
    calc |ionShell 2 + 4 / (2 : ℝ) ^ 2| + |ionShell 1 + 4|
        ≤ (24 / 5) * (fineStructureApprox : ℝ) ^ 2 / (2 : ℝ) ^ 6 +
            (24 / 5) * (fineStructureApprox : ℝ) ^ 2 := by linarith [h2', h1]
      _ = (24 / 5) * (fineStructureApprox : ℝ) ^ 2 * (65 / 64) := by ring
      _ < (24 / 5) * ((73 : ℝ) / 10000) ^ 2 * (65 / 64) := by gcongr
      _ < (1 / 10000) * 3 := hconst
  have htri : |ionShell 2 + 4 / (2 : ℝ) ^ 2 - (ionShell 1 + 4)| ≤
      |ionShell 2 + 4 / (2 : ℝ) ^ 2| + |ionShell 1 + 4| :=
    abs_sub_le _ _
  exact lt_of_le_of_lt htri hsum

theorem ionStep_excited :
    |ionShell 3 - ionShell 2 - (5 / 9)| < (1 / 10000) * (5 / 9) ∧
      |ionShell 4 - ionShell 2 - (3 / 4)| < (1 / 10000) * (3 / 4) ∧
      |ionShell 5 - ionShell 2 - (21 / 25)| < (1 / 10000) * (21 / 25) ∧
      |ionShell 4 - ionShell 3 - (7 / 36)| < (1 / 10000) * (7 / 36) := by
  have h2 := ionShell_gap (n := 2) (by norm_num)
  have h3 := ionShell_gap (n := 3) (by norm_num)
  have h4 := ionShell_gap (n := 4) (by norm_num)
  have h5 := ionShell_gap (n := 5) (by norm_num)
  have hα := fineStructureApprox_lt_73_10000
  have hα0 : (0 : ℝ) ≤ (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos.le
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα hα0 (by norm_num)
  have hpair : (24 / 5) * ((73 : ℝ) / 10000) ^ 2 * (2 / 64) <
      (1 / 10000) * (7 / 36) := by norm_num
  have hloose (n : ℕ) (hn : 2 ≤ n) :
      |ionShell n + 4 / (n : ℝ) ^ 2| <
        (24 / 5) * ((73 : ℝ) / 10000) ^ 2 / (2 : ℝ) ^ 6 := by
    have hgap := ionShell_gap (by omega : 0 < n)
    have hn6 : (2 : ℝ) ^ 6 ≤ (n : ℝ) ^ 6 := by
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact pow_le_pow_left₀ (by norm_num) hn2 6
    calc |ionShell n + 4 / (n : ℝ) ^ 2|
        ≤ (24 / 5) * (fineStructureApprox : ℝ) ^ 2 / (n : ℝ) ^ 6 := hgap
      _ < (24 / 5) * ((73 : ℝ) / 10000) ^ 2 / (n : ℝ) ^ 6 := by gcongr
      _ ≤ (24 / 5) * ((73 : ℝ) / 10000) ^ 2 / (2 : ℝ) ^ 6 := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hn6
  have htwo : |ionShell 2 + 1| + |ionShell 3 + 4 / 9| <
      (24 / 5) * ((73 : ℝ) / 10000) ^ 2 * (2 / 64) := by
    have ha := hloose 2 (by norm_num)
    have hb := hloose 3 (by norm_num)
    have h2s : |ionShell 2 + 4 / (2 : ℝ) ^ 2| = |ionShell 2 + 1| := by norm_num
    have h3s : |ionShell 3 + 4 / (3 : ℝ) ^ 2| = |ionShell 3 + 4 / 9| := by norm_num
    linarith
  -- The four differences are each at most the sum of two gaps, and the
  -- smallest fraction among them is `7/36`.
  have hcap : (24 / 5) * ((73 : ℝ) / 10000) ^ 2 * (2 / 64) <
      (1 / 10000) * (7 / 36) := hpair
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsplit : ionShell 3 - ionShell 2 - (5 / 9) =
        (ionShell 3 + 4 / 9) - (ionShell 2 + 1) := by ring
    rw [hsplit]
    have htri : |(ionShell 3 + 4 / 9) - (ionShell 2 + 1)| ≤
        |ionShell 3 + 4 / 9| + |ionShell 2 + 1| :=
      abs_sub_le _ _
    have h59 : (1 / 10000) * (7 / 36) ≤ (1 / 10000) * (5 / 9) := by norm_num
    linarith
  · have hsplit : ionShell 4 - ionShell 2 - (3 / 4) =
        (ionShell 4 + 4 / 16) - (ionShell 2 + 1) := by ring
    rw [hsplit]
    have ha := hloose 4 (by norm_num)
    have hb := hloose 2 (by norm_num)
    have h4s : |ionShell 4 + 4 / (4 : ℝ) ^ 2| = |ionShell 4 + 4 / 16| := by norm_num
    have h2s : |ionShell 2 + 4 / (2 : ℝ) ^ 2| = |ionShell 2 + 1| := by norm_num
    have htri : |(ionShell 4 + 4 / 16) - (ionShell 2 + 1)| ≤
        |ionShell 4 + 4 / 16| + |ionShell 2 + 1| :=
      abs_sub_le _ _
    have hfrac : (1 / 10000) * (7 / 36) ≤ (1 / 10000) * (3 / 4) := by norm_num
    linarith
  · have hsplit : ionShell 5 - ionShell 2 - (21 / 25) =
        (ionShell 5 + 4 / 25) - (ionShell 2 + 1) := by ring
    rw [hsplit]
    have ha := hloose 5 (by norm_num)
    have hb := hloose 2 (by norm_num)
    have h5s : |ionShell 5 + 4 / (5 : ℝ) ^ 2| = |ionShell 5 + 4 / 25| := by norm_num
    have h2s : |ionShell 2 + 4 / (2 : ℝ) ^ 2| = |ionShell 2 + 1| := by norm_num
    have htri : |(ionShell 5 + 4 / 25) - (ionShell 2 + 1)| ≤
        |ionShell 5 + 4 / 25| + |ionShell 2 + 1| :=
      abs_sub_le _ _
    have hfrac : (1 / 10000) * (7 / 36) ≤ (1 / 10000) * (21 / 25) := by norm_num
    linarith
  · have hsplit : ionShell 4 - ionShell 3 - (7 / 36) =
        (ionShell 4 + 4 / 16) - (ionShell 3 + 4 / 9) := by ring
    rw [hsplit]
    have ha := hloose 4 (by norm_num)
    have hb := hloose 3 (by norm_num)
    have h4s : |ionShell 4 + 4 / (4 : ℝ) ^ 2| = |ionShell 4 + 4 / 16| := by norm_num
    have h3s : |ionShell 3 + 4 / (3 : ℝ) ^ 2| = |ionShell 3 + 4 / 9| := by norm_num
    have htri : |(ionShell 4 + 4 / 16) - (ionShell 3 + 4 / 9)| ≤
        |ionShell 4 + 4 / 16| + |ionShell 3 + 4 / 9| :=
      abs_sub_le _ _
    linarith

theorem diameterStep_two_one :
    |diameterShell 2 - diameterShell 1 - (147 / 32)| < (1 / 10000) * (147 / 32) := by
  have h1 := diameterShell_gap (n := 1) (by norm_num)
  have h2 := diameterShell_gap (n := 2) (by norm_num)
  have hsplit : diameterShell 2 - diameterShell 1 - (147 / 32) =
      (diameterShell 2 + 49 / (8 * (2 : ℝ) ^ 2)) -
        (diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2)) := by
    ring
  rw [hsplit]
  have hα := fineStructureApprox_lt_73_10000
  have hα0 : (0 : ℝ) ≤ (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos.le
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα hα0 (by norm_num)
  have hconst : (33957 / 5120) * ((73 : ℝ) / 10000) ^ 2 * (65 / 64) <
      (1 / 10000) * (147 / 32) := by norm_num
  have hsum : |diameterShell 2 + 49 / (8 * (2 : ℝ) ^ 2)| +
      |diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2)| <
      (1 / 10000) * (147 / 32) := by
    calc |diameterShell 2 + 49 / (8 * (2 : ℝ) ^ 2)| +
          |diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2)|
        ≤ (33957 / 5120) * (fineStructureApprox : ℝ) ^ 2 / (2 : ℝ) ^ 6 +
            (33957 / 5120) * (fineStructureApprox : ℝ) ^ 2 / (1 : ℝ) ^ 6 := by
          linarith [h1, h2]
      _ = (33957 / 5120) * (fineStructureApprox : ℝ) ^ 2 * (65 / 64) := by ring
      _ < (33957 / 5120) * ((73 : ℝ) / 10000) ^ 2 * (65 / 64) := by gcongr
      _ < (1 / 10000) * (147 / 32) := hconst
  have htri : |(diameterShell 2 + 49 / (8 * (2 : ℝ) ^ 2)) -
        (diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2))| ≤
      |diameterShell 2 + 49 / (8 * (2 : ℝ) ^ 2)| +
        |diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2)| :=
    abs_sub_le _ _
  exact lt_of_le_of_lt htri hsum

theorem removal_rel :
    |(ionShell 1 - diameterShell 1) - (17 / 8)| < (1 / 2000) * (17 / 8) := by
  have hi := ionShell_gap (n := 1) (by norm_num)
  have hd := diameterShell_gap (n := 1) (by norm_num)
  have hsplit : ionShell 1 - diameterShell 1 - (17 / 8) =
      (ionShell 1 + 4 / (1 : ℝ) ^ 2) -
        (diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2)) := by
    ring
  rw [hsplit]
  have hα := fineStructureApprox_lt_73_10000
  have hα0 : (0 : ℝ) ≤ (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos.le
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα hα0 (by norm_num)
  have hconst : ((24 / 5) + 33957 / 5120) * ((73 : ℝ) / 10000) ^ 2 <
      (1 / 2000) * (17 / 8) := by norm_num
  have hsum : |ionShell 1 + 4 / (1 : ℝ) ^ 2| +
      |diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2)| <
      (1 / 2000) * (17 / 8) := by
    calc |ionShell 1 + 4 / (1 : ℝ) ^ 2| +
          |diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2)|
        ≤ (24 / 5) * (fineStructureApprox : ℝ) ^ 2 / (1 : ℝ) ^ 6 +
            (33957 / 5120) * (fineStructureApprox : ℝ) ^ 2 / (1 : ℝ) ^ 6 := by
          linarith [hi, hd]
      _ = ((24 / 5) + 33957 / 5120) * (fineStructureApprox : ℝ) ^ 2 := by ring
      _ < ((24 / 5) + 33957 / 5120) * ((73 : ℝ) / 10000) ^ 2 := by gcongr
      _ < (1 / 2000) * (17 / 8) := hconst
  have htri : |(ionShell 1 + 4 / (1 : ℝ) ^ 2) -
        (diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2))| ≤
      |ionShell 1 + 4 / (1 : ℝ) ^ 2| +
        |diameterShell 1 + 49 / (8 * (1 : ℝ) ^ 2)| :=
    abs_sub_le _ _
  exact lt_of_le_of_lt htri hsum

end Gravity

end DstDiophantine
