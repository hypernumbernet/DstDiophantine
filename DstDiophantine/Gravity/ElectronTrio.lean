import DstDiophantine.Gravity.ElectronAngle
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Three equal shared pairs

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. No bond angle in degrees and no dissociation
energy is produced. The plane of three shared pairs is an angular equilibrium;
a second-derivative test that it is restored is not claimed. The radius at
which the axial electron rests is not located.

## What is proved

Distances are in units of `ℓ`. The cosine of the angle between two of three
coplanar rays is `-1/2`. That angle lies strictly between the four-pair angle,
of cosine `-1/3`, and a straight angle, and it is greater than a right angle.

* Three electrons at one distance and three protons at one greater distance,
  with the nuclear distances of the electrons and the electron–proton gaps in
  the outer well, exert no tangential force: on each ray the force lies along
  the ray.
* A further electron on the axis, at a positive distance no greater than the
  bonding electrons' distance and itself in the outer well, contributes nothing
  in the plane of the rays. The generalized force that increases the angle from
  that axis is strictly positive, so each ray is driven off the plane to the
  opposite side. The nuclear charge does not enter that sign.
-/

namespace DstDiophantine.Gravity

noncomputable section

open Real Set Finset

/-! ### Three coplanar rays -/

/-- Cosine of the angle between two of three coplanar rays at equal spacing. -/
def triCos : ℝ := -1 / 2

def triU : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 1, 0 => -1 / 2
  | 1, 1 => sqrt 3 / 2
  | 1, 2 => 0
  | 2, 0 => -1 / 2
  | 2, 1 => -(sqrt 3 / 2)
  | 2, 2 => 0

/-- In-plane vector orthogonal to ray `i`. -/
def triPerp (i : Fin 3) : Fin 3 → ℝ
  | 0 => -triU i 1
  | 1 => triU i 0
  | 2 => 0

/-- Unit vector normal to the plane of the three rays. -/
def triZ : Fin 3 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1

/-- A point on the axis through the nucleus, normal to the plane. -/
def triAxis (s : ℝ) : Fin 3 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => s

theorem triCos_lt_tetCos : triCos < tetCos := by
  unfold triCos tetCos
  norm_num

theorem triCos_lt_zero : triCos < 0 := by
  unfold triCos
  norm_num

/-- The three-pair angle lies strictly between the four-pair angle and a
straight angle, and both exceed a right angle. -/
theorem shared_angle_order :
    π / 2 < arccos tetCos ∧ arccos tetCos < arccos triCos ∧ arccos triCos < π := by
  refine ⟨tetAngle_gt_right, ?_, ?_⟩
  · exact arccos_lt_arccos (by unfold triCos; norm_num) triCos_lt_tetCos
      (by unfold tetCos; norm_num)
  · have h : arccos triCos < arccos (-1) :=
      arccos_lt_arccos (by norm_num) (by unfold triCos; norm_num)
        (by unfold triCos; norm_num)
    simpa [arccos_neg_one] using h

lemma triU_z (i : Fin 3) : triU i 2 = 0 := by
  fin_cases i <;> rfl

lemma triU_normSq (i : Fin 3) : vdot (triU i) (triU i) = 1 := by
  fin_cases i
  · simp [vdot, triU]
  · have hsq : (sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, sq_sqrt (by norm_num)]
      norm_num
    simp only [vdot, triU]
    have hmul : (sqrt 3 / 2) * (sqrt 3 / 2) = (sqrt 3 / 2) ^ 2 := by ring
    rw [hmul, hsq]
    norm_num
  · have hsq : (sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, sq_sqrt (by norm_num)]
      norm_num
    simp only [vdot, triU]
    have hmul : (-(sqrt 3 / 2)) * (-(sqrt 3 / 2)) = (sqrt 3 / 2) ^ 2 := by ring
    rw [hmul, hsq]
    norm_num

lemma triU_norm (i : Fin 3) : vnorm (triU i) = 1 := by
  have hsq : vnorm (triU i) ^ 2 = 1 := by
    rw [vnorm_sq]
    unfold vnorm2
    exact triU_normSq i
  have hnn : 0 ≤ vnorm (triU i) := sqrt_nonneg _
  rw [← sqrt_sq hnn, hsq, sqrt_one]

lemma triU_dot {i j : Fin 3} (hij : i ≠ j) : vdot (triU i) (triU j) = triCos := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simp [vdot, triU, triCos]
  · simp [vdot, triU, triCos]
  · simp [vdot, triU, triCos]
  · exact (hij rfl).elim
  · have hsq : (sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, sq_sqrt (by norm_num)]
      norm_num
    simp only [vdot, triU, triCos]
    have hmul : (sqrt 3 / 2) * (-(sqrt 3 / 2)) = -((sqrt 3 / 2) ^ 2) := by ring
    rw [hmul, hsq]
    norm_num
  · simp [vdot, triU, triCos]
  · have hsq : (sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, sq_sqrt (by norm_num)]
      norm_num
    simp only [vdot, triU, triCos]
    have hmul : (-(sqrt 3 / 2)) * (sqrt 3 / 2) = -((sqrt 3 / 2) ^ 2) := by ring
    rw [hmul, hsq]
    norm_num
  · exact (hij rfl).elim

lemma triPerp_dot (i : Fin 3) : vdot (triPerp i) (triU i) = 0 := by
  unfold vdot triPerp
  ring

lemma triZ_dot (i : Fin 3) : vdot triZ (triU i) = 0 := by
  unfold vdot triZ
  simp [triU_z]

lemma sum_triU (k : Fin 3) : ∑ i : Fin 3, triU i k = 0 := by
  fin_cases k
  · simp [Fin.sum_univ_three, triU]; ring
  · simp [Fin.sum_univ_three, triU]
  · simp [Fin.sum_univ_three, triU]

lemma sum_erase_triU (i : Fin 3) (k : Fin 3) :
    ∑ j ∈ Finset.univ.erase i, triU j k = -triU i k := by
  have h := Finset.add_sum_erase Finset.univ (fun j => triU j k) (mem_univ i)
  rw [sum_triU] at h
  linarith

lemma chord_tri_ee {r : ℝ} (hr : 0 ≤ r) : chord r r triCos = r * sqrt 3 := by
  have hsq : chordSq r r triCos = 3 * r ^ 2 := by
    unfold chordSq triCos
    ring
  unfold chord
  rw [hsq, sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), sqrt_sq hr]
  ring

lemma chord_tri_gt {r : ℝ} (hr : 0 < r) : r < chord r r triCos := by
  rw [chord_tri_ee hr.le]
  have hsqrt : (1 : ℝ) < sqrt 3 := by
    rw [← sqrt_one]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

private lemma pairPhase_anti {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    pairPhase b < pairPhase a := by
  unfold pairPhase
  exact div_lt_div_of_pos_left (by norm_num)
    (mul_pos (by norm_num : (0 : ℝ) < 2) ha)
    (mul_lt_mul_of_pos_left hab (by norm_num : (0 : ℝ) < 2))

private lemma outerSep_longer {d s : ℝ} (hd : outerSep d) (hlt : d < s) : outerSep s := by
  refine ⟨lt_trans hd.1 hlt, lt_trans (pairPhase_anti hd.1 hlt) hd.2⟩

lemma outerSep_tri_ee {r : ℝ} (hr : outerSep r) : outerSep (chord r r triCos) :=
  outerSep_longer hr (chord_tri_gt hr.1)

lemma chord_cross_sq {r R : ℝ} : chordSq r R triCos = r ^ 2 + R ^ 2 + r * R := by
  unfold chordSq triCos
  ring

lemma chord_cross_gt {r R : ℝ} (hr : 0 < r) (hR : r < R) : r < chord r R triCos := by
  have hpos : 0 ≤ r ^ 2 := sq_nonneg r
  have hlt : r ^ 2 < chordSq r R triCos := by
    rw [chord_cross_sq]
    have hrest : 0 < R ^ 2 + r * R := by nlinarith
    linarith
  have hsqrt : sqrt (r ^ 2) < sqrt (chordSq r R triCos) := sqrt_lt_sqrt hpos hlt
  rw [sqrt_sq hr.le] at hsqrt
  simpa [chord] using hsqrt

lemma outerSep_cross {r R : ℝ} (hr : outerSep r) (hR : r < R) :
    outerSep (chord r R triCos) :=
  outerSep_longer hr (chord_cross_gt hr.1 hR)

lemma outerSep_of_le {s r : ℝ} (hs : outerSep s) (hsr : s ≤ r) : outerSep r := by
  refine ⟨lt_of_lt_of_le hs.1 hsr, ?_⟩
  have hφ : pairPhase r ≤ pairPhase s := by
    unfold pairPhase
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (mul_pos (by norm_num : (0 : ℝ) < 2) hs.1) (by linarith)
  exact lt_of_le_of_lt hφ hs.2

/-! ### Forces along a ray -/

private lemma vdot_parallel {t u : Fin 3 → ℝ} {c : ℝ} (ht : vdot t u = 0) :
    vdot t (fun k => c * u k) = 0 := by
  have h : vdot t (fun k => c * u k) = c * vdot t u := by
    unfold vdot
    ring
  rw [h, ht, mul_zero]

lemma nucleus_along {q Z ρ : ℝ} (hρ : 0 < ρ) (i : Fin 3) (k : Fin 3) :
    pairForce q Z (vsmul ρ (triU i)) (fun _ => 0) k =
      (q * Z / (gammaSEqual (pairPhase ρ) * ρ ^ 2)) * triU i k := by
  have hsub : vsub (vsmul ρ (triU i)) (fun _ => 0) = vsmul ρ (triU i) := by
    funext t
    simp [vsub]
  have hv : vnorm (vsub (vsmul ρ (triU i)) (fun _ => 0)) = ρ := by
    rw [hsub, vnorm_smul, abs_of_pos hρ, triU_norm, mul_one]
  unfold pairForce
  rw [hv]
  simp only [vsmul]
  have hne : ρ ≠ 0 := hρ.ne'
  field_simp [hne]
  ring

lemma sameRay_along {q₁ q₂ ρ σ : ℝ} (_hρ : 0 < ρ) (_hσ : 0 < σ) (i : Fin 3) (k : Fin 3) :
    pairForce q₁ q₂ (vsmul ρ (triU i)) (vsmul σ (triU i)) k =
      (q₁ * q₂ * (ρ - σ) / (gammaSEqual (pairPhase |ρ - σ|) * |ρ - σ| ^ 3)) *
        triU i k := by
  have hsub : vsub (vsmul ρ (triU i)) (vsmul σ (triU i)) = vsmul (ρ - σ) (triU i) := by
    funext t
    simp [vsub, vsmul]
    ring
  have hv : vnorm (vsub (vsmul ρ (triU i)) (vsmul σ (triU i))) = |ρ - σ| := by
    rw [hsub, vnorm_smul, triU_norm, mul_one]
  unfold pairForce
  rw [hv]
  simp only [vsmul]
  ring

lemma repulsion_sum_along {ρ : ℝ} {i : Fin 3} (hρ : 0 < ρ)
    (hsep : outerSep (chord ρ ρ triCos)) (k : Fin 3) :
    ∑ j ∈ Finset.univ.erase i,
        pairForce 1 1 (vsmul ρ (triU i)) (vsmul ρ (triU j)) k =
      (3 * ρ / (gammaSEqual (pairPhase (chord ρ ρ triCos)) *
        chord ρ ρ triCos ^ 3)) * triU i k := by
  set d : ℝ := chord ρ ρ triCos
  set D : ℝ := gammaSEqual (pairPhase d) * d ^ 3
  have hD : D ≠ 0 :=
    mul_ne_zero (outer_gamma_pos hsep).ne' (pow_ne_zero 3 hsep.1.ne')
  have hterm : ∀ j ∈ Finset.univ.erase i,
      pairForce 1 1 (vsmul ρ (triU i)) (vsmul ρ (triU j)) k =
        ρ * (triU i k - triU j k) / D := by
    intro j hj
    have hij : i ≠ j := (mem_erase.mp hj).1.symm
    have hv := vnorm_unit_chord (triU_normSq i) (triU_normSq j) (triU_dot hij)
      (chordSq_pos_obtuse hρ hρ triCos_lt_zero.le).le
    unfold pairForce
    rw [hv]
    simp only [vsmul]
    have hnum : (1 : ℝ) * 1 * (ρ * triU i k - ρ * triU j k) =
        ρ * (triU i k - triU j k) := by ring
    rw [hnum]
  have hcard : (Finset.univ.erase i).card = 2 := by
    rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ]
    rfl
  have hdiff : ∑ j ∈ Finset.univ.erase i, (triU i k - triU j k) =
      2 * triU i k + triU i k := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, sum_erase_triU]
    simp [nsmul_eq_mul]
  have hlin : ∑ j ∈ Finset.univ.erase i, ρ * (triU i k - triU j k) =
      ρ * (3 * triU i k) := by
    rw [← Finset.mul_sum, hdiff]
    ring
  rw [sum_congr rfl hterm]
  have hpull : ∑ j ∈ Finset.univ.erase i, ρ * (triU i k - triU j k) / D =
      (∑ j ∈ Finset.univ.erase i, ρ * (triU i k - triU j k)) / D := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  rw [hpull, hlin]
  field_simp [hD]

lemma cross_sum_along {q₁ q₂ ρ σ : ℝ} {i : Fin 3}
    (hq : q₁ * q₂ = -1) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hsep : outerSep (chord ρ σ triCos)) (k : Fin 3) :
    ∑ j ∈ Finset.univ.erase i,
        pairForce q₁ q₂ (vsmul ρ (triU i)) (vsmul σ (triU j)) k =
      (-(2 * ρ + σ) / (gammaSEqual (pairPhase (chord ρ σ triCos)) *
        chord ρ σ triCos ^ 3)) * triU i k := by
  set d : ℝ := chord ρ σ triCos
  set D : ℝ := gammaSEqual (pairPhase d) * d ^ 3
  have hD : D ≠ 0 :=
    mul_ne_zero (outer_gamma_pos hsep).ne' (pow_ne_zero 3 hsep.1.ne')
  have hnn : 0 ≤ chordSq ρ σ triCos :=
    (chordSq_pos_obtuse hρ hσ triCos_lt_zero.le).le
  have hterm : ∀ j ∈ Finset.univ.erase i,
      pairForce q₁ q₂ (vsmul ρ (triU i)) (vsmul σ (triU j)) k =
        -(ρ * triU i k - σ * triU j k) / D := by
    intro j hj
    have hij : i ≠ j := (mem_erase.mp hj).1.symm
    have hv := vnorm_unit_chord (triU_normSq i) (triU_normSq j) (triU_dot hij) hnn
    unfold pairForce
    rw [hv]
    simp only [vsmul]
    have hnum : q₁ * q₂ * (ρ * triU i k - σ * triU j k) =
        -(ρ * triU i k - σ * triU j k) := by
      linear_combination (ρ * triU i k - σ * triU j k) * hq
    rw [hnum]
  have hcard : (Finset.univ.erase i).card = 2 := by
    rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ]
    rfl
  have hdiff : ∑ j ∈ Finset.univ.erase i, (ρ * triU i k - σ * triU j k) =
      (2 * ρ + σ) * triU i k := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, ← Finset.mul_sum, sum_erase_triU]
    simp [nsmul_eq_mul]
    ring
  have hlin : ∑ j ∈ Finset.univ.erase i, -(ρ * triU i k - σ * triU j k) =
      -(2 * ρ + σ) * triU i k := by
    rw [Finset.sum_neg_distrib, hdiff]
    ring
  rw [sum_congr rfl hterm]
  have hpull : ∑ j ∈ Finset.univ.erase i, -(ρ * triU i k - σ * triU j k) / D =
      (∑ j ∈ Finset.univ.erase i, -(ρ * triU i k - σ * triU j k)) / D := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  rw [hpull, hlin]
  field_simp [hD]

/-- Force on the bonding electron of ray `i`, from the nucleus, its proton,
the other two electrons, and the other two protons. -/
def electronForce (Z : ℝ) (i : Fin 3) (r R : ℝ) : Fin 3 → ℝ :=
  fun k =>
    pairForce (-1) Z (vsmul r (triU i)) (fun _ => 0) k +
    pairForce (-1) 1 (vsmul r (triU i)) (vsmul R (triU i)) k +
    (∑ j ∈ Finset.univ.erase i,
      pairForce (-1) (-1) (vsmul r (triU i)) (vsmul r (triU j)) k) +
    (∑ j ∈ Finset.univ.erase i,
      pairForce (-1) 1 (vsmul r (triU i)) (vsmul R (triU j)) k)

/-- Force on the proton of ray `i`. -/
def protonForce (Z : ℝ) (i : Fin 3) (r R : ℝ) : Fin 3 → ℝ :=
  fun k =>
    pairForce 1 Z (vsmul R (triU i)) (fun _ => 0) k +
    pairForce 1 (-1) (vsmul R (triU i)) (vsmul r (triU i)) k +
    (∑ j ∈ Finset.univ.erase i,
      pairForce 1 1 (vsmul R (triU i)) (vsmul R (triU j)) k) +
    (∑ j ∈ Finset.univ.erase i,
      pairForce 1 (-1) (vsmul R (triU i)) (vsmul r (triU j)) k)

private lemma pair_product_swap {q₁ q₂ : ℝ} (ri rj : Fin 3 → ℝ) (k : Fin 3)
    {q₁' q₂' : ℝ} (hq : q₁ * q₂ = q₁' * q₂') :
    pairForce q₁ q₂ ri rj k = pairForce q₁' q₂' ri rj k := by
  unfold pairForce
  rw [hq]

theorem electronForce_parallel {Z r R : ℝ} {i : Fin 3}
    (hr : outerSep r) (hR : r < R) (hgap : outerSep (R - r)) (k : Fin 3) :
    electronForce Z i r R k =
      (-Z / (gammaSEqual (pairPhase r) * r ^ 2) +
        (-1) * (r - R) / (gammaSEqual (pairPhase |r - R|) * |r - R| ^ 3) +
        3 * r / (gammaSEqual (pairPhase (chord r r triCos)) * chord r r triCos ^ 3) +
        (-(2 * r + R) / (gammaSEqual (pairPhase (chord r R triCos)) *
          chord r R triCos ^ 3))) * triU i k := by
  have hr0 : 0 < r := hr.1
  have hR0 : 0 < R := lt_trans hr0 hR
  have hee := outerSep_tri_ee hr
  have hcross := outerSep_cross hr hR
  have hprod : ((-1 : ℝ) * -1) = 1 * 1 := by norm_num
  have hee_sum : ∑ j ∈ Finset.univ.erase i,
      pairForce (-1) (-1) (vsmul r (triU i)) (vsmul r (triU j)) k =
      ∑ j ∈ Finset.univ.erase i,
        pairForce 1 1 (vsmul r (triU i)) (vsmul r (triU j)) k := by
    refine sum_congr rfl ?_
    intro j _hj
    exact pair_product_swap (vsmul r (triU i)) (vsmul r (triU j)) k hprod
  have _used : 0 < R - r := hgap.1
  unfold electronForce
  rw [nucleus_along hr0 i k, sameRay_along hr0 hR0 i k, hee_sum,
    repulsion_sum_along hr0 hee k, cross_sum_along (by norm_num) hr0 hR0 hcross k]
  ring

theorem protonForce_parallel {Z r R : ℝ} {i : Fin 3}
    (hr : outerSep r) (hR : r < R) (hgap : outerSep (R - r)) (k : Fin 3) :
    protonForce Z i r R k =
      (Z / (gammaSEqual (pairPhase R) * R ^ 2) +
        (-1) * (R - r) / (gammaSEqual (pairPhase |R - r|) * |R - r| ^ 3) +
        3 * R / (gammaSEqual (pairPhase (chord R R triCos)) * chord R R triCos ^ 3) +
        (-(2 * R + r) / (gammaSEqual (pairPhase (chord R r triCos)) *
          chord R r triCos ^ 3))) * triU i k := by
  have hr0 : 0 < r := hr.1
  have hR0 : 0 < R := lt_trans hr0 hR
  have hRe : outerSep R := outerSep_longer hr hR
  have hpp := outerSep_tri_ee hRe
  have hsq : chordSq R r triCos = chordSq r R triCos := by
    unfold chordSq
    ring
  have hcross : outerSep (chord R r triCos) := by
    have hch : chord R r triCos = chord r R triCos := by
      unfold chord
      rw [hsq]
    rw [hch]
    exact outerSep_cross hr hR
  have _used : 0 < R - r := hgap.1
  unfold protonForce
  rw [nucleus_along hR0 i k, sameRay_along hR0 hr0 i k,
    repulsion_sum_along hR0 hpp k, cross_sum_along (by norm_num) hR0 hr0 hcross k]
  ring

private lemma vdot_ray {t u : Fin 3 → ℝ} {c : ℝ} (F : Fin 3 → ℝ)
    (ht : vdot t u = 0) (hF : ∀ k, F k = c * u k) : vdot t F = 0 := by
  have hmul : vdot t F = c * vdot t u := by
    unfold vdot
    rw [hF 0, hF 1, hF 2]
    ring
  rw [hmul, ht, mul_zero]

/-- On each ray the force lies along the ray, so both tangential components
vanish. The nuclear charge does not enter the direction. -/
theorem tri_tangent_zero {Z r R : ℝ} {i : Fin 3}
    (hr : outerSep r) (hR : r < R) (hgap : outerSep (R - r)) :
    vdot (triPerp i) (electronForce Z i r R) = 0 ∧
      vdot triZ (electronForce Z i r R) = 0 ∧
      vdot (triPerp i) (protonForce Z i r R) = 0 ∧
      vdot triZ (protonForce Z i r R) = 0 := by
  let cE : ℝ :=
    -Z / (gammaSEqual (pairPhase r) * r ^ 2) +
      (-1) * (r - R) / (gammaSEqual (pairPhase |r - R|) * |r - R| ^ 3) +
      3 * r / (gammaSEqual (pairPhase (chord r r triCos)) * chord r r triCos ^ 3) +
      (-(2 * r + R) / (gammaSEqual (pairPhase (chord r R triCos)) *
        chord r R triCos ^ 3))
  let cP : ℝ :=
    Z / (gammaSEqual (pairPhase R) * R ^ 2) +
      (-1) * (R - r) / (gammaSEqual (pairPhase |R - r|) * |R - r| ^ 3) +
      3 * R / (gammaSEqual (pairPhase (chord R R triCos)) * chord R R triCos ^ 3) +
      (-(2 * R + r) / (gammaSEqual (pairPhase (chord R r triCos)) *
        chord R r triCos ^ 3))
  have hE : ∀ k, electronForce Z i r R k = cE * triU i k := by
    intro k
    simpa [cE] using electronForce_parallel hr hR hgap k
  have hP : ∀ k, protonForce Z i r R k = cP * triU i k := by
    intro k
    simpa [cP] using protonForce_parallel hr hR hgap k
  exact ⟨vdot_ray _ (triPerp_dot i) hE, vdot_ray _ (triZ_dot i) hE,
    vdot_ray _ (triPerp_dot i) hP, vdot_ray _ (triZ_dot i) hP⟩

/-! ### An electron on the axis -/

/-- Distance from a charge at radius `ρ` in the plane to an electron at
height `s` on the axis. -/
def axialDist (ρ s : ℝ) : ℝ := sqrt (ρ ^ 2 + s ^ 2)

/-- Generalized force that increases the angle from the positive axis, at the
plane. Positive drives every ray to the side opposite an electron at `+s`. -/
def triBend (r R s : ℝ) : ℝ :=
  s * (r / (gammaSEqual (pairPhase (axialDist r s)) * axialDist r s ^ 3) -
    R / (gammaSEqual (pairPhase (axialDist R s)) * axialDist R s ^ 3))

lemma vnorm_axial (ρ s : ℝ) (i : Fin 3) :
    vnorm (vsub (vsmul ρ (triU i)) (triAxis s)) = axialDist ρ s := by
  have hu : triU i 0 * triU i 0 + triU i 1 * triU i 1 = 1 := by
    have h := triU_normSq i
    simp only [vdot] at h
    rw [triU_z] at h
    simpa using h
  have h2 : vnorm2 (vsub (vsmul ρ (triU i)) (triAxis s)) = ρ ^ 2 + s ^ 2 := by
    unfold vnorm2 vdot vsub vsmul triAxis
    simp only [triU_z]
    calc
      (ρ * triU i 0 - 0) * (ρ * triU i 0 - 0) +
          (ρ * triU i 1 - 0) * (ρ * triU i 1 - 0) +
          (ρ * 0 - s) * (ρ * 0 - s)
        = ρ ^ 2 * (triU i 0 * triU i 0 + triU i 1 * triU i 1) + s ^ 2 := by ring
      _ = ρ ^ 2 * 1 + s ^ 2 := by rw [hu]
      _ = ρ ^ 2 + s ^ 2 := by ring
  unfold vnorm axialDist
  rw [h2]

lemma plane_pair_normal {q₁ q₂ : ℝ} {a b : Fin 3 → ℝ}
    (ha : a 2 = 0) (hb : b 2 = 0) : pairForce q₁ q₂ a b 2 = 0 := by
  unfold pairForce vsub
  rw [ha, hb]
  simp

/-- In the plane, only the axial electron contributes to the normal component. -/
theorem tri_plane_normal {Z r R : ℝ} {i : Fin 3}
    (_hr : 0 < r) (_hR : 0 < R) :
    electronForce Z i r R 2 = 0 ∧ protonForce Z i r R 2 = 0 := by
  have he : (vsmul r (triU i)) 2 = 0 := by simp [vsmul, triU_z]
  have hp : (vsmul R (triU i)) 2 = 0 := by simp [vsmul, triU_z]
  have h0 : (fun _ : Fin 3 => (0 : ℝ)) 2 = 0 := rfl
  unfold electronForce protonForce
  constructor
  · rw [plane_pair_normal he h0, plane_pair_normal he hp]
    have hsumE : ∑ j ∈ Finset.univ.erase i,
        pairForce (-1) (-1) (vsmul r (triU i)) (vsmul r (triU j)) 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j _hj
      exact plane_pair_normal he (by simp [vsmul, triU_z])
    have hsumP : ∑ j ∈ Finset.univ.erase i,
        pairForce (-1) 1 (vsmul r (triU i)) (vsmul R (triU j)) 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j _hj
      exact plane_pair_normal he (by simp [vsmul, triU_z])
    rw [hsumE, hsumP]
    ring
  · rw [plane_pair_normal hp h0, plane_pair_normal hp he]
    have hsumP : ∑ j ∈ Finset.univ.erase i,
        pairForce 1 1 (vsmul R (triU i)) (vsmul R (triU j)) 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j _hj
      exact plane_pair_normal hp (by simp [vsmul, triU_z])
    have hsumE : ∑ j ∈ Finset.univ.erase i,
        pairForce 1 (-1) (vsmul R (triU i)) (vsmul r (triU j)) 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j _hj
      exact plane_pair_normal hp (by simp [vsmul, triU_z])
    rw [hsumP, hsumE]
    ring

lemma axial_electron_normal {r s : ℝ} (_hr : 0 ≤ r) (i : Fin 3) :
    pairForce (-1) (-1) (vsmul r (triU i)) (triAxis s) 2 =
      -s / (gammaSEqual (pairPhase (axialDist r s)) * axialDist r s ^ 3) := by
  have hv := vnorm_axial r s i
  unfold pairForce
  rw [hv]
  simp only [vsmul, triAxis, triU_z]
  ring

lemma axial_proton_normal {R s : ℝ} (_hR : 0 ≤ R) (i : Fin 3) :
    pairForce 1 (-1) (vsmul R (triU i)) (triAxis s) 2 =
      s / (gammaSEqual (pairPhase (axialDist R s)) * axialDist R s ^ 3) := by
  have hv := vnorm_axial R s i
  unfold pairForce
  rw [hv]
  simp only [vsmul, triAxis, triU_z]
  ring

/-- The axial force has no component in the plane orthogonal to the ray. -/
theorem tri_axis_inplane {q ρ s : ℝ} (_hρ : 0 ≤ ρ) (i : Fin 3) :
    vdot (triPerp i) (fun k =>
      pairForce q (-1) (vsmul ρ (triU i)) (triAxis s) k) = 0 := by
  have hv := vnorm_axial ρ s i
  unfold vdot pairForce
  rw [hv]
  simp only [vsmul, triAxis, triPerp, triU_z]
  ring

/-- At the plane, the generalized force on each ray is `triBend`. The charges
already in the plane do not contribute to it. -/
theorem triRay_bend_eq {Z r R s : ℝ} {i : Fin 3}
    (hr : 0 < r) (hR : 0 < R) (_hs : 0 ≤ s) :
    -r * (electronForce Z i r R 2 +
        pairForce (-1) (-1) (vsmul r (triU i)) (triAxis s) 2) -
      R * (protonForce Z i r R 2 +
        pairForce 1 (-1) (vsmul R (triU i)) (triAxis s) 2) =
      triBend r R s := by
  obtain ⟨he, hp⟩ := tri_plane_normal (Z := Z) (i := i) hr hR
  rw [he, hp, axial_electron_normal hr.le i, axial_proton_normal hR.le i]
  unfold triBend
  ring

theorem axialDist_gt {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) : ρ < axialDist ρ s := by
  have hsq : ρ ^ 2 < ρ ^ 2 + s ^ 2 := by nlinarith [sq_pos_of_pos hs]
  have hsqrt : sqrt (ρ ^ 2) < sqrt (ρ ^ 2 + s ^ 2) :=
    sqrt_lt_sqrt (sq_nonneg ρ) hsq
  rw [sqrt_sq hρ.le] at hsqrt
  simpa [axialDist] using hsqrt

theorem outerSep_axial {ρ s : ℝ} (hρ : outerSep ρ) (hs : 0 < s) :
    outerSep (axialDist ρ s) :=
  outerSep_longer hρ (axialDist_gt hρ.1 hs)

/-- A non-shared electron on the axis, no farther out than the bonding
electrons, drives every ray off the plane to the opposite side. -/
theorem triBend_pos {r R s : ℝ}
    (hs : outerSep s) (hsr : s ≤ r) (hrR : r < R) :
    0 < triBend r R s := by
  have hr : outerSep r := outerSep_of_le hs hsr
  have hR : outerSep R := outerSep_longer hr hrR
  have hs0 : 0 < s := hs.1
  have hr0 : 0 < r := hr.1
  have hR0 : 0 < R := hR.1
  have hde : outerSep (axialDist r s) := outerSep_axial hr hs0
  have hdp : outerSep (axialDist R s) := outerSep_axial hR hs0
  set de : ℝ := axialDist r s
  set dp : ℝ := axialDist R s
  have hde_pos : 0 < de := hde.1
  have hdp_pos : 0 < dp := hdp.1
  have hde2 : de ^ 2 = r ^ 2 + s ^ 2 := by
    unfold de axialDist
    exact sq_sqrt (by positivity)
  have hdp2 : dp ^ 2 = R ^ 2 + s ^ 2 := by
    unfold dp axialDist
    exact sq_sqrt (by positivity)
  have hde_lt_dp : de < dp := by
    have hsq : de ^ 2 < dp ^ 2 := by
      rw [hde2, hdp2]
      nlinarith
    have habs : |de| < |dp| := (sq_lt_sq).mp hsq
    rwa [abs_of_pos hde_pos, abs_of_pos hdp_pos] at habs
  have hcube : R ^ 2 * (de ^ 2) ^ 3 < r ^ 2 * (dp ^ 2) ^ 3 := by
    rw [hde2, hdp2]
    have hdiff : r ^ 2 * (R ^ 2 + s ^ 2) ^ 3 - R ^ 2 * (r ^ 2 + s ^ 2) ^ 3 =
        (R ^ 2 - r ^ 2) *
          (R ^ 2 * r ^ 2 * (R ^ 2 + r ^ 2) + 3 * R ^ 2 * r ^ 2 * s ^ 2 - s ^ 6) := by
      ring
    have hs6 : s ^ 6 ≤ r ^ 6 := pow_le_pow_left₀ hs0.le hsr 6
    have hfactor : 0 < R ^ 2 - r ^ 2 := by nlinarith
    have hlow : 0 < R ^ 2 * r ^ 2 * (R ^ 2 + r ^ 2) - r ^ 6 := by
      have heq : R ^ 2 * r ^ 2 * (R ^ 2 + r ^ 2) - r ^ 6 =
          r ^ 2 * (R ^ 4 + R ^ 2 * r ^ 2 - r ^ 4) := by ring
      rw [heq]
      have hrest : 0 < R ^ 4 + R ^ 2 * r ^ 2 - r ^ 4 := by
        have hpow : r ^ 4 < R ^ 4 :=
          pow_lt_pow_left₀ hrR hr0.le (by norm_num : (4 : ℕ) ≠ 0)
        nlinarith
      positivity
    have hbrack : 0 <
        R ^ 2 * r ^ 2 * (R ^ 2 + r ^ 2) + 3 * R ^ 2 * r ^ 2 * s ^ 2 - s ^ 6 := by
      have hnn : 0 ≤ 3 * R ^ 2 * r ^ 2 * s ^ 2 := by positivity
      have hge : R ^ 2 * r ^ 2 * (R ^ 2 + r ^ 2) - r ^ 6 ≤
          R ^ 2 * r ^ 2 * (R ^ 2 + r ^ 2) + 3 * R ^ 2 * r ^ 2 * s ^ 2 - s ^ 6 := by
        linarith [hs6, hnn]
      linarith [hlow, hge]
    have hpos : 0 < r ^ 2 * (R ^ 2 + s ^ 2) ^ 3 - R ^ 2 * (r ^ 2 + s ^ 2) ^ 3 := by
      rw [hdiff]
      exact mul_pos hfactor hbrack
    linarith
  have hgeom : R * de ^ 3 < r * dp ^ 3 := by
    have hsq : (R * de ^ 3) ^ 2 < (r * dp ^ 3) ^ 2 := by
      calc
        (R * de ^ 3) ^ 2 = R ^ 2 * (de ^ 2) ^ 3 := by ring
        _ < r ^ 2 * (dp ^ 2) ^ 3 := hcube
        _ = (r * dp ^ 3) ^ 2 := by ring
    have habs : |R * de ^ 3| < |r * dp ^ 3| := (sq_lt_sq).mp hsq
    rwa [abs_of_pos (by positivity), abs_of_pos (by positivity)] at habs
  have hφ : pairPhase dp < pairPhase de := pairPhase_anti hde_pos hde_lt_dp
  have hγ : gammaSEqual (pairPhase de) < gammaSEqual (pairPhase dp) :=
    gamma_strictAnti_phase (by
      unfold pairPhase
      exact div_nonneg (by norm_num) (by linarith : (0 : ℝ) ≤ 2 * dp)) hde.2 hφ
  have hγe : 0 < gammaSEqual (pairPhase de) := outer_gamma_pos hde
  have hγp : 0 < gammaSEqual (pairPhase dp) := outer_gamma_pos hdp
  have hdiv : R / (gammaSEqual (pairPhase dp) * dp ^ 3) <
      r / (gammaSEqual (pairPhase de) * de ^ 3) := by
    rw [div_lt_div_iff₀ (mul_pos hγp (pow_pos hdp_pos 3))
      (mul_pos hγe (pow_pos hde_pos 3))]
    have h1 : gammaSEqual (pairPhase de) * (R * de ^ 3) <
        gammaSEqual (pairPhase dp) * (R * de ^ 3) :=
      mul_lt_mul_of_pos_right hγ (mul_pos hR0 (pow_pos hde_pos 3))
    have h2 : gammaSEqual (pairPhase dp) * (R * de ^ 3) <
        gammaSEqual (pairPhase dp) * (r * dp ^ 3) :=
      mul_lt_mul_of_pos_left hgeom hγp
    linarith
  unfold triBend
  exact mul_pos hs0 (sub_pos.mpr hdiv)

end

end DstDiophantine.Gravity
