import DstDiophantine.Gravity.ElectronWater
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The angle of a covalent bond

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. No bond angle in degrees, no dissociation energy,
and no count of seats is produced. The radius at which a non-shared electron
rests is not located. The comparison holds while that electron remains at least
`1/√2` times as far from the nucleus as a bonding electron.

## What is proved

Distances are in units of `ℓ`. The rays are the four vertices of a regular
tetrahedron, and the cosine of the angle between two of them is `-1/3`, so the
angle is greater than a right angle.

* At one common electron distance, with protons at one greater common distance
  on a subset of the rays and with those separations in the outer well, the
  outward force on an electron whose ray carries a proton is strictly greater
  than the outward force on an electron whose ray carries none.
* While the angle is at least a right angle and both separations lie in the
  outer well, a closer electron repels a neighbor more strongly.
* If the closer electron is still at least `1/√2` times as far out as the
  neighbor, the tangential part of that repulsion is stronger as well.
* Four electrons at one distance, and four protons at one greater distance,
  exert no tangential force. Move one electron inward, not past the fraction
  above, and remove the proton on its ray. At this angle the tangential force
  on each of the other three drives the angle with the remaining bonds
  narrower. A second electron moved inward by the same amount, with its proton
  likewise removed, contributes the same narrowing, so the two together
  contribute twice one.
-/

namespace DstDiophantine.Gravity

noncomputable section

open Real Set Finset

/-! ### Tetrahedron -/

/-- Cosine of the angle between two vertices of a regular tetrahedron. -/
def tetCos : ℝ := -1 / 3

def tetRaw : Fin 4 → Fin 3 → ℝ
  | 0, 0 => 1
  | 0, 1 => 1
  | 0, 2 => 1
  | 1, 0 => 1
  | 1, 1 => -1
  | 1, 2 => -1
  | 2, 0 => -1
  | 2, 1 => 1
  | 2, 2 => -1
  | 3, 0 => -1
  | 3, 1 => -1
  | 3, 2 => 1

/-- Unit vector toward vertex `i`. -/
def tetU (i : Fin 4) : Fin 3 → ℝ :=
  vsmul (1 / sqrt 3) (tetRaw i)

private lemma tetRaw_dot (i j : Fin 4) :
    vdot (tetRaw i) (tetRaw j) = if i = j then 3 else -1 := by
  fin_cases i <;> fin_cases j <;> simp [vdot, tetRaw] <;> norm_num

lemma tetU_normSq (i : Fin 4) : vdot (tetU i) (tetU i) = 1 := by
  have hsmul : vdot (vsmul (1 / sqrt 3) (tetRaw i)) (vsmul (1 / sqrt 3) (tetRaw i)) =
      (1 / sqrt 3) ^ 2 * vdot (tetRaw i) (tetRaw i) := by
    unfold vdot vsmul
    ring
  unfold tetU
  rw [hsmul, tetRaw_dot, ite_eq_left rfl]
  have hsq : (sqrt 3) ^ 2 = 3 := sq_sqrt (by norm_num)
  calc
    (1 / sqrt 3) ^ 2 * 3 = 3 / (sqrt 3) ^ 2 := by ring
    _ = 3 / 3 := by rw [hsq]
    _ = 1 := by ring

lemma tetU_dot_self (i : Fin 4) : vdot (tetU i) (tetU i) = 1 :=
  tetU_normSq i

lemma tetU_dot_ne {i j : Fin 4} (hij : i ≠ j) : vdot (tetU i) (tetU j) = tetCos := by
  have hsmul : vdot (vsmul (1 / sqrt 3) (tetRaw i)) (vsmul (1 / sqrt 3) (tetRaw j)) =
      (1 / sqrt 3) ^ 2 * vdot (tetRaw i) (tetRaw j) := by
    unfold vdot vsmul
    ring
  unfold tetU tetCos
  rw [hsmul, tetRaw_dot, ite_eq_right hij]
  have hsq : (sqrt 3) ^ 2 = 3 := sq_sqrt (by norm_num)
  calc
    (1 / sqrt 3) ^ 2 * -1 = -1 / (sqrt 3) ^ 2 := by ring
    _ = -1 / 3 := by rw [hsq]
    _ = -1 / 3 := by ring

lemma tetU_norm (i : Fin 4) : vnorm (tetU i) = 1 := by
  have hsq : vnorm (tetU i) ^ 2 = 1 := by
    rw [vnorm_sq]
    unfold vnorm2
    exact tetU_normSq i
  have hnn : 0 ≤ vnorm (tetU i) := sqrt_nonneg _
  rw [← sqrt_sq hnn, hsq, sqrt_one]

private lemma tetRaw_sum (k : Fin 3) :
    tetRaw 0 k + tetRaw 1 k + tetRaw 2 k + tetRaw 3 k = 0 := by
  fin_cases k <;> simp [tetRaw]

lemma tetU_sum_zero (k : Fin 3) :
    tetU 0 k + tetU 1 k + tetU 2 k + tetU 3 k = 0 := by
  have h := tetRaw_sum k
  have hscale : tetU 0 k + tetU 1 k + tetU 2 k + tetU 3 k =
      (1 / sqrt 3) * (tetRaw 0 k + tetRaw 1 k + tetRaw 2 k + tetRaw 3 k) := by
    unfold tetU vsmul
    ring
  rw [hscale, h, mul_zero]

lemma sum_tetU_zero (k : Fin 3) : ∑ i : Fin 4, tetU i k = 0 := by
  rw [Fin.sum_univ_four]
  exact tetU_sum_zero k

lemma sum_erase_tetU (i : Fin 4) (k : Fin 3) :
    ∑ j ∈ Finset.univ.erase i, tetU j k = -tetU i k := by
  have h := Finset.add_sum_erase Finset.univ (fun j => tetU j k) (mem_univ i)
  rw [sum_tetU_zero] at h
  linarith

theorem tetCos_neg : tetCos < 0 := by
  unfold tetCos
  norm_num

theorem tetAngle_gt_right : π / 2 < arccos tetCos := by
  have h : arccos (0 : ℝ) < arccos tetCos :=
    arccos_lt_arccos (by unfold tetCos; norm_num) tetCos_neg (by norm_num)
  simpa [arccos_zero] using h

/-! ### Chords -/

def chordSq (r s c : ℝ) : ℝ :=
  r ^ 2 + s ^ 2 - 2 * r * s * c

def chord (r s c : ℝ) : ℝ :=
  sqrt (chordSq r s c)

lemma chordSq_tet (r : ℝ) : chordSq r r tetCos = (8 / 3) * r ^ 2 := by
  unfold chordSq tetCos
  ring

lemma chordSq_pos_obtuse {r s c : ℝ} (hr : 0 < r) (hs : 0 < s) (hc : c ≤ 0) :
    0 < chordSq r s c := by
  unfold chordSq
  have hc0 : 0 ≤ -c := neg_nonneg.mpr hc
  have hcross : 0 ≤ 2 * r * s * (-c) := by positivity
  have hsq : 0 < r ^ 2 + s ^ 2 := by positivity
  linarith

lemma chord_pos_obtuse {r s c : ℝ} (hr : 0 < r) (hs : 0 < s) (hc : c ≤ 0) :
    0 < chord r s c :=
  sqrt_pos.mpr (chordSq_pos_obtuse hr hs hc)

lemma chord_sq_eq {r s c : ℝ} (h : 0 ≤ chordSq r s c) :
    chord r s c ^ 2 = chordSq r s c := by
  unfold chord
  exact sq_sqrt h

lemma chord_lt_of_lt {r d D c : ℝ} (hr : 0 < r) (hd : 0 < d) (hD : d < D) (hc : c ≤ 0) :
    chord r d c < chord r D c := by
  have hsq : chordSq r d c < chordSq r D c := by
    unfold chordSq
    have hdiff : (D ^ 2 - d ^ 2) - 2 * r * c * (D - d) =
        (D - d) * (D + d - 2 * r * c) := by ring
    have hpos : 0 < (D - d) * (D + d - 2 * r * c) := by
      have h1 : 0 < D - d := sub_pos.mpr hD
      have h2 : 0 < D + d - 2 * r * c := by
        have hc' : 2 * r * c ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.le) hc
        linarith [hd, hD, hc']
      exact mul_pos h1 h2
    linarith
  exact sqrt_lt_sqrt (chordSq_pos_obtuse hr hd hc).le hsq

lemma vnorm_smul (c : ℝ) (v : Fin 3 → ℝ) :
    vnorm (vsmul c v) = |c| * vnorm v := by
  unfold vnorm
  rw [vnorm2_smul, ← sq_abs, sqrt_mul (sq_nonneg |c|), sqrt_sq (abs_nonneg c)]

lemma vdot_comm (u v : Fin 3 → ℝ) : vdot u v = vdot v u := by
  unfold vdot
  ring

lemma vdot_smul_left (a : ℝ) (t v : Fin 3 → ℝ) :
    vdot (vsmul a t) v = a * vdot t v := by
  unfold vdot vsmul
  ring

lemma vdot_smul_right (a : ℝ) (t v : Fin 3 → ℝ) :
    vdot t (vsmul a v) = a * vdot t v := by
  unfold vdot vsmul
  ring

lemma vdot_sub (t u w : Fin 3 → ℝ) :
    vdot t (vsub u w) = vdot t u - vdot t w := by
  unfold vdot vsub
  ring

lemma vdot_sub_left (u w t : Fin 3 → ℝ) :
    vdot (vsub u w) t = vdot u t - vdot w t := by
  unfold vdot vsub
  ring

lemma vnorm_unit_chord {u v : Fin 3 → ℝ} {r s c : ℝ}
    (hu : vdot u u = 1) (hv : vdot v v = 1) (hc : vdot u v = c)
    (_hnn : 0 ≤ chordSq r s c) :
    vnorm (vsub (vsmul r u) (vsmul s v)) = chord r s c := by
  have h2 : vnorm2 (vsub (vsmul r u) (vsmul s v)) = chordSq r s c := by
    unfold vnorm2 vdot vsub vsmul chordSq
    have hu0 : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1 := by
      simpa [vdot] using hu
    have hv0 : v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = 1 := by
      simpa [vdot] using hv
    have hc0 : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = c := by
      simpa [vdot] using hc
    linear_combination r ^ 2 * hu0 + s ^ 2 * hv0 - 2 * r * s * hc0
  unfold vnorm chord
  rw [h2]

private lemma pairPhase_anti {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    pairPhase b < pairPhase a := by
  unfold pairPhase
  exact div_lt_div_of_pos_left (by norm_num)
    (mul_pos (by norm_num : (0 : ℝ) < 2) ha)
    (mul_lt_mul_of_pos_left hab (by norm_num : (0 : ℝ) < 2))

private lemma outerSep_longer {d s : ℝ} (hd : outerSep d) (hlt : d < s) : outerSep s := by
  refine ⟨lt_trans hd.1 hlt, lt_trans (pairPhase_anti hd.1 hlt) hd.2⟩

lemma chord_tet_gt {r : ℝ} (hr : 0 < r) : r < chord r r tetCos := by
  have hsq : chordSq r r tetCos = (8 / 3) * r ^ 2 := chordSq_tet r
  have hchord : chord r r tetCos = sqrt (8 / 3) * r := by
    unfold chord
    rw [hsq, sqrt_mul (by norm_num : (0 : ℝ) ≤ 8 / 3), sqrt_sq hr.le]
  rw [hchord]
  have h1 : (1 : ℝ) < sqrt (8 / 3) := by
    rw [← sqrt_one]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

lemma outerSep_tet_chord {r : ℝ} (hr : outerSep r) : outerSep (chord r r tetCos) :=
  outerSep_longer hr (chord_tet_gt hr.1)

/-! ### Closer repels more strongly -/

def coulWeight (r s c : ℝ) : ℝ :=
  s / chord r s c ^ 3

def tangWeight (r s c : ℝ) : ℝ :=
  s / (gammaSEqual (pairPhase (chord r s c)) * chord r s c ^ 3)

private lemma vdot_pairForce (qi qj : ℝ) (ri rj t : Fin 3 → ℝ)
    (_hden : gammaSEqual (pairPhase (vnorm (vsub ri rj))) * vnorm (vsub ri rj) ^ 3 ≠ 0) :
    vdot t (fun i => pairForce qi qj ri rj i) =
      qi * qj * vdot t (vsub ri rj) /
        (gammaSEqual (pairPhase (vnorm (vsub ri rj))) * vnorm (vsub ri rj) ^ 3) := by
  unfold vdot pairForce
  field_simp [_hden]
  unfold vsub
  ring

theorem repulsion_gt_of_closer {r d D c : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hD : d < D) (hc : c ≤ 0)
    (hdd : outerSep (chord r d c)) (hDD : outerSep (chord r D c)) :
    pairAttraction (pairPhase (chord r D c)) <
      pairAttraction (pairPhase (chord r d c)) := by
  have hchord := chord_lt_of_lt hr hd hD hc
  have hφ : pairPhase (chord r D c) < pairPhase (chord r d c) :=
    pairPhase_anti hdd.1 hchord
  have hdI : pairPhase (chord r d c) ∈ Ioo 0 resonanceRoot1 := by
    refine ⟨?_, hdd.2⟩
    unfold pairPhase
    exact div_pos (by norm_num) (by linarith [hdd.1])
  have hDI : pairPhase (chord r D c) ∈ Ioo 0 resonanceRoot1 := by
    refine ⟨?_, hDD.2⟩
    unfold pairPhase
    exact div_pos (by norm_num) (by linarith [hDD.1])
  exact (pairAttraction_strictMono_outer.lt_iff_lt hDI hdI).mpr hφ

private theorem hasDerivAt_chordSq (r c s : ℝ) :
    HasDerivAt (fun t => chordSq r t c) (2 * s - 2 * r * c) s := by
  have hlin : HasDerivAt (fun t : ℝ => -(2 * r * c) * t) (-(2 * r * c)) s := by
    simpa using (hasDerivAt_id s).const_mul (-(2 * r * c))
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hfun : (fun t => chordSq r t c) =
      (fun x => r ^ 2) + ((fun t => t ^ 2) + fun t => -(2 * r * c) * t) := by
    funext t
    unfold chordSq
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  exact ((hasDerivAt_const s (r ^ 2)).add (hsq.add hlin)).congr_deriv (by ring)

private theorem hasDerivAt_chord {r c s : ℝ} (hpos : 0 < chordSq r s c) :
    HasDerivAt (fun t => chord r t c) ((s - r * c) / chord r s c) s := by
  have hsqrt := (hasDerivAt_chordSq r c s).sqrt hpos.ne'
  refine hsqrt.congr_deriv ?_
  unfold chord
  have hne : sqrt (chordSq r s c) ≠ 0 := (sqrt_pos.mpr hpos).ne'
  field_simp [hne]

private theorem hasDerivAt_coulWeight {r c s : ℝ} (hpos : 0 < chordSq r s c) :
    HasDerivAt (fun t => coulWeight r t c)
      ((r ^ 2 - 2 * s ^ 2 + r * s * c) / chord r s c ^ 5) s := by
  have hch := hasDerivAt_chord hpos
  have hpow : HasDerivAt (fun t => chord r t c ^ 3)
      (3 * chord r s c ^ 2 * ((s - r * c) / chord r s c)) s := by
    have h := hch.pow 3
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
  have hρpos : 0 < chord r s c := sqrt_pos.mpr hpos
  have hdiv := (hasDerivAt_id s).fun_div hpow (pow_ne_zero 3 hρpos.ne')
  refine hdiv.congr_deriv ?_
  field_simp [hρpos.ne']
  simp only [id]
  rw [chord_sq_eq hpos.le]
  unfold chordSq
  ring

private theorem coulWeight_anti {r d D c : ℝ}
    (hr : 0 < r) (hd : r / sqrt 2 ≤ d) (hD : d < D) (hc : c ≤ 0) :
    coulWeight r D c < coulWeight r d c := by
  have hd0 : 0 < d := by
    have hsqrt : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    exact lt_of_lt_of_le (div_pos hr hsqrt) hd
  have hpos : ∀ t ∈ Icc d D, 0 < chordSq r t c := by
    intro t ht
    exact chordSq_pos_obtuse hr (lt_of_lt_of_le hd0 ht.1) hc
  have hcont : ContinuousOn (fun t => coulWeight r t c) (Icc d D) := by
    unfold coulWeight
    refine ContinuousOn.div continuousOn_id ?_ ?_
    · refine ContinuousOn.pow ?_ 3
      unfold chord chordSq
      have hpoly : Continuous (fun t : ℝ => r ^ 2 + t ^ 2 - 2 * r * t * c) := by
        continuity
      exact (continuous_sqrt.comp hpoly).continuousOn
    · intro t ht
      exact pow_ne_zero 3 (sqrt_pos.mpr (hpos t ht)).ne'
  have hder : ∀ t ∈ Ioo d D, HasDerivAt (fun s => coulWeight r s c)
      ((r ^ 2 - 2 * t ^ 2 + r * t * c) / chord r t c ^ 5) t := by
    intro t ht
    exact hasDerivAt_coulWeight (hpos t ⟨ht.1.le, ht.2.le⟩)
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope (fun t => coulWeight r t c)
      (fun t => (r ^ 2 - 2 * t ^ 2 + r * t * c) / chord r t c ^ 5) hD hcont hder
  have hξsqrt : r / sqrt 2 < ξ := lt_of_le_of_lt hd hξ.1
  have hneg : r ^ 2 - 2 * ξ ^ 2 + r * ξ * c < 0 := by
    have hsqrt : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    have hξ0 : 0 < ξ := lt_trans (div_pos hr hsqrt) hξsqrt
    have hrξ : r < ξ * sqrt 2 := by
      rw [div_lt_iff₀ hsqrt] at hξsqrt
      simpa [mul_comm] using hξsqrt
    have hsq : r ^ 2 < 2 * ξ ^ 2 := by
      have hlt : r ^ 2 < (ξ * sqrt 2) ^ 2 := by
        apply sq_lt_sq'
        · linarith
        · exact hrξ
      have hpow : (ξ * sqrt 2) ^ 2 = 2 * ξ ^ 2 := by
        rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      linarith
    have hcross : r * ξ * c ≤ 0 := by
      have : 0 ≤ -c := neg_nonneg.mpr hc
      have hξr : 0 < r * ξ := mul_pos hr hξ0
      exact mul_nonpos_of_nonneg_of_nonpos hξr.le hc
    linarith
  have hden : 0 < chord r ξ c ^ 5 := pow_pos (chord_pos_obtuse hr (by
      have hsqrt : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
      exact lt_trans (div_pos hr hsqrt) hξsqrt) hc) 5
  have hderiv_neg : (r ^ 2 - 2 * ξ ^ 2 + r * ξ * c) / chord r ξ c ^ 5 < 0 :=
    div_neg_of_neg_of_pos hneg hden
  have hdiff : (coulWeight r D c - coulWeight r d c) / (D - d) < 0 := by
    rw [← hslope]
    exact hderiv_neg
  have hspan : 0 < D - d := sub_pos.mpr hD
  have heq : coulWeight r D c - coulWeight r d c =
      ((coulWeight r D c - coulWeight r d c) / (D - d)) * (D - d) := by
    field_simp [hspan.ne']
  have hlt : coulWeight r D c - coulWeight r d c < 0 := by
    rw [heq]
    exact mul_neg_of_neg_of_pos hdiff hspan
  exact (sub_neg).mp hlt

theorem tangWeight_gt_of_closer {r d D c : ℝ}
    (hr : 0 < r) (hd : r / sqrt 2 ≤ d) (hD : d < D) (hc : c ≤ 0)
    (hdd : outerSep (chord r d c)) (hDD : outerSep (chord r D c)) :
    tangWeight r D c < tangWeight r d c := by
  have hcoul := coulWeight_anti hr hd hD hc
  have hchord := chord_lt_of_lt hr (by
      have hsqrt : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
      exact lt_of_lt_of_le (div_pos hr hsqrt) hd) hD hc
  have hφ : pairPhase (chord r D c) < pairPhase (chord r d c) :=
    pairPhase_anti hdd.1 hchord
  have hγ : gammaSEqual (pairPhase (chord r d c)) <
      gammaSEqual (pairPhase (chord r D c)) := by
    refine gamma_strictAnti_phase ?_ hdd.2 hφ
    unfold pairPhase
    exact div_nonneg (by norm_num) (by linarith [hDD.1])
  have hγd : 0 < gammaSEqual (pairPhase (chord r d c)) := outer_gamma_pos hdd
  have hγD : 0 < gammaSEqual (pairPhase (chord r D c)) := outer_gamma_pos hDD
  have hcd : 0 < coulWeight r d c := by
    unfold coulWeight
    exact div_pos (by
      have hsqrt : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
      exact lt_of_lt_of_le (div_pos hr hsqrt) hd)
      (pow_pos (chord_pos_obtuse hr (by
        have hsqrt : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
        exact lt_of_lt_of_le (div_pos hr hsqrt) hd) hc) 3)
  have h1 : coulWeight r d c / gammaSEqual (pairPhase (chord r D c)) <
      coulWeight r d c / gammaSEqual (pairPhase (chord r d c)) := by
    unfold coulWeight at hcd ⊢
    exact div_lt_div_of_pos_left hcd hγd hγ
  have h2 : coulWeight r D c / gammaSEqual (pairPhase (chord r D c)) <
      coulWeight r d c / gammaSEqual (pairPhase (chord r D c)) := by
    exact div_lt_div_of_pos_right hcoul hγD
  have hTD : tangWeight r D c =
      coulWeight r D c / gammaSEqual (pairPhase (chord r D c)) := by
    unfold tangWeight coulWeight
    field_simp [hγD.ne', hDD.1.ne']
  have hTd : tangWeight r d c =
      coulWeight r d c / gammaSEqual (pairPhase (chord r d c)) := by
    unfold tangWeight coulWeight
    field_simp [hγd.ne', hdd.1.ne']
  rw [hTD, hTd]
  exact lt_trans h2 h1

/-! ### Radial force: a shared electron is driven outward -/

def protonRadial (i j : Fin 4) (r R : ℝ) : ℝ :=
  vdot (tetU i) (fun k => pairForce (-1) 1 (vsmul r (tetU i)) (vsmul R (tetU j)) k)

def nucleusRadial (Z : ℝ) (i : Fin 4) (r : ℝ) : ℝ :=
  vdot (tetU i) (fun k => pairForce (-1) Z (vsmul r (tetU i)) (fun _ => 0) k)

def electronRadial (i j : Fin 4) (ri rj : ℝ) : ℝ :=
  vdot (tetU i) (fun k =>
    pairForce (-1) (-1) (vsmul ri (tetU i)) (vsmul rj (tetU j)) k)

private lemma den_ne {ρ : ℝ} (hρ : 0 < ρ) (hγ : gammaSEqual (pairPhase ρ) ≠ 0) :
    gammaSEqual (pairPhase ρ) * ρ ^ 3 ≠ 0 :=
  mul_ne_zero hγ (pow_ne_zero 3 hρ.ne')

private lemma den_of_norm {u v : Fin 3 → ℝ} {r s ρ : ℝ}
    (hnorm : vnorm (vsub (vsmul r u) (vsmul s v)) = ρ)
    (hden : gammaSEqual (pairPhase ρ) * ρ ^ 3 ≠ 0) :
    gammaSEqual (pairPhase (vnorm (vsub (vsmul r u) (vsmul s v)))) *
        vnorm (vsub (vsmul r u) (vsmul s v)) ^ 3 ≠ 0 := by
  simpa [hnorm] using hden

theorem protonRadial_self {i : Fin 4} {r R : ℝ}
    (_hr : 0 < r) (hR : r < R) (hsep : outerSep (R - r)) :
    protonRadial i i r R =
      1 / (gammaSEqual (pairPhase (R - r)) * (R - r) ^ 2) := by
  have hu := tetU_dot_self i
  have hpos : 0 < R - r := sub_pos.mpr hR
  have hsub : vsub (vsmul r (tetU i)) (vsmul R (tetU i)) = vsmul (r - R) (tetU i) := by
    funext k
    simp [vsub, vsmul]
    ring
  have hnorm : vnorm (vsub (vsmul r (tetU i)) (vsmul R (tetU i))) = R - r := by
    rw [hsub, vnorm_smul, tetU_norm, mul_one, abs_of_neg (sub_neg.mpr hR)]
    linarith
  have hγ : gammaSEqual (pairPhase (R - r)) ≠ 0 := (outer_gamma_pos hsep).ne'
  have hden := den_ne hpos hγ
  rw [protonRadial, vdot_pairForce _ _ _ _ _ (den_of_norm hnorm hden)]
  rw [hnorm, hsub]
  have hdot : vdot (tetU i) (vsmul (r - R) (tetU i)) = r - R := by
    rw [vdot_smul_right, tetU_dot_self, mul_one]
  rw [hdot]
  have hne : R - r ≠ 0 := hpos.ne'
  field_simp [hγ, hne]
  ring

theorem protonRadial_self_pos {i : Fin 4} {r R : ℝ}
    (hr : 0 < r) (hR : r < R) (hsep : outerSep (R - r)) :
    0 < protonRadial i i r R := by
  rw [protonRadial_self hr hR hsep]
  exact div_pos (by norm_num) (mul_pos (outer_gamma_pos hsep) (pow_pos (sub_pos.mpr hR) 2))

theorem protonRadial_cross {i j : Fin 4} {r R : ℝ}
    (hij : i ≠ j) (hr : 0 < r) (hR : 0 < R) (hsep : outerSep (chord r R tetCos)) :
    protonRadial i j r R =
      -(r - R * tetCos) /
        (gammaSEqual (pairPhase (chord r R tetCos)) * chord r R tetCos ^ 3) := by
  have hu := tetU_dot_self i
  have hv := tetU_dot_self j
  have hc := tetU_dot_ne hij
  have hnn : 0 ≤ chordSq r R tetCos := (chordSq_pos_obtuse hr hR tetCos_neg.le).le
  have hnorm := vnorm_unit_chord hu hv hc hnn
  have hρ : 0 < chord r R tetCos := chord_pos_obtuse hr hR tetCos_neg.le
  have hγ : gammaSEqual (pairPhase (chord r R tetCos)) ≠ 0 := (outer_gamma_pos hsep).ne'
  have hden := den_ne hρ hγ
  rw [protonRadial, vdot_pairForce _ _ _ _ _ (den_of_norm hnorm hden), hnorm]
  have hdot : vdot (tetU i) (vsub (vsmul r (tetU i)) (vsmul R (tetU j))) =
      r - R * tetCos := by
    rw [vdot_sub, vdot_smul_right, vdot_smul_right, tetU_dot_self, tetU_dot_ne hij]
    ring
  rw [hdot]
  field_simp [hγ, hρ.ne']

theorem protonRadial_cross_neg {i j : Fin 4} {r R : ℝ}
    (hij : i ≠ j) (hr : 0 < r) (hR : 0 < R) (hsep : outerSep (chord r R tetCos)) :
    protonRadial i j r R < 0 := by
  rw [protonRadial_cross hij hr hR hsep]
  have hnum : 0 < r - R * tetCos := by
    have hneg : R * tetCos < 0 := mul_neg_of_pos_of_neg hR tetCos_neg
    linarith
  have hden : 0 < gammaSEqual (pairPhase (chord r R tetCos)) * chord r R tetCos ^ 3 :=
    mul_pos (outer_gamma_pos hsep) (pow_pos (chord_pos_obtuse hr hR tetCos_neg.le) 3)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden

theorem protonRadial_cross_eq {i j i' j' : Fin 4} {r R : ℝ}
    (hij : i ≠ j) (hij' : i' ≠ j') (hr : 0 < r) (hR : 0 < R)
    (hsep : outerSep (chord r R tetCos)) :
    protonRadial i j r R = protonRadial i' j' r R := by
  rw [protonRadial_cross hij hr hR hsep, protonRadial_cross hij' hr hR hsep]

def protonRadialSum (i : Fin 4) (r R : ℝ) (P : Finset (Fin 4)) : ℝ :=
  ∑ j ∈ P, protonRadial i j r R

def electronRadialSum (i : Fin 4) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, electronRadial i j r r

theorem nucleusRadial_eq {Z r : ℝ} {i i' : Fin 4} (hr : outerSep r) :
    nucleusRadial Z i r = nucleusRadial Z i' r := by
  have hformula (k : Fin 4) : nucleusRadial Z k r =
      -Z / (gammaSEqual (pairPhase r) * r ^ 2) := by
    have hu := tetU_dot_self k
    have hnorm : vnorm (vsub (vsmul r (tetU k)) (fun _ => 0)) = r := by
      have hsub : vsub (vsmul r (tetU k)) (fun _ => 0) = vsmul r (tetU k) := by
        funext t
        simp [vsub]
      rw [hsub, vnorm_smul, tetU_norm, mul_one, abs_of_pos hr.1]
    have hγ : gammaSEqual (pairPhase r) ≠ 0 := (outer_gamma_pos hr).ne'
    have hden := den_ne hr.1 hγ
    have hden' : gammaSEqual (pairPhase (vnorm (vsub (vsmul r (tetU k)) (fun _ => 0)))) *
        vnorm (vsub (vsmul r (tetU k)) (fun _ => 0)) ^ 3 ≠ 0 := by
      rw [hnorm]
      exact hden
    rw [nucleusRadial, vdot_pairForce _ _ _ _ _ hden', hnorm]
    have hdot : vdot (tetU k) (vsub (vsmul r (tetU k)) (fun _ => 0)) = r := by
      have hsub : vsub (vsmul r (tetU k)) (fun _ => 0) = vsmul r (tetU k) := by
        funext t
        simp [vsub]
      rw [hsub, vdot_smul_right, tetU_dot_self, mul_one]
    rw [hdot]
    field_simp [hγ, hr.1.ne']
  rw [hformula i, hformula i']

private theorem electronRadial_cross {i j : Fin 4} {r : ℝ}
    (hij : i ≠ j) (hr : 0 < r) (hsep : outerSep (chord r r tetCos)) :
    electronRadial i j r r =
      (r - r * tetCos) /
        (gammaSEqual (pairPhase (chord r r tetCos)) * chord r r tetCos ^ 3) := by
  have hu := tetU_dot_self i
  have hv := tetU_dot_self j
  have hc := tetU_dot_ne hij
  have hnn : 0 ≤ chordSq r r tetCos := (chordSq_pos_obtuse hr hr tetCos_neg.le).le
  have hnorm := vnorm_unit_chord hu hv hc hnn
  have hρ : 0 < chord r r tetCos := chord_pos_obtuse hr hr tetCos_neg.le
  have hγ : gammaSEqual (pairPhase (chord r r tetCos)) ≠ 0 := (outer_gamma_pos hsep).ne'
  have hden : gammaSEqual (pairPhase (vnorm (vsub (vsmul r (tetU i)) (vsmul r (tetU j))))) *
      vnorm (vsub (vsmul r (tetU i)) (vsmul r (tetU j))) ^ 3 ≠ 0 := by
    rw [hnorm]
    exact den_ne hρ hγ
  rw [electronRadial, vdot_pairForce _ _ _ _ _ hden, hnorm]
  have hdot : vdot (tetU i) (vsub (vsmul r (tetU i)) (vsmul r (tetU j))) =
      r - r * tetCos := by
    rw [vdot_sub, vdot_smul_right, vdot_smul_right, tetU_dot_self, tetU_dot_ne hij]
    ring
  rw [hdot]
  field_simp [hγ, hρ.ne']

private theorem electronRadialSum_eq {i i' : Fin 4} {r : ℝ}
    (hr : 0 < r) (hsep : outerSep (chord r r tetCos)) :
    electronRadialSum i r = electronRadialSum i' r := by
  have hconst (k : Fin 4) : electronRadialSum k r =
      3 * electronRadial 0 1 r r := by
    unfold electronRadialSum
    have hfun : ∀ j ∈ Finset.univ.erase k, electronRadial k j r r = electronRadial 0 1 r r := by
      intro j hj
      have hjne : j ≠ k := (mem_erase.mp hj).1
      rw [electronRadial_cross hjne.symm hr hsep, electronRadial_cross (by decide : (0 : Fin 4) ≠ 1)
        hr hsep]
    rw [sum_congr rfl hfun, sum_const, card_erase_of_mem (mem_univ k), card_univ]
    simp
  rw [hconst i, hconst i']

/-- At one common electron distance, an electron with a proton on its ray is
pushed outward more strongly than an electron with none. -/
theorem shared_outward_gt {Z r R : ℝ} {bond lone : Fin 4} {P : Finset (Fin 4)}
    (hr : outerSep r) (hR : r < R) (hown : outerSep (R - r))
    (hcross : outerSep (chord r R tetCos))
    (hbond : bond ∈ P) (hlone : lone ∉ P) :
    nucleusRadial Z lone r + electronRadialSum lone r + protonRadialSum lone r R P <
      nucleusRadial Z bond r + electronRadialSum bond r + protonRadialSum bond r R P := by
  have hr0 : 0 < r := hr.1
  have hR0 : 0 < R := lt_trans hr0 hR
  have hne : bond ≠ lone := by
    intro h
    apply hlone
    simpa [h] using hbond
  have hchord : outerSep (chord r r tetCos) := outerSep_tet_chord hr
  have hnuc := nucleusRadial_eq (Z := Z) (i := bond) (i' := lone) hr
  have hee := electronRadialSum_eq (i := bond) (i' := lone) hr0 hchord
  have hpro : protonRadialSum lone r R P < protonRadialSum bond r R P := by
    have hsplit : protonRadialSum bond r R P - protonRadialSum lone r R P =
        ∑ j ∈ P, (protonRadial bond j r R - protonRadial lone j r R) := by
      unfold protonRadialSum
      rw [sum_sub_distrib]
    have hsingle : ∑ j ∈ P, (protonRadial bond j r R - protonRadial lone j r R) =
        protonRadial bond bond r R - protonRadial lone bond r R := by
      refine sum_eq_single_of_mem bond hbond ?_
      intro j hj hjne
      have hjl : j ≠ lone := by
        intro h
        exact hlone (h ▸ hj)
      have hbb : protonRadial bond j r R = protonRadial lone j r R := by
        exact protonRadial_cross_eq hjne.symm hjl.symm hr0 hR0 hcross
      linarith
    rw [← sub_pos, hsplit, hsingle]
    have hQ : 0 < protonRadial bond bond r R := protonRadial_self_pos hr0 hR hown
    have hN : protonRadial lone bond r R < 0 :=
      protonRadial_cross_neg hne.symm hr0 hR0 hcross
    linarith
  linarith

/-! ### Tangential force -/

def eeForce (i j : Fin 4) (ri rj : ℝ) : Fin 3 → ℝ :=
  fun k => pairForce (-1) (-1) (vsmul ri (tetU i)) (vsmul rj (tetU j)) k

def eeTang (i j : Fin 4) (ri rj : ℝ) : Fin 3 → ℝ :=
  fun k => eeForce i j ri rj k - vdot (tetU i) (eeForce i j ri rj) * tetU i k

def peForce (i j : Fin 4) (r R : ℝ) : Fin 3 → ℝ :=
  fun k => pairForce (-1) 1 (vsmul r (tetU i)) (vsmul R (tetU j)) k

def peTang (i j : Fin 4) (r R : ℝ) : Fin 3 → ℝ :=
  fun k => peForce i j r R k - vdot (tetU i) (peForce i j r R) * tetU i k

def widenDir (i j : Fin 4) : Fin 3 → ℝ :=
  fun k => tetCos * tetU i k - tetU j k

def protonLever (r R : ℝ) : ℝ :=
  R / (gammaSEqual (pairPhase (chord r R tetCos)) * chord r R tetCos ^ 3)

private lemma vdot_ray_diff {i j : Fin 4} {r s : ℝ} (hij : i ≠ j) :
    vdot (tetU i) (vsub (vsmul r (tetU i)) (vsmul s (tetU j))) = r - s * tetCos := by
  rw [vdot_sub, vdot_smul_right, vdot_smul_right, tetU_dot_self, tetU_dot_ne hij]
  ring

theorem eeTang_eq {i j : Fin 4} {r s : ℝ}
    (hij : i ≠ j) (hr : 0 < r) (hs : 0 < s) (hsep : outerSep (chord r s tetCos)) :
    eeTang i j r s = vsmul (tangWeight r s tetCos) (widenDir i j) := by
  have hρ : 0 < chord r s tetCos := chord_pos_obtuse hr hs tetCos_neg.le
  have hγ : gammaSEqual (pairPhase (chord r s tetCos)) ≠ 0 := (outer_gamma_pos hsep).ne'
  have hnn : 0 ≤ chordSq r s tetCos := (chordSq_pos_obtuse hr hs tetCos_neg.le).le
  have hnorm := vnorm_unit_chord (tetU_dot_self i) (tetU_dot_self j) (tetU_dot_ne hij) hnn
  funext k
  have hden := den_ne hρ hγ
  have hF : eeForce i j r s k =
      (r * tetU i k - s * tetU j k) /
        (gammaSEqual (pairPhase (chord r s tetCos)) * chord r s tetCos ^ 3) := by
    unfold eeForce
    have hv : vnorm (vsub (vsmul r (tetU i)) (vsmul s (tetU j))) = chord r s tetCos := hnorm
    unfold pairForce
    rw [hv]
    field_simp [hγ, hρ.ne']
    simp only [vsmul]
  have hrad : vdot (tetU i) (eeForce i j r s) =
      (r - s * tetCos) /
        (gammaSEqual (pairPhase (chord r s tetCos)) * chord r s tetCos ^ 3) := by
    rw [show eeForce i j r s = fun t => pairForce (-1) (-1)
        (vsmul r (tetU i)) (vsmul s (tetU j)) t from rfl]
    rw [vdot_pairForce _ _ _ _ _ (den_of_norm hnorm hden), hnorm, vdot_ray_diff hij]
    field_simp [hγ, hρ.ne']
  unfold eeTang widenDir vsmul tangWeight
  rw [hF, hrad]
  field_simp [hγ, hρ.ne']
  ring

theorem peTang_eq {i j : Fin 4} {r R : ℝ}
    (hij : i ≠ j) (hr : 0 < r) (hR : 0 < R) (hsep : outerSep (chord r R tetCos)) :
    peTang i j r R = vsmul (-protonLever r R) (widenDir i j) := by
  have hρ : 0 < chord r R tetCos := chord_pos_obtuse hr hR tetCos_neg.le
  have hγ : gammaSEqual (pairPhase (chord r R tetCos)) ≠ 0 := (outer_gamma_pos hsep).ne'
  have hnn : 0 ≤ chordSq r R tetCos := (chordSq_pos_obtuse hr hR tetCos_neg.le).le
  have hnorm := vnorm_unit_chord (tetU_dot_self i) (tetU_dot_self j) (tetU_dot_ne hij) hnn
  funext k
  have hden := den_ne hρ hγ
  have hF : peForce i j r R k =
      -(r * tetU i k - R * tetU j k) /
        (gammaSEqual (pairPhase (chord r R tetCos)) * chord r R tetCos ^ 3) := by
    unfold peForce pairForce
    rw [hnorm]
    field_simp [hγ, hρ.ne']
    simp only [vsmul]
  have hrad : vdot (tetU i) (peForce i j r R) =
      -(r - R * tetCos) /
        (gammaSEqual (pairPhase (chord r R tetCos)) * chord r R tetCos ^ 3) := by
    rw [show peForce i j r R = fun t => pairForce (-1) 1
        (vsmul r (tetU i)) (vsmul R (tetU j)) t from rfl]
    rw [vdot_pairForce _ _ _ _ _ (den_of_norm hnorm hden), hnorm, vdot_ray_diff hij]
    field_simp [hγ, hρ.ne']
  unfold peTang widenDir vsmul protonLever
  rw [hF, hrad]
  field_simp [hγ, hρ.ne']
  ring

lemma vdot_widen {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    vdot (widenDir i j) (widenDir i k) = tetCos * (1 - tetCos) := by
  have hL : widenDir i j = vsub (vsmul tetCos (tetU i)) (tetU j) := by
    funext t
    simp [widenDir, vsub, vsmul]
  have hR : widenDir i k = vsub (vsmul tetCos (tetU i)) (tetU k) := by
    funext t
    simp [widenDir, vsub, vsmul]
  rw [hL, hR, vdot_sub_left, vdot_sub, vdot_sub]
  rw [vdot_smul_left, vdot_smul_right, vdot_smul_left, vdot_smul_right]
  rw [vdot_comm (tetU j) (tetU i), tetU_dot_self, tetU_dot_ne hij, tetU_dot_ne hik,
    tetU_dot_ne hjk]
  ring

lemma tet_widen_dot : tetCos * (1 - tetCos) = -4 / 9 := by
  unfold tetCos
  ring

/-- Tangential shift on ray `i` when the electron on `lone` moves from `r` to
`s` and the proton on `lone` is removed. -/
def loneShift (i lone : Fin 4) (r s R : ℝ) : Fin 3 → ℝ :=
  fun k => eeTang i lone r s k - eeTang i lone r r k - peTang i lone r R k

/-- Component of that shift along the direction that widens the angle with
`partner`. Negative means the bond angle is driven narrower. -/
def narrowComponent (i lone partner : Fin 4) (r s R : ℝ) : ℝ :=
  vdot (loneShift i lone r s R) (widenDir i partner)

theorem narrowComponent_formula {i lone partner : Fin 4} {r s R : ℝ}
    (hil : i ≠ lone) (hip : i ≠ partner) (hlp : lone ≠ partner)
    (hr : 0 < r) (hs : 0 < s) (hR : 0 < R)
    (hee_s : outerSep (chord r s tetCos)) (hee_r : outerSep (chord r r tetCos))
    (hpe : outerSep (chord r R tetCos)) :
    narrowComponent i lone partner r s R =
      -(4 / 9) * ((tangWeight r s tetCos - tangWeight r r tetCos) + protonLever r R) := by
  unfold narrowComponent loneShift
  have hsub : vdot (fun k => eeTang i lone r s k - eeTang i lone r r k - peTang i lone r R k)
      (widenDir i partner) =
      vdot (eeTang i lone r s) (widenDir i partner) -
        vdot (eeTang i lone r r) (widenDir i partner) -
        vdot (peTang i lone r R) (widenDir i partner) := by
    unfold vdot
    ring
  rw [hsub, eeTang_eq hil hr hs hee_s, eeTang_eq hil hr hr hee_r, peTang_eq hil hr hR hpe]
  rw [vdot_smul_left, vdot_smul_left, vdot_smul_left, vdot_widen hil hip hlp, tet_widen_dot]
  ring

theorem narrowComponent_neg {i lone partner : Fin 4} {r s R : ℝ}
    (hil : i ≠ lone) (hip : i ≠ partner) (hlp : lone ≠ partner)
    (hr : 0 < r) (hR : r < R) (hs : r / sqrt 2 ≤ s) (hsr : s < r)
    (hee_s : outerSep (chord r s tetCos)) (hee_r : outerSep (chord r r tetCos))
    (hpe : outerSep (chord r R tetCos)) :
    narrowComponent i lone partner r s R < 0 := by
  have hs0 : 0 < s := by
    have hsqrt : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
    exact lt_of_lt_of_le (div_pos hr hsqrt) hs
  have hR0 : 0 < R := lt_trans hr hR
  rw [narrowComponent_formula hil hip hlp hr hs0 hR0 hee_s hee_r hpe]
  have hw := tangWeight_gt_of_closer hr hs hsr tetCos_neg.le hee_s hee_r
  have hlev : 0 < protonLever r R := by
    unfold protonLever
    exact div_pos hR0 (mul_pos (outer_gamma_pos hpe)
      (pow_pos (chord_pos_obtuse hr hR0 tetCos_neg.le) 3))
  have hsum : 0 < tangWeight r s tetCos - tangWeight r r tetCos + protonLever r R := by
    linarith
  have hcoeff : -(4 / 9 : ℝ) < 0 := by norm_num
  exact mul_neg_of_neg_of_pos hcoeff hsum

theorem narrowComponent_congr {i lone lone' partner : Fin 4} {r s R : ℝ}
    (hil : i ≠ lone) (hil' : i ≠ lone') (hip : i ≠ partner)
    (hlp : lone ≠ partner) (hlp' : lone' ≠ partner)
    (hr : 0 < r) (hs : 0 < s) (hR : 0 < R)
    (hee_s : outerSep (chord r s tetCos)) (hee_r : outerSep (chord r r tetCos))
    (hpe : outerSep (chord r R tetCos)) :
    narrowComponent i lone partner r s R = narrowComponent i lone' partner r s R := by
  rw [narrowComponent_formula hil hip hlp hr hs hR hee_s hee_r hpe,
    narrowComponent_formula hil' hip hlp' hr hs hR hee_s hee_r hpe]

theorem narrow_two_eq_two {i lone lone' partner : Fin 4} {r s R : ℝ}
    (hil : i ≠ lone) (hil' : i ≠ lone') (hip : i ≠ partner)
    (hlp : lone ≠ partner) (hlp' : lone' ≠ partner)
    (hr : 0 < r) (hs : 0 < s) (hR : 0 < R)
    (hee_s : outerSep (chord r s tetCos)) (hee_r : outerSep (chord r r tetCos))
    (hpe : outerSep (chord r R tetCos)) :
    narrowComponent i lone partner r s R + narrowComponent i lone' partner r s R =
      2 * narrowComponent i lone partner r s R := by
  rw [narrowComponent_congr hil hil' hip hlp hlp' hr hs hR hee_s hee_r hpe]
  ring

lemma sum_widen_zero (i : Fin 4) (k : Fin 3) :
    ∑ j ∈ Finset.univ.erase i, widenDir i j k = 0 := by
  have hsum : ∑ j ∈ Finset.univ.erase i, widenDir i j k =
      (Finset.univ.erase i).card * (tetCos * tetU i k) -
        ∑ j ∈ Finset.univ.erase i, tetU j k := by
    unfold widenDir
    rw [sum_sub_distrib, sum_const]
    simp
  have hcard : (Finset.univ.erase i).card = 3 := by
    rw [card_erase_of_mem (mem_univ i), card_univ]
    rfl
  rw [hsum, hcard, sum_erase_tetU]
  have hcoef : (3 : ℝ) * tetCos + 1 = 0 := by
    unfold tetCos
    ring
  have hnat : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [hnat]
  linear_combination tetU i k * hcoef

theorem ee_equal_tang_zero {i : Fin 4} {r : ℝ}
    (hr : 0 < r) (hee : outerSep (chord r r tetCos)) (k : Fin 3) :
    ∑ j ∈ Finset.univ.erase i, eeTang i j r r k = 0 := by
  have hfun : ∀ j ∈ Finset.univ.erase i,
      eeTang i j r r k = tangWeight r r tetCos * widenDir i j k := by
    intro j hj
    have hjne : i ≠ j := (mem_erase.mp hj).1.symm
    have h := congrFun (eeTang_eq hjne hr hr hee) k
    simpa [vsmul] using h
  rw [sum_congr rfl hfun, ← mul_sum, sum_widen_zero, mul_zero]

theorem peTang_self_zero {i : Fin 4} {r R : ℝ}
    (_hr : 0 < r) (hR : r < R) (hsep : outerSep (R - r)) :
    peTang i i r R = fun _ => 0 := by
  funext k
  have hpos : 0 < R - r := sub_pos.mpr hR
  have hsub : vsub (vsmul r (tetU i)) (vsmul R (tetU i)) = vsmul (r - R) (tetU i) := by
    funext t
    simp [vsub, vsmul]
    ring
  have hnorm : vnorm (vsub (vsmul r (tetU i)) (vsmul R (tetU i))) = R - r := by
    rw [hsub, vnorm_smul, tetU_norm, mul_one, abs_of_neg (sub_neg.mpr hR)]
    linarith
  have hγ : gammaSEqual (pairPhase (R - r)) ≠ 0 := (outer_gamma_pos hsep).ne'
  have hden := den_ne hpos hγ
  have hF : peForce i i r R k =
      ((R - r) / (gammaSEqual (pairPhase (R - r)) * (R - r) ^ 3)) * tetU i k := by
    unfold peForce pairForce
    rw [hnorm]
    simp only [vsmul]
    field_simp [hγ, hpos.ne']
    ring
  have hrad : vdot (tetU i) (peForce i i r R) =
      (R - r) / (gammaSEqual (pairPhase (R - r)) * (R - r) ^ 3) := by
    rw [show peForce i i r R = fun t => pairForce (-1) 1
        (vsmul r (tetU i)) (vsmul R (tetU i)) t from rfl]
    rw [vdot_pairForce _ _ _ _ _ (den_of_norm hnorm hden), hnorm, hsub]
    rw [vdot_smul_right, tetU_dot_self, mul_one]
    field_simp [hγ, hpos.ne']
    ring
  unfold peTang
  rw [hF, hrad]
  ring

theorem pe_cross_tang_zero {i : Fin 4} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hcross : outerSep (chord r R tetCos)) (k : Fin 3) :
    ∑ j ∈ Finset.univ.erase i, peTang i j r R k = 0 := by
  have hfun : ∀ j ∈ Finset.univ.erase i,
      peTang i j r R k = -protonLever r R * widenDir i j k := by
    intro j hj
    have hjne : i ≠ j := (mem_erase.mp hj).1.symm
    have h := congrFun (peTang_eq hjne hr hR hcross) k
    simpa [vsmul] using h
  rw [sum_congr rfl hfun]
  have hpull : ∑ j ∈ Finset.univ.erase i, -protonLever r R * widenDir i j k =
      -protonLever r R * ∑ j ∈ Finset.univ.erase i, widenDir i j k := by
    rw [← mul_sum]
  rw [hpull, sum_widen_zero, mul_zero]

/-- Four electrons at one distance and four protons at one greater distance
exert no tangential force. -/
theorem tetra_equal_tang_zero {i : Fin 4} {r R : ℝ}
    (hr : 0 < r) (hR : r < R)
    (hee : outerSep (chord r r tetCos)) (hown : outerSep (R - r))
    (hcross : outerSep (chord r R tetCos)) (k : Fin 3) :
    (∑ j ∈ Finset.univ.erase i, eeTang i j r r k) +
        (∑ j ∈ Finset.univ, peTang i j r R k) = 0 := by
  have hown_zero : peTang i i r R k = 0 := by
    simpa using congrFun (peTang_self_zero hr hR hown) k
  have hsplit : ∑ j ∈ Finset.univ, peTang i j r R k =
      peTang i i r R k + ∑ j ∈ Finset.univ.erase i, peTang i j r R k := by
    have h := Finset.add_sum_erase Finset.univ (fun j => peTang i j r R k) (mem_univ i)
    linarith
  rw [hsplit, hown_zero, zero_add, ee_equal_tang_zero hr hee k,
    pe_cross_tang_zero hr (lt_trans hr hR) hcross k]
  ring

end

end DstDiophantine.Gravity
