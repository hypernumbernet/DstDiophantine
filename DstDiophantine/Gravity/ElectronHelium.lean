import DstDiophantine.Gravity.ElectronSquare
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Charge two, the one-center shell and the midplane pair

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. Nothing here produces a dissociation energy, a
bond length, or a four-electron dimer. The one-center shell of two is not a
zero of the signed force. No reversed-shell root is claimed except the absence
of the square. A square is an equilibrium only where both interference factors
are finite and nonzero; a node is not a balance.

## What is proved

* On the square, two nuclei of charge `Z > 0` with `Z ≠ 1` and two electrons
  are not an equilibrium wherever both interference factors are nonzero. The
  axial balance asks for the factor on the side to be `2√2 / Z` times the
  factor on the diagonal, and the cylindrical balance asks for `2√2 Z` times
  that factor.
* For `1 ≤ Z ≤ 2√2`, while the internuclear separation and the electron
  separation both lie in the outer well, the two forces do not vanish together
  at any ratio. Charge `1` is the proton pair already proved. Charge `2` lies
  in the interval.
* Opposite signs of those two factors likewise give no equilibrium, for every
  `Z > 0`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set

noncomputable def heliumAxial (Z ℓ R ρ : ℝ) : ℝ :=
  let rEp := sqrt ((R / 2) ^ 2 + ρ ^ 2)
  Z ^ 2 / (gammaSEqual (ℓ / (2 * R)) * R ^ 2) -
    Z * R / (gammaSEqual (ℓ / (2 * rEp)) * rEp ^ 3)

noncomputable def heliumRadial (Z ℓ R ρ : ℝ) : ℝ :=
  let rEe := 2 * ρ
  let rEp := sqrt ((R / 2) ^ 2 + ρ ^ 2)
  1 / (gammaSEqual (ℓ / (2 * rEe)) * rEe ^ 2) -
    (2 * Z * ρ) / (gammaSEqual (ℓ / (2 * rEp)) * rEp ^ 3)

lemma heliumAxial_one (ℓ R ρ : ℝ) : heliumAxial 1 ℓ R ρ = covalentAxial ℓ R ρ := by
  unfold heliumAxial covalentAxial
  ring

lemma heliumRadial_one (ℓ R ρ : ℝ) : heliumRadial 1 ℓ R ρ = covalentRadial ℓ R ρ := by
  unfold heliumRadial covalentRadial
  ring

lemma heliumAxial_square {Z ℓ R : ℝ} (hR : 0 < R) :
    heliumAxial Z ℓ R (R / 2) =
      (1 / R ^ 2) * (Z ^ 2 / gammaSEqual (ℓ / (2 * R)) -
        (2 * sqrt 2) * Z / gammaSEqual (sqrt 2 * (ℓ / (2 * R)))) := by
  unfold heliumAxial
  have hr := square_ep hR
  have hphase := square_side_phase (ℓ := ℓ) hR
  simp only [hr, hphase]
  have hs : sqrt 2 ≠ 0 := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [div_sqrt_two_cube]
  field_simp [hR.ne', hs]

lemma heliumRadial_square {Z ℓ R : ℝ} (hR : 0 < R) :
    heliumRadial Z ℓ R (R / 2) =
      (1 / R ^ 2) * (1 / gammaSEqual (ℓ / (2 * R)) -
        (2 * sqrt 2) * Z / gammaSEqual (sqrt 2 * (ℓ / (2 * R)))) := by
  unfold heliumRadial
  have hr := square_ep hR
  have hphase := square_side_phase (ℓ := ℓ) hR
  simp only [hr, hphase, show (2 : ℝ) * (R / 2) = R by ring]
  have hs : sqrt 2 ≠ 0 := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [div_sqrt_two_cube]
  field_simp [hR.ne', hs]

/-- The square asks for two different ratios unless the nuclear charge is one. -/
theorem helium_square_not_balance {Z ℓ R : ℝ} (hZ : 0 < Z) (hZ1 : Z ≠ 1) (hR : 0 < R)
    (hγ : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγs : gammaSEqual (sqrt 2 * (ℓ / (2 * R))) ≠ 0) :
    ¬ (heliumAxial Z ℓ R (R / 2) = 0 ∧ heliumRadial Z ℓ R (R / 2) = 0) := by
  rintro ⟨hA, hC⟩
  have hax := heliumAxial_square (Z := Z) (ℓ := ℓ) hR
  have hrad := heliumRadial_square (Z := Z) (ℓ := ℓ) hR
  rw [hax] at hA
  rw [hrad] at hC
  have hfac : (1 / R ^ 2 : ℝ) ≠ 0 := by positivity
  have hA0 : Z ^ 2 / gammaSEqual (ℓ / (2 * R)) -
      (2 * sqrt 2) * Z / gammaSEqual (sqrt 2 * (ℓ / (2 * R))) = 0 :=
    (mul_eq_zero.mp hA).resolve_left hfac
  have hC0 : 1 / gammaSEqual (ℓ / (2 * R)) -
      (2 * sqrt 2) * Z / gammaSEqual (sqrt 2 * (ℓ / (2 * R))) = 0 :=
    (mul_eq_zero.mp hC).resolve_left hfac
  set γ : ℝ := gammaSEqual (ℓ / (2 * R))
  set γs : ℝ := gammaSEqual (sqrt 2 * (ℓ / (2 * R)))
  have hZsq : Z ^ 2 = 1 := by
    have hside : γs = (2 * sqrt 2) * Z * γ := by
      have hC0' : 1 / γ = (2 * sqrt 2) * Z / γs := by
        simpa [γ, γs, sub_eq_zero] using hC0
      have hmul := congrArg (fun t => t * (γ * γs)) hC0'
      field_simp [hγ, hγs] at hmul
      linarith
    have hax' : Z ^ 2 / γ = (2 * sqrt 2) * Z / γs := by
      simpa [γ, γs, sub_eq_zero] using hA0
    rw [hside] at hax'
    have hnz : (2 * sqrt 2) * Z * γ ≠ 0 := by
      positivity
    have hmul := congrArg (fun t => t * (γ * ((2 * sqrt 2) * Z * γ))) hax'
    field_simp [hγ, hnz] at hmul
    linarith
  have hsq : Z = 1 ∨ Z = -1 := sq_eq_one_iff.mp hZsq
  rcases hsq with h1 | hneg
  · exact hZ1 h1
  · linarith

private lemma helium_cross_ne_of_axial {Z ℓ R ρ : ℝ} (hZ : Z ≠ 0) (hR : 0 < R)
    (hγR : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hA : heliumAxial Z ℓ R ρ = 0) :
    gammaSEqual (ℓ / (2 * sqrt ((R / 2) ^ 2 + ρ ^ 2))) ≠ 0 := by
  intro h0
  unfold heliumAxial at hA
  dsimp only at hA
  rw [h0] at hA
  simp only [zero_mul, div_zero, sub_zero] at hA
  have hdenR : gammaSEqual (ℓ / (2 * R)) * R ^ 2 ≠ 0 :=
    mul_ne_zero hγR (pow_ne_zero 2 hR.ne')
  exact div_ne_zero (pow_ne_zero 2 hZ) hdenR hA

/-- Vanishing of both forces forces the interference factors at the two
separations to stand in the ratio `Z² s³`. -/
theorem helium_gamma_ratio {Z ℓ R ρ : ℝ} (hZ : Z ≠ 0) (hR : 0 < R) (hρ : 0 < ρ)
    (hγR : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγee : gammaSEqual (ℓ / (2 * (2 * ρ))) ≠ 0)
    (hA : heliumAxial Z ℓ R ρ = 0) (hC : heliumRadial Z ℓ R ρ = 0) :
    gammaSEqual (ℓ / (2 * R)) / gammaSEqual (ℓ / (2 * (2 * ρ))) =
      Z ^ 2 * (2 * ρ / R) ^ 3 := by
  have hγep := helium_cross_ne_of_axial hZ hR hγR hA
  unfold heliumAxial at hA
  unfold heliumRadial at hC
  set rEp : ℝ := sqrt ((R / 2) ^ 2 + ρ ^ 2)
  set γR : ℝ := gammaSEqual (ℓ / (2 * R))
  set γee : ℝ := gammaSEqual (ℓ / (2 * (2 * ρ)))
  set γep : ℝ := gammaSEqual (ℓ / (2 * rEp))
  have hrEp : 0 < rEp := by
    dsimp [rEp]
    positivity
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  have hdenR : γR * R ^ 2 ≠ 0 := mul_ne_zero hγR hR2
  have hA' : Z ^ 2 / (γR * R ^ 2) = Z * R / (γep * rEp ^ 3) := by linarith
  have hdenEp : γep * rEp ^ 3 ≠ 0 := mul_ne_zero hγep (pow_ne_zero 3 hrEp.ne')
  have hcross : γep * rEp ^ 3 = γR * R ^ 3 / Z := by
    have hmul := congrArg (fun t => t * ((γR * R ^ 2) * (γep * rEp ^ 3))) hA'
    field_simp [hγR, hR.ne', hγep, hrEp.ne', hZ] at hmul
    have hZc : Z * (γep * rEp ^ 3) = γR * R ^ 3 := by linarith
    field_simp [hZ] at hZc ⊢
    linarith
  have hrEe : (2 : ℝ) * ρ ≠ 0 := mul_ne_zero (by norm_num) hρ.ne'
  have hC' : 1 / (γee * (2 * ρ) ^ 2) = 2 * Z * ρ / (γep * rEp ^ 3) := by linarith
  have hEe : γep * rEp ^ 3 = 2 * Z * ρ * γee * (2 * ρ) ^ 2 := by
    have hmul := congrArg (fun t => t * ((γee * (2 * ρ) ^ 2) * (γep * rEp ^ 3))) hC'
    field_simp [hγee, hρ.ne', hγep, hrEp.ne'] at hmul
    linarith
  have hEq : γR * R ^ 3 / Z = γee * (8 * Z * ρ ^ 3) := by
    calc
      γR * R ^ 3 / Z = γep * rEp ^ 3 := hcross.symm
      _ = 2 * Z * ρ * γee * (2 * ρ) ^ 2 := hEe
      _ = γee * (8 * Z * ρ ^ 3) := by ring
  have hR3 : γR * R ^ 3 = γee * (8 * Z ^ 2 * ρ ^ 3) := by
    have hmul := congrArg (fun t => t * Z) hEq
    field_simp [hZ] at hmul
    linarith
  have hdiv : γR / γee = Z ^ 2 * (2 * ρ / R) ^ 3 := by
    have hpow : (2 * ρ / R) ^ 3 = 8 * ρ ^ 3 / R ^ 3 := by
      field_simp [hR.ne']
      ring
    rw [hpow]
    have hR3ne : R ^ 3 ≠ 0 := pow_ne_zero 3 hR.ne'
    field_simp [hγee, hR3ne, hZ]
    linarith
  simpa [γR, γee] using hdiv

theorem helium_no_opposite_sign {Z ℓ R ρ : ℝ} (hZ : 0 < Z) (hR : 0 < R) (hρ : 0 < ρ)
    (hγR : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγee : gammaSEqual (ℓ / (2 * (2 * ρ))) ≠ 0)
    (hopp : gammaSEqual (ℓ / (2 * R)) * gammaSEqual (ℓ / (2 * (2 * ρ))) < 0) :
    ¬ (heliumAxial Z ℓ R ρ = 0 ∧ heliumRadial Z ℓ R ρ = 0) := by
  rintro ⟨hA, hC⟩
  have hratio := helium_gamma_ratio hZ.ne' hR hρ hγR hγee hA hC
  have hspos : 0 < Z ^ 2 * (2 * ρ / R) ^ 3 := by positivity
  have hquot : gammaSEqual (ℓ / (2 * R)) / gammaSEqual (ℓ / (2 * (2 * ρ))) < 0 :=
    div_neg_iff.mpr (mul_neg_iff.mp hopp)
  linarith

private lemma phase_lt_firstNode_of_pos {p : ℝ} (hpπ : p < π)
    (hγ : 0 < gammaSEqual p) : p < resonanceRoot1 := by
  by_contra h
  have hle : resonanceRoot1 ≤ p := le_of_not_gt h
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [← heq] at hγ
    linarith [resonanceRoot1_gammaSEqual_zero]
  · linarith [gammaSEqual_neg_right_of_first_node ⟨hlt, hpπ⟩, hγ]

private lemma amp_lt_two_sqrt {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 + s ^ 2) * sqrt (1 + s ^ 2) < 2 * sqrt 2 := by
  have h1 : 1 + s ^ 2 < 2 := by nlinarith
  have hpos : (0 : ℝ) < 1 + s ^ 2 := by nlinarith
  have hsqrt : sqrt (1 + s ^ 2) < sqrt 2 := sqrt_lt_sqrt (by linarith) h1
  exact mul_lt_mul h1 hsqrt.le (sqrt_pos.mpr hpos) (by norm_num)

private lemma evenInterval_outer {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) resonanceRoot1) :
    t ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
  obtain ⟨ht0, ht1⟩ := ht
  have htπ : t < π :=
    lt_trans ht1 (lt_trans resonanceRoot1_bounds.2 (by linarith [pi_gt_three]))
  constructor
  · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
    rw [hzero]
    exact ht0.le
  · have hzero : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
    rw [hzero, zero_add]
    exact htπ.le

/-- For every nuclear charge from `1` through `2√2`, the symmetric midplane
pair has no equilibrium while both separations lie in the outer well. -/
theorem pairCharge_no_outer {Z ℓ R ρ : ℝ} (hZlo : (1 : ℝ) ≤ Z) (hZhi : Z ≤ 2 * sqrt 2)
    (hℓ : 0 < ℓ) (hR : 0 < R) (hρ : 0 < ρ)
    (hRwell : ℓ / (2 * R) ∈ Ioo (0 : ℝ) resonanceRoot1)
    (hEwell : ℓ / (2 * (2 * ρ)) ∈ Ioo (0 : ℝ) resonanceRoot1) :
    ¬ (heliumAxial Z ℓ R ρ = 0 ∧ heliumRadial Z ℓ R ρ = 0) := by
  rcases eq_or_lt_of_le hZlo with hZ1 | hZgt
  · subst hZ1
    simpa [heliumAxial_one, heliumRadial_one] using
      no_midplane_outer_equilibrium hℓ hR hρ hRwell hEwell
  have hZpos : 0 < Z := lt_trans (by norm_num : (0 : ℝ) < 1) hZgt
  have hZ0 : Z ≠ 0 := hZpos.ne'
  rintro ⟨hA, hC⟩
  set x : ℝ := ℓ / (2 * R)
  set y : ℝ := ℓ / (2 * (2 * ρ))
  have hx : x ∈ Ioo (0 : ℝ) resonanceRoot1 := hRwell
  have hy : y ∈ Ioo (0 : ℝ) resonanceRoot1 := hEwell
  have hγx : gammaSEqual x ≠ 0 := (gammaSEqual_pos_of_lt_firstNode hx.1.le hx.2).ne'
  have hγy : gammaSEqual y ≠ 0 := (gammaSEqual_pos_of_lt_firstNode hy.1.le hy.2).ne'
  have hposx : 0 < gammaSEqual x := gammaSEqual_pos_of_lt_firstNode hx.1.le hx.2
  have hposy : 0 < gammaSEqual y := gammaSEqual_pos_of_lt_firstNode hy.1.le hy.2
  have hs : 2 * ρ / R = x / y := by
    dsimp [x, y]
    field_simp [hℓ.ne', hR.ne', hρ.ne']
  have hratio := helium_gamma_ratio (Z := Z) (ℓ := ℓ) (R := R) (ρ := ρ)
    hZ0 hR hρ hγx hγy hA hC
  have hcube : gammaSEqual x / gammaSEqual y = Z ^ 2 * (x / y) ^ 3 := by
    simpa [x, y, hs] using hratio
  have hxI := evenInterval_outer hx
  have hyI := evenInterval_outer hy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · -- Electrons closer than the nuclei: the axial balance asks for a larger
    -- factor on the shorter electron–nucleus separation.
    set rEp : ℝ := sqrt ((R / 2) ^ 2 + ρ ^ 2)
    set s : ℝ := x / y
    have hs0 : 0 < s := div_pos hx.1 hy.1
    have hs1 : s < 1 := (div_lt_one hy.1).mpr hlt
    have hrEp : 0 < rEp := by
      dsimp [rEp]
      positivity
    have hγep_ne := helium_cross_ne_of_axial (Z := Z) (ℓ := ℓ) (R := R) (ρ := ρ)
      hZ0 hR hγx hA
    unfold heliumAxial at hA
    have hA' : Z ^ 2 / (gammaSEqual x * R ^ 2) =
        Z * R / (gammaSEqual (ℓ / (2 * rEp)) * rEp ^ 3) := by
      simpa [x, rEp] using by linarith
    have hρs : ρ = s * R / 2 := by
      have hs' : 2 * ρ / R = s := hs
      field_simp [hR.ne'] at hs'
      linarith
    have hspos : (0 : ℝ) < 1 + s ^ 2 := by positivity
    have hsqrt_ne : sqrt (1 + s ^ 2) ≠ 0 := (sqrt_pos.mpr hspos).ne'
    have hrep : rEp = R * sqrt (1 + s ^ 2) / 2 := by
      have hr2 : rEp ^ 2 = (R / 2) ^ 2 + ρ ^ 2 := by
        dsimp [rEp]
        exact sq_sqrt (by positivity)
      have hsq : rEp ^ 2 = (R * sqrt (1 + s ^ 2) / 2) ^ 2 := by
        rw [hr2, hρs]
        have hL : (R / 2) ^ 2 + (s * R / 2) ^ 2 = (R ^ 2 / 4) * (1 + s ^ 2) := by ring
        have hRt : (R * sqrt (1 + s ^ 2) / 2) ^ 2 =
            (R ^ 2 / 4) * (sqrt (1 + s ^ 2)) ^ 2 := by ring
        rw [hL, hRt]
        rw [sq_sqrt hspos.le]
      exact (sq_eq_sq₀ hrEp.le (by positivity)).mp hsq
    have hscale : R / rEp = 2 / sqrt (1 + s ^ 2) := by
      rw [hrep]
      field_simp [hR.ne', hsqrt_ne]
    have hamp : (sqrt (1 + s ^ 2)) ^ 3 = (1 + s ^ 2) * sqrt (1 + s ^ 2) := by
      rw [pow_succ, sq_sqrt hspos.le]
    have hcube_scale : (R / rEp) ^ 3 = 8 / ((1 + s ^ 2) * sqrt (1 + s ^ 2)) := by
      rw [hscale, div_pow]
      have htwo : (2 : ℝ) ^ 3 = 8 := by norm_num
      rw [htwo, hamp]
    have hγquot : gammaSEqual (ℓ / (2 * rEp)) / gammaSEqual x =
        (R / rEp) ^ 3 / Z := by
      set γp : ℝ := gammaSEqual (ℓ / (2 * rEp))
      have hb : gammaSEqual x * R ^ 2 ≠ 0 := mul_ne_zero hγx (pow_ne_zero 2 hR.ne')
      have hd : γp * rEp ^ 3 ≠ 0 := mul_ne_zero hγep_ne (pow_ne_zero 3 hrEp.ne')
      have hmul := (div_eq_div_iff hb hd).mp (by simpa [γp] using hA')
      have hcross : Z * γp * rEp ^ 3 = gammaSEqual x * R ^ 3 := by
        apply mul_left_cancel₀ hZ0
        calc
          Z * (Z * γp * rEp ^ 3) = Z ^ 2 * (γp * rEp ^ 3) := by ring
          _ = (Z * R) * (gammaSEqual x * R ^ 2) := by simpa [mul_assoc] using hmul
          _ = Z * (gammaSEqual x * R ^ 3) := by ring
      have hpow : (R / rEp) ^ 3 = R ^ 3 / rEp ^ 3 := by field_simp [hR.ne', hrEp.ne']
      rw [hpow]
      field_simp [hposx.ne', hZ0, hrEp.ne']
      linarith
    rw [hcube_scale] at hγquot
    have hden_lt := amp_lt_two_sqrt hs0.le hs1
    have hlow : (2 * sqrt 2) / Z <
        8 / ((1 + s ^ 2) * sqrt (1 + s ^ 2)) / Z := by
      have hsq2 : (sqrt 2) ^ 2 = 2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hnum : (2 * sqrt 2) * (2 * sqrt 2) = 8 := by
        calc
          (2 * sqrt 2) * (2 * sqrt 2) = 4 * (sqrt 2) ^ 2 := by ring
          _ = 4 * 2 := by rw [hsq2]
          _ = 8 := by norm_num
      have hb : (2 : ℝ) * sqrt 2 ≠ 0 := by positivity
      have hid : (2 * sqrt 2) / Z = 8 / (2 * sqrt 2) / Z := by
        have hdiv : 8 / (2 * sqrt 2) = 2 * sqrt 2 := (div_eq_iff hb).mpr hnum.symm
        exact congrArg (fun t => t / Z) hdiv.symm
      rw [hid]
      refine div_lt_div_of_pos_right ?_ hZpos
      exact div_lt_div_of_pos_left (by norm_num) (by positivity) hden_lt
    have hge : (1 : ℝ) ≤ (2 * sqrt 2) / Z := by
      rw [one_le_div hZpos]
      exact hZhi
    have hbig : 1 < gammaSEqual (ℓ / (2 * rEp)) / gammaSEqual x := by
      rw [hγquot]
      exact lt_of_le_of_lt hge hlow
    have hγep : gammaSEqual x < gammaSEqual (ℓ / (2 * rEp)) := by
      have h' : 1 * gammaSEqual x < gammaSEqual (ℓ / (2 * rEp)) :=
        (lt_div_iff₀ hposx).mp hbig
      simpa using h'
    have hphase : ℓ / (2 * rEp) = x * (2 / sqrt (1 + s ^ 2)) := by
      have hxdef : x = ℓ / (2 * R) := rfl
      rw [hrep, hxdef]
      field_simp [hR.ne', hsqrt_ne]
    have hp_gt : x < ℓ / (2 * rEp) := by
      rw [hphase]
      refine lt_mul_of_one_lt_right hx.1 ?_
      rw [one_lt_div (sqrt_pos.mpr hspos)]
      rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact sqrt_lt_sqrt (by positivity) (by nlinarith : 1 + s ^ 2 < 2 ^ 2)
    have hp_lt_pi : ℓ / (2 * rEp) < π := by
      rw [hphase]
      have hxlt : x < 1 := lt_trans hx.2 resonanceRoot1_bounds.2
      have hcoef : 2 / sqrt (1 + s ^ 2) < 2 := by
        have hsqrt_gt : (1 : ℝ) < sqrt (1 + s ^ 2) := by
          have h1 : (1 : ℝ) ^ 2 < 1 + s ^ 2 := by
            rw [one_pow]
            linarith [sq_pos_of_pos hs0]
          exact (lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr h1
        rw [div_lt_iff₀ (sqrt_pos.mpr hspos)]
        calc
          (2 : ℝ) = 2 * 1 := by ring
          _ < 2 * sqrt (1 + s ^ 2) := mul_lt_mul_of_pos_left hsqrt_gt (by norm_num)
      have hprod : x * (2 / sqrt (1 + s ^ 2)) < 2 := by
        have hposc : 0 < 2 / sqrt (1 + s ^ 2) :=
          div_pos (by norm_num) (sqrt_pos.mpr hspos)
        calc
          x * (2 / sqrt (1 + s ^ 2)) < 1 * (2 / sqrt (1 + s ^ 2)) :=
            mul_lt_mul_of_pos_right hxlt hposc
          _ = 2 / sqrt (1 + s ^ 2) := by ring
          _ < 2 := hcoef
      linarith [pi_gt_three]
    have hγep_pos : 0 < gammaSEqual (ℓ / (2 * rEp)) := lt_trans hposx hγep
    have hplt := phase_lt_firstNode_of_pos hp_lt_pi hγep_pos
    have hpI := evenInterval_outer ⟨lt_trans hx.1 hp_gt, hplt⟩
    have hγlt : gammaSEqual (ℓ / (2 * rEp)) < gammaSEqual x :=
      strictAntiOn_gammaSEqual_even 0 hxI hpI hp_gt
    linarith
  · have hZsq : Z ^ 2 = 1 := by
      have hγeq : gammaSEqual x = gammaSEqual y := by simp [heq]
      rw [hγeq] at hcube
      have hleft : gammaSEqual y / gammaSEqual y = (1 : ℝ) := by
        field_simp [hposy.ne']
      have hright : (x / y) ^ 3 = 1 := by
        rw [heq]
        field_simp [hy.1.ne']
      have : (1 : ℝ) = Z ^ 2 * 1 := by simpa [hleft, hright] using hcube
      linarith
    have hsq : Z = 1 ∨ Z = -1 := sq_eq_one_iff.mp hZsq
    rcases hsq with h1 | hneg
    · exact (ne_of_gt hZgt) h1
    · linarith
  · have hγ : gammaSEqual x < gammaSEqual y :=
      strictAntiOn_gammaSEqual_even 0 hyI hxI hgt
    have hleft : gammaSEqual x / gammaSEqual y < 1 := by
      rw [div_lt_one hposy]
      exact hγ
    have ht1 : 1 < x / y := (one_lt_div hy.1).mpr hgt
    have hZ2 : (1 : ℝ) < Z ^ 2 := by nlinarith
    have hright : 1 < Z ^ 2 * (x / y) ^ 3 := by
      have hcu : (1 : ℝ) < (x / y) ^ 3 := by
        have hsq : 1 < (x / y) ^ 2 := by nlinarith
        nlinarith
      nlinarith
    linarith

/-- Two nuclei of charge two and two electrons have no equilibrium in the
outer well, at any ratio of the separations. -/
theorem helium_no_outer_equilibrium {ℓ R ρ : ℝ}
    (hℓ : 0 < ℓ) (hR : 0 < R) (hρ : 0 < ρ)
    (hRwell : ℓ / (2 * R) ∈ Ioo (0 : ℝ) resonanceRoot1)
    (hEwell : ℓ / (2 * (2 * ρ)) ∈ Ioo (0 : ℝ) resonanceRoot1) :
    ¬ (heliumAxial 2 ℓ R ρ = 0 ∧ heliumRadial 2 ℓ R ρ = 0) :=
  pairCharge_no_outer (by norm_num) (by nlinarith [one_lt_sqrt_two]) hℓ hR hρ hRwell hEwell

end Gravity

end DstDiophantine
