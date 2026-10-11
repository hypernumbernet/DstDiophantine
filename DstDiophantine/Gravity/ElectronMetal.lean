import DstDiophantine.Gravity.ElectronForce
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Free electrons among ions in the outer well

Lengths are in units of `ℓ` and forces in units of `k e²/ℓ²`. A point
charge `Q` (in units of `e`) at `c` acts on an electron at `p` with the
force `-(Q · 8x³/γ_s(x)) (p - c)`, where `x = 1/(2‖p - c‖)`. The radial
magnitude is `Q · 4x²/γ_s(x)`, the attraction-positive force of
`ElectronForce`.

## Paper boundary (do **not** claim)

No lattice sum over an infinite crystal is taken. No conductivity, no Fermi
surface, and no cohesive energy is derived. Screening is not introduced:
an ion is a point charge. The length `ℓ` is not derived.

## What is proved

* Along a line `p + t v`, the outward component `⟪F, v⟫` of the force of one
  point charge has an explicit derivative at `t = 0`.
* Summed over any orthonormal frame of three directions, that derivative is
  `Q · 16x⁴ cosh x sin x / γ_s(x)²`. For an ion (`Q > 0`) in the outer well
  this is strictly positive; for another electron (`Q = -1`) it is strictly
  negative. With `γ_s = 1` the same sum is zero.
* The outflow `16x⁴ cosh x sin x / γ_s²` is strictly increasing on the outer
  well.
* An electron in the outer well of ions of any positive charges has, in
  every orthonormal frame, a direction along which a displacement is pushed
  further by the ions.
* The same holds with further electrons, when every distance lies in the
  outer well, the ion charges are at least one, and each further electron is
  farther away than a distinct ion.
* At the centre of a regular octahedron, a cube, and a cuboctahedron of ions
  (any of the three charges may vanish), the force on an electron vanishes,
  and every displacement is pushed further, by the same amount in every
  direction. The same shells hold a positive ion at that centre: every
  displacement of the ion is restored.
-/

namespace DstDiophantine

namespace Gravity

open Real Set
open scoped RealInnerProductSpace

/-! ### Radial profile -/

/-- Attraction over distance, `8x³/γ_s(x)`, in units of `k e²/ℓ³`. -/
noncomputable def pullRate (x : ℝ) : ℝ :=
  8 * x ^ 3 / gammaSEqual x

/-- Derivative of `pullRate` in the phase. -/
noncomputable def pullRateDeriv (x : ℝ) : ℝ :=
  24 * x ^ 2 / gammaSEqual x + 16 * x ^ 3 * cosh x * sin x / gammaSEqual x ^ 2

/-- Outflow of one unit charge, `16x⁴ cosh x sin x / γ_s(x)²`. -/
noncomputable def ionOutflow (x : ℝ) : ℝ :=
  16 * x ^ 4 * cosh x * sin x / gammaSEqual x ^ 2

theorem pullRate_eq (x : ℝ) : pullRate x = 2 * x * pairAttraction x := by
  unfold pullRate pairAttraction
  ring

theorem hasDerivAt_pullRate {x : ℝ} (hγ : gammaSEqual x ≠ 0) :
    HasDerivAt pullRate (pullRateDeriv x) x := by
  unfold pullRate
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have hnum : HasDerivAt (fun y : ℝ => 8 * y ^ 3) (8 * (3 * x ^ 2)) x := h3.const_mul 8
  have hdiv := hnum.fun_div (hasDerivAt_gammaSEqual x) hγ
  refine hdiv.congr_deriv ?_
  unfold pullRateDeriv
  field_simp
  ring

/-- The phase-weighted derivative minus three times the rate is the outflow. -/
theorem pullRate_outflow {x : ℝ} (hγ : gammaSEqual x ≠ 0) :
    x * pullRateDeriv x - 3 * pullRate x = ionOutflow x := by
  unfold pullRateDeriv pullRate ionOutflow
  field_simp
  ring

/-- With `γ_s = 1` the rate is `8x³`, and the same combination vanishes. -/
theorem coulomb_outflow_zero (x : ℝ) :
    x * (24 * x ^ 2) - 3 * (8 * x ^ 3) = 0 := by
  ring

private theorem gammaSEqual_sq_pos {x : ℝ} (hγ : gammaSEqual x ≠ 0) :
    0 < gammaSEqual x ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hγ))

theorem ionOutflow_pos {x : ℝ} (hx0 : 0 < x) (hxπ : x < π) (hγ : gammaSEqual x ≠ 0) :
    0 < ionOutflow x := by
  unfold ionOutflow
  have hs := sin_pos_of_pos_of_lt_pi hx0 hxπ
  have hc := cosh_pos x
  have hx4 : 0 < x ^ 4 := pow_pos hx0 4
  have hnum : 0 < 16 * x ^ 4 * cosh x * sin x := by positivity
  exact div_pos hnum (gammaSEqual_sq_pos hγ)

private theorem outer_lt_one {x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1) : x < 1 :=
  lt_trans hx.2 resonanceRoot1_bounds.2

theorem ionOutflow_pos_outer {x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1) :
    0 < ionOutflow x :=
  ionOutflow_pos hx.1 (by linarith [outer_lt_one hx, pi_gt_three])
    (gammaSEqual_pos_left_of_first_node hx).ne'

/-- On the outer well the outflow strictly increases with the phase. -/
theorem ionOutflow_strictMonoOn_outer :
    StrictMonoOn ionOutflow (Ioo 0 resonanceRoot1) := by
  intro x hx y hy hxy
  have hy1 := outer_lt_one hy
  have hγx := gammaSEqual_pos_left_of_first_node hx
  have hγy := gammaSEqual_pos_left_of_first_node hy
  have hγlt : gammaSEqual y < gammaSEqual x := by
    have hxI : x ∈ Icc (0 : ℝ) π := ⟨hx.1.le, by linarith [pi_gt_three]⟩
    have hyI : y ∈ Icc (0 : ℝ) π := ⟨hy.1.le, by linarith [pi_gt_three]⟩
    exact strictAntiOn_gammaSEqual_even 0 (by simpa using hxI) (by simpa using hyI) hxy
  have hsin : sin x < sin y :=
    sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hx.1, pi_pos])
      (by linarith [pi_gt_three]) hxy
  have hsx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 (by linarith [pi_gt_three])
  have hcosh : cosh x < cosh y := by
    rw [cosh_lt_cosh, abs_of_pos hx.1, abs_of_pos hy.1]
    exact hxy
  have hpow : x ^ 4 < y ^ 4 := pow_lt_pow_left₀ hxy hx.1.le (by norm_num)
  have hcx := cosh_pos x
  have hx4 : 0 < x ^ 4 := pow_pos hx.1 4
  have hnum : 16 * x ^ 4 * cosh x * sin x < 16 * y ^ 4 * cosh y * sin y := by
    have h1 : x ^ 4 * cosh x < y ^ 4 * cosh y :=
      mul_lt_mul'' hpow hcosh hx4.le hcx.le
    have h2 : x ^ 4 * cosh x * sin x < y ^ 4 * cosh y * sin y :=
      mul_lt_mul'' h1 hsin (by positivity) hsx.le
    nlinarith
  have hden : gammaSEqual y ^ 2 < gammaSEqual x ^ 2 := by
    nlinarith
  have hnx : 0 < 16 * x ^ 4 * cosh x * sin x := by positivity
  unfold ionOutflow
  rw [div_lt_div_iff₀ (gammaSEqual_sq_pos hγx.ne') (gammaSEqual_sq_pos hγy.ne')]
  have hgy2 : 0 < gammaSEqual y ^ 2 := gammaSEqual_sq_pos hγy.ne'
  calc 16 * x ^ 4 * cosh x * sin x * gammaSEqual y ^ 2
      < 16 * y ^ 4 * cosh y * sin y * gammaSEqual y ^ 2 :=
        mul_lt_mul_of_pos_right hnum hgy2
    _ < 16 * y ^ 4 * cosh y * sin y * gammaSEqual x ^ 2 :=
        mul_lt_mul_of_pos_left hden (lt_trans hnx hnum)

/-! ### Forces in space -/

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Phase of a separation `w`, with `ℓ = 1`. -/
noncomputable def vecPhase (w : E) : ℝ :=
  1 / (2 * ‖w‖)

/-- Force on an electron at `p` from a point charge `Q` at `c`. -/
noncomputable def pointForce (Q : ℝ) (c p : E) : E :=
  -(Q * pullRate (vecPhase (p - c))) • (p - c)

/-- Derivative, along `v`, of the component along `v` of the force of a
point charge `Q` at separation `w`. Positive means the displacement is
pushed further. -/
noncomputable def lineStiff (Q : ℝ) (w v : E) : ℝ :=
  -(Q * (pullRate (vecPhase w) * ‖v‖ ^ 2 -
    pullRateDeriv (vecPhase w) * ⟪w, v⟫ ^ 2 / (2 * ‖w‖ ^ 3)))

omit [InnerProductSpace ℝ E] in
theorem ne_zero_of_vecPhase_pos {w : E} (h : 0 < vecPhase w) : w ≠ 0 := by
  intro hw
  rw [vecPhase, hw, norm_zero, mul_zero, div_zero] at h
  exact lt_irrefl _ h

theorem hasDerivAt_pointForce_line (Q : ℝ) {c p : E} (v : E) (hpc : p ≠ c)
    (hγ : gammaSEqual (vecPhase (p - c)) ≠ 0) :
    HasDerivAt (fun t : ℝ => ⟪pointForce Q c (p + t • v), v⟫)
      (lineStiff Q (p - c) v) 0 := by
  set w := p - c with hw
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hpc
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set q : ℝ → ℝ := fun t => ‖w‖ ^ 2 + (2 * ⟪w, v⟫ * t + ‖v‖ ^ 2 * t ^ 2) with hq
  have hnorm : ∀ t : ℝ, ‖w + t • v‖ = √(q t) := by
    intro t
    rw [← Real.sqrt_sq (norm_nonneg (w + t • v)), norm_add_sq_real, real_inner_smul_right,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    congr 1
    simp only [hq]
    ring
  have hfun : (fun t : ℝ => ⟪pointForce Q c (p + t • v), v⟫) =
      fun t => -(Q * pullRate ((2 * √(q t))⁻¹)) * (⟪w, v⟫ + t * ‖v‖ ^ 2) := by
    funext t
    have hsub : p + t • v - c = w + t • v := by rw [hw]; abel
    unfold pointForce vecPhase
    rw [hsub, real_inner_smul_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hnorm, one_div]
  rw [hfun]
  have hq0 : q 0 = ‖w‖ ^ 2 := by simp [hq]
  have hsq0 : √(q 0) = ‖w‖ := by rw [hq0, Real.sqrt_sq (norm_nonneg w)]
  have hqd : HasDerivAt q (2 * ⟪w, v⟫) 0 := by
    have h1 : HasDerivAt (fun y : ℝ => 2 * ⟪w, v⟫ * y) (2 * ⟪w, v⟫) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * ⟪w, v⟫)
    have h2 : HasDerivAt (fun y : ℝ => ‖v‖ ^ 2 * y ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_mul (‖v‖ ^ 2)
    have h3 := (h1.add h2).const_add (‖w‖ ^ 2)
    simpa [hq] using h3
  have hs := hqd.sqrt (by rw [hq0]; positivity)
  have h2s := hs.const_mul 2
  have h2s0 : 2 * √(q 0) ≠ 0 := by rw [hsq0]; positivity
  have hx := h2s.inv h2s0
  have hγ' : gammaSEqual ((2 * √(q 0))⁻¹) ≠ 0 := by
    rw [hsq0, ← one_div]
    exact hγ
  have hP0 := (hasDerivAt_pullRate hγ').comp 0 hx
  set D := pullRateDeriv ((2 * √(q 0))⁻¹) *
    (-(2 * (2 * ⟪w, v⟫ / (2 * √(q 0)))) / (2 * √(q 0)) ^ 2) with hD
  have hP : HasDerivAt (fun t : ℝ => pullRate ((2 * √(q t))⁻¹)) D 0 := hP0
  have hL : HasDerivAt (fun t : ℝ => ⟪w, v⟫ + t * ‖v‖ ^ 2) (‖v‖ ^ 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (‖v‖ ^ 2)).const_add ⟪w, v⟫
  have hN : HasDerivAt (fun t : ℝ => -(Q * pullRate ((2 * √(q t))⁻¹))) (-(Q * D)) 0 :=
    (hP.const_mul Q).neg
  have htot : HasDerivAt
      (fun t : ℝ => -(Q * pullRate ((2 * √(q t))⁻¹)) * (⟪w, v⟫ + t * ‖v‖ ^ 2))
      (-(Q * D) * (⟪w, v⟫ + 0 * ‖v‖ ^ 2) +
        -(Q * pullRate ((2 * √(q 0))⁻¹)) * ‖v‖ ^ 2) 0 :=
    hN.mul hL
  refine htot.congr_deriv ?_
  unfold lineStiff vecPhase
  rw [hD, hsq0]
  simp only [one_div, zero_mul, add_zero]
  field_simp
  ring

/-- Summed over an orthonormal frame, the line derivative is the charge
times the outflow. -/
theorem sum_lineStiff_basis (b : OrthonormalBasis (Fin 3) ℝ E) (Q : ℝ) {w : E}
    (hw : w ≠ 0) (hγ : gammaSEqual (vecPhase w) ≠ 0) :
    ∑ i, lineStiff Q w (b i) = Q * ionOutflow (vecPhase w) := by
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hn : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hpars : ∑ i, ⟪w, b i⟫ ^ 2 = ‖w‖ ^ 2 := b.sum_sq_inner_left w
  rw [Fin.sum_univ_three] at hpars
  rw [← pullRate_outflow hγ, Fin.sum_univ_three]
  unfold lineStiff
  simp only [hn, one_pow, mul_one]
  set A := pullRate (vecPhase w)
  set B := pullRateDeriv (vecPhase w)
  have hx : vecPhase w = 1 / (2 * ‖w‖) := rfl
  calc -(Q * (A - B * ⟪w, b 0⟫ ^ 2 / (2 * ‖w‖ ^ 3))) +
        -(Q * (A - B * ⟪w, b 1⟫ ^ 2 / (2 * ‖w‖ ^ 3))) +
        -(Q * (A - B * ⟪w, b 2⟫ ^ 2 / (2 * ‖w‖ ^ 3)))
      = -(Q * (3 * A - B * (⟪w, b 0⟫ ^ 2 + ⟪w, b 1⟫ ^ 2 + ⟪w, b 2⟫ ^ 2) /
          (2 * ‖w‖ ^ 3))) := by ring
    _ = -(Q * (3 * A - B * ‖w‖ ^ 2 / (2 * ‖w‖ ^ 3))) := by rw [hpars]
    _ = Q * (vecPhase w * B - 3 * A) := by
        rw [hx]
        field_simp
        ring

/-- Force on an electron at `p` from point charges `Z j` at `c j`. -/
noncomputable def ionsForce {ι : Type*} [Fintype ι] (c : ι → E) (Z : ι → ℝ) (p : E) : E :=
  ∑ j, pointForce (Z j) (c j) p

theorem hasDerivAt_ionsForce_line {ι : Type*} [Fintype ι] (c : ι → E) (Z : ι → ℝ)
    {p : E} (v : E) (hpc : ∀ j, p ≠ c j)
    (hγ : ∀ j, gammaSEqual (vecPhase (p - c j)) ≠ 0) :
    HasDerivAt (fun t : ℝ => ⟪ionsForce c Z (p + t • v), v⟫)
      (∑ j, lineStiff (Z j) (p - c j) v) 0 := by
  have hfun : (fun t : ℝ => ⟪ionsForce c Z (p + t • v), v⟫) =
      fun t => ∑ j, ⟪pointForce (Z j) (c j) (p + t • v), v⟫ := by
    funext t
    unfold ionsForce
    rw [sum_inner]
  rw [hfun]
  exact HasDerivAt.fun_sum fun j _ => hasDerivAt_pointForce_line (Z j) v (hpc j) (hγ j)

/-- Total force on an electron at `p` from ions `(c, Z)` and further
electrons at `e`. -/
noncomputable def metalForce {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → E) (Z : ι → ℝ) (e : κ → E) (p : E) : E :=
  ionsForce c Z p + ionsForce e (fun _ => -1) p

/-- Line derivative of the outward component of the total force. -/
noncomputable def metalStiff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → E) (Z : ι → ℝ) (e : κ → E) (p v : E) : ℝ :=
  ∑ j, lineStiff (Z j) (p - c j) v + ∑ k, lineStiff (-1) (p - e k) v

theorem hasDerivAt_metalForce_line {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → E) (Z : ι → ℝ) (e : κ → E) {p : E} (v : E)
    (hpc : ∀ j, p ≠ c j) (hpe : ∀ k, p ≠ e k)
    (hγc : ∀ j, gammaSEqual (vecPhase (p - c j)) ≠ 0)
    (hγe : ∀ k, gammaSEqual (vecPhase (p - e k)) ≠ 0) :
    HasDerivAt (fun t : ℝ => ⟪metalForce c Z e (p + t • v), v⟫)
      (metalStiff c Z e p v) 0 := by
  have hfun : (fun t : ℝ => ⟪metalForce c Z e (p + t • v), v⟫) =
      fun t => ⟪ionsForce c Z (p + t • v), v⟫ +
        ⟪ionsForce e (fun _ => -1) (p + t • v), v⟫ := by
    funext t
    unfold metalForce
    rw [inner_add_left]
  rw [hfun]
  exact (hasDerivAt_ionsForce_line c Z v hpc hγc).add
    (hasDerivAt_ionsForce_line e (fun _ => -1) v hpe hγe)

/-- In any orthonormal frame the three line derivatives sum to the ion
outflow minus the electron outflow. -/
theorem sum_metalStiff_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis (Fin 3) ℝ E) (c : ι → E) (Z : ι → ℝ) (e : κ → E) {p : E}
    (hpc : ∀ j, p ≠ c j) (hpe : ∀ k, p ≠ e k)
    (hγc : ∀ j, gammaSEqual (vecPhase (p - c j)) ≠ 0)
    (hγe : ∀ k, gammaSEqual (vecPhase (p - e k)) ≠ 0) :
    ∑ i, metalStiff c Z e p (b i) =
      ∑ j, Z j * ionOutflow (vecPhase (p - c j)) -
        ∑ k, ionOutflow (vecPhase (p - e k)) := by
  unfold metalStiff
  have e1 : ∑ i, ∑ j, lineStiff (Z j) (p - c j) (b i) =
      ∑ j, Z j * ionOutflow (vecPhase (p - c j)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ =>
      sum_lineStiff_basis b (Z j) (sub_ne_zero.mpr (hpc j)) (hγc j)
  have e2 : ∑ i, ∑ k, lineStiff (-1) (p - e k) (b i) =
      -∑ k, ionOutflow (vecPhase (p - e k)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_lineStiff_basis b (-1) (sub_ne_zero.mpr (hpe k)) (hγe k)]
    ring
  rw [Finset.sum_add_distrib, e1, e2]
  ring

/-- The ions win against the further electrons once each electron is
farther away than a distinct ion of charge at least one. -/
theorem outflow_balance_pos {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (x : ι → ℝ) (y : κ → ℝ) (Z : ι → ℝ) (hZ : ∀ j, 1 ≤ Z j)
    (hx : ∀ j, x j ∈ Ioo 0 resonanceRoot1) (hy : ∀ k, y k ∈ Ioo 0 resonanceRoot1)
    (σ : κ → ι) (hσ : Function.Injective σ) (hclose : ∀ k, y k < x (σ k)) :
    0 < ∑ j, Z j * ionOutflow (x j) - ∑ k, ionOutflow (y k) := by
  classical
  have hpos : ∀ j, 0 < ionOutflow (x j) := fun j => ionOutflow_pos_outer (hx j)
  have hZsum : ∑ j, ionOutflow (x j) ≤ ∑ j, Z j * ionOutflow (x j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    nlinarith [hpos j, hZ j]
  have himage : ∑ k, ionOutflow (x (σ k)) ≤ ∑ j, ionOutflow (x j) := by
    rw [← Finset.sum_image (f := fun j => ionOutflow (x j))
      (fun a _ b _ h => hσ h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun j _ _ => (hpos j).le
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have hzero : ∑ k, ionOutflow (y k) = 0 := Finset.sum_of_isEmpty _
    have hion : 0 < ∑ j, ionOutflow (x j) :=
      Finset.sum_pos (fun j _ => hpos j) Finset.univ_nonempty
    linarith
  · have hlt : ∑ k, ionOutflow (y k) < ∑ k, ionOutflow (x (σ k)) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ =>
        ionOutflow_strictMonoOn_outer (hy k) (hx (σ k)) (hclose k)
    linarith

/-- A free electron: in every orthonormal frame some direction pushes a
displacement further, so no point of the outer well holds the electron. -/
theorem free_electron_pushed {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (b : OrthonormalBasis (Fin 3) ℝ E) (c : ι → E) (Z : ι → ℝ) (e : κ → E) (p : E)
    (hZ : ∀ j, 1 ≤ Z j)
    (hxc : ∀ j, vecPhase (p - c j) ∈ Ioo 0 resonanceRoot1)
    (hxe : ∀ k, vecPhase (p - e k) ∈ Ioo 0 resonanceRoot1)
    (σ : κ → ι) (hσ : Function.Injective σ)
    (hclose : ∀ k, vecPhase (p - e k) < vecPhase (p - c (σ k))) :
    ∃ i, 0 < metalStiff c Z e p (b i) ∧
      HasDerivAt (fun t : ℝ => ⟪metalForce c Z e (p + t • b i), b i⟫)
        (metalStiff c Z e p (b i)) 0 := by
  have hpc : ∀ j, p ≠ c j := fun j =>
    sub_ne_zero.mp (ne_zero_of_vecPhase_pos (hxc j).1)
  have hpe : ∀ k, p ≠ e k := fun k =>
    sub_ne_zero.mp (ne_zero_of_vecPhase_pos (hxe k).1)
  have hγc : ∀ j, gammaSEqual (vecPhase (p - c j)) ≠ 0 := fun j =>
    (gammaSEqual_pos_left_of_first_node (hxc j)).ne'
  have hγe : ∀ k, gammaSEqual (vecPhase (p - e k)) ≠ 0 := fun k =>
    (gammaSEqual_pos_left_of_first_node (hxe k)).ne'
  have hsum : 0 < ∑ i, metalStiff c Z e p (b i) := by
    rw [sum_metalStiff_basis b c Z e hpc hpe hγc hγe]
    exact outflow_balance_pos _ _ Z hZ hxc hxe σ hσ hclose
  obtain ⟨i, hi⟩ : ∃ i, 0 < metalStiff c Z e p (b i) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hcon i
    linarith
  exact ⟨i, hi, hasDerivAt_metalForce_line c Z e (b i) hpc hpe hγc hγe⟩

/-- Ions alone, of any positive charges: in every orthonormal frame some
direction pushes a displacement of the electron further. -/
theorem ions_alone_pushed {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis (Fin 3) ℝ E) (c : ι → E) (Z : ι → ℝ) (p : E)
    (hZ : ∀ j, 0 < Z j) (hxc : ∀ j, vecPhase (p - c j) ∈ Ioo 0 resonanceRoot1) :
    ∃ i, 0 < ∑ j, lineStiff (Z j) (p - c j) (b i) ∧
      HasDerivAt (fun t : ℝ => ⟪ionsForce c Z (p + t • b i), b i⟫)
        (∑ j, lineStiff (Z j) (p - c j) (b i)) 0 := by
  have hpc : ∀ j, p ≠ c j := fun j =>
    sub_ne_zero.mp (ne_zero_of_vecPhase_pos (hxc j).1)
  have hγc : ∀ j, gammaSEqual (vecPhase (p - c j)) ≠ 0 := fun j =>
    (gammaSEqual_pos_left_of_first_node (hxc j)).ne'
  have hsum : 0 < ∑ i, ∑ j, lineStiff (Z j) (p - c j) (b i) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j _ =>
      sum_lineStiff_basis b (Z j) (sub_ne_zero.mpr (hpc j)) (hγc j)]
    exact Finset.sum_pos (fun j _ => mul_pos (hZ j) (ionOutflow_pos_outer (hxc j)))
      Finset.univ_nonempty
  obtain ⟨i, hi⟩ : ∃ i, 0 < ∑ j, lineStiff (Z j) (p - c j) (b i) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hcon i
    linarith
  exact ⟨i, hi, hasDerivAt_ionsForce_line c Z (b i) hpc hγc⟩

/-! ### Octahedral and cubic sites -/

/-- Separations of equal length whose second moment is isotropic. -/
theorem sum_lineStiff_isotropic {ι : Type*} [Fintype ι] (Q : ℝ) (w : ι → E) {r : ℝ}
    (v : E) (hr : ∀ j, ‖w j‖ = r) (hr0 : 0 < r)
    (hγ : gammaSEqual (1 / (2 * r)) ≠ 0)
    (hiso : ∑ j, ⟪w j, v⟫ ^ 2 = (Fintype.card ι : ℝ) * r ^ 2 / 3 * ‖v‖ ^ 2) :
    ∑ j, lineStiff Q (w j) v =
      (Fintype.card ι : ℝ) / 3 * Q * ionOutflow (1 / (2 * r)) * ‖v‖ ^ 2 := by
  have hphase : ∀ j, vecPhase (w j) = 1 / (2 * r) := fun j => by
    unfold vecPhase
    rw [hr j]
  have hterm : ∀ j, lineStiff Q (w j) v =
      -(Q * pullRate (1 / (2 * r)) * ‖v‖ ^ 2) +
        Q * pullRateDeriv (1 / (2 * r)) / (2 * r ^ 3) * ⟪w j, v⟫ ^ 2 := fun j => by
    unfold lineStiff
    rw [hphase j, hr j]
    ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, hiso, ← pullRate_outflow hγ]
  field_simp
  ring

private def sgn (s : Bool) : ℝ := if s then 1 else -1

private theorem sgn_true : sgn true = 1 := rfl

private theorem sgn_false : sgn false = -1 := rfl

private theorem sgn_sq (s : Bool) : sgn s ^ 2 = 1 := by
  cases s <;> simp [sgn]

/-- Six ions at `p ± a bᵢ`. -/
noncomputable def octaSite (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) (a : ℝ) :
    Fin 3 × Bool → E :=
  fun js => p + (sgn js.2 * a) • b js.1

/-- Eight ions at `p + h (±b₀ ± b₁ ± b₂)`. -/
noncomputable def cubeSite (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) (h : ℝ) :
    Bool × Bool × Bool → E :=
  fun s => p + h • (sgn s.1 • b 0 + sgn s.2.1 • b 1 + sgn s.2.2 • b 2)

private theorem basis_inner (b : OrthonormalBasis (Fin 3) ℝ E) (i j : Fin 3) :
    ⟪b i, b j⟫ = if i = j then 1 else 0 :=
  (orthonormal_iff_ite.mp b.orthonormal) i j

private theorem parseval3 (b : OrthonormalBasis (Fin 3) ℝ E) (v : E) :
    ⟪b 0, v⟫ ^ 2 + ⟪b 1, v⟫ ^ 2 + ⟪b 2, v⟫ ^ 2 = ‖v‖ ^ 2 := by
  have h := b.sum_sq_inner_right v
  rwa [Fin.sum_univ_three] at h

theorem octaSite_sep (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {a : ℝ} (ha : 0 < a)
    (v : E) :
    (∀ js, ‖p - octaSite b p a js‖ = a) ∧
      (∑ js, ⟪p - octaSite b p a js, v⟫ ^ 2 =
        (Fintype.card (Fin 3 × Bool) : ℝ) * a ^ 2 / 3 * ‖v‖ ^ 2) ∧
      (∑ js, (p - octaSite b p a js) = 0) := by
  have hsub : ∀ js : Fin 3 × Bool, p - octaSite b p a js = -((sgn js.2 * a) • b js.1) :=
    fun js => by unfold octaSite; abel
  refine ⟨fun js => ?_, ?_, ?_⟩
  · rw [hsub, norm_neg, norm_smul, b.orthonormal.1 js.1, mul_one, Real.norm_eq_abs,
      abs_mul, abs_of_pos ha]
    cases js.2 <;> simp [sgn]
  · simp only [hsub, inner_neg_left, neg_sq, real_inner_smul_left, mul_pow, sgn_sq,
      one_mul]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Fin.sum_univ_three]
    have hp := parseval3 b v
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast
    linear_combination 2 * a ^ 2 * hp
  · simp only [hsub, Finset.sum_neg_distrib, neg_eq_zero]
    rw [Fintype.sum_prod_type]
    simp [sgn]

theorem cubeSite_sep (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    (v : E) :
    (∀ s, ‖p - cubeSite b p h s‖ = h * √3) ∧
      (∑ s, ⟪p - cubeSite b p h s, v⟫ ^ 2 =
        (Fintype.card (Bool × Bool × Bool) : ℝ) * (h * √3) ^ 2 / 3 * ‖v‖ ^ 2) ∧
      (∑ s, (p - cubeSite b p h s) = 0) := by
  have hsub : ∀ s : Bool × Bool × Bool, p - cubeSite b p h s =
      -(h • (sgn s.1 • b 0 + sgn s.2.1 • b 1 + sgn s.2.2 • b 2)) :=
    fun s => by unfold cubeSite; abel
  have hinner : ∀ (s : Bool × Bool × Bool) (u : E),
      ⟪h • (sgn s.1 • b 0 + sgn s.2.1 • b 1 + sgn s.2.2 • b 2), u⟫ =
        h * (sgn s.1 * ⟪b 0, u⟫ + sgn s.2.1 * ⟪b 1, u⟫ + sgn s.2.2 * ⟪b 2, u⟫) :=
    fun s u => by
      simp only [real_inner_smul_left, inner_add_left]
  refine ⟨fun s => ?_, ?_, ?_⟩
  · rw [hsub, norm_neg]
    set u := h • (sgn s.1 • b 0 + sgn s.2.1 • b 1 + sgn s.2.2 • b 2)
    have hu : ∀ i, ⟪u, b i⟫ = h * (sgn s.1 * ⟪b 0, b i⟫ + sgn s.2.1 * ⟪b 1, b i⟫ +
        sgn s.2.2 * ⟪b 2, b i⟫) := fun i => hinner s (b i)
    have hsq : ‖u‖ ^ 2 = 3 * h ^ 2 := by
      rw [← b.sum_sq_inner_left u, Fin.sum_univ_three, hu 0, hu 1, hu 2]
      simp only [basis_inner, Fin.ext_iff, Fin.isValue, Fin.val_zero, Fin.val_one,
        Fin.val_two]
      norm_num
      linear_combination h ^ 2 * sgn_sq s.1 + h ^ 2 * sgn_sq s.2.1 + h ^ 2 * sgn_sq s.2.2
    have h3 : (h * √3) ^ 2 = 3 * h ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    have hpos : 0 ≤ h * √3 := by positivity
    rw [← h3] at hsq
    exact (pow_left_inj₀ (norm_nonneg u) hpos (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  · simp only [hsub, inner_neg_left, neg_sq, hinner]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, sgn_true, sgn_false]
    have hp := parseval3 b v
    simp only [Fintype.card_prod, Fintype.card_bool]
    have h3 : (h * √3) ^ 2 = 3 * h ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    rw [h3]
    push_cast
    linear_combination 8 * h ^ 2 * hp
  · simp only [hsub, Finset.sum_neg_distrib, neg_eq_zero, ← Finset.smul_sum]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, sgn_true, sgn_false]
    module

/-- Twelve ions at `p + g (±bⱼ ± bₖ)`, `j ≠ k`. -/
noncomputable def cuboSite (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) (g : ℝ) :
    Fin 3 × Bool × Bool → E :=
  fun x => p + g • (sgn x.2.1 • b (x.1 + 1) + sgn x.2.2 • b (x.1 + 2))

private theorem norm_two_axes (b : OrthonormalBasis (Fin 3) ℝ E) {j k : Fin 3} (hjk : j ≠ k)
    {g : ℝ} (hg : 0 < g) (s t : Bool) :
    ‖g • (sgn s • b j + sgn t • b k)‖ = g * √2 := by
  have hjj : ⟪b j, b j⟫ = 1 := by simp
  have hkk : ⟪b k, b k⟫ = 1 := by simp
  have hjk' : ⟪b j, b k⟫ = 0 := by simp [hjk]
  have hkj : ⟪b k, b j⟫ = 0 := by simp [Ne.symm hjk]
  have hsq : ‖g • (sgn s • b j + sgn t • b k)‖ ^ 2 = (g * √2) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hjj, hkk, hjk', hkj]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linear_combination g ^ 2 * sgn_sq s + g ^ 2 * sgn_sq t
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq

theorem cuboSite_sep (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {g : ℝ} (hg : 0 < g)
    (v : E) :
    (∀ x, ‖p - cuboSite b p g x‖ = g * √2) ∧
      (∑ x, ⟪p - cuboSite b p g x, v⟫ ^ 2 =
        (Fintype.card (Fin 3 × Bool × Bool) : ℝ) * (g * √2) ^ 2 / 3 * ‖v‖ ^ 2) ∧
      (∑ x, (p - cuboSite b p g x) = 0) := by
  have hsub : ∀ x : Fin 3 × Bool × Bool, p - cuboSite b p g x =
      -(g • (sgn x.2.1 • b (x.1 + 1) + sgn x.2.2 • b (x.1 + 2))) :=
    fun x => by unfold cuboSite; abel
  have f01 : (0 : Fin 3) + 1 = 1 := by decide
  have f02 : (0 : Fin 3) + 2 = 2 := by decide
  have f11 : (1 : Fin 3) + 1 = 2 := by decide
  have f12 : (1 : Fin 3) + 2 = 0 := by decide
  have f21 : (2 : Fin 3) + 1 = 0 := by decide
  have f22 : (2 : Fin 3) + 2 = 1 := by decide
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [hsub, norm_neg]
    have hne : x.1 + 1 ≠ x.1 + 2 := by
      intro h
      have := add_left_cancel h
      exact absurd this (by decide)
    exact norm_two_axes b hne hg x.2.1 x.2.2
  · simp only [hsub, inner_neg_left, neg_sq, real_inner_smul_left, inner_add_left]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, sgn_true,
      sgn_false, f01, f02, f11, f12, f21, f22]
    have hp := parseval3 b v
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    have h2 : (g * √2) ^ 2 = 2 * g ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [h2]
    push_cast
    linear_combination 8 * g ^ 2 * hp
  · simp only [hsub, Finset.sum_neg_distrib, neg_eq_zero, ← Finset.smul_sum]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, sgn_true,
      sgn_false, f01, f02, f11, f12, f21, f22]
    module

/-- A shell of equal ions about `p`, with zero vector sum, exerts no force at `p`. -/
theorem shell_force_zero {V : Type*} [Fintype V] (Q : ℝ) (f : V → E) (p : E) {r : ℝ}
    (hr : ∀ j, ‖p - f j‖ = r) (hsum : ∑ j, (p - f j) = 0) :
    ∑ j, pointForce Q (f j) p = 0 := by
  unfold pointForce vecPhase
  simp only [hr]
  rw [← Finset.smul_sum, hsum, smul_zero]

/-- Ions on a regular octahedron (radius `a`), a cube (half-edge `h`), and a
cuboctahedron (`g (±bⱼ ± bₖ)`), all centred at `p`. -/
noncomputable def cubicSite (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) (a h g : ℝ) :
    ((Fin 3 × Bool) ⊕ (Bool × Bool × Bool)) ⊕ (Fin 3 × Bool × Bool) → E
  | Sum.inl (Sum.inl js) => octaSite b p a js
  | Sum.inl (Sum.inr s) => cubeSite b p h s
  | Sum.inr x => cuboSite b p g x

/-- Charges `Zo`, `Zc`, `Zq` on the three shells. -/
def cubicCharge (Zo Zc Zq : ℝ) :
    ((Fin 3 × Bool) ⊕ (Bool × Bool × Bool)) ⊕ (Fin 3 × Bool × Bool) → ℝ
  | Sum.inl (Sum.inl _) => Zo
  | Sum.inl (Sum.inr _) => Zc
  | Sum.inr _ => Zq

/-- Isotropic stiffness of the three shells, per unit `‖v‖²`. -/
noncomputable def cubicStiff (Zo Zc Zq a h g : ℝ) : ℝ :=
  2 * Zo * ionOutflow (1 / (2 * a)) + 8 / 3 * Zc * ionOutflow (1 / (2 * (h * √3))) +
    4 * Zq * ionOutflow (1 / (2 * (g * √2)))

private theorem pos_of_phase_mem {r : ℝ} (hr : 1 / (2 * r) ∈ Ioo 0 resonanceRoot1) :
    0 < r := by
  have := hr.1
  rw [one_div, inv_pos] at this
  linarith

/-- At the centre of a regular octahedron, a cube, and a cuboctahedron of ions
(any of the charges may vanish), the force on an electron is zero, and the
line derivative along every `v` is `cubicStiff · ‖v‖² > 0`. -/
theorem cubic_center_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E)
    {a h g Zo Zc Zq : ℝ}
    (ho : 1 / (2 * a) ∈ Ioo 0 resonanceRoot1)
    (hc : 1 / (2 * (h * √3)) ∈ Ioo 0 resonanceRoot1)
    (hq : 1 / (2 * (g * √2)) ∈ Ioo 0 resonanceRoot1)
    (hZo : 0 ≤ Zo) (hZc : 0 ≤ Zc) (hZq : 0 ≤ Zq) (hZ : 0 < Zo + Zc + Zq) :
    ionsForce (cubicSite b p a h g) (cubicCharge Zo Zc Zq) p = 0 ∧
      0 < cubicStiff Zo Zc Zq a h g ∧
      ∀ v : E, HasDerivAt
          (fun t : ℝ => ⟪ionsForce (cubicSite b p a h g) (cubicCharge Zo Zc Zq)
            (p + t • v), v⟫)
          (cubicStiff Zo Zc Zq a h g * ‖v‖ ^ 2) 0 := by
  have ha : 0 < a := pos_of_phase_mem ho
  have hh3 : 0 < h * √3 := pos_of_phase_mem hc
  have hg2 : 0 < g * √2 := pos_of_phase_mem hq
  have hh : 0 < h := pos_of_mul_pos_left hh3 (by positivity)
  have hg : 0 < g := pos_of_mul_pos_left hg2 (by positivity)
  have hγo : gammaSEqual (1 / (2 * a)) ≠ 0 := (gammaSEqual_pos_left_of_first_node ho).ne'
  have hγc : gammaSEqual (1 / (2 * (h * √3))) ≠ 0 :=
    (gammaSEqual_pos_left_of_first_node hc).ne'
  have hγq : gammaSEqual (1 / (2 * (g * √2))) ≠ 0 :=
    (gammaSEqual_pos_left_of_first_node hq).ne'
  have hO := fun v => octaSite_sep b p ha v
  have hC := fun v => cubeSite_sep b p hh v
  have hQ := fun v => cuboSite_sep b p hg v
  have hnorm : ∀ j, ‖p - cubicSite b p a h g j‖ =
      match j with
      | Sum.inl (Sum.inl _) => a
      | Sum.inl (Sum.inr _) => h * √3
      | Sum.inr _ => g * √2 := by
    rintro ((js | s) | x)
    · exact (hO 0).1 js
    · exact (hC 0).1 s
    · exact (hQ 0).1 x
  have hsep_ne : ∀ j, p ≠ cubicSite b p a h g j := by
    intro j hp
    have hn := hnorm j
    rw [← hp, sub_self, norm_zero] at hn
    rcases j with (js | s) | x
    · exact absurd hn (by simp only; linarith)
    · exact absurd hn (by simp only; linarith)
    · exact absurd hn (by simp only; linarith)
  have hγ : ∀ j, gammaSEqual (vecPhase (p - cubicSite b p a h g j)) ≠ 0 := by
    intro j
    unfold vecPhase
    rw [hnorm j]
    rcases j with (js | s) | x
    · exact hγo
    · exact hγc
    · exact hγq
  refine ⟨?_, ?_, fun v => ?_⟩
  · unfold ionsForce
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [cubicSite, cubicCharge]
    rw [shell_force_zero Zo (octaSite b p a) p (hO 0).1 (hO 0).2.2,
      shell_force_zero Zc (cubeSite b p h) p (hC 0).1 (hC 0).2.2,
      shell_force_zero Zq (cuboSite b p g) p (hQ 0).1 (hQ 0).2.2, add_zero, add_zero]
  · have h1 := ionOutflow_pos_outer ho
    have h2 := ionOutflow_pos_outer hc
    have h3 := ionOutflow_pos_outer hq
    unfold cubicStiff
    have t1 : 0 ≤ 2 * Zo * ionOutflow (1 / (2 * a)) := by positivity
    have t2 : 0 ≤ 8 / 3 * Zc * ionOutflow (1 / (2 * (h * √3))) := by positivity
    have t3 : 0 ≤ 4 * Zq * ionOutflow (1 / (2 * (g * √2))) := by positivity
    rcases hZo.lt_or_eq with hZo' | hZo'
    · have : 0 < 2 * Zo * ionOutflow (1 / (2 * a)) := by positivity
      linarith
    rcases hZc.lt_or_eq with hZc' | hZc'
    · have : 0 < 8 / 3 * Zc * ionOutflow (1 / (2 * (h * √3))) := by positivity
      linarith
    have hZq' : 0 < Zq := by linarith
    have : 0 < 4 * Zq * ionOutflow (1 / (2 * (g * √2))) := by positivity
    linarith
  · have hd := hasDerivAt_ionsForce_line (cubicSite b p a h g) (cubicCharge Zo Zc Zq) v
      hsep_ne hγ
    refine hd.congr_deriv ?_
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [cubicSite, cubicCharge]
    rw [sum_lineStiff_isotropic Zo (fun js => p - octaSite b p a js) v (hO v).1 ha hγo
        (hO v).2.1,
      sum_lineStiff_isotropic Zc (fun s => p - cubeSite b p h s) v (hC v).1 hh3 hγc
        (hC v).2.1,
      sum_lineStiff_isotropic Zq (fun x => p - cuboSite b p g x) v (hQ v).1 hg2 hγq
        (hQ v).2.1]
    unfold cubicStiff
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast
    ring

/-- Force on an ion of charge `Zi` at `p` from point charges `Z j` at `c j`. -/
noncomputable def ionOnIon {ι : Type*} [Fintype ι] (Zi : ℝ) (c : ι → E) (Z : ι → ℝ)
    (p : E) : E :=
  (-Zi) • ionsForce c Z p

/-- The same shells hold an ion of positive charge at their centre: the
force vanishes and every displacement is restored. -/
theorem cubic_center_holds_ion (b : OrthonormalBasis (Fin 3) ℝ E) (p : E)
    {a h g Zo Zc Zq Zi : ℝ}
    (ho : 1 / (2 * a) ∈ Ioo 0 resonanceRoot1)
    (hc : 1 / (2 * (h * √3)) ∈ Ioo 0 resonanceRoot1)
    (hq : 1 / (2 * (g * √2)) ∈ Ioo 0 resonanceRoot1)
    (hZo : 0 ≤ Zo) (hZc : 0 ≤ Zc) (hZq : 0 ≤ Zq) (hZ : 0 < Zo + Zc + Zq) (hZi : 0 < Zi) :
    ionOnIon Zi (cubicSite b p a h g) (cubicCharge Zo Zc Zq) p = 0 ∧
      ∀ v : E, v ≠ 0 →
        -Zi * cubicStiff Zo Zc Zq a h g * ‖v‖ ^ 2 < 0 ∧
        HasDerivAt
          (fun t : ℝ => ⟪ionOnIon Zi (cubicSite b p a h g) (cubicCharge Zo Zc Zq)
            (p + t • v), v⟫)
          (-Zi * cubicStiff Zo Zc Zq a h g * ‖v‖ ^ 2) 0 := by
  obtain ⟨h0, hpos, hd⟩ := cubic_center_pushed b p ho hc hq hZo hZc hZq hZ
  refine ⟨?_, fun v hv => ⟨?_, ?_⟩⟩
  · unfold ionOnIon
    rw [h0, smul_zero]
  · have hvn : 0 < ‖v‖ ^ 2 := by positivity
    have : 0 < Zi * cubicStiff Zo Zc Zq a h g * ‖v‖ ^ 2 := by positivity
    linarith
  · have hfun : (fun t : ℝ => ⟪ionOnIon Zi (cubicSite b p a h g) (cubicCharge Zo Zc Zq)
        (p + t • v), v⟫) = fun t => -Zi * ⟪ionsForce (cubicSite b p a h g)
          (cubicCharge Zo Zc Zq) (p + t • v), v⟫ := by
      funext t
      unfold ionOnIon
      rw [real_inner_smul_left]
    rw [hfun]
    have := (hd v).const_mul (-Zi)
    simpa only [mul_assoc] using this

end Space

end Gravity

end DstDiophantine

