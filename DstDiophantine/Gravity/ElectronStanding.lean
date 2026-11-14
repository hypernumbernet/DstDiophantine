import DstDiophantine.Gravity.ElectronLength
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false
set_option linter.unusedSimpArgs false

/-!
# One electron, one proton: a standing-wave boundary

## Paper boundary (do **not** claim)

The amplitude `e^{-r/a}` is not asserted to be an energy eigenfunction.
No binding energy, no Rydberg spectrum, and no reduced mass are derived.
`α` is an input. The electromagnetic length is the reduced Compton
wavelength already used as an identification, not a theorem. `pr = nℏ`
does not select the radius. No angular momentum is assigned, and the
outward term is not a centrifugal contribution `L²/(m r³)`.

## What is proved

* The Laplacian of the radial amplitude `e^{-r/a}` is that amplitude times
  `1/a² - 2/(a r)`. The outward force read from this curvature is
  `ℏ²/(m a r²)`.
* That force cancels the inward signed force `-k e²/(γ r²)` exactly when
  `γ = a/a₀`, with `a₀ = ℏ²/(m k e²)`.
* On the outer well, `1 - x² - x⁴/6 < γ_s(x) < 1 - x²`.
* Every decay `0 < a < a₀` meets the signed force at exactly one outer-well
  phase, and the net force restores that phase: the curvature increases the
  separation at larger radius, and the signed force decreases it at smaller
  radius. The Coulomb decay `a = a₀` has no such phase.
* With the Compton identification, the decay `a₀ γ_s(α/2)` meets the signed
  force at the Bohr radius. The fractional shortening `1 - γ_s(α/2)`, and
  the fractional excess `1/γ_s(α/2) - 1`, both lie strictly between
  `13312/10⁹` and `13314/10⁹`. The shortening lies below the electron-to-proton
  mass ratio. The first node lies strictly between `a₀/261` and `a₀/255`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI Filter

private lemma hasDerivAt_of_forall {f g : ℝ → ℝ} {f' x : ℝ}
    (h : HasDerivAt f f' x) (hfg : ∀ y, g y = f y) : HasDerivAt g f' x :=
  h.congr_of_eventuallyEq (Eventually.of_forall hfg)

private lemma gamma_decreases {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) π) (hb : b ∈ Icc (0 : ℝ) π)
    (hab : a < b) : gammaSEqual b < gammaSEqual a :=
  strictAntiOn_gammaSEqual_even 0 (by simpa using ha) (by simpa using hb) hab

/-! ### Curvature of a radial exponential -/

/-- Radial standing amplitude `e^{-r/a}`. -/
noncomputable def standingAmplitude (a r : ℝ) : ℝ :=
  exp (-r / a)

theorem hasDerivAt_standingAmplitude {a r : ℝ} (_ha : a ≠ 0) :
    HasDerivAt (standingAmplitude a) (-standingAmplitude a r / a) r := by
  unfold standingAmplitude
  have hlin0 : HasDerivAt (fun s : ℝ => -(s / a)) (-(1 / a)) r :=
    ((hasDerivAt_id r).div_const a).neg
  have hlin : HasDerivAt (fun s : ℝ => -s / a) (-1 / a) r := by
    refine (hasDerivAt_of_forall hlin0 fun s => ?_).congr_deriv ?_
    · ring
    · ring
  refine hlin.exp.congr_deriv ?_
  ring

theorem deriv_standingAmplitude {a r : ℝ} (ha : a ≠ 0) :
    deriv (standingAmplitude a) r = -standingAmplitude a r / a :=
  (hasDerivAt_standingAmplitude ha).deriv

theorem hasDerivAt_standingAmplitude_deriv {a r : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun s : ℝ => -standingAmplitude a s / a)
      (standingAmplitude a r / a ^ 2) r := by
  have h := (hasDerivAt_standingAmplitude (a := a) (r := r) ha).const_mul (-1 / a)
  refine (hasDerivAt_of_forall h fun s => ?_).congr_deriv ?_
  · simp [div_eq_mul_inv]
    ring
  · simp [div_eq_mul_inv]
    ring

/-- Radial part of the three-dimensional Laplacian, `f'' + (2/r) f'`. -/
noncomputable def radialLaplacian (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv f) r + (2 / r) * deriv f r

theorem standingAmplitude_laplacian {a r : ℝ} (ha : a ≠ 0) (hr : r ≠ 0) :
    radialLaplacian (standingAmplitude a) r =
      standingAmplitude a r * (1 / a ^ 2 - 2 / (a * r)) := by
  unfold radialLaplacian
  have hfun : deriv (standingAmplitude a) = fun s => -standingAmplitude a s / a := by
    ext s
    exact deriv_standingAmplitude ha
  rw [hfun, (hasDerivAt_standingAmplitude_deriv ha).deriv]
  field_simp [ha, hr]
  ring

/-- Outward force `ℏ²/(m a r²)` read from the curvature of `e^{-r/a}`. -/
noncomputable def standingOutward (ℏ m a r : ℝ) : ℝ :=
  ℏ ^ 2 / (m * a * r ^ 2)

/-- Quantum potential `-(ℏ²/(2m)) (∇²R)/R` of the same amplitude. -/
noncomputable def standingPotential (ℏ m a r : ℝ) : ℝ :=
  -(ℏ ^ 2 / (2 * m)) * (1 / a ^ 2 - 2 / (a * r))

theorem standingPotential_eq_curvature {ℏ m a r : ℝ}
    (ha : a ≠ 0) (hr : r ≠ 0) (hR : standingAmplitude a r ≠ 0) :
    standingPotential ℏ m a r =
      -(ℏ ^ 2 / (2 * m)) *
        (radialLaplacian (standingAmplitude a) r / standingAmplitude a r) := by
  rw [standingAmplitude_laplacian ha hr]
  unfold standingPotential
  field_simp [hR]

theorem hasDerivAt_standingPotential {ℏ m a r : ℝ} (ha : a ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (standingPotential ℏ m a) (-(ℏ ^ 2 / (m * a * r ^ 2))) r := by
  unfold standingPotential
  have hinv : HasDerivAt (fun s : ℝ => 1 / s) (-1 / r ^ 2) r := by
    refine (hasDerivAt_of_forall (hasDerivAt_inv hr) fun s => ?_).congr_deriv ?_
    · ring
    · ring
  have hterm : HasDerivAt (fun s : ℝ => 2 / (a * s)) (-(2 / (a * r ^ 2))) r := by
    have h := hinv.const_mul (2 / a)
    refine (hasDerivAt_of_forall h fun s => ?_).congr_deriv ?_
    · ring
    · field_simp [ha, hr]
  have hdiff := (hasDerivAt_const r (1 / a ^ 2)).sub hterm
  have h := hdiff.const_mul (-(ℏ ^ 2 / (2 * m)))
  refine h.congr_deriv ?_
  field_simp [ha, hr]
  ring

theorem standingOutward_eq_neg_deriv {ℏ m a r : ℝ} (ha : a ≠ 0) (hr : r ≠ 0) :
    standingOutward ℏ m a r = -deriv (standingPotential ℏ m a) r := by
  rw [(hasDerivAt_standingPotential ha hr).deriv]
  unfold standingOutward
  ring

/-- Separation-increasing signed force `-k e²/(γ r²)`. -/
noncomputable def signedOutward (k e γ r : ℝ) : ℝ :=
  -k * e ^ 2 / (γ * r ^ 2)

/-- Coulomb decay `a₀ = ℏ²/(m k e²)`. -/
noncomputable def coulombDecay (ℏ m k e : ℝ) : ℝ :=
  ℏ ^ 2 / (m * k * e ^ 2)

theorem standing_balance_iff {ℏ m k e a γ r : ℝ}
    (hℏ : ℏ ≠ 0) (hm : 0 < m) (hk : 0 < k) (he : e ≠ 0) (ha : 0 < a)
    (hγ : γ ≠ 0) (hr : 0 < r) :
    standingOutward ℏ m a r + signedOutward k e γ r = 0 ↔
      γ = a / coulombDecay ℏ m k e := by
  unfold standingOutward signedOutward coulombDecay
  have hm0 : m ≠ 0 := hm.ne'
  have hk0 : k ≠ 0 := hk.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hr0 : r ≠ 0 := hr.ne'
  have he2 : e ^ 2 ≠ 0 := pow_ne_zero 2 he
  have hℏ2 : ℏ ^ 2 ≠ 0 := pow_ne_zero 2 hℏ
  constructor
  · intro h
    have hclear : ℏ ^ 2 * γ = m * a * k * e ^ 2 := by
      field_simp [hm0, ha0, hr0, hγ] at h
      linarith
    field_simp [hℏ2, hm0, hk0, he2]
    linarith
  · intro hγeq
    rw [hγeq]
    field_simp [hm0, hk0, he2, ha0, hr0, hℏ2]
    ring

/-! ### Polynomial window for `γ_s` on the outer well -/

private lemma resonanceRoot1_lt_pi_div_two : resonanceRoot1 < π / 2 := by
  have h1 : resonanceRoot1 < 1 := resonanceRoot1_sharp_bounds.2
  linarith [pi_gt_three, h1]

private lemma outer_mem_pi {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    x ∈ Icc (0 : ℝ) π :=
  ⟨hx.1.le, le_of_lt (lt_trans hx.2
    (lt_trans resonanceRoot1_lt_pi_div_two (by linarith [pi_pos])))⟩

private lemma gammaSEqual_lt_one_of_pos {x : ℝ} (hx0 : 0 < x) (hxπ : x ≤ π) :
    gammaSEqual x < 1 := by
  have hlt := gamma_decreases ⟨le_rfl, pi_nonneg⟩ ⟨hx0.le, hxπ⟩ hx0
  simpa [gammaSEqual_zero] using hlt

private lemma pos_above_zero {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hcont : ContinuousOn f (Icc 0 b)) (h0 : f 0 = 0)
    (hd : ∀ x ∈ Ioo 0 b, 0 < deriv f x) : 0 < f b := by
  have hmono : StrictMonoOn f (Icc 0 b) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 b) hcont fun x hx => by
      rw [interior_Icc] at hx
      exact hd x hx
  have hlt := hmono ⟨le_rfl, hb.le⟩ ⟨hb.le, le_rfl⟩ hb
  simpa [h0] using hlt

private noncomputable def curvSlope (x : ℝ) : ℝ :=
  sinh x * sin x + cosh x * cos x - 1

private noncomputable def phaseGap (x : ℝ) : ℝ :=
  cosh x * sin x - x

private noncomputable def gammaUpperGap (x : ℝ) : ℝ :=
  1 - x ^ 2 - gammaSEqual x

private noncomputable def gammaFourth (x : ℝ) : ℝ :=
  4 * (1 - gammaSEqual x)

private noncomputable def gammaThird (x : ℝ) : ℝ :=
  -4 * sinh x * cos x + 4 * x

private noncomputable def gammaSecond (x : ℝ) : ℝ :=
  -2 * (sinh x * sin x + cosh x * cos x) + 2 + 2 * x ^ 2

private noncomputable def gammaFirst (x : ℝ) : ℝ :=
  -2 * cosh x * sin x + 2 * x + (2 / 3) * x ^ 3

private noncomputable def gammaLowerGap (x : ℝ) : ℝ :=
  gammaSEqual x - 1 + x ^ 2 + x ^ 4 / 6

private theorem hasDerivAt_curvSlope (x : ℝ) :
    HasDerivAt curvSlope (2 * sinh x * cos x) x := by
  unfold curvSlope
  have hss := (hasDerivAt_sinh x).mul (hasDerivAt_sin x)
  have hcc := (hasDerivAt_cosh x).mul (hasDerivAt_cos x)
  have h := (hss.add hcc).sub (hasDerivAt_const x (1 : ℝ))
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_phaseGap (x : ℝ) :
    HasDerivAt phaseGap (curvSlope x) x := by
  unfold phaseGap curvSlope
  have h := ((hasDerivAt_cosh x).mul (hasDerivAt_sin x)).sub (hasDerivAt_id x)
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_gammaUpperGap (x : ℝ) :
    HasDerivAt gammaUpperGap (2 * phaseGap x) x := by
  unfold gammaUpperGap phaseGap
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa [pow_one] using hasDerivAt_pow 2 x
  have h := ((hasDerivAt_const x (1 : ℝ)).sub h2).sub (hasDerivAt_gammaSEqual x)
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_gammaFourth (x : ℝ) :
    HasDerivAt gammaFourth (4 * (2 * cosh x * sin x)) x := by
  unfold gammaFourth
  have h := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_gammaSEqual x)
  have h4 := h.const_mul 4
  refine h4.congr_deriv ?_
  ring

private theorem hasDerivAt_gammaThird (x : ℝ) :
    HasDerivAt gammaThird (gammaFourth x) x := by
  have hsc := (hasDerivAt_sinh x).mul (hasDerivAt_cos x)
  have h := ((hsc.const_mul (-4)).add ((hasDerivAt_id x).const_mul 4))
  refine (hasDerivAt_of_forall h fun y => ?_).congr_deriv ?_
  · unfold gammaThird
    simp [Pi.add_apply, Pi.mul_apply]
    ring
  · unfold gammaFourth gammaSEqual
    ring

private theorem hasDerivAt_gammaSecond (x : ℝ) :
    HasDerivAt gammaSecond (gammaThird x) x := by
  unfold gammaSecond gammaThird
  have hss := (hasDerivAt_sinh x).mul (hasDerivAt_sin x)
  have hcc := (hasDerivAt_cosh x).mul (hasDerivAt_cos x)
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa [pow_one] using hasDerivAt_pow 2 x
  have h := (((hss.add hcc).const_mul (-2)).add (hasDerivAt_const x (2 : ℝ))).add
      (h2.const_mul 2)
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_gammaFirst (x : ℝ) :
    HasDerivAt gammaFirst (gammaSecond x) x := by
  have hcs := (hasDerivAt_cosh x).mul (hasDerivAt_sin x)
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * x ^ 2) x := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 3 x
  have h := ((hcs.const_mul (-2)).add ((hasDerivAt_id x).const_mul 2)).add
      ((h3.const_mul (2 / 3)))
  refine (hasDerivAt_of_forall h fun y => ?_).congr_deriv ?_
  · unfold gammaFirst
    simp [Pi.add_apply, Pi.mul_apply]
    ring
  · unfold gammaSecond
    simp [Pi.add_apply, Pi.mul_apply]
    ring

private theorem hasDerivAt_gammaLowerGap (x : ℝ) :
    HasDerivAt gammaLowerGap (gammaFirst x) x := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa [pow_one] using hasDerivAt_pow 2 x
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * x ^ 3) x := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 4 x
  have h := ((hasDerivAt_gammaSEqual x).sub (hasDerivAt_const x (1 : ℝ))).add h2
      |>.add (h4.const_mul (1 / 6))
  refine (hasDerivAt_of_forall h fun y => ?_).congr_deriv ?_
  · unfold gammaLowerGap
    simp [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · unfold gammaFirst
    simp [Pi.add_apply, Pi.mul_apply]
    ring

private lemma curvSlope_pos {b : ℝ} (hb : b ≤ resonanceRoot1) :
    ∀ x ∈ Ioo 0 b, 0 < deriv curvSlope x := by
  intro x hx
  obtain ⟨hx0, hxb⟩ := hx
  rw [(hasDerivAt_curvSlope x).deriv]
  have hsinh : 0 < sinh x := sinh_pos_iff.mpr hx0
  have hcos : 0 < cos x :=
    cos_pos_of_mem_Ioo ⟨by linarith [hx0, pi_pos],
      lt_trans hxb (lt_of_le_of_lt hb resonanceRoot1_lt_pi_div_two)⟩
  positivity

private lemma phaseGap_pos {b : ℝ} (hb0 : 0 < b) (hb : b ≤ resonanceRoot1) :
    0 < phaseGap b := by
  refine pos_above_zero hb0 ?_ ?_ ?_
  · refine Continuous.continuousOn ?_
    unfold phaseGap
    continuity
  · unfold phaseGap; simp
  · intro x hx
    rw [(hasDerivAt_phaseGap x).deriv]
    refine pos_above_zero hx.1 ?_ ?_ ?_
    · refine Continuous.continuousOn ?_
      unfold curvSlope
      continuity
    · unfold curvSlope; simp
    · exact curvSlope_pos (le_trans hx.2.le hb)

private lemma gammaUpperGap_pos {b : ℝ} (hb0 : 0 < b) (hb : b ≤ resonanceRoot1) :
    0 < gammaUpperGap b := by
  refine pos_above_zero hb0 ?_ ?_ ?_
  · exact (((continuous_const.sub (continuous_pow 2)).sub
      continuous_gammaSEqual).continuousOn)
  · unfold gammaUpperGap; simp [gammaSEqual_zero]
  · intro x hx
    rw [(hasDerivAt_gammaUpperGap x).deriv]
    have hphase := phaseGap_pos hx.1 (le_trans hx.2.le hb)
    linarith

private lemma gammaFourth_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    0 < gammaFourth x := by
  unfold gammaFourth
  have hlt : gammaSEqual x < 1 :=
    gammaSEqual_lt_one_of_pos hx.1
      (le_of_lt (lt_trans hx.2 (lt_trans resonanceRoot1_lt_pi_div_two (by linarith [pi_pos]))))
  linarith

private lemma gammaThird_pos {b : ℝ} (hb0 : 0 < b) (hb : b < resonanceRoot1) :
    0 < gammaThird b := by
  refine pos_above_zero hb0 ?_ ?_ ?_
  · refine Continuous.continuousOn ?_
    unfold gammaThird
    continuity
  · unfold gammaThird; simp
  · intro x hx
    rw [(hasDerivAt_gammaThird x).deriv]
    exact gammaFourth_pos ⟨hx.1, lt_trans hx.2 hb⟩

private lemma gammaSecond_pos {b : ℝ} (hb0 : 0 < b) (hb : b < resonanceRoot1) :
    0 < gammaSecond b := by
  refine pos_above_zero hb0 ?_ ?_ ?_
  · refine Continuous.continuousOn ?_
    unfold gammaSecond
    continuity
  · unfold gammaSecond; simp
  · intro x hx
    rw [(hasDerivAt_gammaSecond x).deriv]
    exact gammaThird_pos hx.1 (lt_trans hx.2 hb)

private lemma gammaFirst_pos {b : ℝ} (hb0 : 0 < b) (hb : b < resonanceRoot1) :
    0 < gammaFirst b := by
  refine pos_above_zero hb0 ?_ ?_ ?_
  · refine Continuous.continuousOn ?_
    unfold gammaFirst
    continuity
  · unfold gammaFirst; simp
  · intro x hx
    rw [(hasDerivAt_gammaFirst x).deriv]
    exact gammaSecond_pos hx.1 (lt_trans hx.2 hb)

private lemma gammaLowerGap_pos {b : ℝ} (hb0 : 0 < b) (hb : b < resonanceRoot1) :
    0 < gammaLowerGap b := by
  refine pos_above_zero hb0 ?_ ?_ ?_
  · exact ((continuous_gammaSEqual.sub continuous_const).add (continuous_pow 2)
      |>.add ((continuous_pow 4).div_const 6)).continuousOn
  · unfold gammaLowerGap; simp [gammaSEqual_zero]
  · intro x hx
    rw [(hasDerivAt_gammaLowerGap x).deriv]
    exact gammaFirst_pos hx.1 (lt_trans hx.2 hb)

/-- On the outer well, `1 - x² - x⁴/6 < γ_s(x) < 1 - x²`. -/
theorem gammaSEqual_poly_bounds {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    1 - x ^ 2 - x ^ 4 / 6 < gammaSEqual x ∧ gammaSEqual x < 1 - x ^ 2 := by
  have hup := gammaUpperGap_pos hx.1 hx.2.le
  have hlo := gammaLowerGap_pos hx.1 hx.2
  constructor
  · unfold gammaLowerGap at hlo
    linarith
  · unfold gammaUpperGap at hup
    linarith

/-! ### The Bohr standing wave -/

/-- Reduced Compton length `ℏ/(m_e c)` on the SI stand-ins. -/
noncomputable def comptonLengthApprox : ℝ :=
  (hbarApprox : ℝ) / ((electronMassApprox : ℝ) * (speedOfLight : ℝ))

theorem comptonLengthApprox_eq_bohr_mul_alpha :
    comptonLengthApprox =
      (bohrRadiusApprox : ℝ) * (fineStructureApprox : ℝ) := by
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  have hcast : (bohrRadiusApprox : ℝ) =
      (hbarApprox : ℝ) /
        ((electronMassApprox : ℝ) * (speedOfLight : ℝ) * (fineStructureApprox : ℝ)) := by
    unfold bohrRadiusApprox
    exact_mod_cast rfl
  unfold comptonLengthApprox
  rw [hcast]
  field_simp [hm, hc, hα]

theorem compton_phase_at_bohr :
    comptonLengthApprox / (2 * (bohrRadiusApprox : ℝ)) =
      (fineStructureApprox : ℝ) / 2 := by
  rw [comptonLengthApprox_eq_bohr_mul_alpha]
  have ha : (bohrRadiusApprox : ℝ) ≠ 0 := by exact_mod_cast bohrRadiusApprox_pos.ne'
  field_simp [ha]

/-- Phase `α/2` of the Bohr radius under the Compton identification. -/
noncomputable def bohrPhase : ℝ :=
  (fineStructureApprox : ℝ) / 2

private lemma bohrPhase_mem_outer :
    bohrPhase ∈ Ioo (0 : ℝ) resonanceRoot1 := by
  refine ⟨?_, ?_⟩
  · unfold bohrPhase fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  · refine lt_trans ?_ firstNode_num_window.1
    unfold bohrPhase fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num

/-- Decay that meets the signed force at the Bohr radius, `a₀ γ_s(α/2)`. -/
noncomputable def hydrogenDecay : ℝ :=
  (bohrRadiusApprox : ℝ) * gammaSEqual bohrPhase

theorem hydrogenDecay_ratio :
    hydrogenDecay / (bohrRadiusApprox : ℝ) = gammaSEqual bohrPhase := by
  unfold hydrogenDecay
  have ha : (bohrRadiusApprox : ℝ) ≠ 0 := by exact_mod_cast bohrRadiusApprox_pos.ne'
  field_simp [ha]

theorem hydrogenDecay_lt_bohr :
    hydrogenDecay < (bohrRadiusApprox : ℝ) := by
  have hmem := bohrPhase_mem_outer
  have hγ : gammaSEqual bohrPhase < 1 :=
    gammaSEqual_lt_one_of_pos hmem.1
      (le_of_lt (lt_trans hmem.2 (lt_trans resonanceRoot1_lt_pi_div_two (by linarith [pi_pos]))))
  have ha : (0 : ℝ) < (bohrRadiusApprox : ℝ) := by exact_mod_cast bohrRadiusApprox_pos
  unfold hydrogenDecay
  nlinarith

theorem hydrogenDecay_pos : 0 < hydrogenDecay := by
  have hγ : 0 < gammaSEqual bohrPhase := gammaSEqual_pos_left_of_first_node bohrPhase_mem_outer
  have ha : (0 : ℝ) < (bohrRadiusApprox : ℝ) := by exact_mod_cast bohrRadiusApprox_pos
  unfold hydrogenDecay
  positivity

/-- Fractional shortening `1 - γ_s(α/2)`, and the force excess `1/γ_s(α/2) - 1`,
both lie strictly between `13312/10⁹` and `13314/10⁹`. -/
theorem hydrogen_fraction_window :
    (13312 / 10 ^ 9 : ℝ) < 1 - gammaSEqual bohrPhase ∧
      1 - gammaSEqual bohrPhase < 13314 / 10 ^ 9 ∧
        (13312 / 10 ^ 9 : ℝ) < 1 / gammaSEqual bohrPhase - 1 ∧
          1 / gammaSEqual bohrPhase - 1 < 13314 / 10 ^ 9 := by
  set x : ℝ := bohrPhase
  have hxdef : x = (fineStructureApprox : ℝ) / 2 := rfl
  have hmem : x ∈ Ioo (0 : ℝ) resonanceRoot1 := bohrPhase_mem_outer
  have hpoly := gammaSEqual_poly_bounds hmem
  have hγpos : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hmem
  have hx2 : (13312 / 10 ^ 9 : ℝ) < x ^ 2 := by
    rw [hxdef]
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hx4 : x ^ 2 + x ^ 4 / 6 < (13314 / 10 ^ 9 : ℝ) := by
    rw [hxdef]
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hforceLoRat : (13312 / 10 ^ 9 : ℝ) < x ^ 2 / (1 - x ^ 2) := by
    rw [hxdef]
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hforceHiRat : (x ^ 2 + x ^ 4 / 6) / (1 - (x ^ 2 + x ^ 4 / 6)) <
      (13314 / 10 ^ 9 : ℝ) := by
    rw [hxdef]
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hshort_lo : 13312 / 10 ^ 9 < 1 - gammaSEqual x := by
    have : x ^ 2 < 1 - gammaSEqual x := by linarith [hpoly.2]
    exact lt_trans hx2 this
  have hshort_hi : 1 - gammaSEqual x < 13314 / 10 ^ 9 := by
    have : 1 - gammaSEqual x < x ^ 2 + x ^ 4 / 6 := by linarith [hpoly.1]
    exact lt_trans this hx4
  have hden1 : 0 < 1 - x ^ 2 := by linarith [hpoly.2, hγpos]
  have hforce_lo : 13312 / 10 ^ 9 < 1 / gammaSEqual x - 1 := by
    have hone : 1 / (1 - x ^ 2) < 1 / gammaSEqual x :=
      one_div_lt_one_div_of_lt hγpos hpoly.2
    have hid : 1 / (1 - x ^ 2) - 1 = x ^ 2 / (1 - x ^ 2) := by
      field_simp [hden1.ne']
      ring
    linarith [hone, hid, hforceLoRat]
  have hden4 : 0 < 1 - x ^ 2 - x ^ 4 / 6 := by linarith [hpoly.1, hγpos]
  have hden4' : 0 < 1 - (x ^ 2 + x ^ 4 / 6) := by linarith [hden4]
  have hforce_hi : 1 / gammaSEqual x - 1 < 13314 / 10 ^ 9 := by
    have hone : 1 / gammaSEqual x < 1 / (1 - x ^ 2 - x ^ 4 / 6) :=
      one_div_lt_one_div_of_lt hden4 hpoly.1
    set d : ℝ := 1 - (x ^ 2 + x ^ 4 / 6)
    have hid : 1 / d - 1 = (x ^ 2 + x ^ 4 / 6) / d := by
      have hd : d ≠ 0 := hden4'.ne'
      have hnum : 1 - d = x ^ 2 + x ^ 4 / 6 := by ring
      rw [← hnum, ← div_self hd, ← sub_div]
    have hone' : 1 / gammaSEqual x < 1 / (1 - (x ^ 2 + x ^ 4 / 6)) := by
      have hsame : 1 - x ^ 2 - x ^ 4 / 6 = 1 - (x ^ 2 + x ^ 4 / 6) := by ring
      simpa [hsame] using hone
    linarith [hone', hid, hforceHiRat]
  exact ⟨hshort_lo, hshort_hi, hforce_lo, hforce_hi⟩

/-- The shortening lies below the ratio of the electron mass to the proton mass. -/
theorem hydrogen_shortening_lt_mass_ratio :
    1 - gammaSEqual bohrPhase <
      (electronMassApprox : ℝ) / (protonMassApprox : ℝ) := by
  have hshort := hydrogen_fraction_window.2.1
  have hmass : (13314 / 10 ^ 9 : ℝ) <
      (electronMassApprox : ℝ) / (protonMassApprox : ℝ) := by
    unfold electronMassApprox electronMassMantissa electronMassScale
      protonMassApprox protonMassMantissa protonMassScale
    norm_num
  exact lt_trans hshort hmass

theorem hydrogenStanding_unique {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    gammaSEqual x = hydrogenDecay / (bohrRadiusApprox : ℝ) ↔ x = bohrPhase := by
  rw [hydrogenDecay_ratio]
  constructor
  · intro h
    rcases lt_trichotomy x bohrPhase with hlt | heq | hgt
    · have hltγ := gamma_decreases (outer_mem_pi hx) (outer_mem_pi bohrPhase_mem_outer) hlt
      linarith
    · exact heq
    · have hltγ := gamma_decreases (outer_mem_pi bohrPhase_mem_outer) (outer_mem_pi hx) hgt
      linarith
  · rintro rfl
    rfl

/-- Sign of the separation-increasing imbalance. Positive outside the Bohr phase. -/
noncomputable def hydrogenImbalance (x : ℝ) : ℝ :=
  1 / gammaSEqual bohrPhase - 1 / gammaSEqual x

theorem hydrogenImbalance_pos_iff {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    0 < hydrogenImbalance x ↔ x < bohrPhase := by
  have hγ : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  have hγb : 0 < gammaSEqual bohrPhase :=
    gammaSEqual_pos_left_of_first_node bohrPhase_mem_outer
  unfold hydrogenImbalance
  constructor
  · intro hpos
    by_contra hge
    have hle : bohrPhase ≤ x := le_of_not_gt hge
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hpos
      linarith
    · have hγlt := gamma_decreases (outer_mem_pi bohrPhase_mem_outer) (outer_mem_pi hx) hlt
      have hdiv : 1 / gammaSEqual bohrPhase < 1 / gammaSEqual x :=
        one_div_lt_one_div_of_lt hγ hγlt
      linarith
  · intro hlt
    have hγgt := gamma_decreases (outer_mem_pi hx) (outer_mem_pi bohrPhase_mem_outer) hlt
    have hdiv : 1 / gammaSEqual x < 1 / gammaSEqual bohrPhase :=
      one_div_lt_one_div_of_lt hγb hγgt
    linarith

/-- The Coulomb decay `a = a₀` is pulled inward at every finite outer-well phase. -/
theorem coulombDecay_inward {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    1 - 1 / gammaSEqual x < 0 := by
  have hγ : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  have hlt : gammaSEqual x < 1 :=
    gammaSEqual_lt_one_of_pos hx.1
      (le_of_lt (lt_trans hx.2 (lt_trans resonanceRoot1_lt_pi_div_two (by linarith [pi_pos]))))
  have hone : 1 < 1 / gammaSEqual x := (one_lt_div hγ).mpr hlt
  linarith

/-- The first node, in units of the Bohr radius, lies strictly between `1/261` and `1/255`. -/
theorem firstNode_over_bohr_window :
    (1 / 261 : ℝ) < (fineStructureApprox : ℝ) / (2 * resonanceRoot1) ∧
      (fineStructureApprox : ℝ) / (2 * resonanceRoot1) < 1 / 255 := by
  have hx := firstNode_num_window
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hxpos : (0 : ℝ) < resonanceRoot1 :=
    lt_trans (by norm_num : (0 : ℝ) < 14 / 15) hx.1
  have h2pos : (0 : ℝ) < 2 * resonanceRoot1 := by positivity
  have hlo_phase : 2 * resonanceRoot1 < 19 / 10 := by nlinarith [hx.2]
  have hhi_phase : 28 / 15 < 2 * resonanceRoot1 := by nlinarith [hx.1]
  have hrecip_lo : (10 / 19 : ℝ) < 1 / (2 * resonanceRoot1) := by
    rw [lt_div_iff₀ h2pos]
    nlinarith [hx.2]
  have hrecip_hi : 1 / (2 * resonanceRoot1) < 15 / 28 := by
    rw [div_lt_iff₀ h2pos]
    nlinarith [hx.1]
  have hlo : (fineStructureApprox : ℝ) * (10 / 19) <
      (fineStructureApprox : ℝ) / (2 * resonanceRoot1) := by
    have hmul := mul_lt_mul_of_pos_left hrecip_lo hα
    have hid : (fineStructureApprox : ℝ) * (1 / (2 * resonanceRoot1)) =
        (fineStructureApprox : ℝ) / (2 * resonanceRoot1) := by ring
    linarith
  have hhi : (fineStructureApprox : ℝ) / (2 * resonanceRoot1) <
      (fineStructureApprox : ℝ) * (15 / 28) := by
    have hmul := mul_lt_mul_of_pos_left hrecip_hi hα
    have hid : (fineStructureApprox : ℝ) * (1 / (2 * resonanceRoot1)) =
        (fineStructureApprox : ℝ) / (2 * resonanceRoot1) := by ring
    linarith
  have hrat_lo : (1 / 261 : ℝ) < (fineStructureApprox : ℝ) * (10 / 19) := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hrat_hi : (fineStructureApprox : ℝ) * (15 / 28) < 1 / 255 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  exact ⟨lt_trans hrat_lo hlo, lt_trans hhi hrat_hi⟩

end Gravity

end DstDiophantine
