import DstDiophantine.Gravity.DualControl
import DstDiophantine.Gravity.ElectronShell
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Dual-only shielding and the one-axis clock are distinct displacements

The factor \(\gamma_{\mathrm{eff}}(\alpha,\beta)=\cosh\alpha-\sinh\alpha\sin\beta\)
of `ElectronShell` is a one-axis observable. It is **not** a product of
three sandwiches, and it is **not** the mismatch \(J\). Dual-only motion
on a boosted axis moves both, but they do not return together.

## Paper boundary (do **not** claim)

No electromagnetic coupling, no laboratory protocol, no helicity drive of
\(J\), and no identification of a many-axis clock with a product of
one-axis factors.

## What is proved

* For \(\alpha>0\) the map \(\beta\mapsto\gamma_{\mathrm{eff}}(\alpha,\beta)\)
  is strictly decreasing on \([0,\pi/2]\).
* \(\gamma_{\mathrm{eff}}(\alpha,\beta)=1\) holds on that interval at a
  unique dual angle \(\beta_\ast=\arcsin\tanh(\alpha/2)\in(0,\pi/2)\).
* For \(0<\alpha\le\pi/2\) one has \(\beta_\ast<\alpha\), so every
  admissible coaxial shield \(\beta=\alpha\) (which requires
  \(\alpha\le\pi/4\)) already has \(\gamma_{\mathrm{eff}}<1\).
* \(\cos\alpha=\tanh(\alpha/2)\) has a unique root \(\alpha_\dagger\) in
  \((\pi/3,\pi/2)\). Below that root a coaxial dual ray meets
  \(\gamma_{\mathrm{eff}}=1\) before the wall; above it every admissible
  dual angle on the boosted axis remains on the side \(\gamma_{\mathrm{eff}}>1\).
* The coaxial and cross-axis shields of a pure-usual seed have the same
  \(J=0\) and the same unsigned mass. The cross-axis shield leaves the
  boosted axis at \((\alpha,0)\), hence at \(\cosh\alpha\), while the
  compensating axis contributes the trivial factor \(1\).
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Real Set Operations Invariant Admissible

/-! ### Interval membership for \(\sin\) on \([0,\pi/2]\) -/

private theorem mem_sin_Icc {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ π / 2) :
    β ∈ Icc (-(π / 2)) (π / 2) :=
  ⟨le_trans (neg_nonpos_of_nonneg pi_div_two_pos.le) hβ0, hβ⟩

/-! ### One-axis decrease of \(\gamma_{\mathrm{eff}}\) -/

theorem gammaEff_lt_gammaEff_of_lt_beta {α β₁ β₂ : ℝ}
    (hα : 0 < α) (hlo : 0 ≤ β₁) (hlt : β₁ < β₂) (hhi : β₂ ≤ π / 2) :
    gammaEff α β₂ < gammaEff α β₁ := by
  have hs : 0 < sinh α := sinh_pos_iff.mpr hα
  have hsin : sin β₁ < sin β₂ :=
    strictMonoOn_sin
      (mem_sin_Icc hlo (le_trans hlt.le hhi))
      (mem_sin_Icc (le_of_lt (lt_of_le_of_lt hlo hlt)) hhi)
      hlt
  rw [gammaEff_closed, gammaEff_closed]
  nlinarith [hs]

/-! ### Half-angle identity and \(\tanh x < x\) -/

private theorem tanh_half_eq (x : ℝ) :
    tanh (x / 2) = (cosh x - 1) / sinh x := by
  have htwo : (2 : ℝ) * (x / 2) = x := by ring
  have hsinh : sinh x = 2 * sinh (x / 2) * cosh (x / 2) := by
    simpa [htwo] using sinh_two_mul (x / 2)
  have hcosh : cosh x - 1 = 2 * sinh (x / 2) ^ 2 := by
    have h := cosh_two_mul (x / 2)
    rw [htwo] at h
    nlinarith [cosh_sq (x / 2)]
  have hden : cosh (x / 2) ≠ 0 := (cosh_pos _).ne'
  rw [tanh_eq_sinh_div_cosh, hcosh, hsinh]
  field_simp [hden]

private theorem tanh_lt_self {x : ℝ} (hx : 0 < x) : tanh x < x := by
  have hcosh : 0 < cosh x := cosh_pos x
  rw [tanh_eq_sinh_div_cosh, div_lt_iff₀ hcosh]
  set f : ℝ → ℝ := fun y => y * cosh y - sinh y
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ t, HasDerivAt f (t * sinh t) t := fun t => by
    have hmul := (hasDerivAt_id t).mul (hasDerivAt_cosh t)
    have : HasDerivAt f (1 * cosh t + t * sinh t - cosh t) t :=
      hmul.sub (hasDerivAt_sinh t)
    convert this using 1
    ring
  have hcont : ContinuousOn f (Icc 0 x) := fun t _ =>
    (hderiv t).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hEq⟩ :=
    exists_hasDerivAt_eq_slope f (fun t => t * sinh t) hx hcont
      fun t _ => hderiv t
  have hxne : (x : ℝ) ≠ 0 := hx.ne'
  have hfx : f x = x * (c * sinh c) := by
    have : c * sinh c = (f x - f 0) / (x - 0) := hEq
    simp only [hf0, sub_zero] at this
    field_simp [hxne] at this
    linarith
  have hpos : 0 < c * sinh c :=
    mul_pos hc.1 (sinh_pos_iff.mpr hc.1)
  have : 0 < f x := by
    rw [hfx]
    exact mul_pos hx hpos
  simpa [f] using this

private theorem pi_lt_31416 : π < (31416 : ℝ) / 10000 := by
  convert pi_lt_d4 using 1
  norm_num

private theorem sqrt_three_gt_pi_div_two : π / 2 < sqrt 3 := by
  have hπ : π / 2 < (17 : ℝ) / 10 := by
    linarith [pi_lt_31416]
  exact hπ.trans (lt_sqrt_of_sq_lt (by norm_num))

private theorem half_lt_sin {α : ℝ} (hα0 : 0 < α) (hα : α ≤ π / 2) :
    α / 2 < sin α := by
  by_cases hsmall : α ≤ π / 3
  · set g : ℝ → ℝ := fun y => sin y - y / 2
    have hg0 : g 0 = 0 := by simp [g]
    have hderiv : ∀ t, HasDerivAt g (cos t - 1 / 2) t := fun t =>
      (hasDerivAt_sin t).sub ((hasDerivAt_id t).div_const 2)
    have hcont : ContinuousOn g (Icc 0 α) := fun t _ =>
      (hderiv t).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hEq⟩ :=
      exists_hasDerivAt_eq_slope g (fun t => cos t - 1 / 2) hα0 hcont
        fun t _ => hderiv t
    have hαne : (α : ℝ) ≠ 0 := hα0.ne'
    have hgα : g α = α * (cos c - 1 / 2) := by
      have : cos c - 1 / 2 = (g α - g 0) / (α - 0) := hEq
      simp only [hg0, sub_zero] at this
      field_simp [hαne] at this
      linarith
    have hcπ : c < π / 3 := lt_of_lt_of_le hc.2 hsmall
    have hcos : (1 / 2 : ℝ) < cos c := by
      have hmono :=
        strictAntiOn_cos
          ⟨hc.1.le, le_of_lt (lt_trans hcπ (by linarith [pi_pos] : π / 3 < π))⟩
          ⟨by positivity,
            le_of_lt (by linarith [pi_pos] : π / 3 < π)⟩
          hcπ
      simpa [cos_pi_div_three] using hmono
    have : 0 < g α := by
      rw [hgα]
      exact mul_pos hα0 (sub_pos.mpr hcos)
    simpa [g] using this
  · have hlo : π / 3 ≤ α := le_of_not_ge hsmall
    have hsin : sqrt 3 / 2 ≤ sin α := by
      have hmono :=
        strictMonoOn_sin.monotoneOn
          (mem_sin_Icc (by positivity : (0 : ℝ) ≤ π / 3)
            (by linarith [pi_gt_three] : π / 3 ≤ π / 2))
          (mem_sin_Icc (le_trans (by positivity) hlo) hα)
          hlo
      simpa [sin_pi_div_three] using hmono
    have hπ : π / 4 < sqrt 3 / 2 := by
      have : π / 2 < sqrt 3 := sqrt_three_gt_pi_div_two
      linarith
    have hα2 : α / 2 ≤ π / 4 := by linarith
    linarith

private theorem tanh_half_lt_sin {α : ℝ} (hα0 : 0 < α) (hα : α ≤ π / 2) :
    tanh (α / 2) < sin α :=
  (tanh_lt_self (half_pos hα0)).trans (half_lt_sin hα0 hα)

/-! ### Clock return \(\beta_\ast\) -/

/-- Dual angle at which a boosted axis returns \(\gamma_{\mathrm{eff}}=1\). -/
noncomputable def clockAngle (α : ℝ) : ℝ :=
  arcsin (tanh (α / 2))

private theorem tanh_half_pos {α : ℝ} (hα : 0 < α) : 0 < tanh (α / 2) := by
  rw [tanh_eq_sinh_div_cosh]
  exact div_pos (sinh_pos_iff.mpr (half_pos hα)) (cosh_pos _)

theorem clockAngle_mem {α : ℝ} (hα : 0 < α) :
    clockAngle α ∈ Ioo (0 : ℝ) (π / 2) :=
  ⟨arcsin_pos.mpr (tanh_half_pos hα),
    arcsin_lt_pi_div_two.mpr (tanh_lt_one _)⟩

theorem sin_clockAngle {α : ℝ} (hα : 0 < α) :
    sin (clockAngle α) = tanh (α / 2) :=
  sin_arcsin (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (tanh_half_pos hα).le)
    (tanh_lt_one _).le

theorem gammaEff_clockAngle {α : ℝ} (hα : 0 < α) :
    gammaEff α (clockAngle α) = 1 := by
  have hs : 0 < sinh α := sinh_pos_iff.mpr hα
  rw [gammaEff_closed, sin_clockAngle hα, tanh_half_eq α]
  field_simp [hs.ne']
  ring

theorem gammaEff_eq_one_iff_clockAngle {α β : ℝ} (hα : 0 < α)
    (hβ0 : 0 ≤ β) (hβ : β ≤ π / 2) :
    gammaEff α β = 1 ↔ β = clockAngle α := by
  constructor
  · intro h
    have hs : 0 < sinh α := sinh_pos_iff.mpr hα
    have hsin : sin β = tanh (α / 2) := by
      have : sinh α * sin β = cosh α - 1 := by
        rw [gammaEff_closed] at h
        linarith
      rw [tanh_half_eq α, eq_div_iff hs.ne']
      linarith
    have hclk := clockAngle_mem hα
    exact strictMonoOn_sin.injOn
      (mem_sin_Icc hβ0 hβ)
      (mem_sin_Icc (le_of_lt hclk.1) (le_of_lt hclk.2))
      (hsin.trans (sin_clockAngle hα).symm)
  · intro h
    rw [h]
    exact gammaEff_clockAngle hα

theorem clockAngle_lt_alpha {α : ℝ} (hα0 : 0 < α) (hα : α ≤ π / 2) :
    clockAngle α < α := by
  have hclk := clockAngle_mem hα0
  have hsin : sin (clockAngle α) < sin α := by
    rw [sin_clockAngle hα0]
    exact tanh_half_lt_sin hα0 hα
  exact (strictMonoOn_sin.lt_iff_lt
      (mem_sin_Icc (le_of_lt hclk.1) (le_of_lt hclk.2))
      (mem_sin_Icc hα0.le hα)).mp hsin

/-- An admissible coaxial shield has already passed the clock return. -/
theorem gammaEff_coaxial_lt_one {α : ℝ} (hα0 : 0 < α) (hα : α ≤ π / 4) :
    gammaEff α α < 1 := by
  have hαπ : α ≤ π / 2 := le_trans hα (by linarith [pi_pos])
  have hclk := clockAngle_mem hα0
  have := gammaEff_lt_gammaEff_of_lt_beta hα0 (le_of_lt hclk.1)
    (clockAngle_lt_alpha hα0 hαπ) hαπ
  rwa [gammaEff_clockAngle hα0] at this

/-! ### Wall versus clock: the threshold \(\alpha_\dagger\) -/

/-- Sign of \(\gamma_{\mathrm{eff}}-1\) at the dual wall of a boosted axis. -/
noncomputable def wallClockProbe (α : ℝ) : ℝ :=
  cos α - tanh (α / 2)

private theorem tanh_strictMono : StrictMono tanh := by
  intro a b hab
  have hden_a := cosh_pos a
  have hden_b := cosh_pos b
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, div_lt_div_iff₀ hden_a hden_b]
  have : 0 < sinh (b - a) := sinh_pos_iff.mpr (sub_pos.mpr hab)
  rw [sinh_sub] at this
  linarith

private theorem continuous_tanh : Continuous tanh := by
  have h : (tanh : ℝ → ℝ) = fun x => sinh x / cosh x :=
    funext tanh_eq_sinh_div_cosh
  rw [h]
  exact continuous_sinh.div continuous_cosh fun _ => (cosh_pos _).ne'

private theorem continuous_wallClockProbe : Continuous wallClockProbe :=
  continuous_cos.sub (continuous_tanh.comp (continuous_id.div_const 2))

private theorem strictAntiOn_wallClockProbe :
    StrictAntiOn wallClockProbe (Icc (0 : ℝ) (π / 2)) := by
  intro a ha b hb hab
  have hcos : cos b < cos a :=
    strictAntiOn_cos
      ⟨ha.1, le_trans ha.2 (by linarith [pi_pos])⟩
      ⟨hb.1, le_trans hb.2 (by linarith [pi_pos])⟩
      hab
  have htanh : tanh (a / 2) < tanh (b / 2) :=
    tanh_strictMono (div_lt_div_of_pos_right hab (by norm_num : (0 : ℝ) < 2))
  unfold wallClockProbe
  linarith

private theorem exp_pi_div_three_lt_three : exp (π / 3) < 3 := by
  have harg : π / 3 < (21 : ℝ) / 20 := by
    linarith [pi_lt_31416]
  have hsplit : exp ((21 : ℝ) / 20) = exp 1 * exp ((1 : ℝ) / 20) := by
    rw [← exp_add]; ring_nf
  have hsmall : exp ((1 : ℝ) / 20) ≤ (20 : ℝ) / 19 := by
    have hbound :=
      exp_bound_div_one_sub_of_interval (by positivity : (0 : ℝ) ≤ 1 / 20)
        (by norm_num : (1 : ℝ) / 20 < 1)
    have hsimp : (1 : ℝ) / (1 - 1 / 20) = 20 / 19 := by field_simp; ring
    rwa [hsimp] at hbound
  have hprod : exp 1 * ((20 : ℝ) / 19) < (2.7182818286 : ℝ) * (20 / 19) :=
    mul_lt_mul_of_pos_right exp_one_lt_d9 (by positivity)
  have hnum : (2.7182818286 : ℝ) * (20 / 19) < 3 := by norm_num
  have hle : exp (π / 3) < exp 1 * ((20 : ℝ) / 19) := by
    have : exp (π / 3) < exp ((21 : ℝ) / 20) := exp_lt_exp.mpr harg
    rw [hsplit] at this
    exact this.trans_le (mul_le_mul_of_nonneg_left hsmall (exp_pos 1).le)
  exact hle.trans (hprod.trans hnum)

private theorem tanh_pi_div_six_lt_half : tanh (π / 6) < 1 / 2 := by
  have hx : exp (π / 6) ≠ 0 := (exp_pos _).ne'
  have h1 : exp (π / 6) * exp (π / 6) = exp (π / 3) := by
    rw [← exp_add]; ring_nf
  have h2 : exp (π / 6) * exp (-(π / 6)) = (1 : ℝ) := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  have hform : tanh (π / 6) = (exp (π / 3) - 1) / (exp (π / 3) + 1) := by
    rw [tanh_eq, ← mul_div_mul_left _ _ hx, mul_sub, mul_add, h1, h2]
  rw [hform, div_lt_iff₀ (by linarith [exp_pos (π / 3)])]
  linarith [exp_pi_div_three_lt_three, exp_pos (π / 3)]

private theorem wallClockProbe_pi_div_three_pos :
    0 < wallClockProbe (π / 3) := by
  have hhalf : (π / 3) / 2 = π / 6 := by ring
  unfold wallClockProbe
  rw [cos_pi_div_three, hhalf]
  linarith [tanh_pi_div_six_lt_half]

private theorem wallClockProbe_pi_div_two_neg :
    wallClockProbe (π / 2) < 0 := by
  have hhalf : (π / 2) / 2 = π / 4 := by ring
  unfold wallClockProbe
  rw [cos_pi_div_two, hhalf, zero_sub, neg_lt_zero]
  rw [tanh_eq_sinh_div_cosh]
  exact div_pos (sinh_pos_iff.mpr (by positivity)) (cosh_pos _)

private theorem mem_Icc_zero_pi_div_two_of_Ioo_pi_div_three {α : ℝ}
    (h : α ∈ Ioo (π / 3) (π / 2)) :
    α ∈ Icc (0 : ℝ) (π / 2) :=
  ⟨le_of_lt (lt_trans (by positivity) h.1), le_of_lt h.2⟩

theorem exists_unique_wallClockRoot :
    ∃! α : ℝ, α ∈ Ioo (π / 3) (π / 2) ∧ wallClockProbe α = 0 := by
  have hab : π / 3 ≤ π / 2 := by linarith [pi_pos]
  have hcont : ContinuousOn wallClockProbe (Icc (π / 3) (π / 2)) :=
    continuous_wallClockProbe.continuousOn
  have hmem : (0 : ℝ) ∈ Ioo (wallClockProbe (π / 2)) (wallClockProbe (π / 3)) :=
    ⟨wallClockProbe_pi_div_two_neg, wallClockProbe_pi_div_three_pos⟩
  obtain ⟨α, hαIoo, hαeq⟩ := intermediate_value_Ioo' hab hcont hmem
  refine ⟨α, ⟨hαIoo, hαeq⟩, ?_⟩
  intro β ⟨hβIoo, hβeq⟩
  exact (strictAntiOn_wallClockProbe.injOn
    (mem_Icc_zero_pi_div_two_of_Ioo_pi_div_three hαIoo)
    (mem_Icc_zero_pi_div_two_of_Ioo_pi_div_three hβIoo)
    (hαeq.trans hβeq.symm)).symm

/-- Unique usual rapidity at which the dual wall itself returns the clock. -/
noncomputable def wallClockRoot : ℝ :=
  exists_unique_wallClockRoot.choose

private theorem wallClockRoot_spec :
    wallClockRoot ∈ Ioo (π / 3) (π / 2) ∧ wallClockProbe wallClockRoot = 0 :=
  exists_unique_wallClockRoot.choose_spec.1

theorem wallClockRoot_mem : wallClockRoot ∈ Ioo (π / 3) (π / 2) :=
  wallClockRoot_spec.1

theorem wallClockProbe_root : wallClockProbe wallClockRoot = 0 :=
  wallClockRoot_spec.2

theorem eq_wallClockRoot {α : ℝ}
    (h : α ∈ Ioo (π / 3) (π / 2)) (hz : wallClockProbe α = 0) :
    α = wallClockRoot :=
  exists_unique_wallClockRoot.choose_spec.2 α ⟨h, hz⟩

private theorem wallClockRoot_mem_Icc :
    wallClockRoot ∈ Icc (0 : ℝ) (π / 2) :=
  mem_Icc_zero_pi_div_two_of_Ioo_pi_div_three wallClockRoot_mem

private theorem pos_of_gt_wallClockRoot {α : ℝ} (hgt : wallClockRoot < α) :
    0 < α :=
  lt_trans (lt_trans (by positivity) wallClockRoot_mem.1) hgt

private theorem wallClockProbe_pos_of_lt {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ π / 2) (hlt : α < wallClockRoot) :
    0 < wallClockProbe α := by
  have := strictAntiOn_wallClockProbe ⟨hα0, hα⟩ wallClockRoot_mem_Icc hlt
  rwa [wallClockProbe_root] at this

private theorem wallClockProbe_neg_of_gt {α : ℝ}
    (hα : α ≤ π / 2) (hgt : wallClockRoot < α) :
    wallClockProbe α < 0 := by
  have := strictAntiOn_wallClockProbe wallClockRoot_mem_Icc
    ⟨(pos_of_gt_wallClockRoot hgt).le, hα⟩ hgt
  rwa [wallClockProbe_root] at this

/-- Below the threshold, coaxial dual excitation meets \(\gamma_{\mathrm{eff}}=1\)
before the wall. -/
theorem clockAngle_lt_wall_of_lt_root {α : ℝ}
    (hα0 : 0 < α) (hα : α ≤ π / 2) (hlt : α < wallClockRoot) :
    clockAngle α < π / 2 - α := by
  have hclk := clockAngle_mem hα0
  have hwall0 : 0 ≤ π / 2 - α := sub_nonneg.mpr hα
  have hwall : π / 2 - α ≤ π / 2 := by linarith [hα0]
  have hsin : sin (clockAngle α) < sin (π / 2 - α) := by
    rw [sin_clockAngle hα0, sin_pi_div_two_sub]
    exact sub_pos.mp (wallClockProbe_pos_of_lt hα0.le hα hlt)
  exact (strictMonoOn_sin.lt_iff_lt
      (mem_sin_Icc (le_of_lt hclk.1) (le_of_lt hclk.2))
      (mem_sin_Icc hwall0 hwall)).mp hsin

/-- Above the threshold, the wall lies before the clock return. -/
theorem wall_lt_clockAngle_of_gt_root {α : ℝ}
    (hα : α ≤ π / 2) (hgt : wallClockRoot < α) :
    π / 2 - α < clockAngle α := by
  have hα0 := pos_of_gt_wallClockRoot hgt
  have hclk := clockAngle_mem hα0
  have hwall0 : 0 ≤ π / 2 - α := sub_nonneg.mpr hα
  have hwall : π / 2 - α ≤ π / 2 := by linarith [hα0]
  have hsin : sin (π / 2 - α) < sin (clockAngle α) := by
    rw [sin_clockAngle hα0, sin_pi_div_two_sub]
    exact sub_lt_zero.mp (wallClockProbe_neg_of_gt hα hgt)
  exact (strictMonoOn_sin.lt_iff_lt
      (mem_sin_Icc hwall0 hwall)
      (mem_sin_Icc (le_of_lt hclk.1) (le_of_lt hclk.2))).mp hsin

/-- Above the threshold every admissible dual angle on the boosted axis
stays on the side \(\gamma_{\mathrm{eff}}>1\). -/
theorem gammaEff_gt_one_of_le_wall_of_gt_root {α β : ℝ}
    (hα : α ≤ π / 2) (hgt : wallClockRoot < α)
    (hβ0 : 0 ≤ β) (hβ : β ≤ π / 2 - α) :
    1 < gammaEff α β := by
  have hα0 := pos_of_gt_wallClockRoot hgt
  have hclk := clockAngle_mem hα0
  have hβclk : β < clockAngle α :=
    lt_of_le_of_lt hβ (wall_lt_clockAngle_of_gt_root hα hgt)
  have := gammaEff_lt_gammaEff_of_lt_beta hα0 hβ0 hβclk (le_of_lt hclk.2)
  rwa [gammaEff_clockAngle hα0] at this

/-! ### Coaxial versus cross-axis shields of a pure-usual seed -/

private theorem mass_crossAxisDual (α : ℝ) :
    mass (crossAxisDual α) = α ^ 2 := by
  rw [mass_coef, Fin.sum_univ_three]
  simp [crossAxisDual, finCoord]
  ring

private theorem mass_equalScale_axisUsual (α : ℝ) :
    mass (equalScaleOf (axisUsual α)) = α ^ 2 := by
  rw [mass_equalScaleOf]
  simp [axisUsual, finCoord]

theorem mass_crossAxisDual_eq_equalScale (α : ℝ) :
    mass (crossAxisDual α) = mass (equalScaleOf (axisUsual α)) := by
  rw [mass_crossAxisDual, mass_equalScale_axisUsual]

theorem gammaEff_crossAxisDual_boost (α : ℝ) :
    gammaEff ((crossAxisDual α).alpha 0) ((crossAxisDual α).beta 0) = cosh α := by
  simp [crossAxisDual, finCoord, gammaEff_of_beta_zero]

theorem gammaEff_crossAxisDual_comp (α : ℝ) :
    gammaEff ((crossAxisDual α).alpha 1) ((crossAxisDual α).beta 1) = 1 := by
  simp [crossAxisDual, finCoord, gammaEff_eq_one_of_alpha_zero]

end Gravity

end DstDiophantine
