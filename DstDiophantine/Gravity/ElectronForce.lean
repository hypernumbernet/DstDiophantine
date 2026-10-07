import DstDiophantine.Gravity.ElectronSquare
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Electron–proton force along the equal-scale ray

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. Nothing here produces a Bohr spectrum.
The critical phase is not identified with a decimal, a spectroscopic shell,
or an equilibrium. No centrifugal term is added.

## What is proved

* Counted with attraction positive, the electron–proton force at phase
  `x = ℓ/(2r)` is `4x²/γ_s(x)`.
* On the outer well `(0, x₁)` this force is positive and strictly increasing
  in the phase.
* On the first repulsive shell `(x₁, x₂)` the same force is negative, so an
  unlike pair is driven back toward the first node.
* On the first repulsive shell it has exactly one critical point. The phase
  lies in `(5/2, π)`, so the radius `1/(2x)` lies in `(1/(2π), 1/5)`.
* The attraction-positive value there lies strictly between `-3` and `0`.
  At `x = π` the value is `-4π²/cosh π`, which is strictly less than `-3`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set

/-! ### Attraction-positive force -/

/-- Dimensionless electron–proton force, attraction positive, at phase `x`. -/
noncomputable def pairAttraction (x : ℝ) : ℝ :=
  4 * x ^ 2 / gammaSEqual x

/-- Numerator of the derivative of `x ↦ x²/γ_s(x)`. -/
noncomputable def forceCrit (x : ℝ) : ℝ :=
  gammaSEqual x + x * cosh x * sin x

theorem hasDerivAt_pairAttraction {x : ℝ} (hγ : gammaSEqual x ≠ 0) :
    HasDerivAt pairAttraction (8 * x * forceCrit x / gammaSEqual x ^ 2) x := by
  unfold pairAttraction
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [pow_one] using hasDerivAt_pow 2 x
  have hnum : HasDerivAt (fun y : ℝ => 4 * y ^ 2) (8 * x) x := by
    have h := hsq.const_mul 4
    have heq : 4 * (2 * x) = 8 * x := by ring
    rwa [heq] at h
  have hdiv := hnum.fun_div (hasDerivAt_gammaSEqual x) hγ
  refine hdiv.congr_deriv ?_
  unfold forceCrit
  ring

theorem deriv_pairAttraction {x : ℝ} (hγ : gammaSEqual x ≠ 0) :
    deriv pairAttraction x = 8 * x * forceCrit x / gammaSEqual x ^ 2 :=
  (hasDerivAt_pairAttraction hγ).deriv

private theorem continuousOn_pairAttraction {s : Set ℝ}
    (hs : ∀ x ∈ s, gammaSEqual x ≠ 0) : ContinuousOn pairAttraction s := by
  refine ContinuousOn.div ?_ continuous_gammaSEqual.continuousOn hs
  exact (by continuity : Continuous fun y : ℝ => 4 * y ^ 2).continuousOn

theorem pairAttraction_pi : pairAttraction π = -plateauForceFactor 1 := by
  unfold pairAttraction plateauForceFactor
  have hγ : gammaSEqual π = -cosh π := by
    simpa [Nat.cast_one, one_mul, pow_one] using gammaSEqual_nat_mul_pi 1
  rw [hγ]
  simp only [Nat.cast_one, one_pow, one_mul, mul_one, div_neg]

/-! ### One-sided Taylor bounds on `[0, ∞)` -/

private lemma sin_lower_cubic {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ sin x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · exact (sin_gt_sub_cube hx).le

private theorem hasDerivAt_cosUpper (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 24 - cos s)
      (sin t - (t - t ^ 3 / 6)) t := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa [pow_one] using hasDerivAt_pow 2 t
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 4 t
  have h := ((hasDerivAt_const t (1 : ℝ)).sub (h2.div_const 2)).add (h4.div_const 24)
      |>.sub (hasDerivAt_cos t)
  refine h.congr_deriv ?_
  ring

private lemma cos_upper_quartic {x : ℝ} (hx : 0 ≤ x) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun s => 1 - s ^ 2 / 2 + s ^ 4 / 24 - cos s
  have hmono : MonotoneOn f (Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      (by continuity : Continuous f).continuousOn
      (fun t ht => (hasDerivAt_cosUpper t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hasDerivAt_cosUpper t).deriv]
        exact sub_nonneg.mpr (sin_lower_cubic ht.1.le))
  have h0 : f 0 = 0 := by simp [f]
  have hle := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [f, h0] using hle

private theorem hasDerivAt_sinUpper (t : ℝ) :
    HasDerivAt (fun s : ℝ => s - s ^ 3 / 6 + s ^ 5 / 120 - sin s)
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t) t := by
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 3 t
  have h5 : HasDerivAt (fun s : ℝ => s ^ 5) (5 * t ^ 4) t := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 5 t
  have h := ((hasDerivAt_id t).sub (h3.div_const 6)).add (h5.div_const 120)
      |>.sub (hasDerivAt_sin t)
  refine h.congr_deriv ?_
  ring

private lemma sin_upper_quintic {x : ℝ} (hx : 0 ≤ x) :
    sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℝ → ℝ := fun s => s - s ^ 3 / 6 + s ^ 5 / 120 - sin s
  have hmono : MonotoneOn f (Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      (by continuity : Continuous f).continuousOn
      (fun t ht => (hasDerivAt_sinUpper t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hasDerivAt_sinUpper t).deriv]
        exact sub_nonneg.mpr (cos_upper_quartic ht.1.le))
  have h0 : f 0 = 0 := by simp [f]
  have hle := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  have : 0 ≤ f x := by simpa [h0] using hle
  simpa [f] using this

private theorem hasDerivAt_cosLower (t : ℝ) :
    HasDerivAt (fun s : ℝ => cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720))
      (t - t ^ 3 / 6 + t ^ 5 / 120 - sin t) t := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa [pow_one] using hasDerivAt_pow 2 t
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 4 t
  have h6 : HasDerivAt (fun s : ℝ => s ^ 6) (6 * t ^ 5) t := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 6 t
  have hpoly := ((hasDerivAt_const t (1 : ℝ)).sub (h2.div_const 2)).add (h4.div_const 24)
      |>.sub (h6.div_const 720)
  have h := (hasDerivAt_cos t).sub hpoly
  refine h.congr_deriv ?_
  ring

private lemma cos_lower_sextic {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ cos x := by
  let f : ℝ → ℝ := fun s => cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)
  have hmono : MonotoneOn f (Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      (by continuity : Continuous f).continuousOn
      (fun t ht => (hasDerivAt_cosLower t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hasDerivAt_cosLower t).deriv]
        have hsin := sin_upper_quintic ht.1.le
        linarith)
  have h0 : f 0 = 0 := by simp [f]
  have hle := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  have : 0 ≤ f x := by simpa [h0] using hle
  simpa [f] using this

/-! ### Polynomial comparison on `[0, 1]` -/

private noncomputable def polySin3 (x : ℝ) : ℝ := x - x ^ 3 / 6

private noncomputable def polySin5 (x : ℝ) : ℝ := x - x ^ 3 / 6 + x ^ 5 / 120

private noncomputable def polyCos4 (x : ℝ) : ℝ := 1 - x ^ 2 / 2 + x ^ 4 / 24

private noncomputable def polyCos6 (x : ℝ) : ℝ := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720

private theorem hasDerivAt_polySin3 (x : ℝ) :
    HasDerivAt polySin3 (1 - x ^ 2 / 2) x := by
  unfold polySin3
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * x ^ 2) x := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 3 x
  have h := (hasDerivAt_id x).sub (h3.div_const 6)
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_polySin5 (x : ℝ) :
    HasDerivAt polySin5 (1 - x ^ 2 / 2 + x ^ 4 / 24) x := by
  unfold polySin5
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * x ^ 2) x := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 3 x
  have h5 : HasDerivAt (fun s : ℝ => s ^ 5) (5 * x ^ 4) x := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 5 x
  have h := ((hasDerivAt_id x).sub (h3.div_const 6)).add (h5.div_const 120)
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_polyCos4 (x : ℝ) :
    HasDerivAt polyCos4 (-x + x ^ 3 / 6) x := by
  unfold polyCos4
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa [pow_one] using hasDerivAt_pow 2 x
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * x ^ 3) x := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 4 x
  have h := ((hasDerivAt_const x (1 : ℝ)).sub (h2.div_const 2)).add (h4.div_const 24)
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_polyCos6 (x : ℝ) :
    HasDerivAt polyCos6 (-x + x ^ 3 / 6 - x ^ 5 / 120) x := by
  unfold polyCos6
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa [pow_one] using hasDerivAt_pow 2 x
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * x ^ 3) x := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 4 x
  have h6 : HasDerivAt (fun s : ℝ => s ^ 6) (6 * x ^ 5) x := by
    simpa [pow_succ, pow_one] using hasDerivAt_pow 6 x
  have h := (((hasDerivAt_const x (1 : ℝ)).sub (h2.div_const 2)).add (h4.div_const 24)).sub
      (h6.div_const 720)
  refine h.congr_deriv ?_
  ring

private lemma mono_polySin3 : MonotoneOn polySin3 (Icc 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    (by unfold polySin3; continuity : Continuous polySin3).continuousOn
    (fun x _ => (hasDerivAt_polySin3 x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hasDerivAt_polySin3 x).deriv]
      nlinarith [sq_nonneg x, hx.1, hx.2])

private lemma mono_polySin5 : MonotoneOn polySin5 (Icc 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    (by unfold polySin5; continuity : Continuous polySin5).continuousOn
    (fun x _ => (hasDerivAt_polySin5 x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hasDerivAt_polySin5 x).deriv]
      nlinarith [sq_nonneg x, hx.1, hx.2])

private lemma anti_polyCos4 : AntitoneOn polyCos4 (Icc 0 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    (by unfold polyCos4; continuity : Continuous polyCos4).continuousOn
    (fun x _ => (hasDerivAt_polyCos4 x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hasDerivAt_polyCos4 x).deriv]
      have hfac : -x + x ^ 3 / 6 = -x * (1 - x ^ 2 / 6) := by ring
      rw [hfac]
      have h1 : 0 < 1 - x ^ 2 / 6 := by
        have hsq : x ^ 2 < 1 := by
          have hpow := pow_lt_pow_left₀ hx.2 hx.1.le (by decide : (2 : ℕ) ≠ 0)
          simpa using hpow
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.1]) h1.le)

private lemma anti_polyCos6 : AntitoneOn polyCos6 (Icc 0 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    (by unfold polyCos6; continuity : Continuous polyCos6).continuousOn
    (fun x _ => (hasDerivAt_polyCos6 x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hasDerivAt_polyCos6 x).deriv]
      have hfac : -x + x ^ 3 / 6 - x ^ 5 / 120 =
          -x * (1 - x ^ 2 / 6 + x ^ 4 / 120) := by ring
      rw [hfac]
      have hquad : 0 < 1 - x ^ 2 / 6 + x ^ 4 / 120 := by
        nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), hx.1, hx.2]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.1]) hquad.le)

/-! ### The shift `5/2 = π/2 + ε` -/

private lemma eps_window :
    (9292035 / 10000000 : ℝ) < 5 / 2 - π / 2 ∧
      5 / 2 - π / 2 < 929204 / 1000000 := by
  have hlo : π < 3141593 / 1000000 := by
    have h := pi_lt_d6
    norm_num at h
    exact h
  have hhi : 3141592 / 1000000 < π := by
    have h := pi_gt_d6
    norm_num at h
    have heq : (392699 / 125000 : ℝ) = 3141592 / 1000000 := by norm_num
    linarith
  constructor <;> linarith

private lemma five_halves_lt_pi : (5 / 2 : ℝ) < π := by
  linarith [pi_gt_three]

private lemma pi_div_two_lt_five_halves : π / 2 < (5 / 2 : ℝ) := by
  have h : π < 4 := by
    have hπ := pi_lt_d2
    norm_num at hπ
    linarith
  linarith

private lemma sin_five_halves :
    sin (5 / 2) = cos (5 / 2 - π / 2) := by
  have harg : 5 / 2 = π / 2 + (5 / 2 - π / 2) := by ring
  rw [harg, sin_add, sin_pi_div_two, cos_pi_div_two]
  simp

private lemma cos_five_halves :
    cos (5 / 2) = -sin (5 / 2 - π / 2) := by
  have harg : 5 / 2 = π / 2 + (5 / 2 - π / 2) := by ring
  rw [harg, cos_add, sin_pi_div_two, cos_pi_div_two]
  simp

private noncomputable def critU (x : ℝ) : ℝ := cos x + (x - 1) * sin x

private noncomputable def critV (x : ℝ) : ℝ := cos x + (x + 1) * sin x

private noncomputable def critP (x : ℝ) : ℝ := (x - 1) * sin x + x * cos x

private noncomputable def critQ (x : ℝ) : ℝ := x * cos x - (x + 1) * sin x

private lemma forceCrit_exp (x : ℝ) :
    forceCrit x = (exp x * critU x + exp (-x) * critV x) / 2 := by
  unfold forceCrit critU critV gammaSEqual
  rw [cosh_eq, sinh_eq]
  ring

private theorem hasDerivAt_critU (x : ℝ) :
    HasDerivAt critU ((x - 1) * cos x) x := by
  unfold critU
  have hlin : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    have h := (hasDerivAt_id x).sub (hasDerivAt_const x (1 : ℝ))
    refine h.congr_deriv ?_
    ring
  have h := (hasDerivAt_cos x).add (hlin.mul (hasDerivAt_sin x))
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_critV (x : ℝ) :
    HasDerivAt critV ((x + 1) * cos x) x := by
  unfold critV
  have hlin : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    have h := (hasDerivAt_id x).add (hasDerivAt_const x (1 : ℝ))
    refine h.congr_deriv ?_
    ring
  have h := (hasDerivAt_cos x).add (hlin.mul (hasDerivAt_sin x))
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_critP (x : ℝ) :
    HasDerivAt critP (x * cos x + (1 - x) * sin x) x := by
  unfold critP
  have hlin : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    have h := (hasDerivAt_id x).sub (hasDerivAt_const x (1 : ℝ))
    refine h.congr_deriv ?_
    ring
  have h := (hlin.mul (hasDerivAt_sin x)).add ((hasDerivAt_id x).mul (hasDerivAt_cos x))
  refine h.congr_deriv ?_
  simp only [id_eq]
  ring

private lemma critU_five_halves_pos : 0 < critU (5 / 2) := by
  have hε := eps_window
  set ε : ℝ := 5 / 2 - π / 2
  have hb1 : (929204 / 1000000 : ℝ) ≤ 1 := by norm_num
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2, hb1]⟩
  have hbI : (929204 / 1000000 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, hb1⟩
  have hsin : sin ε ≤ polySin5 (929204 / 1000000) := by
    have h1 := sin_upper_quintic hεI.1
    have h2 := mono_polySin5 hεI hbI hε.2.le
    unfold polySin5 at *
    linarith
  have hcos : polyCos6 (929204 / 1000000) ≤ cos ε := by
    have h1 := cos_lower_sextic hεI.1
    have h2 := anti_polyCos6 hεI hbI hε.2.le
    unfold polyCos6 at *
    linarith
  have hU : critU (5 / 2) = -sin ε + (3 / 2) * cos ε := by
    unfold critU
    rw [sin_five_halves, cos_five_halves]
    ring
  have hlo : 0 < -polySin5 (929204 / 1000000) +
      (3 / 2) * polyCos6 (929204 / 1000000) := by
    unfold polySin5 polyCos6
    norm_num
  linarith

private lemma critV_five_halves_pos : 0 < critV (5 / 2) := by
  have hε := eps_window
  set ε : ℝ := 5 / 2 - π / 2
  have hb1 : (929204 / 1000000 : ℝ) ≤ 1 := by norm_num
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2, hb1]⟩
  have hbI : (929204 / 1000000 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, hb1⟩
  have hsin : sin ε ≤ polySin5 (929204 / 1000000) := by
    have h1 := sin_upper_quintic hεI.1
    have h2 := mono_polySin5 hεI hbI hε.2.le
    unfold polySin5 at *
    linarith
  have hcos : polyCos6 (929204 / 1000000) ≤ cos ε := by
    have h1 := cos_lower_sextic hεI.1
    have h2 := anti_polyCos6 hεI hbI hε.2.le
    unfold polyCos6 at *
    linarith
  have hV : critV (5 / 2) = -sin ε + (7 / 2) * cos ε := by
    unfold critV
    rw [sin_five_halves, cos_five_halves]
    ring
  have hlo : 0 < -polySin5 (929204 / 1000000) +
      (7 / 2) * polyCos6 (929204 / 1000000) := by
    unfold polySin5 polyCos6
    norm_num
  linarith

private lemma critU_strictAnti : StrictAntiOn critU (Icc (π / 2) (5 / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold critU; continuity : Continuous critU).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_critU x).deriv]
  have hbound : (5 : ℝ) / 2 < π + π / 2 := by linarith [pi_gt_three]
  have hcos : cos x < 0 :=
    cos_neg_of_pi_div_two_lt_of_lt hx.1 (lt_trans hx.2 hbound)
  have hx1 : 0 < x - 1 := by linarith [hx.1, pi_gt_three]
  exact mul_neg_of_pos_of_neg hx1 hcos

private lemma critV_strictAnti : StrictAntiOn critV (Icc (π / 2) (5 / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold critV; continuity : Continuous critV).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_critV x).deriv]
  have hbound : (5 : ℝ) / 2 < π + π / 2 := by linarith [pi_gt_three]
  have hcos : cos x < 0 :=
    cos_neg_of_pi_div_two_lt_of_lt hx.1 (lt_trans hx.2 hbound)
  exact mul_neg_of_pos_of_neg (by linarith [hx.1, pi_pos]) hcos

private lemma critU_pos_on {x : ℝ} (hx : x ∈ Icc (π / 2) (5 / 2)) : 0 < critU x := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · exact critU_five_halves_pos
  · exact lt_trans critU_five_halves_pos
      (critU_strictAnti hx (right_mem_Icc.mpr pi_div_two_lt_five_halves.le) hlt)

private lemma critV_pos_on {x : ℝ} (hx : x ∈ Icc (π / 2) (5 / 2)) : 0 < critV x := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · exact critV_five_halves_pos
  · exact lt_trans critV_five_halves_pos
      (critV_strictAnti hx (right_mem_Icc.mpr pi_div_two_lt_five_halves.le) hlt)

private lemma forceCrit_pos_through_five_halves {x : ℝ}
    (hx : x ∈ Icc (π / 2) (5 / 2)) : 0 < forceCrit x := by
  rw [forceCrit_exp]
  have hU := critU_pos_on hx
  have hV := critV_pos_on hx
  have hsum : 0 < exp x * critU x + exp (-x) * critV x :=
    add_pos (mul_pos (exp_pos x) hU) (mul_pos (exp_pos (-x)) hV)
  exact div_pos hsum (by norm_num)

/-! ### Sign of the critical numerator -/

private theorem hasDerivAt_radialWeight (t : ℝ) :
    HasDerivAt (fun s : ℝ => s * cosh s - sinh s) (t * sinh t) t := by
  have h := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
  refine h.congr_deriv ?_
  simp only [id_eq]
  ring

private lemma radialWeight_pos {x : ℝ} (hx : 0 < x) : 0 < x * cosh x - sinh x := by
  have hmono : StrictMonoOn (fun t : ℝ => t * cosh t - sinh t) (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
      (by continuity : Continuous fun t : ℝ => t * cosh t - sinh t).continuousOn ?_
    intro t ht
    rw [interior_Ici] at ht
    rw [(hasDerivAt_radialWeight t).deriv]
    exact mul_pos ht (sinh_pos_iff.mpr ht)
  have hlt := hmono (by simp : (0 : ℝ) ∈ Ici 0) (mem_Ici.mpr hx.le) hx
  simpa using hlt

private lemma forceCrit_expand (x : ℝ) :
    forceCrit x = cosh x * cos x + (x * cosh x - sinh x) * sin x := by
  unfold forceCrit gammaSEqual
  ring

theorem forceCrit_pos_of_le_pi_div_two {x : ℝ} (hx0 : 0 < x) (hxπ : x ≤ π / 2) :
    0 < forceCrit x := by
  rw [forceCrit_expand]
  have hcos : 0 ≤ cos x :=
    cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hxπ
  have hsin : 0 < sin x :=
    sin_pos_of_pos_of_lt_pi hx0 (lt_of_le_of_lt hxπ (half_lt_self pi_pos))
  have hw := radialWeight_pos hx0
  have h1 : 0 ≤ cosh x * cos x := mul_nonneg (cosh_pos x).le hcos
  have h2 : 0 < (x * cosh x - sinh x) * sin x := mul_pos hw hsin
  linarith

private lemma forceCrit_pos_up_to_five_halves {x : ℝ}
    (hx1 : resonanceRoot1 < x) (hx2 : x ≤ 5 / 2) : 0 < forceCrit x := by
  have hx0 : 0 < x := by linarith [hx1, resonanceRoot1_sharp_bounds.1, pi_pos]
  by_cases h : x ≤ π / 2
  · exact forceCrit_pos_of_le_pi_div_two hx0 h
  · push Not at h
    exact forceCrit_pos_through_five_halves ⟨h.le, hx2⟩

theorem forceCrit_pos_outer {x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1) :
    0 < forceCrit x := by
  have hxπ : x ≤ π / 2 := by
    linarith [hx.2, resonanceRoot1_sharp_bounds.2, pi_gt_three]
  exact forceCrit_pos_of_le_pi_div_two hx.1 hxπ

theorem pairAttraction_pos_outer {x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1) :
    0 < pairAttraction x := by
  unfold pairAttraction
  exact div_pos (by nlinarith [hx.1]) (gammaSEqual_pos_left_of_first_node hx)

/-- `γ_s` stays negative from the first node up to the next node. -/
private theorem gamma_neg_on_first_shell {x : ℝ}
    (hx : x ∈ Ioo resonanceRoot1 (branchNode 1)) : gammaSEqual x < 0 := by
  rcases le_or_gt x π with hle | hgt
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · have hπ : gammaSEqual π = -cosh π := by
        simpa [Nat.cast_one, one_mul] using gammaSEqual_nat_mul_pi 1
      linarith [cosh_pos π]
    · exact gammaSEqual_neg_right_of_first_node ⟨hx.1, hlt⟩
  · have hnode := (branchNode_spec 1).1
    have hzero : gammaSEqual (branchNode 1) = 0 := (branchNode_spec 1).2
    have hup : branchNode 1 < π + π := by
      simpa [Nat.cast_one, one_mul] using hnode.2
    have hlo : π < branchNode 1 := by
      simpa [Nat.cast_one, one_mul] using hnode.1
    have hxI : x ∈ Icc π (π + π) := ⟨hgt.le, le_of_lt (lt_trans hx.2 hup)⟩
    have hnI : branchNode 1 ∈ Icc π (π + π) := ⟨hlo.le, hup.le⟩
    have hlt := strictMonoOn_gammaSEqual_odd 0 (by simpa using hxI) (by simpa using hnI) hx.2
    rwa [hzero] at hlt

/-- Inside the first repulsive shell the attraction-positive force is negative,
so an unlike pair is driven back toward the first node. -/
theorem pairAttraction_neg_first_shell {x : ℝ}
    (hx : x ∈ Ioo resonanceRoot1 (branchNode 1)) : pairAttraction x < 0 := by
  unfold pairAttraction
  exact div_neg_of_pos_of_neg (by nlinarith [hx.1, resonanceRoot1_bounds.1])
    (gamma_neg_on_first_shell hx)

theorem pairAttraction_strictMono_outer :
    StrictMonoOn pairAttraction (Ioo 0 resonanceRoot1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 resonanceRoot1)
    (continuousOn_pairAttraction fun x hx => (gammaSEqual_pos_left_of_first_node hx).ne') ?_
  intro x hx
  rw [interior_Ioo] at hx
  have hγ : gammaSEqual x ≠ 0 := (gammaSEqual_pos_left_of_first_node hx).ne'
  rw [deriv_pairAttraction hγ]
  exact div_pos (mul_pos (mul_pos (by norm_num) hx.1) (forceCrit_pos_outer hx))
    (sq_pos_of_ne_zero hγ)

private lemma critP_five_halves_neg : critP (5 / 2) < 0 := by
  have hε := eps_window
  set ε : ℝ := 5 / 2 - π / 2
  have ha1 : (9292035 / 10000000 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hb1 : (929204 / 1000000 : ℝ) ≤ 1 := by norm_num
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2, hb1]⟩
  have hsin : polySin3 (9292035 / 10000000) ≤ sin ε := by
    have h1 := sin_lower_cubic hεI.1
    have h2 := mono_polySin3 ha1 hεI (le_of_lt hε.1)
    unfold polySin3 at *
    linarith
  have hcos : cos ε ≤ polyCos4 (9292035 / 10000000) := by
    have h1 := cos_upper_quartic hεI.1
    have h2 := anti_polyCos4 ha1 hεI (le_of_lt hε.1)
    unfold polyCos4 at *
    linarith
  have hP : critP (5 / 2) = (3 / 2) * cos ε - (5 / 2) * sin ε := by
    unfold critP
    rw [sin_five_halves, cos_five_halves]
    ring
  have hhi : (3 / 2) * polyCos4 (9292035 / 10000000) -
      (5 / 2) * polySin3 (9292035 / 10000000) < 0 := by
    unfold polyCos4 polySin3
    norm_num
  linarith

private lemma critP_strictAnti : StrictAntiOn critP (Icc (5 / 2) π) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold critP; continuity : Continuous critP).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_critP x).deriv]
  have hsin : 0 < sin x := sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) hx.2
  have hcos : cos x < 0 :=
    cos_neg_of_pi_div_two_lt_of_lt (by linarith [hx.1, pi_div_two_lt_five_halves])
      (by linarith [hx.2, pi_pos])
  have h1 : x * cos x < 0 := mul_neg_of_pos_of_neg (by linarith [hx.1]) hcos
  have h2 : (1 - x) * sin x < 0 := mul_neg_of_neg_of_pos (by linarith [hx.1]) hsin
  linarith

private lemma critP_neg_of_ge_five_halves {x : ℝ} (hx : x ∈ Icc (5 / 2) π) :
    critP x < 0 := by
  rcases eq_or_lt_of_le hx.1 with rfl | hlt
  · exact critP_five_halves_neg
  · exact lt_trans (critP_strictAnti (left_mem_Icc.mpr five_halves_lt_pi.le) hx hlt)
      critP_five_halves_neg

private lemma critQ_neg {x : ℝ} (hx1 : π / 2 < x) (hx2 : x < π) : critQ x < 0 := by
  unfold critQ
  have hsin : 0 < sin x := sin_pos_of_pos_of_lt_pi (by linarith) hx2
  have hcos : cos x < 0 := cos_neg_of_pi_div_two_lt_of_lt hx1 (by linarith [pi_pos])
  have h1 : x * cos x < 0 := mul_neg_of_pos_of_neg (by linarith) hcos
  have h2 : 0 < (x + 1) * sin x := mul_pos (by linarith) hsin
  linarith

private theorem hasDerivAt_forceCrit (x : ℝ) :
    HasDerivAt forceCrit ((x * sinh x - cosh x) * sin x + x * cosh x * cos x) x := by
  unfold forceCrit
  have hmul : HasDerivAt (fun y : ℝ => y * cosh y * sin y)
      (cosh x * sin x + x * sinh x * sin x + x * cosh x * cos x) x := by
    have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).mul (hasDerivAt_sin x)
    refine h.congr_deriv ?_
    simp only [id_eq, Pi.mul_apply]
    ring
  have h := (hasDerivAt_gammaSEqual x).add hmul
  refine h.congr_deriv ?_
  ring

private lemma forceCrit_deriv_factor (x : ℝ) :
    (x * sinh x - cosh x) * sin x + x * cosh x * cos x =
      exp (-x) / 2 * (exp (2 * x) * critP x + critQ x) := by
  have hL : (x * sinh x - cosh x) * sin x + x * cosh x * cos x =
      (exp x * critP x + exp (-x) * critQ x) / 2 := by
    unfold critP critQ
    rw [sinh_eq, cosh_eq]
    ring
  have hR : exp (-x) / 2 * (exp (2 * x) * critP x + critQ x) =
      (exp x * critP x + exp (-x) * critQ x) / 2 := by
    have h2 : exp (2 * x) = exp x * exp x := by
      rw [show (2 : ℝ) * x = x + x by ring, exp_add]
    have hc : exp x * exp (-x) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
    have hcomm : exp (-x) * exp x = exp x * exp (-x) := by ring
    rw [h2]
    have hdist : exp (-x) / 2 * (exp x * exp x * critP x + critQ x) =
        (exp (-x) * exp x * exp x * critP x + exp (-x) * critQ x) / 2 := by ring
    rw [hdist, hcomm, hc]
    ring
  rw [hL, hR]

private lemma continuous_forceCrit : Continuous forceCrit := by
  unfold forceCrit
  exact continuous_gammaSEqual.add ((continuous_id.mul continuous_cosh).mul continuous_sin)

private lemma forceCrit_strictAnti : StrictAntiOn forceCrit (Icc (5 / 2) π) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_forceCrit.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_forceCrit x).deriv, forceCrit_deriv_factor]
  have hxπ2 : π / 2 < x := by linarith [hx.1, pi_div_two_lt_five_halves]
  have hP := critP_neg_of_ge_five_halves ⟨hx.1.le, hx.2.le⟩
  have hQ := critQ_neg hxπ2 hx.2
  have hsum : exp (2 * x) * critP x + critQ x < 0 := by
    have hEP : exp (2 * x) * critP x < 0 := mul_neg_of_pos_of_neg (exp_pos _) hP
    linarith
  exact mul_neg_of_pos_of_neg (by positivity) hsum

theorem forceCrit_pi : forceCrit π = -cosh π := by
  unfold forceCrit
  have hγ : gammaSEqual π = -cosh π := by
    simpa [Nat.cast_one, one_mul, pow_one] using gammaSEqual_nat_mul_pi 1
  rw [hγ, sin_pi]
  ring

private lemma forceCrit_five_halves_pos : 0 < forceCrit (5 / 2) :=
  forceCrit_pos_through_five_halves ⟨pi_div_two_lt_five_halves.le, le_rfl⟩

private lemma forceCrit_pi_neg : forceCrit π < 0 := by
  rw [forceCrit_pi]
  linarith [cosh_pos π]

theorem exists_unique_forceQuiet :
    ∃! x : ℝ, x ∈ Ioo (5 / 2) π ∧ forceCrit x = 0 := by
  have hmem : (0 : ℝ) ∈ Ioo (forceCrit π) (forceCrit (5 / 2)) :=
    ⟨forceCrit_pi_neg, forceCrit_five_halves_pos⟩
  obtain ⟨x, hx, hx0⟩ :=
    intermediate_value_Ioo' five_halves_lt_pi.le continuous_forceCrit.continuousOn hmem
  refine ⟨x, ⟨hx, hx0⟩, ?_⟩
  intro y hy
  exact (forceCrit_strictAnti.injOn
    ⟨hy.1.1.le, hy.1.2.le⟩ ⟨hx.1.le, hx.2.le⟩ (by rw [hy.2, hx0]))

private lemma branchNode_one_gt_pi : π < branchNode 1 := by
  simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1

private lemma forceCrit_neg_after_pi {x : ℝ} (hx : x ∈ Ioo π (branchNode 1)) :
    forceCrit x < 0 := by
  have hγ : gammaSEqual x < 0 := by
    have hzero : gammaSEqual (branchNode 1) = 0 := (branchNode_spec 1).2
    have hlo : ((1 : ℕ) : ℝ) * π < x := by
      simpa [Nat.cast_one, one_mul] using hx.1
    have hup : branchNode 1 < ((1 : ℕ) : ℝ) * π + π := (branchNode_spec 1).1.2
    have hxI : x ∈ Icc (((1 : ℕ) : ℝ) * π) (((1 : ℕ) : ℝ) * π + π) :=
      ⟨hlo.le, le_of_lt (lt_trans hx.2 hup)⟩
    have hnlo : ((1 : ℕ) : ℝ) * π ≤ branchNode 1 := by
      simpa [Nat.cast_one, one_mul] using branchNode_one_gt_pi.le
    have hnI : branchNode 1 ∈ Icc (((1 : ℕ) : ℝ) * π) (((1 : ℕ) : ℝ) * π + π) :=
      ⟨hnlo, hup.le⟩
    have hlt := strictMonoOn_gammaSEqual_odd 0 hxI hnI hx.2
    rwa [hzero] at hlt
  have hsin : sin x < 0 := by
    have hmem : x ∈ Ioo (((1 : ℕ) : ℝ) * π) (((1 : ℕ) : ℝ) * π + π) :=
      ⟨by simpa [Nat.cast_one, one_mul] using hx.1, lt_trans hx.2 (branchNode_spec 1).1.2⟩
    have hs := signed_sin_pos_on_branch 1 hmem
    simp only [pow_one] at hs
    linarith
  have hterm : x * cosh x * sin x < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by linarith [pi_pos, hx.1]) (cosh_pos x)) hsin
  unfold forceCrit
  linarith

theorem forceQuiet_shell_phase {x : ℝ}
    (hx : x ∈ Ioo resonanceRoot1 (branchNode 1)) (h0 : forceCrit x = 0) :
    x ∈ Ioo (5 / 2) π := by
  refine ⟨?_, ?_⟩
  · by_contra hle
    have hx2 : x ≤ 5 / 2 := le_of_not_gt hle
    exact (ne_of_gt (forceCrit_pos_up_to_five_halves hx.1 hx2)) h0
  · by_contra hge
    have hxπ : π ≤ x := le_of_not_gt hge
    rcases eq_or_lt_of_le hxπ with rfl | hgt
    · rw [forceCrit_pi] at h0
      exact (neg_ne_zero.mpr (cosh_pos π).ne') h0
    · exact (ne_of_lt (forceCrit_neg_after_pi ⟨hgt, hx.2⟩)) h0

theorem exists_unique_forceQuiet_shell :
    ∃! x : ℝ, x ∈ Ioo resonanceRoot1 (branchNode 1) ∧ forceCrit x = 0 := by
  obtain ⟨x, hx, huniq⟩ := exists_unique_forceQuiet
  have hxshell : x ∈ Ioo resonanceRoot1 (branchNode 1) :=
    ⟨by linarith [hx.1.1, resonanceRoot1_sharp_bounds.2], lt_trans hx.1.2 branchNode_one_gt_pi⟩
  refine ⟨x, ⟨hxshell, hx.2⟩, ?_⟩
  intro y hy
  have hyphase : y ∈ Ioo (5 / 2) π := forceQuiet_shell_phase hy.1 hy.2
  exact huniq y ⟨hyphase, hy.2⟩

/-! ### Magnitude against `3` -/

private lemma gamma_five_halves_lt : gammaSEqual (5 / 2) < -25 / 3 := by
  have hε := eps_window
  set ε : ℝ := 5 / 2 - π / 2
  let E0 : ℝ := (2.7182818283 : ℝ) ^ 2 * (164 / 100)
  let E1 : ℝ := (2.7182818286 : ℝ) ^ 2 * (165 / 100)
  let sLo : ℝ := polySin3 (9292035 / 10000000)
  let sHi : ℝ := polySin5 (929204 / 1000000)
  let cLo : ℝ := polyCos6 (929204 / 1000000)
  let cHi : ℝ := polyCos4 (9292035 / 10000000)
  have haI : (9292035 / 10000000 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hb1 : (929204 / 1000000 : ℝ) ≤ 1 := by norm_num
  have hbI : (929204 / 1000000 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, hb1⟩
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2, hb1]⟩
  have hsLo : sLo ≤ sin ε := by
    have h1 := sin_lower_cubic hεI.1
    have h2 := mono_polySin3 haI hεI (le_of_lt hε.1)
    simpa [sLo, polySin3] using le_trans h2 h1
  have hsHi : sin ε ≤ sHi := by
    have h1 := sin_upper_quintic hεI.1
    have h2 := mono_polySin5 hεI hbI hε.2.le
    simpa [sHi, polySin5] using le_trans h1 h2
  have hcLo : cLo ≤ cos ε := by
    have h1 := cos_lower_sextic hεI.1
    have h2 := anti_polyCos6 hεI hbI hε.2.le
    simpa [cLo, polyCos6] using le_trans h2 h1
  have hcHi : cos ε ≤ cHi := by
    have h1 := cos_upper_quartic hεI.1
    have h2 := anti_polyCos4 haI hεI (le_of_lt hε.1)
    simpa [cHi, polyCos4] using le_trans h1 h2
  have hE0 : E0 < exp (5 / 2) := by
    have hid : exp (5 / 2) = exp 1 * exp 1 * exp (1 / 2) := by
      rw [show (5 / 2 : ℝ) = 1 + 1 + 1 / 2 by norm_num, exp_add, exp_add]
    dsimp [E0]
    nlinarith [exp_one_gt_d9, exp_half_bounds.1, exp_pos 1, exp_pos (1 / 2), hid]
  have hE1 : exp (5 / 2) < E1 := by
    have hid : exp (5 / 2) = exp 1 * exp 1 * exp (1 / 2) := by
      rw [show (5 / 2 : ℝ) = 1 + 1 + 1 / 2 by norm_num, exp_add, exp_add]
    dsimp [E1]
    nlinarith [exp_one_lt_d9, exp_half_bounds.2, exp_pos 1, hid]
  have hDhi : -(sLo + cLo) < 0 := by
    dsimp [sLo, cLo, polySin3, polyCos6]
    norm_num
  have hShi : -sLo + cHi < 0 := by
    dsimp [sLo, cHi, polySin3, polyCos4]
    norm_num
  have hnum : E0 / 2 * -(sLo + cLo) + (-sLo + cHi) / (2 * E1) < -25 / 3 := by
    dsimp [E0, E1, sLo, cLo, cHi, polySin3, polyCos4, polyCos6]
    norm_num
  have hsinx : sin (5 / 2) = cos ε := sin_five_halves
  have hcosx : cos (5 / 2) = -sin ε := cos_five_halves
  set D : ℝ := cos (5 / 2) - sin (5 / 2)
  set S : ℝ := cos (5 / 2) + sin (5 / 2)
  have hDle : D ≤ -(sLo + cLo) := by
    dsimp [D]
    rw [hsinx, hcosx]
    linarith
  have hSle : S ≤ -sLo + cHi := by
    dsimp [S]
    rw [hsinx, hcosx]
    linarith
  have hDneg : D < 0 := lt_of_le_of_lt hDle hDhi
  have hSneg : S < 0 := lt_of_le_of_lt hSle hShi
  have hE0pos : 0 < E0 := by dsimp [E0]; norm_num
  have hE1pos : 0 < E1 := by dsimp [E1]; norm_num
  have hterm1 : exp (5 / 2) * D < E0 * -(sLo + cLo) := by
    exact lt_of_lt_of_le (mul_lt_mul_of_neg_right hE0 hDneg)
      (mul_le_mul_of_nonneg_left hDle hE0pos.le)
  have hinv : E1⁻¹ < exp (-(5 / 2)) := by
    rw [exp_neg]
    exact (inv_lt_inv₀ hE1pos (exp_pos _)).mpr hE1
  have hterm2 : exp (-(5 / 2)) * S < E1⁻¹ * (-sLo + cHi) := by
    exact lt_of_lt_of_le (mul_lt_mul_of_neg_right hinv hSneg)
      (mul_le_mul_of_nonneg_left hSle (inv_nonneg.mpr hE1pos.le))
  have hhalf1 : exp (5 / 2) / 2 * D < E0 / 2 * -(sLo + cLo) := by
    calc exp (5 / 2) / 2 * D = exp (5 / 2) * D / 2 := by ring
      _ < E0 * -(sLo + cLo) / 2 := div_lt_div_of_pos_right hterm1 (by norm_num)
      _ = E0 / 2 * -(sLo + cLo) := by ring
  have hhalf2 : exp (-(5 / 2)) / 2 * S < (-sLo + cHi) / (2 * E1) := by
    calc exp (-(5 / 2)) / 2 * S = exp (-(5 / 2)) * S / 2 := by ring
      _ < (E1⁻¹ * (-sLo + cHi)) / 2 := div_lt_div_of_pos_right hterm2 (by norm_num)
      _ = (-sLo + cHi) / (2 * E1) := by field_simp
  have hγ := gammaSEqual_exp (5 / 2)
  have hlt : gammaSEqual (5 / 2) < E0 / 2 * -(sLo + cLo) + (-sLo + cHi) / (2 * E1) := by
    rw [hγ, show cos (5 / 2) - sin (5 / 2) = D by rfl,
      show cos (5 / 2) + sin (5 / 2) = S by rfl]
    linarith
  linarith

private lemma pairAttraction_five_halves :
    pairAttraction (5 / 2) = 25 / gammaSEqual (5 / 2) := by
  unfold pairAttraction
  have hγ : gammaSEqual (5 / 2) ≠ 0 := (lt_trans gamma_five_halves_lt (by norm_num)).ne
  have hsq : (5 / 2 : ℝ) ^ 2 = 25 / 4 := by norm_num
  rw [hsq]
  field_simp [hγ]

private lemma pairAttraction_five_halves_gt_neg_three : -3 < pairAttraction (5 / 2) := by
  rw [pairAttraction_five_halves]
  have hγ : gammaSEqual (5 / 2) < -25 / 3 := gamma_five_halves_lt
  have hneg : gammaSEqual (5 / 2) < 0 := lt_trans hγ (by norm_num)
  have hnum : 25 + 3 * gammaSEqual (5 / 2) < 0 := by linarith
  have hpos : 0 < (25 + 3 * gammaSEqual (5 / 2)) / gammaSEqual (5 / 2) :=
    div_pos_of_neg_of_neg hnum hneg
  have hid : 25 / gammaSEqual (5 / 2) - (-3) =
      (25 + 3 * gammaSEqual (5 / 2)) / gammaSEqual (5 / 2) := by
    field_simp [hneg.ne]
    ring
  rw [← sub_pos, hid]
  exact hpos

private lemma gamma_neg_on_quiet {t : ℝ} (ht1 : 5 / 2 ≤ t) (ht2 : t < π) :
    gammaSEqual t < 0 :=
  gammaSEqual_neg_right_of_first_node
    ⟨by linarith [ht1, resonanceRoot1_sharp_bounds.2], ht2⟩

theorem forceQuiet_magnitude {x : ℝ} (hx : x ∈ Ioo (5 / 2) π) (h0 : forceCrit x = 0) :
    -3 < pairAttraction x ∧ pairAttraction x < 0 := by
  have hmono : StrictMonoOn pairAttraction (Icc (5 / 2) x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · exact continuousOn_pairAttraction fun t ht =>
        (gamma_neg_on_quiet ht.1 (lt_of_le_of_lt ht.2 hx.2)).ne
    · intro t ht
      rw [interior_Icc] at ht
      have hγ : gammaSEqual t ≠ 0 :=
        (gamma_neg_on_quiet ht.1.le (lt_trans ht.2 hx.2)).ne
      rw [deriv_pairAttraction hγ]
      have hcrit : 0 < forceCrit t := by
        have hlt := forceCrit_strictAnti ⟨ht.1.le, le_trans ht.2.le hx.2.le⟩
          ⟨hx.1.le, hx.2.le⟩ ht.2
        linarith [h0]
      have ht0 : 0 < t := by linarith [ht.1]
      exact div_pos (mul_pos (mul_pos (by norm_num) ht0) hcrit) (sq_pos_of_ne_zero hγ)
  have hgt : pairAttraction (5 / 2) < pairAttraction x :=
    hmono ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1
  have hneg : pairAttraction x < 0 := by
    unfold pairAttraction
    exact div_neg_of_pos_of_neg (by nlinarith [hx.1]) (gamma_neg_on_quiet hx.1.le hx.2)
  exact ⟨lt_trans pairAttraction_five_halves_gt_neg_three hgt, hneg⟩

theorem three_cosh_pi_lt_four_pi_sq : 3 * cosh π < 4 * π ^ 2 := by
  have hπlo : 3141592 / 1000000 < π := by
    have h := pi_gt_d6
    norm_num at h
    have heq : (392699 / 125000 : ℝ) = 3141592 / 1000000 := by norm_num
    linarith
  have hπhi : π < 3141593 / 1000000 := by
    have h := pi_lt_d6
    norm_num at h
    exact h
  have hδ0 : 0 ≤ π - 3 := by linarith [pi_gt_three]
  have hδ1 : π - 3 < 1 := by linarith
  have hexp : exp (π - 3) ≤ 1 / (4 - π) := by
    have h := exp_bound_div_one_sub_of_interval hδ0 hδ1
    rwa [show (1 : ℝ) - (π - 3) = 4 - π by ring] at h
  have h4 : 858407 / 1000000 < 4 - π := by linarith
  have hrec : 1 / (4 - π) < 1000000 / 858407 := by
    have hpos1 : (0 : ℝ) < 4 - π := by linarith
    have hpos2 : (0 : ℝ) < 858407 / 1000000 := by norm_num
    calc 1 / (4 - π) = (4 - π)⁻¹ := by ring
      _ < (858407 / 1000000)⁻¹ := (inv_lt_inv₀ hpos1 hpos2).mpr h4
      _ = 1000000 / 858407 := by norm_num
  have hexplt : exp (π - 3) < 1000000 / 858407 := lt_of_le_of_lt hexp hrec
  have he3 : exp 3 < (2.7182818286 : ℝ) ^ 3 := by
    have hid : exp 3 = exp 1 ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, exp_nat_mul]
    rw [hid]
    exact pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos _).le (by decide)
  have hprod : exp π < (2.7182818286 : ℝ) ^ 3 * (1000000 / 858407) := by
    have hsplit : exp π = exp 3 * exp (π - 3) := by
      rw [← exp_add]
      ring_nf
    rw [hsplit]
    exact mul_lt_mul he3 hexplt.le (exp_pos _) (by positivity)
  have hcmp : 3 * ((2.7182818286 : ℝ) ^ 3 * (1000000 / 858407)) + 3 <
      8 * (3141592 / 1000000) ^ 2 := by
    norm_num
  have hsq : (3141592 / 1000000 : ℝ) ^ 2 < π ^ 2 :=
    pow_lt_pow_left₀ hπlo (by norm_num) (by decide)
  have h8 : 3 * (exp π + 1) < 8 * π ^ 2 := by
    have hleft : 3 * (exp π + 1) < 3 * ((2.7182818286 : ℝ) ^ 3 * (1000000 / 858407)) + 3 := by
      linarith
    have hmid : 3 * ((2.7182818286 : ℝ) ^ 3 * (1000000 / 858407)) + 3 <
        8 * (3141592 / 1000000) ^ 2 := hcmp
    have hright : 8 * (3141592 / 1000000) ^ 2 < 8 * π ^ 2 := by
      exact mul_lt_mul_of_pos_left hsq (by norm_num)
    linarith
  have hcosh : cosh π < (exp π + 1) / 2 := by
    rw [cosh_eq]
    have hneg : exp (-π) < 1 := by
      rw [← exp_zero]
      exact exp_strictMono (by linarith [pi_pos])
    linarith
  calc 3 * cosh π < 3 * ((exp π + 1) / 2) := by
        exact mul_lt_mul_of_pos_left hcosh (by norm_num)
    _ = 3 * (exp π + 1) / 2 := by ring
    _ < 4 * π ^ 2 := by
        rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith [h8]

theorem pairAttraction_pi_lt_neg_three : pairAttraction π < -3 := by
  rw [pairAttraction_pi]
  have hfac : plateauForceFactor 1 = 4 * π ^ 2 / cosh π := by
    unfold plateauForceFactor
    simp only [Nat.cast_one, one_pow, one_mul, mul_one]
  rw [hfac]
  have hc : 0 < cosh π := cosh_pos π
  have hdiv : 3 < 4 * π ^ 2 / cosh π := by
    rw [lt_div_iff₀ hc]
    linarith [three_cosh_pi_lt_four_pi_sq]
  linarith

theorem forceQuiet_radius {x : ℝ} (hx : x ∈ Ioo (5 / 2) π) :
    1 / (2 * π) < 1 / (2 * x) ∧ 1 / (2 * x) < 1 / 5 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hπ0 : 0 < π := pi_pos
  refine ⟨?_, ?_⟩
  · have hinv : 1 / π < 1 / x := by
      rw [one_div, one_div]
      exact (inv_lt_inv₀ hπ0 hx0).mpr hx.2
    calc 1 / (2 * π) = (1 / π) / 2 := by ring
      _ < (1 / x) / 2 := div_lt_div_of_pos_right hinv (by norm_num)
      _ = 1 / (2 * x) := by ring
  · have h52 : (0 : ℝ) < 5 / 2 := by norm_num
    have hinv : 1 / x < 2 / 5 := by
      calc 1 / x = x⁻¹ := one_div x
        _ < (5 / 2)⁻¹ := (inv_lt_inv₀ hx0 h52).mpr hx.1
        _ = 2 / 5 := by norm_num
    calc 1 / (2 * x) = (1 / x) / 2 := by ring
      _ < (2 / 5) / 2 := div_lt_div_of_pos_right hinv (by norm_num)
      _ = 1 / 5 := by ring

end Gravity

end DstDiophantine
