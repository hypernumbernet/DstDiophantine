import DstDiophantine.Gravity.CompactS3
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Dual image lattice and the galactic rotation curve

The \(S^3\) chart of `CompactS3` places the images of a source along the
radius, at spacing \(\pi R\): \(1/(R^2\sin^2(r/R))=\sum_n 1/(r-n\pi R)^2\).
The image at \(r=\pi R\) is the antipode, and there the circular speed has no
finite value. Here the same period is laid along the dual direction. Image
\(n\) sits at squared distance \(r^2+(n\pi R)^2\), and the lattice sum is

\[
\sum_{n\in\mathbb Z}\frac{GM}{r^2+(n\pi R)^2}=\frac{GM}{rR}\coth\frac rR .
\]

The ratio to the Newtonian term is the dual enhancement \(x\coth x\), with
\(x=r/R\). These are theorems: the lattice identity, from the Mittag-Leffler
expansion of the cotangent; \(\max(1,x)<x\coth x<\min(1+x,\,1+x^2/3)\) for
\(x>0\); strict increase; limit \(1\) at the origin; \(\coth\) strictly
decreasing to \(1\). On the chart: the acceleration exceeds Newton by less
than \(GM/(3R^2)\) and by less than \(GM/(rR)\), and exceeds \(GM/(rR)\);
\(v^2=(GM(r)/R)\coth(r/R)=v_{\mathrm{bar}}^2\,x\coth x\); a Newtonian
baryonic curve with \(r\,v_{\mathrm{bar}}^2\to GM\) tends to \(GM/R\); a
regular centre gives \(v\to 0\); outside the mass \(v^2\) strictly decreases,
and past \(3R\) it lies within \(1/200\) of \(GM/R\). Given
\(R^2=GM/a_0\): \((GM/R)^2=GMa_0\), \((GM/(rR))^2=a_0\,GM/r^2\), and
\(x^2\,GM/r^2=a_0\), so the lattice acceleration is
\(g=\sqrt{a_0g_N}\coth\sqrt{a_0/g_N}\), with
\(\max(g_N,\sqrt{a_0g_N})<g<g_N+\min(\sqrt{a_0g_N},a_0/3)\). Read on the
patch of the enclosed mass, \(v^2=r\,g(v_{\mathrm{bar}}^2/r)\) lies between
\(\max(v_{\mathrm{bar}}^2,\sqrt{a_0rv_{\mathrm{bar}}^2})\) and
\(v_{\mathrm{bar}}^2+\sqrt{a_0rv_{\mathrm{bar}}^2}\), and a Keplerian tail
flattens at \(\sqrt{GMa_0}\). At \(GM/r^2=a_0\) the enhancement is
\(\coth 1\in(1.31,1.32)\). On the SI stand-ins the Milky-Way \(GMa_0\) lies between
\((175\,\mathrm{km/s})^4\) and \((176\,\mathrm{km/s})^4\), and the
\(S^3\) antipode \(\pi R\) between \(25\) and \(29\,\mathrm{kpc}\); the
\(S^3\) shape \(f\) tends to \(+\infty\) at \(\pi^-\).

The lattice reading, \(R^2=GM/a_0\), and \(a_0\) itself are inputs. No
theorem asserts `dst_derives_a0`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Filter Topology SI

/-- Dual-image enhancement \(x\coth x\). -/
noncomputable def dualEnhancement (x : ℝ) : ℝ :=
  x * cosh x / sinh x

/-! ### Lattice identity -/

private theorem mem_integerComplement_mul_I {y : ℝ} (hy : y ≠ 0) :
    (y : ℂ) * Complex.I ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have him := congrArg Complex.im hn
  simp at him
  exact hy him.symm

private theorem cotTerm_mul_I (y : ℝ) (hy : y ≠ 0) (n : ℕ) :
    1 / ((y : ℂ) * Complex.I - (n + 1)) + 1 / ((y : ℂ) * Complex.I + (n + 1)) =
      ((-2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) * Complex.I := by
  have hpos : (0 : ℝ) < y ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
  have h1 : (y : ℂ) * Complex.I - (n + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h2 : (y : ℂ) * Complex.I + (n + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h3 : ((y ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  push_cast at h3 ⊢
  field_simp
  linear_combination (2 * (y : ℂ) ^ 3 * Complex.I) * Complex.I_sq

private theorem pi_cot_mul_I (y : ℝ) (hy : y ≠ 0) :
    (π : ℂ) * Complex.cot ((π : ℂ) * ((y : ℂ) * Complex.I)) - 1 / ((y : ℂ) * Complex.I) =
      ((-(π * cosh (π * y) / sinh (π * y) - 1 / y) : ℝ) : ℂ) * Complex.I := by
  have hs : sinh (π * y) ≠ 0 := by
    rw [Ne, sinh_eq_zero]
    exact mul_ne_zero pi_ne_zero hy
  have harg : (π : ℂ) * ((y : ℂ) * Complex.I) = ((π * y : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I]
  have hs' : (sinh (π * y) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  rw [← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem hasSum_inv_sq_add_succ_sq {y : ℝ} (hy : y ≠ 0) :
    HasSum (fun n : ℕ => 1 / (y ^ 2 + ((n : ℝ) + 1) ^ 2))
      (π * cosh (π * y) / (2 * y * sinh (π * y)) - 1 / (2 * y ^ 2)) := by
  have hz := mem_integerComplement_mul_I hy
  have hsum := (summable_cotTerm hz).hasSum
  rw [← cot_series_rep' hz] at hsum
  simp only [cotTerm] at hsum
  have hsum' : HasSum (fun n : ℕ => ((-2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) *
      Complex.I) (((-(π * cosh (π * y) / sinh (π * y) - 1 / y)) : ℝ) * Complex.I) := by
    rw [← pi_cot_mul_I y hy]
    convert hsum using 1
    funext n
    rw [cotTerm_mul_I y hy n]
  have hreal : HasSum (fun n : ℕ => -2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2))
      (-(π * cosh (π * y) / sinh (π * y) - 1 / y)) := by
    have := hsum'.mul_right (-Complex.I)
    simp only [mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, mul_one] at this
    exact_mod_cast this
  have := hreal.mul_left (-1 / (2 * y))
  have hs : sinh (π * y) ≠ 0 := by
    rw [Ne, sinh_eq_zero]
    exact mul_ne_zero pi_ne_zero hy
  convert this using 1
  · rfl
  · funext n
    field_simp
  · field_simp

/-- The dual image lattice: \(\sum_{n\in\mathbb Z} x^2/(x^2+(n\pi)^2)=x\coth x\). -/
theorem hasSum_dualImage {x : ℝ} (hx : x ≠ 0) :
    HasSum (fun n : ℤ => x ^ 2 / (x ^ 2 + ((n : ℝ) * π) ^ 2)) (dualEnhancement x) := by
  obtain ⟨y, rfl⟩ : ∃ y : ℝ, x = π * y := ⟨x / π, by field_simp⟩
  have hy : y ≠ 0 := right_ne_zero_of_mul hx
  have hterm : ∀ m : ℝ, (π * y) ^ 2 / ((π * y) ^ 2 + (m * π) ^ 2) =
      y ^ 2 * (1 / (y ^ 2 + m ^ 2)) := by
    intro m
    have hy2 : 0 < y ^ 2 := (sq_pos_iff).mpr hy
    have hd1 : y ^ 2 + m ^ 2 ≠ 0 := (add_pos_of_pos_of_nonneg hy2 (sq_nonneg m)).ne'
    have hd2 : (π * y) ^ 2 + (m * π) ^ 2 ≠ 0 := by
      have : 0 < (π * y) ^ 2 := (sq_pos_iff).mpr hx
      exact (add_pos_of_pos_of_nonneg this (sq_nonneg _)).ne'
    field_simp
  set f : ℤ → ℝ := fun k => (π * y) ^ 2 / ((π * y) ^ 2 + ((k : ℝ) * π) ^ 2) with hf
  set S : ℝ := y ^ 2 * (π * cosh (π * y) / (2 * y * sinh (π * y)) - 1 / (2 * y ^ 2)) with hS
  have h := (hasSum_inv_sq_add_succ_sq hy).mul_left (y ^ 2)
  have hpos : HasSum (fun n : ℕ => f ((n : ℤ) + 1)) S := by
    have hfun : (fun n : ℕ => f ((n : ℤ) + 1)) =
        fun n : ℕ => y ^ 2 * (1 / (y ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
      funext n
      simp only [hf]
      push_cast
      exact hterm _
    rw [hfun]
    exact h
  have hneg : HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) S := by
    have hfun : (fun n : ℕ => f (-((n : ℤ) + 1))) =
        fun n : ℕ => y ^ 2 * (1 / (y ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
      funext n
      simp only [hf]
      push_cast
      rw [hterm, neg_sq]
    rw [hfun]
    exact h
  have hall := HasSum.of_add_one_of_neg_add_one hpos hneg
  have hval : S + f 0 + S = dualEnhancement (π * y) := by
    have hs : sinh (π * y) ≠ 0 := by rw [Ne, sinh_eq_zero]; exact hx
    have h0 : f 0 = 1 := by simp [hf, hy, pi_ne_zero]
    rw [h0, hS]
    unfold dualEnhancement
    field_simp
    ring
  rw [← hval]
  exact hall

/-! ### Hyperbolic bounds -/

theorem coth_eq_one_add {x : ℝ} (hx : x ≠ 0) :
    cosh x / sinh x = 1 + 2 / (exp (2 * x) - 1) := by
  have hs : sinh x ≠ 0 := by rw [Ne, sinh_eq_zero]; exact hx
  have hE : exp (2 * x) - 1 ≠ 0 := by
    have : exp (2 * x) ≠ 1 := by
      rw [Ne, exp_eq_one_iff]
      exact mul_ne_zero two_ne_zero hx
    exact sub_ne_zero.mpr this
  have h2 : exp (2 * x) = exp x * exp x := by rw [two_mul, exp_add]
  have he : exp x ≠ 0 := (exp_pos x).ne'
  have hrhs : 1 + 2 / (exp (2 * x) - 1) = (exp (2 * x) + 1) / (exp (2 * x) - 1) := by
    field_simp
    ring
  rw [hrhs, div_eq_div_iff hs hE, sinh_eq, cosh_eq, exp_neg, h2]
  field_simp

private theorem one_lt_coth {x : ℝ} (hx : 0 < x) : 1 < cosh x / sinh x := by
  rw [coth_eq_one_add hx.ne']
  have : 1 < exp (2 * x) := one_lt_exp_iff.mpr (by positivity)
  have : 0 < 2 / (exp (2 * x) - 1) := div_pos two_pos (by linarith)
  linarith

theorem strictAntiOn_coth : StrictAntiOn (fun x : ℝ => cosh x / sinh x) (Ioi 0) := by
  intro a ha b hb hab
  simp only
  rw [coth_eq_one_add (ne_of_gt ha), coth_eq_one_add (ne_of_gt hb)]
  have ha1 : 0 < exp (2 * a) - 1 := by
    have : 1 < exp (2 * a) := one_lt_exp_iff.mpr (by linarith [mem_Ioi.mp ha])
    linarith
  have hlt : exp (2 * a) - 1 < exp (2 * b) - 1 := by
    have := exp_lt_exp.mpr (by linarith : 2 * a < 2 * b)
    linarith
  have := div_lt_div_of_pos_left two_pos ha1 hlt
  linarith

theorem tendsto_coth_atTop : Tendsto (fun x : ℝ => cosh x / sinh x) atTop (𝓝 1) := by
  have hE : Tendsto (fun x : ℝ => exp (2 * x) - 1) atTop atTop := by
    have h := tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop two_pos)
    have := tendsto_atTop_add_const_right atTop (-1) h
    simpa [sub_eq_add_neg, Function.comp] using this
  have h2 : Tendsto (fun x : ℝ => 1 + 2 / (exp (2 * x) - 1)) atTop (𝓝 (1 + 0)) :=
    (tendsto_const_nhds.div_atTop hE).const_add 1
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact (coth_eq_one_add hx.ne').symm

theorem self_lt_dualEnhancement {x : ℝ} (hx : 0 < x) : x < dualEnhancement x := by
  unfold dualEnhancement
  rw [mul_div_assoc]
  have := one_lt_coth hx
  nlinarith

private theorem sinh_lt_mul_cosh {x : ℝ} (hx : 0 < x) : sinh x < x * cosh x := by
  have hmono : StrictMonoOn (fun t : ℝ => t * cosh t - sinh t) (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      ((continuous_id.mul continuous_cosh).sub continuous_sinh).continuousOn ?_
    intro t ht
    rw [interior_Ici] at ht
    have hd : HasDerivAt (fun t : ℝ => t * cosh t - sinh t) (t * sinh t) t :=
      (((hasDerivAt_id' t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)).congr_deriv
        (by ring)
    rw [hd.deriv]
    exact mul_pos ht (sinh_pos_iff.mpr ht)
  have := hmono (mem_Ici.mpr le_rfl) (show x ∈ Ici (0 : ℝ) from hx.le) hx
  simp at this
  linarith

theorem one_lt_dualEnhancement {x : ℝ} (hx : 0 < x) : 1 < dualEnhancement x := by
  unfold dualEnhancement
  rw [one_lt_div (sinh_pos_iff.mpr hx)]
  exact sinh_lt_mul_cosh hx

theorem dualEnhancement_lt_one_add {x : ℝ} (hx : 0 < x) : dualEnhancement x < 1 + x := by
  unfold dualEnhancement
  rw [mul_div_assoc, coth_eq_one_add hx.ne']
  have hE : 2 * x + 1 < exp (2 * x) := add_one_lt_exp (by positivity)
  have hpos : 0 < exp (2 * x) - 1 := by linarith
  have : 2 * x / (exp (2 * x) - 1) < 1 := by
    rw [div_lt_one hpos]; linarith
  have heq : x * (1 + 2 / (exp (2 * x) - 1)) = x + 2 * x / (exp (2 * x) - 1) := by
    field_simp
  rw [heq]
  linarith

private theorem mul_cosh_lt {x : ℝ} (hx : 0 < x) :
    x * cosh x < (1 + x * x / 3) * sinh x := by
  have hmono :
      StrictMonoOn (fun t : ℝ => (1 + t * t / 3) * sinh t - t * cosh t) (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (((continuous_const.add ((continuous_id.mul continuous_id).div_const 3)).mul
        continuous_sinh).sub (continuous_id.mul continuous_cosh)).continuousOn ?_
    intro t ht
    rw [interior_Ici] at ht
    have hd : HasDerivAt (fun t : ℝ => (1 + t * t / 3) * sinh t - t * cosh t)
        (t / 3 * (t * cosh t - sinh t)) t := by
      have h1 : HasDerivAt (fun t : ℝ => 1 + t * t / 3) ((1 * t + t * 1) / 3) t :=
        (((hasDerivAt_id' t).mul (hasDerivAt_id' t)).div_const 3).const_add 1
      exact ((h1.mul (hasDerivAt_sinh t)).sub
        ((hasDerivAt_id' t).mul (hasDerivAt_cosh t))).congr_deriv (by ring)
    rw [hd.deriv]
    have ht0 : 0 < t := ht
    have := sinh_lt_mul_cosh ht0
    exact mul_pos (div_pos ht0 (by norm_num)) (by linarith)
  have := hmono (mem_Ici.mpr le_rfl) (show x ∈ Ici (0 : ℝ) from hx.le) hx
  simp at this
  linarith

theorem dualEnhancement_lt_one_add_sq_div_three {x : ℝ} (hx : 0 < x) :
    dualEnhancement x < 1 + x ^ 2 / 3 := by
  unfold dualEnhancement
  rw [div_lt_iff₀ (sinh_pos_iff.mpr hx), sq]
  exact mul_cosh_lt hx

theorem strictMonoOn_dualEnhancement : StrictMonoOn dualEnhancement (Ioi 0) := by
  change StrictMonoOn (fun y : ℝ => y * cosh y / sinh y) (Ioi 0)
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    exact ((continuous_id.mul continuous_cosh).continuousAt.div continuous_sinh.continuousAt
      (sinh_pos_iff.mpr hx).ne').continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hs := sinh_pos_iff.mpr hx
    have hd : HasDerivAt (fun y : ℝ => y * cosh y / sinh y)
        ((sinh x * cosh x - x) / sinh x ^ 2) x := by
      refine (((hasDerivAt_id' x).mul (hasDerivAt_cosh x)).div (hasDerivAt_sinh x)
        hs.ne').congr_deriv ?_
      rw [div_left_inj' (pow_ne_zero 2 hs.ne')]
      simp only [Pi.mul_apply]
      linear_combination (-x) * cosh_sq_sub_sinh_sq x
    rw [hd.deriv]
    have hx0 : 0 < x := hx
    have h2 : 2 * x < sinh (2 * x) := self_lt_sinh_iff.mpr (by positivity)
    rw [sinh_two_mul] at h2
    exact div_pos (by linarith) (pow_pos hs 2)

theorem tendsto_dualEnhancement_zero : Tendsto dualEnhancement (𝓝[>] 0) (𝓝 1) := by
  have hup : Tendsto (fun x : ℝ => 1 + x ^ 2 / 3) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun x : ℝ => 1 + x ^ 2 / 3) (𝓝 0) (𝓝 (1 + 0 ^ 2 / 3)) :=
      (continuous_const.add ((continuous_pow 2).div_const 3)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx using (one_lt_dualEnhancement hx).le
  · filter_upwards [self_mem_nhdsWithin] with x hx using
      (dualEnhancement_lt_one_add_sq_div_three hx).le

/-! ### Acceleration of the lattice -/

/-- Inward acceleration of the dual image lattice about a mass `M`. -/
noncomputable def dualAccel (G M R r : ℝ) : ℝ :=
  G * M / (r * R) * (cosh (r / R) / sinh (r / R))

theorem dualAccel_eq_newton_mul {G M R r : ℝ} (hr : r ≠ 0) (hR : R ≠ 0) :
    dualAccel G M R r = G * M / r ^ 2 * dualEnhancement (r / R) := by
  have hs : sinh (r / R) ≠ 0 := by rw [Ne, sinh_eq_zero]; exact div_ne_zero hr hR
  unfold dualAccel dualEnhancement
  field_simp

/-- Each winding of the dual phase contributes \(GM/(r^2+(n\pi R)^2)\). -/
theorem hasSum_dualAccel {G M R r : ℝ} (hr : r ≠ 0) (hR : R ≠ 0) :
    HasSum (fun n : ℤ => G * M / (r ^ 2 + ((n : ℝ) * π * R) ^ 2)) (dualAccel G M R r) := by
  have hx : r / R ≠ 0 := div_ne_zero hr hR
  have h := (hasSum_dualImage hx).mul_left (G * M / r ^ 2)
  rw [← dualAccel_eq_newton_mul hr hR] at h
  have hfun : (fun n : ℤ => G * M / (r ^ 2 + ((n : ℝ) * π * R) ^ 2)) =
      fun n : ℤ => G * M / r ^ 2 * ((r / R) ^ 2 / ((r / R) ^ 2 + ((n : ℝ) * π) ^ 2)) := by
    funext n
    have hr2 : 0 < r ^ 2 := (sq_pos_iff).mpr hr
    have hd1 : r ^ 2 + ((n : ℝ) * π * R) ^ 2 ≠ 0 :=
      (add_pos_of_pos_of_nonneg hr2 (sq_nonneg _)).ne'
    have hx2 : 0 < (r / R) ^ 2 := (sq_pos_iff).mpr hx
    have hd2 : (r / R) ^ 2 + ((n : ℝ) * π) ^ 2 ≠ 0 :=
      (add_pos_of_pos_of_nonneg hx2 (sq_nonneg _)).ne'
    field_simp
  rw [hfun]
  exact h

theorem dualAccel_bounds {G M R r : ℝ} (hGM : 0 < G * M) (hR : 0 < R) (hr : 0 < r) :
    G * M / r ^ 2 < dualAccel G M R r ∧ G * M / (r * R) < dualAccel G M R r ∧
      dualAccel G M R r < G * M / r ^ 2 + G * M / (r * R) ∧
      dualAccel G M R r < G * M / r ^ 2 + G * M / (3 * R ^ 2) := by
  have hx : 0 < r / R := div_pos hr hR
  have hN : 0 < G * M / r ^ 2 := by positivity
  rw [dualAccel_eq_newton_mul hr.ne' hR.ne']
  have e1 := one_lt_dualEnhancement hx
  have e2 := self_lt_dualEnhancement hx
  have e3 := dualEnhancement_lt_one_add hx
  have e4 := dualEnhancement_lt_one_add_sq_div_three hx
  have k1 : G * M / r ^ 2 * (r / R) = G * M / (r * R) := by
    field_simp
  have k2 : G * M / r ^ 2 * ((r / R) ^ 2 / 3) = G * M / (3 * R ^ 2) := by
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc G * M / r ^ 2 = G * M / r ^ 2 * 1 := (mul_one _).symm
      _ < _ := mul_lt_mul_of_pos_left e1 hN
  · rw [← k1]
    exact mul_lt_mul_of_pos_left e2 hN
  · calc _ < G * M / r ^ 2 * (1 + r / R) := mul_lt_mul_of_pos_left e3 hN
      _ = _ := by rw [mul_add, mul_one, k1]
  · calc _ < G * M / r ^ 2 * (1 + (r / R) ^ 2 / 3) := mul_lt_mul_of_pos_left e4 hN
      _ = _ := by rw [mul_add, mul_one, k2]

/-! ### Rotation curve -/

/-- Rotation curve from a Newtonian baryonic curve `vbarSq`:
\(v^2=v_{\mathrm{bar}}^2\,x\coth x\). -/
noncomputable def dualRotationSq (R : ℝ) (vbarSq : ℝ → ℝ) (r : ℝ) : ℝ :=
  vbarSq r * dualEnhancement (r / R)

/-- Circular speed squared about an enclosed mass `M r`: \((GM(r)/R)\coth(r/R)\). -/
noncomputable def dualCircularSpeedSq (G R : ℝ) (M : ℝ → ℝ) (r : ℝ) : ℝ :=
  G * M r / R * (cosh (r / R) / sinh (r / R))

theorem dualCircularSpeedSq_eq_mul_accel {G R r : ℝ} {M : ℝ → ℝ} (hr : r ≠ 0) :
    dualCircularSpeedSq G R M r = r * dualAccel G (M r) R r := by
  unfold dualCircularSpeedSq dualAccel
  field_simp

theorem dualRotationSq_spherical {G R r : ℝ} {M : ℝ → ℝ} (hr : r ≠ 0) (hR : R ≠ 0) :
    dualRotationSq R (fun s => G * M s / s) r = dualCircularSpeedSq G R M r := by
  have hs : sinh (r / R) ≠ 0 := by rw [Ne, sinh_eq_zero]; exact div_ne_zero hr hR
  unfold dualRotationSq dualCircularSpeedSq dualEnhancement
  field_simp

/-- A baryonic curve with Keplerian tail \(r\,v_{\mathrm{bar}}^2\to GM\) flattens at \(GM/R\). -/
theorem tendsto_dualRotationSq_atTop {R GM : ℝ} {vbarSq : ℝ → ℝ} (hR : 0 < R)
    (h : Tendsto (fun r => r * vbarSq r) atTop (𝓝 GM)) :
    Tendsto (dualRotationSq R vbarSq) atTop (𝓝 (GM / R)) := by
  have hc : Tendsto (fun r : ℝ => cosh (r / R) / sinh (r / R)) atTop (𝓝 1) :=
    tendsto_coth_atTop.comp (tendsto_id.atTop_div_const hR)
  have hprod := (h.div_const R).mul hc
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  unfold dualRotationSq dualEnhancement
  field_simp

theorem dualCircularSpeedSq_bounds {G R r : ℝ} {M : ℝ → ℝ}
    (hGM : 0 < G * M r) (hR : 0 < R) (hr : 0 < r) :
    G * M r / R < dualCircularSpeedSq G R M r ∧
      dualCircularSpeedSq G R M r < G * M r / r + G * M r / R := by
  rw [dualCircularSpeedSq_eq_mul_accel hr.ne']
  have hb := dualAccel_bounds hGM hR hr
  constructor
  · have := mul_lt_mul_of_pos_left hb.2.1 hr
    have heq : r * (G * M r / (r * R)) = G * M r / R := by field_simp
    linarith
  · have := mul_lt_mul_of_pos_left hb.2.2.1 hr
    have heq : r * (G * M r / r ^ 2 + G * M r / (r * R)) = G * M r / r + G * M r / R := by
      field_simp
    linarith

theorem strictAntiOn_dualCircularSpeedSq {G R M0 a : ℝ} {M : ℝ → ℝ}
    (hGM : 0 < G * M0) (hR : 0 < R) (ha : 0 ≤ a) (hM : ∀ r ∈ Ioi a, M r = M0) :
    StrictAntiOn (dualCircularSpeedSq G R M) (Ioi a) := by
  intro r hr s hs hrs
  have hr0 : 0 < r := lt_of_le_of_lt ha hr
  have hs0 : 0 < s := lt_of_le_of_lt ha hs
  unfold dualCircularSpeedSq
  rw [hM r hr, hM s hs]
  have hc := strictAntiOn_coth (mem_Ioi.mpr (div_pos hr0 hR)) (mem_Ioi.mpr (div_pos hs0 hR))
    (div_lt_div_of_pos_right hrs hR)
  exact mul_lt_mul_of_pos_left hc (div_pos hGM hR)

theorem tendsto_dualCircularSpeedSq_atTop {G R Mtot : ℝ} {M : ℝ → ℝ} (hR : 0 < R)
    (hM : Tendsto M atTop (𝓝 Mtot)) :
    Tendsto (dualCircularSpeedSq G R M) atTop (𝓝 (G * Mtot / R)) := by
  have hc : Tendsto (fun r : ℝ => cosh (r / R) / sinh (r / R)) atTop (𝓝 1) :=
    tendsto_coth_atTop.comp (tendsto_id.atTop_div_const hR)
  have h := ((hM.const_mul G).div_const R).mul hc
  rw [mul_one] at h
  exact h

theorem tendsto_dualCircularSpeedSq_zero {G R : ℝ} {M : ℝ → ℝ} (hR : 0 < R)
    (hM : Tendsto (fun r => M r / r) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (dualCircularSpeedSq G R M) (𝓝[>] 0) (𝓝 0) := by
  have hx : Tendsto (fun r : ℝ => r / R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun r : ℝ => r / R) (𝓝 0) (𝓝 (0 / R)) :=
        (continuous_id.div_const R).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact div_pos hr hR
  have h := (hM.const_mul G).mul (tendsto_dualEnhancement_zero.comp hx)
  rw [mul_zero, zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := (mem_Ioi.mp hr).ne'
  have hs : sinh (r / R) ≠ 0 := by rw [Ne, sinh_eq_zero]; exact div_ne_zero hr0 hR.ne'
  simp only [Function.comp, dualEnhancement, dualCircularSpeedSq]
  field_simp

/-! ### Tully–Fisher and the acceleration relation -/

theorem dual_tullyFisher {G M R a0 : ℝ} (hR : 0 < R) (ha0 : 0 < a0)
    (hscale : R ^ 2 = G * M / a0) :
    (G * M / R) ^ 2 = G * M * a0 := by
  have hGM : G * M = R ^ 2 * a0 := by
    rw [hscale]; field_simp
  rw [hGM]
  field_simp

theorem dual_rar {G M R a0 r : ℝ} (hR : 0 < R) (ha0 : 0 < a0) (hr : 0 < r)
    (hscale : R ^ 2 = G * M / a0) :
    (G * M / (r * R)) ^ 2 = a0 * (G * M / r ^ 2) ∧
      (r / R) ^ 2 * (G * M / r ^ 2) = a0 ∧ G * M / (3 * R ^ 2) = a0 / 3 := by
  have hGM : G * M = R ^ 2 * a0 := by
    rw [hscale]; field_simp
  rw [hGM]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-! ### The acceleration relation on the enclosed patch -/

/-- Dual acceleration relation \(g=\sqrt{a_0g_N}\,\coth\sqrt{a_0/g_N}\). -/
noncomputable def dualRAR (a0 gN : ℝ) : ℝ :=
  sqrt (a0 * gN) * (cosh (sqrt (a0 / gN)) / sinh (sqrt (a0 / gN)))

theorem dualAccel_eq_dualRAR {G M R a0 r : ℝ} (hGM : 0 < G * M) (hR : 0 < R) (ha0 : 0 < a0)
    (hr : 0 < r) (hscale : R ^ 2 = G * M / a0) :
    dualAccel G M R r = dualRAR a0 (G * M / r ^ 2) := by
  obtain ⟨h1, h2, -⟩ := dual_rar hR ha0 hr hscale
  have hgN : 0 < G * M / r ^ 2 := by positivity
  have hs1 : sqrt (a0 * (G * M / r ^ 2)) = G * M / (r * R) := by
    rw [← h1]; exact sqrt_sq (by positivity)
  have hs2 : sqrt (a0 / (G * M / r ^ 2)) = r / R := by
    rw [← h2, mul_div_assoc, div_self hgN.ne', mul_one]; exact sqrt_sq (by positivity)
  unfold dualAccel dualRAR
  rw [hs1, hs2]

theorem dualRAR_bounds {a0 gN : ℝ} (ha0 : 0 < a0) (hgN : 0 < gN) :
    gN < dualRAR a0 gN ∧ sqrt (a0 * gN) < dualRAR a0 gN ∧
      dualRAR a0 gN < gN + sqrt (a0 * gN) ∧ dualRAR a0 gN < gN + a0 / 3 := by
  set R := sqrt (gN / a0) with hRdef
  have hR : 0 < R := sqrt_pos.mpr (div_pos hgN ha0)
  have hscale : R ^ 2 = 1 * gN / a0 := by rw [one_mul, hRdef, sq_sqrt (div_pos hgN ha0).le]
  have hGM : (0 : ℝ) < 1 * gN := by linarith
  have heq := dualAccel_eq_dualRAR hGM hR ha0 one_pos hscale
  obtain ⟨h1, h2, h3, h4⟩ := dualAccel_bounds hGM hR one_pos
  obtain ⟨k1, -, k3⟩ := dual_rar hR ha0 one_pos hscale
  simp only [one_pow, div_one, one_mul] at heq h1 h2 h3 h4 k1 k3
  have hs : sqrt (a0 * gN) = gN / R := by
    rw [← k1]; exact sqrt_sq (div_pos hgN hR).le
  rw [← heq, hs, ← k3]
  exact ⟨h1, h2, h3, h4⟩

private theorem mul_sqrt_div {a0 r v : ℝ} (hr : 0 < r) :
    r * sqrt (a0 * (v / r)) = sqrt (a0 * (r * v)) := by
  calc r * sqrt (a0 * (v / r)) = sqrt (r ^ 2) * sqrt (a0 * (v / r)) := by rw [sqrt_sq hr.le]
    _ = sqrt (r ^ 2 * (a0 * (v / r))) := (sqrt_mul (sq_nonneg r) _).symm
    _ = sqrt (a0 * (r * v)) := by congr 1; field_simp

/-- Rotation curve on the enclosed patch, from a Newtonian baryonic curve `vbarSq`. -/
noncomputable def dualLocalRotationSq (a0 : ℝ) (vbarSq : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * dualRAR a0 (vbarSq r / r)

theorem dualLocalRotationSq_eq {a0 r : ℝ} {vbarSq : ℝ → ℝ} (ha0 : 0 < a0) (hr : 0 < r)
    (hv : 0 < vbarSq r) :
    dualLocalRotationSq a0 vbarSq r =
      vbarSq r * dualEnhancement (sqrt (a0 * r / vbarSq r)) := by
  have hdiv : a0 / (vbarSq r / r) = a0 * r / vbarSq r := by field_simp
  have hsq : r * sqrt (a0 * (vbarSq r / r)) = vbarSq r * sqrt (a0 * r / vbarSq r) := by
    rw [mul_sqrt_div hr]
    calc sqrt (a0 * (r * vbarSq r)) = sqrt (vbarSq r ^ 2 * (a0 * r / vbarSq r)) := by
          congr 1; field_simp
      _ = sqrt (vbarSq r ^ 2) * sqrt (a0 * r / vbarSq r) := sqrt_mul (sq_nonneg _) _
      _ = _ := by rw [sqrt_sq hv.le]
  unfold dualLocalRotationSq dualRAR dualEnhancement
  rw [hdiv, ← mul_assoc, hsq]
  ring

theorem dualLocalRotationSq_bounds {a0 r : ℝ} {vbarSq : ℝ → ℝ} (ha0 : 0 < a0) (hr : 0 < r)
    (hv : 0 < vbarSq r) :
    vbarSq r < dualLocalRotationSq a0 vbarSq r ∧
      sqrt (a0 * (r * vbarSq r)) < dualLocalRotationSq a0 vbarSq r ∧
      dualLocalRotationSq a0 vbarSq r < vbarSq r + sqrt (a0 * (r * vbarSq r)) := by
  obtain ⟨h1, h2, h3, -⟩ := dualRAR_bounds ha0 (div_pos hv hr)
  have hk : r * (vbarSq r / r) = vbarSq r := by field_simp
  unfold dualLocalRotationSq
  refine ⟨?_, ?_, ?_⟩
  · calc vbarSq r = r * (vbarSq r / r) := hk.symm
      _ < _ := mul_lt_mul_of_pos_left h1 hr
  · rw [← mul_sqrt_div hr]
    exact mul_lt_mul_of_pos_left h2 hr
  · calc _ < r * (vbarSq r / r + sqrt (a0 * (vbarSq r / r))) := mul_lt_mul_of_pos_left h3 hr
      _ = _ := by rw [mul_add, hk, mul_sqrt_div hr]

/-- A Keplerian baryonic tail \(r\,v_{\mathrm{bar}}^2\to GM\) flattens at \(\sqrt{GMa_0}\). -/
theorem tendsto_dualLocalRotationSq_atTop {a0 GM : ℝ} {vbarSq : ℝ → ℝ} (ha0 : 0 < a0)
    (hGM : 0 < GM) (h : Tendsto (fun r => r * vbarSq r) atTop (𝓝 GM)) :
    Tendsto (dualLocalRotationSq a0 vbarSq) atTop (𝓝 (sqrt (a0 * GM))) := by
  have hpos : ∀ᶠ r in atTop, 0 < r * vbarSq r := h.eventually (lt_mem_nhds hGM)
  have hs : Tendsto (fun r => sqrt (a0 * (r * vbarSq r))) atTop (𝓝 (sqrt (a0 * GM))) :=
    ((h.const_mul a0).sqrt)
  have hinv : Tendsto (fun r => a0 * (r * vbarSq r)⁻¹) atTop (𝓝 (a0 * GM⁻¹)) :=
    (h.inv₀ hGM.ne').const_mul a0
  have harg : Tendsto (fun r : ℝ => a0 * (r * vbarSq r)⁻¹ * r ^ 2) atTop atTop :=
    hinv.pos_mul_atTop (by positivity) (tendsto_pow_atTop two_ne_zero)
  have hc : Tendsto (fun r : ℝ => cosh (sqrt (a0 * (r * vbarSq r)⁻¹ * r ^ 2)) /
      sinh (sqrt (a0 * (r * vbarSq r)⁻¹ * r ^ 2))) atTop (𝓝 1) :=
    tendsto_coth_atTop.comp (tendsto_sqrt_atTop.comp harg)
  have hprod := hs.mul hc
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [hpos, eventually_gt_atTop 0] with r hp hr
  have hv : 0 < vbarSq r := pos_of_mul_pos_right hp hr.le
  have hdiv : a0 / (vbarSq r / r) = a0 * (r * vbarSq r)⁻¹ * r ^ 2 := by field_simp
  unfold dualLocalRotationSq dualRAR
  rw [hdiv, ← mul_assoc r, mul_sqrt_div hr]

/-! ### Numerical windows -/

theorem coth_one_bounds :
    (131 / 100 : ℝ) < cosh 1 / sinh 1 ∧ cosh 1 / sinh 1 < 132 / 100 := by
  rw [coth_eq_one_add one_ne_zero]
  have h2 : exp (2 * 1) = exp 1 ^ 2 := by
    rw [show (2 : ℝ) * 1 = 1 + 1 by norm_num, exp_add]; ring
  rw [h2]
  have he1 := exp_one_gt_d9
  have he2 := exp_one_lt_d9
  have hE1 : (73 / 10 : ℝ) < exp 1 ^ 2 := by nlinarith
  have hE2 : exp 1 ^ 2 < 74 / 10 := by nlinarith
  have hpos : 0 < exp 1 ^ 2 - 1 := by linarith
  constructor
  · have : (31 / 100 : ℝ) < 2 / (exp 1 ^ 2 - 1) := by
      rw [lt_div_iff₀ hpos]; linarith
    linarith
  · have : 2 / (exp 1 ^ 2 - 1) < (32 / 100 : ℝ) := by
      rw [div_lt_iff₀ hpos]; linarith
    linarith

/-- At \(GM/r^2=a_0\), i.e. \(x=1\), the enhancement is \(\coth 1\in(1.31,1.32)\). -/
theorem dualEnhancement_one_bounds :
    (131 / 100 : ℝ) < dualEnhancement 1 ∧ dualEnhancement 1 < 132 / 100 := by
  have h : dualEnhancement 1 = cosh 1 / sinh 1 := by unfold dualEnhancement; ring
  rw [h]
  exact coth_one_bounds

/-- At \(g_N=a_0\) the relation gives \(g=a_0\coth 1\). -/
theorem dualRAR_self {a0 : ℝ} (ha0 : 0 < a0) : dualRAR a0 a0 = a0 * (cosh 1 / sinh 1) := by
  unfold dualRAR
  rw [div_self ha0.ne', sqrt_one, ← sq, sqrt_sq ha0.le]

theorem coth_three_lt : cosh 3 / sinh 3 < 1 + 1 / 200 := by
  rw [coth_eq_one_add (by norm_num : (3 : ℝ) ≠ 0)]
  have h6 : exp (2 * 3) = (exp 1 ^ 2) ^ 3 := by
    rw [← pow_mul, ← exp_nat_mul]; norm_num
  rw [h6]
  have he1 := exp_one_gt_d9
  have hE1 : (7389 / 1000 : ℝ) < exp 1 ^ 2 := by nlinarith
  have hE3 : (7389 / 1000 : ℝ) ^ 3 < (exp 1 ^ 2) ^ 3 :=
    pow_lt_pow_left₀ hE1 (by norm_num) (by norm_num)
  have h401 : (401 : ℝ) < (exp 1 ^ 2) ^ 3 := lt_trans (by norm_num) hE3
  have hpos : 0 < (exp 1 ^ 2) ^ 3 - 1 := by linarith
  have : 2 / ((exp 1 ^ 2) ^ 3 - 1) < 1 / 200 := by
    rw [div_lt_iff₀ hpos]; linarith
  linarith

/-- Outside the mass, past three compactification radii, \(v^2<(1+1/200)\,GM/R\). -/
theorem dualCircularSpeedSq_near_flat {G R M0 r : ℝ} {M : ℝ → ℝ}
    (hGM : 0 < G * M0) (hR : 0 < R) (hr : 3 * R ≤ r) (hM : M r = M0) :
    dualCircularSpeedSq G R M r < (1 + 1 / 200) * (G * M0 / R) := by
  unfold dualCircularSpeedSq
  rw [hM]
  have hx : 3 ≤ r / R := (le_div_iff₀ hR).mpr (by linarith)
  have hc : cosh (r / R) / sinh (r / R) ≤ cosh 3 / sinh 3 := by
    rcases eq_or_lt_of_le hx with h | h
    · rw [← h]
    · exact (strictAntiOn_coth (mem_Ioi.mpr (by norm_num)) (mem_Ioi.mpr (by linarith)) h).le
  have hpos : 0 < G * M0 / R := div_pos hGM hR
  calc G * M0 / R * (cosh (r / R) / sinh (r / R))
      ≤ G * M0 / R * (cosh 3 / sinh 3) := mul_le_mul_of_nonneg_left hc hpos.le
    _ < G * M0 / R * (1 + 1 / 200) := mul_lt_mul_of_pos_left coth_three_lt hpos
    _ = (1 + 1 / 200) * (G * M0 / R) := by ring

/-- The \(S^3\) shape has no finite value at the antipode. -/
theorem tendsto_rotationShape_pi : Tendsto rotationShape (𝓝[<] π) atTop := by
  have hsin : Tendsto (fun x => sin x ^ 2) (𝓝[<] π) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x => sin x ^ 2) (𝓝 π) (𝓝 (sin π ^ 2)) :=
        (continuous_sin.pow 2).tendsto π
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT pi_pos] with x hx
      exact pow_pos (sin_pos_of_mem_Ioo hx) 2
  have hinv := tendsto_inv_nhdsGT_zero.comp hsin
  have hid : Tendsto (fun x : ℝ => x) (𝓝[<] π) (𝓝 π) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := hid.pos_mul_atTop pi_pos hinv
  refine h.congr' ?_
  filter_upwards with x
  simp [rotationShape, div_eq_mul_inv]

theorem milkyWayAntipode_bounds :
    (25 : ℝ) < π * milkyWayROverKpc ∧ π * milkyWayROverKpc < 29 := by
  have ⟨hlo, hhi⟩ := milkyWayROverKpc_bounds
  have hp1 := pi_gt_d2
  have hp2 := pi_lt_d2
  constructor <;> nlinarith

/-- \(GMa_0\) on the Milky-Way stand-ins, in m⁴/s⁴. -/
def milkyWayFlatSpeedFourth : ℚ :=
  GApprox * milkyWayMassApprox * mondAccelApprox

theorem milkyWayFlatSpeedFourth_bounds :
    ((175 * 10 ^ 3 : ℚ)) ^ 4 < milkyWayFlatSpeedFourth ∧
      milkyWayFlatSpeedFourth < ((176 * 10 ^ 3 : ℚ)) ^ 4 := by
  unfold milkyWayFlatSpeedFourth GApprox milkyWayMassApprox mondAccelApprox solarMassApprox
    milkyWayMassCoeff GMantissa GScale solarMassMantissa solarMassScale mondAccelMantissa
    mondAccelScale
  norm_num

end Gravity

end DstDiophantine
