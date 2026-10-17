import DstDiophantine.Gravity.ElectronOrbit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue

/-!
# Strong channel: rapidity threshold and dual excitation

## Paper boundary (do **not** claim)

The nuclear prefactor `κ`, the length `ℓ`, the disposal of rapidity inside a
compound nucleus, and the laboratory `1/v` law are **not** derived. Neither
is a capture cross section. QCD and `A_max` stay outside this module.

## What is proved

On the window `(π/4, π/2)` the rapidity threshold
`φ_*(x) = log(sin x + cos x) - log(sin x - cos x) - 2x`
is strictly decreasing, vanishes at the first equal-scale node, and has
derivative `-4 cosh(x₁)²` there. No finite rapidity makes the interference
factor negative at phase `x ≤ π/4`. Below the threshold the factor is
positive. A nonnegative rapidity that increases from a value below `φ_*`
meets `φ_*` at one phase strictly before `x₁`.

A dual excitation `ψ_*(x) = 2 arctan(γ_s(x)/τ(x))` is strictly decreasing on
the outer well, vanishes at the first node, and tends to `π` at large
separation.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Filter

/-! ### Auxiliary combinations -/

noncomputable def sigmaEqual (x : ℝ) : ℝ :=
  cosh x * sin x - sinh x * cos x

noncomputable def tauEqual (x : ℝ) : ℝ :=
  cosh x * sin x + sinh x * cos x

theorem sigmaEqual_add_gammaSEqual (x : ℝ) :
    sigmaEqual x + gammaSEqual x = exp (-x) * (sin x + cos x) := by
  unfold sigmaEqual gammaSEqual
  rw [cosh_eq, sinh_eq]
  field_simp
  ring

theorem sigmaEqual_sub_gammaSEqual (x : ℝ) :
    sigmaEqual x - gammaSEqual x = exp x * (sin x - cos x) := by
  unfold sigmaEqual gammaSEqual
  rw [cosh_eq, sinh_eq]
  field_simp
  ring

theorem continuous_tauEqual : Continuous tauEqual := by
  unfold tauEqual
  exact (continuous_cosh.mul continuous_sin).add (continuous_sinh.mul continuous_cos)

theorem tauEqual_zero : tauEqual 0 = 0 := by
  simp [tauEqual]

theorem hasDerivAt_tauEqual (x : ℝ) :
    HasDerivAt tauEqual (2 * cosh x * cos x) x := by
  have h1 : HasDerivAt (fun y => cosh y * sin y) (sinh x * sin x + cosh x * cos x) x :=
    (hasDerivAt_cosh x).mul (hasDerivAt_sin x)
  have h2 : HasDerivAt (fun y => sinh y * cos y) (cosh x * cos x + sinh x * -sin x) x :=
    (hasDerivAt_sinh x).mul (hasDerivAt_cos x)
  have hsum := h1.add h2
  have heq : (sinh x * sin x + cosh x * cos x) + (cosh x * cos x + sinh x * -sin x) =
      2 * cosh x * cos x := by ring
  unfold tauEqual
  rw [heq] at hsum
  exact hsum

theorem tauEqual_pos {x : ℝ} (hx : 0 < x) (hx2 : x < π / 2) : 0 < tauEqual x := by
  have hmono : StrictMonoOn tauEqual (Icc 0 (π / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_tauEqual.continuousOn ?_
    intro y hy
    rw [interior_Icc] at hy
    rw [(hasDerivAt_tauEqual y).deriv]
    have hcos : 0 < cos y :=
      cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hy.1], hy.2⟩
    positivity
  have hlt := hmono ⟨le_rfl, by linarith [pi_pos]⟩ ⟨hx.le, hx2.le⟩ hx
  simpa [tauEqual_zero] using hlt

theorem gammaSEqual_sq_add_tauEqual_sq (x : ℝ) :
    gammaSEqual x ^ 2 + tauEqual x ^ 2 = cosh (2 * x) := by
  unfold gammaSEqual tauEqual
  have h := sin_sq_add_cos_sq x
  have hcs : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, h]
  calc
    (cosh x * cos x - sinh x * sin x) ^ 2 + (cosh x * sin x + sinh x * cos x) ^ 2
      = cosh x ^ 2 * (cos x ^ 2 + sin x ^ 2) + sinh x ^ 2 * (sin x ^ 2 + cos x ^ 2) := by ring
    _ = cosh x ^ 2 + sinh x ^ 2 := by rw [hcs, h, mul_one, mul_one]
    _ = cosh (2 * x) := by rw [cosh_two_mul]

/-! ### Relative rapidity -/

noncomputable def gammaRapidity (x δ : ℝ) : ℝ :=
  cosh δ * gammaSEqual x - sinh δ * sigmaEqual x

theorem gammaRapidity_closed (x δ : ℝ) :
    gammaRapidity x δ =
      (1 / 2) * exp (δ + x) * (cos x - sin x) +
        (1 / 2) * exp (-(δ + x)) * (cos x + sin x) := by
  unfold gammaRapidity sigmaEqual gammaSEqual
  simp only [cosh_eq, sinh_eq]
  field_simp
  rw [exp_add δ x]
  have hneg : -(δ + x) = -δ + -x := by ring
  rw [hneg, exp_add (-δ) (-x)]
  ring

private theorem sin_sub_cos_pos {x : ℝ} (hx : π / 4 < x) (hx2 : x < π / 2) :
    0 < sin x - cos x := by
  have hcos : 0 < cos x :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hx2⟩
  have hmem₁ : (π / 4) ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hmem₂ : x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], hx2⟩
  have htan : 1 < tan x := by
    have hstep := strictMonoOn_tan hmem₁ hmem₂ hx
    rwa [tan_pi_div_four] at hstep
  rw [tan_eq_sin_div_cos, lt_div_iff₀ hcos] at htan
  linarith

private theorem sin_add_cos_pos {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ π / 2) :
    0 < sin x + cos x := by
  have hcos : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hx2⟩
  have hsin : 0 ≤ sin x := sin_nonneg_of_mem_Icc ⟨hx0, by linarith [pi_pos]⟩
  rcases eq_or_lt_of_le hx0 with rfl | hx
  · simp [sin_zero, cos_zero]
  · have hsin' : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by linarith [pi_pos])
    positivity

private theorem cos_sub_sin_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ π / 4) :
    0 ≤ cos x - sin x := by
  have hcos : 0 < cos x :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · simp [sin_zero, cos_zero]
  · rcases eq_or_lt_of_le hx with rfl | hlt
    · simp [sin_pi_div_four, cos_pi_div_four]
    · have hmem₁ : x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
      have hmem₂ : (π / 4) ∈ Ioo (-(π / 2)) (π / 2) :=
        ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
      have htan : tan x < 1 := by
        have hstep := strictMonoOn_tan hmem₁ hmem₂ hlt
        rwa [tan_pi_div_four] at hstep
      rw [tan_eq_sin_div_cos, div_lt_one hcos] at htan
      linarith

/-- No finite rapidity inverts the channel at phase `x ≤ π/4`. -/
theorem gammaRapidity_pos_of_le_quarter {x δ : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ π / 4) :
    0 < gammaRapidity x δ := by
  rw [gammaRapidity_closed]
  have hdiff : 0 ≤ cos x - sin x := cos_sub_sin_nonneg hx0 hx
  have hsum : 0 < sin x + cos x := sin_add_cos_pos hx0 (by linarith [pi_pos])
  have hA : 0 ≤ (1 / 2) * exp (δ + x) * (cos x - sin x) := by
    have he : 0 < exp (δ + x) := exp_pos _
    positivity
  have hB : 0 < (1 / 2) * exp (-(δ + x)) * (sin x + cos x) := by
    have he : 0 < exp (-(δ + x)) := exp_pos _
    positivity
  have hcomm : cos x + sin x = sin x + cos x := by ring
  rw [hcomm]
  linarith

noncomputable def phiStar (x : ℝ) : ℝ :=
  log (sin x + cos x) - log (sin x - cos x) - 2 * x

theorem phiStar_eq_log_div {x : ℝ} (hnum : 0 < sin x + cos x) (hden : 0 < sin x - cos x) :
    phiStar x = log ((sin x + cos x) / (sin x - cos x)) - 2 * x := by
  unfold phiStar
  rw [log_div hnum.ne' hden.ne']

theorem phiStar_node : phiStar resonanceRoot1 = 0 := by
  have hx := resonanceRoot1_sharp_bounds
  have hπ : resonanceRoot1 < π / 2 := by linarith [pi_gt_three]
  have htan := tan_eq_of_gammaSEqual_eq_zero (by linarith) resonanceRoot1_gammaSEqual_zero
  have hs : 0 < sinh resonanceRoot1 := sinh_pos_iff.mpr (by linarith)
  have hcos : 0 < cos resonanceRoot1 :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hπ⟩
  have hden : 0 < sin resonanceRoot1 - cos resonanceRoot1 := sin_sub_cos_pos hx.1 hπ
  have hnum : 0 < sin resonanceRoot1 + cos resonanceRoot1 :=
    sin_add_cos_pos (by linarith) hπ.le
  have hratio : (sin resonanceRoot1 + cos resonanceRoot1) /
      (sin resonanceRoot1 - cos resonanceRoot1) = exp (2 * resonanceRoot1) := by
    have hrewrite : (sin resonanceRoot1 + cos resonanceRoot1) /
        (sin resonanceRoot1 - cos resonanceRoot1) =
        (tan resonanceRoot1 + 1) / (tan resonanceRoot1 - 1) := by
      rw [tan_eq_sin_div_cos]
      field_simp
    rw [hrewrite, htan]
    field_simp
    rw [cosh_add_sinh, cosh_sub_sinh, ← exp_add]
    ring_nf
  rw [phiStar_eq_log_div hnum hden, hratio, log_exp]
  ring

private theorem phiStar_hasDeriv_raw {x : ℝ}
    (hnum : sin x + cos x ≠ 0) (hden : sin x - cos x ≠ 0) :
    HasDerivAt phiStar
      ((cos x + -sin x) / (sin x + cos x) -
        (cos x + sin x) / (sin x - cos x) - 2) x := by
  have hN := ((hasDerivAt_sin x).add (hasDerivAt_cos x)).log hnum
  have hD := ((hasDerivAt_sin x).sub (hasDerivAt_cos x)).log hden
  have h2 := (hasDerivAt_id x).const_mul 2
  have h := (hN.sub hD).sub h2
  have hfun : phiStar =
      ((fun y => log (sin y + cos y)) - (fun y => log (sin y - cos y))) - (fun y => 2 * y) := by
    funext y
    unfold phiStar
    simp [Pi.sub_apply]
  simpa [hfun, Pi.sub_apply] using h

private theorem phiStar_deriv_simplified {x : ℝ} (hx : π / 4 < x) (hx2 : x < π / 2) :
    (cos x - sin x) / (sin x + cos x) - (cos x + sin x) / (sin x - cos x) - 2 =
      2 * (1 - cos (2 * x)) / cos (2 * x) := by
  have hden : 0 < sin x - cos x := sin_sub_cos_pos hx hx2
  have hnum : 0 < sin x + cos x := sin_add_cos_pos (by linarith) hx2.le
  have hB : cos x - sin x = -(sin x - cos x) := by ring
  have hA : cos x + sin x = sin x + cos x := by ring
  have hprod : (sin x - cos x) * (sin x + cos x) = -cos (2 * x) := by
    have : (sin x - cos x) * (sin x + cos x) = sin x ^ 2 - cos x ^ 2 := by ring
    rw [this, cos_two_mul']
    ring
  have hsumsq : (sin x - cos x) ^ 2 + (sin x + cos x) ^ 2 = 2 := by
    have : (sin x - cos x) ^ 2 + (sin x + cos x) ^ 2 = 2 * (sin x ^ 2 + cos x ^ 2) := by ring
    rw [this, sin_sq_add_cos_sq]
    ring
  rw [hB, hA]
  have hcomb : -(sin x - cos x) / (sin x + cos x) - (sin x + cos x) / (sin x - cos x) =
      -((sin x - cos x) ^ 2 + (sin x + cos x) ^ 2) /
        ((sin x + cos x) * (sin x - cos x)) := by
    field_simp
    ring
  have hdenprod : (sin x + cos x) * (sin x - cos x) = -cos (2 * x) := by
    rw [mul_comm, hprod]
  rw [hcomb, hsumsq, hdenprod]
  have hcos2 : cos (2 * x) ≠ 0 :=
    (cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [pi_pos])).ne
  field_simp [hcos2]

theorem hasDerivAt_phiStar {x : ℝ} (hx : π / 4 < x) (hx2 : x < π / 2) :
    HasDerivAt phiStar (2 * (1 - cos (2 * x)) / cos (2 * x)) x := by
  have hden : sin x - cos x ≠ 0 := (sin_sub_cos_pos hx hx2).ne'
  have hnum : sin x + cos x ≠ 0 := (sin_add_cos_pos (by linarith) hx2.le).ne'
  have hraw := phiStar_hasDeriv_raw hnum hden
  have hugly : (cos x + -sin x) / (sin x + cos x) -
      (cos x + sin x) / (sin x - cos x) - 2 =
      (cos x - sin x) / (sin x + cos x) - (cos x + sin x) / (sin x - cos x) - 2 := by
    ring
  rw [hugly, phiStar_deriv_simplified hx hx2] at hraw
  exact hraw

theorem continuousOn_phiStar : ContinuousOn phiStar (Ioo (π / 4) (π / 2)) :=
  fun _ hx => (hasDerivAt_phiStar hx.1 hx.2).continuousAt.continuousWithinAt

theorem strictAntiOn_phiStar : StrictAntiOn phiStar (Ioo (π / 4) (π / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) continuousOn_phiStar ?_
  intro x hx
  rw [interior_Ioo] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [(hasDerivAt_phiStar hx1 hx2).deriv]
  have hcos2 : cos (2 * x) < 0 :=
    cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [pi_pos])
  have hnum : 0 < 1 - cos (2 * x) := by linarith
  exact div_neg_of_pos_of_neg (by positivity) hcos2

theorem phiStar_pos {x : ℝ} (hx : π / 4 < x) (hx1 : x < resonanceRoot1) :
    0 < phiStar x := by
  have hπ : resonanceRoot1 < π / 2 := by linarith [pi_gt_three, resonanceRoot1_sharp_bounds.2]
  have hlt := strictAntiOn_phiStar ⟨hx, by linarith⟩ ⟨resonanceRoot1_sharp_bounds.1, hπ⟩ hx1
  rw [phiStar_node] at hlt
  exact hlt

theorem phiStar_deriv_node :
    deriv phiStar resonanceRoot1 = -4 * cosh resonanceRoot1 ^ 2 := by
  have hx := resonanceRoot1_sharp_bounds
  have hπ : resonanceRoot1 < π / 2 := by linarith [pi_gt_three]
  set x : ℝ := resonanceRoot1
  rw [(hasDerivAt_phiStar hx.1 hπ).deriv]
  have htan := tan_eq_of_gammaSEqual_eq_zero (by linarith) resonanceRoot1_gammaSEqual_zero
  have hs : 0 < sinh x := sinh_pos_iff.mpr (by linarith)
  have hfrac : cos (2 * x) = (1 - tan x ^ 2) / (1 + tan x ^ 2) := by
    rw [cos_two_mul', tan_eq_sin_div_cos]
    have hcos : cos x ≠ 0 :=
      (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hπ⟩).ne'
    field_simp
    have hsc : sin x ^ 2 + cos x ^ 2 = 1 := sin_sq_add_cos_sq x
    have hcs : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, hsc]
    rw [hcs]
    ring
  have hcosh : cos (2 * x) = -1 / cosh (2 * x) := by
    rw [hfrac, htan]
    have hrewrite : (1 - (cosh x / sinh x) ^ 2) / (1 + (cosh x / sinh x) ^ 2) =
        (sinh x ^ 2 - cosh x ^ 2) / (sinh x ^ 2 + cosh x ^ 2) := by
      field_simp
    rw [hrewrite]
    have hnum : sinh x ^ 2 - cosh x ^ 2 = -1 := by
      have h := cosh_sq_sub_sinh_sq x
      linarith
    have hden : sinh x ^ 2 + cosh x ^ 2 = cosh (2 * x) := by
      rw [cosh_two_mul]
      ring
    rw [hnum, hden]
  have hplus : cosh (2 * x) + 1 = 2 * cosh x ^ 2 := by
    rw [cosh_two_mul, cosh_sq']
    ring
  have hcosh_pos : 0 < cosh (2 * x) := cosh_pos _
  rw [hcosh]
  field_simp
  nlinarith [hplus]

/-- Below the threshold the channel attracts; above it the channel repels. -/
theorem gammaRapidity_pos_iff {x δ : ℝ} (hx : π / 4 < x) (hx2 : x < π / 2) :
    0 < gammaRapidity x δ ↔ δ < phiStar x / 2 := by
  have hden : 0 < sin x - cos x := sin_sub_cos_pos hx hx2
  have hnum : 0 < sin x + cos x := sin_add_cos_pos (by linarith) hx2.le
  rw [gammaRapidity_closed]
  have hfac : 0 < (1 / 2) * exp (-(δ + x)) := by positivity
  have hinside : (1 / 2) * exp (δ + x) * (cos x - sin x) +
      (1 / 2) * exp (-(δ + x)) * (cos x + sin x) =
      ((1 / 2) * exp (-(δ + x))) *
        (exp (2 * (δ + x)) * (cos x - sin x) + (cos x + sin x)) := by
    have he : exp (δ + x) = exp (2 * (δ + x)) * exp (-(δ + x)) := by
      rw [← exp_add]
      ring_nf
    rw [he]
    ring
  rw [hinside]
  have hcomm : cos x + sin x = sin x + cos x := by ring
  rw [hcomm]
  constructor
  · intro hpos
    have hrest : 0 < exp (2 * (δ + x)) * (cos x - sin x) + (sin x + cos x) :=
      (mul_pos_iff_of_pos_left hfac).mp hpos
    have hdiff : cos x - sin x = -(sin x - cos x) := by ring
    rw [hdiff] at hrest
    have : exp (2 * (δ + x)) * (sin x - cos x) < sin x + cos x := by linarith
    have hexp : exp (2 * (δ + x)) < (sin x + cos x) / (sin x - cos x) := by
      rwa [lt_div_iff₀ hden]
    have hlog := (lt_log_iff_exp_lt (div_pos hnum hden)).mpr hexp
    rw [phiStar_eq_log_div hnum hden] at *
    linarith
  · intro hδ
    rw [phiStar_eq_log_div hnum hden] at hδ
    have hexp : exp (2 * (δ + x)) < (sin x + cos x) / (sin x - cos x) :=
      (lt_log_iff_exp_lt (div_pos hnum hden)).mp (by linarith)
    have : exp (2 * (δ + x)) * (sin x - cos x) < sin x + cos x := by
      rwa [lt_div_iff₀ hden] at hexp
    have hdiff : cos x - sin x = -(sin x - cos x) := by ring
    have hrest : 0 < exp (2 * (δ + x)) * (cos x - sin x) + (sin x + cos x) := by
      rw [hdiff]
      linarith
    exact mul_pos hfac hrest

theorem gammaRapidity_eq_zero_iff {x δ : ℝ} (hx : π / 4 < x) (hx2 : x < π / 2) :
    gammaRapidity x δ = 0 ↔ δ = phiStar x / 2 := by
  have hden : 0 < sin x - cos x := sin_sub_cos_pos hx hx2
  have hnum : 0 < sin x + cos x := sin_add_cos_pos (by linarith) hx2.le
  rw [gammaRapidity_closed]
  have hfac : (1 / 2) * exp (-(δ + x)) ≠ 0 := by positivity
  have hinside : (1 / 2) * exp (δ + x) * (cos x - sin x) +
      (1 / 2) * exp (-(δ + x)) * (cos x + sin x) =
      ((1 / 2) * exp (-(δ + x))) *
        (exp (2 * (δ + x)) * (cos x - sin x) + (cos x + sin x)) := by
    have he : exp (δ + x) = exp (2 * (δ + x)) * exp (-(δ + x)) := by
      rw [← exp_add]
      ring_nf
    rw [he]
    ring
  rw [hinside]
  have hcomm : cos x + sin x = sin x + cos x := by ring
  rw [hcomm]
  constructor
  · intro hzero
    have hrest : exp (2 * (δ + x)) * (cos x - sin x) + (sin x + cos x) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hfac
    have hdiff : cos x - sin x = -(sin x - cos x) := by ring
    rw [hdiff] at hrest
    have hexp : exp (2 * (δ + x)) = (sin x + cos x) / (sin x - cos x) := by
      rw [eq_div_iff hden.ne']
      linarith
    have hlog : 2 * (δ + x) = log ((sin x + cos x) / (sin x - cos x)) := by
      rw [← hexp, log_exp]
    rw [phiStar_eq_log_div hnum hden]
    linarith
  · intro hδ
    rw [phiStar_eq_log_div hnum hden] at hδ
    have hlog : 2 * (δ + x) = log ((sin x + cos x) / (sin x - cos x)) := by linarith
    have hexp : exp (2 * (δ + x)) = (sin x + cos x) / (sin x - cos x) := by
      rw [hlog, exp_log (div_pos hnum hden)]
    have hdiff : cos x - sin x = -(sin x - cos x) := by ring
    have hrest : exp (2 * (δ + x)) * (cos x - sin x) + (sin x + cos x) = 0 := by
      rw [hdiff, hexp]
      field_simp
      ring
    exact mul_eq_zero.mpr (Or.inr hrest)

/-- While the channel attracts, an inward rapidity increases. -/
theorem infall_phase_deriv_pos {φ γ K dφ : ℝ}
    (hφ : 0 < φ) (hγ : 0 < γ) (hK : 0 < K)
    (h : sinh φ * γ * dφ = K) : 0 < dφ := by
  have hs : 0 < sinh φ := sinh_pos_iff.mpr hφ
  have hprod : 0 < sinh φ * γ := mul_pos hs hγ
  have hmul : 0 < sinh φ * γ * dφ := by rw [h]; exact hK
  exact (mul_pos_iff_of_pos_left hprod).mp hmul

/-- A nonnegative increasing rapidity that starts below the threshold meets it
before the static node. -/
theorem inward_rapidity_meets_threshold {c : ℝ} {φ : ℝ → ℝ}
    (hc : π / 4 < c) (hc1 : c < resonanceRoot1)
    (h0 : 0 ≤ φ c) (hlt : φ c < phiStar c)
    (hcont : ContinuousOn φ (Icc c resonanceRoot1))
    (hmono : StrictMonoOn φ (Icc c resonanceRoot1)) :
    ∃ t, t ∈ Ioo c resonanceRoot1 ∧ φ t = phiStar t := by
  have hπ : resonanceRoot1 < π / 2 := by linarith [pi_gt_three, resonanceRoot1_sharp_bounds.2]
  have hsub : Icc c resonanceRoot1 ⊆ Ioo (π / 4) (π / 2) := by
    intro t ht
    refine ⟨lt_of_lt_of_le hc ht.1, ?_⟩
    exact lt_of_le_of_lt ht.2 hπ
  let g : ℝ → ℝ := fun t => phiStar t - φ t
  have hgcont : ContinuousOn g (Icc c resonanceRoot1) :=
    (continuousOn_phiStar.mono hsub).sub hcont
  have hφlt : φ c < φ resonanceRoot1 :=
    hmono ⟨le_rfl, hc1.le⟩ ⟨hc1.le, le_rfl⟩ hc1
  have hgleft : 0 < g c := by
    dsimp [g]
    linarith
  have hgright : g resonanceRoot1 < 0 := by
    dsimp [g]
    rw [phiStar_node]
    linarith
  have hmem : (0 : ℝ) ∈ Ioo (g resonanceRoot1) (g c) := ⟨hgright, hgleft⟩
  have himg := intermediate_value_Ioo' hc1.le hgcont
  obtain ⟨t, ht, ht0⟩ := himg hmem
  exact ⟨t, ht, by dsimp [g] at ht0; linarith⟩

theorem inward_rapidity_meets_threshold_of_deriv {c : ℝ} {φ : ℝ → ℝ}
    (hc : π / 4 < c) (hc1 : c < resonanceRoot1)
    (h0 : 0 ≤ φ c) (hlt : φ c < phiStar c)
    (hcont : ContinuousOn φ (Icc c resonanceRoot1))
    (hderiv : ∀ x ∈ Ioo c resonanceRoot1, 0 < deriv φ x) :
    ∃ t, t ∈ Ioo c resonanceRoot1 ∧ φ t = phiStar t := by
  have hmono : StrictMonoOn φ (Icc c resonanceRoot1) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont fun x hx => by
      rw [interior_Icc] at hx
      exact hderiv x hx
  exact inward_rapidity_meets_threshold hc hc1 h0 hlt hcont hmono

theorem meeting_radius_outside_node {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht0 : 0 < t)
    (ht : t < resonanceRoot1) :
    layerRadius ℓ resonanceRoot1 < layerRadius ℓ t := by
  unfold layerRadius
  have hx : 0 < resonanceRoot1 := by linarith [resonanceRoot1_sharp_bounds.1, pi_pos]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### Every finite rapidity sits once in the window -/

theorem phiStar_tendsto_atTop :
    Tendsto phiStar (nhdsWithin (π / 4) (Ioi (π / 4))) atTop := by
  have hden_to : Tendsto (fun x => sin x - cos x) (nhds (π / 4)) (nhds 0) := by
    simpa [sin_pi_div_four, cos_pi_div_four] using
      ((continuous_sin.tendsto (π / 4)).sub (continuous_cos.tendsto (π / 4)))
  have hden : Tendsto (fun x => sin x - cos x)
      (nhdsWithin (π / 4) (Ioi (π / 4))) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hden_to.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show π / 4 < π / 2 by linarith [pi_pos])] with x hx
    exact sin_sub_cos_pos hx.1 hx.2
  have hnum : Tendsto (fun x => sin x + cos x) (nhdsWithin (π / 4) (Ioi (π / 4)))
      (nhds (sin (π / 4) + cos (π / 4))) :=
    ((continuous_sin.tendsto _).add (continuous_cos.tendsto _)).mono_left nhdsWithin_le_nhds
  have hnumpos : 0 < sin (π / 4) + cos (π / 4) := by
    rw [sin_pi_div_four, cos_pi_div_four]
    positivity
  have hlogden : Tendsto (fun x => log (sin x - cos x)) (nhdsWithin (π / 4) (Ioi (π / 4))) atBot :=
    tendsto_log_nhdsGT_zero.comp hden
  have hlognum : Tendsto (fun x => log (sin x + cos x)) (nhdsWithin (π / 4) (Ioi (π / 4)))
      (nhds (log (sin (π / 4) + cos (π / 4)))) :=
    (continuousAt_log hnumpos.ne').tendsto.comp hnum
  have hlin : Tendsto (fun x => log (sin x + cos x) - 2 * x) (nhdsWithin (π / 4) (Ioi (π / 4)))
      (nhds (log (sin (π / 4) + cos (π / 4)) - 2 * (π / 4))) :=
    hlognum.sub <| ((continuous_id.tendsto (π / 4)).const_mul 2).mono_left nhdsWithin_le_nhds
  have hneg : Tendsto (fun x => -(log (sin x - cos x))) (nhdsWithin (π / 4) (Ioi (π / 4))) atTop :=
    tendsto_neg_atBot_atTop.comp hlogden
  have hadd := hneg.atTop_add hlin
  refine hadd.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show π / 4 < π / 2 by linarith [pi_pos])] with x hx
  unfold phiStar
  ring

/-! ### Dual excitation -/

noncomputable def psiStar (x : ℝ) : ℝ :=
  2 * arctan (gammaSEqual x / tauEqual x)

theorem psiStar_node : psiStar resonanceRoot1 = 0 := by
  have hπ : resonanceRoot1 < π / 2 := by linarith [pi_gt_three, resonanceRoot1_sharp_bounds.2]
  have hτ : 0 < tauEqual resonanceRoot1 :=
    tauEqual_pos (by linarith [resonanceRoot1_sharp_bounds.1, pi_pos]) hπ
  unfold psiStar
  rw [resonanceRoot1_gammaSEqual_zero, zero_div, arctan_zero, mul_zero]

private theorem tau_bracket (x : ℝ) :
    sin x * tauEqual x + gammaSEqual x * cos x = cosh x := by
  unfold tauEqual gammaSEqual
  have h := sin_sq_add_cos_sq x
  calc
    sin x * (cosh x * sin x + sinh x * cos x) +
        (cosh x * cos x - sinh x * sin x) * cos x
      = cosh x * (sin x ^ 2 + cos x ^ 2) := by ring
    _ = cosh x := by rw [h, mul_one]

theorem hasDerivAt_gamma_div_tau {x : ℝ} (hτ : tauEqual x ≠ 0) :
    HasDerivAt (fun t => gammaSEqual t / tauEqual t)
      (-2 * cosh x ^ 2 / tauEqual x ^ 2) x := by
  have hdiv := (hasDerivAt_gammaSEqual x).div (hasDerivAt_tauEqual x) hτ
  have hbr := tau_bracket x
  have heq : (-2 * cosh x * sin x) * tauEqual x -
      gammaSEqual x * (2 * cosh x * cos x) = -2 * cosh x ^ 2 := by
    calc
      (-2 * cosh x * sin x) * tauEqual x - gammaSEqual x * (2 * cosh x * cos x)
        = -2 * cosh x * (sin x * tauEqual x + gammaSEqual x * cos x) := by ring
      _ = -2 * cosh x * cosh x := by rw [hbr]
      _ = -2 * cosh x ^ 2 := by ring
  simp only [heq] at hdiv
  exact hdiv

theorem hasDerivAt_psiStar {x : ℝ} (hx : 0 < x) (hx2 : x < π / 2) :
    HasDerivAt psiStar
      (-4 * cosh x ^ 2 / (gammaSEqual x ^ 2 + tauEqual x ^ 2)) x := by
  have hτ : tauEqual x ≠ 0 := (tauEqual_pos hx hx2).ne'
  have hquot := (hasDerivAt_gamma_div_tau hτ).arctan
  have h := hquot.const_mul 2
  have hscalar : 2 * (1 / (1 + (gammaSEqual x / tauEqual x) ^ 2) *
      (-2 * cosh x ^ 2 / tauEqual x ^ 2)) =
      -4 * cosh x ^ 2 / (gammaSEqual x ^ 2 + tauEqual x ^ 2) := by
    have hden : gammaSEqual x ^ 2 + tauEqual x ^ 2 ≠ 0 := by
      rw [gammaSEqual_sq_add_tauEqual_sq]
      exact (cosh_pos _).ne'
    field_simp
    ring
  unfold psiStar
  rw [hscalar] at h
  exact h

theorem strictAntiOn_psiStar : StrictAntiOn psiStar (Ioo 0 (π / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) ?_ ?_
  · intro x hx
    exact (hasDerivAt_psiStar hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_psiStar hx.1 hx.2).deriv]
    have hden : 0 < gammaSEqual x ^ 2 + tauEqual x ^ 2 := by
      rw [gammaSEqual_sq_add_tauEqual_sq]
      exact cosh_pos _
    have hnum : -4 * cosh x ^ 2 < 0 := by
      have hc : 0 < cosh x := cosh_pos _
      nlinarith
    exact div_neg_of_neg_of_pos hnum hden

theorem psiStar_pos {x : ℝ} (hx : 0 < x) (hx1 : x < resonanceRoot1) : 0 < psiStar x := by
  have hπ : resonanceRoot1 < π / 2 := by linarith [pi_gt_three, resonanceRoot1_sharp_bounds.2]
  have hlt := strictAntiOn_psiStar ⟨hx, by linarith⟩
    ⟨by linarith [resonanceRoot1_sharp_bounds.1, pi_pos], hπ⟩ hx1
  rw [psiStar_node] at hlt
  exact hlt

theorem psiStar_tendsto_pi : Tendsto psiStar (nhdsWithin 0 (Ioi 0)) (nhds π) := by
  have hγ : Tendsto gammaSEqual (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa [gammaSEqual_zero] using
      (continuous_gammaSEqual.tendsto 0).mono_left nhdsWithin_le_nhds
  have hτ : Tendsto tauEqual (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa [tauEqual_zero] using
        (continuous_tauEqual.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by linarith [pi_pos])] with x hx
      exact tauEqual_pos hx.1 hx.2
  have hinv : Tendsto (fun x => (tauEqual x)⁻¹) (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hτ
  have hquot : Tendsto (fun x => gammaSEqual x / tauEqual x) (nhdsWithin 0 (Ioi 0)) atTop := by
    have hmul := hγ.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hinv
    refine hmul.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by linarith [pi_pos])] with x hx
    have hτne : tauEqual x ≠ 0 := (tauEqual_pos hx.1 hx.2).ne'
    field_simp
  have hatan : Tendsto (fun x => arctan (gammaSEqual x / tauEqual x))
      (nhdsWithin 0 (Ioi 0)) (nhds (π / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin (tendsto_arctan_atTop.comp hquot)
  have htwo := hatan.const_mul 2
  have hπ : 2 * (π / 2) = π := by field_simp
  rw [hπ] at htwo
  unfold psiStar
  exact htwo

end Gravity

end DstDiophantine
