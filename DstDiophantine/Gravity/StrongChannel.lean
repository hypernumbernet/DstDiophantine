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

## Charged entrance (do **not** claim)

The host that holds a rapidity down, a fusion rate, and the value of the
Coulomb-to-nuclear ratio are **not** derived. What is proved is the sign
comparison. Above the threshold the nuclear term adds to a positive Coulomb
term. Below it, every finite positive ratio is overcome on a nonempty
interval of rapidity abutting the threshold, and a higher sub-threshold
rapidity pulls harder. A smaller positive rapidity keeps that onset closer
to the node: the phase gap is strictly smaller than `φ/(4 cosh(x₁)²)`, and
the fractional widening of the radius is strictly smaller than `φ/π`. If
`0 < T/mc² ≤ 10⁻¹⁰`, that widening is strictly less than `5 × 10⁻⁶`.
Outside phase `π/4`, a sufficiently large rapidity leaves a net repulsion.
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

/-! ### Charged entrance: the slow side of the pole -/

noncomputable def chargedShift (γ ρ γE : ℝ) : ℝ :=
  -1 / γ + ρ / γE

theorem gammaRapidity_zero (x : ℝ) : gammaRapidity x 0 = gammaSEqual x := by
  simp [gammaRapidity, sinh_zero, cosh_zero]

theorem cosh_sub_one_local (φ : ℝ) :
    cosh φ - 1 = 2 * sinh (φ / 2) ^ 2 := by
  have h := cosh_two_mul (φ / 2)
  rw [show 2 * (φ / 2) = φ by ring] at h
  have hsq := cosh_sq_sub_sinh_sq (φ / 2)
  linarith

/-- Above the threshold the nuclear term is outward, so the net coefficient
strictly exceeds the Coulomb piece. -/
theorem chargedShift_gt_coulomb_of_neg {γ ρ γE : ℝ}
    (hγ : γ < 0) (_hρ : 0 < ρ) (_hγE : 0 < γE) :
    ρ / γE < chargedShift γ ρ γE := by
  unfold chargedShift
  have hpos : 0 < -1 / γ := by
    refine div_pos_of_neg_of_neg ?_ hγ
    norm_num
  linarith

theorem above_threshold_reinforces_coulomb {x δ ρ γE : ℝ}
    (hx : π / 4 < x) (hx2 : x < π / 2)
    (hδ : phiStar x / 2 < δ) (hρ : 0 < ρ) (hγE : 0 < γE) :
    ρ / γE < chargedShift (gammaRapidity x δ) ρ γE := by
  have hγ : gammaRapidity x δ < 0 := by
    have hnot : ¬ 0 < gammaRapidity x δ := by
      intro hpos
      have hlt := (gammaRapidity_pos_iff hx hx2).mp hpos
      linarith
    have hne : gammaRapidity x δ ≠ 0 := by
      intro hzero
      have := (gammaRapidity_eq_zero_iff hx hx2).mp hzero
      linarith
    exact lt_of_le_of_ne (le_of_not_gt hnot) hne
  exact chargedShift_gt_coulomb_of_neg hγ hρ hγE

noncomputable def gammaRapidityDeltaDeriv (x δ : ℝ) : ℝ :=
  (1 / 2) * exp (δ + x) * (cos x - sin x) -
    (1 / 2) * exp (-(δ + x)) * (cos x + sin x)

theorem hasDerivAt_gammaRapidity_delta (x δ : ℝ) :
    HasDerivAt (gammaRapidity x) (gammaRapidityDeltaDeriv x δ) δ := by
  have hclosed : gammaRapidity x = fun t =>
      (1 / 2) * exp (t + x) * (cos x - sin x) +
        (1 / 2) * exp (-(t + x)) * (cos x + sin x) := by
    funext t
    exact gammaRapidity_closed x t
  rw [hclosed]
  have h1 : HasDerivAt (fun t => exp (t + x)) (exp (δ + x)) δ := by
    simpa [id_eq, mul_one] using ((hasDerivAt_id δ).add_const x).exp
  have h2 : HasDerivAt (fun t => exp (-(t + x))) (-exp (-(δ + x))) δ := by
    have hsum : HasDerivAt (fun t => t + x) 1 δ := by
      simpa [id_eq, mul_one] using (hasDerivAt_id δ).add_const x
    simpa [mul_neg_one] using hsum.neg.exp
  have hmul1 := h1.const_mul ((1 / 2) * (cos x - sin x))
  have hmul2 := h2.const_mul ((1 / 2) * (cos x + sin x))
  have hsumd := hmul1.add hmul2
  have hfun :
      (fun y => (1 / 2) * (cos x - sin x) * exp (y + x)) +
        (fun y => (1 / 2) * (cos x + sin x) * exp (-(y + x))) =
      fun t =>
        (1 / 2) * exp (t + x) * (cos x - sin x) +
          (1 / 2) * exp (-(t + x)) * (cos x + sin x) := by
    funext t
    simp only [Pi.add_apply]
    ring_nf
  have hderiv :
      (1 / 2) * (cos x - sin x) * exp (δ + x) +
        (1 / 2) * (cos x + sin x) * -exp (-(δ + x)) =
      gammaRapidityDeltaDeriv x δ := by
    unfold gammaRapidityDeltaDeriv
    ring_nf
  rw [hfun, hderiv] at hsumd
  exact hsumd

theorem gammaRapidityDeltaDeriv_neg {x δ : ℝ}
    (hx : π / 4 < x) (hx2 : x < π / 2) :
    gammaRapidityDeltaDeriv x δ < 0 := by
  have hdiff : cos x - sin x < 0 := by linarith [sin_sub_cos_pos hx hx2]
  have hsum : 0 < cos x + sin x := by
    linarith [sin_add_cos_pos (by linarith [pi_pos]) hx2.le]
  have hA : (1 / 2) * exp (δ + x) * (cos x - sin x) < 0 := by
    have he : 0 < exp (δ + x) := exp_pos _
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) he) hdiff
  have hB : 0 < (1 / 2) * exp (-(δ + x)) * (cos x + sin x) := by
    have he : 0 < exp (-(δ + x)) := exp_pos _
    positivity
  unfold gammaRapidityDeltaDeriv
  linarith

/-- On the window the interference factor falls strictly as the rapidity rises. -/
theorem gammaRapidity_lt_of_lt_delta {x δ₁ δ₂ : ℝ}
    (hx : π / 4 < x) (hx2 : x < π / 2) (hδ : δ₁ < δ₂) :
    gammaRapidity x δ₂ < gammaRapidity x δ₁ := by
  have hcont : ContinuousOn (gammaRapidity x) (Icc δ₁ δ₂) :=
    fun t _ => (hasDerivAt_gammaRapidity_delta x t).continuousAt.continuousWithinAt
  have hder : ∀ t ∈ Ioo δ₁ δ₂,
      HasDerivAt (gammaRapidity x) (gammaRapidityDeltaDeriv x t) t :=
    fun t _ => hasDerivAt_gammaRapidity_delta x t
  obtain ⟨c, -, hslope⟩ := exists_hasDerivAt_eq_slope (gammaRapidity x)
    (gammaRapidityDeltaDeriv x) hδ hcont hder
  have hneg := gammaRapidityDeltaDeriv_neg (x := x) (δ := c) hx hx2
  have hden : 0 < δ₂ - δ₁ := by linarith
  have hquot : (gammaRapidity x δ₂ - gammaRapidity x δ₁) / (δ₂ - δ₁) < 0 := by
    rw [← hslope]
    exact hneg
  have hnum : gammaRapidity x δ₂ - gammaRapidity x δ₁ < 0 := by
    have hclear : gammaRapidity x δ₂ - gammaRapidity x δ₁ =
        ((gammaRapidity x δ₂ - gammaRapidity x δ₁) / (δ₂ - δ₁)) * (δ₂ - δ₁) := by
      field_simp
    rw [hclear]
    exact mul_neg_of_neg_of_pos hquot hden
  linarith

/-- `γ < γ_E/ρ` with all three positive is an inward net coefficient. -/
theorem chargedShift_neg_of_gamma_lt {γ ρ γE : ℝ}
    (hγ : 0 < γ) (hρ : 0 < ρ) (hγE : 0 < γE) (hlt : γ < γE / ρ) :
    chargedShift γ ρ γE < 0 := by
  unfold chargedShift
  have hstep : γ * ρ < γE := (lt_div_iff₀ hρ).mp hlt
  have hinv : ρ / γE < 1 / γ := by
    rw [div_lt_div_iff₀ hγE hγ]
    linarith
  have hrew : -1 / γ = -(1 / γ) := by ring
  rw [hrew]
  linarith

/-- A higher rapidity that is still below the threshold makes the net
coefficient more inward. -/
theorem higher_subthreshold_pulls_harder {x δ₁ δ₂ ρ γE : ℝ}
    (hx : π / 4 < x) (hx2 : x < π / 2)
    (hδ : δ₁ < δ₂) (h2 : δ₂ < phiStar x / 2) :
    chargedShift (gammaRapidity x δ₂) ρ γE < chargedShift (gammaRapidity x δ₁) ρ γE := by
  have hγ2 : 0 < gammaRapidity x δ₂ :=
    (gammaRapidity_pos_iff hx hx2).mpr h2
  have hlt := gammaRapidity_lt_of_lt_delta hx hx2 hδ
  unfold chargedShift
  have hinv : 1 / gammaRapidity x δ₁ < 1 / gammaRapidity x δ₂ :=
    one_div_lt_one_div_of_lt hγ2 hlt
  have hrew1 : -1 / gammaRapidity x δ₁ = -(1 / gammaRapidity x δ₁) := by ring
  have hrew2 : -1 / gammaRapidity x δ₂ = -(1 / gammaRapidity x δ₂) := by ring
  rw [hrew1, hrew2]
  linarith

theorem exists_subthreshold_net_inward {x ρ γE : ℝ}
    (hx : π / 4 < x) (hx1 : x < resonanceRoot1)
    (hρ : 0 < ρ) (hγE : 0 < γE) :
    ∃ δ, 0 ≤ δ ∧ δ < phiStar x / 2 ∧
      chargedShift (gammaRapidity x δ) ρ γE < 0 := by
  have hπ : resonanceRoot1 < π / 2 := by
    linarith [pi_gt_three, resonanceRoot1_sharp_bounds.2]
  set δs : ℝ := phiStar x / 2
  have hδs : 0 < δs := by
    have hφ := phiStar_pos hx hx1
    dsimp [δs]
    linarith
  have hzero : gammaRapidity x δs = 0 :=
    (gammaRapidity_eq_zero_iff hx (by linarith)).mpr rfl
  have hleft : 0 < gammaRapidity x 0 :=
    (gammaRapidity_pos_iff hx (by linarith)).mpr (by simpa [δs] using hδs)
  have hcont : ContinuousOn (gammaRapidity x) (Icc 0 δs) :=
    fun t _ => (hasDerivAt_gammaRapidity_delta x t).continuousAt.continuousWithinAt
  by_cases hsmall : gammaRapidity x 0 < γE / ρ
  · exact ⟨0, le_rfl, by simpa [δs] using hδs,
      chargedShift_neg_of_gamma_lt hleft hρ hγE hsmall⟩
  · have hge : γE / ρ ≤ gammaRapidity x 0 := le_of_not_gt hsmall
    set target : ℝ := γE / (2 * ρ)
    have htarget : 0 < target := by
      dsimp [target]
      positivity
    have htarget_lt : target < γE / ρ := by
      dsimp [target]
      have hρ2 : 0 < 2 * ρ := by positivity
      rw [div_lt_div_iff₀ hρ2 hρ]
      have : γE * ρ < γE * (2 * ρ) := by nlinarith [hγE, hρ]
      linarith
    have hmem : target ∈ Ioo (gammaRapidity x δs) (gammaRapidity x 0) := by
      rw [hzero]
      exact ⟨htarget, lt_of_lt_of_le htarget_lt hge⟩
    obtain ⟨δ, hδ, hγ⟩ := intermediate_value_Ioo' hδs.le hcont hmem
    have hpos : 0 < gammaRapidity x δ := by
      rw [hγ]
      exact htarget
    have hbelow : gammaRapidity x δ < γE / ρ := by
      rw [hγ]
      exact htarget_lt
    exact ⟨δ, hδ.1.le, by simpa [δs] using hδ.2,
      chargedShift_neg_of_gamma_lt hpos hρ hγE hbelow⟩

/-- At rest, every finite Coulomb ratio is overcome somewhere before the node. -/
theorem exists_rest_net_inward {ρ γE : ℝ} (hρ : 0 < ρ) (hγE : 0 < γE) :
    ∃ x, π / 4 < x ∧ x < resonanceRoot1 ∧
      chargedShift (gammaRapidity x 0) ρ γE < 0 := by
  set xL : ℝ := (π / 4 + resonanceRoot1) / 2
  have hx1 : π / 4 < resonanceRoot1 := resonanceRoot1_sharp_bounds.1
  have hxL₁ : π / 4 < xL := by dsimp [xL]; linarith
  have hxL₂ : xL < resonanceRoot1 := by dsimp [xL]; linarith
  have hγL : 0 < gammaSEqual xL :=
    gammaSEqual_pos_left_of_first_node ⟨by linarith [pi_pos], hxL₂⟩
  have hzero : gammaSEqual resonanceRoot1 = 0 := resonanceRoot1_gammaSEqual_zero
  have hcont : ContinuousOn gammaSEqual (Icc xL resonanceRoot1) :=
    continuous_gammaSEqual.continuousOn
  by_cases hsmall : gammaSEqual xL < γE / ρ
  · have hshift := chargedShift_neg_of_gamma_lt hγL hρ hγE hsmall
    rw [← gammaRapidity_zero] at hshift
    exact ⟨xL, hxL₁, hxL₂, hshift⟩
  · have hge : γE / ρ ≤ gammaSEqual xL := le_of_not_gt hsmall
    set target : ℝ := γE / (2 * ρ)
    have htarget : 0 < target := by
      dsimp [target]
      positivity
    have htarget_lt : target < γE / ρ := by
      dsimp [target]
      have hρ2 : 0 < 2 * ρ := by positivity
      rw [div_lt_div_iff₀ hρ2 hρ]
      nlinarith [hγE, hρ]
    have hmem : target ∈ Ioo (gammaSEqual resonanceRoot1) (gammaSEqual xL) := by
      rw [hzero]
      exact ⟨htarget, lt_of_lt_of_le htarget_lt hge⟩
    have hlt : xL < resonanceRoot1 := hxL₂
    obtain ⟨x, hx, hγ⟩ := intermediate_value_Ioo' hlt.le hcont hmem
    have hpos : 0 < gammaSEqual x := by rw [hγ]; exact htarget
    have hbelow : gammaSEqual x < γE / ρ := by rw [hγ]; exact htarget_lt
    have hshift := chargedShift_neg_of_gamma_lt hpos hρ hγE hbelow
    rw [← gammaRapidity_zero] at hshift
    exact ⟨x, lt_trans hxL₁ hx.1, hx.2, hshift⟩

/-! ### The pole moves inward as the rapidity falls -/

private noncomputable def phiStarSlope (x : ℝ) : ℝ :=
  2 * (1 - cos (2 * x)) / cos (2 * x)

private theorem phiStarSlope_lt_of_lt {c x : ℝ}
    (hc : π / 4 < c) (hlt : c < x) (hx : x < π / 2) :
    phiStarSlope c < phiStarSlope x := by
  have hcos : cos (2 * x) < cos (2 * c) :=
    cos_lt_cos_of_nonneg_of_le_pi (by linarith : (0 : ℝ) ≤ 2 * c)
      (by linarith [pi_pos] : 2 * x ≤ π) (by linarith : 2 * c < 2 * x)
  have hnegc : cos (2 * c) < 0 :=
    cos_neg_of_pi_div_two_lt_of_lt (by linarith : π / 2 < 2 * c)
      (by linarith [pi_pos] : 2 * c < π + π / 2)
  have hnegx : cos (2 * x) < 0 :=
    cos_neg_of_pi_div_two_lt_of_lt (by linarith : π / 2 < 2 * x)
      (by linarith [pi_pos] : 2 * x < π + π / 2)
  have hsec : 1 / cos (2 * c) < 1 / cos (2 * x) := by
    have hnum : cos (2 * x) - cos (2 * c) < 0 := by linarith
    have hden : 0 < cos (2 * c) * cos (2 * x) := by nlinarith
    have hdiff : 1 / cos (2 * c) - 1 / cos (2 * x) =
        (cos (2 * x) - cos (2 * c)) / (cos (2 * c) * cos (2 * x)) := by
      field_simp [hnegc.ne, hnegx.ne]
    have hquot : (cos (2 * x) - cos (2 * c)) / (cos (2 * c) * cos (2 * x)) < 0 :=
      div_neg_of_neg_of_pos hnum hden
    linarith
  have hrew (t : ℝ) (ht : cos (2 * t) ≠ 0) :
      phiStarSlope t = 2 * (1 / cos (2 * t) - 1) := by
    unfold phiStarSlope
    field_simp [ht]
  have hc' := hrew c hnegc.ne
  have hx' := hrew x hnegx.ne
  linarith

private theorem phiStarSlope_node :
    phiStarSlope resonanceRoot1 = -4 * cosh resonanceRoot1 ^ 2 := by
  have hx := resonanceRoot1_sharp_bounds
  have hπ : resonanceRoot1 < π / 2 := by linarith [pi_gt_three]
  have heq : phiStarSlope resonanceRoot1 = deriv phiStar resonanceRoot1 := by
    unfold phiStarSlope
    exact (hasDerivAt_phiStar hx.1 hπ).deriv.symm
  rw [heq, phiStar_deriv_node]

/-- Every positive rapidity meets the threshold at a phase strictly closer to
the node than the tangent estimate `φ/(4 cosh(x₁)²)`. -/
theorem phase_gap_lt_linear {φ x : ℝ}
    (hx : x ∈ Ioo (π / 4) resonanceRoot1) (hφx : phiStar x = φ) :
    resonanceRoot1 - x < φ / (4 * cosh resonanceRoot1 ^ 2) := by
  have hx1 : x < resonanceRoot1 := hx.2
  have hπ : resonanceRoot1 < π / 2 := by
    linarith [pi_gt_three, resonanceRoot1_sharp_bounds.2]
  have hcont : ContinuousOn phiStar (Icc x resonanceRoot1) :=
    continuousOn_phiStar.mono (by
      intro t ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hπ⟩)
  have hder : ∀ t ∈ Ioo x resonanceRoot1, HasDerivAt phiStar (phiStarSlope t) t := by
    intro t ht
    have ht1 : π / 4 < t := lt_trans hx.1 ht.1
    have ht2 : t < π / 2 := lt_trans ht.2 hπ
    simpa [phiStarSlope] using hasDerivAt_phiStar ht1 ht2
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope phiStar phiStarSlope hx1 hcont hder
  have hceq := hslope.symm
  rw [phiStar_node, hφx] at hceq
  have hden : 0 < resonanceRoot1 - x := by linarith
  have hlt_slope : phiStarSlope c < phiStarSlope resonanceRoot1 :=
    phiStarSlope_lt_of_lt (lt_trans hx.1 hc.1) hc.2 hπ
  rw [phiStarSlope_node] at hlt_slope
  have hrew : (0 - φ) / (resonanceRoot1 - x) = -(φ / (resonanceRoot1 - x)) := by ring
  rw [hrew] at hceq
  have hgt : 4 * cosh resonanceRoot1 ^ 2 < φ / (resonanceRoot1 - x) := by
    have hlt : -(φ / (resonanceRoot1 - x)) < -4 * cosh resonanceRoot1 ^ 2 := by
      rw [hceq]
      exact hlt_slope
    linarith
  have hcosh : 0 < 4 * cosh resonanceRoot1 ^ 2 := by
    have hcsh : 0 < cosh resonanceRoot1 := cosh_pos _
    positivity
  have hmul : (4 * cosh resonanceRoot1 ^ 2) * (resonanceRoot1 - x) < φ :=
    (lt_div_iff₀ hden).mp hgt
  rw [lt_div_iff₀ hcosh]
  linarith

/-- The fractional widening `(r_*-r₁)/r₁` is strictly smaller than `φ/π`. -/
theorem fractional_widening_lt_phi_div_pi {φ x : ℝ} (hφ : 0 < φ)
    (hx : x ∈ Ioo (π / 4) resonanceRoot1) (hφx : phiStar x = φ) :
    (resonanceRoot1 - x) / x < φ / π := by
  have hgap := phase_gap_lt_linear hx hφx
  have hcosh : 1 < cosh resonanceRoot1 := by
    have hpos : 0 < resonanceRoot1 :=
      lt_trans (lt_trans (by linarith [pi_pos] : (0 : ℝ) < π / 4) hx.1) hx.2
    have hsub := cosh_sub_one_local resonanceRoot1
    have hsinh : 0 < sinh (resonanceRoot1 / 2) := sinh_pos_iff.mpr (by linarith)
    have hpos' : 0 < cosh resonanceRoot1 - 1 := by
      rw [hsub]
      positivity
    linarith
  have hden : 0 < 4 * cosh resonanceRoot1 ^ 2 := by
    have hcsh : 0 < cosh resonanceRoot1 := cosh_pos _
    positivity
  have hquarter : φ / (4 * cosh resonanceRoot1 ^ 2) < φ / 4 := by
    refine div_lt_div_of_pos_left hφ (by norm_num) ?_
    have hcsh : 1 < cosh resonanceRoot1 := hcosh
    nlinarith
  have hphase : resonanceRoot1 - x < φ / 4 := lt_trans hgap hquarter
  have hxpos : 0 < x := by linarith [hx.1, pi_pos]
  have hfrac_phase : (resonanceRoot1 - x) / x < (φ / 4) / x :=
    div_lt_div_of_pos_right hphase hxpos
  have hxq : π / 4 < x := hx.1
  have hbound : (φ / 4) / x < (φ / 4) / (π / 4) :=
    div_lt_div_of_pos_left (by positivity) (by linarith [pi_pos] : (0 : ℝ) < π / 4) hxq
  have hpi : (φ / 4) / (π / 4) = φ / π := by
    field_simp
  exact lt_trans hfrac_phase (lt_of_lt_of_eq hbound hpi)

theorem exists_threshold_phase {φ : ℝ} (hφ : 0 < φ) :
    ∃ x, x ∈ Ioo (π / 4) resonanceRoot1 ∧ phiStar x = φ := by
  have hx1 : π / 4 < resonanceRoot1 := resonanceRoot1_sharp_bounds.1
  have hπ : resonanceRoot1 < π / 2 := by
    linarith [pi_gt_three, resonanceRoot1_sharp_bounds.2]
  have hlarge : ∀ᶠ t in nhdsWithin (π / 4) (Ioi (π / 4)), φ < phiStar t :=
    phiStar_tendsto_atTop.eventually (eventually_gt_atTop φ)
  have hnear : Ioo (π / 4) resonanceRoot1 ∈ nhdsWithin (π / 4) (Ioi (π / 4)) :=
    Ioo_mem_nhdsGT hx1
  have hmem : ∀ᶠ t in nhdsWithin (π / 4) (Ioi (π / 4)),
      t ∈ Ioo (π / 4) resonanceRoot1 :=
    eventually_of_mem hnear fun t ht => ht
  obtain ⟨x0, hx0φ, hx0mem⟩ := (hlarge.and hmem).exists
  have hcont : ContinuousOn phiStar (Icc x0 resonanceRoot1) :=
    continuousOn_phiStar.mono (by
      intro t ht
      exact ⟨lt_of_lt_of_le hx0mem.1 ht.1, lt_of_le_of_lt ht.2 hπ⟩)
  have hval : φ ∈ Ioo (phiStar resonanceRoot1) (phiStar x0) := by
    rw [phiStar_node]
    exact ⟨hφ, hx0φ⟩
  obtain ⟨x, hx, hxφ⟩ := intermediate_value_Ioo' hx0mem.2.le hcont hval
  exact ⟨x, ⟨lt_trans hx0mem.1 hx.1, hx.2⟩, hxφ⟩

/-- A smaller rapidity meets the threshold at a larger phase, hence at a
smaller radius. -/
theorem slower_threshold_deeper {φ₁ φ₂ x₁ x₂ : ℝ}
    (hφ : φ₁ < φ₂)
    (hx₁ : x₁ ∈ Ioo (π / 4) resonanceRoot1) (hx₂ : x₂ ∈ Ioo (π / 4) resonanceRoot1)
    (h₁ : phiStar x₁ = φ₁) (h₂ : phiStar x₂ = φ₂) :
    x₂ < x₁ := by
  by_contra hnot
  have hle : x₁ ≤ x₂ := le_of_not_gt hnot
  have hπ : resonanceRoot1 < π / 2 := by
    linarith [pi_gt_three, resonanceRoot1_sharp_bounds.2]
  have hanti := strictAntiOn_phiStar
  have hx₁' : x₁ ∈ Ioo (π / 4) (π / 2) := ⟨hx₁.1, lt_trans hx₁.2 hπ⟩
  have hx₂' : x₂ ∈ Ioo (π / 4) (π / 2) := ⟨hx₂.1, lt_trans hx₂.2 hπ⟩
  rcases eq_or_lt_of_le hle with rfl | hlt
  · linarith
  · have hφle : phiStar x₂ < phiStar x₁ := hanti hx₁' hx₂' hlt
    linarith

theorem slower_threshold_radius {ℓ φ₁ φ₂ x₁ x₂ : ℝ}
    (hℓ : 0 < ℓ) (hφ : φ₁ < φ₂)
    (hx₁ : x₁ ∈ Ioo (π / 4) resonanceRoot1) (hx₂ : x₂ ∈ Ioo (π / 4) resonanceRoot1)
    (h₁ : phiStar x₁ = φ₁) (h₂ : phiStar x₂ = φ₂) :
    layerRadius ℓ x₁ < layerRadius ℓ x₂ := by
  have hx := slower_threshold_deeper hφ hx₁ hx₂ h₁ h₂
  unfold layerRadius
  have hx1pos : 0 < x₁ := by linarith [hx₁.1, pi_pos]
  have hx2pos : 0 < x₂ := by linarith [hx₂.1, pi_pos]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### Thermal rapidity -/

theorem rapidity_lt_sqrt_two {φ y : ℝ} (hφ : 0 < φ) (hy : cosh φ = 1 + y) :
    φ < sqrt (2 * y) := by
  have hsub := cosh_sub_one_local φ
  have hy' : y = 2 * sinh (φ / 2) ^ 2 := by linarith
  have hhalf : 0 < φ / 2 := by linarith
  have hsinh : φ / 2 < sinh (φ / 2) := self_lt_sinh_iff.mpr hhalf
  have hsq : (φ / 2) ^ 2 < sinh (φ / 2) ^ 2 := by
    have habs : |φ / 2| < |sinh (φ / 2)| := by
      rw [abs_of_pos hhalf, abs_of_pos (sinh_pos_iff.mpr hhalf)]
      exact hsinh
    exact (sq_lt_sq).mpr habs
  have hφsq : φ ^ 2 < 2 * y := by
    have hleft : (φ / 2) ^ 2 < y / 2 := by
      have hs : sinh (φ / 2) ^ 2 = y / 2 := by
        rw [hy']
        field_simp
      linarith
    nlinarith
  have hy0 : 0 ≤ 2 * y := by
    have : 0 < sinh (φ / 2) ^ 2 := by positivity
    linarith
  rw [← sq_lt_sq₀ (le_of_lt hφ) (sqrt_nonneg _)]
  rw [sq_sqrt hy0]
  exact hφsq

theorem sqrt_two_tenth_lt :
    sqrt (2 / (10 : ℝ) ^ 10) < (3 : ℝ) / 2 / (10 : ℝ) ^ 5 := by
  have hL : 0 ≤ sqrt (2 / (10 : ℝ) ^ 10) := sqrt_nonneg _
  have hR : 0 ≤ (3 : ℝ) / 2 / (10 : ℝ) ^ 5 := by positivity
  rw [← sq_lt_sq₀ hL hR, sq_sqrt (by positivity)]
  have hsq : ((3 : ℝ) / 2 / (10 : ℝ) ^ 5) ^ 2 = (9 / 4) / (10 : ℝ) ^ 10 := by
    field_simp
    ring
  rw [hsq]
  have hden : (0 : ℝ) < (10 : ℝ) ^ 10 := by positivity
  rw [div_lt_div_iff₀ hden hden]
  norm_num

theorem fractional_widening_of_small_energy {φ y x : ℝ}
    (hφ : 0 < φ) (hy : cosh φ = 1 + y)
    (hyb : y ≤ 1 / (10 : ℝ) ^ 10)
    (hx : x ∈ Ioo (π / 4) resonanceRoot1) (hφx : phiStar x = φ) :
    (resonanceRoot1 - x) / x < 5 / (10 : ℝ) ^ 6 := by
  have hfrac := fractional_widening_lt_phi_div_pi hφ hx hφx
  have hφsqrt := rapidity_lt_sqrt_two hφ hy
  have hle : sqrt (2 * y) ≤ sqrt (2 / (10 : ℝ) ^ 10) := by
    refine sqrt_le_sqrt ?_
    have hyb' : 2 * y ≤ 2 / (10 : ℝ) ^ 10 := by
      have hden : (0 : ℝ) < (10 : ℝ) ^ 10 := by positivity
      have : y ≤ 1 / (10 : ℝ) ^ 10 := hyb
      nlinarith
    exact hyb'
  have hφnum : φ < (3 : ℝ) / 2 / (10 : ℝ) ^ 5 :=
    lt_trans hφsqrt (lt_of_le_of_lt hle sqrt_two_tenth_lt)
  have hπ : (3 : ℝ) < π := pi_gt_three
  have hφπ : φ / π < φ / 3 := div_lt_div_of_pos_left hφ (by norm_num) hπ
  have hφ3 : φ / 3 < ((3 : ℝ) / 2 / (10 : ℝ) ^ 5) / 3 :=
    div_lt_div_of_pos_right hφnum (by norm_num)
  have hend : ((3 : ℝ) / 2 / (10 : ℝ) ^ 5) / 3 = 5 / (10 : ℝ) ^ 6 := by
    field_simp
    ring
  have hchain : φ / π < 5 / (10 : ℝ) ^ 6 := by
    have hstep : φ / π < ((3 : ℝ) / 2 / (10 : ℝ) ^ 5) / 3 := lt_trans hφπ hφ3
    linarith
  linarith

/-! ### Outside the quarter-phase, a fast pair is left to Coulomb -/

private theorem cos_sub_sin_pos {x : ℝ} (hx0 : 0 ≤ x) (hx : x < π / 4) :
    0 < cos x - sin x := by
  have hcos : 0 < cos x :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · simp [sin_zero, cos_zero]
  · have hmem₁ : x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have hmem₂ : (π / 4) ∈ Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have htan : tan x < 1 := by
      have hstep := strictMonoOn_tan hmem₁ hmem₂ hx
      rwa [tan_pi_div_four] at hstep
    rw [tan_eq_sin_div_cos, div_lt_one hcos] at htan
    linarith

theorem gammaRapidity_tendsto_atTop_below_quarter {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x < π / 4) :
    Tendsto (gammaRapidity x) atTop atTop := by
  have hdiff : 0 < cos x - sin x := cos_sub_sin_pos hx0 hx
  set a : ℝ := (1 / 2) * (cos x - sin x) * exp x
  have ha : 0 < a := by
    dsimp [a]
    positivity
  set b : ℝ := (1 / 2) * (cos x + sin x)
  have hmain : Tendsto (fun δ => exp δ * a) atTop atTop :=
    tendsto_exp_atTop.atTop_mul_const ha
  have hbot : Tendsto (fun δ => -(δ + x)) atTop atBot := by
    have hsum : Tendsto (fun δ => δ + x) atTop atTop :=
      tendsto_id.atTop_add tendsto_const_nhds
    exact tendsto_neg_atTop_atBot.comp hsum
  have hexp : Tendsto (fun δ => exp (-(δ + x))) atTop (nhds 0) :=
    tendsto_exp_atBot.comp hbot
  have hrest : Tendsto (fun δ => exp (-(δ + x)) * b) atTop (nhds 0) := by
    simpa [mul_zero] using hexp.mul_const b
  refine (hrest.add_atTop hmain).congr fun δ => ?_
  rw [gammaRapidity_closed]
  have hexpadd : exp (δ + x) = exp δ * exp x := exp_add _ _
  rw [hexpadd]
  ring

theorem exists_fast_net_outward {x ρ γE : ℝ}
    (hx0 : 0 ≤ x) (hx : x < π / 4) (hρ : 0 < ρ) (hγE : 0 < γE) :
    ∃ Δ, ∀ δ, Δ ≤ δ → 0 < chargedShift (gammaRapidity x δ) ρ γE := by
  have hlim := gammaRapidity_tendsto_atTop_below_quarter hx0 hx
  have hev : ∀ᶠ δ in atTop, γE / ρ < gammaRapidity x δ :=
    hlim.eventually (eventually_gt_atTop (γE / ρ))
  rw [eventually_atTop] at hev
  obtain ⟨Δ, hΔ⟩ := hev
  refine ⟨Δ, ?_⟩
  intro δ hδ
  have hγ : γE / ρ < gammaRapidity x δ := hΔ δ hδ
  have hpos : 0 < gammaRapidity x δ := lt_trans (div_pos hγE hρ) hγ
  have hinv : 1 / gammaRapidity x δ < ρ / γE := by
    have hrew : 1 / (γE / ρ) = ρ / γE := by field_simp
    have hlt : 1 / gammaRapidity x δ < 1 / (γE / ρ) :=
      one_div_lt_one_div_of_lt (div_pos hγE hρ) hγ
    rw [hrew] at hlt
    exact hlt
  exact by
    unfold chargedShift
    have hrew : -1 / gammaRapidity x δ = -(1 / gammaRapidity x δ) := by ring
    rw [hrew]
    linarith

end Gravity

end DstDiophantine
