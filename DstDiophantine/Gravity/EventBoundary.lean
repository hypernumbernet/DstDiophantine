import DstDiophantine.Gravity.Sandwich
import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.Amplification
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quasi-horizon cutoff from the admissible torsional ceiling

## Working hypothesis (not a derivation)

Identify the proved admissible ceiling `|J| ≤ 3π²/8` (equivalently
`|JNormalized| ≤ 1`) with the DST quasi-horizon / event-boundary shell.
On the radial pure-boost chart `J = ½ φ²`, this inverts to the finite cutoff

\[
\varphi_{\max} = \frac{\pi\sqrt{3}}{2},\qquad
A_{\min} = e^{-2\varphi_{\max}} = e^{-\pi\sqrt{3}}.
\]

Classical Schwarzschild has `φ → ∞` and `A → 0` as `r → rₛ⁺`. The cutoff
replaces that divergence by a finite redshift floor, matching the paper claim
that a true one-way horizon (`A = 0`) does not form.

## Not claimed

* Derivation of Newton `G` from `c` (see `NewtonFromLight`).
* Identification of dimensionless `J` with `c⁴/(G ℓ_P⁻²)`.
* That `pureBoost φ_max` lies in `IsAdmissibleContinuous` (single-axis
  admissibility requires `φ ≤ π/2 < φ_max`; the ceiling `JNormalized = 1`
  comes from the three-axis normalisation inverted on one boost axis).
* Rewriting the exterior Schwarzschild metric theorems.
-/

namespace DstDiophantine

namespace Gravity

open Admissible Amplification Invariant

/-! ### Source-of-truth constants

`phiMax` is primary; `AMin` and the redshift / stretch factors are derived from it.
-/

/-- Maximal radial rapidity at the quasi-horizon: `π √3 / 2`. -/
noncomputable def phiMax : ℝ :=
  Real.pi * Real.sqrt 3 / 2

/-- Raw torsional ceiling `|J| ≤ 3π²/8`. -/
noncomputable def JMax : ℝ :=
  3 * Real.pi ^ 2 / 8

/-- Minimal Schwarzschild factor `A_min = e^{-2 φ_max}`. -/
noncomputable def AMin : ℝ :=
  Real.exp (-(2 * phiMax))

/-- Redshift floor `e^{-φ_max} = √A_min`. -/
noncomputable def redshiftMin : ℝ :=
  Real.exp (-phiMax)

/-- Radial stretch ceiling `e^{φ_max}`. -/
noncomputable def stretchMax : ℝ :=
  Real.exp phiMax

/-- Ratio `r_★ / rₛ = 1 / (1 - A_min)`. -/
noncomputable def radiusRatio : ℝ :=
  (1 - AMin)⁻¹

/-- Quasi-horizon radius where classical `φ(r) = φ_max`. -/
noncomputable def eventBoundaryRadius (rs : ℝ) : ℝ :=
  rs * radiusRatio

/-- Finite rapidity at the event boundary. -/
noncomputable abbrev eventBoundaryRapidity : ℝ := phiMax

/-- Finite `A` at the event boundary. -/
noncomputable abbrev eventBoundaryA : ℝ := AMin

/-! ### Algebraic identities -/

theorem AMin_eq_exp_neg_pi_sqrt_three :
    AMin = Real.exp (-(Real.pi * Real.sqrt 3)) := by
  unfold AMin phiMax
  ring_nf

theorem redshiftMin_sq_eq_AMin : redshiftMin ^ 2 = AMin := by
  unfold redshiftMin AMin
  rw [sq, ← Real.exp_add]
  ring_nf

theorem stretchMax_mul_redshiftMin : stretchMax * redshiftMin = 1 := by
  unfold stretchMax redshiftMin
  simp [← Real.exp_add]

theorem J_pureBoost_phiMax : J (pureBoost phiMax) = JMax := by
  unfold phiMax JMax
  rw [J_pureBoost]
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem JNormalized_pureBoost_phiMax :
    JNormalized (pureBoost phiMax) = 1 := by
  unfold phiMax
  rw [JNormalized_pureBoost]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  field_simp [hπ.ne']
  ring

theorem AMin_pos : (0 : ℝ) < AMin :=
  Real.exp_pos _

theorem AMin_lt_one : AMin < 1 := by
  rw [← Real.exp_zero, AMin_eq_exp_neg_pi_sqrt_three]
  exact Real.exp_lt_exp.mpr
    (neg_neg_of_pos (mul_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num))))

theorem one_sub_AMin_pos : (0 : ℝ) < 1 - AMin :=
  sub_pos.mpr AMin_lt_one

theorem radiusRatio_pos : (0 : ℝ) < radiusRatio :=
  inv_pos.mpr one_sub_AMin_pos

theorem one_lt_radiusRatio : (1 : ℝ) < radiusRatio := by
  unfold radiusRatio
  rw [one_lt_inv_iff₀]
  exact ⟨one_sub_AMin_pos, sub_lt_self _ AMin_pos⟩

theorem eventBoundaryRadius_pos {rs : ℝ} (hrs : 0 < rs) :
    0 < eventBoundaryRadius rs :=
  mul_pos hrs radiusRatio_pos

theorem rs_lt_eventBoundaryRadius {rs : ℝ} (hrs : 0 < rs) :
    rs < eventBoundaryRadius rs := by
  unfold eventBoundaryRadius
  simpa using mul_lt_mul_of_pos_left one_lt_radiusRatio hrs

/-! ### Chart dictionary: classical `φ = φ_max` ↔ `r = r_★` -/

theorem schwarzschildRapidity_eq_phiMax_iff {rs r : ℝ}
    (hrs : 0 < rs) (hr : rs < r) :
    schwarzschildRapidity rs r = phiMax ↔ 1 - rs / r = AMin := by
  have hApos := A_pos_of_exterior hrs hr
  constructor
  · intro h
    have hlog : Real.log (1 - rs / r) = -(2 * phiMax) := by
      have := congrArg (fun x : ℝ => -2 * x) h
      simp only [schwarzschildRapidity] at this
      linarith
    have := congrArg Real.exp hlog
    rwa [Real.exp_log hApos] at this
  · intro h
    unfold schwarzschildRapidity
    rw [h, AMin, Real.log_exp]
    ring

theorem A_eq_AMin_iff_eq_eventBoundaryRadius {rs r : ℝ}
    (hrs : 0 < rs) (hr : 0 < r) :
    1 - rs / r = AMin ↔ r = eventBoundaryRadius rs := by
  have hden : 1 - AMin ≠ 0 := one_sub_AMin_pos.ne'
  constructor
  · intro h
    unfold eventBoundaryRadius radiusRatio
    have hquot : rs / r = 1 - AMin := by linarith
    -- `r = rs * (1-A)⁻¹` ↔ `r * (1-A) = rs`
    rw [← div_eq_mul_inv, eq_div_iff hden, mul_comm]
    exact (div_eq_iff hr.ne').mp hquot |>.symm
  · intro h
    rw [h]
    unfold eventBoundaryRadius radiusRatio
    field_simp [hrs.ne', hden]
    ring

theorem schwarzschildRapidity_eq_phiMax_iff_eventBoundaryRadius {rs r : ℝ}
    (hrs : 0 < rs) (hr : rs < r) :
    schwarzschildRapidity rs r = phiMax ↔ r = eventBoundaryRadius rs := by
  rw [schwarzschildRapidity_eq_phiMax_iff hrs hr,
    A_eq_AMin_iff_eq_eventBoundaryRadius hrs (hrs.trans hr)]

/-! ### Horizon boost is outside the admissible cone -/

theorem phiMax_gt_half_pi : Real.pi / 2 < phiMax := by
  unfold phiMax
  have hs : (1 : ℝ) < Real.sqrt 3 :=
    Real.lt_sqrt_of_sq_lt (by norm_num : (1 : ℝ) ^ 2 < 3)
  nlinarith [Real.pi_pos]

theorem not_admissible_pureBoost_phiMax :
    ¬ IsAdmissibleContinuous (pureBoost phiMax) := by
  intro h
  have hsum := (h 0).2.2
  simp only [pureBoost, add_zero] at hsum
  exact absurd hsum phiMax_gt_half_pi.not_ge

/-! ### Saturated chart (definition only; no metric re-proof) -/

/-- Freeze rapidity at `φ_max` for `r ≤ r_★`; classical exterior formula outside. -/
noncomputable def saturatedRapidity (rs r : ℝ) : ℝ :=
  if r ≤ eventBoundaryRadius rs then phiMax else schwarzschildRapidity rs r

/-- Freeze `A` at `A_min` for `r ≤ r_★`; classical `1 - rₛ/r` outside. -/
noncomputable def saturatedA (rs r : ℝ) : ℝ :=
  if r ≤ eventBoundaryRadius rs then AMin else 1 - rs / r

@[simp] theorem saturatedRapidity_of_le {rs r : ℝ}
    (h : r ≤ eventBoundaryRadius rs) :
    saturatedRapidity rs r = phiMax := by
  simp [saturatedRapidity, h]

@[simp] theorem saturatedRapidity_of_gt {rs r : ℝ}
    (h : eventBoundaryRadius rs < r) :
    saturatedRapidity rs r = schwarzschildRapidity rs r := by
  simp [saturatedRapidity, not_le_of_gt h]

@[simp] theorem saturatedA_of_le {rs r : ℝ}
    (h : r ≤ eventBoundaryRadius rs) :
    saturatedA rs r = AMin := by
  simp [saturatedA, h]

@[simp] theorem saturatedA_of_gt {rs r : ℝ}
    (h : eventBoundaryRadius rs < r) :
    saturatedA rs r = 1 - rs / r := by
  simp [saturatedA, not_le_of_gt h]

theorem saturatedA_pos {rs r : ℝ} (hrs : 0 < rs) :
    0 < saturatedA rs r := by
  by_cases h : r ≤ eventBoundaryRadius rs
  · simpa [h] using AMin_pos
  · have hr : eventBoundaryRadius rs < r := lt_of_not_ge h
    simpa [hr] using
      A_pos_of_exterior hrs ((rs_lt_eventBoundaryRadius hrs).trans hr)

/-! ### Rational envelopes (machine-checked numerics) -/

private theorem sqrt_three_gt_173_100 :
    (173 : ℝ) / 100 < Real.sqrt 3 :=
  Real.lt_sqrt_of_sq_lt (by norm_num : ((173 : ℝ) / 100) ^ 2 < 3)

private theorem pi_mul_sqrt_three_gt :
    (314 : ℝ) * 173 / 10000 < Real.pi * Real.sqrt 3 := by
  have hπ : (314 : ℝ) / 100 < Real.pi := by
    convert (Real.pi_gt_d2 : (3.14 : ℝ) < Real.pi) using 1
    norm_num
  have hs := sqrt_three_gt_173_100
  have hπpos : (0 : ℝ) < 314 / 100 := by norm_num
  calc (314 : ℝ) * 173 / 10000
      = (314 / 100) * (173 / 100) := by ring
    _ < Real.pi * Real.sqrt 3 :=
        mul_lt_mul hπ hs.le (by norm_num) (le_of_lt (hπpos.trans hπ))

/-- Shared bridge: `log n < π√3` ⇒ `A_min < 1/n`. -/
private theorem AMin_lt_inv_of {n : ℕ} (hn : 0 < n)
    (hlog : Real.log (n : ℝ) < Real.pi * Real.sqrt 3) :
    AMin < (1 : ℝ) / n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlt :
      Real.exp (-(Real.pi * Real.sqrt 3)) < Real.exp (-Real.log (n : ℝ)) :=
    Real.exp_lt_exp.mpr (neg_lt_neg hlog)
  calc AMin = Real.exp (-(Real.pi * Real.sqrt 3)) :=
      AMin_eq_exp_neg_pi_sqrt_three
    _ < Real.exp (-Real.log (n : ℝ)) := hlt
    _ = (Real.exp (Real.log (n : ℝ)))⁻¹ := by rw [Real.exp_neg]
    _ = (n : ℝ)⁻¹ := by rw [Real.exp_log hnR]
    _ = 1 / n := by rw [one_div]

private theorem log_100_lt_pi_sqrt_three :
    Real.log 100 < Real.pi * Real.sqrt 3 := by
  have h2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h5 : Real.log 5 < (1.6094379126 : ℝ) := Real.log_five_lt_d9
  have h100 : Real.log 100 = 2 * (Real.log 2 + Real.log 5) := by
    have h : (100 : ℝ) = (10 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h, Real.log_pow, Real.log_ten_eq]
    norm_cast
  have hlog : Real.log 100 < (314 : ℝ) * 173 / 10000 := by
    rw [h100]
    linarith
  exact hlog.trans pi_mul_sqrt_three_gt

/-- `0 < A_min < 10^{-2}`. -/
theorem AMin_bounds :
    (0 : ℝ) < AMin ∧ AMin < (1 : ℝ) / 100 :=
  ⟨AMin_pos, AMin_lt_inv_of (by norm_num) log_100_lt_pi_sqrt_three⟩

private theorem log_201_lt_pi_sqrt_three :
    Real.log 201 < Real.pi * Real.sqrt 3 := by
  have h2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h5 : Real.log 5 < (1.6094379126 : ℝ) := Real.log_five_lt_d9
  have h200 : Real.log 200 = Real.log 2 + 2 * (Real.log 2 + Real.log 5) := by
    have h : (200 : ℝ) = 2 * ((10 : ℝ) ^ (2 : ℕ)) := by norm_num
    rw [h, Real.log_mul (by norm_num) (pow_ne_zero _ (by norm_num)),
      Real.log_pow, Real.log_ten_eq]
    norm_cast
  have hfactor : (201 : ℝ) = 200 * (201 / 200) := by ring
  have h201 : Real.log 201 = Real.log 200 + Real.log (201 / 200) := by
    have hmul := Real.log_mul (by norm_num : (200 : ℝ) ≠ 0)
      (by positivity : (201 : ℝ) / 200 ≠ 0)
    rwa [← hfactor] at hmul
  have hlog1p : Real.log (201 / 200) < (1 : ℝ) / 200 := by
    have hx : (0 : ℝ) < 201 / 200 := by positivity
    have hne : (201 : ℝ) / 200 ≠ 1 := by norm_num
    convert (Real.log_lt_sub_one_of_pos hx hne) using 1
    norm_num
  have hlog200 : Real.log 200 < (314 : ℝ) * 173 / 10000 - 1 / 200 := by
    rw [h200]
    norm_num
    linarith
  have : Real.log 201 < (314 : ℝ) * 173 / 10000 := by
    rw [h201]
    linarith
  exact this.trans pi_mul_sqrt_three_gt

private theorem AMin_lt_inv_201 : AMin < (1 : ℝ) / 201 :=
  AMin_lt_inv_of (by norm_num) log_201_lt_pi_sqrt_three

/-- `1 < radiusRatio < 1005/1000`. -/
theorem radiusRatio_bounds :
    (1 : ℝ) < radiusRatio ∧ radiusRatio < (1005 : ℝ) / 1000 := by
  refine ⟨one_lt_radiusRatio, ?_⟩
  have hbound : (200 : ℝ) / 201 < 1 - AMin := by
    have : (1 : ℝ) - 1 / 201 = (200 : ℝ) / 201 := by norm_num
    linarith [AMin_lt_inv_201]
  have hinv :
      (1 - AMin)⁻¹ < ((200 : ℝ) / 201)⁻¹ :=
    (inv_lt_inv₀ one_sub_AMin_pos (by norm_num)).mpr hbound
  have hsimp : ((200 : ℝ) / 201)⁻¹ = (1005 : ℝ) / 1000 := by norm_num
  simpa [radiusRatio, hsimp] using hinv

end Gravity

end DstDiophantine
