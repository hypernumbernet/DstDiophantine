import DstDiophantine.Logic.Quantum.CarrierDeficit
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Quantum Fisher information of the relative phase

`PhaseInformation` names `I = 4p(1 − p)` and leaves the symmetric logarithmic derivative unbuilt.
On the orthonormal weight space the relative phase is unitary. Its generator is the projector onto
the second weight. The horizontal derivative `D` is orthogonal to the state, the pure-state
symmetric logarithmic derivative satisfies `Lψ = 2D`, and `⟨ψ, L²ψ⟩ = I`.

Two carriers are different. The curve `a + e^{iθ} b` changes length, so it is not that unitary
orbit. The numerator of its projective metric does not depend on `θ`:

`⟨∂ψ, ∂ψ⟩ ⟨ψ, ψ⟩ − |⟨ψ, ∂ψ⟩|² = ‖a‖² ‖b‖² − |⟨a, b⟩|²`.

The quantum Fisher information is four times that numerator over `‖ψ‖⁴`. It equals the carrier
deficit `Δ` exactly where the interference term vanishes. At a density peak or valley, and when
`0 < F < 1` with both weights nonzero, it is not `Δ`. The extreme chart ratio still squares to
shell information.

Mean rest, mass 3: quadrature `544/625`, peak `136/289`, valley `17/8`. Rest against `(5, 4, 0, 0)`:
the samples at time `0` and `-π/2` have Fisher `81/841` and `81/25`, and a quadrature time has
density `68/9` and Fisher `81/289`. The opposite Weyl seed has Fisher `1` at every phase. None of
these numbers is a Newton–Wigner operator.
-/

namespace DstDiophantine

namespace Logic

open Complex InnerProductSpace ContinuousLinearMap

/-! ### The weight space is a unitary phase -/

abbrev WeightSpace := EuclideanSpace ℂ (Fin 2)

noncomputable def weightNorm (r s : ℝ) : ℝ :=
  Real.sqrt (r ^ 2 + s ^ 2)

theorem weightNorm_sq (r s : ℝ) : weightNorm r s ^ 2 = r ^ 2 + s ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg r) (sq_nonneg s))

theorem weightNorm_ne_zero {r s : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) : weightNorm r s ≠ 0 := by
  intro hz
  have := weightNorm_sq r s
  rw [hz, sq, zero_mul] at this
  exact h this.symm

/-- Normalised weights `r` and `s e^{iα}` on the two momentum axes. -/
noncomputable def weightState (r s α : ℝ) : WeightSpace :=
  (r / weightNorm r s : ℂ) • EuclideanSpace.single 0 1 +
    ((s / weightNorm r s : ℂ) * exp (I * (α : ℂ))) • EuclideanSpace.single 1 1

/-- Derivative of `weightState` in the relative phase. -/
noncomputable def weightPhaseDerivative (r s α : ℝ) : WeightSpace :=
  ((s / weightNorm r s : ℂ) * I * exp (I * (α : ℂ))) • EuclideanSpace.single 1 1

private theorem norm_I_one : ‖(I : ℂ)‖ = 1 := by
  have hsq : ‖(I : ℂ)‖ ^ 2 = 1 := by
    rw [← normSq_eq_norm_sq, normSq_I]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]

private theorem norm_real (t : ℝ) : ‖(t : ℂ)‖ = |t| :=
  RCLike.norm_ofReal t

private theorem norm_real_sq (t : ℝ) : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
  rw [norm_real, sq_abs]

private theorem normSq_div (a b : ℝ) (hb : 0 ≤ b) :
    ‖(a : ℂ) / (b : ℂ)‖ ^ 2 = a ^ 2 / b ^ 2 := by
  have ha : ‖(a : ℂ)‖ = |a| := norm_real a
  have hb' : ‖(b : ℂ)‖ = b := by
    rw [norm_real, abs_of_nonneg hb]
  rw [norm_div, ha, hb', div_pow, sq_abs]

private theorem weight_basis_ortho :
    inner ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
        (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) = 0 ∧
      inner ℂ (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
          (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) = 1 ∧
        inner ℂ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
            (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [EuclideanSpace.inner_single_left]

theorem weightState_normSq {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    ‖weightState r s α‖ ^ 2 = 1 := by
  have hN := weightNorm_ne_zero h
  have hsq := weightNorm_sq r s
  set e0 : WeightSpace := EuclideanSpace.single 0 1
  set e1 : WeightSpace := EuclideanSpace.single 1 1
  set c0 : ℂ := (r / weightNorm r s : ℂ)
  set c1 : ℂ := (s / weightNorm r s : ℂ) * exp (I * (α : ℂ))
  have horth := weight_basis_ortho
  have hψ : weightState r s α = c0 • e0 + c1 • e1 := by
    simp [weightState, c0, c1, e0, e1]
  have hcross : inner ℂ (c0 • e0) (c1 • e1) = 0 := by
    rw [inner_smul_left, inner_smul_right, horth.1]
    simp
  rw [hψ, norm_add_sq (𝕜 := ℂ), hcross, RCLike.zero_re, mul_zero, add_zero]
  have he0 : ‖e0‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    calc
      Complex.ofReal (‖e0‖ ^ 2) = (‖e0‖ : ℂ) ^ 2 := Complex.ofReal_pow ‖e0‖ 2
      _ = inner ℂ e0 e0 := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := e0)).symm
      _ = 1 := horth.2.2
      _ = Complex.ofReal 1 := by norm_num
  have he1 : ‖e1‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    calc
      Complex.ofReal (‖e1‖ ^ 2) = (‖e1‖ : ℂ) ^ 2 := Complex.ofReal_pow ‖e1‖ 2
      _ = inner ℂ e1 e1 := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := e1)).symm
      _ = 1 := horth.2.1
      _ = Complex.ofReal 1 := by norm_num
  have hc0 : ‖c0 • e0‖ ^ 2 = r ^ 2 / (r ^ 2 + s ^ 2) := by
    rw [norm_smul, mul_pow, he0, mul_one]
    have hcoef : ‖c0‖ ^ 2 = r ^ 2 / weightNorm r s ^ 2 := by
      simp only [c0]
      exact normSq_div r (weightNorm r s) (Real.sqrt_nonneg _)
    rw [hcoef, hsq]
  have hc1 : ‖c1 • e1‖ ^ 2 = s ^ 2 / (r ^ 2 + s ^ 2) := by
    rw [norm_smul, mul_pow, he1, mul_one]
    have hce : ‖c1‖ ^ 2 = s ^ 2 / weightNorm r s ^ 2 := by
      simp only [c1, norm_mul, norm_exp_I, mul_one]
      exact normSq_div s (weightNorm r s) (Real.sqrt_nonneg _)
    rw [hce, hsq]
  rw [hc0, hc1]
  field_simp [h]

theorem weightState_inner_one {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    inner ℂ (weightState r s α) (weightState r s α) = 1 := by
  calc
    inner ℂ (weightState r s α) (weightState r s α) = (‖weightState r s α‖ : ℂ) ^ 2 :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := weightState r s α)
    _ = Complex.ofReal (‖weightState r s α‖ ^ 2) := (Complex.ofReal_pow _ 2).symm
    _ = Complex.ofReal 1 := by rw [weightState_normSq h]
    _ = 1 := by norm_num

theorem weightPhaseDerivative_normSq {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    ‖weightPhaseDerivative r s α‖ ^ 2 = s ^ 2 / (r ^ 2 + s ^ 2) := by
  have hN := weightNorm_ne_zero h
  have hsq := weightNorm_sq r s
  set e1 : WeightSpace := EuclideanSpace.single 1 1
  set d1 : ℂ := (s / weightNorm r s : ℂ) * I * exp (I * (α : ℂ))
  have hd : weightPhaseDerivative r s α = d1 • e1 := by
    simp [weightPhaseDerivative, d1, e1, mul_comm]
  have he1 : ‖e1‖ = 1 := by
    have hpow : ‖e1‖ ^ 2 = 1 := by
      apply Complex.ofReal_injective
      calc
        Complex.ofReal (‖e1‖ ^ 2) = (‖e1‖ : ℂ) ^ 2 := Complex.ofReal_pow ‖e1‖ 2
        _ = inner ℂ e1 e1 := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := e1)).symm
        _ = 1 := weight_basis_ortho.2.1
        _ = Complex.ofReal 1 := by norm_num
    rw [← Real.sqrt_sq (norm_nonneg e1), hpow, Real.sqrt_one]
  rw [hd, norm_smul, he1, mul_one]
  have hcoef : ‖d1‖ ^ 2 = s ^ 2 / weightNorm r s ^ 2 := by
    simp only [d1]
    rw [norm_mul, norm_mul, mul_pow, mul_pow, norm_exp_I, norm_I_one, one_pow, mul_one, mul_one]
    exact normSq_div s (weightNorm r s) (Real.sqrt_nonneg _)
  rw [hcoef, hsq]

theorem weightConnection_eq {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    inner ℂ (weightState r s α) (weightPhaseDerivative r s α) =
      I * (s ^ 2 / (r ^ 2 + s ^ 2) : ℂ) := by
  have hN := weightNorm_ne_zero h
  have hsq := weightNorm_sq r s
  set e0 : WeightSpace := EuclideanSpace.single 0 1
  set e1 : WeightSpace := EuclideanSpace.single 1 1
  set c0 : ℂ := (r / weightNorm r s : ℂ)
  set c1 : ℂ := (s / weightNorm r s : ℂ) * exp (I * (α : ℂ))
  set d1 : ℂ := I * c1
  have hbasis := weight_basis_ortho
  have hψ : weightState r s α = c0 • e0 + c1 • e1 := by
    simp [weightState, c0, c1, e0, e1]
  have hd : weightPhaseDerivative r s α = d1 • e1 := by
    simp [weightPhaseDerivative, d1, c1, e1, mul_left_comm, mul_comm]
  rw [hψ, hd, inner_add_left, inner_smul_left, inner_smul_right, inner_smul_left,
    inner_smul_right, hbasis.1, hbasis.2.1]
  simp only [mul_zero, mul_one]
  have hn : ‖c1‖ ^ 2 = s ^ 2 / (r ^ 2 + s ^ 2) := by
    simp only [c1, norm_mul, norm_exp_I, mul_one]
    rw [normSq_div s (weightNorm r s) (Real.sqrt_nonneg _), hsq]
  have hstar : starRingEnd ℂ c1 * c1 =
      (s ^ 2 : ℂ) / ((r ^ 2 : ℂ) + (s ^ 2 : ℂ)) := by
    have hmul : starRingEnd ℂ c1 * c1 = (‖c1‖ : ℂ) ^ 2 := by
      rw [show starRingEnd ℂ c1 = star c1 from rfl, Complex.star_def]
      exact RCLike.conj_mul c1
    have hcast : (‖c1‖ : ℂ) ^ 2 = Complex.ofReal (‖c1‖ ^ 2) :=
      (Complex.ofReal_pow ‖c1‖ 2).symm
    have hpush : Complex.ofReal (s ^ 2 / (r ^ 2 + s ^ 2)) =
        (s ^ 2 : ℂ) / ((r ^ 2 : ℂ) + (s ^ 2 : ℂ)) := by
      norm_cast
    exact (hmul.trans hcast).trans (congrArg Complex.ofReal hn |>.trans hpush)
  have hord : starRingEnd ℂ c1 * d1 = I * (starRingEnd ℂ c1 * c1) := by
    simp only [d1]
    ring
  rw [hord, hstar, zero_add]

/-- Horizontal derivative: the Berry connection is subtracted. -/
noncomputable def weightHorizontal (r s α : ℝ) : WeightSpace :=
  weightPhaseDerivative r s α -
    inner ℂ (weightState r s α) (weightPhaseDerivative r s α) • weightState r s α

theorem weightHorizontal_ortho {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    inner ℂ (weightState r s α) (weightHorizontal r s α) = 0 := by
  unfold weightHorizontal
  rw [inner_sub_right, inner_smul_right, weightState_inner_one h]
  ring

theorem weightHorizontal_inner_left {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    inner ℂ (weightHorizontal r s α) (weightState r s α) = 0 := by
  rw [← inner_conj_symm, weightHorizontal_ortho h, map_zero]

theorem weightHorizontal_normSq {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    ‖weightHorizontal r s α‖ ^ 2 = r ^ 2 * s ^ 2 / (r ^ 2 + s ^ 2) ^ 2 := by
  have hconn : inner ℂ (weightState r s α) (weightPhaseDerivative r s α) =
      I * (s ^ 2 / (r ^ 2 + s ^ 2) : ℂ) := weightConnection_eq h
  have hd : ‖weightPhaseDerivative r s α‖ ^ 2 = s ^ 2 / (r ^ 2 + s ^ 2) :=
    weightPhaseDerivative_normSq h
  have hψ : ‖weightState r s α‖ ^ 2 = 1 := weightState_normSq h
  unfold weightHorizontal
  set ψ := weightState r s α
  set d := weightPhaseDerivative r s α
  set c : ℂ := inner ℂ ψ d
  have hcnorm : ‖c‖ ^ 2 = (s ^ 2 / (r ^ 2 + s ^ 2)) ^ 2 := by
    rw [hconn, norm_mul, norm_I_one, one_mul]
    have hcoe : (s ^ 2 : ℂ) / ((r ^ 2 : ℂ) + (s ^ 2 : ℂ)) =
        Complex.ofReal (s ^ 2 / (r ^ 2 + s ^ 2)) := by
      have hpush : Complex.ofReal (s ^ 2 / (r ^ 2 + s ^ 2)) =
          (s ^ 2 : ℂ) / ((r ^ 2 : ℂ) + (s ^ 2 : ℂ)) := by
        norm_cast
      exact hpush.symm
    rw [hcoe]
    exact norm_real_sq (s ^ 2 / (r ^ 2 + s ^ 2))
  have hre : RCLike.re (inner ℂ d (c • ψ)) = ‖c‖ ^ 2 := by
    rw [inner_smul_right, ← inner_conj_symm, show inner ℂ ψ d = c from rfl,
      show starRingEnd ℂ c = star c from rfl, Complex.star_def, RCLike.mul_conj,
      RCLike.re_ofReal_pow]
  have hcψ : ‖c • ψ‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [norm_smul, mul_pow, hψ, mul_one]
  rw [norm_sub_sq (𝕜 := ℂ), hre, hcψ, hd, hcnorm]
  field_simp [h]
  ring

/-- Quantum Fisher information of the weight-space phase. It does not depend on `α`. -/
noncomputable def weightFisher (r s α : ℝ) : ℝ :=
  4 * ‖weightHorizontal r s α‖ ^ 2

theorem weightFisher_eq_phaseInformation {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    weightFisher r s α = phaseInformation r s := by
  unfold weightFisher
  rw [weightHorizontal_normSq h, phaseInformation_eq r s h]
  ring

/-- The phase derivative is `i` times the projector onto the second weight. -/
theorem weightPhaseDerivative_generator (r s α : ℝ) :
    weightPhaseDerivative r s α =
      I • (rankOne ℂ (EuclideanSpace.single 1 (1 : ℂ)) (EuclideanSpace.single 1 (1 : ℂ))
        (weightState r s α)) := by
  set e1 : WeightSpace := EuclideanSpace.single 1 1
  set c1 : ℂ := (s / weightNorm r s : ℂ) * exp (I * (α : ℂ))
  have hψ1 : weightState r s α 1 = c1 := by
    simp [weightState, c1, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single]
  have hd : weightPhaseDerivative r s α = (I * c1) • e1 := by
    simp [weightPhaseDerivative, c1, e1, mul_left_comm, mul_comm]
  have hinner : inner ℂ e1 (weightState r s α) = c1 := by
    rw [EuclideanSpace.inner_single_left, hψ1]
    simp
  rw [hd, rankOne_apply, hinner, smul_smul]

/-- Symmetric logarithmic derivative of the pure weight state. -/
noncomputable def phaseSLD (r s α : ℝ) : WeightSpace →ₗ[ℂ] WeightSpace :=
  ((2 : ℂ) • (rankOne ℂ (weightHorizontal r s α) (weightState r s α) +
      rankOne ℂ (weightState r s α) (weightHorizontal r s α))).toLinearMap

theorem phaseSLD_state {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    phaseSLD r s α (weightState r s α) = (2 : ℂ) • weightHorizontal r s α := by
  unfold phaseSLD
  simp only [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_add,
    LinearMap.smul_apply, LinearMap.add_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    weightState_inner_one h, weightHorizontal_inner_left h, one_smul, zero_smul, add_zero]

theorem phaseSLD_horizontal {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    phaseSLD r s α (weightHorizontal r s α) =
      ((2 : ℂ) * (‖weightHorizontal r s α‖ : ℂ) ^ 2) • weightState r s α := by
  unfold phaseSLD
  simp only [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_add,
    LinearMap.smul_apply, LinearMap.add_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    weightHorizontal_ortho h, inner_self_eq_norm_sq_to_K, zero_smul, zero_add, smul_smul]
  apply congrArg (fun z : ℂ => z • weightState r s α)
  rfl

theorem phaseSLD_fisher {r s α : ℝ} (h : r ^ 2 + s ^ 2 ≠ 0) :
    inner ℂ (weightState r s α) (phaseSLD r s α (weightState r s α)) = 0 ∧
      inner ℂ (weightState r s α)
          (phaseSLD r s α (phaseSLD r s α (weightState r s α))) =
        (phaseInformation r s : ℂ) := by
  have hstate : phaseSLD r s α (weightState r s α) = (2 : ℂ) • weightHorizontal r s α :=
    phaseSLD_state h
  have hD : phaseSLD r s α (weightHorizontal r s α) =
      ((2 : ℂ) * (‖weightHorizontal r s α‖ : ℂ) ^ 2) • weightState r s α :=
    phaseSLD_horizontal h
  refine ⟨?_, ?_⟩
  · rw [hstate, inner_smul_right, weightHorizontal_ortho h, mul_zero]
  · rw [hstate, LinearMap.map_smul, hD, smul_smul, inner_smul_right, weightState_inner_one h,
      mul_one]
    have hI := weightFisher_eq_phaseInformation (r := r) (s := s) (α := α) h
    rw [weightFisher] at hI
    calc
      (2 : ℂ) * (2 * (‖weightHorizontal r s α‖ : ℂ) ^ 2) =
          Complex.ofReal (4 * ‖weightHorizontal r s α‖ ^ 2) := by
        rw [(Complex.ofReal_pow ‖weightHorizontal r s α‖ 2).symm]
        norm_cast
        ring
      _ = (phaseInformation r s : ℂ) := by rw [hI]

/-! ### Projective Fisher information of two carriers -/

noncomputable def phaseCross (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) : ℝ :=
  (exp (I * (θ : ℂ)) * inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)).re

noncomputable def phaseCurveNormSq (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) : ℝ :=
  ‖(r : ℂ) • u‖ ^ 2 + ‖(s : ℂ) • v‖ ^ 2 + 2 * phaseCross r s u v θ

noncomputable def phaseFisherNum (r s : ℝ) (u v : DiracSpinor) : ℝ :=
  ‖(r : ℂ) • u‖ ^ 2 * ‖(s : ℂ) • v‖ ^ 2 -
    ‖inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖ ^ 2

/-- `ψ(θ) = r u + e^{iθ} s v`, before normalisation. -/
noncomputable def phaseCurve (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) : DiracSpinor :=
  (r : ℂ) • u + (exp (I * (θ : ℂ)) * (s : ℂ)) • v

noncomputable def phaseCurveDeriv (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) : DiracSpinor :=
  let _ := r
  let _ := u
  (I * exp (I * (θ : ℂ)) * (s : ℂ)) • v

/-- Projective quantum Fisher information of the relative phase. -/
noncomputable def phaseFisher (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) : ℝ :=
  4 * phaseFisherNum r s u v / phaseCurveNormSq r s u v θ ^ 2

theorem carrierOverlap_eq (u v : DiracSpinor) :
    carrierOverlap u v = carrierFidelity u v * ‖u‖ * ‖v‖ := by
  unfold carrierFidelity carrierOverlap
  by_cases h : ‖u‖ * ‖v‖ = 0
  · rcases mul_eq_zero.mp h with hu | hv
    · simp [norm_eq_zero.mp hu, inner_zero_left]
    · simp [norm_eq_zero.mp hv, inner_zero_right]
  · rw [mul_assoc, div_mul_cancel₀ _ h]

theorem bornWeight_eq (c : ℝ) (u : DiracSpinor) :
    ‖(c : ℂ) • u‖ ^ 2 = (|c| * ‖u‖) ^ 2 := by
  rw [norm_smul, mul_pow, norm_real]
  ring

theorem phaseAmplitude_norm (r s : ℝ) (u v : DiracSpinor) :
    ‖inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖ =
      carrierFidelity u v * (|r| * ‖u‖) * (|s| * ‖v‖) := by
  rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, starRingEnd_apply, norm_star]
  have hr : ‖(r : ℂ)‖ = |r| := norm_real r
  have hs : ‖(s : ℂ)‖ = |s| := norm_real s
  have hov : ‖inner ℂ u v‖ = carrierFidelity u v * ‖u‖ * ‖v‖ := by
    simpa [carrierOverlap] using carrierOverlap_eq u v
  rw [hr, hs, hov]
  ring

theorem phaseFisherNum_factor (r s : ℝ) (u v : DiracSpinor) :
    phaseFisherNum r s u v =
      (1 - carrierFidelity u v ^ 2) * (|r| * ‖u‖) ^ 2 * (|s| * ‖v‖) ^ 2 := by
  unfold phaseFisherNum
  rw [bornWeight_eq, bornWeight_eq, phaseAmplitude_norm]
  ring

private theorem phaseCurve_parts (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) :
    phaseCurve r s u v θ = (r : ℂ) • u + exp (I * (θ : ℂ)) • ((s : ℂ) • v) ∧
      phaseCurveDeriv r s u v θ = (I * exp (I * (θ : ℂ))) • ((s : ℂ) • v) := by
  constructor
  · rw [phaseCurve, ← smul_smul]
  · rw [phaseCurveDeriv, ← smul_smul]

theorem phaseCurve_normSq_eq (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) :
    ‖phaseCurve r s u v θ‖ ^ 2 = phaseCurveNormSq r s u v θ := by
  obtain ⟨hψ, _⟩ := phaseCurve_parts r s u v θ
  rw [hψ, norm_add_sq (𝕜 := ℂ)]
  have hz : ‖exp (I * (θ : ℂ)) • ((s : ℂ) • v)‖ ^ 2 = ‖(s : ℂ) • v‖ ^ 2 := by
    rw [norm_smul, norm_exp_I, one_mul]
  have hre : RCLike.re (inner ℂ ((r : ℂ) • u) (exp (I * (θ : ℂ)) • ((s : ℂ) • v))) =
      phaseCross r s u v θ := by
    rw [inner_smul_right]
    rfl
  rw [hz, hre]
  unfold phaseCurveNormSq
  ring

private theorem normSq_ofReal_add (t : ℝ) (w : ℂ) :
    ‖(t : ℂ) + w‖ ^ 2 = t ^ 2 + ‖w‖ ^ 2 + 2 * t * w.re := by
  rw [← normSq_eq_norm_sq, normSq_add, normSq_ofReal, normSq_eq_norm_sq]
  have hre : ((t : ℂ) * starRingEnd ℂ w).re = t * w.re := by
    rw [show starRingEnd ℂ w = star w from rfl, Complex.star_def, mul_re, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre, sq]
  ring

theorem phaseCurve_numerator (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) :
    ‖phaseCurveDeriv r s u v θ‖ ^ 2 * ‖phaseCurve r s u v θ‖ ^ 2 -
        ‖inner ℂ (phaseCurve r s u v θ) (phaseCurveDeriv r s u v θ)‖ ^ 2 =
      phaseFisherNum r s u v := by
  obtain ⟨hψ, hd⟩ := phaseCurve_parts r s u v θ
  set a : DiracSpinor := (r : ℂ) • u
  set b : DiracSpinor := (s : ℂ) • v
  set z : ℂ := exp (I * (θ : ℂ))
  have hdn : ‖phaseCurveDeriv r s u v θ‖ ^ 2 = ‖b‖ ^ 2 := by
    rw [hd, norm_smul]
    have hIz : ‖I * z‖ = 1 := by
      rw [norm_mul, norm_I_one, show ‖z‖ = 1 from norm_exp_I θ, mul_one]
    rw [hIz, one_mul]
  have hψn : ‖phaseCurve r s u v θ‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (z * inner ℂ a b).re := by
    rw [phaseCurve_normSq_eq]
    unfold phaseCurveNormSq phaseCross
    simp [a, b, z]
  have hinner : inner ℂ (phaseCurve r s u v θ) (phaseCurveDeriv r s u v θ) =
      I * (Complex.ofReal (‖b‖ ^ 2) + z * inner ℂ a b) := by
    rw [hψ, hd, inner_add_left]
    have h1 : inner ℂ a ((I * z) • b) = (I * z) * inner ℂ a b := inner_smul_right _ _ _
    have h2 : inner ℂ (z • b) ((I * z) • b) =
        starRingEnd ℂ z * (I * z * inner ℂ b b) := by
      rw [inner_smul_left, inner_smul_right]
    rw [h1, h2]
    have hb : inner ℂ b b = Complex.ofReal (‖b‖ ^ 2) := by
      rw [inner_self_eq_norm_sq_to_K]
      exact (Complex.ofReal_pow ‖b‖ 2).symm
    have hzz : starRingEnd ℂ z * (I * z) = I := by
      have hz1 : starRingEnd ℂ z * z = 1 := by
        rw [starRingEnd_apply, Complex.star_def, RCLike.conj_mul,
          show ‖z‖ = 1 from norm_exp_I θ]
        norm_num
      calc
        starRingEnd ℂ z * (I * z) = I * (starRingEnd ℂ z * z) := by ring
        _ = I := by rw [hz1, mul_one]
    rw [hb]
    have hassoc : starRingEnd ℂ z * (I * z * Complex.ofReal (‖b‖ ^ 2)) =
        (starRingEnd ℂ z * (I * z)) * Complex.ofReal (‖b‖ ^ 2) := by ring
    rw [hassoc, hzz]
    ring
  have hmod : ‖inner ℂ (phaseCurve r s u v θ) (phaseCurveDeriv r s u v θ)‖ ^ 2 =
      ‖b‖ ^ 4 + ‖inner ℂ a b‖ ^ 2 + 2 * ‖b‖ ^ 2 * (z * inner ℂ a b).re := by
    rw [hinner, norm_mul, norm_I_one, one_mul, normSq_ofReal_add]
    have hzβ : ‖z * inner ℂ a b‖ ^ 2 = ‖inner ℂ a b‖ ^ 2 := by
      rw [norm_mul, show ‖z‖ = 1 from norm_exp_I θ, one_mul]
    rw [hzβ]
    ring
  rw [hdn, hψn, hmod]
  unfold phaseFisherNum
  simp only [a, b]
  ring

theorem phaseFisher_eq_derivative (r s : ℝ) (u v : DiracSpinor) (θ : ℝ)
    (_hden : phaseCurveNormSq r s u v θ ≠ 0) :
    phaseFisher r s u v θ =
      4 * (‖phaseCurveDeriv r s u v θ‖ ^ 2 * ‖phaseCurve r s u v θ‖ ^ 2 -
          ‖inner ℂ (phaseCurve r s u v θ) (phaseCurveDeriv r s u v θ)‖ ^ 2) /
        ‖phaseCurve r s u v θ‖ ^ 4 := by
  rw [phaseCurve_numerator]
  have hpow : ‖phaseCurve r s u v θ‖ ^ 4 = phaseCurveNormSq r s u v θ ^ 2 := by
    rw [← phaseCurve_normSq_eq]
    ring
  rw [hpow]
  unfold phaseFisher
  rfl

theorem shellDeficit_mul_weight (r s : ℝ) (u v : DiracSpinor)
    (hW : (|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2 ≠ 0) :
    shellDeficit r s u v * ((|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2) ^ 2 =
      4 * phaseFisherNum r s u v := by
  set A : ℝ := |r| * ‖u‖
  set B : ℝ := |s| * ‖v‖
  have hAB : A ^ 2 + B ^ 2 ≠ 0 := hW
  rw [shellDeficit, phaseFisherNum_factor, phaseInformation_eq A B hAB]
  field_simp [hAB]
  ring

theorem weightSum_ne_of_curve {r s : ℝ} {u v : DiracSpinor} {θ : ℝ}
    (hden : phaseCurveNormSq r s u v θ ≠ 0) :
    (|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2 ≠ 0 := by
  intro hW
  have hA : |r| * ‖u‖ = 0 := by nlinarith [sq_nonneg (|s| * ‖v‖)]
  have hB : |s| * ‖v‖ = 0 := by nlinarith [sq_nonneg (|r| * ‖u‖)]
  have ha : (r : ℂ) • u = 0 := by
    have hsq : ‖(r : ℂ) • u‖ ^ 2 = 0 := by
      rw [bornWeight_eq, hA]
      ring
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hb : (s : ℂ) • v = 0 := by
    have hsq : ‖(s : ℂ) • v‖ ^ 2 = 0 := by
      rw [bornWeight_eq, hB]
      ring
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  unfold phaseCurveNormSq phaseCross at hden
  simp [ha, hb] at hden

theorem phaseFisher_eq_scaled {r s : ℝ} {u v : DiracSpinor} {θ : ℝ}
    (hden : phaseCurveNormSq r s u v θ ≠ 0) :
    phaseFisher r s u v θ =
      shellDeficit r s u v *
        ((|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2) ^ 2 /
          phaseCurveNormSq r s u v θ ^ 2 := by
  have hW := weightSum_ne_of_curve hden
  have hmul := shellDeficit_mul_weight r s u v hW
  unfold phaseFisher
  rw [← hmul]

theorem phaseFisher_quadrature {r s : ℝ} {u v : DiracSpinor} {θ : ℝ}
    (hcross : phaseCross r s u v θ = 0) (hden : phaseCurveNormSq r s u v θ ≠ 0) :
    phaseFisher r s u v θ = shellDeficit r s u v := by
  have hsq : phaseCurveNormSq r s u v θ =
      (|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2 := by
    unfold phaseCurveNormSq
    rw [hcross, mul_zero, add_zero, bornWeight_eq, bornWeight_eq]
  rw [phaseFisher_eq_scaled hden, hsq]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (by rwa [hsq] at hden))

theorem phaseAmplitude_eq_zero_of_fidelity {u v : DiracSpinor} (hF : carrierFidelity u v = 0)
    (r s : ℝ) : inner ℂ ((r : ℂ) • u) ((s : ℂ) • v) = 0 := by
  have hnorm : ‖inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖ = 0 := by
    rw [phaseAmplitude_norm, hF, zero_mul, zero_mul]
  exact norm_eq_zero.mp hnorm

theorem phaseFisher_orthogonal {r s : ℝ} {u v : DiracSpinor} (hF : carrierFidelity u v = 0)
    (θ : ℝ) (hden : phaseCurveNormSq r s u v θ ≠ 0) :
    phaseFisher r s u v θ = shellDeficit r s u v := by
  have hcross : phaseCross r s u v θ = 0 := by
    unfold phaseCross
    rw [phaseAmplitude_eq_zero_of_fidelity hF]
    simp
  exact phaseFisher_quadrature hcross hden

theorem phaseFisher_parallel {r s : ℝ} {u v : DiracSpinor} (hF : carrierFidelity u v = 1)
    (θ : ℝ) (_hden : phaseCurveNormSq r s u v θ ≠ 0) :
    phaseFisher r s u v θ = 0 := by
  have hnum : phaseFisherNum r s u v = 0 := by
    rw [phaseFisherNum_factor, hF]
    ring
  unfold phaseFisher
  rw [hnum, mul_zero, zero_div]

private theorem exp_mul_I_re (θ : ℝ) (z : ℂ) :
    (exp ((θ : ℂ) * I) * z).re = Real.cos θ * z.re - Real.sin θ * z.im := by
  rw [Complex.exp_mul_I, mul_re, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

private theorem exp_align_re (z : ℂ) :
    (exp (I * -((arg z) : ℂ)) * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · have hcos : Real.cos (arg z) = z.re / ‖z‖ := cos_arg hz
    have hsin : Real.sin (arg z) = z.im / ‖z‖ := sin_arg z
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hswap : I * -((arg z) : ℂ) = ((-arg z) : ℂ) * I := by
      rw [← Complex.ofReal_neg]
      ring
    rw [hswap, ← Complex.ofReal_neg, exp_mul_I_re, Real.cos_neg, Real.sin_neg, hcos, hsin]
    field_simp [hn]
    nlinarith [sq_nonneg z.re, sq_nonneg z.im, normSq_eq_norm_sq z, normSq_apply z]

private theorem exp_align_neg (z : ℂ) :
    (exp (I * (-((arg z) : ℂ) + (Real.pi : ℂ))) * z).re = -‖z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · have hcos : Real.cos (arg z) = z.re / ‖z‖ := cos_arg hz
    have hsin : Real.sin (arg z) = z.im / ‖z‖ := sin_arg z
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hform : (exp (Complex.ofReal (-arg z + Real.pi) * I) * z).re = -‖z‖ := by
      rw [exp_mul_I_re, Real.cos_add_pi, Real.sin_add_pi, Real.cos_neg, Real.sin_neg, hcos, hsin]
      field_simp [hn]
      nlinarith [sq_nonneg z.re, sq_nonneg z.im, normSq_eq_norm_sq z, normSq_apply z]
    have harg : I * (-((arg z) : ℂ) + (Real.pi : ℂ)) =
        Complex.ofReal (-arg z + Real.pi) * I := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_add]
      ring
    rw [harg]
    exact hform

private theorem exp_quadrature_re (z : ℂ) :
    (exp (I * (-((arg z) : ℂ) + (Real.pi : ℂ) / 2)) * z).re = 0 := by
  by_cases hz : z = 0
  · simp [hz]
  · have hcos : Real.cos (arg z) = z.re / ‖z‖ := cos_arg hz
    have hsin : Real.sin (arg z) = z.im / ‖z‖ := sin_arg z
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hθcos : Real.cos (-arg z + Real.pi / 2) = Real.sin (arg z) := by
      rw [Real.cos_add, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    have hθsin : Real.sin (-arg z + Real.pi / 2) = Real.cos (arg z) := by
      rw [Real.sin_add, Real.sin_neg, Real.cos_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    have hform : (exp (Complex.ofReal (-arg z + Real.pi / 2) * I) * z).re = 0 := by
      rw [exp_mul_I_re, hθcos, hθsin, hcos, hsin]
      field_simp [hn]
      ring
    have harg : I * (-((arg z) : ℂ) + (Real.pi : ℂ) / 2) =
        Complex.ofReal (-arg z + Real.pi / 2) * I := by
      rw [← Complex.ofReal_neg]
      have hhalf : Complex.ofReal Real.pi / 2 = Complex.ofReal (Real.pi / 2) := by
        norm_cast
      rw [hhalf, ← Complex.ofReal_add]
      ring
    rw [harg]
    exact hform

theorem exists_phaseCross_zero (r s : ℝ) (u v : DiracSpinor) :
    ∃ θ : ℝ, phaseCross r s u v θ = 0 := by
  refine ⟨-arg (inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)) + Real.pi / 2, ?_⟩
  simp only [phaseCross]
  convert exp_quadrature_re (inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)) using 1
  push_cast
  ring

theorem exists_phaseCross_peak (r s : ℝ) (u v : DiracSpinor) :
    ∃ θ : ℝ,
      phaseCross r s u v θ = ‖inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖ := by
  refine ⟨-arg (inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)), ?_⟩
  simp only [phaseCross]
  convert exp_align_re (inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)) using 1
  push_cast
  ring

theorem exists_phaseCross_valley (r s : ℝ) (u v : DiracSpinor) :
    ∃ θ : ℝ,
      phaseCross r s u v θ = -‖inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖ := by
  refine ⟨-arg (inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)) + Real.pi, ?_⟩
  simp only [phaseCross]
  convert exp_align_neg (inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)) using 1
  push_cast
  ring

theorem phaseFisher_extreme_ne {r s : ℝ} {u v : DiracSpinor} {θ : ℝ}
    (hF0 : 0 < carrierFidelity u v) (hF1 : carrierFidelity u v < 1)
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcross : phaseCross r s u v θ = ‖inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖ ∨
      phaseCross r s u v θ = -‖inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖) :
    phaseFisher r s u v θ ≠ shellDeficit r s u v := by
  set A : ℝ := |r| * ‖u‖
  set B : ℝ := |s| * ‖v‖
  set W : ℝ := A ^ 2 + B ^ 2
  set amp : ℂ := inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)
  have hA : 0 < A := mul_pos (abs_pos.mpr hr) (norm_pos_iff.mpr hu)
  have hB : 0 < B := mul_pos (abs_pos.mpr hs) (norm_pos_iff.mpr hv)
  have hamp : ‖amp‖ = carrierFidelity u v * A * B := by
    simpa [amp, A, B, mul_assoc] using phaseAmplitude_norm r s u v
  have hamp_pos : 0 < ‖amp‖ := by
    rw [hamp]
    exact mul_pos (mul_pos hF0 hA) hB
  have hWpos : 0 < W := by nlinarith
  have hgap : carrierFidelity u v ^ 2 < 1 := by
    have : carrierFidelity u v ^ 2 < 1 ^ 2 := by
      rw [sq_lt_sq, abs_of_nonneg (carrierFidelity_nonneg u v), abs_one]
      exact hF1
    simpa using this
  have hdef : shellDeficit r s u v ≠ 0 := by
    have hsum : A ^ 2 + B ^ 2 ≠ 0 := ne_of_gt hWpos
    have hI : phaseInformation A B ≠ 0 := by
      intro hz
      rcases (phaseInformation_eq_zero_iff A B hsum).mp hz with hA0 | hB0
      · exact (ne_of_gt hA) hA0
      · exact (ne_of_gt hB) hB0
    unfold shellDeficit
    have hFsq : (1 - carrierFidelity u v ^ 2) ≠ 0 := by linarith
    exact mul_ne_zero hFsq hI
  have hden_pos : 0 < phaseCurveNormSq r s u v θ := by
    rcases hcross with hpeak | hvalley
    · unfold phaseCurveNormSq
      rw [hpeak, bornWeight_eq, bornWeight_eq]
      nlinarith
    · unfold phaseCurveNormSq
      rw [hvalley, bornWeight_eq, bornWeight_eq, hamp]
      have hnn : 0 ≤ (A - B) ^ 2 := sq_nonneg _
      nlinarith [hnn]
  have hden : phaseCurveNormSq r s u v θ ≠ 0 := ne_of_gt hden_pos
  have hscale := phaseFisher_eq_scaled (r := r) (s := s) (u := u) (v := v) (θ := θ) hden
  intro heq
  have hdiv : shellDeficit r s u v * W ^ 2 / phaseCurveNormSq r s u v θ ^ 2 =
      shellDeficit r s u v := by
    rw [hscale] at heq
    exact heq
  rw [div_eq_iff (pow_ne_zero 2 hden)] at hdiv
  have hdiff : shellDeficit r s u v * (W ^ 2 - phaseCurveNormSq r s u v θ ^ 2) = 0 := by
    linear_combination hdiv
  rcases mul_eq_zero.mp hdiff with hbad | hsq
  · exact hdef hbad
  · have hden_eq : phaseCurveNormSq r s u v θ =
        W + 2 * phaseCross r s u v θ := by
      unfold phaseCurveNormSq
      rw [bornWeight_eq, bornWeight_eq]
    have hcross_ne : phaseCross r s u v θ ≠ 0 := by
      rcases hcross with hpeak | hvalley
      · rw [hpeak]
        exact ne_of_gt hamp_pos
      · rw [hvalley]
        linarith
    have hWden : W ≠ phaseCurveNormSq r s u v θ := by
      rw [hden_eq]
      intro hsame
      have : (2 : ℝ) * phaseCross r s u v θ = 0 := by linarith
      exact hcross_ne ((mul_eq_zero.mp this).resolve_left (by norm_num))
    have hsq' : W ^ 2 = phaseCurveNormSq r s u v θ ^ 2 := by linarith
    have habs := (sq_eq_sq₀ (le_of_lt hWpos) (le_of_lt hden_pos)).mp hsq'
    exact hWden habs

theorem bornDensity_eq_phaseCurveNormSq (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (x : Vec4) :
    bornDensity (shellPacket r s α p q u v) x =
      phaseCurveNormSq r s u v (wavePhase (q - p) x + α) := by
  rw [bornDensity_shellPacket]
  have hwu : shellWeight r u = ‖(r : ℂ) • u‖ ^ 2 := by
    unfold shellWeight
    calc
      r ^ 2 * ‖u‖ ^ 2 = |r| ^ 2 * ‖u‖ ^ 2 := by rw [← sq_abs]
      _ = (|r| * ‖u‖) ^ 2 := by ring
      _ = ‖(r : ℂ) • u‖ ^ 2 := (bornWeight_eq r u).symm
  have hwv : shellWeight s v = ‖(s : ℂ) • v‖ ^ 2 := by
    unfold shellWeight
    calc
      s ^ 2 * ‖v‖ ^ 2 = |s| ^ 2 * ‖v‖ ^ 2 := by rw [← sq_abs]
      _ = (|s| * ‖v‖) ^ 2 := by ring
      _ = ‖(s : ℂ) • v‖ ^ 2 := (bornWeight_eq s v).symm
  rw [hwu, hwv]
  unfold phaseCurveNormSq phaseCross
  have hinner : inner ℂ ((r : ℂ) • u) ((s : ℂ) • v) =
      ((r * s : ℝ) : ℂ) * inner ℂ u v := by
    rw [inner_smul_left, inner_smul_right]
    have hstar : starRingEnd ℂ (r : ℂ) = (r : ℂ) := by
      rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
    rw [hstar, ← mul_assoc]
    congr 1
    push_cast
    ring
  have hθ : exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) =
      exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hinner, hθ]
  have hre :
      (exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) *
          (((r * s : ℝ) : ℂ) * inner ℂ u v)).re =
        r * s *
          (exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) * inner ℂ u v).re := by
    have hcomm :
        exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) *
            (((r * s : ℝ) : ℂ) * inner ℂ u v) =
          ((r * s : ℝ) : ℂ) *
            (exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) * inner ℂ u v) := by
      ring
    rw [hcomm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ← hθ]
    ring
  rw [hre, ← hθ]
  ring

/-! ### Mass 3, in three readings -/

theorem shellRest_phaseFisher :
    (∃ θ : ℝ, phaseCross 1 1 shellParticleP shellParticleQ θ = 0 ∧
        phaseFisher 1 1 shellParticleP shellParticleQ θ = 544 / 625) ∧
      (∃ θ : ℝ, phaseCross 1 1 shellParticleP shellParticleQ θ =
          ‖inner ℂ (((1 : ℝ) : ℂ) • shellParticleP) (((1 : ℝ) : ℂ) • shellParticleQ)‖ ∧
        phaseFisher 1 1 shellParticleP shellParticleQ θ = 136 / 289) ∧
        (∃ θ : ℝ, phaseCross 1 1 shellParticleP shellParticleQ θ =
            -‖inner ℂ (((1 : ℝ) : ℂ) • shellParticleP) (((1 : ℝ) : ℂ) • shellParticleQ)‖ ∧
          phaseFisher 1 1 shellParticleP shellParticleQ θ = 17 / 8) := by
  have hprod : ‖shellParticleP‖ * ‖shellParticleQ‖ = 50 / 9 := by
    have heq : ‖shellParticleP‖ = ‖shellParticleQ‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        (shellRest_norms.1.trans shellRest_norms.2.symm)
    rw [heq, ← sq, shellRest_norms.2]
  have hamp : ‖inner ℂ (((1 : ℝ) : ℂ) • shellParticleP) (((1 : ℝ) : ℂ) • shellParticleQ)‖ = 2 := by
    rw [phaseAmplitude_norm, shellRest_fidelity]
    simp only [abs_one, one_mul]
    calc
      (9 / 25) * ‖shellParticleP‖ * ‖shellParticleQ‖ =
          (9 / 25) * (‖shellParticleP‖ * ‖shellParticleQ‖) := by ring
      _ = (9 / 25) * (50 / 9) := by rw [hprod]
      _ = 2 := by norm_num
  have hnum : phaseFisherNum 1 1 shellParticleP shellParticleQ = 2176 / 81 := by
    rw [phaseFisherNum_factor, shellRest_fidelity]
    simp only [abs_one, one_mul]
    rw [shellRest_norms.1, shellRest_norms.2]
    norm_num
  have hW : ‖((1 : ℝ) : ℂ) • shellParticleP‖ ^ 2 + ‖((1 : ℝ) : ℂ) • shellParticleQ‖ ^ 2 =
      100 / 9 := by
    rw [bornWeight_eq, bornWeight_eq]
    simp only [abs_one, one_mul]
    rw [shellRest_norms.1, shellRest_norms.2]
    norm_num
  have hfisher (θ : ℝ) (c : ℝ) (hcross : phaseCross 1 1 shellParticleP shellParticleQ θ = c) :
      phaseFisher 1 1 shellParticleP shellParticleQ θ =
        4 * (2176 / 81) / (100 / 9 + 2 * c) ^ 2 := by
    unfold phaseFisher phaseCurveNormSq
    rw [hcross, hnum, hW]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨θ, hθ⟩ := exists_phaseCross_zero 1 1 shellParticleP shellParticleQ
    refine ⟨θ, hθ, ?_⟩
    rw [hfisher θ 0 hθ]
    norm_num
  · obtain ⟨θ, hθ⟩ := exists_phaseCross_peak 1 1 shellParticleP shellParticleQ
    have hc : phaseCross 1 1 shellParticleP shellParticleQ θ = 2 := by rw [hθ, hamp]
    refine ⟨θ, by rw [hθ, hamp], ?_⟩
    rw [hfisher θ 2 hc]
    norm_num
  · obtain ⟨θ, hθ⟩ := exists_phaseCross_valley 1 1 shellParticleP shellParticleQ
    have hc : phaseCross 1 1 shellParticleP shellParticleQ θ = -2 := by rw [hθ, hamp]
    refine ⟨θ, by rw [hθ, hamp], ?_⟩
    rw [hfisher θ (-2) hc]
    norm_num

/-- The extreme chart ratio squares to shell information, not to the Fisher number at either
extreme phase. -/
theorem shellRest_chart_not_fisher (α : ℝ) :
    ∃ x y : Vec4,
      ((bornDensity (shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ) x -
            bornDensity (shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ) y) /
          (bornDensity (shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ) x +
            bornDensity (shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ)
              y)) ^ 2 =
        shellInformation 1 1 shellParticleP shellParticleQ ∧
        shellInformation 1 1 shellParticleP shellParticleQ = 81 / 625 ∧
          (∃ θ : ℝ, phaseFisher 1 1 shellParticleP shellParticleQ θ = 136 / 289) ∧
            (∃ θ : ℝ, phaseFisher 1 1 shellParticleP shellParticleQ θ = 17 / 8) ∧
              (81 / 625 : ℝ) ≠ 136 / 289 ∧ (81 / 625 : ℝ) ≠ 17 / 8 := by
  have hden : shellWeight 1 shellParticleP + shellWeight 1 shellParticleQ ≠ 0 := by
    unfold shellWeight
    rw [shellRest_norms.1, shellRest_norms.2]
    norm_num
  obtain ⟨x, y, _, hsq⟩ :=
    shell_chart_ratio (r := 1) (s := 1) (by norm_num) (by norm_num) shellRest_geometry.2.2.2.2.2.2
      α shellParticleP shellParticleQ hden
  refine ⟨x, y, hsq, shellRest_information.1, ?_, ?_, by norm_num, by norm_num⟩
  · obtain ⟨θ, _, hF⟩ := shellRest_phaseFisher.2.1
    exact ⟨θ, hF⟩
  · obtain ⟨θ, _, hF⟩ := shellRest_phaseFisher.2.2
    exact ⟨θ, hF⟩

theorem shellLab_phaseFisher :
    phaseFisher 1 1 shellParticleP shellLabSpinor
        (wavePhase (restMomentum 3 - shellRestP) (timeShift 0)) = 81 / 841 ∧
      phaseFisher 1 1 shellParticleP shellLabSpinor
          (wavePhase (restMomentum 3 - shellRestP) (timeShift (-Real.pi / 2))) = 81 / 25 ∧
        (∃ t : ℝ,
          phaseCross 1 1 shellParticleP shellLabSpinor
              (wavePhase (restMomentum 3 - shellRestP) (timeShift t)) = 0 ∧
            phaseCurveNormSq 1 1 shellParticleP shellLabSpinor
                (wavePhase (restMomentum 3 - shellRestP) (timeShift t)) = 68 / 9 ∧
              phaseFisher 1 1 shellParticleP shellLabSpinor
                  (wavePhase (restMomentum 3 - shellRestP) (timeShift t)) = 81 / 289) ∧
          shellInformation 1 1 shellParticleP shellLabSpinor = 144 / 289 ∧
            (144 / 289 : ℝ) ≠ 81 / 841 ∧ (144 / 289 : ℝ) ≠ 81 / 25 := by
  have hnum : phaseFisherNum 1 1 shellParticleP shellLabSpinor = 4 := by
    rw [phaseFisherNum_factor, shellLab_fidelity]
    simp only [abs_one, one_mul]
    rw [shellRest_norms.1, shellLab_norm]
    norm_num
  have hW : ‖((1 : ℝ) : ℂ) • shellParticleP‖ ^ 2 + ‖((1 : ℝ) : ℂ) • shellLabSpinor‖ ^ 2 =
      68 / 9 := by
    rw [bornWeight_eq, bornWeight_eq]
    simp only [abs_one, one_mul]
    rw [shellRest_norms.1, shellLab_norm]
    norm_num
  have hd0 := shellLab_time_density.1
  have hd1 := shellLab_time_density.2.1
  have hborn0 :=
    bornDensity_eq_phaseCurveNormSq 1 1 0 shellRestP (restMomentum 3) shellParticleP
      shellLabSpinor (timeShift 0)
  have hborn1 :=
    bornDensity_eq_phaseCurveNormSq 1 1 0 shellRestP (restMomentum 3) shellParticleP
      shellLabSpinor (timeShift (-Real.pi / 2))
  have hsq0 : phaseCurveNormSq 1 1 shellParticleP shellLabSpinor
      (wavePhase (restMomentum 3 - shellRestP) (timeShift 0)) = 116 / 9 := by
    have hadd : wavePhase (restMomentum 3 - shellRestP) (timeShift 0) =
        wavePhase (restMomentum 3 - shellRestP) (timeShift 0) + 0 := (add_zero _).symm
    rw [hadd, ← hborn0]
    exact hd0
  have hsq1 : phaseCurveNormSq 1 1 shellParticleP shellLabSpinor
      (wavePhase (restMomentum 3 - shellRestP) (timeShift (-Real.pi / 2))) = 20 / 9 := by
    have hadd : wavePhase (restMomentum 3 - shellRestP) (timeShift (-Real.pi / 2)) =
        wavePhase (restMomentum 3 - shellRestP) (timeShift (-Real.pi / 2)) + 0 :=
      (add_zero _).symm
    rw [hadd, ← hborn1]
    exact hd1
  have hF0 : phaseFisher 1 1 shellParticleP shellLabSpinor
      (wavePhase (restMomentum 3 - shellRestP) (timeShift 0)) = 81 / 841 := by
    unfold phaseFisher
    rw [hnum, hsq0]
    norm_num
  have hF1 : phaseFisher 1 1 shellParticleP shellLabSpinor
      (wavePhase (restMomentum 3 - shellRestP) (timeShift (-Real.pi / 2))) = 81 / 25 := by
    unfold phaseFisher
    rw [hnum, hsq1]
    norm_num
  refine ⟨hF0, hF1, ?_, shellLab_information.1, by norm_num, by norm_num⟩
  · obtain ⟨θ, hθ⟩ := exists_phaseCross_zero 1 1 shellParticleP shellLabSpinor
    have hδ : (restMomentum 3 - shellRestP) 0 ≠ 0 := by
      rw [shellLab_geometry.2.1]
      norm_num
    obtain ⟨t, ht⟩ := exists_wavePhase_eq_time hδ θ
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [ht, hθ]
    · rw [ht]
      unfold phaseCurveNormSq
      rw [hθ, mul_zero, add_zero, hW]
    · rw [ht]
      unfold phaseFisher phaseCurveNormSq
      rw [hθ, hnum, mul_zero, add_zero, hW]
      norm_num

theorem shellOrth_phaseFisher (θ : ℝ) :
    phaseFisher 1 1 shellParticleP shellOrthQ θ = 1 ∧
      shellDeficit 1 1 shellParticleP shellOrthQ = 1 := by
  have hF : carrierFidelity shellParticleP shellOrthQ = 0 := by
    unfold carrierFidelity carrierOverlap
    rw [shellOrth_inner]
    simp
  have hden : phaseCurveNormSq 1 1 shellParticleP shellOrthQ θ ≠ 0 := by
    unfold phaseCurveNormSq phaseCross
    rw [phaseAmplitude_eq_zero_of_fidelity hF, bornWeight_eq, bornWeight_eq]
    simp only [abs_one, one_mul, mul_zero]
    rw [shellRest_norms.1, shellOrth_norm]
    norm_num
  have hfish := phaseFisher_orthogonal hF θ hden
  have hdef := shellOrth_deficit.2.2.2
  exact ⟨hfish.trans hdef, hdef⟩

end Logic

end DstDiophantine
