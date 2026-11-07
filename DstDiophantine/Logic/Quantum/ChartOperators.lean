import DstDiophantine.Logic.Quantum.Complementarity
import DstDiophantine.Logic.Quantum.DiracGauge
import DstDiophantine.Logic.Quantum.ExternalChart
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Trace

/-!
# Position and momentum on the chart

The Hilbert space of the information is the dual spinor space `ℂ²`. It is
finite-dimensional, so no operators on it obey `[A, B] = i I`: the trace of a
commutator vanishes, while `tr(i I)` is `2i`. The spin commutators live there
because they are traceless.

Position and momentum answer the chart argument of the de Broglie phase.
On a differentiable field, `X^ν` multiplies by the coordinate `x^ν` and
`P_μ = -i ∂_μ`. They satisfy `[X^ν, P_μ] = i δ^ν_μ`. A differentiable field
is an eigenfield of every `P_μ` with eigenvalues `p_μ` exactly when
translation multiplies it by `e^{i p·a}`. A plane wave of nonzero amplitude
is such an eigenfield, and it is an eigenfield of no position operator.
Dividing out its phase from `P_μ` of the wave returns `p_μ` times the carrier.

An uncertainty bound for orbital angles is not claimed.
-/

namespace DstDiophantine

namespace Logic

open Complex Matrix

/-! ### The dual Hilbert space does not carry the canonical pair -/

private theorem trace_comp_sub_comm (A B : DualSpinor →ₗ[ℂ] DualSpinor) :
    LinearMap.trace ℂ DualSpinor (A.comp B - B.comp A) = 0 := by
  rw [LinearMap.map_sub, LinearMap.trace_comp_comm' B A, sub_self]

/-- No endomorphisms of the dual spinor space satisfy `[A, B] = i I`. -/
theorem no_ccr_dualSpinor (A B : DualSpinor →ₗ[ℂ] DualSpinor) :
    A.comp B - B.comp A ≠ I • LinearMap.id := by
  intro h
  have htr := congrArg (LinearMap.trace ℂ DualSpinor) h
  rw [trace_comp_sub_comm, LinearMap.map_smul, LinearMap.trace_id, dualSpinor_finrank] at htr
  have hzero : (I : ℂ) * 2 = 0 := by
    simpa [smul_eq_mul, mul_comm] using htr.symm
  exact I_ne_zero ((mul_eq_zero.mp hzero).resolve_right (by norm_num))

/-- The same obstruction on a single Dirac value, which is four-dimensional. -/
theorem no_ccr_diracSpinor (A B : DiracSpinor →ₗ[ℂ] DiracSpinor) :
    A.comp B - B.comp A ≠ I • LinearMap.id := by
  intro h
  have htr := congrArg (LinearMap.trace ℂ DiracSpinor) h
  rw [LinearMap.map_sub, LinearMap.trace_comp_comm' B A, sub_self, LinearMap.map_smul,
    LinearMap.trace_id, diracSpinor_finrank] at htr
  have hzero : (I : ℂ) * 4 = 0 := by
    simpa [smul_eq_mul, mul_comm] using htr.symm
  exact I_ne_zero ((mul_eq_zero.mp hzero).resolve_right (by norm_num))

/-- Every commutator on the dual matrices is traceless, and so is
`[σ·a, σ·b]`. -/
theorem trace_dual_commutator (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (A * B - B * A) = 0 := by
  rw [trace_sub, trace_mul_comm, sub_self]

theorem trace_pauliComb_comm (a b : Fin 3 → ℝ) :
    trace (pauliComb a * pauliComb b - pauliComb b * pauliComb a) = 0 :=
  trace_dual_commutator (pauliComb a) (pauliComb b)

/-! ### Chart operators -/

/-- Position operator `(X^ν Ψ)(x) = x^ν Ψ(x)`. -/
noncomputable def positionOp (ν : Fin 4) (Ψ : Vec4 → DiracSpinor) : Vec4 → DiracSpinor :=
  fun x => (x ν : ℂ) • Ψ x

/-- Momentum operator `P_μ Ψ = -i ∂_μ Ψ`. -/
noncomputable def momentumOp (μ : Fin 4) (Ψ : Vec4 → DiracSpinor) : Vec4 → DiracSpinor :=
  fun x => (-I) • partialD Ψ μ x

/-- Eigenfield of one position component: `X^ν Ψ = λ Ψ`. -/
def PositionEigen (ν : Fin 4) (lam : ℂ) (Ψ : Vec4 → DiracSpinor) : Prop :=
  ∀ x, positionOp ν Ψ x = lam • Ψ x

private theorem smul_comm_spinor (a b : ℂ) (v : DiracSpinor) : a • (b • v) = b • (a • v) := by
  rw [smul_smul, smul_smul, mul_comm]

private theorem I_mul_neg_I : I * -I = (1 : ℂ) := by
  rw [mul_neg, I_mul_I, neg_neg]

/-- Chart coordinate `x^ν`, as a real-linear map into `ℂ`. -/
noncomputable def chartCoordCLM (ν : Fin 4) : Vec4 →L[ℝ] ℂ :=
  ofRealCLM.comp (ContinuousLinearMap.proj ν)

theorem chartCoordCLM_apply (ν : Fin 4) (x : Vec4) : chartCoordCLM ν x = (x ν : ℂ) := by
  simp [chartCoordCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ofRealCLM_apply]

theorem chartCoordCLM_single (ν μ : Fin 4) :
    chartCoordCLM ν (Pi.single μ (1 : ℝ)) = if ν = μ then 1 else 0 := by
  rw [chartCoordCLM_apply]
  by_cases hν : ν = μ
  · subst hν
    simp
  · rw [Pi.single_eq_of_ne hν, ite_eq_right hν]
    simp

theorem differentiable_positionOp {Ψ : Vec4 → DiracSpinor} (hΨ : Differentiable ℝ Ψ)
    (ν : Fin 4) : Differentiable ℝ (positionOp ν Ψ) := by
  have hEq : positionOp ν Ψ = fun y => chartCoordCLM ν y • Ψ y := by
    funext y
    rw [positionOp, chartCoordCLM_apply]
  rw [hEq]
  exact (chartCoordCLM ν).differentiable.smul hΨ

theorem partialD_positionOp {Ψ : Vec4 → DiracSpinor} {x : Vec4}
    (hΨ : DifferentiableAt ℝ Ψ x) (ν μ : Fin 4) :
    partialD (positionOp ν Ψ) μ x =
      (x ν : ℂ) • partialD Ψ μ x +
        (if ν = μ then (1 : ℂ) else 0) • Ψ x := by
  have hEq : positionOp ν Ψ = fun y => chartCoordCLM ν y • Ψ y := by
    funext y
    rw [positionOp, chartCoordCLM_apply]
  rw [hEq]
  unfold partialD
  rw [fderiv_fun_smul (chartCoordCLM ν).differentiableAt hΨ]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    (chartCoordCLM ν).fderiv]
  rw [chartCoordCLM_apply, chartCoordCLM_single]

/-- On every differentiable field, `[X^ν, P_μ] = i δ^ν_μ`. -/
theorem position_comm_momentum {Ψ : Vec4 → DiracSpinor} (hΨ : Differentiable ℝ Ψ)
    (ν μ : Fin 4) (x : Vec4) :
    positionOp ν (momentumOp μ Ψ) x - momentumOp μ (positionOp ν Ψ) x =
      (if ν = μ then I else 0) • Ψ x := by
  have hPX : momentumOp μ (positionOp ν Ψ) x =
      (-I) • ((x ν : ℂ) • partialD Ψ μ x) +
        (-I) • ((if ν = μ then (1 : ℂ) else 0) • Ψ x) := by
    unfold momentumOp
    rw [partialD_positionOp (hΨ x), smul_add]
  have hXP : positionOp ν (momentumOp μ Ψ) x =
      (x ν : ℂ) • ((-I) • partialD Ψ μ x) := by
    unfold positionOp momentumOp
    rfl
  rw [hXP, hPX, smul_comm_spinor]
  have hsub : ∀ (a b : DiracSpinor), a - (a + b) = -b := fun _ _ => by abel
  rw [hsub]
  simp only [neg_smul]
  split_ifs <;> simp [neg_neg, one_smul, zero_smul]

theorem momentumOp_planeWave (p : Vec4) (u : DiracSpinor) (μ : Fin 4) (x : Vec4) :
    momentumOp μ (planeWave p u) x = (p μ : ℂ) • planeWave p u x := by
  unfold momentumOp
  rw [planeWave_partialD, smul_smul, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]

/-- Dividing out the de Broglie phase of `P_μ` on a plane wave returns
`p_μ` times the carrier. -/
theorem momentumOp_planeWave_strip (p : Vec4) (u : DiracSpinor) (μ : Fin 4) (x : Vec4) :
    exp (-(I * (wavePhase p x : ℂ))) • momentumOp μ (planeWave p u) x = (p μ : ℂ) • u := by
  rw [momentumOp_planeWave, smul_comm_spinor, planeWave_strip]

theorem momentumEigen_imp_momentumOp {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (h : MomentumEigen p Ψ) (μ : Fin 4) (x : Vec4) :
    momentumOp μ Ψ x = (p μ : ℂ) • Ψ x := by
  have hpw : Ψ = planeWave p (Ψ 0) := by
    funext y
    simpa [planeWave] using (momentumEigen_iff_phase.mp h) y
  rw [hpw, momentumOp_planeWave]

private theorem partial_of_momentumOp {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (h : ∀ μ x, momentumOp μ Ψ x = (p μ : ℂ) • Ψ x) (μ : Fin 4) (x : Vec4) :
    partialD Ψ μ x = (I * (p μ : ℂ)) • Ψ x := by
  have hμ := h μ x
  unfold momentumOp at hμ
  apply_fun (fun w : DiracSpinor => I • w) at hμ
  rw [smul_smul, smul_smul, I_mul_neg_I, one_smul] at hμ
  exact hμ

private theorem differentiableAt_wavePhase (p : Vec4) (x : Vec4) :
    DifferentiableAt ℝ (fun y : Vec4 => wavePhase p y) x := by
  have hfun : (fun y : Vec4 => wavePhase p y) = ⇑(wavePhaseCLM p) := by
    funext y
    exact wavePhaseCLM_apply p y
  rw [hfun]
  exact (wavePhaseCLM p).differentiableAt

private theorem fderiv_eq_zero_of_partial {f : Vec4 → DiracSpinor} {x : Vec4}
    (h : ∀ μ, partialD f μ x = 0) : fderiv ℝ f x = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ μ : Fin 4, v μ • Pi.single μ (1 : ℝ) := by
    ext ν
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single ν]
    · simp
    · intro μ _ hμ
      rw [Pi.single_eq_of_ne (Ne.symm hμ), mul_zero]
    · intro hν
      exact absurd (Finset.mem_univ ν) hν
  rw [hv, map_sum]
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [map_smul]
  have hpartial : (fderiv ℝ f x) (Pi.single μ (1 : ℝ)) = partialD f μ x := rfl
  rw [hpartial, h μ, smul_zero]

/-- A differentiable field is an eigenfield of every momentum component,
with eigenvalues `p_μ`, exactly when translation multiplies it by `e^{i p·a}`. -/
theorem momentumEigen_iff_momentumOp {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (hΨ : Differentiable ℝ Ψ) :
    MomentumEigen p Ψ ↔ ∀ μ x, momentumOp μ Ψ x = (p μ : ℂ) • Ψ x := by
  constructor
  · intro h μ x
    exact momentumEigen_imp_momentumOp h μ x
  · intro h
    let χ : Vec4 → ℝ := fun y => wavePhase p y
    have hχ : Differentiable ℝ χ := fun x => differentiableAt_wavePhase p x
    let f : Vec4 → DiracSpinor := gaugePhase (-1) χ Ψ
    have hf : Differentiable ℝ f := by
      intro x
      exact (hasFDerivAt_gaugePhase (-1) (hχ x) (hΨ x)).differentiableAt
    have hpartial : ∀ x μ, partialD f μ x = 0 := by
      intro x μ
      have hder := partial_of_momentumOp h μ x
      rw [partialD_gaugePhase (-1) (hχ x) (hΨ x)]
      have hgrad : fderiv ℝ χ x (Pi.single μ (1 : ℝ)) = p μ := by
        have hfun : χ = ⇑(wavePhaseCLM p) := by
          funext y
          exact wavePhaseCLM_apply p y
        rw [hfun, (wavePhaseCLM p).fderiv, wavePhaseCLM_apply, wavePhase_single]
      rw [hgrad, hder]
      have hcancel : (I * (p μ : ℂ)) • Ψ x +
          (I * (((-1) * p μ : ℝ) : ℂ)) • Ψ x = 0 := by
        rw [← add_smul]
        have hcoeff : (I * (p μ : ℂ)) + (I * (((-1) * p μ : ℝ) : ℂ)) = 0 := by
          push_cast
          ring
        rw [hcoeff, zero_smul]
      rw [hcancel, smul_zero]
    have hf' : ∀ x, fderiv ℝ f x = 0 := fun x =>
      fderiv_eq_zero_of_partial (fun μ => hpartial x μ)
    have hconst : ∀ x, f x = f 0 := fun x => is_const_of_fderiv_eq_zero hf hf' x 0
    have hf0 : f 0 = Ψ 0 := by
      simp [f, gaugePhase, χ, wavePhase_zero]
    refine momentumEigen_iff_phase.mpr ?_
    intro x
    have hx := hconst x
    rw [hf0] at hx
    -- `exp(-i p·x) • Ψ x = Ψ 0`
    have hstrip : exp (-(I * (wavePhase p x : ℂ))) • Ψ x = Ψ 0 := by
      simpa [f, gaugePhase, χ, neg_mul] using hx
    apply_fun (fun w : DiracSpinor => exp (I * (wavePhase p x : ℂ)) • w) at hstrip
    rw [smul_smul, ← exp_add] at hstrip
    have hcancel : I * (wavePhase p x : ℂ) + -(I * (wavePhase p x : ℂ)) = 0 := by ring
    rw [hcancel, exp_zero, one_smul] at hstrip
    exact hstrip

theorem bornDensity_momentumEigen {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (h : MomentumEigen p Ψ) (x y : Vec4) : bornDensity Ψ x = bornDensity Ψ y := by
  have hpw : Ψ = planeWave p (Ψ 0) := by
    funext z
    simpa [planeWave] using (momentumEigen_iff_phase.mp h) z
  rw [hpw, bornDensity_planeWave_const]

/-- A plane wave of nonzero amplitude is an eigenfield of no position component. -/
theorem planeWave_not_positionEigen {u : DiracSpinor} (hu : u ≠ 0) (p : Vec4)
    (ν : Fin 4) (lam : ℂ) : ¬ PositionEigen ν lam (planeWave p u) := by
  intro h
  have h0 := h 0
  have hpw0 : planeWave p u 0 = u := by
    unfold planeWave
    rw [wavePhase_zero, ofReal_zero, mul_zero, exp_zero, one_smul]
  unfold positionOp at h0
  rw [show ((0 : Vec4) ν : ℂ) = 0 by simp, zero_smul, hpw0] at h0
  have hlam : lam = 0 := by
    have : lam • u = 0 := h0.symm
    exact (smul_eq_zero.mp this).resolve_right hu
  have h1 := h (Pi.single ν 1)
  rw [hlam, zero_smul] at h1
  unfold positionOp at h1
  have hcoord : ((Pi.single ν (1 : ℝ) : Vec4) ν : ℂ) = 1 := by simp
  rw [hcoord, one_smul] at h1
  exact planeWave_ne_zero hu p (Pi.single ν 1) h1

end Logic

end DstDiophantine
