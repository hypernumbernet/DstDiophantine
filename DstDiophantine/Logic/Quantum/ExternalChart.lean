import DstDiophantine.Logic.Quantum.Complementarity
import DstDiophantine.Logic.Quantum.DeBroglie
import DstDiophantine.Logic.Quantum.DiracGauge
import DstDiophantine.Logic.Quantum.LightFilter

/-!
# The carrier before the chart

The curve of a dual rotor lies on a dual spinor. Its parameter scales the
dual rapidity and solves `i u' = ½ (ω·σ) u`, while the time component the
chart receives stays the information weight. A chart time of nonzero energy
writes a de Broglie phase of slope `p₀`. Dividing the phase `e^{i p·x}` out
of a plane wave returns the carrier.

The matrix `e^{iα} I` is a dual rotor exactly when the phase is `±1`. A
constant potential `e^{-i V t}` is a dual rotor at every time exactly when
`V = 0`, and a nonzero momentum kick fails to be one at some chart point.
That phase is the argument written after the carrier. The Schrödinger
equation takes the argument as its domain. Position and momentum on that
argument are the chart operators of `ChartOperators`.
-/

namespace DstDiophantine

namespace Logic

open Complex

/-! ### The spin curve lives on the carrier -/

/-- Dual rotor of rapidity `t ω`, applied to the carrier. -/
noncomputable def spinCurve (ω : DualRapidity) (u : DualSpinor) (t : ℝ) : DualSpinor :=
  applyMat (dualRotorMat (t • ω)) u

theorem hasDerivAt_spinCurve (ω : DualRapidity) (u : DualSpinor) (t : ℝ) :
    HasDerivAt (spinCurve ω u)
      ((-(I / 2)) • applyMat (pauliComb (fun a => ω a)) (spinCurve ω u t)) t :=
  hasDerivAt_dualRotor_ray ω u t

private theorem I_mul_neg_I_div_two : I * (-(I / 2)) = (1 / 2 : ℂ) := by
  calc
    I * (-(I / 2)) = -(I * (I / 2)) := by ring
    _ = -((I * I) / 2) := by ring
    _ = -((-1) / 2) := by rw [I_mul_I]
    _ = (1 / 2 : ℂ) := by ring

/-- The spin curve solves `i u' = ½ (ω·σ) u`. -/
theorem spinCurve_schrodinger (ω : DualRapidity) (u : DualSpinor) (t : ℝ) :
    I • deriv (spinCurve ω u) t =
      (1 / 2 : ℂ) • applyMat (pauliComb (fun a => ω a)) (spinCurve ω u t) := by
  rw [(hasDerivAt_spinCurve ω u t).deriv, smul_smul, I_mul_neg_I_div_two]

theorem spinCurve_informationWeight (ω : DualRapidity) (u : DualSpinor) (t : ℝ) :
    informationWeight (spinCurve ω u t) = informationWeight u := by
  unfold spinCurve informationWeight
  rw [norm_applyMat_dualRotor_sq]

/-- The time component the chart receives does not move with the parameter. -/
theorem spinCurve_manifest_time (ω : DualRapidity) (u : DualSpinor) (t : ℝ) :
    manifest (spinCurve ω u t) 0 = manifest u 0 := by
  rw [manifest_zero, manifest_zero, spinCurve_informationWeight]

/-- De Broglie phase along the chart's time axis, of slope `p₀`. -/
theorem wavePhase_time_axis (p : Vec4) (t : ℝ) :
    wavePhase p (t • (Pi.single 0 (1 : ℝ) : Vec4)) = t * p 0 := by
  rw [wavePhase_smul_right, wavePhase_single]

/-- The spin parameter keeps the filter's time component fixed. A chart time
of nonzero energy does not keep the de Broglie phase fixed. -/
theorem spin_parameter_not_chart_time (ω : DualRapidity) (u : DualSpinor) {p : Vec4}
    (hp : p 0 ≠ 0) :
    (∀ t, manifest (spinCurve ω u t) 0 = manifest u 0) ∧
      ∃ t : ℝ, wavePhase p (t • (Pi.single 0 (1 : ℝ) : Vec4)) ≠ 0 :=
  ⟨fun t => spinCurve_manifest_time ω u t,
    ⟨1, by rw [wavePhase_time_axis]; simpa using hp⟩⟩

/-! ### A chart point is a phase in front of the carrier -/

theorem planeWave_strip (p : Vec4) (u : DiracSpinor) (x : Vec4) :
    exp (-(I * (wavePhase p x : ℂ))) • planeWave p u x = u := by
  unfold planeWave
  rw [smul_smul, ← exp_add]
  have hcancel : -(I * (wavePhase p x : ℂ)) + I * (wavePhase p x : ℂ) = 0 := by ring
  rw [hcancel, exp_zero, one_smul]

/-! ### A continuous phase on the identity is a dual rotor only at `±1` -/

/-- Multiplication of the identity by the phase `e^{iα}`. -/
noncomputable def phaseGate (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  exp (I * (α : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem phaseGate_zero : phaseGate 0 = 1 := by
  unfold phaseGate
  simp [exp_zero]

theorem phaseGate_det (α : ℝ) :
    (phaseGate α).det = exp (I * (α : ℂ)) ^ 2 := by
  unfold phaseGate
  rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]

private theorem sq_eq_one_complex {c : ℂ} (h : c ^ 2 = 1) : c = 1 ∨ c = -1 := by
  have hfac : (c - 1) * (c + 1) = c ^ 2 - 1 := by ring
  have h0 : (c - 1) * (c + 1) = 0 := by rw [hfac, h, sub_self]
  rcases mul_eq_zero.mp h0 with hsub | hadd
  · left
    exact sub_eq_zero.mp hsub
  · right
    exact eq_neg_of_add_eq_zero_left hadd

private theorem exp_I_pi_div_two : exp (I * ((Real.pi / 2 : ℝ) : ℂ)) = I := by
  rw [mul_comm I _, exp_mul_I]
  simp

private theorem exp_I_neg_pi_div_two :
    exp (I * ((-(Real.pi / 2) : ℝ) : ℂ)) = -I := by
  rw [Complex.ofReal_neg, mul_neg, mul_comm I _, exp_neg, exp_mul_I]
  simp [inv_I]

/-- `e^{iα} I` is a dual rotor exactly at the phases `±1`. -/
theorem phaseGate_dualRotor_iff (α : ℝ) :
    (∃ β : DualRapidity, dualRotorMat β = phaseGate α) ↔
      exp (I * (α : ℂ)) = 1 ∨ exp (I * (α : ℂ)) = -1 := by
  constructor
  · intro ⟨β, hβ⟩
    have hdet : (phaseGate α).det = 1 := by rw [← hβ, dualRotorMat_det]
    rw [phaseGate_det] at hdet
    exact sq_eq_one_complex hdet
  · intro h
    rcases h with h | h
    · refine ⟨0, ?_⟩
      rw [dualRotorMat_zero, phaseGate, h, one_smul]
    · refine ⟨EuclideanSpace.single 2 (2 * Real.pi), ?_⟩
      rw [dualRotorMat_axis2_two_pi, phaseGate, h, neg_one_smul]

/-- A constant potential phase is a dual rotor at every time exactly when the
potential vanishes. -/
theorem constPotential_dualRotor_iff (V : ℝ) :
    (∀ t : ℝ, ∃ β : DualRapidity, dualRotorMat β = phaseGate (-(V * t))) ↔ V = 0 := by
  constructor
  · intro h
    by_contra hV
    have ht : V * (Real.pi / (2 * V)) = Real.pi / 2 := by
      field_simp [hV]
    have hphase : exp (I * ((-(V * (Real.pi / (2 * V))) : ℝ) : ℂ)) = -I := by
      have harg : -(V * (Real.pi / (2 * V))) = -(Real.pi / 2) := by linarith
      rw [harg]
      exact exp_I_neg_pi_div_two
    obtain ⟨β, hβ⟩ := h (Real.pi / (2 * V))
    have hpm := (phaseGate_dualRotor_iff (-(V * (Real.pi / (2 * V))))).mp ⟨β, hβ⟩
    rw [hphase] at hpm
    rcases hpm with h1 | hm1
    · have him := congrArg Complex.im h1
      simp at him
    · have him := congrArg Complex.im hm1
      simp at him
  · intro hV
    subst hV
    intro t
    refine ⟨0, ?_⟩
    rw [dualRotorMat_zero]
    have hzero : phaseGate (-((0 : ℝ) * t)) = phaseGate 0 := by simp
    rw [hzero, phaseGate_zero]

theorem exists_wavePhase_half_pi {δ : Vec4} (hδ : δ ≠ 0) :
    ∃ x : Vec4, wavePhase δ x = Real.pi / 2 := by
  have hcomp : ∃ μ : Fin 4, δ μ ≠ 0 := by
    by_contra h
    push Not at h
    apply hδ
    ext μ
    exact h μ
  obtain ⟨μ, hμ⟩ := hcomp
  refine ⟨(Real.pi / 2 / δ μ) • Pi.single μ (1 : ℝ), ?_⟩
  rw [wavePhase_smul_right, wavePhase_single]
  field_simp [hμ]

/-- A nonzero momentum kick is a phase on the identity, and that phase fails
to be a dual rotor at some chart point. -/
theorem kick_not_dualRotor {k : Vec4} (hk : k ≠ 0) :
    ∃ x : Vec4, ∀ β : DualRapidity, dualRotorMat β ≠ phaseGate (wavePhase k x) := by
  obtain ⟨x, hx⟩ := exists_wavePhase_half_pi hk
  refine ⟨x, ?_⟩
  intro β hβ
  have hpm := (phaseGate_dualRotor_iff (wavePhase k x)).mp ⟨β, hβ⟩
  rw [hx] at hpm
  have hI : exp (I * ((Real.pi / 2 : ℝ) : ℂ)) = I := exp_I_pi_div_two
  rw [hI] at hpm
  rcases hpm with h1 | hm1
  · have him := congrArg Complex.im h1
    simp at him
  · have hre := congrArg Complex.re hm1
    simp at hre

end Logic

end DstDiophantine
