import DstDiophantine.Logic.Quantum.DiracField
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Electromagnetic coupling of the Dirac field

Minimal coupling `D_μ = ∂_μ - i e A_μ` gives `γ^μ D_μ Ψ = -m Ψ`. Solutions are
carried to solutions by `Ψ ↦ e^{i e χ} Ψ`, `A ↦ A + ∂χ`; in a constant
potential a plane wave solves the coupled equation exactly when its amplitude
solves the free equation at the kinetic momentum `p - e a`. The current is
gauge invariant and conserved for real mass, charge, and potential.

For a twice-differentiable spinor `[D_μ, D_ν] = -i e F_{μν}`, so every
solution obeys `η^{μμ} D_μ D_μ Ψ - (i e / 2) F_{μν} γ^μ γ^ν Ψ = m² Ψ`. In the
Weyl blocks the field-strength term is `e σ·(B + iE)` above and
`e σ·(B - iE)` below, with `B = (F₂₃, F₃₁, F₁₂)` and `E_k = F_{k0}`. Since
`σ·B = i Γ(B)` with `Γ` the dual generators, the magnetic field enters both
blocks through the same dual-rotor generator. At zero charge the equation is
the Klein–Gordon equation. A Hamiltonian `½ ω·σ` evolves a dual spinor by the
dual rotor of rapidity `t ω`.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

open scoped InnerProductSpace

/-! ### Minimal coupling to an electromagnetic potential -/

/-- Covariant derivative `D_μ Ψ = ∂_μ Ψ - i e A_μ Ψ`. -/
noncomputable def covD (e : ℝ) (A : Vec4 → Vec4) (Ψ : Vec4 → DiracSpinor) (μ : Fin 4)
    (x : Vec4) : DiracSpinor :=
  partialD Ψ μ x - (I * ((e * A x μ : ℝ) : ℂ)) • Ψ x

/-- Coupled Dirac operator `γ^μ D_μ`. -/
noncomputable def gaugeDiracOp (e : ℝ) (A : Vec4 → Vec4) (Ψ : Vec4 → DiracSpinor)
    (x : Vec4) : DiracSpinor :=
  ∑ μ : Fin 4, applyDiracMat (diracMat μ) (covD e A Ψ μ x)

/-- Dirac equation in a potential, `γ^μ (∂_μ - i e A_μ) Ψ = -m Ψ`: the image of
`γ(p - eA) Ψ = i m Ψ` under `p_μ ↦ -i ∂_μ`. -/
def DiracGaugeField (m e : ℝ) (A : Vec4 → Vec4) (Ψ : Vec4 → DiracSpinor) : Prop :=
  Differentiable ℝ Ψ ∧ ∀ x, gaugeDiracOp e A Ψ x = (-(m : ℂ)) • Ψ x

theorem gaugeDiracOp_eq (e : ℝ) (A : Vec4 → Vec4) (Ψ : Vec4 → DiracSpinor) (x : Vec4) :
    gaugeDiracOp e A Ψ x =
      diracOp Ψ x - (I * (e : ℂ)) • applyDiracMat (slashMat (A x)) (Ψ x) := by
  unfold gaugeDiracOp diracOp covD slashMat
  simp only [Fin.sum_univ_four, applyDiracMat_add_mat, applyDiracMat_smul_mat,
    applyDiracMat_sub, applyDiracMat_smul, ofReal_mul]
  module

/-- Without a potential the coupled equation is the free equation. -/
theorem diracGaugeField_zero (m e : ℝ) (Ψ : Vec4 → DiracSpinor) :
    DiracGaugeField m e 0 Ψ ↔ DiracField m Ψ := by
  have h : ∀ x, gaugeDiracOp e 0 Ψ x = diracOp Ψ x := fun x => by
    rw [gaugeDiracOp_eq]
    simp [slashMat, applyDiracMat_zero_mat]
  simp only [DiracGaugeField, DiracField, h]

/-! ### Gauge covariance -/

/-- Local phase `e^{i e χ}` acting on a spinor field. -/
noncomputable def gaugePhase (e : ℝ) (χ : Vec4 → ℝ) (Ψ : Vec4 → DiracSpinor) :
    Vec4 → DiracSpinor :=
  fun x => Complex.exp (I * ((e * χ x : ℝ) : ℂ)) • Ψ x

/-- Potential shifted by the gradient `A_μ + ∂_μ χ`. -/
noncomputable def gaugePot (A : Vec4 → Vec4) (χ : Vec4 → ℝ) : Vec4 → Vec4 :=
  fun x μ => A x μ + fderiv ℝ χ x (Pi.single μ 1)

theorem hasFDerivAt_gaugePhase (e : ℝ) {χ : Vec4 → ℝ} {Ψ : Vec4 → DiracSpinor} {x : Vec4}
    (hχ : DifferentiableAt ℝ χ x) (hΨ : DifferentiableAt ℝ Ψ x) :
    HasFDerivAt (gaugePhase e χ Ψ)
      (Complex.exp (I * ((e * χ x : ℝ) : ℂ)) • fderiv ℝ Ψ x +
        (Complex.exp (I * ((e * χ x : ℝ) : ℂ)) •
          (I • Complex.ofRealCLM.comp (e • fderiv ℝ χ x))).smulRight (Ψ x)) x := by
  have h1 : HasFDerivAt (fun y => ((e * χ y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (e • fderiv ℝ χ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hχ.hasFDerivAt.const_mul e)
  have h2 := (h1.const_mul I).cexp
  exact h2.smul hΨ.hasFDerivAt

theorem partialD_gaugePhase (e : ℝ) {χ : Vec4 → ℝ} {Ψ : Vec4 → DiracSpinor} {x : Vec4}
    (hχ : DifferentiableAt ℝ χ x) (hΨ : DifferentiableAt ℝ Ψ x) (μ : Fin 4) :
    partialD (gaugePhase e χ Ψ) μ x =
      Complex.exp (I * ((e * χ x : ℝ) : ℂ)) •
        (partialD Ψ μ x + (I * ((e * fderiv ℝ χ x (Pi.single μ 1) : ℝ) : ℂ)) • Ψ x) := by
  unfold partialD
  rw [(hasFDerivAt_gaugePhase e hχ hΨ).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, smul_add, smul_smul]
  push_cast
  ring_nf

/-- Gauge covariance of the covariant derivative. -/
theorem covD_gauge (e : ℝ) (A : Vec4 → Vec4) {χ : Vec4 → ℝ} {Ψ : Vec4 → DiracSpinor}
    {x : Vec4} (hχ : DifferentiableAt ℝ χ x) (hΨ : DifferentiableAt ℝ Ψ x) (μ : Fin 4) :
    covD e (gaugePot A χ) (gaugePhase e χ Ψ) μ x =
      Complex.exp (I * ((e * χ x : ℝ) : ℂ)) • covD e A Ψ μ x := by
  unfold covD
  rw [partialD_gaugePhase e hχ hΨ]
  simp only [gaugePot, gaugePhase]
  push_cast
  module

/-- Gauge covariance of the coupled Dirac equation. -/
theorem diracGaugeField_gauge {m e : ℝ} {A : Vec4 → Vec4} {χ : Vec4 → ℝ}
    {Ψ : Vec4 → DiracSpinor} (hχ : Differentiable ℝ χ) (hΨ : DiracGaugeField m e A Ψ) :
    DiracGaugeField m e (gaugePot A χ) (gaugePhase e χ Ψ) := by
  refine ⟨fun x => (hasFDerivAt_gaugePhase e (hχ x) (hΨ.1 x)).differentiableAt, fun x => ?_⟩
  unfold gaugeDiracOp
  simp only [covD_gauge e A (hχ x) (hΨ.1 x), applyDiracMat_smul]
  rw [← Finset.smul_sum]
  have h := hΨ.2 x
  unfold gaugeDiracOp at h
  rw [h, gaugePhase, smul_comm]

/-! ### Kinetic momentum in a constant potential -/

theorem slashMat_sub_smul (p a : Vec4) (e : ℝ) :
    slashMat (p - e • a) = slashMat p - (e : ℂ) • slashMat a := by
  unfold slashMat
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ofReal_sub, ofReal_mul, sub_smul,
    Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]

/-- In a constant potential a plane wave of momentum `p` solves the coupled
equation exactly when its amplitude solves the momentum-space equation at the
kinetic momentum `p - e a`. -/
theorem diracGaugeField_planeWave_iff (m e : ℝ) (a p : Vec4) (u : DiracSpinor) :
    DiracGaugeField m e (fun _ => a) (planeWave p u) ↔ DiracMomentum m (p - e • a) u := by
  have hop : ∀ x, gaugeDiracOp e (fun _ => a) (planeWave p u) x =
      (I * Complex.exp (I * (wavePhase p x : ℂ))) • applyDiracMat (slashMat (p - e • a)) u := by
    intro x
    rw [gaugeDiracOp_eq, planeWave_diracOp, slashMat_sub_smul, applyDiracMat_sub_mat,
      applyDiracMat_smul_mat]
    unfold planeWave
    rw [applyDiracMat_smul]
    module
  constructor
  · rintro ⟨-, h⟩
    have h0 := h 0
    rw [hop] at h0
    unfold planeWave at h0
    rw [wavePhase_zero, ofReal_zero, mul_zero, Complex.exp_zero, mul_one, one_smul] at h0
    unfold DiracMomentum
    have := congrArg (fun v => (-I) • v) h0
    simp only [smul_smul] at this
    rw [show -I * I = (1 : ℂ) by rw [neg_mul, I_mul_I, neg_neg], one_smul] at this
    rw [this]
    congr 1
    ring
  · intro h
    refine ⟨differentiable_planeWave p u, fun x => ?_⟩
    rw [hop, h]
    unfold planeWave
    rw [smul_smul, smul_smul]
    congr 1
    rw [show I * Complex.exp (I * (wavePhase p x : ℂ)) * (I * (m : ℂ)) =
      (I * I) * (m : ℂ) * Complex.exp (I * (wavePhase p x : ℂ)) by ring, I_mul_I]
    ring

/-! ### Current in a potential -/

/-- The current is gauge invariant. -/
theorem currentField_gaugePhase (e : ℝ) (χ : Vec4 → ℝ) (Ψ Φ : Vec4 → DiracSpinor)
    (μ : Fin 4) (x : Vec4) :
    currentField (gaugePhase e χ Ψ) (gaugePhase e χ Φ) μ x = currentField Ψ Φ μ x := by
  unfold currentField gaugePhase diracCurrent
  rw [applyDiracMat_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
  have h : (starRingEnd ℂ) (Complex.exp (I * ((e * χ x : ℝ) : ℂ))) *
      Complex.exp (I * ((e * χ x : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal]
  rw [h, one_mul]

/-- Continuity equation in a real potential: for two differentiable solutions
of the same mass and charge the current is conserved. -/
theorem currentField_conserved_gauge {m e : ℝ} {A : Vec4 → Vec4} {Ψ Φ : Vec4 → DiracSpinor}
    (hΨ : DiracGaugeField m e A Ψ) (hΦ : DiracGaugeField m e A Φ) (x : Vec4) :
    ∑ μ : Fin 4, fderiv ℝ (currentField Ψ Φ μ) x (Pi.single μ 1) = 0 := by
  simp only [currentField_partial hΨ.1 hΦ.1]
  rw [Finset.sum_add_distrib]
  have hA : ∀ μ : Fin 4, inner ℂ (Ψ x)
      (applyDiracMat (diracAdjointMat * diracMat μ) (partialD Φ μ x)) =
      inner ℂ (Ψ x) (applyDiracMat diracAdjointMat
        (applyDiracMat (diracMat μ) (partialD Φ μ x))) := fun μ => by
    rw [applyDiracMat_mul]
  have hB : ∀ μ : Fin 4, inner ℂ (partialD Ψ μ x)
      (applyDiracMat (diracAdjointMat * diracMat μ) (Φ x)) =
      -inner ℂ (applyDiracMat diracAdjointMat
        (applyDiracMat (diracMat μ) (partialD Ψ μ x))) (Φ x) := fun μ => by
    rw [applyDiracMat_inner_ct, diracAdjointMat_mul_gamma_antiHermitian, applyDiracMat_neg,
      inner_neg_left, applyDiracMat_mul]
  simp only [hA, hB]
  have hΦx : ∑ μ : Fin 4, applyDiracMat (diracMat μ) (partialD Φ μ x) =
      (-(m : ℂ)) • Φ x + (I * (e : ℂ)) • applyDiracMat (slashMat (A x)) (Φ x) := by
    have h := hΦ.2 x
    rw [gaugeDiracOp_eq] at h
    unfold diracOp at h
    rw [← h]
    abel
  have hΨx : ∑ μ : Fin 4, applyDiracMat (diracMat μ) (partialD Ψ μ x) =
      (-(m : ℂ)) • Ψ x + (I * (e : ℂ)) • applyDiracMat (slashMat (A x)) (Ψ x) := by
    have h := hΨ.2 x
    rw [gaugeDiracOp_eq] at h
    unfold diracOp at h
    rw [← h]
    abel
  rw [Finset.sum_neg_distrib, ← inner_sum, ← sum_inner, ← applyDiracMat_finset_sum,
    ← applyDiracMat_finset_sum, hΦx, hΨx, applyDiracMat_add, applyDiracMat_add,
    applyDiracMat_smul, applyDiracMat_smul, applyDiracMat_smul, applyDiracMat_smul,
    inner_add_right, inner_add_left, inner_smul_right, inner_smul_right, inner_smul_left,
    inner_smul_left]
  have hsym : inner ℂ (applyDiracMat diracAdjointMat (Ψ x)) (Φ x) =
      inner ℂ (Ψ x) (applyDiracMat diracAdjointMat (Φ x)) := by
    rw [applyDiracMat_inner_ct, diracAdjointMat_hermitian]
  have hanti : inner ℂ (applyDiracMat diracAdjointMat
      (applyDiracMat (slashMat (A x)) (Ψ x))) (Φ x) =
      -inner ℂ (Ψ x) (applyDiracMat diracAdjointMat
        (applyDiracMat (slashMat (A x)) (Φ x))) := by
    rw [← applyDiracMat_mul]
    have h := applyDiracMat_inner_ct ((diracAdjointMat * slashMat (A x))ᴴ) (Ψ x) (Φ x)
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [← h, diracAdjointMat_mul_slash_antiHermitian, applyDiracMat_neg, inner_neg_right,
      applyDiracMat_mul]
  rw [hsym, hanti]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-! ### Commutator of covariant derivatives -/

/-- `∂_μ A_ν`. -/
noncomputable def potD (A : Vec4 → Vec4) (ν μ : Fin 4) (x : Vec4) : ℝ :=
  fderiv ℝ (fun y => A y ν) x (Pi.single μ 1)

/-- Field strength `F_{μν} = ∂_μ A_ν - ∂_ν A_μ`. -/
noncomputable def fieldStrength (A : Vec4 → Vec4) (x : Vec4) (μ ν : Fin 4) : ℝ :=
  potD A ν μ x - potD A μ ν x

theorem fieldStrength_antisymm (A : Vec4 → Vec4) (x : Vec4) (μ ν : Fin 4) :
    fieldStrength A x μ ν = -fieldStrength A x ν μ := by
  unfold fieldStrength
  ring

theorem differentiable_partialD {Ψ : Vec4 → DiracSpinor} (hΨ : ContDiff ℝ 2 Ψ) (ν : Fin 4) :
    Differentiable ℝ (fun y => partialD Ψ ν y) := by
  have h : Differentiable ℝ (fderiv ℝ Ψ) :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact fun x => (h x).clm_apply (differentiableAt_const _)

theorem hasFDerivAt_potSmul (e : ℝ) {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor} {x : Vec4}
    (hA : Differentiable ℝ A) (hΨ : DifferentiableAt ℝ Ψ x) (ν : Fin 4) :
    HasFDerivAt (fun y => (I * ((e * A y ν : ℝ) : ℂ)) • Ψ y)
      ((I * ((e * A x ν : ℝ) : ℂ)) • fderiv ℝ Ψ x +
        (I • Complex.ofRealCLM.comp (e • fderiv ℝ (fun y => A y ν) x)).smulRight (Ψ x)) x := by
  have hAν : DifferentiableAt ℝ (fun y => A y ν) x := differentiable_pi.1 hA ν x
  have h1 : HasFDerivAt (fun y => ((e * A y ν : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (e • fderiv ℝ (fun y => A y ν) x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hAν.hasFDerivAt.const_mul e)
  exact (h1.const_mul I).smul hΨ.hasFDerivAt

theorem differentiable_covD (e : ℝ) {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hA : Differentiable ℝ A) (hΨ : ContDiff ℝ 2 Ψ) (ν : Fin 4) :
    Differentiable ℝ (covD e A Ψ ν) := fun x =>
  ((differentiable_partialD hΨ ν x).hasFDerivAt.sub
    (hasFDerivAt_potSmul e hA (hΨ.differentiable (by norm_num) x) ν)).differentiableAt

theorem partialD_covD (e : ℝ) {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hA : Differentiable ℝ A) (hΨ : ContDiff ℝ 2 Ψ) (ν μ : Fin 4) (x : Vec4) :
    partialD (covD e A Ψ ν) μ x =
      fderiv ℝ (fderiv ℝ Ψ) x (Pi.single μ 1) (Pi.single ν 1) -
        (I * ((e * potD A ν μ x : ℝ) : ℂ)) • Ψ x -
          (I * ((e * A x ν : ℝ) : ℂ)) • partialD Ψ μ x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ Ψ) x :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have h1 : HasFDerivAt (fun y => partialD Ψ ν y)
      (fderiv ℝ (fun y => fderiv ℝ Ψ y (Pi.single ν 1)) x) x :=
    (differentiable_partialD hΨ ν x).hasFDerivAt
  have h2 := hasFDerivAt_potSmul e hA (hΨ.differentiable (by norm_num) x) ν
  have hcov : covD e A Ψ ν =
      fun y => partialD Ψ ν y - (I * ((e * A y ν : ℝ) : ℂ)) • Ψ y := rfl
  have hsecond : fderiv ℝ (fun y => fderiv ℝ Ψ y (Pi.single ν 1)) x (Pi.single μ 1) =
      fderiv ℝ (fderiv ℝ Ψ) x (Pi.single μ 1) (Pi.single ν 1) := by
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  have h3 : HasFDerivAt (fun y => partialD Ψ ν y - (I * ((e * A y ν : ℝ) : ℂ)) • Ψ y)
      (fderiv ℝ (fun y => fderiv ℝ Ψ y (Pi.single ν 1)) x -
        ((I * ((e * A x ν : ℝ) : ℂ)) • fderiv ℝ Ψ x +
          (I • Complex.ofRealCLM.comp (e • fderiv ℝ (fun y => A y ν) x)).smulRight (Ψ x))) x :=
    h1.sub h2
  conv_lhs => unfold partialD
  rw [hcov, h3.fderiv]
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, hsecond]
  unfold potD partialD
  push_cast
  module

/-- Covariant derivatives commute up to the field strength:
`[D_μ, D_ν] Ψ = -i e F_{μν} Ψ`. -/
theorem covD_comm (e : ℝ) {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hA : Differentiable ℝ A) (hΨ : ContDiff ℝ 2 Ψ) (μ ν : Fin 4) (x : Vec4) :
    covD e A (covD e A Ψ ν) μ x - covD e A (covD e A Ψ μ) ν x =
      (-(I * ((e * fieldStrength A x μ ν : ℝ) : ℂ))) • Ψ x := by
  have hsymm : IsSymmSndFDerivAt ℝ Ψ x :=
    hΨ.contDiffAt.isSymmSndFDerivAt (by simp)
  have hs := hsymm (Pi.single μ 1) (Pi.single ν 1)
  have e1 : ∀ α β : Fin 4, covD e A (covD e A Ψ β) α x =
      partialD (covD e A Ψ β) α x - (I * ((e * A x α : ℝ) : ℂ)) • covD e A Ψ β x :=
    fun _ _ => rfl
  rw [e1, e1, partialD_covD e hA hΨ, partialD_covD e hA hΨ, hs]
  unfold fieldStrength covD
  push_cast
  module

/-! ### The squared coupled operator -/

theorem covD_sum_mat (e : ℝ) (A : Vec4 → Vec4) (Mν : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    {f : Fin 4 → Vec4 → DiracSpinor} {x : Vec4} (hf : ∀ ν, DifferentiableAt ℝ (f ν) x)
    (μ : Fin 4) :
    covD e A (fun y => ∑ ν : Fin 4, applyDiracMat (Mν ν) (f ν y)) μ x =
      ∑ ν : Fin 4, applyDiracMat (Mν ν) (covD e A (f ν) μ x) := by
  have h : HasFDerivAt (fun y => ∑ ν : Fin 4, applyDiracMat (Mν ν) (f ν y))
      (∑ ν : Fin 4, (diracCLM (Mν ν)).comp (fderiv ℝ (f ν) x)) x :=
    HasFDerivAt.fun_sum fun ν _ => (diracCLM (Mν ν)).hasFDerivAt.comp x (hf ν).hasFDerivAt
  unfold covD partialD
  rw [h.fderiv]
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply, diracCLM_apply,
    applyDiracMat_sub, applyDiracMat_smul, Finset.smul_sum, Finset.sum_sub_distrib]

/-- `(γ^μ D_μ)² Ψ = Σ_{μν} γ^μ γ^ν D_μ D_ν Ψ`. -/
theorem gaugeDiracOp_sq (e : ℝ) {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hA : Differentiable ℝ A) (hΨ : ContDiff ℝ 2 Ψ) (x : Vec4) :
    gaugeDiracOp e A (gaugeDiracOp e A Ψ) x =
      ∑ μ : Fin 4, ∑ ν : Fin 4,
        applyDiracMat (diracMat μ * diracMat ν) (covD e A (covD e A Ψ ν) μ x) := by
  have hK : gaugeDiracOp e A Ψ =
      fun y => ∑ ν : Fin 4, applyDiracMat (diracMat ν) (covD e A Ψ ν y) := rfl
  have hcs : ∀ μ, covD e A (gaugeDiracOp e A Ψ) μ x =
      ∑ ν : Fin 4, applyDiracMat (diracMat ν) (covD e A (covD e A Ψ ν) μ x) := fun μ => by
    rw [hK]
    exact covD_sum_mat e A diracMat (f := fun ν => covD e A Ψ ν)
      (fun ν => differentiable_covD e hA hΨ ν x) μ
  conv_lhs => rw [gaugeDiracOp]
  simp only [hcs, applyDiracMat_finset_sum, applyDiracMat_mul]

/-- Clifford split of a double sum: the symmetric part is the Minkowski
contraction, the antisymmetric part is carried by the bivectors. -/
theorem clifford_double_sum (X : Fin 4 → Fin 4 → DiracSpinor) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, applyDiracMat (diracMat μ * diracMat ν) (X μ ν) =
      ∑ μ : Fin 4, (minkowskiEta μ μ : ℂ) • X μ μ +
        (1 / 2 : ℂ) • ∑ μ : Fin 4, ∑ ν : Fin 4,
          applyDiracMat (diracMat μ * diracMat ν) (X μ ν - X ν μ) := by
  set S := ∑ μ : Fin 4, ∑ ν : Fin 4, applyDiracMat (diracMat μ * diracMat ν) (X μ ν)
  have hswap : ∑ μ : Fin 4, ∑ ν : Fin 4, applyDiracMat (diracMat μ * diracMat ν) (X ν μ) =
      (2 : ℂ) • ∑ μ : Fin 4, (minkowskiEta μ μ : ℂ) • X μ μ - S := by
    rw [Finset.sum_comm]
    have hc : ∀ μ ν : Fin 4, diracMat ν * diracMat μ =
        (2 * minkowskiEta μ ν : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - diracMat μ * diracMat ν :=
      fun μ ν => by
        rw [eq_sub_iff_add_eq, add_comm]
        exact diracMat_clifford μ ν
    have hterm : ∀ μ ν : Fin 4, applyDiracMat (diracMat ν * diracMat μ) (X μ ν) =
        (2 * minkowskiEta μ ν : ℂ) • X μ ν - applyDiracMat (diracMat μ * diracMat ν) (X μ ν) :=
      fun μ ν => by
        rw [hc μ ν, applyDiracMat_sub_mat, applyDiracMat_smul_mat, applyDiracMat_one]
    simp only [hterm, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_eq_single μ]
    · rw [smul_smul]
    · intro ν _ hν
      rw [minkowskiEta_off (Ne.symm hν)]
      simp
    · simp
  simp only [applyDiracMat_sub, Finset.sum_sub_distrib]
  rw [hswap]
  module

/-- Field-strength matrix `Σ_{μν} F_{μν} γ^μ γ^ν`. -/
noncomputable def fieldMat (F : Fin 4 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, (F μ ν : ℂ) • (diracMat μ * diracMat ν)

/-- Second-order coupled equation operator:
`(γ^μ D_μ)² = η^{μμ} D_μ D_μ - (i e / 2) F_{μν} γ^μ γ^ν`. -/
theorem gaugeDiracOp_sq_eq (e : ℝ) {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hA : Differentiable ℝ A) (hΨ : ContDiff ℝ 2 Ψ) (x : Vec4) :
    gaugeDiracOp e A (gaugeDiracOp e A Ψ) x =
      ∑ μ : Fin 4, (minkowskiEta μ μ : ℂ) • covD e A (covD e A Ψ μ) μ x -
        (I * (e : ℂ) / 2) • applyDiracMat (fieldMat (fieldStrength A x)) (Ψ x) := by
  rw [gaugeDiracOp_sq e hA hΨ, clifford_double_sum]
  simp only [covD_comm e hA hΨ, applyDiracMat_smul]
  unfold fieldMat
  simp only [applyDiracMat_finset_sum_mat, applyDiracMat_smul_mat, Finset.smul_sum, smul_smul]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← neg_smul]
  congr 1
  push_cast
  ring

theorem gaugeDiracOp_smul (e : ℝ) (A : Vec4 → Vec4) {Ψ : Vec4 → DiracSpinor}
    (hΨ : Differentiable ℝ Ψ) (c : ℂ) (x : Vec4) :
    gaugeDiracOp e A (c • Ψ) x = c • gaugeDiracOp e A Ψ x := by
  rw [gaugeDiracOp_eq, gaugeDiracOp_eq, diracOp_smul hΨ, Pi.smul_apply, applyDiracMat_smul]
  module

/-- Every twice-differentiable solution in a differentiable potential obeys the
second-order equation `η^{μμ} D_μ D_μ Ψ - (i e/2) F_{μν} γ^μ γ^ν Ψ = m² Ψ`. -/
theorem diracGaugeField_second_order {m e : ℝ} {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hA : Differentiable ℝ A) (hΨ2 : ContDiff ℝ 2 Ψ) (hΨ : DiracGaugeField m e A Ψ)
    (x : Vec4) :
    ∑ μ : Fin 4, (minkowskiEta μ μ : ℂ) • covD e A (covD e A Ψ μ) μ x -
        (I * (e : ℂ) / 2) • applyDiracMat (fieldMat (fieldStrength A x)) (Ψ x) =
      ((m : ℂ) ^ 2) • Ψ x := by
  rw [← gaugeDiracOp_sq_eq e hA hΨ2]
  have hK : gaugeDiracOp e A Ψ = (-(m : ℂ)) • Ψ := funext hΨ.2
  rw [hK, gaugeDiracOp_smul e A hΨ.1, hΨ.2, smul_smul]
  congr 1
  ring

/-! ### Weyl blocks of the field strength -/

/-- Magnetic field `B = (F₂₃, F₃₁, F₁₂)`. -/
def magVec (F : Fin 4 → Fin 4 → ℝ) : Fin 3 → ℝ
  | 0 => F 2 3
  | 1 => F 3 1
  | 2 => F 1 2

/-- Electric field `E_k = F_{k0}`. -/
def elecVec (F : Fin 4 → Fin 4 → ℝ) : Fin 3 → ℝ
  | 0 => F 1 0
  | 1 => F 2 0
  | 2 => F 3 0

/-- Upper Weyl block of a bivector `γ^μ γ^ν`. -/
theorem diracUpper_gamma_pair (μ ν : Fin 4) (Ψ : DiracSpinor) :
    diracUpper (applyDiracMat (diracMat μ * diracMat ν) Ψ) =
      applyMat (pauliSlash (Pi.single μ 1) * pauliSlashBar (Pi.single ν 1)) (diracUpper Ψ) := by
  rw [applyDiracMat_mul, ← slashMat_single μ, ← slashMat_single ν, diracUpper_slash,
    diracLower_slash, applyMat_mul]

/-- Lower Weyl block of a bivector `γ^μ γ^ν`. -/
theorem diracLower_gamma_pair (μ ν : Fin 4) (Ψ : DiracSpinor) :
    diracLower (applyDiracMat (diracMat μ * diracMat ν) Ψ) =
      applyMat (pauliSlashBar (Pi.single μ 1) * pauliSlash (Pi.single ν 1)) (diracLower Ψ) := by
  rw [applyDiracMat_mul, ← slashMat_single μ, ← slashMat_single ν, diracLower_slash,
    diracUpper_slash, applyMat_mul]

/-- Upper-block matrix of the field strength. -/
noncomputable def fieldUpper (F : Fin 4 → Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    (F μ ν : ℂ) • (pauliSlash (Pi.single μ 1) * pauliSlashBar (Pi.single ν 1))

/-- Lower-block matrix of the field strength. -/
noncomputable def fieldLower (F : Fin 4 → Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    (F μ ν : ℂ) • (pauliSlashBar (Pi.single μ 1) * pauliSlash (Pi.single ν 1))

theorem diracUpper_fieldMat (F : Fin 4 → Fin 4 → ℝ) (Ψ : DiracSpinor) :
    diracUpper (applyDiracMat (fieldMat F) Ψ) = applyMat (fieldUpper F) (diracUpper Ψ) := by
  unfold fieldMat fieldUpper
  simp only [applyDiracMat_finset_sum_mat, applyDiracMat_smul_mat, diracUpper_finset_sum,
    diracUpper_smul, diracUpper_gamma_pair, applyMat_finset_sum_mat, applyMat_smul_mat]

theorem diracLower_fieldMat (F : Fin 4 → Fin 4 → ℝ) (Ψ : DiracSpinor) :
    diracLower (applyDiracMat (fieldMat F) Ψ) = applyMat (fieldLower F) (diracLower Ψ) := by
  unfold fieldMat fieldLower
  simp only [applyDiracMat_finset_sum_mat, applyDiracMat_smul_mat, diracLower_finset_sum,
    diracLower_smul, diracLower_gamma_pair, applyMat_finset_sum_mat, applyMat_smul_mat]

/-- Upper block: `-(i e/2) F_{μν} s_μ s̄_ν = e (σ·B + i σ·E)`. -/
theorem fieldUpper_eq (F : Fin 4 → Fin 4 → ℝ) (hF : ∀ μ ν, F μ ν = -F ν μ) (e : ℝ) :
    (-(I * (e : ℂ) / 2)) • fieldUpper F =
      (e : ℂ) • (pauliComb (magVec F) + I • pauliComb (elecVec F)) := by
  have d : ∀ μ, F μ μ = 0 := fun μ => by linarith [hF μ μ]
  have h01 := hF 0 1
  have h02 := hF 0 2
  have h03 := hF 0 3
  have h13 := hF 1 3
  have h21 := hF 2 1
  have h32 := hF 3 2
  unfold fieldUpper
  simp only [Fin.sum_univ_four, pauliSlash_single_zero, pauliSlash_single_one,
    pauliSlash_single_two, pauliSlash_single_three, pauliSlashBar_single_zero,
    pauliSlashBar_single_one, pauliSlashBar_single_two, pauliSlashBar_single_three, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_neg, pauliX_sq, pauliY_sq, pauliZ_sq,
    pauliX_mul_pauliY, pauliY_mul_pauliX, pauliY_mul_pauliZ, pauliZ_mul_pauliY,
    pauliZ_mul_pauliX, pauliX_mul_pauliZ, d, h01, h02, h03, h13, h21, h32]
  simp only [magVec, elecVec, pauliComb, pauli, Fin.sum_univ_three]
  push_cast
  match_scalars <;> (try ring_nf) <;> (try simp only [I_sq]) <;> (try ring)

/-- Lower block: `-(i e/2) F_{μν} s̄_μ s_ν = e (σ·B - i σ·E)`. -/
theorem fieldLower_eq (F : Fin 4 → Fin 4 → ℝ) (hF : ∀ μ ν, F μ ν = -F ν μ) (e : ℝ) :
    (-(I * (e : ℂ) / 2)) • fieldLower F =
      (e : ℂ) • (pauliComb (magVec F) - I • pauliComb (elecVec F)) := by
  have d : ∀ μ, F μ μ = 0 := fun μ => by linarith [hF μ μ]
  have h01 := hF 0 1
  have h02 := hF 0 2
  have h03 := hF 0 3
  have h13 := hF 1 3
  have h21 := hF 2 1
  have h32 := hF 3 2
  unfold fieldLower
  simp only [Fin.sum_univ_four, pauliSlash_single_zero, pauliSlash_single_one,
    pauliSlash_single_two, pauliSlash_single_three, pauliSlashBar_single_zero,
    pauliSlashBar_single_one, pauliSlashBar_single_two, pauliSlashBar_single_three, Matrix.one_mul,
    Matrix.mul_one, Matrix.neg_mul, pauliX_sq, pauliY_sq, pauliZ_sq,
    pauliX_mul_pauliY, pauliY_mul_pauliX, pauliY_mul_pauliZ, pauliZ_mul_pauliY,
    pauliZ_mul_pauliX, pauliX_mul_pauliZ, d, h01, h02, h03, h13, h21, h32]
  simp only [magVec, elecVec, pauliComb, pauli, Fin.sum_univ_three]
  push_cast
  match_scalars <;> (try ring_nf) <;> (try simp only [I_sq]) <;> (try ring)

/-- Upper Weyl block of the second-order equation: the magnetic field couples
through `e σ·B`, the electric field through `i e σ·E`. -/
theorem diracGaugeField_pauli_upper {m e : ℝ} {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hA : Differentiable ℝ A) (hΨ2 : ContDiff ℝ 2 Ψ) (hΨ : DiracGaugeField m e A Ψ)
    (x : Vec4) :
    diracUpper (∑ μ : Fin 4, (minkowskiEta μ μ : ℂ) • covD e A (covD e A Ψ μ) μ x) +
        applyMat ((e : ℂ) • (pauliComb (magVec (fieldStrength A x)) +
          I • pauliComb (elecVec (fieldStrength A x)))) (diracUpper (Ψ x)) =
      ((m : ℂ) ^ 2) • diracUpper (Ψ x) := by
  have h := congrArg diracUpper (diracGaugeField_second_order hA hΨ2 hΨ x)
  rw [diracUpper_sub, diracUpper_smul, diracUpper_smul, diracUpper_fieldMat] at h
  rw [← fieldUpper_eq _ (fieldStrength_antisymm A x), applyMat_smul_mat, ← h]
  module

/-- Lower Weyl block of the second-order equation: the same magnetic matrix
`e σ·B`, the opposite electric term `-i e σ·E`. -/
theorem diracGaugeField_pauli_lower {m e : ℝ} {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hA : Differentiable ℝ A) (hΨ2 : ContDiff ℝ 2 Ψ) (hΨ : DiracGaugeField m e A Ψ)
    (x : Vec4) :
    diracLower (∑ μ : Fin 4, (minkowskiEta μ μ : ℂ) • covD e A (covD e A Ψ μ) μ x) +
        applyMat ((e : ℂ) • (pauliComb (magVec (fieldStrength A x)) -
          I • pauliComb (elecVec (fieldStrength A x)))) (diracLower (Ψ x)) =
      ((m : ℂ) ^ 2) • diracLower (Ψ x) := by
  have h := congrArg diracLower (diracGaugeField_second_order hA hΨ2 hΨ x)
  rw [diracLower_sub, diracLower_smul, diracLower_smul, diracLower_fieldMat] at h
  rw [← fieldLower_eq _ (fieldStrength_antisymm A x), applyMat_smul_mat, ← h]
  module

theorem covD_charge_zero (A : Vec4 → Vec4) (Ψ : Vec4 → DiracSpinor) (μ : Fin 4) :
    covD 0 A Ψ μ = fun y => partialD Ψ μ y := by
  funext y
  simp [covD]

/-- Klein–Gordon: every component of a twice-differentiable free solution obeys
`η^{μμ} ∂_μ ∂_μ Ψ = m² Ψ`. -/
theorem diracField_kleinGordon {m : ℝ} {Ψ : Vec4 → DiracSpinor} (hΨ2 : ContDiff ℝ 2 Ψ)
    (hΨ : DiracField m Ψ) (x : Vec4) :
    ∑ μ : Fin 4, (minkowskiEta μ μ : ℂ) • partialD (fun y => partialD Ψ μ y) μ x =
      ((m : ℂ) ^ 2) • Ψ x := by
  have hg : DiracGaugeField m 0 0 Ψ := (diracGaugeField_zero m 0 Ψ).2 hΨ
  have h := diracGaugeField_second_order (differentiable_const 0) hΨ2 hg x
  simp only [covD_charge_zero, ofReal_zero, mul_zero, zero_div, zero_smul, sub_zero] at h
  exact h

/-! ### Spin precession as a dual rotor -/

section Precession

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `t ↦ U(t ω) u` solves `i u' = ½ (ω·σ) u`: a spin Hamiltonian linear in
the Pauli matrices generates a dual rotor whose rapidity grows linearly. -/
theorem hasDerivAt_dualRotor_ray (ω : DualRapidity) (u : DualSpinor) (t : ℝ) :
    HasDerivAt (fun s : ℝ => applyMat (dualRotorMat (s • ω)) u)
      ((-(I / 2)) • applyMat (pauliComb (fun a => ω a)) (applyMat (dualRotorMat (t • ω)) u))
      t := by
  have hexp : ∀ s : ℝ, dualRotorMat (s • ω) = NormedSpace.exp (s • dualRotorGen ω) := by
    intro s
    rw [dualRotorMat_eq_exp_gen, dualRotorGen_smul]
  let L : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] DualSpinor :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => applyMat X u
        map_add' := fun X Y => applyMat_add_mat X Y u
        map_smul' := fun r X => by
          simp only [RingHom.id_apply]
          rw [← Complex.coe_smul, applyMat_smul_mat, Complex.coe_smul] }
  have h := L.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (dualRotorGen ω) t)
  simp only [Function.comp_def] at h
  have hf : (fun s : ℝ => applyMat (dualRotorMat (s • ω)) u) =
      fun s => L (NormedSpace.exp (s • dualRotorGen ω)) := by
    funext s
    rw [hexp]
    rfl
  rw [hf]
  have hv : L (dualRotorGen ω * NormedSpace.exp (t • dualRotorGen ω)) =
      (-(I / 2)) • applyMat (pauliComb (fun a => ω a)) (applyMat (dualRotorMat (t • ω)) u) := by
    change applyMat (dualRotorGen ω * NormedSpace.exp (t • dualRotorGen ω)) u = _
    rw [applyMat_mul, ← hexp, dualRotorGen_eq_pauliComb, applyMat_smul_mat]
  exact h.congr_deriv hv

end Precession

end Logic

end DstDiophantine
