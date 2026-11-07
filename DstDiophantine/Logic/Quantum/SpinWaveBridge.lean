import DstDiophantine.Logic.Quantum.ExternalChart

/-!
# What joins the internal spin to the chart wave

A chart phase multiplies the identity. The magnetic spin Hamiltonian is
traceless, so the two never agree. The join is the field strength of the
wave. On a twice differentiable carrier the spatial kinetic momenta
`Π_a = -i D_a` satisfy `(σ·Π)² = Π² - e σ·B`. The orbital square is the
wave; the remainder is one dual generator on both Weyl blocks. For `m ≠ 0`
that remainder divided by `2m` is the dual rotor of rapidity rate
`-(e/m) B`, whose angular speed is `|e| ‖B‖ / |m|`. The electric part
changes sign between the blocks, and the blocks agree exactly when the
charge or the electric field vanishes.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

open scoped InnerProductSpace

/-! ### Pauli combinations -/

theorem pauliComb_smul (c : ℝ) (n : Fin 3 → ℝ) :
    pauliComb (fun a => c * n a) = (c : ℂ) • pauliComb n := by
  unfold pauliComb
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

theorem pauliComb_zero : pauliComb (0 : Fin 3 → ℝ) = 0 := by
  simp [pauliComb]

private theorem pauliComb_00 (n : Fin 3 → ℝ) : pauliComb n 0 0 = (n 2 : ℂ) := by
  simp [pauliComb, pauli, Fin.sum_univ_three, pauliX, pauliY, pauliZ]

private theorem pauliComb_01 (n : Fin 3 → ℝ) :
    pauliComb n 0 1 = (n 0 : ℂ) - I * (n 1 : ℂ) := by
  simp [pauliComb, pauli, Fin.sum_univ_three, pauliX, pauliY, pauliZ]
  ring

private theorem pauliComb_10 (n : Fin 3 → ℝ) :
    pauliComb n 1 0 = (n 0 : ℂ) + I * (n 1 : ℂ) := by
  simp [pauliComb, pauli, Fin.sum_univ_three, pauliX, pauliY, pauliZ]
  ring

theorem pauliComb_eq_zero_iff (n : Fin 3 → ℝ) : pauliComb n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have h00 : pauliComb n 0 0 = 0 := by rw [h]; rfl
    have h01 : pauliComb n 0 1 = 0 := by rw [h]; rfl
    have h10 : pauliComb n 1 0 = 0 := by rw [h]; rfl
    rw [pauliComb_00] at h00
    rw [pauliComb_01] at h01
    rw [pauliComb_10] at h10
    have hn2 : n 2 = 0 := by
      have := congrArg Complex.re h00
      simpa using this
    have hre : n 0 = 0 := by
      have := congrArg Complex.re h01
      simpa using this
    have him : n 1 = 0 := by
      have := congrArg Complex.im h10
      simpa using this
    ext a
    fin_cases a <;> assumption
  · rintro rfl
    exact pauliComb_zero

private theorem smul_mat_eq_zero {c : ℂ} {M : Matrix (Fin 2) (Fin 2) ℂ} :
    c • M = 0 ↔ c = 0 ∨ M = 0 := by
  constructor
  · intro h
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      ext i j
      have hij : c * M i j = 0 := by simpa [Matrix.smul_apply] using congrFun (congrFun h i) j
      exact (mul_eq_zero.mp hij).resolve_left hc
  · rintro (hc | hM)
    · simp [hc]
    · simp [hM]

/-- The two Weyl blocks of the field strength agree exactly when the charge
vanishes or the electric field does. The shared matrix is then the magnetic
dual generator. -/
theorem fieldBlocks_eq_iff (e : ℝ) (B E : Fin 3 → ℝ) :
    (e : ℂ) • (pauliComb B + I • pauliComb E) =
        (e : ℂ) • (pauliComb B - I • pauliComb E) ↔
      e = 0 ∨ E = 0 := by
  constructor
  · intro h
    have hsub := congrArg (fun M => M - (e : ℂ) • (pauliComb B - I • pauliComb E)) h
    simp only [sub_self] at hsub
    have htwice : (e : ℂ) • (pauliComb B + I • pauliComb E) -
        (e : ℂ) • (pauliComb B - I • pauliComb E) =
        ((e : ℂ) * 2 * I) • pauliComb E := by
      module
    rw [htwice] at hsub
    rcases smul_mat_eq_zero.mp hsub with hc | hE
    · left
      have hI : (2 : ℂ) * I ≠ 0 := by simp
      have : (e : ℂ) = 0 := by
        have hmul : (e : ℂ) * ((2 : ℂ) * I) = 0 := by
          simpa [mul_assoc] using hc
        exact (mul_eq_zero.mp hmul).resolve_right hI
      exact_mod_cast this
    · right
      exact (pauliComb_eq_zero_iff E).mp hE
  · rintro (he | hE)
    · subst he
      simp
    · subst hE
      simp [pauliComb_zero]

/-! ### The carrier, lifted to the upper Weyl block -/

/-- Pauli index `0,1,2` as the spatial chart axis `x,y,z`. -/
def pauliAxis : Fin 3 → Fin 4
  | 0 => 1
  | 1 => 2
  | 2 => 3

noncomputable def weylUpperCLM : DualSpinor →L[ℝ] DiracSpinor :=
  LinearMap.toContinuousLinearMap
    { toFun := weylUpper
      map_add' := weylUpper_add
      map_smul' := fun r ψ => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, weylUpper_smul, Complex.coe_smul] }

theorem weylUpperCLM_apply (ψ : DualSpinor) : weylUpperCLM ψ = weylUpper ψ := rfl

noncomputable def diracUpperCLM : DiracSpinor →L[ℝ] DualSpinor :=
  LinearMap.toContinuousLinearMap
    { toFun := diracUpper
      map_add' := diracUpper_add
      map_smul' := fun r Ψ => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, diracUpper_smul, Complex.coe_smul] }

theorem diracUpperCLM_apply (Ψ : DiracSpinor) : diracUpperCLM Ψ = diracUpper Ψ := rfl

noncomputable def applyMatCLM (M : Matrix (Fin 2) (Fin 2) ℂ) : DualSpinor →L[ℝ] DualSpinor :=
  LinearMap.toContinuousLinearMap
    { toFun := applyMat M
      map_add' := applyMat_add M
      map_smul' := fun r ψ => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, applyMat_smul, Complex.coe_smul] }

theorem applyMatCLM_apply (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor) :
    applyMatCLM M ψ = applyMat M ψ := rfl

/-- Constant complex scaling as a real-linear map. -/
noncomputable def spinorSmulCLM (c : ℂ) : DualSpinor →L[ℝ] DualSpinor :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ => c • ψ
      map_add' := fun ψ φ => smul_add c ψ φ
      map_smul' := fun r ψ => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul r ψ, smul_smul, mul_comm, ← smul_smul, Complex.coe_smul] }

theorem spinorSmulCLM_apply (c : ℂ) (ψ : DualSpinor) : spinorSmulCLM c ψ = c • ψ := rfl

noncomputable def diracSmulCLM (c : ℂ) : DiracSpinor →L[ℝ] DiracSpinor :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Ψ => c • Ψ
      map_add' := fun Ψ Φ => smul_add c Ψ Φ
      map_smul' := fun r Ψ => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul r Ψ, smul_smul, mul_comm, ← smul_smul, Complex.coe_smul] }

theorem diracSmulCLM_apply (c : ℂ) (Ψ : DiracSpinor) : diracSmulCLM c Ψ = c • Ψ := rfl

/-- Upper-block lift of a dual-spinor field. -/
noncomputable def carrierField (φ : Vec4 → DualSpinor) : Vec4 → DiracSpinor :=
  fun x => weylUpper (φ x)

theorem contDiff_carrierField {n : WithTop ℕ∞} {φ : Vec4 → DualSpinor} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (carrierField φ) := by
  have hcomp : carrierField φ = weylUpperCLM ∘ φ := by
    funext x
    rfl
  rw [hcomp]
  exact weylUpperCLM.contDiff.comp hφ

theorem partialD_carrier {φ : Vec4 → DualSpinor} {x : Vec4} (hφ : DifferentiableAt ℝ φ x)
    (μ : Fin 4) :
    partialD (carrierField φ) μ x = weylUpper (fderiv ℝ φ x (Pi.single μ 1)) := by
  have h : HasFDerivAt (carrierField φ) (weylUpperCLM.comp (fderiv ℝ φ x)) x :=
    weylUpperCLM.hasFDerivAt.comp x hφ.hasFDerivAt
  unfold partialD
  rw [h.fderiv]
  rfl

theorem diracUpper_partialD_carrier {φ : Vec4 → DualSpinor} {x : Vec4}
    (hφ : DifferentiableAt ℝ φ x) (μ : Fin 4) :
    diracUpper (partialD (carrierField φ) μ x) = fderiv ℝ φ x (Pi.single μ 1) := by
  rw [partialD_carrier hφ, diracUpper_weylUpper]

theorem diracLower_covD_carrier (e : ℝ) (A : Vec4 → Vec4) {φ : Vec4 → DualSpinor} {x : Vec4}
    (hφ : DifferentiableAt ℝ φ x) (μ : Fin 4) :
    diracLower (covD e A (carrierField φ) μ x) = 0 := by
  conv_lhs => unfold covD
  rw [diracLower_sub, diracLower_smul, partialD_carrier hφ, diracLower_weylUpper]
  simp [carrierField, diracLower_weylUpper]

theorem covD_carrier_upper (e : ℝ) (A : Vec4 → Vec4) {φ : Vec4 → DualSpinor} {x : Vec4}
    (hφ : DifferentiableAt ℝ φ x) (μ : Fin 4) :
    covD e A (carrierField φ) μ x =
      weylUpper (diracUpper (covD e A (carrierField φ) μ x)) := by
  have hdec := weyl_decompose (covD e A (carrierField φ) μ x)
  rw [diracLower_covD_carrier e A hφ μ, weylLower_zero, add_zero] at hdec
  exact hdec.symm

theorem diracUpper_covD_carrier (e : ℝ) (A : Vec4 → Vec4) {φ : Vec4 → DualSpinor} {x : Vec4}
    (hφ : DifferentiableAt ℝ φ x) (μ : Fin 4) :
    diracUpper (covD e A (carrierField φ) μ x) =
      fderiv ℝ φ x (Pi.single μ 1) - (I * ((e * A x μ : ℝ) : ℂ)) • φ x := by
  conv_lhs => unfold covD
  rw [diracUpper_sub, diracUpper_smul, diracUpper_partialD_carrier hφ]
  simp [carrierField, diracUpper_weylUpper]

theorem covD_const_smul (e : ℝ) (A : Vec4 → Vec4) {Ψ : Vec4 → DiracSpinor}
    (hΨ : Differentiable ℝ Ψ) (c : ℂ) (μ : Fin 4) (x : Vec4) :
    covD e A (fun y => c • Ψ y) μ x = c • covD e A Ψ μ x := by
  have hfun : (fun y => c • Ψ y) = diracSmulCLM c ∘ Ψ := by
    funext y
    rfl
  unfold covD partialD
  rw [hfun]
  have h := (diracSmulCLM c).hasFDerivAt.comp x (hΨ x).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply, diracSmulCLM_apply, smul_sub]
  congr 1
  rw [smul_smul, smul_smul, mul_comm]

/-! ### Kinetic momentum on the carrier -/

/-- Spatial kinetic momentum `Π_a φ = -i D_a φ` on the upper block. -/
noncomputable def kinPi (e : ℝ) (A : Vec4 → Vec4) (φ : Vec4 → DualSpinor) (a : Fin 3)
    (x : Vec4) : DualSpinor :=
  (-I) • diracUpper (covD e A (carrierField φ) (pauliAxis a) x)

theorem differentiable_kinPi (e : ℝ) {A : Vec4 → Vec4} {φ : Vec4 → DualSpinor}
    (hA : Differentiable ℝ A) (hφ : ContDiff ℝ 2 φ) (a : Fin 3) :
    Differentiable ℝ (fun y => kinPi e A φ a y) := by
  have hD := differentiable_covD e hA (contDiff_carrierField hφ) (pauliAxis a)
  change Differentiable ℝ fun y =>
    spinorSmulCLM (-I) (diracUpperCLM (covD e A (carrierField φ) (pauliAxis a) y))
  exact ((spinorSmulCLM (-I)).comp diracUpperCLM).differentiable.comp hD

private theorem applyMat_sub (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ φ : DualSpinor) :
    applyMat M (ψ - φ) = applyMat M ψ - applyMat M φ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, applyMat_add, ← neg_one_smul (R := ℂ) φ, applyMat_smul]
  module

theorem kinPi_applyMat (e : ℝ) (A : Vec4 → Vec4) (M : Matrix (Fin 2) (Fin 2) ℂ)
    {φ : Vec4 → DualSpinor} (hφ : Differentiable ℝ φ) (a : Fin 3) (x : Vec4) :
    kinPi e A (fun y => applyMat M (φ y)) a x = applyMat M (kinPi e A φ a x) := by
  unfold kinPi
  have hAt : DifferentiableAt ℝ (fun y => applyMat M (φ y)) x :=
    ((applyMatCLM M).differentiableAt).comp x (hφ x)
  rw [diracUpper_covD_carrier e A hAt, diracUpper_covD_carrier e A (hφ x)]
  have hfun : (fun y => applyMat M (φ y)) = applyMatCLM M ∘ φ := by
    funext y
    rfl
  rw [hfun]
  have h := (applyMatCLM M).hasFDerivAt.comp x (hφ x).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, applyMatCLM_apply, applyMat_sub, applyMat_smul]

theorem kinPi_add (e : ℝ) (A : Vec4 → Vec4) {φ ψ : Vec4 → DualSpinor}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (a : Fin 3) (x : Vec4) :
    kinPi e A (φ + ψ) a x = kinPi e A φ a x + kinPi e A ψ a x := by
  unfold kinPi
  have hAt : DifferentiableAt ℝ (φ + ψ) x := (hφ x).add (hψ x)
  rw [diracUpper_covD_carrier e A hAt, diracUpper_covD_carrier e A (hφ x),
    diracUpper_covD_carrier e A (hψ x), fderiv_add (hφ x) (hψ x)]
  have hv :
      (fderiv ℝ φ x + fderiv ℝ ψ x) (Pi.single (pauliAxis a) 1) =
        fderiv ℝ φ x (Pi.single (pauliAxis a) 1) +
          fderiv ℝ ψ x (Pi.single (pauliAxis a) 1) :=
    _root_.add_apply _ _ _
  rw [hv, Pi.add_apply, smul_sub, smul_sub, smul_sub, smul_add, smul_add, smul_add]
  abel

private theorem differentiable_dualSum {ι : Type*} (s : Finset ι) (f : ι → Vec4 → DualSpinor)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) :
    Differentiable ℝ (fun y => ∑ i ∈ s, f i y) := by
  induction s using Finset.cons_induction with
  | empty =>
    exact differentiable_const (0 : DualSpinor)
  | cons i s hi ih =>
    have hfun : (fun y => ∑ k ∈ Finset.cons i s hi, f k y) =
        f i + fun y => ∑ k ∈ s, f k y := by
      funext y
      rw [Finset.sum_cons, Pi.add_apply]
    rw [hfun]
    exact (hf i (Finset.mem_cons_self i s)).add
      (ih fun k hk => hf k (Finset.mem_cons_of_mem hk))

theorem kinPi_finset_sum (e : ℝ) (A : Vec4 → Vec4) {ι : Type*} (s : Finset ι)
    (f : ι → Vec4 → DualSpinor) (hf : ∀ i ∈ s, Differentiable ℝ (f i))
    (a : Fin 3) (x : Vec4) :
    kinPi e A (fun y => ∑ i ∈ s, f i y) a x = ∑ i ∈ s, kinPi e A (f i) a x := by
  induction s using Finset.cons_induction with
  | empty =>
    unfold kinPi
    simp only [Finset.sum_empty]
    rw [diracUpper_covD_carrier e A (differentiableAt_const (0 : DualSpinor))]
    simp
  | cons i s hi ih =>
    have hfi : Differentiable ℝ (f i) := hf i (Finset.mem_cons_self i s)
    have hrest : ∀ k ∈ s, Differentiable ℝ (f k) := fun k hk =>
      hf k (Finset.mem_cons_of_mem hk)
    have hfun : (fun y => ∑ k ∈ Finset.cons i s hi, f k y) =
        f i + fun y => ∑ k ∈ s, f k y := by
      funext y
      rw [Finset.sum_cons, Pi.add_apply]
    rw [hfun, kinPi_add e A hfi (differentiable_dualSum s f hrest), ih hrest, Finset.sum_cons]

/-- `σ·Π` on the carrier. -/
noncomputable def sigmaPi (e : ℝ) (A : Vec4 → Vec4) (φ : Vec4 → DualSpinor) (x : Vec4) :
    DualSpinor :=
  ∑ a : Fin 3, applyMat (pauli a) (kinPi e A φ a x)

/-- `(σ·Π)²`, the kinetic spin-momentum applied twice. -/
noncomputable def sigmaPiSq (e : ℝ) (A : Vec4 → Vec4) (φ : Vec4 → DualSpinor) (x : Vec4) :
    DualSpinor :=
  sigmaPi e A (fun y => sigmaPi e A φ y) x

/-- `Π_b Π_a` on the carrier. -/
noncomputable def piComp (e : ℝ) (A : Vec4 → Vec4) (φ : Vec4 → DualSpinor) (b a : Fin 3)
    (x : Vec4) : DualSpinor :=
  kinPi e A (fun y => kinPi e A φ a y) b x

/-- Orbital square `Π² = Σ_a Π_a²`. -/
noncomputable def kinSq (e : ℝ) (A : Vec4 → Vec4) (φ : Vec4 → DualSpinor) (x : Vec4) :
    DualSpinor :=
  ∑ a : Fin 3, piComp e A φ a a x

theorem differentiable_sigmaPi (e : ℝ) {A : Vec4 → Vec4} {φ : Vec4 → DualSpinor}
    (hA : Differentiable ℝ A) (hφ : ContDiff ℝ 2 φ) :
    Differentiable ℝ (fun y => sigmaPi e A φ y) := by
  unfold sigmaPi
  exact differentiable_dualSum Finset.univ
    (fun a y => applyMat (pauli a) (kinPi e A φ a y))
    fun a _ => (applyMatCLM (pauli a)).differentiable.comp (differentiable_kinPi e hA hφ a)

private theorem piComp_as_cov (e : ℝ) {A : Vec4 → Vec4} {φ : Vec4 → DualSpinor}
    (hA : Differentiable ℝ A) (hφ : ContDiff ℝ 2 φ) (b a : Fin 3) (x : Vec4) :
    piComp e A φ b a x =
      ((-I) * (-I)) • diracUpper
        (covD e A (covD e A (carrierField φ) (pauliAxis a)) (pauliAxis b) x) := by
  have hpure : carrierField (fun z => kinPi e A φ a z) =
      fun y => (-I) • covD e A (carrierField φ) (pauliAxis a) y := by
    funext y
    change weylUpper (kinPi e A φ a y) = _
    unfold kinPi
    rw [weylUpper_smul]
    exact congrArg ((-I) • ·)
      (covD_carrier_upper e A (hφ.differentiable (by norm_num) y) (pauliAxis a)).symm
  have hdiff : Differentiable ℝ (covD e A (carrierField φ) (pauliAxis a)) :=
    differentiable_covD e hA (contDiff_carrierField hφ) (pauliAxis a)
  unfold piComp
  change (-I) • diracUpper
      (covD e A (carrierField (fun y => kinPi e A φ a y)) (pauliAxis b) x) = _
  rw [hpure, covD_const_smul e A hdiff (-I), diracUpper_smul, smul_smul]

theorem piComp_sub (e : ℝ) {A : Vec4 → Vec4} {φ : Vec4 → DualSpinor}
    (hA : Differentiable ℝ A) (hφ : ContDiff ℝ 2 φ) (b a : Fin 3) (x : Vec4) :
    piComp e A φ b a x - piComp e A φ a b x =
      (I * ((e * fieldStrength A x (pauliAxis b) (pauliAxis a) : ℝ) : ℂ)) • φ x := by
  rw [piComp_as_cov e hA hφ b a x, piComp_as_cov e hA hφ a b x]
  have hI : (-I) * (-I) = (-1 : ℂ) := by simp [I_mul_I]
  rw [hI, neg_one_smul, neg_one_smul]
  have hcomm := covD_comm e hA (contDiff_carrierField hφ) (pauliAxis b) (pauliAxis a) x
  have hΔ : diracUpper (covD e A (covD e A (carrierField φ) (pauliAxis a)) (pauliAxis b) x) -
      diracUpper (covD e A (covD e A (carrierField φ) (pauliAxis b)) (pauliAxis a) x) =
      diracUpper ((-(I * ((e * fieldStrength A x (pauliAxis b) (pauliAxis a) : ℝ) : ℂ))) •
        carrierField φ x) := by
    rw [← diracUpper_sub, hcomm, diracUpper_smul]
  rw [show -diracUpper (covD e A (covD e A (carrierField φ) (pauliAxis a)) (pauliAxis b) x) -
      -diracUpper (covD e A (covD e A (carrierField φ) (pauliAxis b)) (pauliAxis a) x) =
      -(diracUpper (covD e A (covD e A (carrierField φ) (pauliAxis a)) (pauliAxis b) x) -
        diracUpper (covD e A (covD e A (carrierField φ) (pauliAxis b)) (pauliAxis a) x)) by
    module]
  rw [hΔ, diracUpper_smul, carrierField, diracUpper_weylUpper]
  module

private theorem applyMat_sum {ι : Type*} (s : Finset ι) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (f : ι → DualSpinor) :
    applyMat M (∑ i ∈ s, f i) = ∑ i ∈ s, applyMat M (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp [applyMat]
  | cons i s _ ih =>
    rw [Finset.sum_cons, Finset.sum_cons, applyMat_add, ih]

private theorem sigmaPiSq_expand (e : ℝ) {A : Vec4 → Vec4} {φ : Vec4 → DualSpinor}
    (hA : Differentiable ℝ A) (hφ : ContDiff ℝ 2 φ) (x : Vec4) :
    sigmaPiSq e A φ x =
      ∑ b : Fin 3, ∑ a : Fin 3,
        applyMat (pauli b * pauli a) (piComp e A φ b a x) := by
  have hkin : ∀ a, Differentiable ℝ (fun y => kinPi e A φ a y) :=
    fun a => differentiable_kinPi e hA hφ a
  unfold sigmaPiSq sigmaPi
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [kinPi_finset_sum e A Finset.univ (fun a y => applyMat (pauli a) (kinPi e A φ a y))
    (fun a _ => (applyMatCLM (pauli a)).differentiable.comp (hkin a))]
  rw [applyMat_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [kinPi_applyMat e A (pauli a) (hkin a), applyMat_mul]
  rfl

private theorem pauli_pair_comm (e c : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q φ : DualSpinor)
    (hpq : p - q = (I * ((e * c : ℝ) : ℂ)) • φ) :
    applyMat (I • σ) p + applyMat ((-I) • σ) q =
      applyMat (((-(e * c) : ℝ) : ℂ) • σ) φ := by
  have hp : p = (I * ((e * c : ℝ) : ℂ)) • φ + q := by
    calc
      p = p - q + q := by abel
      _ = (I * ((e * c : ℝ) : ℂ)) • φ + q := by rw [hpq]
  rw [hp, applyMat_smul_mat, applyMat_smul_mat, applyMat_smul_mat, applyMat_add, applyMat_smul,
    smul_add, smul_smul, ← mul_assoc, I_mul_I]
  have hcancel : (I : ℂ) • applyMat σ q + (-I) • applyMat σ q = 0 := by
    rw [← add_smul]
    ring_nf
    simp
  rw [add_assoc, hcancel, add_zero]
  congr 1
  push_cast
  ring

private theorem neg_e_pauli (e c : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℂ) (φ : DualSpinor) :
    applyMat (((-(e * c) : ℝ) : ℂ) • σ) φ =
      applyMat ((-(e : ℂ)) • ((c : ℂ) • σ)) φ := by
  congr 1
  push_cast
  module

/-- On a twice differentiable carrier, `(σ·Π)² = Π² - e σ·B`. -/
theorem sigmaPi_sq_split (e : ℝ) {A : Vec4 → Vec4} {φ : Vec4 → DualSpinor}
    (hA : Differentiable ℝ A) (hφ : ContDiff ℝ 2 φ) (x : Vec4) :
    sigmaPiSq e A φ x =
      kinSq e A φ x +
        applyMat ((-(e : ℂ)) • pauliComb (magVec (fieldStrength A x))) (φ x) := by
  rw [sigmaPiSq_expand e hA hφ x]
  simp only [Fin.sum_univ_three]
  set F := fieldStrength A x
  set p := fun b a => piComp e A φ b a x
  have hxy := piComp_sub e hA hφ 0 1 x
  have hyz := piComp_sub e hA hφ 1 2 x
  have hzx := piComp_sub e hA hφ 2 0 x
  have hpair01 := pauli_pair_comm e (F 1 2) pauliZ (p 0 1) (p 1 0) (φ x) (by
    simpa [p, pauliAxis, magVec] using hxy)
  have hpair12 := pauli_pair_comm e (F 2 3) pauliX (p 1 2) (p 2 1) (φ x) (by
    simpa [p, pauliAxis] using hyz)
  have hpair20 := pauli_pair_comm e (F 3 1) pauliY (p 2 0) (p 0 2) (φ x) (by
    simpa [p, pauliAxis] using hzx)
  have hdiag : applyMat (pauli 0 * pauli 0) (p 0 0) + applyMat (pauli 1 * pauli 1) (p 1 1) +
      applyMat (pauli 2 * pauli 2) (p 2 2) = kinSq e A φ x := by
    simp only [pauli_sq, applyMat_one, kinSq, Fin.sum_univ_three, p]
  have hcross : applyMat (pauli 0 * pauli 1) (p 0 1) + applyMat (pauli 1 * pauli 0) (p 1 0) +
      (applyMat (pauli 1 * pauli 2) (p 1 2) + applyMat (pauli 2 * pauli 1) (p 2 1)) +
      (applyMat (pauli 2 * pauli 0) (p 2 0) + applyMat (pauli 0 * pauli 2) (p 0 2)) =
      applyMat ((-(e : ℂ)) • pauliComb (magVec F)) (φ x) := by
    rw [show pauli 0 * pauli 1 = I • pauliZ by simp [pauli, pauliX_mul_pauliY],
      show pauli 1 * pauli 0 = (-I) • pauliZ by simp [pauli, pauliY_mul_pauliX],
      show pauli 1 * pauli 2 = I • pauliX by simp [pauli, pauliY_mul_pauliZ],
      show pauli 2 * pauli 1 = (-I) • pauliX by simp [pauli, pauliZ_mul_pauliY],
      show pauli 2 * pauli 0 = I • pauliY by simp [pauli, pauliZ_mul_pauliX],
      show pauli 0 * pauli 2 = (-I) • pauliY by simp [pauli, pauliX_mul_pauliZ]]
    rw [hpair01, hpair12, hpair20]
    rw [neg_e_pauli e (F 1 2) pauliZ (φ x), neg_e_pauli e (F 2 3) pauliX (φ x),
      neg_e_pauli e (F 3 1) pauliY (φ x)]
    have hB : (-(e : ℂ)) • ((F 1 2 : ℂ) • pauliZ) +
        (-(e : ℂ)) • ((F 2 3 : ℂ) • pauliX) +
        (-(e : ℂ)) • ((F 3 1 : ℂ) • pauliY) =
        (-(e : ℂ)) • pauliComb (magVec F) := by
      simp only [pauliComb, pauli, magVec, Fin.sum_univ_three]
      module
    rw [← applyMat_add_mat, ← applyMat_add_mat]
    exact congrArg (fun M => applyMat M (φ x)) hB
  -- nine terms, regrouped into the diagonal and the three pairs
  have hgroup :
      (applyMat (pauli 0 * pauli 0) (p 0 0) + applyMat (pauli 0 * pauli 1) (p 0 1) +
          applyMat (pauli 0 * pauli 2) (p 0 2)) +
        (applyMat (pauli 1 * pauli 0) (p 1 0) + applyMat (pauli 1 * pauli 1) (p 1 1) +
          applyMat (pauli 1 * pauli 2) (p 1 2)) +
        (applyMat (pauli 2 * pauli 0) (p 2 0) + applyMat (pauli 2 * pauli 1) (p 2 1) +
          applyMat (pauli 2 * pauli 2) (p 2 2)) =
      (applyMat (pauli 0 * pauli 0) (p 0 0) + applyMat (pauli 1 * pauli 1) (p 1 1) +
          applyMat (pauli 2 * pauli 2) (p 2 2)) +
        (applyMat (pauli 0 * pauli 1) (p 0 1) + applyMat (pauli 1 * pauli 0) (p 1 0) +
          (applyMat (pauli 1 * pauli 2) (p 1 2) + applyMat (pauli 2 * pauli 1) (p 2 1)) +
          (applyMat (pauli 2 * pauli 0) (p 2 0) + applyMat (pauli 0 * pauli 2) (p 0 2))) := by
    abel
  rw [hgroup, hdiag, hcross]

/-! ### The magnetic piece is a dual rotor, never a chart phase -/

/-- Rapidity rate `ω = -(e/m) B`. -/
noncomputable def magneticRapidity (e m : ℝ) (B : DualRapidity) : DualRapidity :=
  (-(e / m)) • B

theorem spinCurve_magnetic (e m : ℝ) (B : DualRapidity) (u : DualSpinor) (hm : m ≠ 0)
    (t : ℝ) :
    I • deriv (spinCurve (magneticRapidity e m B) u) t =
      applyMat (((-(e / (2 * m)) : ℝ) : ℂ) • pauliComb (fun a => B a))
        (spinCurve (magneticRapidity e m B) u t) := by
  rw [spinCurve_schrodinger, magneticRapidity]
  have hω : (fun a => ((-(e / m)) • B) a) = fun a => (-(e / m)) * (B a) := by
    funext a
    simp
  have hscal : (1 / 2 : ℝ) * (-(e / m)) = -(e / (2 * m)) := by
    field_simp [hm]
  rw [hω, pauliComb_smul]
  conv_lhs => rw [applyMat_smul_mat, smul_smul]
  conv_rhs => rw [applyMat_smul_mat]
  congr 1
  calc
    (1 / 2 : ℂ) * Complex.ofReal (-(e / m)) =
        Complex.ofReal (1 / 2) * Complex.ofReal (-(e / m)) := by
      congr 1
      norm_num
    _ = Complex.ofReal ((1 / 2) * -(e / m)) := by
      rw [← Complex.ofReal_mul]
    _ = Complex.ofReal (-(e / (2 * m))) := by
      rw [hscal]

theorem magnetic_rapidity_norm (e m : ℝ) (B : DualRapidity) (hm : m ≠ 0) :
    ‖magneticRapidity e m B‖ = |e| * ‖B‖ / |m| := by
  unfold magneticRapidity
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_div]
  have hm0 : |m| ≠ 0 := abs_ne_zero.mpr hm
  field_simp [hm0]

/-- For `m ≠ 0` the magnetic spin Hamiltonian is never a chart phase. -/
theorem magneticSpin_ne_phaseGate (e m : ℝ) (B : Fin 3 → ℝ) (α : ℝ) (_hm : m ≠ 0) :
    ((-(e / (2 * m)) : ℝ) : ℂ) • pauliComb B ≠ phaseGate α := by
  intro h
  have hleft : (((( -(e / (2 * m)) : ℝ) : ℂ) • pauliComb B).trace) = 0 := by
    rw [Matrix.trace_smul, pauliComb_trace, smul_zero]
  have hright : (phaseGate α).trace = 2 * exp (I * (α : ℂ)) := by
    unfold phaseGate
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    norm_num
    ring
  have hexp : exp (I * (α : ℂ)) ≠ 0 := exp_ne_zero _
  have hne : (2 : ℂ) * exp (I * (α : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hexp
  rw [h, hright] at hleft
  exact hne hleft

end Logic

end DstDiophantine
