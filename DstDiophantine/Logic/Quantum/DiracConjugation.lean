import DstDiophantine.Logic.Quantum.DiracGauge

/-!
# Charge conjugation, the dual map, and the antiparticle

The quaternionic structure of the dual spinor is `J u = ε ū` with `ε = iσ_y`.
It is antilinear, `J² = -1`, `J u ⊥ u`, and `J (M u) = (adj M)† J u` for every
`2 × 2` matrix `M`. In particular `J` commutes with every dual rotor and
reverses `σ·n` along every axis.

Charge conjugation on `ℂ⁴` is `Ψᶜ = (-J l, J u)` for `Ψ = (u, l)`. It is an
antilinear involution that commutes with every `γ^μ` and every total rotor.
It carries a solution at `p` to a solution at `-p`, and a solution of charge
`e` in a potential `A` to a solution of charge `-e` in the same potential.
It preserves the density and the current of one spinor and reverses the mass
bilinear.

The pseudoscalar `e₀e₁e₂e₃` of the dual map `X ↦ X i` acts on `ℂ⁴` as
`ω = γ⁰γ¹γ²γ³ = iγ⁵`. It squares to `-1`, anticommutes with every `γ^μ`, and
commutes with every total rotor, so it carries a solution at `p` to a solution
of the same mass at `-p`. It preserves the current and reverses the mass
bilinear. On spacetime `x ↦ ω Ψ(-x)` solves the equation in the reflected
potential `-A(-x)`.

The antiparticle `ω Ψᶜ` is a solution at the same momentum `p`, with the same
mass bilinear, current, and density. The field `x ↦ ω Ψᶜ(-x)` solves the
equation of charge `-e` in the reflected potential and carries a plane wave of
momentum `p` to a plane wave of momentum `p`. At rest the antiparticle of
`(u, iu)` is `-(J u, i J u)`.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

open scoped InnerProductSpace

/-! ### Quaternionic structure of the dual spinor -/

/-- `J u = ε ū` with `ε = iσ_y = !![0, 1; -1, 0]`. -/
noncomputable def quatJ (u : DualSpinor) : DualSpinor :=
  WithLp.toLp 2 ![star (u 1), -star (u 0)]

@[simp] theorem quatJ_apply_zero (u : DualSpinor) : quatJ u 0 = star (u 1) := rfl

@[simp] theorem quatJ_apply_one (u : DualSpinor) : quatJ u 1 = -star (u 0) := rfl

theorem quatJ_add (u v : DualSpinor) : quatJ (u + v) = quatJ u + quatJ v := by
  ext i; fin_cases i <;> (simp [quatJ]; try ring)

theorem quatJ_smul (c : ℂ) (u : DualSpinor) : quatJ (c • u) = star c • quatJ u := by
  ext i; fin_cases i <;> simp [quatJ]

theorem quatJ_neg (u : DualSpinor) : quatJ (-u) = -quatJ u := by
  ext i; fin_cases i <;> simp [quatJ]

theorem quatJ_sub (u v : DualSpinor) : quatJ (u - v) = quatJ u - quatJ v := by
  ext i; fin_cases i <;> (simp [quatJ]; try ring)

theorem quatJ_zero : quatJ 0 = 0 := by
  ext i; fin_cases i <;> simp [quatJ]

/-- `J² = -1`. -/
theorem quatJ_quatJ (u : DualSpinor) : quatJ (quatJ u) = -u := by
  ext i; fin_cases i <;> simp [quatJ]

theorem inner_quatJ_quatJ (u v : DualSpinor) :
    inner ℂ (quatJ u) (quatJ v) = inner ℂ v u := by
  simp only [dualSpinor_inner_eq, Fin.sum_univ_two, quatJ_apply_zero, quatJ_apply_one,
    star_star, star_neg]
  ring

/-- `J u` is orthogonal to `u`. -/
theorem inner_self_quatJ (u : DualSpinor) : inner ℂ u (quatJ u) = 0 := by
  simp only [dualSpinor_inner_eq, Fin.sum_univ_two, quatJ_apply_zero, quatJ_apply_one]
  ring

theorem norm_quatJ (u : DualSpinor) : ‖quatJ u‖ = ‖u‖ := by
  have h := inner_quatJ_quatJ u u
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖quatJ u‖ ^ 2 = ‖u‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (quatJ u), norm_nonneg u, sq_nonneg (‖quatJ u‖ - ‖u‖),
    sq_nonneg (‖quatJ u‖ + ‖u‖)]

/-- `J (M u) = (adj M)† J u` for every `2 × 2` matrix. -/
theorem quatJ_applyMat (M : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) :
    quatJ (applyMat M u) = applyMat (rotorLower M) (quatJ u) := by
  ext i
  fin_cases i <;>
    (simp [quatJ, applyMat_apply, rotorLower, Matrix.adjugate_fin_two, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]; try ring)

theorem rotorLower_rotorLower (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rotorLower (rotorLower M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotorLower, Matrix.adjugate_fin_two, Matrix.conjTranspose_apply]

theorem quatJ_applyMat_rotorLower (M : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) :
    quatJ (applyMat (rotorLower M) u) = applyMat M (quatJ u) := by
  rw [quatJ_applyMat, rotorLower_rotorLower]

/-- `J` commutes with every dual rotor. -/
theorem quatJ_dualRotor (β : DualRapidity) (u : DualSpinor) :
    quatJ (applyMat (dualRotorMat β) u) = applyMat (dualRotorMat β) (quatJ u) := by
  rw [quatJ_applyMat, rotorLower_dualRotor]

/-- `J` reverses the spin along every axis: `J (σ·n u) = -σ·n (J u)`. -/
theorem quatJ_pauliComb (n : Fin 3 → ℝ) (u : DualSpinor) :
    quatJ (applyMat (pauliComb n) u) = -applyMat (pauliComb n) (quatJ u) := by
  ext i
  fin_cases i <;>
    (simp [quatJ, applyMat_apply, pauliComb, pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_two,
      Fin.sum_univ_three]; try ring)

theorem quatJ_pauliSlash (p : Vec4) (u : DualSpinor) :
    quatJ (applyMat (pauliSlash p) u) = -applyMat (pauliSlashBar p) (quatJ u) := by
  ext i
  fin_cases i <;>
    simp [quatJ, applyMat_apply, pauliSlash, pauliSlashBar, pauliX, pauliY, pauliZ,
      Fin.sum_univ_two] <;> ring

theorem quatJ_pauliSlashBar (p : Vec4) (u : DualSpinor) :
    quatJ (applyMat (pauliSlashBar p) u) = -applyMat (pauliSlash p) (quatJ u) := by
  ext i
  fin_cases i <;>
    simp [quatJ, applyMat_apply, pauliSlash, pauliSlashBar, pauliX, pauliY, pauliZ,
      Fin.sum_univ_two] <;> ring

@[simp] theorem applyMat_neg_right (M : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) :
    applyMat M (-u) = -applyMat M u := by
  simpa using applyMat_smul (-1) M u

theorem applyDiracMat_neg_right (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat M (-Ψ) = -applyDiracMat M Ψ := by
  simpa using applyDiracMat_smul (-1) M Ψ

@[simp] theorem diracUpper_neg (Ψ : DiracSpinor) : diracUpper (-Ψ) = -diracUpper Ψ := by
  simpa using diracUpper_smul (-1) Ψ

@[simp] theorem diracLower_neg (Ψ : DiracSpinor) : diracLower (-Ψ) = -diracLower Ψ := by
  simpa using diracLower_smul (-1) Ψ

/-- A Dirac spinor is determined by its two Weyl blocks. -/
theorem dirac_ext_weyl {Ψ Φ : DiracSpinor} (hu : diracUpper Ψ = diracUpper Φ)
    (hl : diracLower Ψ = diracLower Φ) : Ψ = Φ := by
  rw [← weyl_decompose Ψ, ← weyl_decompose Φ, hu, hl]

/-! ### Charge conjugation on `ℂ⁴` -/

/-- Charge conjugation `(u, l) ↦ (-J l, J u)`. -/
noncomputable def chargeConj (Ψ : DiracSpinor) : DiracSpinor :=
  weylUpper (-quatJ (diracLower Ψ)) + weylLower (quatJ (diracUpper Ψ))

@[simp] theorem diracUpper_chargeConj (Ψ : DiracSpinor) :
    diracUpper (chargeConj Ψ) = -quatJ (diracLower Ψ) := by
  rw [chargeConj, diracUpper_add, diracUpper_weylUpper, diracUpper_weylLower, add_zero]

@[simp] theorem diracLower_chargeConj (Ψ : DiracSpinor) :
    diracLower (chargeConj Ψ) = quatJ (diracUpper Ψ) := by
  rw [chargeConj, diracLower_add, diracLower_weylUpper, diracLower_weylLower, zero_add]

theorem chargeConj_weyl (u l : DualSpinor) :
    chargeConj (weylUpper u + weylLower l) = weylUpper (-quatJ l) + weylLower (quatJ u) := by
  rw [chargeConj, diracUpper_add, diracLower_add, diracUpper_weylUpper, diracUpper_weylLower,
    diracLower_weylUpper, diracLower_weylLower, add_zero, zero_add]

/-- Charge conjugation is an involution. -/
theorem chargeConj_chargeConj (Ψ : DiracSpinor) : chargeConj (chargeConj Ψ) = Ψ := by
  apply dirac_ext_weyl
  · simp [quatJ_quatJ]
  · simp [quatJ_neg, quatJ_quatJ]

theorem chargeConj_add (Ψ Φ : DiracSpinor) :
    chargeConj (Ψ + Φ) = chargeConj Ψ + chargeConj Φ := by
  apply dirac_ext_weyl
  · simp [diracUpper_add, diracLower_add, quatJ_add, add_comm]
  · simp [diracUpper_add, diracLower_add, quatJ_add]

theorem chargeConj_sub (Ψ Φ : DiracSpinor) :
    chargeConj (Ψ - Φ) = chargeConj Ψ - chargeConj Φ := by
  apply dirac_ext_weyl
  · simp [diracUpper_sub, diracLower_sub, quatJ_sub]
    abel
  · simp [diracUpper_sub, diracLower_sub, quatJ_sub]

/-- Charge conjugation is antilinear. -/
theorem chargeConj_smul (c : ℂ) (Ψ : DiracSpinor) :
    chargeConj (c • Ψ) = star c • chargeConj Ψ := by
  apply dirac_ext_weyl
  · simp [diracUpper_smul, diracLower_smul, quatJ_smul]
  · simp [diracUpper_smul, diracLower_smul, quatJ_smul]

theorem chargeConj_neg (Ψ : DiracSpinor) : chargeConj (-Ψ) = -chargeConj Ψ := by
  simpa using chargeConj_smul (-1) Ψ

theorem chargeConj_zero : chargeConj 0 = 0 := by
  simpa using chargeConj_smul 0 0

theorem chargeConj_finset_sum {ι : Type*} (s : Finset ι) (f : ι → DiracSpinor) :
    chargeConj (∑ i ∈ s, f i) = ∑ i ∈ s, chargeConj (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [chargeConj_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, chargeConj_add, ih]

theorem chargeConj_injective : Function.Injective chargeConj := fun Ψ Φ h => by
  rw [← chargeConj_chargeConj Ψ, h, chargeConj_chargeConj]

/-- Charge conjugation commutes with the slash of every real four-vector. -/
theorem slash_chargeConj (p : Vec4) (Ψ : DiracSpinor) :
    applyDiracMat (slashMat p) (chargeConj Ψ) = chargeConj (applyDiracMat (slashMat p) Ψ) := by
  apply dirac_ext_weyl
  · simp [diracUpper_slash, diracLower_slash, quatJ_pauliSlashBar]
  · simp [diracUpper_slash, diracLower_slash, quatJ_pauliSlash]

/-- Charge conjugation commutes with every `γ^μ`. -/
theorem diracMat_chargeConj (μ : Fin 4) (Ψ : DiracSpinor) :
    applyDiracMat (diracMat μ) (chargeConj Ψ) = chargeConj (applyDiracMat (diracMat μ) Ψ) := by
  rw [← slashMat_single, slash_chargeConj]

theorem slashMat_neg (p : Vec4) : slashMat (-p) = -slashMat p := by
  simp [slashMat, Finset.sum_neg_distrib, neg_smul]

/-- The charge conjugate of a solution at `p` is a solution of the same mass at `-p`. -/
theorem diracMomentum_chargeConj {m : ℝ} {p : Vec4} {Ψ : DiracSpinor}
    (h : DiracMomentum m p Ψ) : DiracMomentum m (-p) (chargeConj Ψ) := by
  unfold DiracMomentum at h ⊢
  rw [slashMat_neg, applyDiracMat_neg, slash_chargeConj, h, chargeConj_smul]
  simp only [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal, ← neg_smul]
  ring_nf

/-- Charge conjugation is a bijection between solutions at `p` and at `-p`. -/
theorem diracMomentum_chargeConj_iff {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} :
    DiracMomentum m (-p) (chargeConj Ψ) ↔ DiracMomentum m p Ψ := by
  refine ⟨fun h => ?_, diracMomentum_chargeConj⟩
  have h2 := diracMomentum_chargeConj h
  rwa [neg_neg, chargeConj_chargeConj] at h2

/-- Charge conjugation commutes with every total rotor. -/
theorem chargeConj_rotorDirac (M : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : DiracSpinor) :
    chargeConj (rotorDirac M Ψ) = rotorDirac M (chargeConj Ψ) := by
  apply dirac_ext_weyl
  · simp [rotorDirac, diracUpper_add, diracLower_add, diracUpper_weylUpper,
      diracUpper_weylLower, diracLower_weylUpper, diracLower_weylLower,
      quatJ_applyMat_rotorLower]
  · simp [rotorDirac, diracUpper_add, diracLower_add, diracUpper_weylUpper,
      diracUpper_weylLower, diracLower_weylUpper, diracLower_weylLower, quatJ_applyMat]

theorem inner_chargeConj (Ψ Φ : DiracSpinor) :
    inner ℂ (chargeConj Ψ) (chargeConj Φ) = inner ℂ Φ Ψ := by
  rw [← weyl_decompose Ψ, ← weyl_decompose Φ, chargeConj_weyl, chargeConj_weyl]
  simp only [inner_add_left, inner_add_right, weylUpper_inner_upper, weylUpper_inner_lower,
    weylLower_inner_upper, weylLower_inner_lower, inner_neg_left, inner_neg_right,
    inner_quatJ_quatJ]
  ring

/-- Charge conjugation preserves the density `Ψ†Ψ`. -/
theorem norm_chargeConj (Ψ : DiracSpinor) : ‖chargeConj Ψ‖ = ‖Ψ‖ := by
  have h := inner_chargeConj Ψ Ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖chargeConj Ψ‖ ^ 2 = ‖Ψ‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (chargeConj Ψ), norm_nonneg Ψ, sq_nonneg (‖chargeConj Ψ‖ - ‖Ψ‖),
    sq_nonneg (‖chargeConj Ψ‖ + ‖Ψ‖)]

/-- Charge conjugation reverses the mass bilinear. -/
theorem diracScalar_chargeConj (Ψ Φ : DiracSpinor) :
    diracScalar (chargeConj Ψ) (chargeConj Φ) = -diracScalar Φ Ψ := by
  rw [← weyl_decompose Ψ, ← weyl_decompose Φ, chargeConj_weyl, chargeConj_weyl,
    diracScalar_weyl, diracScalar_weyl]
  simp only [inner_neg_left, inner_neg_right, inner_quatJ_quatJ]
  ring

theorem diracScalar_gamma_swap (μ : Fin 4) (Ψ Φ : DiracSpinor) :
    diracScalar (applyDiracMat (diracMat μ) Ψ) Φ =
      -diracScalar Ψ (applyDiracMat (diracMat μ) Φ) := by
  unfold diracScalar
  have h : inner ℂ Ψ (applyDiracMat diracAdjointMat (applyDiracMat (diracMat μ) Φ)) =
      -inner ℂ (applyDiracMat (diracMat μ) Ψ) (applyDiracMat diracAdjointMat Φ) := by
    rw [← applyDiracMat_mul, applyDiracMat_inner_ct, diracAdjointMat_mul_gamma_antiHermitian,
      applyDiracMat_neg, inner_neg_left, applyDiracMat_mul, inner_diracAdjoint_left]
  rw [h, neg_neg]

/-- The current of two charge conjugates is the current with the arguments
exchanged; for one spinor it is unchanged. -/
theorem diracCurrent_chargeConj (μ : Fin 4) (Ψ Φ : DiracSpinor) :
    diracCurrent μ (chargeConj Ψ) (chargeConj Φ) = diracCurrent μ Φ Ψ := by
  rw [diracCurrent_eq_scalar, diracCurrent_eq_scalar, diracMat_chargeConj,
    diracScalar_chargeConj, diracScalar_gamma_swap, neg_neg]

theorem realCurrent_chargeConj (Ψ : DiracSpinor) : realCurrent (chargeConj Ψ) = realCurrent Ψ := by
  funext μ
  simp only [realCurrent, diracCurrent_chargeConj]

/-! ### The pseudoscalar of the dual map on `ℂ⁴` -/

/-- Image `γ⁰γ¹γ²γ³` of the pseudoscalar `e₀e₁e₂e₃` of the dual map `X ↦ X i`. -/
def dualPseudoMat : Matrix (Fin 4) (Fin 4) ℂ :=
  diracMat0 * diracMat1 * diracMat2 * diracMat3

theorem dualPseudoMat_eq : dualPseudoMat = I • diracMat5 := by
  unfold diracMat5 dualPseudoMat
  rw [smul_smul]
  simp

/-- The dual map on a Dirac spinor. -/
noncomputable def dualFlip (Ψ : DiracSpinor) : DiracSpinor :=
  applyDiracMat dualPseudoMat Ψ

/-- `ω` is `+i` on the upper Weyl block and `-i` on the lower. -/
theorem dualFlip_weyl (u l : DualSpinor) :
    dualFlip (weylUpper u + weylLower l) = weylUpper (I • u) + weylLower (-I • l) := by
  rw [dualFlip, dualPseudoMat_eq, applyDiracMat_smul_mat, applyDiracMat_add,
    applyDiracMat5_weylUpper, applyDiracMat5_weylLower, smul_add, weylUpper_smul,
    weylLower_smul, neg_smul, smul_neg]

@[simp] theorem diracUpper_dualFlip (Ψ : DiracSpinor) :
    diracUpper (dualFlip Ψ) = I • diracUpper Ψ := by
  conv_lhs => rw [← weyl_decompose Ψ, dualFlip_weyl]
  rw [diracUpper_add, diracUpper_weylUpper, diracUpper_weylLower, add_zero]

@[simp] theorem diracLower_dualFlip (Ψ : DiracSpinor) :
    diracLower (dualFlip Ψ) = -I • diracLower Ψ := by
  conv_lhs => rw [← weyl_decompose Ψ, dualFlip_weyl]
  rw [diracLower_add, diracLower_weylUpper, diracLower_weylLower, zero_add]

/-- `ω² = -1`. -/
theorem dualFlip_dualFlip (Ψ : DiracSpinor) : dualFlip (dualFlip Ψ) = -Ψ := by
  apply dirac_ext_weyl
  · simp [smul_smul]
  · simp [smul_smul]

theorem dualFlip_add (Ψ Φ : DiracSpinor) : dualFlip (Ψ + Φ) = dualFlip Ψ + dualFlip Φ :=
  applyDiracMat_add _ _ _

theorem dualFlip_sub (Ψ Φ : DiracSpinor) : dualFlip (Ψ - Φ) = dualFlip Ψ - dualFlip Φ :=
  applyDiracMat_sub _ _ _

theorem dualFlip_smul (c : ℂ) (Ψ : DiracSpinor) : dualFlip (c • Ψ) = c • dualFlip Ψ :=
  applyDiracMat_smul _ _ _

theorem dualFlip_finset_sum {ι : Type*} (s : Finset ι) (f : ι → DiracSpinor) :
    dualFlip (∑ i ∈ s, f i) = ∑ i ∈ s, dualFlip (f i) :=
  applyDiracMat_finset_sum _ _ _

/-- `ω` anticommutes with the slash of every four-vector. -/
theorem slash_dualFlip (p : Vec4) (Ψ : DiracSpinor) :
    applyDiracMat (slashMat p) (dualFlip Ψ) = -dualFlip (applyDiracMat (slashMat p) Ψ) := by
  apply dirac_ext_weyl
  · simp [diracUpper_slash, applyMat_smul]
  · simp [diracLower_slash, applyMat_smul]

theorem diracMat_dualFlip (μ : Fin 4) (Ψ : DiracSpinor) :
    applyDiracMat (diracMat μ) (dualFlip Ψ) = -dualFlip (applyDiracMat (diracMat μ) Ψ) := by
  rw [← slashMat_single, slash_dualFlip]

/-- The dual map reverses the four-momentum: a solution at `p` goes to a
solution of the same mass at `-p`. -/
theorem diracMomentum_dualFlip {m : ℝ} {p : Vec4} {Ψ : DiracSpinor}
    (h : DiracMomentum m p Ψ) : DiracMomentum m (-p) (dualFlip Ψ) := by
  unfold DiracMomentum at h ⊢
  rw [slashMat_neg, applyDiracMat_neg, slash_dualFlip, neg_neg, h, dualFlip_smul]

/-- `ω` commutes with every total rotor. -/
theorem dualFlip_rotorDirac (M : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : DiracSpinor) :
    dualFlip (rotorDirac M Ψ) = rotorDirac M (dualFlip Ψ) := by
  apply dirac_ext_weyl
  · simp [rotorDirac, diracUpper_add, diracUpper_weylUpper, diracUpper_weylLower, applyMat_smul]
  · simp [rotorDirac, diracLower_add, diracLower_weylUpper, diracLower_weylLower, applyMat_smul]

theorem inner_dualFlip (Ψ Φ : DiracSpinor) :
    inner ℂ (dualFlip Ψ) (dualFlip Φ) = inner ℂ Ψ Φ := by
  rw [← weyl_decompose Ψ, ← weyl_decompose Φ, dualFlip_weyl, dualFlip_weyl]
  simp only [inner_add_left, inner_add_right, weylUpper_inner_upper, weylUpper_inner_lower,
    weylLower_inner_upper, weylLower_inner_lower, inner_smul_left, inner_smul_right,
    Complex.conj_I, map_neg]
  ring_nf
  simp only [I_sq]
  ring

/-- The dual map preserves the density `Ψ†Ψ`. -/
theorem norm_dualFlip (Ψ : DiracSpinor) : ‖dualFlip Ψ‖ = ‖Ψ‖ := by
  have h := inner_dualFlip Ψ Ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖dualFlip Ψ‖ ^ 2 = ‖Ψ‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (dualFlip Ψ), norm_nonneg Ψ, sq_nonneg (‖dualFlip Ψ‖ - ‖Ψ‖),
    sq_nonneg (‖dualFlip Ψ‖ + ‖Ψ‖)]

/-- The dual map reverses the mass bilinear. -/
theorem diracScalar_dualFlip (Ψ Φ : DiracSpinor) :
    diracScalar (dualFlip Ψ) (dualFlip Φ) = -diracScalar Ψ Φ := by
  rw [← weyl_decompose Ψ, ← weyl_decompose Φ, dualFlip_weyl, dualFlip_weyl,
    diracScalar_weyl, diracScalar_weyl]
  simp only [inner_smul_left, inner_smul_right, Complex.conj_I, map_neg]
  ring_nf
  simp only [I_pow_three]
  ring

private theorem diracScalar_neg_right (Ψ Φ : DiracSpinor) :
    diracScalar Ψ (-Φ) = -diracScalar Ψ Φ := by
  unfold diracScalar
  rw [applyDiracMat_neg_right, inner_neg_right]

/-- The dual map preserves the current. -/
theorem diracCurrent_dualFlip (μ : Fin 4) (Ψ Φ : DiracSpinor) :
    diracCurrent μ (dualFlip Ψ) (dualFlip Φ) = diracCurrent μ Ψ Φ := by
  rw [diracCurrent_eq_scalar, diracCurrent_eq_scalar, diracMat_dualFlip, diracScalar_neg_right,
    diracScalar_dualFlip, neg_neg]

/-- At rest the dual map carries the particle pair `(u, iu)` to `i (u, -iu)`. -/
theorem dualFlip_restParticle (u : DualSpinor) :
    dualFlip (restParticleSpinor u) = I • restAntiparticleSpinor u := by
  rw [restParticleSpinor, dualFlip_weyl, restAntiparticleSpinor, smul_add, ← weylUpper_smul,
    ← weylLower_smul, smul_smul, smul_smul]
  congr 2
  simp

/-! ### The antiparticle -/

/-- Antiparticle `ω Ψᶜ`: charge conjugation followed by the dual map. -/
noncomputable def antiparticle (Ψ : DiracSpinor) : DiracSpinor :=
  dualFlip (chargeConj Ψ)

/-- The antiparticle of a solution at `p` is a solution at the same `p`. -/
theorem diracMomentum_antiparticle {m : ℝ} {p : Vec4} {Ψ : DiracSpinor}
    (h : DiracMomentum m p Ψ) : DiracMomentum m p (antiparticle Ψ) := by
  have h2 := diracMomentum_dualFlip (diracMomentum_chargeConj h)
  rwa [neg_neg] at h2

theorem antiparticle_rotorDirac (M : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : DiracSpinor) :
    antiparticle (rotorDirac M Ψ) = rotorDirac M (antiparticle Ψ) := by
  rw [antiparticle, antiparticle, chargeConj_rotorDirac, dualFlip_rotorDirac]

theorem norm_antiparticle (Ψ : DiracSpinor) : ‖antiparticle Ψ‖ = ‖Ψ‖ := by
  rw [antiparticle, norm_dualFlip, norm_chargeConj]

theorem diracScalar_antiparticle (Ψ Φ : DiracSpinor) :
    diracScalar (antiparticle Ψ) (antiparticle Φ) = diracScalar Φ Ψ := by
  rw [antiparticle, antiparticle, diracScalar_dualFlip, diracScalar_chargeConj, neg_neg]

theorem diracCurrent_antiparticle (μ : Fin 4) (Ψ Φ : DiracSpinor) :
    diracCurrent μ (antiparticle Ψ) (antiparticle Φ) = diracCurrent μ Φ Ψ := by
  rw [antiparticle, antiparticle, diracCurrent_dualFlip, diracCurrent_chargeConj]

theorem realCurrent_antiparticle (Ψ : DiracSpinor) :
    realCurrent (antiparticle Ψ) = realCurrent Ψ := by
  funext μ
  simp only [realCurrent, diracCurrent_antiparticle]

/-- At rest the antiparticle of `(u, iu)` is `-(J u, i J u)`: a particle pair
whose dual spinor is `J u`. -/
theorem antiparticle_restParticle (u : DualSpinor) :
    antiparticle (restParticleSpinor u) = -restParticleSpinor (quatJ u) := by
  apply dirac_ext_weyl
  · simp [antiparticle, restParticleSpinor, diracUpper_add, diracLower_add,
      diracUpper_weylUpper, diracUpper_weylLower, diracLower_weylUpper, diracLower_weylLower,
      quatJ_smul, smul_smul]
  · simp [antiparticle, restParticleSpinor, diracUpper_add, diracLower_add,
      diracUpper_weylUpper, diracUpper_weylLower, diracLower_weylUpper, diracLower_weylLower]

/-! ### Charge conjugation of a field -/

/-- Charge conjugation as a real continuous linear map. -/
noncomputable def chargeConjCLM : DiracSpinor →L[ℝ] DiracSpinor :=
  LinearMap.toContinuousLinearMap
    { toFun := chargeConj
      map_add' := chargeConj_add
      map_smul' := fun r Ψ => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, chargeConj_smul, Complex.star_def, Complex.conj_ofReal,
          Complex.coe_smul] }

theorem chargeConjCLM_apply (Ψ : DiracSpinor) : chargeConjCLM Ψ = chargeConj Ψ := rfl

/-- Charge-conjugate field `x ↦ Ψᶜ(x)`. -/
noncomputable def conjField (Ψ : Vec4 → DiracSpinor) : Vec4 → DiracSpinor :=
  fun x => chargeConj (Ψ x)

theorem partialD_conjField {Ψ : Vec4 → DiracSpinor} {x : Vec4} (hΨ : DifferentiableAt ℝ Ψ x)
    (μ : Fin 4) : partialD (conjField Ψ) μ x = chargeConj (partialD Ψ μ x) := by
  have h : HasFDerivAt (conjField Ψ) (chargeConjCLM.comp (fderiv ℝ Ψ x)) x :=
    chargeConjCLM.hasFDerivAt.comp x hΨ.hasFDerivAt
  unfold partialD
  rw [h.fderiv]
  rfl

theorem covD_conjField (e : ℝ) (A : Vec4 → Vec4) {Ψ : Vec4 → DiracSpinor} {x : Vec4}
    (hΨ : DifferentiableAt ℝ Ψ x) (μ : Fin 4) :
    covD (-e) A (conjField Ψ) μ x = chargeConj (covD e A Ψ μ x) := by
  rw [covD, covD, partialD_conjField hΨ, chargeConj_sub, chargeConj_smul, conjField]
  congr 2
  simp only [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The charge conjugate of a solution of charge `e` in a potential `A` is a
solution of charge `-e` in the same potential. -/
theorem diracGaugeField_conjField {m e : ℝ} {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hΨ : DiracGaugeField m e A Ψ) : DiracGaugeField m (-e) A (conjField Ψ) := by
  refine ⟨chargeConjCLM.differentiable.comp hΨ.1, fun x => ?_⟩
  unfold gaugeDiracOp
  simp only [covD_conjField e A (hΨ.1 x), diracMat_chargeConj]
  rw [← chargeConj_finset_sum]
  have h := hΨ.2 x
  unfold gaugeDiracOp at h
  rw [h, chargeConj_smul, conjField]
  simp [Complex.conj_ofReal]

theorem diracField_conjField {m : ℝ} {Ψ : Vec4 → DiracSpinor} (hΨ : DiracField m Ψ) :
    DiracField m (conjField Ψ) := by
  have h := diracGaugeField_conjField ((diracGaugeField_zero m 0 Ψ).2 hΨ)
  rw [neg_zero] at h
  exact (diracGaugeField_zero m 0 _).1 h

theorem wavePhase_neg_left (p x : Vec4) : wavePhase (-p) x = -wavePhase p x := by
  simp [wavePhase, Finset.sum_neg_distrib]

theorem wavePhase_neg_right (p x : Vec4) : wavePhase p (-x) = wavePhase (-p) x := by
  simp [wavePhase, Finset.sum_neg_distrib]

/-- The charge conjugate of the plane wave of momentum `p` is the plane wave of
momentum `-p`: positive frequency becomes negative frequency. -/
theorem conjField_planeWave (p : Vec4) (u : DiracSpinor) :
    conjField (planeWave p u) = planeWave (-p) (chargeConj u) := by
  funext x
  rw [conjField, planeWave, planeWave, chargeConj_smul, Complex.star_def, ← Complex.exp_conj,
    wavePhase_neg_left]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-! ### Point reflection by the dual map -/

/-- Reflected potential `x ↦ -A(-x)`. -/
def reflectPot (A : Vec4 → Vec4) : Vec4 → Vec4 :=
  fun x => -A (-x)

theorem reflectPot_zero : reflectPot (0 : Vec4 → Vec4) = 0 := by
  funext x
  simp [reflectPot]

/-- Reflected field `x ↦ ω Ψ(-x)`. -/
noncomputable def reflectField (Ψ : Vec4 → DiracSpinor) : Vec4 → DiracSpinor :=
  fun x => dualFlip (Ψ (-x))

theorem reflectField_eq (Ψ : Vec4 → DiracSpinor) :
    reflectField Ψ = diracCLM dualPseudoMat ∘ Ψ ∘ fun x => -x := rfl

theorem partialD_reflectField {Ψ : Vec4 → DiracSpinor} {x : Vec4}
    (hΨ : DifferentiableAt ℝ Ψ (-x)) (μ : Fin 4) :
    partialD (reflectField Ψ) μ x = -dualFlip (partialD Ψ μ (-x)) := by
  have h : HasFDerivAt (reflectField Ψ)
      ((diracCLM dualPseudoMat).comp
        ((fderiv ℝ Ψ (-x)).comp (-ContinuousLinearMap.id ℝ Vec4))) x := by
    rw [reflectField_eq]
    exact (diracCLM _).hasFDerivAt.comp x (hΨ.hasFDerivAt.comp x (hasFDerivAt_id x).neg)
  unfold partialD
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply, ContinuousLinearMap.id_apply,
    map_neg, diracCLM_apply]
  rfl

theorem covD_reflectField (e : ℝ) (A : Vec4 → Vec4) {Ψ : Vec4 → DiracSpinor} {x : Vec4}
    (hΨ : DifferentiableAt ℝ Ψ (-x)) (μ : Fin 4) :
    covD e (reflectPot A) (reflectField Ψ) μ x = -dualFlip (covD e A Ψ μ (-x)) := by
  rw [covD, covD, partialD_reflectField hΨ, dualFlip_sub, dualFlip_smul, reflectField,
    reflectPot]
  simp only [Pi.neg_apply, mul_neg, ofReal_neg, neg_smul, sub_neg_eq_add, neg_sub]
  abel

/-- Point reflection by the dual map carries a solution in `A` to a solution of
the same mass and charge in the reflected potential. -/
theorem diracGaugeField_reflectField {m e : ℝ} {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hΨ : DiracGaugeField m e A Ψ) : DiracGaugeField m e (reflectPot A) (reflectField Ψ) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [reflectField_eq]
    exact (diracCLM _).differentiable.comp (hΨ.1.comp differentiable_id.neg)
  unfold gaugeDiracOp
  simp only [covD_reflectField e A (hΨ.1 (-x)), applyDiracMat_neg_right, diracMat_dualFlip,
    neg_neg]
  rw [← dualFlip_finset_sum]
  have h := hΨ.2 (-x)
  unfold gaugeDiracOp at h
  rw [h, dualFlip_smul, reflectField]

theorem diracField_reflectField {m : ℝ} {Ψ : Vec4 → DiracSpinor} (hΨ : DiracField m Ψ) :
    DiracField m (reflectField Ψ) := by
  have h := diracGaugeField_reflectField ((diracGaugeField_zero m 0 Ψ).2 hΨ)
  rw [reflectPot_zero] at h
  exact (diracGaugeField_zero m 0 _).1 h

/-- Point reflection by the dual map carries the plane wave of momentum `p` to
the plane wave of momentum `-p`. -/
theorem reflectField_planeWave (p : Vec4) (u : DiracSpinor) :
    reflectField (planeWave p u) = planeWave (-p) (dualFlip u) := by
  funext x
  rw [reflectField, planeWave, planeWave, dualFlip_smul, wavePhase_neg_right]

/-! ### The antiparticle field -/

/-- Antiparticle field `x ↦ ω Ψᶜ(-x)`. -/
noncomputable def antiparticleField (Ψ : Vec4 → DiracSpinor) : Vec4 → DiracSpinor :=
  reflectField (conjField Ψ)

/-- The antiparticle field of a solution of charge `e` in `A` solves the
equation of charge `-e` in the reflected potential. -/
theorem diracGaugeField_antiparticleField {m e : ℝ} {A : Vec4 → Vec4}
    {Ψ : Vec4 → DiracSpinor} (hΨ : DiracGaugeField m e A Ψ) :
    DiracGaugeField m (-e) (reflectPot A) (antiparticleField Ψ) :=
  diracGaugeField_reflectField (diracGaugeField_conjField hΨ)

theorem diracField_antiparticleField {m : ℝ} {Ψ : Vec4 → DiracSpinor} (hΨ : DiracField m Ψ) :
    DiracField m (antiparticleField Ψ) :=
  diracField_reflectField (diracField_conjField hΨ)

/-- The antiparticle field of a plane wave of momentum `p` is a plane wave of
the same momentum `p`. -/
theorem antiparticleField_planeWave (p : Vec4) (u : DiracSpinor) :
    antiparticleField (planeWave p u) = planeWave p (antiparticle u) := by
  rw [antiparticleField, conjField_planeWave, reflectField_planeWave, neg_neg, antiparticle]

end Logic

end DstDiophantine
