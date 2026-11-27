import DoubleSpacetime.Logic.Quantum.ShellInformation

/-!
# Shell information off the mean rest frame

`ShellInformation` reads one mean-rest pair. There the relative momentum is spatial, the Born
density is invariant under time translation, and equal weights on one Weyl seed give information
`81/625`.

The same mass and the same seed, with one momentum at rest and the other at `(5, 4, 0, 0)`, leave
that frame. The relative momentum has time component `-2`, so a pure time displacement realises
every relative phase. Equal weights have fidelity `4/5` and information `144/289`. The chart
ratio of the two time-axis densities is `12/17`, and its square is that information. The number
is not `81/625`: shell information is not a function of the mass.

Fidelity `4/5` is strictly below `1`, so the sample at the origin lies on neither carrier ray.
On the mean-rest pair, the opposite Weyl seed is orthogonal to the original particle. That pair of
on-shell solutions has information `0` and no chart contrast. Two momenta are not enough. The
overlap is the information, and it is still not a Newton–Wigner operator.
-/

namespace DoubleSpacetime

namespace Logic

open Complex

/-! ### A relative energy is read on the time axis -/

theorem wavePhase_timeShift_coord (δ : Vec4) (t : ℝ) :
    wavePhase δ (timeShift t) = δ 0 * t := by
  have hsingle : timeShift t = t • Pi.single 0 (1 : ℝ) := by
    ext μ
    fin_cases μ <;> simp [timeShift]
  rw [hsingle, wavePhase_smul_right, wavePhase_single, mul_comm]

theorem exists_wavePhase_eq_time {δ : Vec4} (h0 : δ 0 ≠ 0) (t : ℝ) :
    ∃ s : ℝ, wavePhase δ (timeShift s) = t := by
  refine ⟨t / δ 0, ?_⟩
  rw [wavePhase_timeShift_coord]
  exact mul_div_cancel₀ t h0

private theorem re_exp_mul (θ : ℝ) (z : ℂ) :
    (exp (I * (θ : ℂ)) * z).re = Real.cos θ * z.re - Real.sin θ * z.im := by
  rw [show I * (θ : ℂ) = (θ : ℂ) * I by ring, Complex.exp_mul_I, mul_re, Complex.add_re,
    Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem align_overlap (z : ℂ) :
    (exp (I * ((-arg z) : ℂ)) * z).re = ‖z‖ ∧
      (exp (I * ((-arg z + Real.pi) : ℂ)) * z).re = -‖z‖ := by
  have hsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    ring
  by_cases hz : z = 0
  · simp [hz]
  · have hcos : Real.cos (arg z) = z.re / ‖z‖ := cos_arg hz
    have hsin : Real.sin (arg z) = z.im / ‖z‖ := sin_arg z
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hneg : ((-arg z : ℝ) : ℂ) = -((arg z : ℝ) : ℂ) := by simp
    have hpi : ((-arg z + Real.pi : ℝ) : ℂ) =
        -((arg z : ℝ) : ℂ) + (Real.pi : ℂ) := by
      push_cast
      ring
    constructor
    · rw [← hneg, re_exp_mul]
      simp only [Real.cos_neg, Real.sin_neg, hcos, hsin]
      field_simp [hn]
      nlinarith
    · rw [← hpi, re_exp_mul, Real.cos_add_pi, Real.sin_add_pi]
      simp only [Real.cos_neg, Real.sin_neg, hcos, hsin, neg_mul, sub_neg_eq_add]
      field_simp [hn]
      nlinarith

/-- Nonzero relative energy puts the carrier overlap on the time axis. -/
theorem relativeEnergy_timeContrast {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) {p q : Vec4}
    (h0 : (q - p) 0 ≠ 0) {u v : DiracSpinor} (hov : inner ℂ u v ≠ 0) (α : ℝ) :
    ∃ t₁ t₂ : ℝ,
      bornDensity (shellPacket r s α p q u v) (timeShift t₁) ≠
        bornDensity (shellPacket r s α p q u v) (timeShift t₂) := by
  set z : ℂ := inner ℂ u v
  have hz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hov
  set θ : ℝ := -arg z
  obtain ⟨t₁, ht₁⟩ := exists_wavePhase_eq_time h0 (θ - α)
  obtain ⟨t₂, ht₂⟩ := exists_wavePhase_eq_time h0 (θ + Real.pi - α)
  have ht₁θ : wavePhase (q - p) (timeShift t₁) + α = θ := by linarith
  have ht₂θ : wavePhase (q - p) (timeShift t₂) + α = θ + Real.pi := by linarith
  have ht₁C : (wavePhase (q - p) (timeShift t₁) : ℂ) + (α : ℂ) = (θ : ℂ) := by
    rw [← ofReal_add, ht₁θ]
  have ht₂C : (wavePhase (q - p) (timeShift t₂) : ℂ) + (α : ℂ) =
      ((θ + Real.pi : ℝ) : ℂ) := by
    rw [← ofReal_add, ht₂θ]
  refine ⟨t₁, t₂, ?_⟩
  intro heq
  have hdiff : bornDensity (shellPacket r s α p q u v) (timeShift t₁) -
      bornDensity (shellPacket r s α p q u v) (timeShift t₂) = 4 * r * s * ‖z‖ := by
    rw [bornDensity_shellPacket, bornDensity_shellPacket, ht₁C, ht₂C]
    have hzuv : z = inner ℂ u v := rfl
    rw [← hzuv]
    simp only [θ]
    rw [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_neg]
    have halign := align_overlap z
    rw [halign.1, halign.2]
    ring
  rw [heq, sub_self] at hdiff
  exact absurd hdiff.symm
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hr) hs) hz)

/-! ### Rest momentum against `(5, 4, 0, 0)` -/

/-- On-shell particle at rest, mass `3`, seed `shellAxisSeed`. -/
noncomputable def shellLabSpinor : DiracSpinor :=
  onShellParticleSpinor 3 (restMomentum 3) shellAxisSeed

theorem shellLab_geometry :
    minkowskiQ shellRestP = minkowskiQ (restMomentum 3) ∧
      (restMomentum 3 - shellRestP) 0 = -2 ∧
        ¬ MeanRestFrame shellRestP (restMomentum 3) ∧
          shellRestP ≠ restMomentum 3 := by
  have hP := shellRest_geometry.1
  have hrest : minkowskiQ (restMomentum 3) = -((3 : ℝ) ^ 2) := by
    simpa using minkowskiQ_rest (3 : ℝ)
  refine ⟨hP.trans hrest.symm, ?_, ?_, ?_⟩
  · simp [restMomentum, shellRestP, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne]
    norm_num
  · intro hframe
    have h1 := hframe.1
    simp [shellRestP, restMomentum, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne] at h1
  · intro h
    have h1 := congrFun h 1
    simp [shellRestP, restMomentum, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne] at h1

private theorem shellLab_coord :
    shellLabSpinor 0 = 1 ∧ shellLabSpinor 1 = 0 ∧
      shellLabSpinor 2 = I ∧ shellLabSpinor 3 = 0 := by
  have heq : shellLabSpinor = restParticleSpinor shellAxisSeed :=
    onShellParticleSpinor_rest (by norm_num) shellAxisSeed
  rw [heq]
  have hseed0 : shellAxisSeed 0 = 1 := by simp [shellAxisSeed, EuclideanSpace.single]
  have hseed1 : shellAxisSeed 1 = 0 := by simp [shellAxisSeed, EuclideanSpace.single]
  have hI0 : (I • shellAxisSeed) 0 = I := by simp [PiLp.smul_apply, hseed0]
  have hI1 : (I • shellAxisSeed) 1 = 0 := by simp [PiLp.smul_apply, hseed1]
  have hv := weylUpper_add_lower shellAxisSeed (I • shellAxisSeed)
  have hdec : weylUpper shellAxisSeed + weylLower (I • shellAxisSeed) =
      restParticleSpinor shellAxisSeed := by
    unfold restParticleSpinor
    rfl
  rw [hv] at hdec
  have hfun := congrArg (fun w : DiracSpinor => (w 0, w 1, w 2, w 3)) hdec
  suffices (1 : ℂ) = restParticleSpinor shellAxisSeed 0 ∧
      (0 : ℂ) = restParticleSpinor shellAxisSeed 1 ∧
        I = restParticleSpinor shellAxisSeed 2 ∧
          (0 : ℂ) = restParticleSpinor shellAxisSeed 3 by
    refine ⟨this.1.symm, this.2.1.symm, this.2.2.1.symm, this.2.2.2.symm⟩
  simpa [hseed0, hseed1, hI0, hI1] using hfun

private theorem shellLab_inner :
    inner ℂ shellParticleP shellLabSpinor = (8 / 3 : ℂ) ∧
      inner ℂ shellLabSpinor shellLabSpinor = (2 : ℂ) := by
  have hP := shellParticleP_coord
  have hR := shellLab_coord
  have hinner (χ ψ : DiracSpinor) (a0 a1 a2 a3 b0 b1 b2 b3 : ℂ)
      (ha0 : χ 0 = a0) (ha1 : χ 1 = a1) (ha2 : χ 2 = a2) (ha3 : χ 3 = a3)
      (hb0 : ψ 0 = b0) (hb1 : ψ 1 = b1) (hb2 : ψ 2 = b2) (hb3 : ψ 3 = b3) :
      inner ℂ χ ψ = star a0 * b0 + star a1 * b1 + star a2 * b2 + star a3 * b3 := by
    rw [diracSpinor_inner_eq, Fin.sum_univ_four, ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
  refine ⟨?_, ?_⟩
  · have h := hinner shellParticleP shellLabSpinor 1 0 (5 * I / 3) (-((4 : ℂ) * I) / 3)
      1 0 I 0 hP.1 hP.2.1 hP.2.2.1 hP.2.2.2 hR.1 hR.2.1 hR.2.2.1 hR.2.2.2
    rw [h]
    simp [conj_I]
    ring_nf
    norm_num
  · have h := hinner shellLabSpinor shellLabSpinor 1 0 I 0 1 0 I 0
      hR.1 hR.2.1 hR.2.2.1 hR.2.2.2 hR.1 hR.2.1 hR.2.2.1 hR.2.2.2
    rw [h]
    simp [conj_I]
    ring_nf

theorem shellLab_norm : ‖shellLabSpinor‖ ^ 2 = 2 := by
  have h := shellLab_inner.2
  have heq := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := shellLabSpinor)
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (‖shellLabSpinor‖ ^ 2) = (‖shellLabSpinor‖ : ℂ) ^ 2 :=
      Complex.ofReal_pow ‖shellLabSpinor‖ 2
    _ = inner ℂ shellLabSpinor shellLabSpinor := heq.symm
    _ = (2 : ℂ) := h
    _ = Complex.ofReal 2 := by norm_num

theorem shellLab_fidelity : carrierFidelity shellParticleP shellLabSpinor = 4 / 5 := by
  have hinner := shellLab_inner.1
  unfold carrierFidelity carrierOverlap
  rw [hinner]
  have hnp : ‖shellParticleP‖ = √(50 / 9) := by
    rw [← Real.sqrt_sq (norm_nonneg _), shellRest_norms.1]
  have hnr : ‖shellLabSpinor‖ = √2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), shellLab_norm]
  have h8 : ‖(8 / 3 : ℂ)‖ = 8 / 3 := by norm_num
  rw [hnp, hnr, h8]
  have hprod : √(50 / 9) * √2 = √(100 / 9) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 50 / 9)]
    norm_num
  have h10 : √(100 / 9) = 10 / 3 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  rw [hprod, h10]
  norm_num

theorem shellLab_weightInformation :
    phaseInformation ‖shellParticleP‖ ‖shellLabSpinor‖ = 225 / 289 := by
  have hden : ‖shellParticleP‖ ^ 2 + ‖shellLabSpinor‖ ^ 2 ≠ 0 := by
    rw [shellRest_norms.1, shellLab_norm]
    norm_num
  rw [phaseInformation_eq _ _ hden, shellRest_norms.1, shellLab_norm]
  norm_num

theorem shellLab_information :
    shellInformation 1 1 shellParticleP shellLabSpinor = 144 / 289 ∧
      shellInformation 1 1 shellParticleP shellLabSpinor ≠ 81 / 625 := by
  have hfid := shellLab_fidelity
  have hphase := shellLab_weightInformation
  have hI : shellInformation 1 1 shellParticleP shellLabSpinor = 144 / 289 := by
    rw [shellInformation_eq_fidelity_sq, hfid]
    simp only [abs_one, one_mul]
    rw [hphase]
    norm_num
  refine ⟨hI, ?_⟩
  rw [hI]
  norm_num

theorem shellLab_time_density :
    let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
    bornDensity Ψ (timeShift 0) = 116 / 9 ∧
      bornDensity Ψ (timeShift (-Real.pi / 2)) = 20 / 9 ∧
        (timeShift (-Real.pi / 2)) 1 = 0 ∧
          (timeShift (-Real.pi / 2)) 2 = 0 ∧
            (timeShift (-Real.pi / 2)) 3 = 0 := by
  intro Ψ
  have hinner := shellLab_inner.1
  have hδ : (restMomentum 3 - shellRestP) 0 = -2 := shellLab_geometry.2.1
  have hwP : shellWeight 1 shellParticleP = 50 / 9 := by
    unfold shellWeight
    rw [shellRest_norms.1]
    norm_num
  have hwR : shellWeight 1 shellLabSpinor = 2 := by
    unfold shellWeight
    rw [shellLab_norm]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [bornDensity_shellPacket, hwP, hwR, hinner]
    have hphase : wavePhase (restMomentum 3 - shellRestP) (timeShift 0) = 0 := by
      rw [wavePhase_timeShift_coord, hδ]
      simp
    rw [hphase]
    simp only [ofReal_zero, add_zero]
    norm_num
  · rw [bornDensity_shellPacket, hwP, hwR, hinner]
    have hphase : wavePhase (restMomentum 3 - shellRestP) (timeShift (-Real.pi / 2)) =
        Real.pi := by
      rw [wavePhase_timeShift_coord, hδ]
      ring
    rw [hphase]
    simp only [ofReal_zero, add_zero]
    rw [re_exp_mul, Real.cos_pi, Real.sin_pi]
    norm_num
  · simp [timeShift]
  · simp [timeShift]
  · simp [timeShift]

theorem shellLab_time_ratio :
    let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
    (bornDensity Ψ (timeShift 0) - bornDensity Ψ (timeShift (-Real.pi / 2))) /
        (bornDensity Ψ (timeShift 0) + bornDensity Ψ (timeShift (-Real.pi / 2))) =
      12 / 17 ∧
        shellVisibility 1 1 shellParticleP shellLabSpinor = 12 / 17 ∧
          (12 / 17) ^ 2 = shellInformation 1 1 shellParticleP shellLabSpinor := by
  intro Ψ
  have hden := shellLab_time_density
  have hinfo := shellLab_information.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hden.1, hden.2.1]
    norm_num
  · unfold shellVisibility shellWeight carrierOverlap
    rw [shellLab_inner.1, shellRest_norms.1, shellLab_norm]
    have h8 : ‖(8 / 3 : ℂ)‖ = 8 / 3 := by norm_num
    rw [h8]
    norm_num
  · rw [hinfo]
    norm_num

/-! ### The origin sample leaves both carrier rays -/

theorem carrierFidelity_comm (u v : DiracSpinor) :
    carrierFidelity u v = carrierFidelity v u := by
  unfold carrierFidelity carrierOverlap
  rw [← inner_conj_symm u v, Complex.norm_conj, mul_comm]

theorem carrierFidelity_self_smul {u : DiracSpinor} (hu : u ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    carrierFidelity u (z • u) = 1 := by
  unfold carrierFidelity carrierOverlap
  rw [inner_smul_right, norm_smul, inner_self_eq_norm_sq_to_K, norm_mul, norm_pow]
  simp [Complex.norm_real]
  field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hz]

theorem not_smul_of_fidelity_lt_one {u v : DiracSpinor} (hv : v ≠ 0)
    (h : carrierFidelity u v < 1) : ∀ z : ℂ, v ≠ z • u := by
  intro z hz
  have hu : u ≠ 0 := by
    intro hu0
    apply hv
    simpa [hu0] using hz
  by_cases hz0 : z = 0
  · exact hv (by simpa [hz0] using hz)
  · have h1 : carrierFidelity u v = 1 := by
      rw [hz]
      exact carrierFidelity_self_smul hu hz0
    linarith

private theorem shellLab_origin :
    shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor 0 =
      shellParticleP + shellLabSpinor := by
  unfold shellPacket planeWave
  rw [wavePhase_zero, wavePhase_zero]
  simp [Complex.exp_zero]

theorem shellLab_sample_leaves_ray :
    let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
    (∀ z : ℂ, Ψ 0 ≠ z • shellParticleP) ∧ (∀ z : ℂ, Ψ 0 ≠ z • shellLabSpinor) := by
  intro Ψ
  have hfid := shellLab_fidelity
  have hlt : carrierFidelity shellParticleP shellLabSpinor < 1 := by
    rw [hfid]
    norm_num
  have hu : shellParticleP ≠ 0 :=
    onShellParticleSpinor_ne_zero (by simp [shellAxisSeed, EuclideanSpace.single])
  have hv : shellLabSpinor ≠ 0 :=
    onShellParticleSpinor_ne_zero (by simp [shellAxisSeed, EuclideanSpace.single])
  refine ⟨?_, ?_⟩
  · intro z hz
    have hvsmul : shellLabSpinor = (z - 1) • shellParticleP := by
      have hsum : shellParticleP + shellLabSpinor = z • shellParticleP :=
        shellLab_origin.symm.trans hz
      have hsub := congrArg (fun w : DiracSpinor => w - shellParticleP) hsum
      simpa [sub_smul, one_smul] using hsub
    exact not_smul_of_fidelity_lt_one hv hlt (z - 1) hvsmul
  · intro z hz
    have hlt' : carrierFidelity shellLabSpinor shellParticleP < 1 := by
      rw [carrierFidelity_comm, hfid]
      norm_num
    have husmul : shellParticleP = (z - 1) • shellLabSpinor := by
      have hsum : shellParticleP + shellLabSpinor = z • shellLabSpinor :=
        shellLab_origin.symm.trans hz
      have hsub := congrArg (fun w : DiracSpinor => w - shellLabSpinor) hsum
      simpa [add_sub_assoc, sub_smul, one_smul, add_comm] using hsub
    exact not_smul_of_fidelity_lt_one hu hlt' (z - 1) husmul

theorem shellLab_dirac :
    DiracMomentum 3 shellRestP shellParticleP ∧
      DiracMomentum 3 (restMomentum 3) shellLabSpinor ∧
        ¬ (DiracMomentum 3 shellRestP shellLabSpinor ∧
            DiracMomentum 3 (restMomentum 3) shellLabSpinor) := by
  have hv : shellLabSpinor ≠ 0 :=
    onShellParticleSpinor_ne_zero (by simp [shellAxisSeed, EuclideanSpace.single])
  refine ⟨onShellParticle_dirac (by norm_num) shellRest_geometry.1 shellAxisSeed,
      onShellParticle_dirac (by norm_num) (minkowskiQ_rest 3) shellAxisSeed, ?_⟩
  intro ⟨hp, hq⟩
  exact shellLab_geometry.2.2.2 (diracMomentum_unique (by norm_num) hv hp hq)

theorem shellLab_regression :
    (restMomentum 3 - shellRestP) 0 ≠ 0 ∧
      carrierFidelity shellParticleP shellLabSpinor = 4 / 5 ∧
        phaseInformation ‖shellParticleP‖ ‖shellLabSpinor‖ = 225 / 289 ∧
          shellInformation 1 1 shellParticleP shellLabSpinor = 144 / 289 ∧
            shellInformation 1 1 shellParticleP shellLabSpinor ≠ 81 / 625 ∧
              (∀ z : ℂ, shellPacket 1 1 0 shellRestP (restMomentum 3)
                  shellParticleP shellLabSpinor 0 ≠ z • shellParticleP) := by
  have hgeom := shellLab_geometry
  have hinfo := shellLab_information
  refine ⟨?_, shellLab_fidelity, shellLab_weightInformation, hinfo.1, hinfo.2,
      shellLab_sample_leaves_ray.1⟩
  · rw [hgeom.2.1]
    norm_num

/-! ### The opposite Weyl seed is silent -/

/-- Weyl seed `(0, 1)`. -/
noncomputable def shellAxisOrth : DualSpinor :=
  EuclideanSpace.single 1 1

/-- On-shell particle at `shellRestQ` with the opposite seed. -/
noncomputable def shellOrthQ : DiracSpinor :=
  onShellParticleSpinor 3 shellRestQ shellAxisOrth

private theorem diracLower_onShell_formula (m : ℝ) (p : Vec4) (u : DualSpinor) :
    diracLower (onShellParticleSpinor m p u) =
      -(I / (m : ℂ)) • applyMat (pauliSlashBar p) u := by
  unfold onShellParticleSpinor
  rw [diracLower_add, diracLower_weylUpper, diracLower_weylLower, zero_add]

private theorem diracUpper_onShell_formula (m : ℝ) (p : Vec4) (u : DualSpinor) :
    diracUpper (onShellParticleSpinor m p u) = u := by
  unfold onShellParticleSpinor
  rw [diracUpper_add, diracUpper_weylUpper, diracUpper_weylLower, add_zero]

private theorem apply_pauliX_orth :
    applyMat pauliX shellAxisOrth = shellAxisSeed := by
  ext i
  fin_cases i <;>
    simp [applyMat_apply, pauliX, shellAxisOrth, shellAxisSeed, EuclideanSpace.single,
      PiLp.single_apply]

private theorem shellRestQ_coord :
    shellRestQ 0 = 5 ∧ shellRestQ 1 = -4 ∧ shellRestQ 2 = 0 ∧ shellRestQ 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp [shellRestQ, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne]

private theorem slashBar_orth :
    applyMat (pauliSlashBar shellRestQ) shellAxisOrth =
      (-4 : ℂ) • shellAxisSeed + (-5 : ℂ) • shellAxisOrth := by
  have hq := shellRestQ_coord
  have hmat : pauliSlashBar shellRestQ =
      (-5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (-4 : ℂ) • pauliX := by
    unfold pauliSlashBar
    rw [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2]
    simp [zero_smul]
  rw [hmat, applyMat_add_mat, applyMat_smul_mat, applyMat_smul_mat, applyMat_one,
    apply_pauliX_orth, add_comm]

private theorem shellOrth_lower :
    diracLower shellOrthQ =
      (4 * I / 3 : ℂ) • shellAxisSeed + (5 * I / 3 : ℂ) • shellAxisOrth := by
  rw [shellOrthQ, diracLower_onShell_formula, slashBar_orth, smul_add, smul_smul, smul_smul]
  have h0 : -(I / ((3 : ℝ) : ℂ)) * (-4) = 4 * I / 3 := by
    field_simp
    norm_cast
  have h1 : -(I / ((3 : ℝ) : ℂ)) * (-5) = 5 * I / 3 := by
    field_simp
    norm_cast
  rw [h0, h1]

private theorem shellOrth_coord :
    shellOrthQ 0 = 0 ∧ shellOrthQ 1 = 1 ∧
      shellOrthQ 2 = 4 * I / 3 ∧ shellOrthQ 3 = 5 * I / 3 := by
  have hup : diracUpper shellOrthQ = shellAxisOrth :=
    diracUpper_onShell_formula 3 shellRestQ shellAxisOrth
  have hdec : weylUpper shellAxisOrth + weylLower (diracLower shellOrthQ) = shellOrthQ := by
    simpa [hup] using weyl_decompose shellOrthQ
  rw [shellOrth_lower] at hdec
  have horth0 : shellAxisOrth 0 = 0 := by simp [shellAxisOrth, EuclideanSpace.single]
  have horth1 : shellAxisOrth 1 = 1 := by simp [shellAxisOrth, EuclideanSpace.single]
  have hlow0 : (((4 * I / 3 : ℂ) • shellAxisSeed +
      (5 * I / 3 : ℂ) • shellAxisOrth : DualSpinor) 0) = 4 * I / 3 := by
    simp [shellAxisSeed, shellAxisOrth, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single]
  have hlow1 : (((4 * I / 3 : ℂ) • shellAxisSeed +
      (5 * I / 3 : ℂ) • shellAxisOrth : DualSpinor) 1) = 5 * I / 3 := by
    simp [shellAxisSeed, shellAxisOrth, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single]
  have hv := weylUpper_add_lower shellAxisOrth
    ((4 * I / 3 : ℂ) • shellAxisSeed + (5 * I / 3 : ℂ) • shellAxisOrth)
  rw [hv] at hdec
  have hfun := congrArg (fun w : DiracSpinor => (w 0, w 1, w 2, w 3)) hdec
  suffices (0 : ℂ) = shellOrthQ 0 ∧ (1 : ℂ) = shellOrthQ 1 ∧
      4 * I / 3 = shellOrthQ 2 ∧ 5 * I / 3 = shellOrthQ 3 by
    refine ⟨this.1.symm, this.2.1.symm, this.2.2.1.symm, this.2.2.2.symm⟩
  simpa [horth0, horth1, hlow0, hlow1] using hfun

theorem shellOrth_norm : ‖shellOrthQ‖ ^ 2 = 50 / 9 := by
  have hQ := shellOrth_coord
  have hself : inner ℂ shellOrthQ shellOrthQ = (50 / 9 : ℂ) := by
    rw [diracSpinor_inner_eq, Fin.sum_univ_four, hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2]
    simp [conj_I]
    ring_nf
    norm_num
  have heq := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := shellOrthQ)
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (‖shellOrthQ‖ ^ 2) = (‖shellOrthQ‖ : ℂ) ^ 2 :=
      Complex.ofReal_pow ‖shellOrthQ‖ 2
    _ = inner ℂ shellOrthQ shellOrthQ := heq.symm
    _ = (50 / 9 : ℂ) := hself
    _ = Complex.ofReal (50 / 9) := by norm_num

theorem shellOrth_inner : inner ℂ shellParticleP shellOrthQ = 0 := by
  have hP := shellParticleP_coord
  have hQ := shellOrth_coord
  rw [diracSpinor_inner_eq, Fin.sum_univ_four, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2,
    hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2]
  simp [conj_I]
  ring_nf

theorem shellOrth_silent (α : ℝ) :
    inner ℂ shellParticleP shellOrthQ = 0 ∧
      shellInformation 1 1 shellParticleP shellOrthQ = 0 ∧
        ¬ ChartPositionInfo
          (shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellOrthQ) ∧
          DiracMomentum 3 shellRestQ shellOrthQ ∧
            shellInformation 1 1 shellParticleP shellParticleQ = 81 / 625 := by
  have hinner := shellOrth_inner
  refine ⟨hinner, orthogonal_shellInformation hinner 1 1,
      orthogonal_no_chartPositionInfo hinner 1 1 α shellRestP shellRestQ,
      onShellParticle_dirac (by norm_num) shellRest_geometry.2.1 shellAxisOrth,
      shellRest_information.1⟩

end Logic

end DoubleSpacetime
