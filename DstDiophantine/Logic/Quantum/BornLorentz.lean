import DstDiophantine.Logic.Quantum.FrameInformation

/-!
# Chart Born density against the Lorentz scalar

The chart Born density is `‖Ψ‖²`, and `realCurrent_zero` says that this is the time component of
the probability current. It is not a Lorentz scalar. The scalar is the mass bilinear
`invariantDensity Ψ = (Ψ̄Ψ).re`. On a solution of mass `m` at momentum `p` the two differ by the
energy factor: the scalar is `(m / p₀) ‖Ψ‖²`. They agree exactly at rest.

A longitudinal boost multiplies the chart density by `cosh` and leaves the scalar at its rest
value. The two agree for every seed only at rapidity `0`.

The information numbers above are read from fixed Weyl seeds, which are not the rotor images of
the rest spinor. On the mass-3 shell the fixed seed at `(5, 4, 0, 0)` has chart density `50/9`
and scalar `10/3`, ratio `5/3`. The rest spinor has both equal to `2`. A usual rotor carrying
that rest spinor onto the same momentum has chart density `2 · 5/3 = 10/3` and scalar `2`. Same
momentum, different representative.

Weight information rebuilt from the square roots of the scalars stays `1` in the mean rest frame,
because both carriers share the factor `5/3`. Against the rest spinor the chart reading is
`225/289` and the scalar reading is `15/16`. The shell information `144/289` still multiplies by
the chart fidelity. An invariant fidelity is not defined here.
-/

namespace DstDiophantine

namespace Logic

open Complex InnerProductSpace

/-! ### The scalar density -/

/-- Real mass bilinear `(Ψ̄Ψ).re`. -/
noncomputable def invariantDensity (Ψ : DiracSpinor) : ℝ :=
  (diracScalar Ψ Ψ).re

theorem bornDensity_eq_realCurrent (p : Vec4) (u : DiracSpinor) (x : Vec4) :
    bornDensity (planeWave p u) x = realCurrent u 0 := by
  rw [bornDensity_planeWave, realCurrent_zero]

theorem invariantDensity_onShell {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (hm : m ≠ 0)
    (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) :
    invariantDensity Ψ = m / p 0 * ‖Ψ‖ ^ 2 := by
  obtain ⟨-, hS⟩ := diracScalar_self_eq hm hΨ h
  unfold invariantDensity
  rw [hS, ofReal_re]

theorem chart_over_invariant {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (hm : m ≠ 0)
    (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) :
    ‖Ψ‖ ^ 2 / invariantDensity Ψ = p 0 / m := by
  have hI := invariantDensity_onShell hm hΨ h
  have hp0 : p 0 ≠ 0 := (diracScalar_self_eq hm hΨ h).1
  have hnorm : ‖Ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hΨ)
  have hden : m / p 0 * ‖Ψ‖ ^ 2 ≠ 0 := mul_ne_zero (div_ne_zero hm hp0) hnorm
  rw [hI]
  field_simp [hden, hp0, hm, hnorm]

/-- On a positive-energy shell the chart density equals the scalar exactly at rest. -/
theorem invariant_eq_chart_iff_rest {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (hm : 0 < m)
    (hp : 0 < p 0) (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) :
    invariantDensity Ψ = ‖Ψ‖ ^ 2 ↔ p = restMomentum m := by
  have hI := invariantDensity_onShell hm.ne' hΨ h
  have hnorm : ‖Ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hΨ)
  constructor
  · intro heq
    rw [hI] at heq
    have hratio : m / p 0 = 1 := by
      apply mul_right_cancel₀ hnorm
      rw [one_mul]
      exact heq
    have hp0m : p 0 = m := by
      have hmul : m / p 0 * p 0 = p 0 := by rw [hratio, one_mul]
      rw [div_mul_cancel₀ _ hp.ne'] at hmul
      exact hmul.symm
    have hQ := diracMomentum_implies_mass_shell hΨ h
    rw [minkowskiQ_eq, hp0m] at hQ
    have hsum : p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 = 0 := by linarith
    have h1 : p 1 = 0 := by
      have : p 1 ^ 2 = 0 := by nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
      exact sq_eq_zero_iff.mp this
    have h2 : p 2 = 0 := by
      have : p 2 ^ 2 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 3)]
      exact sq_eq_zero_iff.mp this
    have h3 : p 3 = 0 := by
      have : p 3 ^ 2 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]
      exact sq_eq_zero_iff.mp this
    ext μ
    fin_cases μ <;> simp [restMomentum, hp0m, h1, h2, h3]
  · intro hpRest
    rw [hI, hpRest]
    simp [restMomentum, div_self hm.ne', one_mul]

/-! ### A longitudinal boost scales the chart and fixes the scalar -/

theorem boostedRest_chartDensity (α : ℝ) (u : DualSpinor) :
    ‖applyDiracBoostZ α (restParticleSpinor u)‖ ^ 2 =
      Real.cosh α * ‖restParticleSpinor u‖ ^ 2 := by
  set Ψ := applyDiracBoostZ α (restParticleSpinor u)
  set Φ := restParticleSpinor u
  have hjoin : inner ℂ Ψ Ψ = (Real.cosh α : ℂ) * inner ℂ Φ Φ := by
    rw [boostedRest_inner, restParticle_inner]
    ring
  apply ofReal_injective
  calc
    ofReal (‖Ψ‖ ^ 2) = (‖Ψ‖ : ℂ) ^ 2 := ofReal_pow _ _
    _ = inner ℂ Ψ Ψ := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := Ψ)).symm
    _ = (Real.cosh α : ℂ) * inner ℂ Φ Φ := hjoin
    _ = (Real.cosh α : ℂ) * (‖Φ‖ : ℂ) ^ 2 :=
      congrArg (fun z : ℂ => (Real.cosh α : ℂ) * z)
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := Φ))
    _ = (Real.cosh α : ℂ) * ofReal (‖Φ‖ ^ 2) :=
      congrArg (fun z : ℂ => (Real.cosh α : ℂ) * z) (ofReal_pow ‖Φ‖ 2).symm
    _ = ofReal (Real.cosh α * ‖Φ‖ ^ 2) := (ofReal_mul _ _).symm

theorem boostedRest_invariantDensity (α : ℝ) (u : DualSpinor) :
    invariantDensity (applyDiracBoostZ α (restParticleSpinor u)) =
      invariantDensity (restParticleSpinor u) := by
  unfold invariantDensity
  rw [boostedRest_diracScalar, restParticle_diracScalar]

private theorem shell_energy : shellRestP 0 = 5 ∧ shellRestQ 0 = 5 := by
  constructor
  · simp [shellRestP, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne]
  · simp [shellRestQ, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne]

private theorem shell_seed_ne : shellAxisSeed ≠ 0 := by
  simp [shellAxisSeed, EuclideanSpace.single]

theorem shellLab_densities :
    invariantDensity shellLabSpinor = 2 ∧ ‖shellLabSpinor‖ ^ 2 = 2 := by
  refine ⟨?_, shellLab_norm⟩
  have hinv := invariantDensity_onShell (by norm_num : (3 : ℝ) ≠ 0)
    (onShellParticleSpinor_ne_zero shell_seed_ne) shellLab_dirac.2.1
  have hinv' : invariantDensity shellLabSpinor =
      3 / restMomentum 3 0 * ‖shellLabSpinor‖ ^ 2 := by
    simpa [shellLabSpinor] using hinv
  have hp : restMomentum 3 0 = 3 := by simp [restMomentum]
  rw [hinv', hp, shellLab_norm]
  norm_num

private theorem cosh_eq_one_iff (α : ℝ) : Real.cosh α = 1 ↔ α = 0 := by
  constructor
  · intro h
    have hexp : Real.exp α + Real.exp (-α) = 2 := by
      rw [Real.cosh_eq] at h
      linarith
    have hneg : Real.exp (-α) * Real.exp α = 1 := by
      rw [← Real.exp_add]
      simp
    have hpoly : Real.exp α ^ 2 + 1 = 2 * Real.exp α := by
      calc Real.exp α ^ 2 + 1
          = Real.exp α ^ 2 + Real.exp (-α) * Real.exp α := by rw [hneg]
        _ = Real.exp α * (Real.exp α + Real.exp (-α)) := by ring
        _ = Real.exp α * 2 := by rw [hexp]
        _ = 2 * Real.exp α := by ring
    have hsq : (Real.exp α - 1) ^ 2 = 0 := by
      have : (Real.exp α - 1) ^ 2 = Real.exp α ^ 2 - 2 * Real.exp α + 1 := by ring
      linarith
    have hexp1 : Real.exp α = 1 := by
      have : Real.exp α - 1 = 0 := sq_eq_zero_iff.mp hsq
      linarith
    exact Real.exp_injective (by simpa [Real.exp_zero] using hexp1)
  · intro h
    simp [h]

/-- Chart and scalar densities of every boosted rest spinor agree only at rapidity `0`. -/
theorem boostedRest_densities_eq_iff (α : ℝ) :
    (∀ u : DualSpinor,
        invariantDensity (applyDiracBoostZ α (restParticleSpinor u)) =
          ‖applyDiracBoostZ α (restParticleSpinor u)‖ ^ 2) ↔
      α = 0 := by
  constructor
  · intro h
    have heq : restParticleSpinor shellAxisSeed = shellLabSpinor :=
      (onShellParticleSpinor_rest (by norm_num : (3 : ℝ) ≠ 0) shellAxisSeed).symm
    have hu := h shellAxisSeed
    rw [boostedRest_invariantDensity, boostedRest_chartDensity, heq, shellLab_densities.1,
      shellLab_densities.2] at hu
    have hcosh : Real.cosh α = 1 := by
      apply mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
      have : 2 * Real.cosh α = 2 * 1 := by
        rw [mul_one]
        linarith [hu]
      exact this
    exact (cosh_eq_one_iff α).1 hcosh
  · intro hα u
    subst hα
    rw [boostedRest_chartDensity, Real.cosh_zero, one_mul, boostedRest_invariantDensity]
    unfold invariantDensity
    rw [restParticle_diracScalar_eq_inner]
    have hself := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := restParticleSpinor u)
    calc
      (inner ℂ (restParticleSpinor u) (restParticleSpinor u)).re =
          ((‖restParticleSpinor u‖ : ℂ) ^ 2).re := congrArg Complex.re hself
      _ = (ofReal (‖restParticleSpinor u‖ ^ 2)).re :=
          congrArg Complex.re (ofReal_pow _ 2).symm
      _ = ‖restParticleSpinor u‖ ^ 2 := ofReal_re _

/-! ### Fixed seeds on the mass-3 shell, and the rotor image of rest -/

private theorem shell_carrier_densities {Ψ : DiracSpinor} {p : Vec4} (hΨ : Ψ ≠ 0)
    (h : DiracMomentum 3 p Ψ) (hp : p 0 = 5) (hn : ‖Ψ‖ ^ 2 = 50 / 9) :
    invariantDensity Ψ = 10 / 3 ∧
      ‖Ψ‖ ^ 2 / invariantDensity Ψ = 5 / 3 ∧
        ‖Ψ‖ ^ 2 / invariantDensity Ψ = p 0 / 3 := by
  have hI : invariantDensity Ψ = 10 / 3 := by
    rw [invariantDensity_onShell (by norm_num : (3 : ℝ) ≠ 0) hΨ h, hp, hn]
    norm_num
  refine ⟨hI, ?_, ?_⟩
  · rw [hn, hI]
    norm_num
  · rw [hn, hI, hp]
    norm_num

theorem shellParticle_densities :
    invariantDensity shellParticleP = 10 / 3 ∧
      ‖shellParticleP‖ ^ 2 = 50 / 9 ∧
        ‖shellParticleP‖ ^ 2 / invariantDensity shellParticleP = 5 / 3 ∧
          ‖shellParticleP‖ ^ 2 / invariantDensity shellParticleP = shellRestP 0 / 3 ∧
            invariantDensity shellParticleQ = 10 / 3 ∧
              ‖shellParticleQ‖ ^ 2 = 50 / 9 ∧
                ‖shellParticleQ‖ ^ 2 / invariantDensity shellParticleQ = 5 / 3 ∧
                  ‖shellParticleQ‖ ^ 2 / invariantDensity shellParticleQ =
                    shellRestQ 0 / 3 := by
  have hne : shellParticleP ≠ 0 := onShellParticleSpinor_ne_zero shell_seed_ne
  have hneQ : shellParticleQ ≠ 0 := onShellParticleSpinor_ne_zero shell_seed_ne
  have hP := shell_carrier_densities hne shellRest_dirac.1 shell_energy.1 shellRest_norms.1
  have hQ := shell_carrier_densities hneQ shellRest_dirac.2.1 shell_energy.2 shellRest_norms.2
  exact ⟨hP.1, shellRest_norms.1, hP.2.1, hP.2.2, hQ.1, shellRest_norms.2, hQ.2.1, hQ.2.2⟩

/-- The rest spinor, carried onto `(5, 4, 0, 0)`, is not the fixed-seed carrier. -/
theorem shellRest_rotorImage :
    ∃ Ψ : DiracSpinor,
      DiracMomentum 3 shellRestP Ψ ∧
        ‖Ψ‖ ^ 2 = 10 / 3 ∧
          invariantDensity Ψ = 2 ∧
            ‖Ψ‖ ^ 2 = 2 * (shellRestP 0 / 3) ∧
              ‖shellParticleP‖ ^ 2 ≠ ‖Ψ‖ ^ 2 := by
  obtain ⟨α, hα⟩ := exists_usualRotor_momentum (by norm_num : (0 : ℝ) < 3)
    shellRest_geometry.1 shellRest_geometry.2.2.2.1
  set M := usualRotorMat α
  set Ψ := rotorDirac M shellLabSpinor
  have hdet : M.det = 1 := usualRotorMat_det α
  have hrest : DiracMomentum 3 (restMomentum 3) shellLabSpinor := shellLab_dirac.2.1
  have hdir : DiracMomentum 3 shellRestP Ψ := by
    have hmove := diracMomentum_rotorDirac hdet hrest
    rwa [hα] at hmove
  have hprod : (3 : ℝ) * ‖Ψ‖ ^ 2 = 10 := by
    have hscale := norm_sq_rotorDirac_rest hdet (by norm_num : (3 : ℝ) ≠ 0) hrest
    rw [hα] at hscale
    calc
      (3 : ℝ) * ‖Ψ‖ ^ 2 = shellRestP 0 * ‖shellLabSpinor‖ ^ 2 := hscale
      _ = 5 * 2 := by rw [shell_energy.1, shellLab_norm]
      _ = 10 := by norm_num
  have hn : ‖Ψ‖ ^ 2 = 10 / 3 := by
    rw [eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)]
    linarith [hprod]
  have hinv : invariantDensity Ψ = 2 := by
    unfold invariantDensity
    rw [diracScalar_rotorDirac hdet]
    exact shellLab_densities.1
  have hfactor : ‖Ψ‖ ^ 2 = 2 * (shellRestP 0 / 3) := by
    rw [hn, shell_energy.1]
    norm_num
  have hne : ‖shellParticleP‖ ^ 2 ≠ ‖Ψ‖ ^ 2 := by
    rw [shellRest_norms.1, hn]
    norm_num
  exact ⟨Ψ, hdir, hn, hinv, hfactor, hne⟩

/-! ### Weight information from the scalar densities -/

theorem shellParticleP_invariant : invariantDensity shellParticleP = 10 / 3 :=
  shellParticle_densities.1

theorem shellParticleQ_invariant : invariantDensity shellParticleQ = 10 / 3 :=
  shellParticle_densities.2.2.2.2.1

theorem shellRest_invariantPhase :
    phaseInformation ‖shellParticleP‖ ‖shellParticleQ‖ = 1 ∧
      phaseInformation (Real.sqrt (invariantDensity shellParticleP))
          (Real.sqrt (invariantDensity shellParticleQ)) = 1 := by
  refine ⟨shellRest_information.2.1, ?_⟩
  rw [shellParticleP_invariant, shellParticleQ_invariant]
  exact phaseInformation_equal <|
    (Real.sqrt_ne_zero (by norm_num : (0 : ℝ) ≤ 10 / 3)).mpr (by norm_num)

theorem shellLab_invariantPhase :
    phaseInformation ‖shellParticleP‖ ‖shellLabSpinor‖ = 225 / 289 ∧
      phaseInformation (Real.sqrt (invariantDensity shellParticleP))
          (Real.sqrt (invariantDensity shellLabSpinor)) = 15 / 16 ∧
        (15 / 16 : ℝ) ≠ 225 / 289 ∧
          shellInformation 1 1 shellParticleP shellLabSpinor = 144 / 289 := by
  refine ⟨shellLab_weightInformation, ?_, by norm_num, shellLab_information.1⟩
  have hP : invariantDensity shellParticleP = 10 / 3 := shellParticleP_invariant
  have hL : invariantDensity shellLabSpinor = 2 := shellLab_densities.1
  have hsP : 0 ≤ invariantDensity shellParticleP := by rw [hP]; norm_num
  have hsL : 0 ≤ invariantDensity shellLabSpinor := by rw [hL]; norm_num
  have hden : (Real.sqrt (invariantDensity shellParticleP)) ^ 2 +
      (Real.sqrt (invariantDensity shellLabSpinor)) ^ 2 ≠ 0 := by
    rw [Real.sq_sqrt hsP, Real.sq_sqrt hsL, hP, hL]
    norm_num
  rw [phaseInformation_eq _ _ hden, Real.sq_sqrt hsP, Real.sq_sqrt hsL, hP, hL]
  norm_num

end Logic

end DstDiophantine
