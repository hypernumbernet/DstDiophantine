import DstDiophantine.Logic.Quantum.FrameInformation

/-!
# The carrier deficit of shell information

`PhaseInformation` gives `D² + I = 1` on one carrier. `ShellInformation` multiplies `I` by the
fidelity squared. The product is what the chart can read. The remainder is the carrier deficit

`Δ = (1 − F²) · phaseInformation`.

The three terms add to one. `Δ` depends on the two carriers and the two weights. It does not
depend on a chart point. A shared carrier has `F = 1`, so `Δ = 0` and the single-carrier identity
returns. One weight has phase information `0`, so `Δ = 0`: a definite momentum has no deficit.

One nonzero mass forbids a shared carrier at two momenta. Both weights then force `Δ > 0`, and
`D² + I_shell < 1`. The extreme chart ratio equals `shellVisibility`, so those two samples read
`I_shell` and do not read `Δ`. Every chart contrast stays at most `4rs|⟨u, v⟩|`, strictly below
the Cauchy bound `4rs‖u‖‖v‖`.

On the mass-3 shell the split is numerical. Mean rest has `D = 0`, visibility `9/25`, and
`Δ = 544/625`. Rest against `(5, 4, 0, 0)` has `D = 8/17`, visibility `12/17`, and
`Δ = 81/289`. The opposite Weyl seed has `Δ = 1`. The deficit is not a Newton–Wigner operator.
-/

namespace DstDiophantine

namespace Logic

open Complex

/-! ### The complement that the chart does not read -/

/-- Carrier deficit: the part of `phaseInformation` removed by `1 − F²`. -/
noncomputable def shellDeficit (r s : ℝ) (u v : DiracSpinor) : ℝ :=
  (1 - carrierFidelity u v ^ 2) * phaseInformation (|r| * ‖u‖) (|s| * ‖v‖)

theorem shellDeficit_nonneg (r s : ℝ) (u v : DiracSpinor) : 0 ≤ shellDeficit r s u v := by
  unfold shellDeficit
  have hF := carrierFidelity_le_one u v
  have h0 := carrierFidelity_nonneg u v
  have hgap : 0 ≤ 1 - carrierFidelity u v ^ 2 := by nlinarith
  exact mul_nonneg hgap (phaseInformation_nonneg _ _)

theorem which_shell_deficit (r s : ℝ) (u v : DiracSpinor)
    (h : (|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2 ≠ 0) :
    whichMomentum (|r| * ‖u‖) (|s| * ‖v‖) ^ 2 + shellInformation r s u v +
        shellDeficit r s u v =
      1 := by
  have hid := whichMomentum_sq_add_phaseInformation (|r| * ‖u‖) (|s| * ‖v‖) h
  rw [shellInformation_eq_fidelity_sq, shellDeficit]
  linarith

theorem shellDeficit_eq_zero_iff (r s : ℝ) (u v : DiracSpinor)
    (h : (|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2 ≠ 0) :
    shellDeficit r s u v = 0 ↔
      |r| * ‖u‖ = 0 ∨ |s| * ‖v‖ = 0 ∨ carrierFidelity u v = 1 := by
  unfold shellDeficit
  set a : ℝ := |r| * ‖u‖
  set b : ℝ := |s| * ‖v‖
  set F : ℝ := carrierFidelity u v
  have hI : phaseInformation a b = 0 ↔ a = 0 ∨ b = 0 := phaseInformation_eq_zero_iff a b h
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with hF | hphase
    · have hsq : F ^ 2 = 1 := by linarith
      rcases sq_eq_one_iff.mp hsq with h1 | hm1
      · exact Or.inr (Or.inr h1)
      · exact absurd (le_of_eq hm1) (by linarith [carrierFidelity_nonneg u v])
    · rcases hI.mp hphase with ha | hb
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
  · intro hrs
    rcases hrs with ha | hb | hF
    · rw [hI.mpr (Or.inl ha), mul_zero]
    · rw [hI.mpr (Or.inr hb), mul_zero]
    · rw [hF, one_pow, sub_self, zero_mul]

theorem shellDeficit_same_carrier (r s : ℝ) {u : DiracSpinor} (hu : u ≠ 0) :
    shellDeficit r s u u = 0 := by
  unfold shellDeficit
  rw [carrierFidelity_self hu, one_pow, sub_self, zero_mul]

theorem shellDeficit_one_weight {r s : ℝ} {u v : DiracSpinor}
    (h : |r| * ‖u‖ = 0 ∨ |s| * ‖v‖ = 0) : shellDeficit r s u v = 0 := by
  unfold shellDeficit
  by_cases hden : (|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2 = 0
  · have ha : |r| * ‖u‖ = 0 := by nlinarith [sq_nonneg (|s| * ‖v‖)]
    have hb : |s| * ‖v‖ = 0 := by nlinarith [sq_nonneg (|r| * ‖u‖)]
    simp [ha, hb, phaseInformation, momentumVariance, momentumShare, div_zero]
  · rw [(phaseInformation_eq_zero_iff _ _ hden).mpr h, mul_zero]

/-! ### One mass forces a positive deficit -/

theorem diracMomentum_of_smul {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} {z : ℂ} (hz : z ≠ 0)
    (h : DiracMomentum m p (z • Ψ)) : DiracMomentum m p Ψ := by
  unfold DiracMomentum at *
  rw [applyDiracMat_smul] at h
  calc
    applyDiracMat (slashMat p) Ψ
        = z⁻¹ • (z • applyDiracMat (slashMat p) Ψ) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = z⁻¹ • ((I * (m : ℂ)) • (z • Ψ)) := by rw [h]
      _ = (I * (m : ℂ)) • Ψ := by
          rw [smul_smul, smul_smul, mul_assoc]
          congr 1
          rw [mul_left_comm, inv_mul_cancel₀ hz, mul_one]

theorem massShell_fidelity_lt_one {m : ℝ} (hm : m ≠ 0) {p q : Vec4} {u v : DiracSpinor}
    (hu : u ≠ 0) (hv : v ≠ 0) (hp : DiracMomentum m p u) (hq : DiracMomentum m q v)
    (hpq : p ≠ q) : carrierFidelity u v < 1 := by
  refine lt_of_le_of_ne (carrierFidelity_le_one u v) ?_
  intro hF
  have hprod : ‖u‖ * ‖v‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr hv)
  have hov : ‖inner ℂ u v‖ = ‖u‖ * ‖v‖ := by
    unfold carrierFidelity carrierOverlap at hF
    have := (div_eq_iff hprod).mp hF
    simpa using this
  obtain ⟨z, hz, hvz⟩ := (norm_inner_eq_norm_iff hu hv).mp hov
  rw [hvz] at hq
  exact hpq (diracMomentum_unique hm hu hp (diracMomentum_of_smul hz hq))

theorem massShell_deficit_pos {m : ℝ} (hm : m ≠ 0) {p q : Vec4} {u v : DiracSpinor}
    (hu : u ≠ 0) (hv : v ≠ 0) (hp : DiracMomentum m p u) (hq : DiracMomentum m q v)
    (hpq : p ≠ q) {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    0 < shellDeficit r s u v ∧
      whichMomentum (|r| * ‖u‖) (|s| * ‖v‖) ^ 2 + shellInformation r s u v < 1 := by
  have hF := massShell_fidelity_lt_one hm hu hv hp hq hpq
  set a : ℝ := |r| * ‖u‖
  set b : ℝ := |s| * ‖v‖
  have ha : a ≠ 0 := mul_ne_zero (abs_ne_zero.mpr hr) (norm_ne_zero_iff.mpr hu)
  have hb : b ≠ 0 := mul_ne_zero (abs_ne_zero.mpr hs) (norm_ne_zero_iff.mpr hv)
  have hden : a ^ 2 + b ^ 2 ≠ 0 := by
    intro hzero
    exact ha (by nlinarith [sq_nonneg b])
  have hI0 : phaseInformation a b ≠ 0 := by
    intro hz
    rcases (phaseInformation_eq_zero_iff a b hden).mp hz with ha0 | hb0
    · exact ha ha0
    · exact hb hb0
  have hIpos : 0 < phaseInformation a b :=
    lt_of_le_of_ne (phaseInformation_nonneg a b) (Ne.symm hI0)
  have hsq : carrierFidelity u v ^ 2 < 1 := by
    have hlt : |carrierFidelity u v| < |(1 : ℝ)| := by
      rw [abs_of_nonneg (carrierFidelity_nonneg u v), abs_one]
      exact hF
    simpa using sq_lt_sq.mpr hlt
  have hgap : 0 < 1 - carrierFidelity u v ^ 2 := by linarith
  have hdef : 0 < shellDeficit r s u v := by
    unfold shellDeficit
    exact mul_pos hgap hIpos
  refine ⟨hdef, ?_⟩
  have hid := which_shell_deficit r s u v hden
  linarith

/-! ### The chart reads the visibility, not the deficit -/

private theorem abs_cross_re (θ : ℝ) (z : ℂ) : |(exp (I * (θ : ℂ)) * z).re| ≤ ‖z‖ := by
  have hmul : ‖exp (I * (θ : ℂ)) * z‖ = ‖z‖ := by rw [norm_mul, norm_exp_I, one_mul]
  have hre : (exp (I * (θ : ℂ)) * z).re ^ 2 ≤ ‖exp (I * (θ : ℂ)) * z‖ ^ 2 := by
    have hsum : (exp (I * (θ : ℂ)) * z).re ^ 2 + (exp (I * (θ : ℂ)) * z).im ^ 2 =
        ‖exp (I * (θ : ℂ)) * z‖ ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]
      ring
    nlinarith [sq_nonneg (exp (I * (θ : ℂ)) * z).im]
  rw [← hmul]
  exact abs_le_of_sq_le_sq hre (norm_nonneg _)

theorem chartContrast_shell_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (α : ℝ) (p q : Vec4)
    (u v : DiracSpinor) (x y : Vec4) :
    |chartContrast (shellPacket r s α p q u v) x y| ≤
      4 * r * s * carrierOverlap u v := by
  unfold chartContrast carrierOverlap
  rw [bornDensity_shellPacket, bornDensity_shellPacket]
  set z : ℂ := inner ℂ u v
  have hdiff : shellWeight r u + shellWeight s v +
        2 * r * s * (exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) * z).re -
      (shellWeight r u + shellWeight s v +
        2 * r * s * (exp (I * ((wavePhase (q - p) y : ℂ) + (α : ℂ))) * z).re) =
      2 * r * s *
        ((exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) * z).re -
          (exp (I * ((wavePhase (q - p) y : ℂ) + (α : ℂ))) * z).re) := by
    ring
  rw [hdiff, abs_mul]
  have hcoeff : |2 * r * s| = 2 * r * s := abs_of_nonneg (by positivity)
  rw [hcoeff]
  have hre : |(exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) * z).re -
        (exp (I * ((wavePhase (q - p) y : ℂ) + (α : ℂ))) * z).re| ≤
      2 * ‖z‖ := by
    have hx := abs_cross_re (wavePhase (q - p) x + α) z
    have hy := abs_cross_re (wavePhase (q - p) y + α) z
    rw [ofReal_add] at hx hy
    set rx : ℝ := (exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) * z).re
    set ry : ℝ := (exp (I * ((wavePhase (q - p) y : ℂ) + (α : ℂ))) * z).re
    have hsub : |rx - ry| ≤ |rx| + |ry| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le rx, le_abs_self ry]
      · linarith [le_abs_self rx, neg_abs_le ry]
    linarith
  have hmul : 2 * r * s * |(exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) * z).re -
        (exp (I * ((wavePhase (q - p) y : ℂ) + (α : ℂ))) * z).re| ≤
      2 * r * s * (2 * ‖z‖) :=
    mul_le_mul_of_nonneg_left hre (by positivity)
  have hfour : 2 * r * s * (2 * ‖z‖) = 4 * r * s * ‖z‖ := by ring
  linarith

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

theorem shellPacket_extremes {r s : ℝ} {p q : Vec4} (hpq : p ≠ q) (α : ℝ)
    (u v : DiracSpinor) :
    ∃ x y : Vec4,
      bornDensity (shellPacket r s α p q u v) x -
          bornDensity (shellPacket r s α p q u v) y =
        4 * r * s * carrierOverlap u v ∧
        bornDensity (shellPacket r s α p q u v) x +
            bornDensity (shellPacket r s α p q u v) y =
          2 * (shellWeight r u + shellWeight s v) := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  set z : ℂ := inner ℂ u v
  set θ : ℝ := -arg z
  obtain ⟨x, hx⟩ := exists_wavePhase_eq hδ (θ - α)
  obtain ⟨y, hy⟩ := exists_wavePhase_eq hδ (θ + Real.pi - α)
  have hxθ : wavePhase (q - p) x + α = θ := by linarith
  have hyθ : wavePhase (q - p) y + α = θ + Real.pi := by linarith
  have hxC : (wavePhase (q - p) x : ℂ) + (α : ℂ) = (θ : ℂ) := by
    rw [← ofReal_add, hxθ]
  have hyC : (wavePhase (q - p) y : ℂ) + (α : ℂ) = ((θ + Real.pi : ℝ) : ℂ) := by
    rw [← ofReal_add, hyθ]
  have halign := align_overlap z
  refine ⟨x, y, ?_, ?_⟩
  · rw [bornDensity_shellPacket, bornDensity_shellPacket, hxC, hyC]
    simp only [θ, z]
    rw [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_neg, halign.1, halign.2]
    unfold carrierOverlap
    ring
  · rw [bornDensity_shellPacket, bornDensity_shellPacket, hxC, hyC]
    simp only [θ, z]
    rw [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_neg, halign.1, halign.2]
    ring

theorem shell_chart_ratio {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) {p q : Vec4} (hpq : p ≠ q)
    (α : ℝ) (u v : DiracSpinor) (hden : shellWeight r u + shellWeight s v ≠ 0) :
    ∃ x y : Vec4,
      (bornDensity (shellPacket r s α p q u v) x -
          bornDensity (shellPacket r s α p q u v) y) /
        (bornDensity (shellPacket r s α p q u v) x +
          bornDensity (shellPacket r s α p q u v) y) =
      shellVisibility r s u v ∧
        ((bornDensity (shellPacket r s α p q u v) x -
            bornDensity (shellPacket r s α p q u v) y) /
          (bornDensity (shellPacket r s α p q u v) x +
            bornDensity (shellPacket r s α p q u v) y)) ^ 2 =
          shellInformation r s u v := by
  obtain ⟨x, y, hdiff, hsum⟩ := shellPacket_extremes hpq α u v
  have hsum_ne : bornDensity (shellPacket r s α p q u v) x +
      bornDensity (shellPacket r s α p q u v) y ≠ 0 := by
    rw [hsum]
    exact mul_ne_zero (by norm_num) hden
  have hratio : (bornDensity (shellPacket r s α p q u v) x -
        bornDensity (shellPacket r s α p q u v) y) /
      (bornDensity (shellPacket r s α p q u v) x +
        bornDensity (shellPacket r s α p q u v) y) =
      shellVisibility r s u v := by
    rw [hdiff, hsum]
    unfold shellVisibility shellWeight carrierOverlap
    rw [abs_of_nonneg hr, abs_of_nonneg hs]
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    field_simp [hden, htwo]
    ring
  refine ⟨x, y, hratio, ?_⟩
  rw [hratio, shellInformation]

theorem massShell_chart_short {m : ℝ} (hm : m ≠ 0) {p q : Vec4} {u v : DiracSpinor}
    (hu : u ≠ 0) (hv : v ≠ 0) (hp : DiracMomentum m p u) (hq : DiracMomentum m q v)
    (hpq : p ≠ q) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (α : ℝ) (x y : Vec4) :
    |chartContrast (shellPacket r s α p q u v) x y| < 4 * r * s * ‖u‖ * ‖v‖ := by
  have hle := chartContrast_shell_le hr hs α p q u v x y
  have hov : carrierOverlap u v < ‖u‖ * ‖v‖ := by
    have hprod : 0 < ‖u‖ * ‖v‖ :=
      mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
    have hF := massShell_fidelity_lt_one hm hu hv hp hq hpq
    rw [carrierFidelity, div_lt_one hprod] at hF
    exact hF
  have h4 : 0 < 4 * r * s := by positivity
  have hceil : 4 * r * s * carrierOverlap u v < 4 * r * s * ‖u‖ * ‖v‖ := by
    calc
      4 * r * s * carrierOverlap u v < 4 * r * s * (‖u‖ * ‖v‖) :=
        mul_lt_mul_of_pos_left hov h4
      _ = 4 * r * s * ‖u‖ * ‖v‖ := by ring
  exact lt_of_le_of_lt hle hceil

/-! ### The mass-3 shell, in three readings -/

theorem shellVisibility_nonneg (r s : ℝ) (u v : DiracSpinor) :
    0 ≤ shellVisibility r s u v := by
  unfold shellVisibility shellWeight carrierOverlap
  exact div_nonneg (by positivity)
    (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

private theorem equal_norm_of_sq {u v : DiracSpinor} (h : ‖u‖ ^ 2 = ‖v‖ ^ 2) :
    ‖u‖ = ‖v‖ :=
  (sq_eq_sq₀ (norm_nonneg u) (norm_nonneg v)).mp h

theorem shellRest_visibility :
    shellVisibility 1 1 shellParticleP shellParticleQ = 9 / 25 := by
  have hsq : shellVisibility 1 1 shellParticleP shellParticleQ ^ 2 = (9 / 25) ^ 2 := by
    rw [← shellInformation, shellRest_information.1]
    norm_num
  exact (sq_eq_sq₀ (shellVisibility_nonneg 1 1 shellParticleP shellParticleQ)
    (by norm_num : (0 : ℝ) ≤ 9 / 25)).mp hsq

theorem shellRest_deficit : shellDeficit 1 1 shellParticleP shellParticleQ = 544 / 625 := by
  unfold shellDeficit
  rw [shellRest_fidelity]
  simp only [abs_one, one_mul]
  rw [shellRest_information.2.1]
  norm_num

theorem shellRest_which : whichMomentum ‖shellParticleP‖ ‖shellParticleQ‖ = 0 := by
  have hnorm := shellRest_norms
  rw [equal_norm_of_sq (hnorm.1.trans hnorm.2.symm)]
  exact whichMomentum_equal ‖shellParticleQ‖

theorem shellRest_split :
    whichMomentum ‖shellParticleP‖ ‖shellParticleQ‖ = 0 ∧
      shellVisibility 1 1 shellParticleP shellParticleQ = 9 / 25 ∧
        shellDeficit 1 1 shellParticleP shellParticleQ = 544 / 625 ∧
          whichMomentum ‖shellParticleP‖ ‖shellParticleQ‖ ^ 2 +
              shellInformation 1 1 shellParticleP shellParticleQ +
                shellDeficit 1 1 shellParticleP shellParticleQ =
            1 := by
  refine ⟨shellRest_which, shellRest_visibility, shellRest_deficit, ?_⟩
  have hden : (|1| * ‖shellParticleP‖) ^ 2 + (|1| * ‖shellParticleQ‖) ^ 2 ≠ 0 := by
    simp only [abs_one, one_mul]
    rw [shellRest_norms.1, shellRest_norms.2]
    norm_num
  have hid := which_shell_deficit 1 1 shellParticleP shellParticleQ hden
  simpa [abs_one, one_mul] using hid

theorem shellLab_which : whichMomentum ‖shellParticleP‖ ‖shellLabSpinor‖ = 8 / 17 := by
  unfold whichMomentum
  rw [shellRest_norms.1, shellLab_norm]
  norm_num

theorem shellLab_deficit : shellDeficit 1 1 shellParticleP shellLabSpinor = 81 / 289 := by
  unfold shellDeficit
  rw [shellLab_fidelity]
  simp only [abs_one, one_mul]
  rw [shellLab_weightInformation]
  norm_num

theorem shellLab_split :
    whichMomentum ‖shellParticleP‖ ‖shellLabSpinor‖ = 8 / 17 ∧
      shellVisibility 1 1 shellParticleP shellLabSpinor = 12 / 17 ∧
        shellDeficit 1 1 shellParticleP shellLabSpinor = 81 / 289 ∧
          ((8 : ℝ) / 17) ^ 2 + (12 / 17) ^ 2 + (81 / 289) = 1 := by
  have hV : shellVisibility 1 1 shellParticleP shellLabSpinor = 12 / 17 :=
    shellLab_time_ratio.2.1
  have hsum : ((8 : ℝ) / 17) ^ 2 + (12 / 17) ^ 2 + (81 / 289) = 1 := by norm_num
  exact ⟨shellLab_which, hV, shellLab_deficit, hsum⟩

theorem shellOrth_deficit :
    ‖shellOrthQ‖ ^ 2 = 50 / 9 ∧
      whichMomentum ‖shellParticleP‖ ‖shellOrthQ‖ = 0 ∧
        shellInformation 1 1 shellParticleP shellOrthQ = 0 ∧
          shellDeficit 1 1 shellParticleP shellOrthQ = 1 := by
  have hnorm : ‖shellParticleP‖ = ‖shellOrthQ‖ :=
    equal_norm_of_sq (shellRest_norms.1.trans shellOrth_norm.symm)
  have hne : ‖shellOrthQ‖ ≠ 0 := by
    intro h
    have : ‖shellOrthQ‖ ^ 2 = 0 := by simp [h]
    linarith [shellOrth_norm]
  refine ⟨shellOrth_norm, ?_, orthogonal_shellInformation shellOrth_inner 1 1, ?_⟩
  · rw [hnorm]
    exact whichMomentum_equal ‖shellOrthQ‖
  · unfold shellDeficit carrierFidelity carrierOverlap
    rw [shellOrth_inner, hnorm]
    simp only [norm_zero, zero_div, abs_one, one_mul]
    have hcoeff : (1 - (0 : ℝ) ^ 2) = 1 := by norm_num
    rw [hcoeff, one_mul]
    exact phaseInformation_equal hne

end Logic

end DstDiophantine
