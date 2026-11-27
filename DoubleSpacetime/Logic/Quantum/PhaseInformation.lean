import DoubleSpacetime.Logic.Quantum.PositionInformation

/-!
# The relative chart phase as information

`PositionInformation` splits a two-momentum packet into which-momentum distinguishability `D` and
fringe visibility `V`, with `D² + V² = 1`. This section names the complementary number.

The share of the first momentum is `p = r² / (r² + s²)`. Its Bernoulli variance is `p(1 − p)`.
Four times that variance is the information `I` of the relative chart phase. It equals `V²`, so
`D² + I = 1`. For a pure state this `I` is the quantum Fisher information of the phase generated
by the projector onto the second momentum. `PhaseFisher.weightPhaseDerivative_generator` is that
generator, and `PhaseFisher.phaseSLD_fisher` is the symmetric logarithmic derivative: `⟨ψ, Lψ⟩ = 0`
and `⟨ψ, L²ψ⟩ = I`. On two carriers the projective Fisher information equals the carrier deficit
exactly where the interference term vanishes (`PhaseFisher.phaseFisher_quadrature`).

The number is not a location. `I` depends only on the two weights. When the two momenta coincide,
`I` may be `1` while every Born density agrees, so the chart carries no position information.
When the momenta differ and both weights are nonzero, the chart does carry that information, and
every sample is still a scalar times the one carrier spinor. Scaling that spinor multiplies every
density and does not enter `I`. A position operator on the carrier is not restored.
-/

namespace DoubleSpacetime

namespace Logic

open Complex

/-! ### Share, variance, phase information -/

/-- Share of the first momentum. The Lean zero when both weights vanish. -/
noncomputable def momentumShare (r s : ℝ) : ℝ :=
  r ^ 2 / (r ^ 2 + s ^ 2)

/-- Bernoulli variance of `momentumShare`. -/
noncomputable def momentumVariance (r s : ℝ) : ℝ :=
  momentumShare r s * (1 - momentumShare r s)

/-- Information of the relative chart phase: four times `momentumVariance`. -/
noncomputable def phaseInformation (r s : ℝ) : ℝ :=
  4 * momentumVariance r s

theorem phaseInformation_eq (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) :
    phaseInformation r s = 4 * r ^ 2 * s ^ 2 / (r ^ 2 + s ^ 2) ^ 2 := by
  unfold phaseInformation momentumVariance momentumShare
  field_simp [h]
  ring

theorem phaseInformation_nonneg (r s : ℝ) : 0 ≤ phaseInformation r s := by
  by_cases h : r ^ 2 + s ^ 2 = 0
  · unfold phaseInformation momentumVariance momentumShare
    simp [h]
  · rw [phaseInformation_eq r s h]
    exact div_nonneg (by positivity) (sq_nonneg _)

theorem phaseInformation_eq_visibility_sq (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) :
    phaseInformation r s = fringeVisibility r s ^ 2 := by
  rw [phaseInformation_eq r s h]
  unfold fringeVisibility
  rw [div_pow]
  congr 1
  ring

theorem whichMomentum_sq_add_phaseInformation (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) :
    whichMomentum r s ^ 2 + phaseInformation r s = 1 := by
  rw [phaseInformation_eq_visibility_sq r s h]
  exact whichMomentum_sq_add_fringeVisibility r s h

theorem phaseInformation_le_one (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) :
    phaseInformation r s ≤ 1 := by
  have hid := whichMomentum_sq_add_phaseInformation r s h
  have hnn : 0 ≤ whichMomentum r s ^ 2 := sq_nonneg _
  linarith

theorem phaseInformation_eq_zero_iff (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) :
    phaseInformation r s = 0 ↔ r = 0 ∨ s = 0 := by
  rw [phaseInformation_eq r s h]
  have hden : (r ^ 2 + s ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h
  rw [div_eq_zero_iff]
  constructor
  · intro h0
    rcases h0 with hnum | hbad
    · have h4 : (4 : ℝ) ≠ 0 := by norm_num
      have hprod : r ^ 2 * s ^ 2 = 0 := by
        have hmul : 4 * (r ^ 2 * s ^ 2) = 0 := by
          simpa [mul_assoc] using hnum
        exact (mul_eq_zero.mp hmul).resolve_left h4
      rcases mul_eq_zero.mp hprod with hr | hs
      · exact Or.inl (sq_eq_zero_iff.mp hr)
      · exact Or.inr (sq_eq_zero_iff.mp hs)
    · exact absurd hbad hden
  · intro hrs
    refine Or.inl ?_
    rcases hrs with hr | hs
    · simp [hr]
    · simp [hs]

theorem whichMomentum_nonneg (r s : ℝ) : 0 ≤ whichMomentum r s := by
  unfold whichMomentum
  exact div_nonneg (abs_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem whichMomentum_eq_one_iff (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) :
    whichMomentum r s = 1 ↔ phaseInformation r s = 0 := by
  have hid := whichMomentum_sq_add_phaseInformation r s h
  constructor
  · intro hD
    have : (1 : ℝ) ^ 2 + phaseInformation r s = 1 := by simpa [hD] using hid
    linarith
  · intro hI
    have hsq : whichMomentum r s ^ 2 = 1 := by simpa [hI] using hid
    rcases sq_eq_one_iff.mp hsq with h1 | hm1
    · exact h1
    · linarith [whichMomentum_nonneg r s, hm1]

theorem phaseInformation_definite (r : ℝ) : phaseInformation r 0 = 0 := by
  by_cases hr : r = 0
  · unfold phaseInformation momentumVariance momentumShare
    simp [hr]
  · have hden : r ^ 2 + 0 ^ 2 ≠ 0 := by simpa using pow_ne_zero 2 hr
    rw [phaseInformation_eq r 0 hden]
    simp

theorem phaseInformation_equal {r : ℝ} (hr : r ≠ 0) : phaseInformation r r = 1 := by
  have hden : r ^ 2 + r ^ 2 ≠ 0 := by
    have hrw : r ^ 2 + r ^ 2 = 2 * r ^ 2 := by ring
    rw [hrw]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
  rw [phaseInformation_eq_visibility_sq r r hden, fringeVisibility_equal hr]
  norm_num

theorem half_weight_phaseInformation :
    phaseInformation 1 (1 / 2) = 16 / 25 ∧
      whichMomentum 1 (1 / 2) ^ 2 + phaseInformation 1 (1 / 2) = 1 := by
  have hden : (1 : ℝ) ^ 2 + (1 / 2) ^ 2 ≠ 0 := by norm_num
  refine ⟨?_, whichMomentum_sq_add_phaseInformation 1 (1 / 2) hden⟩
  rw [phaseInformation_eq_visibility_sq 1 (1 / 2) hden, half_weight_information.2.1]
  norm_num

/-! ### The sample stays on one carrier ray -/

theorem phasedPacket_eq_smul (r s α : ℝ) (p q : Vec4) (u : DiracSpinor) (x : Vec4) :
    phasedPacket r s α p q u x =
      ((r : ℂ) * exp (I * (wavePhase p x : ℂ)) +
        (s : ℂ) * exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ))) • u := by
  unfold phasedPacket planeWave
  rw [smul_smul, smul_smul, ← add_smul]

theorem bornDensity_phasedPacket_smul (c : ℂ) (r s α : ℝ) (p q : Vec4) (u : DiracSpinor)
    (x : Vec4) :
    bornDensity (phasedPacket r s α p q (c • u)) x =
      ‖c‖ ^ 2 * bornDensity (phasedPacket r s α p q u) x := by
  rw [bornDensity_phasedPacket, bornDensity_phasedPacket, norm_smul, mul_pow]
  ring

/-- The carrier scale multiplies every density and does not enter the phase information. -/
theorem carrier_scale_drops_out (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) (c : ℂ) :
    phaseInformation r s = fringeVisibility r s ^ 2 ∧
      ∀ (α : ℝ) (p q : Vec4) (u : DiracSpinor) (x : Vec4),
        bornDensity (phasedPacket r s α p q (c • u)) x =
          ‖c‖ ^ 2 * bornDensity (phasedPacket r s α p q u) x :=
  ⟨phaseInformation_eq_visibility_sq r s h,
    fun α p q u x => bornDensity_phasedPacket_smul c r s α p q u x⟩

/-! ### The weight formula is not a chart location -/

theorem bornDensity_phasedPacket_sameMomentum (r s α : ℝ) (p : Vec4) (u : DiracSpinor)
    (x y : Vec4) :
    bornDensity (phasedPacket r s α p p u) x =
      bornDensity (phasedPacket r s α p p u) y := by
  rw [bornDensity_phasedPacket, bornDensity_phasedPacket]
  have hphase : ∀ z : Vec4, wavePhase (p - p) z = 0 := by
    intro z
    simp [wavePhase, sub_self]
  rw [hphase x, hphase y]

theorem sameMomentum_no_chartPositionInfo (r s α : ℝ) (p : Vec4) (u : DiracSpinor) :
    ¬ ChartPositionInfo (phasedPacket r s α p p u) := by
  intro ⟨x, y, hxy⟩
  exact hxy (bornDensity_phasedPacket_sameMomentum r s α p u x y)

/-- Full phase information of the weights, and no chart-position information. -/
theorem phaseInformation_not_a_location {r : ℝ} (hr : r ≠ 0) (α : ℝ) (p : Vec4)
    (u : DiracSpinor) :
    phaseInformation r r = 1 ∧ ¬ ChartPositionInfo (phasedPacket r r α p p u) :=
  ⟨phaseInformation_equal hr, sameMomentum_no_chartPositionInfo r r α p u⟩

theorem both_weights_chartPositionInfo {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) {p q : Vec4}
    (hpq : p ≠ q) {u : DiracSpinor} (hu : u ≠ 0) (α : ℝ) :
    ChartPositionInfo (phasedPacket r s α p q u) := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  obtain ⟨x, hx⟩ := exists_wavePhase_eq hδ (-α)
  obtain ⟨y, hy⟩ := exists_wavePhase_eq hδ (Real.pi - α)
  have hx0 : -α + α = 0 := by ring
  have hyπ : Real.pi - α + α = Real.pi := by ring
  refine ⟨x, y, ?_⟩
  intro hden
  have hxden : bornDensity (phasedPacket r s α p q u) x =
      (r ^ 2 + s ^ 2 + 2 * r * s) * ‖u‖ ^ 2 := by
    rw [bornDensity_phasedPacket, hx, hx0, Real.cos_zero]
    ring
  have hyden : bornDensity (phasedPacket r s α p q u) y =
      (r ^ 2 + s ^ 2 - 2 * r * s) * ‖u‖ ^ 2 := by
    rw [bornDensity_phasedPacket, hy, hyπ, Real.cos_pi]
    ring
  have hdiff : bornDensity (phasedPacket r s α p q u) x -
      bornDensity (phasedPacket r s α p q u) y = 4 * r * s * ‖u‖ ^ 2 := by
    rw [hxden, hyden]
    ring
  rw [hden, sub_self] at hdiff
  have hN : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have hne : 4 * r * s * ‖u‖ ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hr) hs) hN
  exact absurd hdiff.symm hne

/-- Distinct momenta make the phase information a chart reading, on one carrier ray. -/
theorem chart_reads_phaseInformation {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) {p q : Vec4}
    (hpq : p ≠ q) {u : DiracSpinor} (hu : u ≠ 0) (α : ℝ) :
    0 < phaseInformation r s ∧
      phaseInformation r s ≤ 1 ∧
        whichMomentum r s ^ 2 + phaseInformation r s = 1 ∧
          ChartPositionInfo (phasedPacket r s α p q u) ∧
            ∀ x, ∃ z : ℂ, phasedPacket r s α p q u x = z • u := by
  have hden : r ^ 2 + s ^ 2 ≠ 0 := by
    intro h
    have hr0 : r ^ 2 = 0 := by nlinarith [sq_nonneg s]
    exact hr (sq_eq_zero_iff.mp hr0)
  have hpos : 0 < phaseInformation r s := by
    rw [phaseInformation_eq r s hden]
    refine div_pos ?_ (pow_pos (lt_of_le_of_ne (add_nonneg (sq_nonneg r) (sq_nonneg s))
      (Ne.symm hden)) 2)
    positivity
  refine ⟨hpos, phaseInformation_le_one r s hden,
    whichMomentum_sq_add_phaseInformation r s hden,
    both_weights_chartPositionInfo hr hs hpq hu α, fun x => ?_⟩
  exact ⟨_, phasedPacket_eq_smul r s α p q u x⟩

theorem definite_momentum_zero_phaseInformation {r : ℝ} (hr : r ≠ 0) (α : ℝ) (p q : Vec4)
    (u : DiracSpinor) :
    phaseInformation r 0 = 0 ∧
      whichMomentum r 0 = 1 ∧
        ¬ ChartPositionInfo (phasedPacket r 0 α p q u) ∧
          ∀ x, ∃ z : ℂ, phasedPacket r 0 α p q u x = z • u :=
  ⟨phaseInformation_definite r, whichMomentum_definite hr,
    phasedPacket_definite_no_chartPositionInfo r α p q u,
    fun x => ⟨_, phasedPacket_eq_smul r 0 α p q u x⟩⟩

theorem axis_fringe_phaseInformation :
    phaseInformation 1 1 = 1 ∧
      chartContrast
        (phasedPacket 1 1 0 (0 : Vec4) (Pi.single 1 (1 : ℝ))
          (EuclideanSpace.single 0 (1 : ℂ)))
        0 (Pi.single 1 Real.pi) = 4 :=
  ⟨phaseInformation_equal (by norm_num), axis_fringe_full_visibility.2⟩

end Logic

end DoubleSpacetime
