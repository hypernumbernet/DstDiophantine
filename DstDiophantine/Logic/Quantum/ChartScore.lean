import DstDiophantine.Logic.Quantum.ChartFisher

/-!
# The position operator and the displacement score

`chartFisher` is the Fisher information of a displacement along one chart axis. It is not a
reading of `positionOp`. On a nonzero sample the axis velocity splits into a ray and a horizontal
vector.

`positionOp` multiplies the sample by the coordinate, so it lies on the ray. The displacement
score is twice the horizontal part, the pure-state symmetric logarithmic derivative applied to
the sample. It is orthogonal to the state. Its squared length is `chartFisher` times the Born
density. The common-phase rate `p μ` drops out, and a vanishing momentum split `q − p` makes the
score zero.

The two vectors are scalar multiples only in a degenerate case. When the coordinate and the chart
Fisher information are both nonzero, the position vector meets the state and the score does not.
A zero coordinate with positive Fisher information makes `positionOp` zero and the score nonzero.
Zero Fisher information with a nonzero coordinate does the reverse.

Mean rest, mass 3, origin, axis `1`, quadrature: the position reads `0` and the score length
squared is `139264/225`. At time `1` the score is `0` and the position reads `1`. Rest against
`(5, 4, 0, 0)` at time `-π/2`: the position reads `-π/2` and the score length squared is `144/5`,
and the two vectors are not scalar multiples. The opposite Weyl seed at the origin reads position
`0` and score length squared `6400/9`. One momentum has score `0` and position `1`.
-/

namespace DstDiophantine

namespace Logic

open Complex InnerProductSpace

/-! ### The score is twice the horizontal velocity -/

/-- Component of `v` orthogonal to `ψ`. -/
noncomputable def horizontalPart (ψ v : DiracSpinor) : DiracSpinor :=
  v - (inner ℂ ψ v * ((‖ψ‖ ^ 2 : ℝ) : ℂ)⁻¹) • ψ

/-- Displacement score: twice the horizontal axis velocity. -/
noncomputable def chartScore (r s : ℝ) (u v : DiracSpinor) (φ θ speed rel : ℝ) : DiracSpinor :=
  (2 : ℂ) • horizontalPart (chartState r s u v φ θ) (chartVelocity r s u v φ θ speed rel)

theorem horizontalPart_ortho {ψ : DiracSpinor} (hψ : ψ ≠ 0) (v : DiracSpinor) :
    inner ℂ ψ (horizontalPart ψ v) = 0 := by
  have hn : ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  unfold horizontalPart
  rw [inner_sub_right, inner_smul_right]
  have hself : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (ofReal_pow ‖ψ‖ 2).symm
  rw [hself, mul_assoc, inv_mul_cancel₀ hn, mul_one, sub_self]

theorem horizontalPart_add_smul (ψ w : DiracSpinor) (c : ℂ) :
    horizontalPart ψ (c • ψ + w) = horizontalPart ψ w := by
  unfold horizontalPart
  by_cases hψ : ψ = 0
  · simp [hψ]
  · have hn : ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [ofReal_ne_zero]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
    have hself : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      exact (ofReal_pow ‖ψ‖ 2).symm
    rw [inner_add_right, inner_smul_right, hself]
    have hcoe : (c * ((‖ψ‖ ^ 2 : ℝ) : ℂ) + inner ℂ ψ w) * ((‖ψ‖ ^ 2 : ℝ) : ℂ)⁻¹ =
        c + inner ℂ ψ w * ((‖ψ‖ ^ 2 : ℝ) : ℂ)⁻¹ := by
      rw [add_mul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
    rw [hcoe, add_smul]
    abel

theorem horizontalPart_normSq {ψ : DiracSpinor} (hψ : ψ ≠ 0) (v : DiracSpinor) :
    ‖horizontalPart ψ v‖ ^ 2 * ‖ψ‖ ^ 2 =
      ‖v‖ ^ 2 * ‖ψ‖ ^ 2 - ‖inner ℂ ψ v‖ ^ 2 := by
  have hn0 : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hn : ‖ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn0
  set n : ℝ := ‖ψ‖ ^ 2 with hn_def
  set α : ℂ := inner ℂ ψ v with hα_def
  set c : ℂ := α * (n : ℂ)⁻¹ with hc_def
  have hh : horizontalPart ψ v = v - c • ψ := by
    rw [horizontalPart, hc_def, hα_def, hn_def]
  have hinner : inner ℂ v (c • ψ) = c * starRingEnd ℂ α := by
    rw [inner_smul_right, ← inner_conj_symm, hα_def]
  have hnorm : ‖c • ψ‖ ^ 2 = ‖α‖ ^ 2 / n := by
    rw [norm_smul, mul_pow]
    have hn_nonneg : 0 ≤ n := by
      rw [hn_def]
      exact sq_nonneg ‖ψ‖
    have hc : ‖c‖ ^ 2 = ‖α‖ ^ 2 / n ^ 2 := by
      rw [hc_def, norm_mul, mul_pow, norm_inv]
      have hnrm : ‖(n : ℂ)‖ = n := (RCLike.norm_ofReal n).trans (abs_of_nonneg hn_nonneg)
      rw [hnrm]
      ring
    rw [hc, hn_def]
    field_simp [hn]
  have hre : RCLike.re (c * starRingEnd ℂ α) = ‖α‖ ^ 2 / n := by
    rw [RCLike.re_eq_complex_re]
    have hmul : c * starRingEnd ℂ α = ((‖α‖ ^ 2 / n : ℝ) : ℂ) := by
      rw [hc_def]
      have hcomm : (α * (n : ℂ)⁻¹) * starRingEnd ℂ α =
          (α * starRingEnd ℂ α) * (n : ℂ)⁻¹ := by ring
      rw [hcomm]
      have hsq : α * starRingEnd ℂ α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, starRingEnd_apply, star_def, ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_eq_norm_sq]
      rw [hsq, ← ofReal_inv, ← ofReal_mul]
      congr 1
    rw [hmul, ofReal_re]
  rw [hh, norm_sub_sq (𝕜 := ℂ), hinner, hre, hnorm]
  have hlin : ‖v‖ ^ 2 - 2 * (‖α‖ ^ 2 / n) + ‖α‖ ^ 2 / n = ‖v‖ ^ 2 - ‖α‖ ^ 2 / n := by
    ring
  rw [hlin, sub_mul, div_mul_cancel₀ _ hn]

theorem chartVelocity_eq_ray (r s : ℝ) (u v : DiracSpinor) (φ θ speed rel : ℝ) :
    chartVelocity r s u v φ θ speed rel =
      (I * (speed : ℂ)) • chartState r s u v φ θ +
        ((rel : ℂ) * exp (I * (φ : ℂ))) • phaseCurveDeriv r s u v θ := by
  unfold chartVelocity chartState
  have hcoe : I * (speed : ℂ) * exp (I * (φ : ℂ)) =
      (I * (speed : ℂ)) * exp (I * (φ : ℂ)) := by ring
  rw [hcoe, smul_smul]

theorem chartScore_speed_invariant (r s : ℝ) (u v : DiracSpinor) (φ θ speed rel : ℝ) :
    chartScore r s u v φ θ speed rel = chartScore r s u v φ θ 0 rel := by
  unfold chartScore
  rw [chartVelocity_eq_ray, chartVelocity_eq_ray]
  have hray : (I * ((0 : ℝ) : ℂ)) • chartState r s u v φ θ = 0 := by simp
  rw [hray, zero_add]
  exact congrArg (fun w => (2 : ℂ) • w)
    (horizontalPart_add_smul (chartState r s u v φ θ)
      (((rel : ℂ) * exp (I * (φ : ℂ))) • phaseCurveDeriv r s u v θ) (I * (speed : ℂ)))

theorem chartScore_of_zero_rel (r s : ℝ) (u v : DiracSpinor) (φ θ speed : ℝ) :
    chartScore r s u v φ θ speed 0 = 0 := by
  rw [chartScore_speed_invariant]
  unfold chartScore chartVelocity horizontalPart
  simp

theorem chartScore_ortho (r s : ℝ) (u v : DiracSpinor) (φ θ speed rel : ℝ)
    (hψ : chartState r s u v φ θ ≠ 0) :
    inner ℂ (chartState r s u v φ θ) (chartScore r s u v φ θ speed rel) = 0 := by
  unfold chartScore
  rw [inner_smul_right, horizontalPart_ortho hψ, mul_zero]

theorem chartScore_normSq (r s : ℝ) (u v : DiracSpinor) (φ θ speed : ℝ) (δ : Vec4) (μ : Fin 4)
    (hden : phaseCurveNormSq r s u v θ ≠ 0) :
    ‖chartScore r s u v φ θ speed (δ μ)‖ ^ 2 =
      chartFisher r s u v δ μ θ * ‖chartState r s u v φ θ‖ ^ 2 := by
  have hsq : ‖chartState r s u v φ θ‖ ^ 2 = phaseCurveNormSq r s u v θ :=
    chartState_normSq r s u v φ θ
  have hstate : chartState r s u v φ θ ≠ 0 := by
    intro hz
    apply hden
    rw [← hsq, hz, norm_zero]
    simp
  have hn : ‖chartState r s u v φ θ‖ ^ 2 ≠ 0 := by
    rw [hsq]
    exact hden
  have hn4 : ‖chartState r s u v φ θ‖ ^ 4 ≠ 0 := by
    have : ‖chartState r s u v φ θ‖ ^ 4 = (‖chartState r s u v φ θ‖ ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_ne_zero 2 hn
  have hproj :=
    horizontalPart_normSq hstate (chartVelocity r s u v φ θ speed (δ μ))
  have hF := chartFisher_eq_velocity r s u v φ θ speed δ μ hden
  rw [← hproj, div_eq_iff hn4] at hF
  unfold chartScore
  rw [norm_smul, mul_pow]
  have htwo : ‖(2 : ℂ)‖ ^ 2 = 4 := by norm_num
  rw [htwo]
  have hassoc : 4 * (‖horizontalPart (chartState r s u v φ θ)
        (chartVelocity r s u v φ θ speed (δ μ))‖ ^ 2 * ‖chartState r s u v φ θ‖ ^ 2) =
      (4 * ‖horizontalPart (chartState r s u v φ θ)
        (chartVelocity r s u v φ θ speed (δ μ))‖ ^ 2) * ‖chartState r s u v φ θ‖ ^ 2 := by
    ring
  have hpow : ‖chartState r s u v φ θ‖ ^ 4 =
      ‖chartState r s u v φ θ‖ ^ 2 * ‖chartState r s u v φ θ‖ ^ 2 := by ring
  rw [hassoc, hpow] at hF
  have hright : chartFisher r s u v δ μ θ *
        (‖chartState r s u v φ θ‖ ^ 2 * ‖chartState r s u v φ θ‖ ^ 2) =
      (chartFisher r s u v δ μ θ * ‖chartState r s u v φ θ‖ ^ 2) *
        ‖chartState r s u v φ θ‖ ^ 2 := by ring
  rw [hright] at hF
  exact mul_right_cancel₀ hn hF

/-! ### Position multiplies by the coordinate -/

theorem positionOp_inner (μ : Fin 4) (Ψ : Vec4 → DiracSpinor) (x : Vec4) :
    inner ℂ (Ψ x) (positionOp μ Ψ x) = (x μ : ℂ) * ((‖Ψ x‖ ^ 2 : ℝ) : ℂ) := by
  rw [positionOp, inner_smul_right, inner_self_eq_norm_sq_to_K]
  congr 1
  exact (ofReal_pow ‖Ψ x‖ 2).symm

theorem position_reading {Ψ : Vec4 → DiracSpinor} {μ : Fin 4} {x : Vec4} (hΨ : Ψ x ≠ 0) :
    (inner ℂ (Ψ x) (positionOp μ Ψ x)).re / ‖Ψ x‖ ^ 2 = x μ := by
  rw [positionOp_inner]
  have hre : ((x μ : ℂ) * ((‖Ψ x‖ ^ 2 : ℝ) : ℂ)).re = x μ * ‖Ψ x‖ ^ 2 := by
    rw [← ofReal_mul, ofReal_re]
  rw [hre]
  exact mul_div_cancel_right₀ (x μ) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hΨ))

theorem positionOp_of_coord_zero {μ : Fin 4} {x : Vec4} (hx : x μ = 0) (Ψ : Vec4 → DiracSpinor) :
    positionOp μ Ψ x = 0 := by
  rw [positionOp, hx, ofReal_zero, zero_smul]

theorem positionOp_ne_zero_of_coord {Ψ : Vec4 → DiracSpinor} {μ : Fin 4} {x : Vec4}
    (hΨ : Ψ x ≠ 0) (hx : x μ ≠ 0) : positionOp μ Ψ x ≠ 0 := by
  rw [positionOp]
  intro hz
  rcases smul_eq_zero.mp hz with h0 | hψ
  · exact hx (ofReal_eq_zero.mp h0)
  · exact hΨ hψ

/-- Score of the shell packet under a displacement along axis `μ`. -/
noncomputable def packetScore (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) : DiracSpinor :=
  chartScore r s u v (wavePhase p x) (wavePhase (q - p) x + α) (p μ) ((q - p) μ)

theorem packetScore_ortho (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4) (x : Vec4)
    (hψ : shellPacket r s α p q u v x ≠ 0) :
    inner ℂ (shellPacket r s α p q u v x) (packetScore r s α p q u v μ x) = 0 := by
  have hstate : chartState r s u v (wavePhase p x) (wavePhase (q - p) x + α) ≠ 0 := by
    rwa [← shellPacket_eq_chartState]
  rw [shellPacket_eq_chartState, packetScore]
  exact chartScore_ortho r s u v (wavePhase p x) (wavePhase (q - p) x + α) (p μ) ((q - p) μ)
    hstate

theorem packetScore_normSq (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4) (x : Vec4)
    (hψ : shellPacket r s α p q u v x ≠ 0) :
    ‖packetScore r s α p q u v μ x‖ ^ 2 =
      chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) *
        bornDensity (shellPacket r s α p q u v) x := by
  have hden : phaseCurveNormSq r s u v (wavePhase (q - p) x + α) ≠ 0 := by
    intro hz
    apply hψ
    have hborn : bornDensity (shellPacket r s α p q u v) x = 0 := by
      rw [bornDensity_eq_phaseCurveNormSq, hz]
    rw [bornDensity, sq_eq_zero_iff, norm_eq_zero] at hborn
    exact hborn
  rw [packetScore, chartScore_normSq r s u v (wavePhase p x) (wavePhase (q - p) x + α) (p μ)
      (q - p) μ hden, chartState_normSq, ← bornDensity_eq_phaseCurveNormSq]

theorem packetScore_eq_zero_of_chartFisher (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0)
    (hF : chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) = 0) :
    packetScore r s α p q u v μ x = 0 := by
  have h := packetScore_normSq r s α p q u v μ x hψ
  rw [hF, zero_mul] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

theorem packetScore_ne_zero_of_chartFisher (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0)
    (hF : chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) ≠ 0) :
    packetScore r s α p q u v μ x ≠ 0 := by
  intro hz
  have h := packetScore_normSq r s α p q u v μ x hψ
  rw [hz, norm_zero] at h
  have hzero : chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) *
      bornDensity (shellPacket r s α p q u v) x = 0 := by
    simpa [sq] using h.symm
  have hden : bornDensity (shellPacket r s α p q u v) x ≠ 0 := by
    rw [bornDensity]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  exact hF ((mul_eq_zero.mp hzero).resolve_right hden)

theorem packetScore_of_zero_split {r s α : ℝ} {p q : Vec4} {u v : DiracSpinor} {μ : Fin 4}
    {x : Vec4} (hμ : (q - p) μ = 0) : packetScore r s α p q u v μ x = 0 := by
  unfold packetScore
  rw [hμ]
  exact chartScore_of_zero_rel r s u v (wavePhase p x) (wavePhase (q - p) x + α) (p μ)

theorem positionOp_ne_smul_packetScore (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0)
    (hF : chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) ≠ 0) (hx : x μ ≠ 0) :
    ∀ c : ℂ, positionOp μ (shellPacket r s α p q u v) x ≠ c • packetScore r s α p q u v μ x := by
  intro c h
  have _hscore := packetScore_ne_zero_of_chartFisher r s α p q u v μ x hψ hF
  have hinner := congrArg (fun w => inner ℂ (shellPacket r s α p q u v x) w) h
  rw [positionOp_inner, inner_smul_right, packetScore_ortho r s α p q u v μ x hψ, mul_zero]
    at hinner
  have hn : ((‖shellPacket r s α p q u v x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  exact hx (ofReal_eq_zero.mp ((mul_eq_zero.mp hinner).resolve_right hn))

/-- On a nonzero sample the score is orthogonal to the state and the position operator is the
coordinate times the state. The squared score length is the chart Fisher information times the
Born density. -/
theorem positionOp_score_split (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) :
    inner ℂ (shellPacket r s α p q u v x) (packetScore r s α p q u v μ x) = 0 ∧
      inner ℂ (shellPacket r s α p q u v x) (positionOp μ (shellPacket r s α p q u v) x) =
        (x μ : ℂ) * (bornDensity (shellPacket r s α p q u v) x : ℂ) ∧
        ‖packetScore r s α p q u v μ x‖ ^ 2 =
          chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) *
            bornDensity (shellPacket r s α p q u v) x ∧
          ((chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) ≠ 0 ∧ x μ ≠ 0) →
            ∀ c : ℂ,
              positionOp μ (shellPacket r s α p q u v) x ≠ c • packetScore r s α p q u v μ x) ∧
            ((x μ = 0 ∧ chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) ≠ 0) →
              positionOp μ (shellPacket r s α p q u v) x = 0 ∧
                packetScore r s α p q u v μ x ≠ 0) ∧
              ((chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) = 0 ∧ x μ ≠ 0) →
                packetScore r s α p q u v μ x = 0 ∧
                  positionOp μ (shellPacket r s α p q u v) x ≠ 0) := by
  refine ⟨packetScore_ortho r s α p q u v μ x hψ, ?_, packetScore_normSq r s α p q u v μ x hψ,
      ?_, ?_, ?_⟩
  · rw [positionOp_inner, bornDensity]
  · intro ⟨hF, hx⟩
    exact positionOp_ne_smul_packetScore r s α p q u v μ x hψ hF hx
  · intro ⟨hx, hF⟩
    exact ⟨positionOp_of_coord_zero hx _,
      packetScore_ne_zero_of_chartFisher r s α p q u v μ x hψ hF⟩
  · intro ⟨hF, hx⟩
    exact ⟨packetScore_eq_zero_of_chartFisher r s α p q u v μ x hψ hF,
      positionOp_ne_zero_of_coord hψ hx⟩

/-! ### Mass 3 -/

theorem shellRest_origin_score :
    ∃ θ : ℝ,
      let Ψ := shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
      phaseCross 1 1 shellParticleP shellParticleQ θ = 0 ∧
        bornDensity Ψ 0 = 100 / 9 ∧
          positionOp 1 Ψ 0 = 0 ∧
            ‖packetScore 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 1 0‖ ^ 2 =
              139264 / 225 ∧
              inner ℂ (Ψ 0) (packetScore 1 1 θ shellRestP shellRestQ
                shellParticleP shellParticleQ 1 0) = 0 := by
  obtain ⟨θ, hcross, _, _, hF⟩ := shellRest_chartFisher.1
  refine ⟨θ, hcross, ?_, ?_, ?_, ?_⟩
  · have hW : phaseCurveNormSq 1 1 shellParticleP shellParticleQ θ = 100 / 9 := by
      unfold phaseCurveNormSq
      rw [hcross, bornWeight_eq, bornWeight_eq]
      simp only [abs_one, one_mul, shellRest_norms.1, shellRest_norms.2]
      norm_num
    rw [bornDensity_eq_phaseCurveNormSq, wavePhase_zero, zero_add, hW]
  · exact positionOp_of_coord_zero (by simp) _
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    have hnorm := packetScore_normSq 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 1 0
      hψ
    have hphase : wavePhase (shellRestQ - shellRestP) 0 + θ = θ := by
      rw [wavePhase_zero, zero_add]
    rw [hphase, hF] at hnorm
    have hborn : bornDensity (shellPacket 1 1 θ shellRestP shellRestQ shellParticleP
        shellParticleQ) 0 = 100 / 9 := by
      have hW : phaseCurveNormSq 1 1 shellParticleP shellParticleQ θ = 100 / 9 := by
        unfold phaseCurveNormSq
        rw [hcross, bornWeight_eq, bornWeight_eq]
        simp only [abs_one, one_mul, shellRest_norms.1, shellRest_norms.2]
        norm_num
      rw [bornDensity_eq_phaseCurveNormSq, wavePhase_zero, zero_add, hW]
    rw [hborn] at hnorm
    have hprod : (34816 / 625 : ℝ) * (100 / 9) = 139264 / 225 := by norm_num
    rw [← hprod]
    exact hnorm
  · exact packetScore_ortho 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 1 0
      (shellRest_packet_ne_zero θ 0)

theorem shellRest_time_score (α : ℝ) :
    let Ψ := shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ
    let x := timeShift (1 : ℝ)
    Ψ x ≠ 0 ∧
      chartFisher 1 1 shellParticleP shellParticleQ (shellRestQ - shellRestP) 0
          (wavePhase (shellRestQ - shellRestP) x + α) = 0 ∧
        packetScore 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ 0 x = 0 ∧
          (inner ℂ (Ψ x) (positionOp 0 Ψ x)).re / ‖Ψ x‖ ^ 2 = 1 := by
  intro Ψ x
  have hψ : Ψ x ≠ 0 := shellRest_packet_ne_zero α x
  refine ⟨hψ, ?_, ?_, ?_⟩
  · exact chartFisher_of_zero_component shellRest_relative.1 1 1 shellParticleP shellParticleQ _
  · exact packetScore_of_zero_split shellRest_relative.1
  · have hx : x 0 = 1 := by simp [x, timeShift, Pi.single_eq_same]
    rw [position_reading hψ, hx]

theorem shellLab_score :
    let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
    let x := timeShift (-Real.pi / 2)
    (inner ℂ (Ψ x) (positionOp 0 Ψ x)).re / ‖Ψ x‖ ^ 2 = -Real.pi / 2 ∧
      ‖packetScore 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor 0 x‖ ^ 2 =
        144 / 5 ∧
        inner ℂ (Ψ x) (packetScore 1 1 0 shellRestP (restMomentum 3) shellParticleP
          shellLabSpinor 0 x) = 0 ∧
          ∀ c : ℂ,
            positionOp 0 Ψ x ≠ c •
              packetScore 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor 0 x := by
  intro Ψ x
  have hden : bornDensity Ψ x = 20 / 9 := shellLab_time_density.2.1
  have hψ : Ψ x ≠ 0 := by
    intro hz
    have : bornDensity Ψ x = 0 := by rw [bornDensity, hz, norm_zero]; simp
    rw [hden] at this
    norm_num at this
  have hF : chartFisher 1 1 shellParticleP shellLabSpinor (restMomentum 3 - shellRestP) 0
      (wavePhase (restMomentum 3 - shellRestP) x) = 324 / 25 := shellLab_chartFisher.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hx : x 0 = -Real.pi / 2 := by simp [x, timeShift, Pi.single_eq_same]
    rw [position_reading hψ, hx]
  · have hnorm := packetScore_normSq 1 1 0 shellRestP (restMomentum 3) shellParticleP
      shellLabSpinor 0 x hψ
    have hphase : wavePhase (restMomentum 3 - shellRestP) x + 0 =
        wavePhase (restMomentum 3 - shellRestP) x := by ring
    rw [hphase, hF, hden] at hnorm
    have hprod : (324 / 25 : ℝ) * (20 / 9) = 144 / 5 := by norm_num
    rw [← hprod]
    exact hnorm
  · exact packetScore_ortho 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor 0 x hψ
  · have hx : x 0 ≠ 0 := by
      have hcoord : x 0 = -Real.pi / 2 := by simp [x, timeShift, Pi.single_eq_same]
      rw [hcoord]
      exact div_ne_zero (neg_ne_zero.mpr Real.pi_ne_zero) (by norm_num)
    have hFne : chartFisher 1 1 shellParticleP shellLabSpinor (restMomentum 3 - shellRestP) 0
        (wavePhase (restMomentum 3 - shellRestP) x + 0) ≠ 0 := by
      rw [add_zero, hF]
      norm_num
    exact positionOp_ne_smul_packetScore 1 1 0 shellRestP (restMomentum 3) shellParticleP
      shellLabSpinor 0 x hψ hFne hx

theorem phaseCross_shellOrth (θ : ℝ) : phaseCross 1 1 shellParticleP shellOrthQ θ = 0 := by
  unfold phaseCross
  rw [inner_smul_left, inner_smul_right, shellOrth_inner]
  simp

theorem shellOrth_origin_score :
    let Ψ := shellPacket 1 1 0 shellRestP shellRestQ shellParticleP shellOrthQ
    bornDensity Ψ 0 = 100 / 9 ∧
      positionOp 1 Ψ 0 = 0 ∧
        ‖packetScore 1 1 0 shellRestP shellRestQ shellParticleP shellOrthQ 1 0‖ ^ 2 = 6400 / 9 ∧
          inner ℂ (Ψ 0) (packetScore 1 1 0 shellRestP shellRestQ shellParticleP shellOrthQ 1 0) =
            0 := by
  intro Ψ
  have hW : phaseCurveNormSq 1 1 shellParticleP shellOrthQ 0 = 100 / 9 := by
    unfold phaseCurveNormSq
    rw [phaseCross_shellOrth, bornWeight_eq, bornWeight_eq]
    simp only [abs_one, one_mul, shellRest_norms.1, shellOrth_norm]
    norm_num
  have hborn : bornDensity Ψ 0 = 100 / 9 := by
    rw [bornDensity_eq_phaseCurveNormSq, wavePhase_zero, zero_add, hW]
  have hψ : Ψ 0 ≠ 0 := by
    intro hz
    have : bornDensity Ψ 0 = 0 := by rw [bornDensity, hz, norm_zero]; simp
    rw [hborn] at this
    norm_num at this
  refine ⟨hborn, positionOp_of_coord_zero (by simp) _, ?_,
      packetScore_ortho 1 1 0 shellRestP shellRestQ shellParticleP shellOrthQ 1 0 hψ⟩
  have hnorm := packetScore_normSq 1 1 0 shellRestP shellRestQ shellParticleP shellOrthQ 1 0 hψ
  have hphase : wavePhase (shellRestQ - shellRestP) 0 + 0 = 0 := by
    rw [wavePhase_zero, add_zero]
  have hF := (shellOrth_chartFisher (0 : ℝ)).2
  rw [hphase, hF, hborn] at hnorm
  have hprod : (64 : ℝ) * (100 / 9) = 6400 / 9 := by norm_num
  rw [← hprod]
  exact hnorm

theorem sameMomentum_score :
    let u : DiracSpinor := EuclideanSpace.single 0 1
    let x : Vec4 := Pi.single 1 1
    let Ψ := shellPacket 1 1 0 (0 : Vec4) 0 u u
    Ψ x ≠ 0 ∧
      chartFisher 1 1 u u (0 - 0) 1 (wavePhase (0 - 0) x) = 0 ∧
        packetScore 1 1 0 (0 : Vec4) 0 u u 1 x = 0 ∧
          (inner ℂ (Ψ x) (positionOp 1 Ψ x)).re / ‖Ψ x‖ ^ 2 = 1 := by
  intro u x Ψ
  have hinner : inner ℂ u u = 1 := by
    rw [EuclideanSpace.inner_single_left]
    simp [u]
  have hnorm : ‖u‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    calc
      ((‖u‖ ^ 2 : ℝ) : ℂ) = (‖u‖ : ℂ) ^ 2 := ofReal_pow ‖u‖ 2
      _ = inner ℂ u u := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := u)).symm
      _ = 1 := hinner
  have hcross : phaseCross 1 1 u u 0 = 1 := by
    unfold phaseCross
    rw [inner_smul_left, inner_smul_right, hinner]
    simp [Complex.exp_zero]
  have hden : phaseCurveNormSq 1 1 u u 0 = 4 := by
    unfold phaseCurveNormSq
    rw [hcross, bornWeight_eq 1 u, abs_one, one_mul, hnorm]
    norm_num
  have hphase : wavePhase ((0 : Vec4) - 0) x + 0 = 0 := by
    simp [wavePhase]
  have hψ : Ψ x ≠ 0 :=
    shellPacket_ne_zero_of_normSq (by rw [hphase, hden]; norm_num)
  refine ⟨hψ, ?_, ?_, ?_⟩
  · exact chartFisher_of_zero_component (by simp) 1 1 u u _
  · exact packetScore_of_zero_split (by simp : ((0 : Vec4) - 0) 1 = 0)
  · have hx : x 1 = 1 := by simp [x, Pi.single_eq_same]
    rw [position_reading hψ, hx]

end Logic

end DstDiophantine
