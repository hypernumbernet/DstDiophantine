import DoubleSpacetime.Logic.Quantum.ChartScore

/-!
# The momentum operator on a shell packet

`positionOp` multiplies a sample by the coordinate, so it lies on the ray. `momentumOp` does not.
On a shell packet the axis derivative is `chartVelocity`, and `P_μ = -i ∂_μ`, so

`momentumOp μ Ψ = (p μ) • Ψ + (-i (q − p) μ) • (common phase • phaseCurveDeriv)`.

The part orthogonal to the sample is `-i/2` times the displacement score. Its squared length is
`chartFisher` times the Born density, divided by `4`. A vanishing momentum split makes the sample
an eigen-sample of value `p μ`. A positive chart Fisher information means it is not an
eigen-sample.

The Rayleigh quotient `⟨Ψ, P_μ Ψ⟩ / ‖Ψ‖²` is not an L² expectation. Its real part is the
interference-weighted momentum. Its imaginary part is the momentum split times the imaginary
overlap, divided by the Born density. The quotient can vanish while `momentumOp` does not.

Mean rest, mass 3, quadrature, origin: axis `1` has real part `0`, imaginary part squared
`(36/25)²`, and horizontal length squared `34816/225`. The time axis is the eigen-sample `5 • Ψ`.
Rest against `(5, 4, 0, 0)` at time `-π/2`: the quotient is `28/5` and the horizontal length
squared is `36/5`, while the position reads `-π/2`. The opposite Weyl seed at the origin has
quotient `0`, momentum operator nonzero, and horizontal length squared `1600/9`. One momentum is
the eigen-sample of that momentum. The zero-momentum packet has `momentumOp = 0` and position `1`.
-/

namespace DoubleSpacetime

namespace Logic

open Complex InnerProductSpace

/-! ### Pointwise quotient and horizontal part -/

/-- Rayleigh quotient of `momentumOp` on one sample. -/
noncomputable def momentumQuotient (μ : Fin 4) (Ψ : Vec4 → DiracSpinor) (x : Vec4) : ℂ :=
  inner ℂ (Ψ x) (momentumOp μ Ψ x) * ((‖Ψ x‖ ^ 2 : ℝ) : ℂ)⁻¹

/-- Component of `momentumOp` orthogonal to the sample. -/
noncomputable def momentumHorizontal (μ : Fin 4) (Ψ : Vec4 → DiracSpinor) (x : Vec4) :
    DiracSpinor :=
  horizontalPart (Ψ x) (momentumOp μ Ψ x)

theorem differentiable_shellPacket (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) :
    Differentiable ℝ (shellPacket r s α p q u v) := by
  unfold shellPacket
  refine Differentiable.add ?_ ?_
  · exact (differentiable_planeWave p u).const_smul (r : ℂ)
  · exact (differentiable_planeWave q v).const_smul ((s : ℂ) * exp (I * (α : ℂ)))

theorem horizontalPart_smul (ψ : DiracSpinor) (c : ℂ) (w : DiracSpinor) :
    horizontalPart ψ (c • w) = c • horizontalPart ψ w := by
  unfold horizontalPart
  rw [inner_smul_right]
  have hcoe : (c * inner ℂ ψ w * ((‖ψ‖ ^ 2 : ℝ) : ℂ)⁻¹) • ψ =
      c • ((inner ℂ ψ w * ((‖ψ‖ ^ 2 : ℝ) : ℂ)⁻¹) • ψ) := by
    rw [smul_smul]
    apply congrArg (fun z : ℂ => z • ψ)
    ring
  rw [hcoe, ← smul_sub]

private theorem momentumOp_axis_sum (Ψ : Vec4 → DiracSpinor) (μ : Fin 4) (x : Vec4) :
    ∑ ν : Fin 4, (Complex.ofReal ((Pi.single μ (1 : ℝ) : Vec4) ν)) • momentumOp ν Ψ x =
      momentumOp μ Ψ x := by
  rw [Finset.sum_eq_single μ]
  · simp [Pi.single_eq_same]
  · intro ν _ hν
    simp [Pi.single_eq_of_ne hν]
  · intro hμ
    exact absurd (Finset.mem_univ μ) hμ

private theorem star_exp_I (θ : ℝ) :
    star (exp (I * (θ : ℂ))) = exp (I * ((-θ) : ℂ)) := by
  rw [Complex.star_def, ← exp_conj]
  congr 1
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

private theorem star_exp_mul_self (θ : ℝ) :
    star (exp (I * (θ : ℂ))) * exp (I * (θ : ℂ)) = 1 := by
  rw [star_exp_I, ← exp_add]
  have : I * -(θ : ℂ) + I * (θ : ℂ) = 0 := by
    ring
  rw [this, exp_zero]

private theorem inner_exp_cancel (φ : ℝ) (a b : DiracSpinor) :
    inner ℂ (exp (I * (φ : ℂ)) • a) (exp (I * (φ : ℂ)) • b) = inner ℂ a b := by
  rw [inner_smul_left, inner_smul_right, starRingEnd_apply, ← mul_assoc, star_exp_mul_self,
    one_mul]

theorem momentumOp_eq_chartVelocity (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) :
    momentumOp μ (shellPacket r s α p q u v) x =
      (-I) • chartVelocity r s u v (wavePhase p x) (wavePhase (q - p) x + α)
        (p μ) ((q - p) μ) := by
  let Ψ := shellPacket r s α p q u v
  have hdiff : DifferentiableAt ℝ Ψ x := differentiable_shellPacket r s α p q u v x
  have haxis := hasDerivAt_shellPacket_axis r s α p q u v μ x
  have htrans := translate_deriv_momentum hdiff (Pi.single μ (1 : ℝ))
  have hvel : chartVelocity r s u v (wavePhase p x) (wavePhase (q - p) x + α)
      (p μ) ((q - p) μ) = I • momentumOp μ Ψ x := by
    rw [← HasDerivAt.deriv haxis, htrans, momentumOp_axis_sum]
  have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I, neg_neg]
  apply_fun (fun w : DiracSpinor => (-I) • w) at hvel
  rw [smul_smul, hI, one_smul] at hvel
  exact hvel.symm

/-- `momentumOp` splits into the common momentum on the ray and the relative-phase derivative. -/
theorem momentumOp_shellPacket (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) :
    momentumOp μ (shellPacket r s α p q u v) x =
      (p μ : ℂ) • shellPacket r s α p q u v x +
        ((-I) * ((q - p) μ : ℂ)) •
          (exp (I * (wavePhase p x : ℂ)) •
            phaseCurveDeriv r s u v (wavePhase (q - p) x + α)) := by
  rw [momentumOp_eq_chartVelocity, chartVelocity_eq_ray, smul_add]
  have hstate : chartState r s u v (wavePhase p x) (wavePhase (q - p) x + α) =
      shellPacket r s α p q u v x := (shellPacket_eq_chartState r s α p q u v x).symm
  rw [hstate]
  have hray : (-I) • ((I * (p μ : ℂ)) • shellPacket r s α p q u v x) =
      (p μ : ℂ) • shellPacket r s α p q u v x := by
    rw [smul_smul]
    apply congrArg (fun z : ℂ => z • shellPacket r s α p q u v x)
    calc
      (-I) * (I * (p μ : ℂ)) = ((-I) * I) * (p μ : ℂ) := by ring
      _ = (1 : ℂ) * (p μ : ℂ) := by rw [neg_mul, I_mul_I, neg_neg]
      _ = (p μ : ℂ) := by rw [one_mul]
  have hrel : (-I) • ((((q - p) μ : ℂ) * exp (I * (wavePhase p x : ℂ))) •
        phaseCurveDeriv r s u v (wavePhase (q - p) x + α)) =
      ((-I) * ((q - p) μ : ℂ)) • (exp (I * (wavePhase p x : ℂ)) •
        phaseCurveDeriv r s u v (wavePhase (q - p) x + α)) := by
    rw [smul_smul]
    rw [show ((-I) * (((q - p) μ : ℂ) * exp (I * (wavePhase p x : ℂ)))) •
          phaseCurveDeriv r s u v (wavePhase (q - p) x + α) =
        (((-I) * ((q - p) μ : ℂ)) * exp (I * (wavePhase p x : ℂ))) •
          phaseCurveDeriv r s u v (wavePhase (q - p) x + α) by
      apply congrArg (fun z : ℂ => z • phaseCurveDeriv r s u v (wavePhase (q - p) x + α))
      ring]
    rw [← smul_smul]
  rw [hray, hrel]

theorem momentumOp_of_zero_split {r s α : ℝ} {p q : Vec4} {u v : DiracSpinor} {μ : Fin 4}
    {x : Vec4} (hμ : (q - p) μ = 0) :
    momentumOp μ (shellPacket r s α p q u v) x =
      (p μ : ℂ) • shellPacket r s α p q u v x := by
  rw [momentumOp_shellPacket, hμ]
  simp

theorem momentumOp_same {r s α : ℝ} {p : Vec4} {u v : DiracSpinor} {μ : Fin 4} {x : Vec4} :
    momentumOp μ (shellPacket r s α p p u v) x =
      (p μ : ℂ) • shellPacket r s α p p u v x :=
  momentumOp_of_zero_split (by simp)

/-- The horizontal part of `momentumOp` is `-i/2` times the displacement score. -/
theorem momentumHorizontal_eq_packetScore (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) :
    momentumHorizontal μ (shellPacket r s α p q u v) x =
      (-I / 2) • packetScore r s α p q u v μ x := by
  let Ψ := shellPacket r s α p q u v
  unfold momentumHorizontal packetScore
  rw [momentumOp_shellPacket, horizontalPart_add_smul, shellPacket_eq_chartState]
  have hL := horizontalPart_smul (chartState r s u v (wavePhase p x) (wavePhase (q - p) x + α))
    ((-I) * ((q - p) μ : ℂ))
    (exp (I * (wavePhase p x : ℂ)) • phaseCurveDeriv r s u v (wavePhase (q - p) x + α))
  rw [hL, chartScore_speed_invariant, chartScore, chartVelocity_eq_ray]
  have hzero : (I * ((0 : ℝ) : ℂ)) •
      chartState r s u v (wavePhase p x) (wavePhase (q - p) x + α) = 0 := by simp
  rw [hzero, zero_add]
  have hpack : (((q - p) μ : ℂ) * exp (I * (wavePhase p x : ℂ))) •
        phaseCurveDeriv r s u v (wavePhase (q - p) x + α) =
      ((q - p) μ : ℂ) • (exp (I * (wavePhase p x : ℂ)) •
        phaseCurveDeriv r s u v (wavePhase (q - p) x + α)) := by
    rw [smul_smul]
  rw [hpack]
  have hR := horizontalPart_smul (chartState r s u v (wavePhase p x) (wavePhase (q - p) x + α))
    ((q - p) μ : ℂ)
    (exp (I * (wavePhase p x : ℂ)) • phaseCurveDeriv r s u v (wavePhase (q - p) x + α))
  rw [hR]
  set H : DiracSpinor := horizontalPart
      (chartState r s u v (wavePhase p x) (wavePhase (q - p) x + α))
      (exp (I * (wavePhase p x : ℂ)) •
        phaseCurveDeriv r s u v (wavePhase (q - p) x + α))
  simp only [smul_smul]
  apply congrArg (fun z : ℂ => z • H)
  ring

theorem momentumHorizontal_of_zero_split {r s α : ℝ} {p q : Vec4} {u v : DiracSpinor}
    {μ : Fin 4} {x : Vec4} (hμ : (q - p) μ = 0) :
    momentumHorizontal μ (shellPacket r s α p q u v) x = 0 := by
  rw [momentumHorizontal_eq_packetScore, packetScore_of_zero_split hμ, smul_zero]

theorem momentumHorizontal_normSq (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) :
    ‖momentumHorizontal μ (shellPacket r s α p q u v) x‖ ^ 2 =
      chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) *
        bornDensity (shellPacket r s α p q u v) x / 4 := by
  rw [momentumHorizontal_eq_packetScore, norm_smul, mul_pow, packetScore_normSq r s α p q u v μ x
    hψ]
  have hcoef : ‖(-I / 2 : ℂ)‖ ^ 2 = 1 / 4 := by
    rw [norm_div, norm_neg, norm_I]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    norm_num
  rw [hcoef]
  ring

theorem momentumQuotient_eigen {Ψ : Vec4 → DiracSpinor} {μ : Fin 4} {x : Vec4} {lam : ℂ}
    (hψ : Ψ x ≠ 0) (h : momentumOp μ Ψ x = lam • Ψ x) :
    momentumQuotient μ Ψ x = lam := by
  unfold momentumQuotient
  rw [h, inner_smul_right]
  have hself : inner ℂ (Ψ x) (Ψ x) = ((‖Ψ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (ofReal_pow ‖Ψ x‖ 2).symm
  have hn : ((‖Ψ x‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ))
  rw [hself, mul_assoc, mul_inv_cancel₀ hn, mul_one]

theorem momentumQuotient_of_zero_split {r s α : ℝ} {p q : Vec4} {u v : DiracSpinor}
    {μ : Fin 4} {x : Vec4} (hψ : shellPacket r s α p q u v x ≠ 0) (hμ : (q - p) μ = 0) :
    momentumQuotient μ (shellPacket r s α p q u v) x = (p μ : ℂ) :=
  momentumQuotient_eigen hψ (momentumOp_of_zero_split hμ)

private theorem shellWeight_eq_normSq (c : ℝ) (w : DiracSpinor) :
    ‖(c : ℂ) • w‖ ^ 2 = shellWeight c w := by
  rw [bornWeight_eq]
  unfold shellWeight
  rw [mul_pow, sq_abs]

private theorem readingReal (pμ qμ Wr Ws cross : ℝ) :
    pμ * (Wr + Ws + 2 * cross) + (qμ - pμ) * Ws + (qμ - pμ) * cross =
      pμ * Wr + qμ * Ws + (pμ + qμ) * cross := by
  ring

private theorem phaseCurve_inner_deriv (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) :
    inner ℂ (phaseCurve r s u v θ) (phaseCurveDeriv r s u v θ) =
      I * (exp (I * (θ : ℂ)) * inner ℂ ((r : ℂ) • u) ((s : ℂ) • v) +
        ((‖(s : ℂ) • v‖ ^ 2 : ℝ) : ℂ)) := by
  set z : ℂ := exp (I * (θ : ℂ))
  set b : DiracSpinor := (s : ℂ) • v
  have hχ : phaseCurve r s u v θ = (r : ℂ) • u + z • b := by
    rw [phaseCurve, smul_smul]
  have hχ' : phaseCurveDeriv r s u v θ = (I * z) • b := by
    unfold phaseCurveDeriv
    rw [smul_smul]
  have hself : inner ℂ b b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (ofReal_pow ‖b‖ 2).symm
  have h1 : inner ℂ ((r : ℂ) • u) ((I * z) • b) =
      (I * z) * inner ℂ ((r : ℂ) • u) b := by
    rw [inner_smul_right]
  have h2 : inner ℂ (z • b) ((I * z) • b) =
      star z * (I * z * inner ℂ b b) := by
    rw [inner_smul_left, inner_smul_right, starRingEnd_apply]
  have hunit : star z * z = 1 := by
    have hz : z = exp (I * (θ : ℂ)) := rfl
    rw [hz]
    exact star_exp_mul_self θ
  rw [hχ, hχ', inner_add_left, h1, h2, hself]
  calc
    (I * z) * inner ℂ ((r : ℂ) • u) b + star z * (I * z * ((‖b‖ ^ 2 : ℝ) : ℂ)) =
        I * (z * inner ℂ ((r : ℂ) • u) b) + I * ((star z * z) * ((‖b‖ ^ 2 : ℝ) : ℂ)) := by
      ring
    _ = I * (z * inner ℂ ((r : ℂ) • u) b) + I * ((‖b‖ ^ 2 : ℝ) : ℂ) := by
      rw [hunit]
      ring
    _ = I * (z * inner ℂ ((r : ℂ) • u) b + ((‖b‖ ^ 2 : ℝ) : ℂ)) := by
      ring

private theorem overlap_smul (r s : ℝ) (u v : DiracSpinor) :
    inner ℂ ((r : ℂ) • u) ((s : ℂ) • v) = (r : ℂ) * (s : ℂ) * inner ℂ u v := by
  rw [inner_smul_left, inner_smul_right, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  ring

private theorem momentum_inner_shellPacket (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) :
    inner ℂ (shellPacket r s α p q u v x)
        (momentumOp μ (shellPacket r s α p q u v) x) =
      ((p μ * shellWeight r u + q μ * shellWeight s v +
          (p μ + q μ) * phaseCross r s u v (wavePhase (q - p) x + α) : ℝ) : ℂ) +
        ((((q - p) μ) *
            (exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) * (r : ℂ) * (s : ℂ) *
              inner ℂ u v).im : ℝ) : ℂ) * I := by
  let Ψ := shellPacket r s α p q u v
  set θ : ℝ := wavePhase (q - p) x + α
  have hsub : (q - p) μ = q μ - p μ := by simp [Pi.sub_apply]
  have hN : ‖Ψ x‖ ^ 2 =
      shellWeight r u + shellWeight s v + 2 * phaseCross r s u v θ := by
    rw [show ‖Ψ x‖ ^ 2 = bornDensity Ψ x by unfold bornDensity; rfl]
    rw [bornDensity_eq_phaseCurveNormSq]
    unfold phaseCurveNormSq
    rw [shellWeight_eq_normSq, shellWeight_eq_normSq]
  have hsplit := momentumOp_shellPacket r s α p q u v μ x
  rw [hsplit, inner_add_right]
  have hray : inner ℂ (Ψ x) ((p μ : ℂ) • Ψ x) = (p μ : ℂ) * inner ℂ (Ψ x) (Ψ x) :=
    inner_smul_right (Ψ x) (Ψ x) (p μ : ℂ)
  have hshift : inner ℂ (Ψ x) (((-I) * ((q - p) μ : ℂ)) •
        (exp (I * (wavePhase p x : ℂ)) • phaseCurveDeriv r s u v θ)) =
      ((-I) * ((q - p) μ : ℂ)) *
        inner ℂ (Ψ x) (exp (I * (wavePhase p x : ℂ)) • phaseCurveDeriv r s u v θ) :=
    inner_smul_right (Ψ x)
      (exp (I * (wavePhase p x : ℂ)) • phaseCurveDeriv r s u v θ)
      ((-I) * ((q - p) μ : ℂ))
  rw [hray, hshift]
  have hself : inner ℂ (Ψ x) (Ψ x) = ((‖Ψ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (ofReal_pow ‖Ψ x‖ 2).symm
  rw [hself]
  have hrel : inner ℂ (Ψ x) (exp (I * (wavePhase p x : ℂ)) • phaseCurveDeriv r s u v θ) =
      inner ℂ (phaseCurve r s u v θ) (phaseCurveDeriv r s u v θ) := by
    have hstate : Ψ x = chartState r s u v (wavePhase p x) θ := by
      simpa [Ψ, θ] using shellPacket_eq_chartState r s α p q u v x
    rw [hstate, chartState, inner_exp_cancel]
  rw [hrel, phaseCurve_inner_deriv r s u v θ, shellWeight_eq_normSq]
  set crossC : ℂ := exp (I * (θ : ℂ)) * inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)
  have hcross : crossC.re = phaseCross r s u v θ := by
    simp [crossC, phaseCross]
  have him : crossC.im = (exp (I * (θ : ℂ)) * (r : ℂ) * (s : ℂ) * inner ℂ u v).im := by
    have hov : inner ℂ ((r : ℂ) • u) ((s : ℂ) • v) = (r : ℂ) * (s : ℂ) * inner ℂ u v :=
      overlap_smul r s u v
    have hcrossC : crossC = exp (I * (θ : ℂ)) * ((r : ℂ) * (s : ℂ) * inner ℂ u v) := by
      rw [show crossC = exp (I * (θ : ℂ)) * inner ℂ ((r : ℂ) • u) ((s : ℂ) • v) from rfl, hov]
    have hmul : exp (I * (θ : ℂ)) * ((r : ℂ) * (s : ℂ) * inner ℂ u v) =
        exp (I * (θ : ℂ)) * (r : ℂ) * (s : ℂ) * inner ℂ u v := by ring
    rw [hcrossC, hmul]
  have hfac : ((-I) * ((q - p) μ : ℂ)) *
        (I * (crossC + ((shellWeight s v : ℝ) : ℂ))) =
      ((q - p) μ : ℂ) * crossC + ((q - p) μ : ℂ) * ((shellWeight s v : ℝ) : ℂ) := by
    calc
      ((-I) * ((q - p) μ : ℂ)) * (I * (crossC + ((shellWeight s v : ℝ) : ℂ))) =
          (((-I) * I) * ((q - p) μ : ℂ)) * (crossC + ((shellWeight s v : ℝ) : ℂ)) := by ring
      _ = ((1 : ℂ) * ((q - p) μ : ℂ)) * (crossC + ((shellWeight s v : ℝ) : ℂ)) := by
        rw [neg_mul, I_mul_I, neg_neg]
      _ = ((q - p) μ : ℂ) * crossC + ((q - p) μ : ℂ) * ((shellWeight s v : ℝ) : ℂ) := by ring
  rw [hfac]
  set N : ℝ := ‖Ψ x‖ ^ 2
  set δ : ℝ := (q - p) μ
  set W : ℝ := shellWeight s v
  have hleftRe : ((p μ : ℂ) * (N : ℂ) + ((δ : ℂ) * crossC + (δ : ℂ) * (W : ℂ))).re =
      p μ * N + δ * crossC.re + δ * W := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hleftIm : ((p μ : ℂ) * (N : ℂ) + ((δ : ℂ) * crossC + (δ : ℂ) * (W : ℂ))).im =
      δ * crossC.im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  set imag : ℝ := (exp (I * (θ : ℂ)) * (r : ℂ) * (s : ℂ) * inner ℂ u v).im
  set weighted : ℝ :=
    p μ * shellWeight r u + q μ * W + (p μ + q μ) * phaseCross r s u v θ
  have hrightRe : (((weighted : ℝ) : ℂ) + ((δ * imag : ℝ) : ℂ) * I).re = weighted := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, sub_zero, mul_one]
  have hrightIm : (((weighted : ℝ) : ℂ) + ((δ * imag : ℝ) : ℂ) * I).im = δ * imag := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, zero_add, mul_one]
  apply Complex.ext
  · rw [hleftRe, hrightRe, hN, hcross, hsub]
    have hread := readingReal (p μ) (q μ) (shellWeight r u) W (phaseCross r s u v θ)
    linarith
  · rw [hleftIm, him, hrightIm]

/-- Real and imaginary parts of the Rayleigh quotient on a nonzero shell-packet sample. -/
theorem momentumQuotient_shellPacket (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) :
    bornDensity (shellPacket r s α p q u v) x ≠ 0 ∧
      (momentumQuotient μ (shellPacket r s α p q u v) x).re =
      (p μ * shellWeight r u + q μ * shellWeight s v +
          (p μ + q μ) * phaseCross r s u v (wavePhase (q - p) x + α)) /
        bornDensity (shellPacket r s α p q u v) x ∧
      (momentumQuotient μ (shellPacket r s α p q u v) x).im =
        ((q - p) μ) * (exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) * (r : ℂ) * (s : ℂ) *
            inner ℂ u v).im /
          bornDensity (shellPacket r s α p q u v) x := by
  let Ψ := shellPacket r s α p q u v
  have hinner := momentum_inner_shellPacket r s α p q u v μ x
  unfold momentumQuotient
  rw [hinner]
  have hborn_eq : ‖Ψ x‖ ^ 2 = bornDensity Ψ x := by unfold bornDensity; rfl
  rw [hborn_eq]
  have hdiv (a b : ℝ) :
      (((a : ℂ) + (b : ℂ) * I) * (bornDensity Ψ x : ℂ)⁻¹).re = a / bornDensity Ψ x ∧
        (((a : ℂ) + (b : ℂ) * I) * (bornDensity Ψ x : ℂ)⁻¹).im = b / bornDensity Ψ x := by
    have hcoe : ((a : ℂ) + (b : ℂ) * I) * (bornDensity Ψ x : ℂ)⁻¹ =
        ((a : ℂ) + (b : ℂ) * I) / bornDensity Ψ x := by
      rw [div_eq_mul_inv]
    rw [hcoe, div_ofReal_re, div_ofReal_im]
    constructor
    · simp [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.mul_re]
    · simp [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.mul_im]
  have hden : bornDensity Ψ x ≠ 0 := by
    unfold bornDensity
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  exact ⟨hden, hdiv
    (p μ * shellWeight r u + q μ * shellWeight s v +
      (p μ + q μ) * phaseCross r s u v (wavePhase (q - p) x + α))
    (((q - p) μ) *
      (exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) * (r : ℂ) * (s : ℂ) * inner ℂ u v).im)⟩

/-! ### The ray and the horizontal momentum -/

theorem momentumHorizontal_ne_zero_of_chartFisher (r s α : ℝ) (p q : Vec4)
    (u v : DiracSpinor) (μ : Fin 4) (x : Vec4)
    (hψ : shellPacket r s α p q u v x ≠ 0)
    (hF : chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) ≠ 0) :
    momentumHorizontal μ (shellPacket r s α p q u v) x ≠ 0 := by
  intro hH
  have hnorm := momentumHorizontal_normSq r s α p q u v μ x hψ
  rw [hH] at hnorm
  have h0 : ‖(0 : DiracSpinor)‖ ^ 2 = 0 := by simp
  have hden : bornDensity (shellPacket r s α p q u v) x ≠ 0 := by
    unfold bornDensity
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  rw [h0, div_eq_mul_inv] at hnorm
  have hmul : chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) *
      bornDensity (shellPacket r s α p q u v) x = 0 :=
    (mul_eq_zero.mp hnorm.symm).resolve_right (inv_ne_zero h4)
  exact hF ((mul_eq_zero.mp hmul).resolve_right hden)

/-- Positive chart Fisher information means the sample is not an eigen-sample. -/
theorem momentumOp_not_eigen_of_chartFisher (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0)
    (hF : chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) ≠ 0)
    (lam : ℂ) :
    momentumOp μ (shellPacket r s α p q u v) x ≠
      lam • shellPacket r s α p q u v x := by
  intro hlam
  apply momentumHorizontal_ne_zero_of_chartFisher r s α p q u v μ x hψ hF
  unfold momentumHorizontal
  rw [hlam]
  have hzero : horizontalPart (shellPacket r s α p q u v x) 0 = 0 := by
    unfold horizontalPart
    simp
  have h := horizontalPart_add_smul (shellPacket r s α p q u v x) 0 lam
  simpa [hzero] using h

/-- A nonzero coordinate lies on the ray, and positive Fisher information lies across it. -/
theorem positionOp_ne_smul_momentumHorizontal (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) (hx : x μ ≠ 0)
    (hF : chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) ≠ 0) :
    positionOp μ (shellPacket r s α p q u v) x ≠ 0 ∧
      momentumHorizontal μ (shellPacket r s α p q u v) x ≠ 0 ∧
        ∀ c : ℂ, positionOp μ (shellPacket r s α p q u v) x ≠
          c • momentumHorizontal μ (shellPacket r s α p q u v) x := by
  let Ψ := shellPacket r s α p q u v
  refine ⟨positionOp_ne_zero_of_coord hψ hx,
    momentumHorizontal_ne_zero_of_chartFisher r s α p q u v μ x hψ hF, ?_⟩
  intro c hc
  have hpos := positionOp_inner μ Ψ x
  have horth : inner ℂ (Ψ x) (momentumHorizontal μ Ψ x) = 0 := by
    rw [momentumHorizontal_eq_packetScore, inner_smul_right,
      packetScore_ortho r s α p q u v μ x hψ, mul_zero]
  rw [hc, inner_smul_right, horth, mul_zero] at hpos
  have hn : ((‖Ψ x‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ))
  exact hx (ofReal_eq_zero.mp ((mul_eq_zero.mp hpos.symm).resolve_right hn))

/-- A nonzero Rayleigh quotient is a ray component, so `momentumOp` is not the score. -/
theorem momentumOp_ne_smul_packetScore (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0)
    (hq : momentumQuotient μ (shellPacket r s α p q u v) x ≠ 0) (c : ℂ) :
    momentumOp μ (shellPacket r s α p q u v) x ≠
      c • packetScore r s α p q u v μ x := by
  let Ψ := shellPacket r s α p q u v
  intro hc
  have hn : ((‖Ψ x‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ))
  have hinner : inner ℂ (Ψ x) (momentumOp μ Ψ x) =
      momentumQuotient μ Ψ x * ((‖Ψ x‖ ^ 2 : ℝ) : ℂ) := by
    unfold momentumQuotient
    rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]
  rw [hc, inner_smul_right, packetScore_ortho r s α p q u v μ x hψ, mul_zero] at hinner
  exact hq ((mul_eq_zero.mp hinner.symm).resolve_right hn)

/-! ### Four samples -/

private theorem shellRest_overlap_norm :
    ‖inner ℂ shellParticleP shellParticleQ‖ = 2 := by
  have h := phaseAmplitude_norm 1 1 shellParticleP shellParticleQ
  have h1 : ((1 : ℝ) : ℂ) = 1 := by norm_num
  rw [h1, one_smul, one_smul] at h
  simp only [abs_one, one_mul] at h
  rw [shellRest_fidelity] at h
  have hprod : ‖shellParticleP‖ * ‖shellParticleQ‖ = 50 / 9 := by
    have heq : ‖shellParticleP‖ = ‖shellParticleQ‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        (shellRest_norms.1.trans shellRest_norms.2.symm)
    rw [heq, ← sq, shellRest_norms.2]
  calc
    ‖inner ℂ shellParticleP shellParticleQ‖ =
        (9 / 25) * ‖shellParticleP‖ * ‖shellParticleQ‖ := h
    _ = (9 / 25) * (‖shellParticleP‖ * ‖shellParticleQ‖) := by ring
    _ = (9 / 25) * (50 / 9) := by rw [hprod]
    _ = 2 := by norm_num

private theorem shellRest_coord :
    shellRestP 0 = 5 ∧ shellRestP 1 = 4 ∧ shellRestQ 1 = -4 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp [shellRestP, shellRestQ, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne]

/-- Mean rest, quadrature, origin, axis `1`: real part `0`, imaginary part squared
`(36/25)²`, horizontal length squared `34816/225`. -/
theorem shellRest_quadrature_momentum :
    ∃ θ : ℝ,
      let Ψ := shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
      (momentumQuotient 1 Ψ 0).re = 0 ∧
        (momentumQuotient 1 Ψ 0).im ^ 2 = (36 / 25) ^ 2 ∧
          ‖momentumHorizontal 1 Ψ 0‖ ^ 2 = 34816 / 225 := by
  obtain ⟨θ, hcross, _, _, hF⟩ := shellRest_chartFisher.1
  refine ⟨θ, ?_⟩
  intro Ψ
  have hψ := shellRest_packet_ne_zero θ 0
  have hquot := momentumQuotient_shellPacket 1 1 θ shellRestP shellRestQ shellParticleP
    shellParticleQ 1 0 hψ
  have hphase : wavePhase (shellRestQ - shellRestP) 0 + θ = θ := by
    rw [wavePhase_zero, zero_add]
  have hWp : shellWeight 1 shellParticleP = 50 / 9 := by
    unfold shellWeight
    rw [shellRest_norms.1]
    norm_num
  have hWq : shellWeight 1 shellParticleQ = 50 / 9 := by
    unfold shellWeight
    rw [shellRest_norms.2]
    norm_num
  have hborn : bornDensity Ψ 0 = 100 / 9 := by
    rw [bornDensity_eq_phaseCurveNormSq, hphase]
    unfold phaseCurveNormSq
    rw [hcross, shellWeight_eq_normSq, shellWeight_eq_normSq, hWp, hWq]
    norm_num
  set z : ℂ := exp (I * (θ : ℂ)) * inner ℂ shellParticleP shellParticleQ
  have hreZ : z.re = 0 := by
    rw [← hcross]
    have h1 : ((1 : ℝ) : ℂ) = 1 := by norm_num
    unfold phaseCross
    rw [h1, one_smul, one_smul]
  have hnormZ : ‖z‖ = 2 := by
    have hz : z = exp (I * (θ : ℂ)) * inner ℂ shellParticleP shellParticleQ := rfl
    rw [hz, norm_mul, norm_exp_I, one_mul, shellRest_overlap_norm]
  have him2 : z.im ^ 2 = 4 := by
    have hsq : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [hnormZ, hreZ] at hsq
    rw [pow_two]
    linarith
  have himZ : (exp (I * (θ : ℂ)) * ((1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) *
      inner ℂ shellParticleP shellParticleQ).im = z.im := by
    have h1 : ((1 : ℝ) : ℂ) = 1 := by norm_num
    rw [h1, mul_one, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hquot.2.1, hphase, shellRest_coord.2.1, shellRest_coord.2.2, hWp, hWq, hcross, hborn]
    norm_num
  · rw [hquot.2.2, hphase, shellRest_relative.2.1, himZ, hborn]
    have hsq : ((-8 : ℝ) * z.im / (100 / 9)) ^ 2 =
        64 * (z.im ^ 2) / ((100 / 9) ^ 2) := by
      rw [div_pow]
      ring
    rw [hsq, him2]
    norm_num
  · have hlen := momentumHorizontal_normSq 1 1 θ shellRestP shellRestQ shellParticleP
      shellParticleQ 1 0 hψ
    rw [hphase, hF, hborn] at hlen
    have hprod : (34816 / 625 : ℝ) * (100 / 9) / 4 = 34816 / 225 := by norm_num
    rw [hprod] at hlen
    exact hlen

/-- The time axis of mean rest is the eigen-sample `5 • Ψ` at every phase. -/
theorem shellRest_time_eigen (α : ℝ) (x : Vec4) :
    let Ψ := shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ
    momentumOp 0 Ψ x = (5 : ℂ) • Ψ x ∧ momentumHorizontal 0 Ψ x = 0 := by
  intro Ψ
  refine ⟨?_, momentumHorizontal_of_zero_split shellRest_relative.1⟩
  rw [momentumOp_of_zero_split shellRest_relative.1, shellRest_coord.1]
  norm_num
  rfl

private theorem shellLab_overlap_norm :
    ‖inner ℂ shellParticleP shellLabSpinor‖ = 8 / 3 := by
  have h := phaseAmplitude_norm 1 1 shellParticleP shellLabSpinor
  have h1 : ((1 : ℝ) : ℂ) = 1 := by norm_num
  rw [h1, one_smul, one_smul] at h
  simp only [abs_one, one_mul] at h
  rw [shellLab_fidelity] at h
  have hprod : ‖shellParticleP‖ * ‖shellLabSpinor‖ = 10 / 3 := by
    have hsq : (‖shellParticleP‖ * ‖shellLabSpinor‖) ^ 2 = (10 / 3) ^ 2 := by
      rw [mul_pow, shellRest_norms.1, shellLab_norm]
      norm_num
    exact (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)).mp hsq
  calc
    ‖inner ℂ shellParticleP shellLabSpinor‖ =
        (4 / 5) * ‖shellParticleP‖ * ‖shellLabSpinor‖ := h
    _ = (4 / 5) * (‖shellParticleP‖ * ‖shellLabSpinor‖) := by ring
    _ = (4 / 5) * (10 / 3) := by rw [hprod]
    _ = 8 / 3 := by norm_num

private theorem shellLab_carrier :
    inner ℂ shellParticleP shellLabSpinor = (8 / 3 : ℂ) := by
  have hden : bornDensity (shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP
      shellLabSpinor) (timeShift 0) = 116 / 9 := shellLab_time_density.1
  have hwP : shellWeight 1 shellParticleP = 50 / 9 := by
    unfold shellWeight
    rw [shellRest_norms.1]
    norm_num
  have hwL : shellWeight 1 shellLabSpinor = 2 := by
    unfold shellWeight
    rw [shellLab_norm]
    norm_num
  have hphase : wavePhase (restMomentum 3 - shellRestP) (timeShift 0) = 0 := by
    rw [wavePhase_timeShift_coord, shellLab_relative.1]
    simp
  have hre : (inner ℂ shellParticleP shellLabSpinor).re = 8 / 3 := by
    have hborn := bornDensity_shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP
      shellLabSpinor (timeShift 0)
    rw [hden, hwP, hwL, hphase] at hborn
    simp [Complex.exp_zero] at hborn
    linarith
  have him : (inner ℂ shellParticleP shellLabSpinor).im = 0 := by
    have hsq : ‖inner ℂ shellParticleP shellLabSpinor‖ ^ 2 =
        (inner ℂ shellParticleP shellLabSpinor).re *
          (inner ℂ shellParticleP shellLabSpinor).re +
          (inner ℂ shellParticleP shellLabSpinor).im *
            (inner ℂ shellParticleP shellLabSpinor).im := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [shellLab_overlap_norm, hre] at hsq
    nlinarith [sq_nonneg (inner ℂ shellParticleP shellLabSpinor).im]
  apply Complex.ext
  · rw [hre]
    norm_num
  · rw [him]
    norm_num

/-- Rest against `(5, 4, 0, 0)` at time `-π/2`: the quotient is `28/5`, the horizontal length
squared is `36/5`, and the position reads `-π/2`. -/
theorem shellLab_momentum :
    let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
    let x := timeShift (-Real.pi / 2)
    momentumQuotient 0 Ψ x = (28 / 5 : ℂ) ∧
      ‖momentumHorizontal 0 Ψ x‖ ^ 2 = 36 / 5 ∧
        (inner ℂ (Ψ x) (positionOp 0 Ψ x)).re / ‖Ψ x‖ ^ 2 = -Real.pi / 2 := by
  intro Ψ x
  have hψ : Ψ x ≠ 0 := by
    intro hz
    have hzero : bornDensity Ψ x = 0 := by
      rw [bornDensity, hz, norm_zero]
      simp
    rw [shellLab_time_density.2.1] at hzero
    norm_num at hzero
  have hphase : wavePhase (restMomentum 3 - shellRestP) x = Real.pi := by
    rw [wavePhase_timeShift_coord, shellLab_relative.1]
    ring
  have hq0 : restMomentum 3 0 = 3 := by simp [restMomentum, Pi.single_eq_same]
  have hWp : shellWeight 1 shellParticleP = 50 / 9 := by
    unfold shellWeight
    rw [shellRest_norms.1]
    norm_num
  have hWl : shellWeight 1 shellLabSpinor = 2 := by
    unfold shellWeight
    rw [shellLab_norm]
    norm_num
  have hcross : phaseCross 1 1 shellParticleP shellLabSpinor Real.pi = -(8 / 3) := by
    unfold phaseCross
    rw [overlap_smul, shellLab_carrier]
    have hexp : exp (I * (Real.pi : ℂ)) = -1 := by
      rw [mul_comm, exp_pi_mul_I]
    rw [hexp]
    norm_num
  have him0 : (exp (I * (Real.pi : ℂ)) * ((1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) *
      inner ℂ shellParticleP shellLabSpinor).im = 0 := by
    rw [shellLab_carrier]
    have hexp : exp (I * (Real.pi : ℂ)) = -1 := by
      rw [mul_comm, exp_pi_mul_I]
    rw [hexp]
    norm_num
  have hborn : bornDensity Ψ x = 20 / 9 := shellLab_time_density.2.1
  have hquot := momentumQuotient_shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP
    shellLabSpinor 0 x hψ
  have hphase0 : wavePhase (restMomentum 3 - shellRestP) x + 0 = Real.pi := by
    rw [add_zero, hphase]
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ext
    · rw [hquot.2.1, hphase0, shellRest_coord.1, hq0, hWp, hWl, hcross, hborn]
      norm_num
    · rw [hquot.2.2, hphase0, shellLab_relative.1, him0, hborn]
      norm_num
  · have hlen := momentumHorizontal_normSq 1 1 0 shellRestP (restMomentum 3) shellParticleP
      shellLabSpinor 0 x hψ
    have hF := shellLab_chartFisher.2.2
    rw [hphase] at hF
    rw [add_zero, hphase, hF, hborn] at hlen
    have hprod : (324 / 25 : ℝ) * (20 / 9) / 4 = 36 / 5 := by norm_num
    rw [hprod] at hlen
    exact hlen
  · have hx : x 0 = -Real.pi / 2 := by simp [x, timeShift, Pi.single_eq_same]
    rw [position_reading hψ, hx]

/-- The opposite Weyl seed at the origin has quotient `0`, a nonzero momentum operator,
horizontal length squared `1600/9`, and position `0`. -/
theorem shellOrth_momentum :
    let Ψ := shellPacket 1 1 0 shellRestP shellRestQ shellParticleP shellOrthQ
    momentumQuotient 1 Ψ 0 = 0 ∧
      momentumOp 1 Ψ 0 ≠ 0 ∧
        ‖momentumHorizontal 1 Ψ 0‖ ^ 2 = 1600 / 9 ∧
          positionOp 1 Ψ 0 = 0 := by
  intro Ψ
  have hborn : bornDensity Ψ 0 = 100 / 9 := shellOrth_origin_score.1
  have hψ : Ψ 0 ≠ 0 := by
    intro hz
    have hzero : bornDensity Ψ 0 = 0 := by
      rw [bornDensity, hz, norm_zero]
      simp
    rw [hborn] at hzero
    norm_num at hzero
  have hphase : wavePhase (shellRestQ - shellRestP) 0 + 0 = 0 := by
    rw [wavePhase_zero, add_zero]
  have hWp : shellWeight 1 shellParticleP = 50 / 9 := by
    unfold shellWeight
    rw [shellRest_norms.1]
    norm_num
  have hWq : shellWeight 1 shellOrthQ = 50 / 9 := by
    unfold shellWeight
    rw [shellOrth_norm]
    norm_num
  have him0 : (exp (I * ((0 : ℝ) : ℂ)) * ((1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) *
      inner ℂ shellParticleP shellOrthQ).im = 0 := by
    rw [shellOrth_inner]
    simp
  have hquot := momentumQuotient_shellPacket 1 1 0 shellRestP shellRestQ shellParticleP
    shellOrthQ 1 0 hψ
  have hlen : ‖momentumHorizontal 1 Ψ 0‖ ^ 2 = 1600 / 9 := by
    have hnorm := momentumHorizontal_normSq 1 1 0 shellRestP shellRestQ shellParticleP
      shellOrthQ 1 0 hψ
    rw [hphase, (shellOrth_chartFisher (0 : ℝ)).2, hborn] at hnorm
    have hprod : (64 : ℝ) * (100 / 9) / 4 = 1600 / 9 := by norm_num
    rw [hprod] at hnorm
    exact hnorm
  refine ⟨?_, ?_, hlen, shellOrth_origin_score.2.1⟩
  · apply Complex.ext
    · rw [hquot.2.1, hphase, shellRest_coord.2.1, shellRest_coord.2.2, hWp, hWq,
        phaseCross_shellOrth, hborn, Complex.zero_re]
      norm_num
    · rw [hquot.2.2, hphase, shellRest_relative.2.1, him0, hborn, Complex.zero_im]
      norm_num
  · intro hop
    have hH : momentumHorizontal 1 Ψ 0 = 0 := by
      unfold momentumHorizontal
      rw [hop]
      unfold horizontalPart
      simp
    rw [hH, norm_zero] at hlen
    simp at hlen
    norm_num at hlen

/-- One momentum is the eigen-sample of that momentum. The zero packet has vanishing
`momentumOp` and position `1`. -/
theorem zeroMomentum_packet :
    let u : DiracSpinor := EuclideanSpace.single 0 1
    let x : Vec4 := Pi.single 1 1
    let Ψ := shellPacket 1 1 0 (0 : Vec4) 0 u u
    momentumOp 1 Ψ x = 0 ∧
      (inner ℂ (Ψ x) (positionOp 1 Ψ x)).re / ‖Ψ x‖ ^ 2 = 1 := by
  intro u x Ψ
  refine ⟨?_, sameMomentum_score.2.2.2⟩
  have h := momentumOp_same (r := 1) (s := 1) (α := 0) (p := (0 : Vec4)) (u := u) (v := u)
    (μ := 1) (x := x)
  have h0 : ((0 : Vec4) 1 : ℂ) = 0 := by simp
  rw [h, h0, zero_smul]

end Logic

end DoubleSpacetime
