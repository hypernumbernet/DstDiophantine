import DoubleSpacetime.Logic.Quantum.MomentumReading

/-!
# Translation Fisher information as a four-tensor

Time in quantum mechanics is a parameter. A parameter does not need a self-adjoint operator, and
neither does position. Newton–Wigner localisation asks for an operator on the carrier with
commutator `i`. No such pair exists. The replacement is the quantum Fisher information of
spacetime translations,

`F_μν = 4 Cov(P_μ, P_ν)`.

On one sample, `Cov` is the real part of the overlap of the two centred momentum vectors, divided
by the Born density. For a shell packet this matrix is the outer product of the relative momentum
with the projective scalar,

`F_μν(θ) = phaseFisher(θ) · (q − p)_μ · (q − p)_ν`.

The diagonal is `chartFisher`. A linear change of inertial axes remixes these components by
`Λ F Λᵀ` and leaves the contraction `η^{μν} F_μν = phaseFisher · Q(q − p)` fixed, while the
scalar `phaseFisher` is held at one relative phase. Only the component that is read changes. The
chart Born norm of a boosted carrier is a different question; `BornLorentz` separates it from the
Dirac scalar, and it is not identified here.

`F` has rank at most one, so it has no inverse on all four coordinates. On its support the
Cramér–Rao floor of an unbiased displacement along `v` is the reciprocal of `vᵀ F v`. That floor
is the precision with which the displacement can be estimated. It is not a reading of
`positionOp`, which multiplies by the coordinate. The time slot is the same formula as the spatial
slots. It vanishes exactly when the relative energy vanishes, and a boost of the mean-rest pair
moves that information onto the time axis.

Mean rest, mass 3, quadrature: `F_00 = 0`, `F_11 = 34816/625`, and the floor along axis `1` is
`625/34816`, while the position reading at the origin is `0`. The boost of rapidity with
`cosh = 5/3` and `sinh = -4/3` sends the relative momentum `(0, -8)` to `(32/3, -40/3)`. The
contraction stays `34816/625`. The new time slot is `557056/5625`. Rest against `(5, 4, 0, 0)` at
time `-π/2` has time floor `25/324`, and the position reading is `-π/2`.
-/

namespace DoubleSpacetime

namespace Logic

open Complex InnerProductSpace

/-! ### Covariance of the centred momenta -/

/-- Symmetric covariance of two momentum components on one sample. -/
noncomputable def momentumCov (μ ν : Fin 4) (Ψ : Vec4 → DiracSpinor) (x : Vec4) : ℝ :=
  (inner ℂ (momentumHorizontal μ Ψ x) (momentumHorizontal ν Ψ x)).re / ‖Ψ x‖ ^ 2

/-- Quantum Fisher information of translations, `F_μν = 4 Cov(P_μ, P_ν)`. -/
noncomputable def translationFisher (μ ν : Fin 4) (Ψ : Vec4 → DiracSpinor) (x : Vec4) : ℝ :=
  4 * momentumCov μ ν Ψ x

/-- Horizontal score for a unit relative rate, independent of the axis. -/
noncomputable def packetDirection (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (x : Vec4) :
    DiracSpinor :=
  chartScore r s u v (wavePhase p x) (wavePhase (q - p) x + α) 0 1

theorem chartScore_eq_rel_smul (r s : ℝ) (u v : DiracSpinor) (φ θ speed rel : ℝ) :
    chartScore r s u v φ θ speed rel =
      (rel : ℂ) • chartScore r s u v φ θ 0 1 := by
  rw [chartScore_speed_invariant]
  have hvel : chartVelocity r s u v φ θ 0 rel =
      (rel : ℂ) • chartVelocity r s u v φ θ 0 1 := by
    rw [chartVelocity_eq_ray, chartVelocity_eq_ray]
    simp only [Complex.ofReal_zero, mul_zero, zero_smul, zero_add]
    rw [smul_smul]
    apply congrArg (fun z : ℂ => z • phaseCurveDeriv r s u v θ)
    simp
  unfold chartScore
  rw [hvel, horizontalPart_smul, smul_smul, smul_smul]
  apply congrArg
    (fun z : ℂ => z • horizontalPart (chartState r s u v φ θ) (chartVelocity r s u v φ θ 0 1))
  ring

theorem packetScore_eq_direction (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) :
    packetScore r s α p q u v μ x =
      ((q - p) μ : ℂ) • packetDirection r s α p q u v x := by
  unfold packetScore packetDirection
  exact chartScore_eq_rel_smul r s u v (wavePhase p x) (wavePhase (q - p) x + α)
    (p μ) ((q - p) μ)

theorem momentumHorizontal_eq_direction (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) :
    momentumHorizontal μ (shellPacket r s α p q u v) x =
      ((-I / 2) * ((q - p) μ : ℂ)) • packetDirection r s α p q u v x := by
  rw [momentumHorizontal_eq_packetScore, packetScore_eq_direction, smul_smul]

private theorem star_half_I (a b : ℝ) :
    starRingEnd ℂ ((-I / 2) * (a : ℂ)) * ((-I / 2) * (b : ℂ)) =
      ((a * b / 4 : ℝ) : ℂ) := by
  have hL : (-I / 2) * (a : ℂ) = (↑(-a / 2) : ℂ) * I := by
    simp [div_eq_mul_inv]
    ring
  have hR : (-I / 2) * (b : ℂ) = (↑(-b / 2) : ℂ) * I := by
    simp [div_eq_mul_inv]
    ring
  rw [hL, hR, starRingEnd_apply, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hI : (-I) * I = (1 : ℂ) := by
    rw [neg_mul, I_mul_I, neg_neg]
  calc
    (↑(-a / 2) * -I) * (↑(-b / 2) * I) =
        (↑(-a / 2) * ↑(-b / 2)) * ((-I) * I) := by ring
    _ = (↑(-a / 2) * ↑(-b / 2)) * 1 := by rw [hI]
    _ = ↑(-a / 2 * (-b / 2)) := by rw [mul_one, ← ofReal_mul]
    _ = ↑(a * b / 4) := by congr 1; ring

private theorem inner_direction_self (S : DiracSpinor) :
    inner ℂ S S = ((‖S‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  exact (ofReal_pow ‖S‖ 2).symm

theorem packetDirection_normSq (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (x : Vec4)
    (hψ : shellPacket r s α p q u v x ≠ 0) :
    ‖packetDirection r s α p q u v x‖ ^ 2 =
      phaseFisher r s u v (wavePhase (q - p) x + α) *
        bornDensity (shellPacket r s α p q u v) x := by
  have hden : phaseCurveNormSq r s u v (wavePhase (q - p) x + α) ≠ 0 := by
    intro hz
    apply hψ
    have hborn : bornDensity (shellPacket r s α p q u v) x = 0 := by
      rw [bornDensity_eq_phaseCurveNormSq, hz]
    rw [bornDensity, sq_eq_zero_iff, norm_eq_zero] at hborn
    exact hborn
  let ε : Vec4 := Pi.single 0 1
  have hε : ε 0 = 1 := by simp [ε]
  have hscore :=
    chartScore_normSq r s u v (wavePhase p x) (wavePhase (q - p) x + α) 0 ε 0 hden
  rw [hε, chartFisher, chartState_normSq, ← bornDensity_eq_phaseCurveNormSq] at hscore
  simpa [packetDirection, hε, one_pow, mul_one] using hscore

theorem inner_momentumHorizontal_shell (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ ν : Fin 4) (x : Vec4) :
    inner ℂ (momentumHorizontal μ (shellPacket r s α p q u v) x)
        (momentumHorizontal ν (shellPacket r s α p q u v) x) =
      ((((q - p) μ * (q - p) ν / 4 : ℝ) *
          ‖packetDirection r s α p q u v x‖ ^ 2 : ℝ) : ℂ) := by
  rw [momentumHorizontal_eq_direction, momentumHorizontal_eq_direction, inner_smul_left,
    inner_smul_right, inner_direction_self, ← mul_assoc, star_half_I ((q - p) μ) ((q - p) ν),
    ← ofReal_mul]

theorem momentumCov_shellPacket (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ ν : Fin 4)
    (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) :
    momentumCov μ ν (shellPacket r s α p q u v) x =
      phaseFisher r s u v (wavePhase (q - p) x + α) *
        ((q - p) μ) * ((q - p) ν) / 4 := by
  unfold momentumCov
  rw [inner_momentumHorizontal_shell, ofReal_re, packetDirection_normSq r s α p q u v x hψ,
    bornDensity]
  have hden : ‖shellPacket r s α p q u v x‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  field_simp [hden]

/-- On a shell packet the translation Fisher matrix is the outer product of `q − p`. -/
theorem translationFisher_outer (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ ν : Fin 4)
    (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) :
    translationFisher μ ν (shellPacket r s α p q u v) x =
      phaseFisher r s u v (wavePhase (q - p) x + α) * ((q - p) μ) * ((q - p) ν) := by
  unfold translationFisher
  rw [momentumCov_shellPacket r s α p q u v μ ν x hψ]
  have hfour : (4 : ℝ) ≠ 0 := by norm_num
  field_simp [hfour]

theorem translationFisher_diag_eq_chartFisher (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) :
    translationFisher μ μ (shellPacket r s α p q u v) x =
      chartFisher r s u v (q - p) μ (wavePhase (q - p) x + α) := by
  rw [translationFisher_outer r s α p q u v μ μ x hψ, chartFisher]
  ring

theorem translationFisher_symm (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ ν : Fin 4)
    (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) :
    translationFisher μ ν (shellPacket r s α p q u v) x =
      translationFisher ν μ (shellPacket r s α p q u v) x := by
  rw [translationFisher_outer r s α p q u v μ ν x hψ,
    translationFisher_outer r s α p q u v ν μ x hψ]
  ring

/-! ### The Cramér–Rao floor on the support -/

/-- Fisher information of one displacement `v`, the quadratic form `vᵀ F v`. -/
noncomputable def displacementInformation (Ψ : Vec4 → DiracSpinor) (x v : Vec4) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, v μ * translationFisher μ ν Ψ x * v ν

/-- Reciprocal of that quadratic form. On the support of `F` this is the Cramér–Rao floor. -/
noncomputable def precisionFloor (Ψ : Vec4 → DiracSpinor) (x v : Vec4) : ℝ :=
  (displacementInformation Ψ x v)⁻¹

private theorem sum_outer (a b : Vec4) (scale : ℝ) :
    (∑ μ : Fin 4, ∑ ν : Fin 4, b μ * (scale * a μ * a ν) * b ν) =
      scale * (∑ μ : Fin 4, a μ * b μ) ^ 2 := by
  have hmul : (∑ μ : Fin 4, a μ * b μ) * (∑ ν : Fin 4, a ν * b ν) =
      ∑ μ : Fin 4, ∑ ν : Fin 4, (a μ * b μ) * (a ν * b ν) := by
    rw [Finset.sum_mul_sum]
  have hscale : scale * ((∑ μ : Fin 4, a μ * b μ) * (∑ ν : Fin 4, a ν * b ν)) =
      ∑ μ : Fin 4, ∑ ν : Fin 4, scale * ((a μ * b μ) * (a ν * b ν)) := by
    rw [hmul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
  have hreorder : scale * (∑ μ : Fin 4, a μ * b μ) ^ 2 =
      ∑ μ : Fin 4, ∑ ν : Fin 4, b μ * (scale * a μ * a ν) * b ν := by
    rw [pow_two, hscale]
    refine Finset.sum_congr rfl fun μ _ => ?_
    refine Finset.sum_congr rfl fun ν _ => ?_
    ring
  exact hreorder.symm

private theorem dot_single (a : Vec4) (μ : Fin 4) :
    (∑ ν : Fin 4, a ν * (Pi.single μ (1 : ℝ) : Vec4) ν) = a μ := by
  fin_cases μ <;> simp [Fin.sum_univ_four, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem displacementInformation_shellPacket (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (x dir : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) :
    displacementInformation (shellPacket r s α p q u v) x dir =
      phaseFisher r s u v (wavePhase (q - p) x + α) *
        (∑ μ : Fin 4, (q - p) μ * dir μ) ^ 2 := by
  unfold displacementInformation
  simp_rw [translationFisher_outer r s α p q u v _ _ x hψ]
  exact sum_outer (q - p) dir (phaseFisher r s u v (wavePhase (q - p) x + α))

theorem displacementInformation_axis (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0) :
    displacementInformation (shellPacket r s α p q u v) x (Pi.single μ 1) =
      translationFisher μ μ (shellPacket r s α p q u v) x := by
  rw [displacementInformation_shellPacket r s α p q u v x _ hψ, dot_single,
    translationFisher_outer r s α p q u v μ μ x hψ]
  ring

/-- Along one axis the floor is the reciprocal of `F_μμ`, when that entry is positive. -/
theorem precisionFloor_axis (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) (hψ : shellPacket r s α p q u v x ≠ 0)
    (_hF : translationFisher μ μ (shellPacket r s α p q u v) x ≠ 0) :
    precisionFloor (shellPacket r s α p q u v) x (Pi.single μ 1) =
      (translationFisher μ μ (shellPacket r s α p q u v) x)⁻¹ := by
  unfold precisionFloor
  rw [displacementInformation_axis r s α p q u v μ x hψ]

theorem displacement_kernel (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (x dir : Vec4)
    (hψ : shellPacket r s α p q u v x ≠ 0)
    (hphase : phaseFisher r s u v (wavePhase (q - p) x + α) ≠ 0) :
    displacementInformation (shellPacket r s α p q u v) x dir = 0 ↔
      ∑ μ : Fin 4, (q - p) μ * dir μ = 0 := by
  rw [displacementInformation_shellPacket r s α p q u v x dir hψ]
  constructor
  · intro h
    have hsq : (∑ μ : Fin 4, (q - p) μ * dir μ) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hphase
    exact sq_eq_zero_iff.mp hsq
  · intro h
    rw [h, zero_pow (by norm_num : 2 ≠ 0), mul_zero]

/-! ### A boost remixes the components and preserves the contraction -/

/-- Active boost in the `(t, x)` plane, with `cosh` and `sinh` of one rapidity. -/
def boost01 (ch sh : ℝ) (p : Vec4) : Vec4
  | 0 => ch * p 0 + sh * p 1
  | 1 => sh * p 0 + ch * p 1
  | 2 => p 2
  | 3 => p 3

/-- Matrix of `boost01` acting on covariant components. -/
def boost01Matrix (ch sh : ℝ) (μ ν : Fin 4) : ℝ :=
  match μ, ν with
  | 0, 0 => ch
  | 0, 1 => sh
  | 1, 0 => sh
  | 1, 1 => ch
  | 2, 2 => 1
  | 3, 3 => 1
  | _, _ => 0

theorem boost01_eq_sum (ch sh : ℝ) (p : Vec4) (μ : Fin 4) :
    boost01 ch sh p μ = ∑ ν : Fin 4, boost01Matrix ch sh μ ν * p ν := by
  fin_cases μ <;> simp [boost01, boost01Matrix, Fin.sum_univ_four]

theorem minkowskiQ_boost01 {ch sh : ℝ} (h : ch ^ 2 - sh ^ 2 = 1) (p : Vec4) :
    minkowskiQ (boost01 ch sh p) = minkowskiQ p := by
  rw [minkowskiQ_eq, minkowskiQ_eq]
  have hcross :
      -(ch * p 0 + sh * p 1) ^ 2 + (sh * p 0 + ch * p 1) ^ 2 =
        (ch ^ 2 - sh ^ 2) * (-(p 0) ^ 2 + (p 1) ^ 2) := by ring
  simp only [boost01]
  rw [hcross, h, one_mul]

/-- `η^{μν} F_μν` for an outer product `scale · δ ⊗ δ`. -/
def fisherContraction (scale : ℝ) (δ : Vec4) : ℝ :=
  ∑ μ : Fin 4, minkowskiEta μ μ * scale * δ μ * δ μ

theorem fisherContraction_eq (scale : ℝ) (δ : Vec4) :
    fisherContraction scale δ = scale * minkowskiQ δ := by
  unfold fisherContraction minkowskiQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

theorem fisherContraction_boost01 {ch sh : ℝ} (h : ch ^ 2 - sh ^ 2 = 1) (scale : ℝ)
    (δ : Vec4) :
    fisherContraction scale (boost01 ch sh δ) = fisherContraction scale δ := by
  rw [fisherContraction_eq, fisherContraction_eq, minkowskiQ_boost01 h]

theorem fisherOuter_transform (Λ : Fin 4 → Fin 4 → ℝ) (scale : ℝ) (δ : Vec4) (μ ν : Fin 4) :
    let δ' : Vec4 := fun ρ => ∑ α : Fin 4, Λ ρ α * δ α
    scale * δ' μ * δ' ν =
      ∑ α : Fin 4, ∑ β : Fin 4, Λ μ α * Λ ν β * (scale * δ α * δ β) := by
  intro δ'
  rw [mul_assoc]
  have hmul : δ' μ * δ' ν =
      ∑ α : Fin 4, ∑ β : Fin 4, (Λ μ α * δ α) * (Λ ν β * δ β) := by
    simp only [δ']
    rw [Finset.sum_mul_sum]
  rw [hmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

/-! ### Mass 3 -/

private theorem shellRest_phase_at (θ : ℝ) :
    wavePhase (shellRestQ - shellRestP) 0 + θ = θ := by
  rw [wavePhase_zero, zero_add]

theorem shellRest_translationFisher :
    ∃ θ : ℝ,
      let Ψ := shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
      phaseFisher 1 1 shellParticleP shellParticleQ θ = 544 / 625 ∧
        translationFisher 0 0 Ψ 0 = 0 ∧
          translationFisher 1 1 Ψ 0 = 34816 / 625 ∧
            translationFisher 0 1 Ψ 0 = 0 ∧
              precisionFloor Ψ 0 (Pi.single 1 1) = 625 / 34816 ∧
                (inner ℂ (Ψ 0) (positionOp 1 Ψ 0)).re / ‖Ψ 0‖ ^ 2 = 0 := by
  obtain ⟨θ, _, hF, _, hchart⟩ := shellRest_chartFisher.1
  refine ⟨θ, hF, ?_, ?_, ?_, ?_, ?_⟩
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    rw [translationFisher_outer 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0 0 0
        hψ, shellRest_phase_at, hF, shellRest_relative.1]
    norm_num
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    rw [translationFisher_diag_eq_chartFisher 1 1 θ shellRestP shellRestQ shellParticleP
        shellParticleQ 1 0 hψ, shellRest_phase_at, hchart]
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    rw [translationFisher_outer 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0 1 0
        hψ, shellRest_phase_at, hF, shellRest_relative.1]
    norm_num
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    have hpos : translationFisher 1 1
        (shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ) 0 ≠ 0 := by
      rw [translationFisher_diag_eq_chartFisher 1 1 θ shellRestP shellRestQ shellParticleP
          shellParticleQ 1 0 hψ, shellRest_phase_at, hchart]
      norm_num
    rw [precisionFloor_axis 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 1 0 hψ hpos,
      translationFisher_diag_eq_chartFisher 1 1 θ shellRestP shellRestQ shellParticleP
        shellParticleQ 1 0 hψ, shellRest_phase_at, hchart]
    norm_num
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    rw [position_reading (Ψ := shellPacket 1 1 θ shellRestP shellRestQ shellParticleP
        shellParticleQ) (μ := 1) (x := 0) hψ]
    simp

private theorem boost_rapidity_hyp :
    ((5 : ℝ) / 3) ^ 2 - (-4 / 3) ^ 2 = 1 := by norm_num

private theorem shellRest_boost_coords :
    boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP) 0 = 32 / 3 ∧
      boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP) 1 = -40 / 3 := by
  have hδ := shellRest_relative
  refine ⟨?_, ?_⟩
  · simp only [boost01, hδ.1, hδ.2.1]
    norm_num
  · simp only [boost01, hδ.1, hδ.2.1]
    norm_num

private theorem shellRest_minkowski_relative :
    minkowskiQ (shellRestQ - shellRestP) = 64 := by
  have hδ := shellRest_relative
  rw [minkowskiQ_eq, hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2]
  norm_num

theorem shellRest_boost_fisher :
    (shellRestQ - shellRestP) 0 = 0 ∧
      boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP) 0 = 32 / 3 ∧
        boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP) 1 = -40 / 3 ∧
          minkowskiQ (shellRestQ - shellRestP) = 64 ∧
            minkowskiQ (boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP)) = 64 ∧
              fisherContraction ((544 : ℝ) / 625) (shellRestQ - shellRestP) = 34816 / 625 ∧
                fisherContraction ((544 : ℝ) / 625)
                    (boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP)) = 34816 / 625 ∧
                  ((544 : ℝ) / 625) * (32 / 3) * (32 / 3) = 557056 / 5625 ∧
                    ((544 : ℝ) / 625) * ((-40 : ℝ) / 3) * ((-40 : ℝ) / 3) = 34816 / 225 ∧
                      ((544 : ℝ) / 625) * (32 / 3) * ((-40 : ℝ) / 3) = (-139264 : ℝ) / 1125 ∧
                        ((544 : ℝ) / 625) * (((32 : ℝ) / 3) ^ 2 + ((-40 : ℝ) / 3) ^ 2) ≠
                          34816 / 625 := by
  have hcoords := shellRest_boost_coords
  have hQ := shellRest_minkowski_relative
  have hQ' : minkowskiQ (boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP)) = 64 := by
    rw [minkowskiQ_boost01 boost_rapidity_hyp, hQ]
  refine ⟨shellRest_relative.1, hcoords.1, hcoords.2, hQ, hQ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fisherContraction_eq, hQ]
    norm_num
  · rw [fisherContraction_eq, hQ']
    norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-- The boosted components are `Λ F Λᵀ`, not a new scalar. -/
theorem shellRest_boost_tensor :
    (544 / 625) *
        (∑ α : Fin 4, boost01Matrix (5 / 3) (-4 / 3) 0 α * (shellRestQ - shellRestP) α) *
        (∑ β : Fin 4, boost01Matrix (5 / 3) (-4 / 3) 0 β * (shellRestQ - shellRestP) β) =
      ∑ α : Fin 4, ∑ β : Fin 4,
        boost01Matrix (5 / 3) (-4 / 3) 0 α * boost01Matrix (5 / 3) (-4 / 3) 0 β *
          ((544 / 625) * (shellRestQ - shellRestP) α * (shellRestQ - shellRestP) β) ∧
      (∑ α : Fin 4, boost01Matrix (5 / 3) (-4 / 3) 0 α * (shellRestQ - shellRestP) α) =
        32 / 3 ∧
        ((544 : ℝ) / 625) * (32 / 3) * (32 / 3) = 557056 / 5625 := by
  refine ⟨?_, ?_, by norm_num⟩
  · simpa using fisherOuter_transform (boost01Matrix (5 / 3) (-4 / 3)) ((544 : ℝ) / 625)
      (shellRestQ - shellRestP) 0 0
  · rw [← boost01_eq_sum]
    exact shellRest_boost_coords.1

theorem shellLab_translationFisher :
    let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
    let x := timeShift (-Real.pi / 2)
    translationFisher 0 0 Ψ x = 324 / 25 ∧
      translationFisher 1 1 Ψ x = 1296 / 25 ∧
        translationFisher 0 1 Ψ x = 648 / 25 ∧
          precisionFloor Ψ x (Pi.single 0 1) = 25 / 324 ∧
            (inner ℂ (Ψ x) (positionOp 0 Ψ x)).re / ‖Ψ x‖ ^ 2 = -Real.pi / 2 ∧
              -Real.pi / 2 ≠ (25 / 324 : ℝ) := by
  let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
  let x := timeShift (-Real.pi / 2)
  have hden : bornDensity Ψ x = 20 / 9 := shellLab_time_density.2.1
  have hψ : Ψ x ≠ 0 := by
    intro hz
    have hzero : bornDensity Ψ x = 0 := by rw [bornDensity, hz, norm_zero]; simp
    rw [hden] at hzero
    norm_num at hzero
  have hphase : wavePhase (restMomentum 3 - shellRestP) x =
      wavePhase (restMomentum 3 - shellRestP) (timeShift (-Real.pi / 2)) := rfl
  have hF := shellLab_phaseFisher.2.1
  have hF' : phaseFisher 1 1 shellParticleP shellLabSpinor
      (wavePhase (restMomentum 3 - shellRestP) x) = 81 / 25 := by
    rw [hphase]
    exact hF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [translationFisher_outer 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
        0 0 x hψ, add_zero, hF', shellLab_relative.1]
    norm_num
  · rw [translationFisher_outer 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
        1 1 x hψ, add_zero, hF', shellLab_relative.2.1]
    norm_num
  · rw [translationFisher_outer 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
        0 1 x hψ, add_zero, hF', shellLab_relative.1, shellLab_relative.2.1]
    norm_num
  · have hpos : translationFisher 0 0 Ψ x ≠ 0 := by
      rw [translationFisher_outer 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
          0 0 x hψ, add_zero, hF', shellLab_relative.1]
      norm_num
    rw [precisionFloor_axis 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor 0 x
        hψ hpos, translationFisher_outer 1 1 0 shellRestP (restMomentum 3) shellParticleP
        shellLabSpinor 0 0 x hψ, add_zero, hF', shellLab_relative.1]
    norm_num
  · rw [position_reading hψ]
    simp [x, timeShift]
  · intro h
    have hπ : Real.pi = -50 / 324 := by linarith
    have hneg : Real.pi < 0 := by
      rw [hπ]
      norm_num
    exact absurd hneg (not_lt_of_gt Real.pi_pos)

theorem shellLab_quadrature_cross :
    ∃ θ : ℝ,
      phaseFisher 1 1 shellParticleP shellLabSpinor θ = 81 / 289 ∧
        phaseFisher 1 1 shellParticleP shellLabSpinor θ * (-2) * (-2) = 324 / 289 ∧
          phaseFisher 1 1 shellParticleP shellLabSpinor θ * (-4) * (-4) = 1296 / 289 ∧
            phaseFisher 1 1 shellParticleP shellLabSpinor θ * (-2) * (-4) = 648 / 289 ∧
              (324 / 289 : ℝ) ≠ 1296 / 289 := by
  obtain ⟨θ, hcross, _hchart⟩ := shellLab_chartFisher.1
  have hden : phaseCurveNormSq 1 1 shellParticleP shellLabSpinor θ ≠ 0 := by
    have hsq : phaseCurveNormSq 1 1 shellParticleP shellLabSpinor θ = 68 / 9 := by
      unfold phaseCurveNormSq
      rw [hcross, mul_zero, add_zero, bornWeight_eq, bornWeight_eq]
      simp only [abs_one, one_mul, shellRest_norms.1, shellLab_norm]
      norm_num
    rw [hsq]
    norm_num
  have hF : phaseFisher 1 1 shellParticleP shellLabSpinor θ =
      shellDeficit 1 1 shellParticleP shellLabSpinor :=
    phaseFisher_quadrature hcross hden
  refine ⟨θ, ?_, ?_, ?_, ?_, by norm_num⟩
  · rw [hF, shellLab_deficit]
  · rw [hF, shellLab_deficit]
    norm_num
  · rw [hF, shellLab_deficit]
    norm_num
  · rw [hF, shellLab_deficit]
    norm_num

end Logic

end DoubleSpacetime
