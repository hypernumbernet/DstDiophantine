import DstDiophantine.Logic.Quantum.ChartOperators

/-!
# Newton–Wigner localization as chart information

Newton and Wigner ask for a position operator on the Hilbert space of one elementary system, with
`[Q, P] = i`, translating by the shift, and with localized eigenstates. DST splits that demand.

* No endomorphism pair of `DualSpinor` or `DiracSpinor` has commutator `i I`. The operator does not
  live on the carrier.
* Multiplication by the chart coordinate does translate by the shift and does satisfy the canonical
  commutator with `-i∂`. Every continuous eigenfield of that multiplication is the zero field, so
  the localized state is not a chart field.
* A single momentum, the elementary system, has constant Born density. Two chart points are
  indistinguishable. Position information is the failure of that constancy. It is a function of the
  relative phase `(q − p)·x` of two momenta, periodic along that axis, and not confined to a box.
-/

namespace DstDiophantine

namespace Logic

open Complex

/-! ### The carrier admits no Newton–Wigner pair -/

/-- Position and momentum endomorphisms with canonical commutator. -/
def NewtonWignerPair {H : Type} [AddCommGroup H] [Module ℂ H]
    (Q P : H →ₗ[ℂ] H) : Prop :=
  Q.comp P - P.comp Q = I • LinearMap.id

theorem no_newtonWignerPair_dual (Q P : DualSpinor →ₗ[ℂ] DualSpinor) :
    ¬ NewtonWignerPair Q P :=
  no_ccr_dualSpinor Q P

theorem no_newtonWignerPair_dirac (Q P : DiracSpinor →ₗ[ℂ] DiracSpinor) :
    ¬ NewtonWignerPair Q P :=
  no_ccr_diracSpinor Q P

/-! ### Chart position translates, and has no continuous eigenfield -/

theorem chartTranslate_position_shift (ν : Fin 4) (a : Vec4) (Ψ : Vec4 → DiracSpinor)
    (x : Vec4) :
    chartTranslate a (positionOp ν Ψ) x =
      positionOp ν (chartTranslate a Ψ) x + (a ν : ℂ) • chartTranslate a Ψ x := by
  unfold chartTranslate positionOp
  have hcoord : ((x + a) ν : ℂ) = (x ν : ℂ) + (a ν : ℂ) := by
    simp [Pi.add_apply, Complex.ofReal_add]
  rw [hcoord, add_smul]

theorem continuous_chartPosition_eigenfield_zero {ν : Fin 4} {lam : ℂ}
    {Ψ : Vec4 → DiracSpinor} (hcont : Continuous Ψ) (hX : PositionEigen ν lam Ψ) :
    Ψ = 0 := by
  funext x
  exact continuous_positionEigen_zero hcont hX x

theorem no_continuous_localized_chartField (ν : Fin 4) (lam : ℂ) :
    ¬ ∃ Ψ : Vec4 → DiracSpinor,
      Continuous Ψ ∧ (∃ x, Ψ x ≠ 0) ∧ PositionEigen ν lam Ψ := by
  intro ⟨Ψ, hcont, ⟨x, hx⟩, hX⟩
  exact hx (congrFun (continuous_chartPosition_eigenfield_zero hcont hX) x)

/-! ### Position information is Born contrast across the chart -/

/-- Two chart points carry different Born density. -/
def ChartPositionInfo (Ψ : Vec4 → DiracSpinor) : Prop :=
  ∃ x y : Vec4, bornDensity Ψ x ≠ bornDensity Ψ y

/-- Signed difference of Born densities. -/
noncomputable def chartContrast (Ψ : Vec4 → DiracSpinor) (x y : Vec4) : ℝ :=
  bornDensity Ψ x - bornDensity Ψ y

theorem bornDensity_chartTranslate (a : Vec4) (Ψ : Vec4 → DiracSpinor) (x : Vec4) :
    bornDensity (chartTranslate a Ψ) x = bornDensity Ψ (x + a) := rfl

theorem chartContrast_momentumEigen {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (h : MomentumEigen p Ψ) (x y : Vec4) : chartContrast Ψ x y = 0 := by
  unfold chartContrast
  rw [bornDensity_momentumEigen h x y, sub_self]

theorem momentumEigen_no_chartPositionInfo {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (h : MomentumEigen p Ψ) : ¬ ChartPositionInfo Ψ := by
  intro ⟨x, y, hxy⟩
  exact hxy (sub_eq_zero.mp (chartContrast_momentumEigen h x y))

theorem planeWave_no_chartPositionInfo (p : Vec4) (u : DiracSpinor) :
    ¬ ChartPositionInfo (planeWave p u) :=
  momentumEigen_no_chartPositionInfo (planeWave_momentumEigen p u)

theorem momentumEigen_bornDensity_const {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (h : MomentumEigen p Ψ) (x : Vec4) : bornDensity Ψ x = ‖Ψ 0‖ ^ 2 := by
  rw [bornDensity_momentumEigen h x 0]
  rfl

theorem momentumEigen_bornDensity_pos {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (h : MomentumEigen p Ψ) (h0 : Ψ 0 ≠ 0) (x : Vec4) : 0 < bornDensity Ψ x := by
  rw [momentumEigen_bornDensity_const h x]
  exact pow_pos (norm_pos_iff.mpr h0) 2

/-- Vanishes once some coordinate leaves the slab `(-R, R)`. -/
def BoxLocalized (Ψ : Vec4 → DiracSpinor) : Prop :=
  ∃ R : ℝ, ∀ x : Vec4, (∃ μ : Fin 4, R < |x μ|) → Ψ x = 0

theorem momentumEigen_not_boxLocalized {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (h : MomentumEigen p Ψ) (h0 : Ψ 0 ≠ 0) : ¬ BoxLocalized Ψ := by
  intro ⟨R, hR⟩
  let x : Vec4 := Pi.single 0 (|R| + 1)
  have hx0 : x 0 = |R| + 1 := by simp [x]
  have habs : |x 0| = |R| + 1 := by
    rw [hx0]
    exact abs_of_nonneg (by positivity)
  have hlt : R < |x 0| := by
    rw [habs]
    linarith [le_abs_self R]
  have hden : 0 < bornDensity Ψ x := momentumEigen_bornDensity_pos h h0 x
  have hne : Ψ x ≠ 0 := by
    intro hz
    rw [bornDensity, hz, norm_zero] at hden
    simp at hden
  exact hne (hR x ⟨0, hlt⟩)

theorem chartContrast_eq_relativePhase (p q : Vec4) (u : DiracSpinor) (x y : Vec4) :
    chartContrast (equalPacket p q u) x y =
      4 * (Real.cos (wavePhase (q - p) x / 2) ^ 2 -
            Real.cos (wavePhase (q - p) y / 2) ^ 2) * ‖u‖ ^ 2 := by
  unfold chartContrast
  rw [bornDensity_equalPacket, bornDensity_equalPacket]
  ring

theorem equalPacket_chartContrast_node {p q : Vec4} (hpq : p ≠ q) (u : DiracSpinor) :
    ∃ y : Vec4, chartContrast (equalPacket p q u) 0 y = 4 * ‖u‖ ^ 2 := by
  obtain ⟨y, hy⟩ := equalPacket_node hpq u
  refine ⟨y, ?_⟩
  unfold chartContrast
  have hy0 : bornDensity (equalPacket p q u) y = 0 := by
    rw [bornDensity, hy, norm_zero]
    simp
  have hx : bornDensity (equalPacket p q u) 0 = 4 * ‖u‖ ^ 2 := by
    rw [bornDensity_equalPacket, wavePhase_zero, zero_div, Real.cos_zero, one_pow]
    ring
  rw [hy0, hx, sub_zero]

theorem equalPacket_chartPositionInfo {p q : Vec4} (hpq : p ≠ q) {u : DiracSpinor}
    (hu : u ≠ 0) : ChartPositionInfo (equalPacket p q u) := by
  obtain ⟨y, hy⟩ := equalPacket_chartContrast_node hpq u
  refine ⟨0, y, ?_⟩
  intro hden
  have hzero : chartContrast (equalPacket p q u) 0 y = 0 := by
    unfold chartContrast
    rw [hden, sub_self]
  rw [hzero] at hy
  have hpos : 0 < 4 * ‖u‖ ^ 2 := mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hu) 2)
  linarith

/-- A carrier of positive weight can still carry no chart-position information. -/
theorem positive_weight_zero_chartContrast {u : DiracSpinor} (hu : u ≠ 0) (p x y : Vec4) :
    0 < ‖u‖ ^ 2 ∧ chartContrast (planeWave p u) x y = 0 :=
  ⟨pow_pos (norm_pos_iff.mpr hu) 2, chartContrast_momentumEigen (planeWave_momentumEigen p u) x y⟩

theorem chartPositionInfo_chartTranslate (a : Vec4) (Ψ : Vec4 → DiracSpinor) :
    ChartPositionInfo (chartTranslate a Ψ) ↔ ChartPositionInfo Ψ := by
  constructor
  · intro ⟨x, y, h⟩
    refine ⟨x + a, y + a, ?_⟩
    simpa [bornDensity_chartTranslate] using h
  · intro ⟨x, y, h⟩
    refine ⟨x - a, y - a, ?_⟩
    simpa [bornDensity_chartTranslate] using h

/-! ### The contrast is periodic, so it is not a point -/

theorem bornDensity_equalPacket_period (p q : Vec4) (μ : Fin 4) (hμ : (q - p) μ ≠ 0)
    (u : DiracSpinor) (x : Vec4) :
    let τ := 2 * Real.pi / (q - p) μ
    bornDensity (equalPacket p q u) (x + τ • Pi.single μ (1 : ℝ)) =
      bornDensity (equalPacket p q u) x := by
  intro τ
  rw [bornDensity_equalPacket, bornDensity_equalPacket]
  have hphase : wavePhase (q - p) (x + τ • Pi.single μ (1 : ℝ)) =
      wavePhase (q - p) x + 2 * Real.pi := by
    rw [wavePhase_add_right, wavePhase_smul_right, wavePhase_single]
    have hτ : τ * (q - p) μ = 2 * Real.pi := by
      simpa [τ] using div_mul_cancel₀ (2 * Real.pi) hμ
    rw [hτ]
  rw [hphase]
  have hcos : Real.cos ((wavePhase (q - p) x + 2 * Real.pi) / 2) =
      -Real.cos (wavePhase (q - p) x / 2) := by
    have hsplit : (wavePhase (q - p) x + 2 * Real.pi) / 2 =
        wavePhase (q - p) x / 2 + Real.pi := by ring
    rw [hsplit, Real.cos_add_pi]
  rw [hcos, neg_sq]

theorem equalPacket_not_boxLocalized {p q : Vec4} (hpq : p ≠ q) {u : DiracSpinor}
    (hu : u ≠ 0) : ¬ BoxLocalized (equalPacket p q u) := by
  intro ⟨R, hR⟩
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  obtain ⟨μ, hμ⟩ := by
    refine (not_forall.mp ?_ : ∃ μ : Fin 4, ¬ (q - p) μ = 0)
    intro h
    apply hδ
    ext ν
    exact h ν
  let r : ℝ := R * |(q - p) μ| / (2 * Real.pi)
  let k : ℕ := Nat.floor r + 1
  let t : ℝ := 2 * Real.pi * (k : ℝ) / (q - p) μ
  let x : Vec4 := t • Pi.single μ (1 : ℝ)
  have hk : r < (k : ℝ) := by
    simpa [k] using Nat.lt_floor_add_one r
  have ht_abs : |t| = 2 * Real.pi * (k : ℝ) / |(q - p) μ| := by
    have hnum : 0 ≤ 2 * Real.pi * (k : ℝ) := by positivity
    simp only [t, abs_div, abs_of_nonneg hnum]
  have hlt : R < |x μ| := by
    have hxμ : |x μ| = |t| := by simp [x, Pi.smul_apply, Pi.single_eq_same]
    rw [hxμ, ht_abs]
    have hpos : 0 < 2 * Real.pi / |(q - p) μ| := by positivity
    have hmul := mul_lt_mul_of_pos_left hk hpos
    have hleft : 2 * Real.pi / |(q - p) μ| * r = R := by
      unfold r
      field_simp
    rw [hleft] at hmul
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hphase : wavePhase (q - p) x = 2 * Real.pi * (k : ℝ) := by
    rw [show x = t • Pi.single μ (1 : ℝ) from rfl, wavePhase_smul_right, wavePhase_single]
    unfold t
    field_simp
  have hcoeff : exp (I * (wavePhase p x : ℂ)) + exp (I * (wavePhase q x : ℂ)) =
      (2 : ℂ) * exp (I * (wavePhase p x : ℂ)) := by
    have hpull : exp (I * (wavePhase q x : ℂ)) =
        exp (I * (wavePhase p x : ℂ)) * exp (I * (wavePhase (q - p) x : ℂ)) := by
      rw [← exp_add, wavePhase_sub_left, ofReal_sub]
      apply congrArg exp
      ring
    have hone : exp (I * (wavePhase (q - p) x : ℂ)) = 1 := by
      rw [hphase]
      have hexp : I * ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) = (k : ℂ) * (2 * ↑Real.pi * I) := by
        push_cast
        ring
      rw [hexp, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
    rw [hpull, hone, mul_one]
    ring
  have hne : equalPacket p q u x ≠ 0 := by
    intro hz
    unfold equalPacket momentumSum planeWave at hz
    rw [Pi.add_apply, ← add_smul, hcoeff] at hz
    rcases smul_eq_zero.mp hz with hc | hu0
    · rw [mul_eq_zero] at hc
      rcases hc with h2 | hexp
      · norm_num at h2
      · exact exp_ne_zero _ hexp
    · exact hu hu0
  exact hne (hR x ⟨μ, hlt⟩)

/-! ### A calculated fringe -/

/-- On the first spatial axis, momenta `0` and `e₁` interfere with contrast `4` between the origin
and the node at `π e₁`. -/
theorem axis_fringe_contrast :
    let p : Vec4 := 0
    let q : Vec4 := Pi.single 1 1
    let u : DiracSpinor := EuclideanSpace.single 0 1
    let y : Vec4 := Pi.single 1 Real.pi
    chartContrast (equalPacket p q u) 0 y = 4 := by
  intro p q u y
  have hpq : p ≠ q := by
    intro h
    have h1 := congrFun h 1
    simp [p, q] at h1
  have hsq : ‖u‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
    simp [u]
  have hphase : wavePhase (q - p) y = Real.pi := by
    have hq : q - p = q := by simp [p]
    rw [hq]
    have hy : y = Real.pi • Pi.single 1 (1 : ℝ) := by
      ext μ
      fin_cases μ <;> simp [y]
    rw [hy, wavePhase_smul_right, wavePhase_single]
    simp [q]
  rw [chartContrast_eq_relativePhase, hphase, wavePhase_zero, zero_div, Real.cos_zero,
    Real.cos_pi_div_two, hsq]
  norm_num

end Logic

end DstDiophantine
