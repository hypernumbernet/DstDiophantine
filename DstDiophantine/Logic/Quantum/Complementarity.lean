import DstDiophantine.Logic.Quantum.DiracField

/-!
# Position and momentum on the de Broglie phase

The body of a state is a dual vector. A chart point enters only through the
phase `p_μ x^μ` of a plane wave.

A wave of one momentum has density `‖u‖²` at every chart point, and the
value at one point is a unit-modulus phase times the value at any other.
If the amplitude does not vanish, the wave vanishes nowhere. A field that
translation multiplies by one such phase — a momentum eigenfield — inherits
that rigidity: a single zero forces the field to vanish everywhere.

A nonzero solution of one nonzero mass determines its four-momentum. The
sum of two plane waves of distinct momenta, with neither amplitude zero, is
therefore not a wave of any one momentum. Where the two amplitudes are the
same vector, the density is `4 cos²((q−p)·x/2) ‖u‖²` and does vanish.

Translating the argument by `a` and multiplying by the phase `e^{i k·x}`
differ by `e^{i k·a}`. This is the Weyl relation of the phase. It is not a
position operator, not the canonical commutator on a common domain, and not
an uncertainty bound for orbital angles.
-/

namespace DstDiophantine

namespace Logic

open Complex

/-! ### The phase is bilinear -/

theorem wavePhase_add_right (p x a : Vec4) :
    wavePhase p (x + a) = wavePhase p x + wavePhase p a := by
  unfold wavePhase
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem wavePhase_add_left (p k x : Vec4) :
    wavePhase (p + k) x = wavePhase p x + wavePhase k x := by
  unfold wavePhase
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem wavePhase_sub_left (p q x : Vec4) :
    wavePhase (q - p) x = wavePhase q x - wavePhase p x := by
  unfold wavePhase
  simp [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem wavePhase_smul_right (p : Vec4) (c : ℝ) (x : Vec4) :
    wavePhase p (c • x) = c * wavePhase p x := by
  unfold wavePhase
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

theorem wavePhase_pi_axis {δ : Vec4} (μ : Fin 4) (hμ : δ μ ≠ 0) :
    wavePhase δ (Pi.single μ (Real.pi / δ μ)) = Real.pi := by
  have hsingle : Pi.single μ (Real.pi / δ μ) =
      (Real.pi / δ μ) • Pi.single μ (1 : ℝ) := by
    ext ν
    by_cases hν : ν = μ
    · subst hν
      simp
    · simp [Pi.single_eq_of_ne hν]
  rw [hsingle, wavePhase_smul_right, wavePhase_single]
  exact div_mul_cancel₀ Real.pi hμ

theorem exists_wavePhase_pi {δ : Vec4} (hδ : δ ≠ 0) :
    ∃ x : Vec4, wavePhase δ x = Real.pi := by
  have hcomp : ∃ μ : Fin 4, δ μ ≠ 0 := by
    by_contra h
    push Not at h
    apply hδ
    ext μ
    exact h μ
  obtain ⟨μ, hμ⟩ := hcomp
  exact ⟨Pi.single μ (Real.pi / δ μ), wavePhase_pi_axis μ hμ⟩

theorem norm_exp_I (θ : ℝ) : ‖exp (I * (θ : ℂ))‖ = 1 := by
  rw [norm_exp]
  have hre : (I * (θ : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

theorem exp_I_pi : exp (I * (Real.pi : ℂ)) = -1 := by
  rw [show I * (Real.pi : ℂ) = (Real.pi : ℂ) * I by ring]
  exact exp_pi_mul_I

/-! ### One momentum is the same ray at every chart point -/

/-- The value at one chart point lies on the ray of the value at another
when one is a unit-modulus phase times the other. -/
def SameRay (ψ φ : DiracSpinor) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • ψ

/-- Born density `Ψ†Ψ`. -/
noncomputable def bornDensity (Ψ : Vec4 → DiracSpinor) (x : Vec4) : ℝ :=
  ‖Ψ x‖ ^ 2

theorem planeWave_translate (p : Vec4) (u : DiracSpinor) (x a : Vec4) :
    planeWave p u (x + a) = exp (I * (wavePhase p a : ℂ)) • planeWave p u x := by
  unfold planeWave
  rw [wavePhase_add_right, ofReal_add]
  have hsplit : I * ((wavePhase p x : ℂ) + (wavePhase p a : ℂ)) =
      I * (wavePhase p a : ℂ) + I * (wavePhase p x : ℂ) := by ring
  rw [hsplit, exp_add, ← smul_smul]

theorem planeWave_norm (p : Vec4) (u : DiracSpinor) (x : Vec4) :
    ‖planeWave p u x‖ = ‖u‖ := by
  unfold planeWave
  rw [norm_smul, norm_exp_I, one_mul]

theorem planeWave_ne_zero {u : DiracSpinor} (hu : u ≠ 0) (p x : Vec4) :
    planeWave p u x ≠ 0 := by
  intro h
  unfold planeWave at h
  rcases smul_eq_zero.mp h with hz | hz
  · exact exp_ne_zero _ hz
  · exact hu hz

theorem bornDensity_planeWave (p : Vec4) (u : DiracSpinor) (x : Vec4) :
    bornDensity (planeWave p u) x = ‖u‖ ^ 2 := by
  unfold bornDensity
  rw [planeWave_norm]

theorem planeWave_sameRay (p : Vec4) (u : DiracSpinor) (x y : Vec4) :
    SameRay (planeWave p u x) (planeWave p u y) := by
  refine ⟨exp (I * ((wavePhase p y - wavePhase p x : ℝ) : ℂ)), norm_exp_I _, ?_⟩
  unfold planeWave
  rw [smul_smul, ← exp_add, ofReal_sub, mul_sub, sub_add_cancel]

/-- A wave of one momentum has one density at every chart point. -/
theorem bornDensity_planeWave_const (p : Vec4) (u : DiracSpinor) (x y : Vec4) :
    bornDensity (planeWave p u) x = bornDensity (planeWave p u) y := by
  rw [bornDensity_planeWave, bornDensity_planeWave]

/-! ### Translation character -/

/-- Translation by `a` multiplies the field by the phase `e^{i p·a}`. -/
def MomentumEigen (p : Vec4) (Ψ : Vec4 → DiracSpinor) : Prop :=
  ∀ x a, Ψ (x + a) = exp (I * (wavePhase p a : ℂ)) • Ψ x

theorem planeWave_momentumEigen (p : Vec4) (u : DiracSpinor) :
    MomentumEigen p (planeWave p u) :=
  fun x a => planeWave_translate p u x a

theorem momentumEigen_iff_phase {p : Vec4} {Ψ : Vec4 → DiracSpinor} :
    MomentumEigen p Ψ ↔ ∀ x, Ψ x = exp (I * (wavePhase p x : ℂ)) • Ψ 0 := by
  constructor
  · intro h x
    simpa [zero_add] using h 0 x
  · intro h x a
    rw [h (x + a), h x, smul_smul, ← exp_add, wavePhase_add_right, ofReal_add]
    have hsplit : I * ((wavePhase p x : ℂ) + (wavePhase p a : ℂ)) =
        I * (wavePhase p a : ℂ) + I * (wavePhase p x : ℂ) := by ring
    rw [hsplit]

/-- A momentum eigenfield with one zero vanishes at every chart point. -/
theorem momentumEigen_zero {p : Vec4} {Ψ : Vec4 → DiracSpinor}
    (h : MomentumEigen p Ψ) {x : Vec4} (hx : Ψ x = 0) (y : Vec4) : Ψ y = 0 := by
  have hy := h x (y - x)
  rw [hx, smul_zero] at hy
  have hxy : x + (y - x) = y := by rw [add_comm, sub_add_cancel]
  rw [hxy] at hy
  exact hy

theorem momentumEigen_planeWave_eq {p q : Vec4} {u : DiracSpinor}
    (h : MomentumEigen p (planeWave q u)) (hu : u ≠ 0) : p = q := by
  have hphase : ∀ a, exp (I * (wavePhase (q - p) a : ℂ)) = 1 := by
    intro a
    have ha := h 0 a
    unfold planeWave at ha
    rw [zero_add, wavePhase_zero, ofReal_zero, mul_zero, exp_zero, one_smul] at ha
    have hsub : (exp (I * (wavePhase q a : ℂ)) - exp (I * (wavePhase p a : ℂ))) • u = 0 := by
      rw [sub_smul, ha, sub_self]
    rcases smul_eq_zero.mp hsub with hc | hc
    · rw [sub_eq_zero] at hc
      rw [wavePhase_sub_left, ofReal_sub, mul_sub, exp_sub, hc, div_self (exp_ne_zero _)]
    · exact absurd hc hu
  ext μ
  by_contra hμ
  have hδ : (q - p) μ ≠ 0 := by
    rw [Pi.sub_apply, sub_ne_zero]
    intro hqp
    exact hμ hqp.symm
  have hx := hphase (Pi.single μ (Real.pi / (q - p) μ))
  rw [wavePhase_pi_axis μ hδ, exp_I_pi] at hx
  exact absurd hx (by norm_num)

/-- A nonzero solution of one nonzero mass determines its four-momentum. -/
theorem diracMomentum_unique {m : ℝ} {p q : Vec4} {Ψ : DiracSpinor}
    (hm : m ≠ 0) (hΨ : Ψ ≠ 0)
    (hp : DiracMomentum m p Ψ) (hq : DiracMomentum m q Ψ) : p = q := by
  obtain ⟨hp0, hS⟩ := diracScalar_self_eq hm hΨ hp
  have hSne : diracScalar Ψ Ψ ≠ 0 := by
    rw [hS]
    exact ofReal_ne_zero.mpr
      (mul_ne_zero (div_ne_zero hm hp0) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hΨ)))
  ext μ
  have hpcur := diracCurrent_gordon hp hp μ
  have hqcur := diracCurrent_gordon hq hq μ
  have hR : -I * ((minkowskiEta μ μ * p μ : ℝ) : ℂ) * diracScalar Ψ Ψ =
      -I * ((minkowskiEta μ μ * q μ : ℝ) : ℂ) * diracScalar Ψ Ψ := by
    rw [← hpcur, hqcur]
  have hmid := mul_right_cancel₀ hSne hR
  have hsame := mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero) hmid
  have hre : minkowskiEta μ μ * p μ = minkowskiEta μ μ * q μ := by
    exact_mod_cast hsame
  have hη : minkowskiEta μ μ ≠ 0 := by
    rw [minkowskiEta_diag]
    fin_cases μ <;> norm_num [w31]
  exact mul_left_cancel₀ hη hre

/-! ### Two momenta are not one momentum -/

/-- Sum of two plane waves. -/
noncomputable def momentumSum (p q : Vec4) (u v : DiracSpinor) : Vec4 → DiracSpinor :=
  planeWave p u + planeWave q v

private theorem cancel_I_coeff (c : ℝ) (w : DiracSpinor) :
    (-I) • ((I * (c : ℂ)) • w) = (c : ℂ) • w := by
  rw [smul_smul, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]

private theorem transport_phase (α β : ℂ) (w z : DiracSpinor)
    (h : exp α • w + exp β • z = 0) :
    w + exp (β - α) • z = 0 := by
  have hmul := congrArg (fun t : DiracSpinor => exp (-α) • t) h
  rw [smul_add, smul_zero] at hmul
  have hw : exp (-α) • (exp α • w) = w := by
    rw [smul_smul, ← exp_add, neg_add_cancel, exp_zero, one_smul]
  have hz : exp (-α) • (exp β • z) = exp (β - α) • z := by
    rw [smul_smul, ← exp_add, add_comm, sub_eq_add_neg]
  rw [hw, hz] at hmul
  exact hmul

theorem momentumSum_partial (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4) (x : Vec4) :
    partialD (momentumSum p q u v) μ x =
      (I * (p μ : ℂ)) • planeWave p u x + (I * (q μ : ℂ)) • planeWave q v x := by
  unfold partialD momentumSum
  rw [fderiv_add ((differentiable_planeWave p u) x) ((differentiable_planeWave q v) x),
    add_apply]
  have hp := planeWave_partialD p u μ x
  have hq := planeWave_partialD q v μ x
  unfold partialD at hp hq
  rw [hp, hq]

theorem momentumSum_not_eigen {p q : Vec4} (hpq : p ≠ q) {u v : DiracSpinor}
    (hu : u ≠ 0) (hv : v ≠ 0) (r : Vec4) :
    ¬ MomentumEigen r (momentumSum p q u v) := by
  intro h
  have hpw : momentumSum p q u v = planeWave r (momentumSum p q u v 0) := by
    funext x
    simpa [planeWave] using (momentumEigen_iff_phase.mp h) x
  have hcoeff : ∀ x μ,
      (p μ : ℂ) • planeWave p u x + (q μ : ℂ) • planeWave q v x =
        (r μ : ℂ) • momentumSum p q u v x := by
    intro x μ
    have hpartial := momentumSum_partial p q u v μ x
    have hright : partialD (momentumSum p q u v) μ x =
        (I * (r μ : ℂ)) • momentumSum p q u v x := by
      rw [hpw]
      exact planeWave_partialD r (momentumSum p q u v 0) μ x
    rw [hright] at hpartial
    apply_fun (fun w : DiracSpinor => (-I) • w) at hpartial
    rw [smul_add, cancel_I_coeff, cancel_I_coeff, cancel_I_coeff] at hpartial
    exact hpartial.symm
  have hcancel : ∀ x μ,
      exp (I * (wavePhase p x : ℂ)) • (((p μ - r μ : ℝ) : ℂ) • u) +
        exp (I * (wavePhase q x : ℂ)) • (((q μ - r μ : ℝ) : ℂ) • v) = 0 := by
    intro x μ
    have hμeq := hcoeff x μ
    have hdiff : ((p μ : ℂ) - (r μ : ℂ)) • planeWave p u x +
        ((q μ : ℂ) - (r μ : ℂ)) • planeWave q v x = 0 := by
      have hsm : (r μ : ℂ) • momentumSum p q u v x =
          (r μ : ℂ) • planeWave p u x + (r μ : ℂ) • planeWave q v x := by
        rw [momentumSum, Pi.add_apply, smul_add]
      rw [hsm] at hμeq
      have hsub : (p μ : ℂ) • planeWave p u x + (q μ : ℂ) • planeWave q v x -
          ((r μ : ℂ) • planeWave p u x + (r μ : ℂ) • planeWave q v x) = 0 := by
        rw [hμeq, sub_self]
      rw [sub_smul, sub_smul]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    unfold planeWave at hdiff
    rw [← ofReal_sub, ← ofReal_sub] at hdiff
    simpa [smul_smul, mul_comm] using hdiff
  have hline : ∀ x μ,
      ((p μ - r μ : ℝ) : ℂ) • u +
        exp (I * (wavePhase (q - p) x : ℂ)) • (((q μ - r μ : ℝ) : ℂ) • v) = 0 := by
    intro x μ
    have hx := hcancel x μ
    have htr := transport_phase (I * (wavePhase p x : ℂ)) (I * (wavePhase q x : ℂ))
      (((p μ - r μ : ℝ) : ℂ) • u) (((q μ - r μ : ℝ) : ℂ) • v) hx
    have hrel : I * (wavePhase q x : ℂ) - I * (wavePhase p x : ℂ) =
        I * (wavePhase (q - p) x : ℂ) := by
      rw [← mul_sub, wavePhase_sub_left, ofReal_sub]
    rw [hrel] at htr
    exact htr
  have hμne : ∃ μ : Fin 4, p μ ≠ q μ := by
    by_contra hnot
    push Not at hnot
    exact hpq (funext hnot)
  obtain ⟨μ, hμ⟩ := hμne
  have hδ : (q - p) μ ≠ 0 := by
    rw [Pi.sub_apply, sub_ne_zero]
    exact hμ.symm
  have h0 := hline 0 μ
  have hπ := hline (Pi.single μ (Real.pi / (q - p) μ)) μ
  rw [wavePhase_zero, ofReal_zero, mul_zero, exp_zero, one_smul] at h0
  rw [wavePhase_pi_axis μ hδ, exp_I_pi, neg_one_smul] at hπ
  set wp : DiracSpinor := ((p μ - r μ : ℝ) : ℂ) • u
  set wq : DiracSpinor := ((q μ - r μ : ℝ) : ℂ) • v
  have h0' : wp + wq = 0 := by simpa [wp, wq] using h0
  have hπ' : wp - wq = 0 := by simpa [wp, wq, sub_eq_add_neg] using hπ
  have hwp : (2 : ℂ) • wp = 0 := by
    have hsum : wp + wp = (wp + wq) + (wp - wq) := by abel
    rw [two_smul, hsum, h0', hπ', add_zero]
  have hwq : (2 : ℂ) • wq = 0 := by
    have hsub : wq + wq = (wp + wq) - (wp - wq) := by abel
    rw [two_smul, hsub, h0', hπ', sub_zero]
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hwp0 : wp = 0 := (smul_eq_zero.mp hwp).resolve_left h2
  have hwq0 : wq = 0 := (smul_eq_zero.mp hwq).resolve_left h2
  have hp0 : ((p μ - r μ : ℝ) : ℂ) = 0 := by
    rcases smul_eq_zero.mp hwp0 with hc | hu0
    · exact hc
    · exact absurd hu0 hu
  have hq0 : ((q μ - r μ : ℝ) : ℂ) = 0 := by
    rcases smul_eq_zero.mp hwq0 with hc | hv0
    · exact hc
    · exact absurd hv0 hv
  have hpμ : p μ = r μ := by
    have : p μ - r μ = 0 := by exact_mod_cast hp0
    linarith
  have hqμ : q μ = r μ := by
    have : q μ - r μ = 0 := by exact_mod_cast hq0
    linarith
  exact hμ (hpμ.trans hqμ.symm)

/-! ### Equal amplitudes write nodes -/

/-- Equal superposition of two momenta. -/
noncomputable def equalPacket (p q : Vec4) (u : DiracSpinor) : Vec4 → DiracSpinor :=
  momentumSum p q u u

private theorem norm_sq_real_add_I (x y : ℝ) :
    ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  have hxy : (x : ℂ) + (y : ℂ) * I = ⟨x, y⟩ := by
    apply Complex.ext <;> simp
  rw [hxy, ← normSq_eq_norm_sq, normSq_mk]
  ring

private theorem norm_sq_one_add_exp_I (θ : ℝ) :
    ‖(1 : ℂ) + exp (I * (θ : ℂ))‖ ^ 2 = 2 + 2 * Real.cos θ := by
  rw [show I * (θ : ℂ) = (θ : ℂ) * I by ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hsum : (1 : ℂ) + ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) =
      ((1 + Real.cos θ : ℝ) : ℂ) + (Real.sin θ : ℂ) * I := by
    push_cast
    ring
  rw [hsum, norm_sq_real_add_I]
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  calc
    (1 + Real.cos θ) ^ 2 + Real.sin θ ^ 2
      = 1 + 2 * Real.cos θ + (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    _ = 2 + 2 * Real.cos θ := by rw [hcs]; ring

private theorem two_add_two_cos (θ : ℝ) :
    2 + 2 * Real.cos θ = 4 * Real.cos (θ / 2) ^ 2 := by
  have h := Real.cos_sq (θ / 2)
  have h2 : 2 * (θ / 2) = θ := by ring
  rw [h2] at h
  calc
    2 + 2 * Real.cos θ = 4 * (1 / 2 + Real.cos θ / 2) := by ring
    _ = 4 * Real.cos (θ / 2) ^ 2 := by rw [← h]

theorem equalPacket_zero (p q : Vec4) (u : DiracSpinor) :
    equalPacket p q u 0 = (2 : ℂ) • u := by
  unfold equalPacket momentumSum planeWave
  rw [Pi.add_apply, wavePhase_zero, wavePhase_zero, ofReal_zero, mul_zero, exp_zero,
    one_smul, two_smul]

theorem bornDensity_equalPacket (p q : Vec4) (u : DiracSpinor) (x : Vec4) :
    bornDensity (equalPacket p q u) x =
      4 * Real.cos (wavePhase (q - p) x / 2) ^ 2 * ‖u‖ ^ 2 := by
  unfold bornDensity equalPacket momentumSum planeWave
  rw [Pi.add_apply, ← add_smul, norm_smul, mul_pow]
  have hfactor : ‖exp (I * (wavePhase p x : ℂ)) + exp (I * (wavePhase q x : ℂ))‖ ^ 2 =
      ‖(1 : ℂ) + exp (I * (wavePhase (q - p) x : ℂ))‖ ^ 2 := by
    have hpull : exp (I * (wavePhase p x : ℂ)) + exp (I * (wavePhase q x : ℂ)) =
        exp (I * (wavePhase p x : ℂ)) *
          (1 + exp (I * (wavePhase (q - p) x : ℂ))) := by
      rw [mul_add, mul_one, ← exp_add, wavePhase_sub_left, ofReal_sub, mul_sub]
      apply congrArg (fun z => exp (I * (wavePhase p x : ℂ)) + z)
      apply congrArg exp
      rw [add_comm, sub_add_cancel]
    rw [hpull, norm_mul, norm_exp_I, one_mul]
  rw [hfactor, norm_sq_one_add_exp_I, two_add_two_cos]

theorem equalPacket_node {p q : Vec4} (hpq : p ≠ q) (u : DiracSpinor) :
    ∃ x, equalPacket p q u x = 0 := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  obtain ⟨x, hx⟩ := exists_wavePhase_pi hδ
  refine ⟨x, ?_⟩
  unfold equalPacket momentumSum planeWave
  rw [Pi.add_apply, ← add_smul]
  have hsum : exp (I * (wavePhase p x : ℂ)) + exp (I * (wavePhase q x : ℂ)) = 0 := by
    have hβ : wavePhase q x = wavePhase p x + Real.pi := by
      have hsub := wavePhase_sub_left p q x
      rw [hx] at hsub
      linarith
    rw [hβ, ofReal_add, mul_add, exp_add, exp_I_pi]
    ring
  rw [hsum, zero_smul]

/-- A wave of one nonzero amplitude has no node; the equal superposition of
two distinct momenta does, so it is not a wave of any one momentum. -/
theorem equalPacket_not_eigen {p q : Vec4} (hpq : p ≠ q) {u : DiracSpinor}
    (hu : u ≠ 0) (r : Vec4) : ¬ MomentumEigen r (equalPacket p q u) := by
  intro h
  obtain ⟨x, hx⟩ := equalPacket_node hpq u
  have hzero := momentumEigen_zero h hx 0
  rw [equalPacket_zero] at hzero
  rcases smul_eq_zero.mp hzero with h2 | hu0
  · norm_num at h2
  · exact hu hu0

theorem bornDensity_equalPacket_varies {p q : Vec4} (hpq : p ≠ q) {u : DiracSpinor}
    (hu : u ≠ 0) :
    ∃ x y, bornDensity (equalPacket p q u) x ≠ bornDensity (equalPacket p q u) y := by
  obtain ⟨y, hy⟩ := equalPacket_node hpq u
  refine ⟨0, y, ?_⟩
  have hy0 : bornDensity (equalPacket p q u) y = 0 := by
    rw [bornDensity, hy, norm_zero]
    simp [sq]
  have hx : bornDensity (equalPacket p q u) 0 = 4 * ‖u‖ ^ 2 := by
    rw [bornDensity, equalPacket_zero, norm_smul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    ring
  rw [hy0, hx]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))

/-! ### Translation and a momentum shift -/

/-- Read the field at `x + a`. -/
def chartTranslate (a : Vec4) (Ψ : Vec4 → DiracSpinor) : Vec4 → DiracSpinor :=
  fun x => Ψ (x + a)

/-- Multiply by the phase `e^{i k·x}`, which shifts the momentum of a plane wave by `k`. -/
noncomputable def momentumKick (k : Vec4) (Ψ : Vec4 → DiracSpinor) : Vec4 → DiracSpinor :=
  fun x => exp (I * (wavePhase k x : ℂ)) • Ψ x

theorem momentumKick_planeWave (k p : Vec4) (u : DiracSpinor) :
    momentumKick k (planeWave p u) = planeWave (p + k) u := by
  funext x
  unfold momentumKick planeWave
  rw [smul_smul, ← exp_add, wavePhase_add_left, ofReal_add, mul_add, add_comm]

theorem weyl_shift_kick (k a p : Vec4) (u : DiracSpinor) (x : Vec4) :
    chartTranslate a (momentumKick k (planeWave p u)) x =
      exp (I * (wavePhase k a : ℂ)) •
        momentumKick k (chartTranslate a (planeWave p u)) x := by
  unfold chartTranslate momentumKick
  rw [smul_smul, ← exp_add]
  have hphase : I * (wavePhase k (x + a) : ℂ) =
      I * (wavePhase k a : ℂ) + I * (wavePhase k x : ℂ) := by
    rw [wavePhase_add_right, ofReal_add, mul_add, add_comm]
  rw [hphase]

theorem weyl_not_commute {k : Vec4} (hk : k ≠ 0) {u : DiracSpinor} (hu : u ≠ 0) (p : Vec4) :
    ∃ a x, chartTranslate a (momentumKick k (planeWave p u)) x ≠
      momentumKick k (chartTranslate a (planeWave p u)) x := by
  obtain ⟨a, ha⟩ := exists_wavePhase_pi hk
  refine ⟨a, 0, ?_⟩
  intro h
  have hrel := weyl_shift_kick k a p u 0
  rw [h, ha, exp_I_pi, neg_one_smul] at hrel
  have hv : momentumKick k (chartTranslate a (planeWave p u)) 0 = 0 := by
    have htwo : momentumKick k (chartTranslate a (planeWave p u)) 0 +
        momentumKick k (chartTranslate a (planeWave p u)) 0 = 0 := by
      nth_rw 1 [hrel]
      exact neg_add_cancel _
    rw [← two_smul ℂ] at htwo
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  unfold momentumKick chartTranslate at hv
  rw [wavePhase_zero, ofReal_zero, mul_zero, exp_zero, one_smul, zero_add] at hv
  exact planeWave_ne_zero hu p a hv

end Logic

end DstDiophantine
