import DoubleSpacetime.Logic.Quantum.LightFilter
import DoubleSpacetime.Logic.Quantum.MotorReading
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Null speed from a translator

Position is the coefficient vector `λ` of a null translator. A shell packet reads the Euclidean
sum `∑ δ_μ λ^μ`. The rotor preserves the Minkowski square `Q(λ)`. Those are different numbers.

The coordinate speed, in units where the Minkowski weights are `(-,+,+,+)`, is the ratio of the
spatial norm of `λ` to `|λ⁰|`. It equals `1` exactly when `λ⁰ ≠ 0` and `Q(λ) = 0`. No SI value
of `c` is derived.

Unsigned mass `M = ½∑(α²+β²)` sits on the torsion rotor. `M = 0` is the identity rotor and does
not constrain `λ`. A pure time translator on that rotor is at rest. The mass that sets the speed
is the Minkowski mass of the four-momentum the positional phase contracts against: on the Dirac
shell `Q(p) = -m²`, and for `p⁰ ≠ 0` the speed is `1` exactly when `m = 0`.

Manifestation writes a dual vector as a future null four-vector. For `u ≠ 0` that vector is a
translator at speed `1`. Its Euclidean self-reading is `2 ‖u‖⁴`, and the rotor's scalar on the
same vector is `0`. A pure `(t,x)` boost is the sandwich of `pureBoost` and keeps the speed at
`1`. A nonzero null vector is not at rest, and neither is its image under any injective
`Q`-preserving map that fixes the origin. A timelike momentum in the `(t,x)` plane does have a
rest frame.
-/

namespace DoubleSpacetime

namespace Logic

open Motor Amplification Invariant Operations Real

/-! ### Speed of a coefficient vector -/

/-- Squared Euclidean norm of the spatial coefficients. -/
def spatialNormSq (v : Vec4) : ℝ :=
  v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2

/-- Squared coordinate speed. This is the speed only when the time coefficient is nonzero:
division by zero is the Lean zero, not a particle at rest. -/
noncomputable def coordinateSpeedSq (v : Vec4) : ℝ :=
  spatialNormSq v / (v 0) ^ 2

/-- A displacement with a time coefficient and equal spatial norm. Speed `1`. -/
def AtLightSpeed (v : Vec4) : Prop :=
  v 0 ≠ 0 ∧ spatialNormSq v = (v 0) ^ 2

/-- A displacement with a time coefficient and no spatial part. -/
def IsAtRest (v : Vec4) : Prop :=
  v 0 ≠ 0 ∧ spatialNormSq v = 0

theorem minkowskiQ_eq_speed (v : Vec4) :
    minkowskiQ v = spatialNormSq v - (v 0) ^ 2 := by
  rw [minkowskiQ_eq, spatialNormSq]
  ring

theorem Q31_eq_minkowskiQ (v : Vec4) : Q31 v = minkowskiQ v := by
  rw [Q31_eq_minkowskiDot, minkowskiQ_eq, minkowskiDot]
  ring

theorem spatialNormSq_eq_zero_iff (v : Vec4) :
    spatialNormSq v = 0 ↔ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
  unfold spatialNormSq
  constructor
  · intro h
    have h1 : v 1 ^ 2 = 0 := by nlinarith [sq_nonneg (v 2), sq_nonneg (v 3)]
    have h2 : v 2 ^ 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 3)]
    have h3 : v 3 ^ 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
    exact ⟨sq_eq_zero_iff.mp h1, sq_eq_zero_iff.mp h2, sq_eq_zero_iff.mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    ring

theorem vec_eq_zero_of_time_spatial {v : Vec4} (h0 : v 0 = 0) (hs : spatialNormSq v = 0) :
    v = 0 := by
  funext μ
  fin_cases μ
  · exact h0
  · exact ((spatialNormSq_eq_zero_iff v).mp hs).1
  · exact ((spatialNormSq_eq_zero_iff v).mp hs).2.1
  · exact ((spatialNormSq_eq_zero_iff v).mp hs).2.2

theorem coordinateSpeedSq_eq_one_iff {v : Vec4} (h0 : v 0 ≠ 0) :
    coordinateSpeedSq v = 1 ↔ minkowskiQ v = 0 := by
  have hsq : (v 0) ^ 2 ≠ 0 := pow_ne_zero 2 h0
  constructor
  · intro h
    have hmul : spatialNormSq v = 1 * (v 0) ^ 2 := (div_eq_iff hsq).mp h
    have hsp : spatialNormSq v = (v 0) ^ 2 := by simpa using hmul
    have hq := minkowskiQ_eq_speed v
    linarith
  · intro h
    have hsp : spatialNormSq v = (v 0) ^ 2 := by
      have hq := minkowskiQ_eq_speed v
      linarith
    rw [coordinateSpeedSq, hsp, div_self hsq]

theorem coordinateSpeedSq_lt_one_iff {v : Vec4} (h0 : v 0 ≠ 0) :
    coordinateSpeedSq v < 1 ↔ minkowskiQ v < 0 := by
  have hpos : 0 < (v 0) ^ 2 := by
    have hsq : (v 0) ^ 2 ≠ 0 := pow_ne_zero 2 h0
    exact lt_of_le_of_ne (sq_nonneg _) hsq.symm
  unfold coordinateSpeedSq
  rw [div_lt_iff₀ hpos]
  have hq := minkowskiQ_eq_speed v
  constructor <;> intro h <;> linarith

theorem coordinateSpeedSq_le_one_iff {v : Vec4} (h0 : v 0 ≠ 0) :
    coordinateSpeedSq v ≤ 1 ↔ minkowskiQ v ≤ 0 := by
  have hpos : 0 < (v 0) ^ 2 := by
    have hsq : (v 0) ^ 2 ≠ 0 := pow_ne_zero 2 h0
    exact lt_of_le_of_ne (sq_nonneg _) hsq.symm
  unfold coordinateSpeedSq
  rw [div_le_iff₀ hpos]
  have hq := minkowskiQ_eq_speed v
  constructor <;> intro h <;> linarith

theorem atLightSpeed_iff {v : Vec4} :
    AtLightSpeed v ↔ v 0 ≠ 0 ∧ minkowskiQ v = 0 := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hq := minkowskiQ_eq_speed v
    linarith [h.2]
  · intro h
    refine ⟨h.1, ?_⟩
    have hq := minkowskiQ_eq_speed v
    linarith [h.2]

theorem coordinateSpeedSq_of_atLightSpeed {v : Vec4} (h : AtLightSpeed v) :
    coordinateSpeedSq v = 1 :=
  (coordinateSpeedSq_eq_one_iff h.1).mpr ((atLightSpeed_iff.mp h).2)

/-- On a null vector the packet's self-reading is twice the squared time coefficient, and the
rotor's scalar is zero. -/
theorem null_selfPhase {v : Vec4} (hQ : minkowskiQ v = 0) :
    minkowskiPhase v v = 0 ∧ wavePhase v v = 2 * (v 0) ^ 2 := by
  have hM : minkowskiPhase v v = minkowskiQ v := by
    rw [minkowskiPhase_eq, minkowskiQ_eq]
    ring
  have hW : wavePhase v v = (v 0) ^ 2 + spatialNormSq v := by
    rw [wavePhase_expand, spatialNormSq]
    ring
  have hS : spatialNormSq v = (v 0) ^ 2 := by
    have hq := minkowskiQ_eq_speed v
    linarith
  refine ⟨?_, ?_⟩
  · rw [hM, hQ]
  · rw [hW, hS]
    ring

theorem null_selfPhase_eq_zero_iff {v : Vec4} (hQ : minkowskiQ v = 0) :
    wavePhase v v = 0 ↔ v = 0 := by
  obtain ⟨_, hW⟩ := null_selfPhase hQ
  constructor
  · intro hw
    have h0sq : (v 0) ^ 2 = 0 := by nlinarith [hW, hw]
    have h0 : v 0 = 0 := sq_eq_zero_iff.mp h0sq
    have hs : spatialNormSq v = 0 := by
      have hq := minkowskiQ_eq_speed v
      rw [hQ, h0] at hq
      linarith
    exact vec_eq_zero_of_time_spatial h0 hs
  · intro hv
    rw [hv, wavePhase_zero]

theorem nonzero_null_time {v : Vec4} (hv : v ≠ 0) (hQ : minkowskiQ v = 0) : v 0 ≠ 0 := by
  intro h0
  have hs : spatialNormSq v = 0 := by
    have hq := minkowskiQ_eq_speed v
    rw [hQ, h0] at hq
    linarith
  exact hv (vec_eq_zero_of_time_spatial h0 hs)

theorem null_not_atRest {v : Vec4} (hQ : minkowskiQ v = 0) : ¬ IsAtRest v := by
  intro h
  have hsp : spatialNormSq v = (v 0) ^ 2 := by
    have hq := minkowskiQ_eq_speed v
    linarith
  have h0 : v 0 = 0 := sq_eq_zero_iff.mp (by nlinarith [h.2, hsp])
  exact h.1 h0

/-! ### The shell -/

theorem onShell_speed {m : ℝ} {p : Vec4} {Ψ : DiracSpinor}
    (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) (h0 : p 0 ≠ 0) :
    coordinateSpeedSq p ≤ 1 ∧
      (coordinateSpeedSq p = 1 ↔ m = 0) ∧
        (coordinateSpeedSq p < 1 ↔ m ≠ 0) := by
  have hQ := diracMomentum_implies_mass_shell hΨ h
  have hle : coordinateSpeedSq p ≤ 1 := by
    rw [coordinateSpeedSq_le_one_iff h0, hQ]
    nlinarith [sq_nonneg m]
  refine ⟨hle, ?_, ?_⟩
  · rw [coordinateSpeedSq_eq_one_iff h0, hQ]
    constructor
    · intro hq
      nlinarith
    · intro hm
      rw [hm]
      ring
  · rw [coordinateSpeedSq_lt_one_iff h0, hQ]
    constructor
    · intro hq hm
      rw [hm] at hq
      simp at hq
    · intro hm
      have hsq : 0 < m ^ 2 := sq_pos_of_ne_zero hm
      linarith

/-! ### A boost keeps a null ray at speed `1` -/

theorem boost01_zero (ch sh : ℝ) : boost01 ch sh 0 = 0 := by
  funext μ
  fin_cases μ <;> simp [boost01]

theorem boost01_leftInverse {ch sh : ℝ} (h : ch ^ 2 - sh ^ 2 = 1) (p : Vec4) :
    boost01 ch (-sh) (boost01 ch sh p) = p := by
  funext μ
  match μ with
  | 0 =>
    simp only [boost01]
    have hring :
        ch * (ch * p 0 + sh * p 1) + -sh * (sh * p 0 + ch * p 1) =
          (ch ^ 2 - sh ^ 2) * p 0 := by ring
    rw [hring, h, one_mul]
  | 1 =>
    simp only [boost01]
    have hring :
        -sh * (ch * p 0 + sh * p 1) + ch * (sh * p 0 + ch * p 1) =
          (ch ^ 2 - sh ^ 2) * p 1 := by ring
    rw [hring, h, one_mul]
  | 2 => simp [boost01]
  | 3 => simp [boost01]

theorem boost01_injective {ch sh : ℝ} (h : ch ^ 2 - sh ^ 2 = 1) :
    Function.Injective (boost01 ch sh) := by
  intro a b hab
  have hinv := congrArg (boost01 ch (-sh)) hab
  simpa [boost01_leftInverse h] using hinv

theorem boost01_preserves_lightSpeed {ch sh : ℝ} (h : ch ^ 2 - sh ^ 2 = 1) {v : Vec4}
    (hv : v ≠ 0) (hQ : minkowskiQ v = 0) : AtLightSpeed (boost01 ch sh v) := by
  have hQ' : minkowskiQ (boost01 ch sh v) = 0 := by
    rw [minkowskiQ_boost01 h, hQ]
  have hv' : boost01 ch sh v ≠ 0 := by
    intro hz
    have : v = 0 := by
      have hinv := congrArg (boost01 ch (-sh)) hz
      simpa [boost01_leftInverse h, boost01_zero] using hinv
    exact hv this
  exact atLightSpeed_iff.mpr ⟨nonzero_null_time hv' hQ', hQ'⟩

/-- An injective origin-fixing map that preserves `Q` cannot put a nonzero null vector at rest. -/
theorem null_image_not_atRest {f : Vec4 → Vec4} (hfix : f 0 = 0)
    (hQ : ∀ v, minkowskiQ (f v) = minkowskiQ v) (hf : Function.Injective f) {v : Vec4}
    (hv : v ≠ 0) (hn : minkowskiQ v = 0) : ¬ IsAtRest (f v) := by
  have hfv : f v ≠ 0 := by
    intro hz
    exact hv (hf (by simpa [hfix] using hz))
  exact null_not_atRest (by rw [hQ, hn])

theorem boost01_null_not_atRest {ch sh : ℝ} (h : ch ^ 2 - sh ^ 2 = 1) {v : Vec4}
    (hv : v ≠ 0) (hn : minkowskiQ v = 0) : ¬ IsAtRest (boost01 ch sh v) :=
  null_image_not_atRest (boost01_zero ch sh) (fun w => minkowskiQ_boost01 h w)
    (boost01_injective h) hv hn

/-! ### Rest frame in the boost plane -/

/-- Momentum in the `(t, x)` plane. -/
def txMomentum (E px : ℝ) : Vec4
  | 0 => E
  | 1 => px
  | 2 => 0
  | 3 => 0

theorem tx_timelike {E px : ℝ} (hE : 0 < E) (hp : |px| < E) :
    minkowskiQ (txMomentum E px) < 0 ∧ coordinateSpeedSq (txMomentum E px) < 1 := by
  have hsq : px ^ 2 < E ^ 2 := (sq_lt_sq).mpr (by simpa [abs_of_pos hE] using hp)
  have hQ : minkowskiQ (txMomentum E px) = -(E ^ 2 - px ^ 2) := by
    rw [minkowskiQ_eq]
    simp only [txMomentum]
    ring
  have h0 : txMomentum E px 0 ≠ 0 := by
    simpa [txMomentum] using ne_of_gt hE
  refine ⟨?_, ?_⟩
  · rw [hQ]
    linarith
  · rw [coordinateSpeedSq_lt_one_iff h0, hQ]
    linarith

theorem exists_tx_restFrame {E px : ℝ} (hE : 0 < E) (hp : |px| < E) :
    ∃ ch sh : ℝ, ch ^ 2 - sh ^ 2 = 1 ∧ IsAtRest (boost01 ch sh (txMomentum E px)) := by
  have hsq : px ^ 2 < E ^ 2 := (sq_lt_sq).mpr (by simpa [abs_of_pos hE] using hp)
  have hgap : 0 < E ^ 2 - px ^ 2 := by linarith
  set m : ℝ := Real.sqrt (E ^ 2 - px ^ 2)
  have hm0 : 0 < m := Real.sqrt_pos.mpr hgap
  have hmsq : m ^ 2 = E ^ 2 - px ^ 2 := Real.sq_sqrt (le_of_lt hgap)
  set ch : ℝ := E / m
  set sh : ℝ := -px / m
  refine ⟨ch, sh, ?_, ?_⟩
  · calc
      ch ^ 2 - sh ^ 2 = (E / m) ^ 2 - (-px / m) ^ 2 := by
        unfold ch sh
        rfl
      _ = (E ^ 2 - px ^ 2) / m ^ 2 := by
        field_simp [ne_of_gt hm0]
      _ = m ^ 2 / m ^ 2 := by rw [hmsq]
      _ = 1 := by field_simp [ne_of_gt hm0]
  · have h0 : boost01 ch sh (txMomentum E px) 0 = m := by
      simp only [boost01, txMomentum, ch, sh]
      have hmne : m ≠ 0 := ne_of_gt hm0
      calc
        E / m * E + -px / m * px = (E ^ 2 - px ^ 2) / m := by ring
        _ = m ^ 2 / m := by rw [hmsq]
        _ = m := by field_simp [hmne]
    have h1 : boost01 ch sh (txMomentum E px) 1 = 0 := by
      simp only [boost01, txMomentum, ch, sh]
      ring
    have h2 : boost01 ch sh (txMomentum E px) 2 = 0 := by
      simp [boost01, txMomentum]
    have h3 : boost01 ch sh (txMomentum E px) 3 = 0 := by
      simp [boost01, txMomentum]
    have hsp : spatialNormSq (boost01 ch sh (txMomentum E px)) = 0 := by
      rw [spatialNormSq, h1, h2, h3]
      ring
    exact ⟨by rw [h0]; exact ne_of_gt hm0, hsp⟩

/-! ### Manifested rays and the rotor's mass -/

/-- The same coefficients, read as a translator. -/
def rayTranslator (v : Vec4) : TransParams where
  lambda := v

/-- Standard null ray `e₀ + e₁`. -/
def nullRay : Vec4
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => 0

theorem nullRay_atLightSpeed : AtLightSpeed nullRay := by
  refine ⟨?_, ?_⟩
  · simp [nullRay]
  · simp [spatialNormSq, nullRay]

theorem nullRay_reading :
    Q31 nullRay = 0 ∧ coordinateSpeedSq nullRay = 1 ∧
      wavePhase nullRay nullRay = 2 ∧ minkowskiPhase nullRay nullRay = 0 := by
  have hQ : minkowskiQ nullRay = 0 := (atLightSpeed_iff.mp nullRay_atLightSpeed).2
  obtain ⟨hM, hW⟩ := null_selfPhase hQ
  have h0 : nullRay 0 = 1 := by simp [nullRay]
  refine ⟨?_, coordinateSpeedSq_of_atLightSpeed nullRay_atLightSpeed, ?_, hM⟩
  · rw [Q31_eq_minkowskiQ, hQ]
  · rw [hW, h0]
    ring

theorem manifest_atLightSpeed {u : DualSpinor} (hu : u ≠ 0) : AtLightSpeed (manifest u) := by
  have hQ : minkowskiQ (manifest u) = 0 := by
    rw [← Q31_eq_minkowskiQ, Q31_manifest]
  have h0 : manifest u 0 ≠ 0 := by
    intro hz
    exact hu ((informationWeight_eq_zero_iff u).mp (by simpa [manifest_zero] using hz))
  exact atLightSpeed_iff.mpr ⟨h0, hQ⟩

theorem manifest_position_reading {u : DualSpinor} (hu : u ≠ 0) :
    AtLightSpeed (manifest u) ∧
      minkowskiPhase (manifest u) (manifest u) = 0 ∧
        wavePhase (manifest u) (manifest u) = 2 * informationWeight u ^ 2 ∧
          wavePhase (manifest u) (manifest u) ≠ 0 := by
  have hA := manifest_atLightSpeed hu
  have hQ : minkowskiQ (manifest u) = 0 := (atLightSpeed_iff.mp hA).2
  obtain ⟨hM, hW⟩ := null_selfPhase hQ
  have htime : manifest u 0 = informationWeight u := manifest_zero u
  refine ⟨hA, hM, ?_, ?_⟩
  · rw [hW, htime]
  · have hne : informationWeight u ≠ 0 := by
      intro hz
      exact hu ((informationWeight_eq_zero_iff u).mp hz)
    have hpos : 0 < informationWeight u :=
      lt_of_le_of_ne (informationWeight_nonneg u) hne.symm
    have hW' : wavePhase (manifest u) (manifest u) = 2 * informationWeight u ^ 2 := by
      rw [hW, htime]
    rw [hW']
    positivity

theorem manifest_translator_boost {u : DualSpinor} (hu : u ≠ 0) (φ : ℝ) :
    AtLightSpeed
      (boostTranslator (Real.cosh φ) (Real.sinh φ) (rayTranslator (manifest u))).lambda := by
  have hhyp : Real.cosh φ ^ 2 - Real.sinh φ ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq φ
  have hv : manifest u ≠ 0 := by
    intro hz
    exact hu ((manifest_eq_zero_iff u).mp hz)
  have hQ : minkowskiQ (manifest u) = 0 := (atLightSpeed_iff.mp (manifest_atLightSpeed hu)).2
  simpa [boostTranslator, rayTranslator] using boost01_preserves_lightSpeed hhyp hv hQ

private theorem weylUpper_ne_of_ne {u : DualSpinor} (hu : u ≠ 0) : weylUpper u ≠ 0 := by
  intro h
  exact hu (weylUpper_injective (h.trans weylUpper_zero.symm))

/-- The Dirac shell of a manifested ray and the PGA square of the same translator both vanish,
and the coordinate speed is `1`. -/
theorem manifest_shell_and_translator {u : DualSpinor} (hu : u ≠ 0) :
    DiracMomentum 0 (manifest u) (weylUpper u) ∧
      weylUpper u ≠ 0 ∧
        minkowskiQ (manifest u) = 0 ∧
          Q31 (rayTranslator (manifest u)).lambda = 0 ∧
            coordinateSpeedSq (manifest u) = 1 := by
  have hΨ := weylUpper_ne_of_ne hu
  have hdir := dirac_upper_manifest u
  have h0 : manifest u 0 ≠ 0 := (manifest_atLightSpeed hu).1
  have hshell : minkowskiQ (manifest u) = 0 := by
    have hQ := diracMomentum_implies_mass_shell hΨ hdir
    simpa using hQ
  refine ⟨hdir, hΨ, hshell, ?_, ?_⟩
  · rw [rayTranslator, Q31_eq_minkowskiQ, hshell]
  · exact (onShell_speed hΨ hdir h0).2.1.mpr rfl

theorem rest_below_light {m : ℝ} (hm : m ≠ 0) :
    coordinateSpeedSq (restMomentum m) = 0 ∧
      coordinateSpeedSq (restMomentum m) < 1 ∧
        minkowskiPhase (restMomentum m) (restMomentum m) = -m ^ 2 ∧
          wavePhase (restMomentum m) (restMomentum m) = m ^ 2 := by
  have h0 : restMomentum m 0 = m := by simp [restMomentum]
  have h1 : restMomentum m 1 = 0 := by simp [restMomentum]
  have h2 : restMomentum m 2 = 0 := by simp [restMomentum]
  have h3 : restMomentum m 3 = 0 := by simp [restMomentum]
  have hsp : spatialNormSq (restMomentum m) = 0 := by
    rw [spatialNormSq, h1, h2, h3]
    ring
  have hspeed : coordinateSpeedSq (restMomentum m) = 0 := by
    rw [coordinateSpeedSq, hsp, h0, zero_div]
  have hdir := restParticle_dirac m (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
  have hΨ : restParticleSpinor (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) ≠ 0 :=
    restParticleSpinor_ne_zero
  have hlt := (onShell_speed hΨ hdir (by rw [h0]; exact hm)).2.2.mpr hm
  refine ⟨hspeed, hlt, ?_, ?_⟩
  · rw [minkowskiPhase_eq, h0, h1, h2, h3]
    ring
  · rw [wavePhase_expand, h0, h1, h2, h3]
    ring

/-- `M` is the rotor. It does not set the translator's speed. `M = 0` leaves a pure time
translator at rest, while `nullRay` stays at speed `1` at every rapidity. -/
theorem unsignedMass_not_lightSpeed (φ : ℝ) :
    mass (pureBoost φ) = (1 / 2) * φ ^ 2 ∧
      (mass (pureBoost φ) = 0 ↔ φ = 0) ∧
        coordinateSpeedSq (Pi.single (0 : Fin 4) (1 : ℝ)) = 0 ∧
          AtLightSpeed nullRay := by
  refine ⟨mass_pureBoost φ, ?_, ?_, nullRay_atLightSpeed⟩
  · rw [mass_pureBoost]
    constructor
    · intro h
      nlinarith
    · intro h
      rw [h]
      ring
  · rw [coordinateSpeedSq, spatialNormSq]
    simp [Pi.single]

theorem massless_ray_from_position {u : DualSpinor} (hu : u ≠ 0) (φ : ℝ) :
    AtLightSpeed (manifest u) ∧
      wavePhase (manifest u) (manifest u) = 2 * informationWeight u ^ 2 ∧
        minkowskiPhase (manifest u) (manifest u) = 0 ∧
          wavePhase (manifest u) (manifest u) ≠ 0 ∧
            AtLightSpeed
              (boostTranslator (Real.cosh φ) (Real.sinh φ)
                (rayTranslator (manifest u))).lambda := by
  obtain ⟨hA, hM, hW, hne⟩ := manifest_position_reading hu
  exact ⟨hA, hW, hM, hne, manifest_translator_boost hu φ⟩

end Logic

end DoubleSpacetime
