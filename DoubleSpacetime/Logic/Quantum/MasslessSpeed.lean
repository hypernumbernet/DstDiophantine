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
spatial norm of a coefficient vector to its time coefficient. It equals `1` exactly when the
time coefficient is nonzero and `Q` vanishes. No SI value of `c` is derived. Unsigned mass
`M = ½∑(α²+β²)` sits on the torsion rotor. `M = 0` is the identity rotor and does not constrain
`λ`. A pure time translator on that rotor is at rest.

The mass that sets a carrier's speed is the Minkowski mass of a four-momentum on the Dirac
shell `Q(p) = -m²`. For `p⁰ ≠ 0` that speed is `1` exactly when `m = 0`. The shell packet does
not read this ratio. It reads the Euclidean phase of the relative momentum `δ = q − p`. The
phase front of that reading has squared speed `(δ⁰)² / ‖δ_spatial‖²`, and only when the spatial
part is nonzero.

Two future momenta on one shell have `η(p, q) ≤ -m²`. The relative momentum is therefore never
timelike. For `m ≠ 0` it is spacelike whenever `p ≠ q`, so the positional fringe stays below
light speed. For `m = 0` each carrier has coordinate speed `1`, and the fringe has speed `1`
exactly when the two momenta are distinct positive multiples of one null vector. Opposite null
rays give a fringe fixed by time translation: that fringe reads the unit `N_1` translator and
does not read the null line `e₀ − e₃`. The collinear fringe does read the null line, through
its time coefficient.

Manifestation writes a dual vector as a future null four-vector. For `u ≠ 0` that vector is one
massless carrier at speed `1`, not a positional fringe. Its Euclidean self-reading is `2 ‖u‖⁴`,
and the rotor's scalar on the same vector is `0`. A pure `(t,x)` boost keeps that carrier at
speed `1`. A nonzero null vector is not at rest. A timelike momentum in the `(t,x)` plane does
have a rest frame.
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
    minkowskiPolar v v = 0 ∧ wavePhase v v = 2 * (v 0) ^ 2 := by
  have hM : minkowskiPolar v v = minkowskiQ v := minkowskiPolar_self v
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
      wavePhase nullRay nullRay = 2 ∧ minkowskiPolar nullRay nullRay = 0 := by
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
      minkowskiPolar (manifest u) (manifest u) = 0 ∧
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
        minkowskiPolar (restMomentum m) (restMomentum m) = -m ^ 2 ∧
          wavePhase (restMomentum m) (restMomentum m) = m ^ 2 := by
  have h0 : restMomentum m 0 = m := by simp [restMomentum]
  have hsp : spatialNormSq (restMomentum m) = 0 := by
    simp [spatialNormSq, restMomentum]
  have hspeed : coordinateSpeedSq (restMomentum m) = 0 := by
    rw [coordinateSpeedSq, hsp, h0, zero_div]
  have hdir := restParticle_dirac m (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
  have hΨ : restParticleSpinor (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) ≠ 0 :=
    restParticleSpinor_ne_zero
  have hlt := (onShell_speed hΨ hdir (by rw [h0]; exact hm)).2.2.mpr hm
  refine ⟨hspeed, hlt, ?_, ?_⟩
  · rw [minkowskiPolar_self, minkowskiQ_rest]
  · rw [wavePhase_expand]
    simp [restMomentum]
    ring

/-- `M` is the rotor. It does not set the translator's speed. `M = 0` leaves a pure time
translator at rest, while `nullRay` stays at speed `1` at every rapidity. -/
theorem unsignedMass_not_lightSpeed (φ : ℝ) :
    mass (pureBoost φ) = (1 / 2) * φ ^ 2 ∧
      (mass (pureBoost φ) = 0 ↔ φ = 0) ∧
        coordinateSpeedSq timeTranslator.lambda = 0 ∧
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
    simp [timeTranslator]

theorem massless_ray_from_position {u : DualSpinor} (hu : u ≠ 0) (φ : ℝ) :
    AtLightSpeed (manifest u) ∧
      wavePhase (manifest u) (manifest u) = 2 * informationWeight u ^ 2 ∧
        minkowskiPolar (manifest u) (manifest u) = 0 ∧
          wavePhase (manifest u) (manifest u) ≠ 0 ∧
            AtLightSpeed
              (boostTranslator (Real.cosh φ) (Real.sinh φ)
                (rayTranslator (manifest u))).lambda := by
  obtain ⟨hA, hM, hW, hne⟩ := manifest_position_reading hu
  exact ⟨hA, hW, hM, hne, manifest_translator_boost hu φ⟩

/-! ### The fringe the shell packet reads -/

/-- Squared speed of a surface of constant `wavePhase v`. This is that speed only when the
spatial part is nonzero. Division by zero is the Lean zero. -/
noncomputable def phaseFrontSpeedSq (v : Vec4) : ℝ :=
  (v 0) ^ 2 / spatialNormSq v

/-- Spatial contraction. The packet's phase uses this together with the time slot, without `η`. -/
def spatialDot (p q : Vec4) : ℝ :=
  p 1 * q 1 + p 2 * q 2 + p 3 * q 3

/-- Future momenta on one ray. Not the carrier relation `SameRay`. -/
def FutureRay (p q : Vec4) : Prop :=
  ∃ t : ℝ, 0 < t ∧ q = t • p

theorem spatialNormSq_nonneg (v : Vec4) : 0 ≤ spatialNormSq v := by
  unfold spatialNormSq
  nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]

theorem spatial_of_shell {m : ℝ} {p : Vec4} (hQ : minkowskiQ p = -m ^ 2) :
    spatialNormSq p = (p 0) ^ 2 - m ^ 2 := by
  have hq := minkowskiQ_eq_speed p
  linarith

theorem minkowskiPolar_expand (p q : Vec4) :
    minkowskiPolar p q = -(p 0) * q 0 + spatialDot p q := by
  rw [minkowskiPolar_eq, spatialDot]
  ring

theorem minkowskiPolar_smul_right (p : Vec4) (t : ℝ) (q : Vec4) :
    minkowskiPolar p (t • q) = t * minkowskiPolar p q := by
  unfold minkowskiPolar
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

theorem minkowskiQ_smul (t : ℝ) (p : Vec4) : minkowskiQ (t • p) = t ^ 2 * minkowskiQ p := by
  rw [minkowskiQ_eq, minkowskiQ_eq]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem minkowskiQ_sub (p q : Vec4) :
    minkowskiQ (q - p) = minkowskiQ p + minkowskiQ q - 2 * minkowskiPolar p q := by
  rw [minkowskiQ_eq, minkowskiQ_eq, minkowskiQ_eq, minkowskiPolar_expand]
  simp only [Pi.sub_apply, spatialDot]
  ring

theorem spatialDot_comm (p q : Vec4) : spatialDot p q = spatialDot q p := by
  unfold spatialDot
  ring

theorem spatialDot_smul_right (p q : Vec4) (t : ℝ) :
    spatialDot p (t • q) = t * spatialDot p q := by
  unfold spatialDot
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem spatialNormSq_smul (t : ℝ) (p : Vec4) :
    spatialNormSq (t • p) = t ^ 2 * spatialNormSq p := by
  unfold spatialNormSq
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem spatialNormSq_sub (p q : Vec4) :
    spatialNormSq (q - p) =
      spatialNormSq p + spatialNormSq q - 2 * spatialDot p q := by
  unfold spatialNormSq spatialDot
  simp only [Pi.sub_apply]
  ring

theorem spatial_dot_sq_le (p q : Vec4) :
    spatialDot p q ^ 2 ≤ spatialNormSq p * spatialNormSq q := by
  have h :
      spatialNormSq p * spatialNormSq q - spatialDot p q ^ 2 =
        (p 1 * q 2 - p 2 * q 1) ^ 2 + (p 1 * q 3 - p 3 * q 1) ^ 2 +
          (p 2 * q 3 - p 3 * q 2) ^ 2 := by
    unfold spatialNormSq spatialDot
    ring
  nlinarith [sq_nonneg (p 1 * q 2 - p 2 * q 1), sq_nonneg (p 1 * q 3 - p 3 * q 1),
    sq_nonneg (p 2 * q 3 - p 3 * q 2)]

theorem future_shell_time {m : ℝ} {p : Vec4} (hQ : minkowskiQ p = -m ^ 2) (h0 : 0 < p 0) :
    |m| ≤ p 0 := by
  have hs := spatial_of_shell hQ
  have hsq : m ^ 2 ≤ (p 0) ^ 2 := by linarith [spatialNormSq_nonneg p, hs]
  exact abs_le_of_sq_le_sq hsq h0.le

theorem phaseFrontSpeedSq_eq_one_iff {v : Vec4} (hs : spatialNormSq v ≠ 0) :
    phaseFrontSpeedSq v = 1 ↔ minkowskiQ v = 0 := by
  constructor
  · intro h
    have hmul : (v 0) ^ 2 = 1 * spatialNormSq v :=
      (div_eq_iff hs).mp (by simpa [phaseFrontSpeedSq] using h)
    have htime : (v 0) ^ 2 = spatialNormSq v := by simpa using hmul
    have hq := minkowskiQ_eq_speed v
    linarith
  · intro h
    have htime : (v 0) ^ 2 = spatialNormSq v := by
      have hq := minkowskiQ_eq_speed v
      linarith
    rw [phaseFrontSpeedSq, htime, div_self hs]

theorem phaseFrontSpeedSq_lt_one_iff {v : Vec4} (hs : spatialNormSq v ≠ 0) :
    phaseFrontSpeedSq v < 1 ↔ 0 < minkowskiQ v := by
  have hpos : 0 < spatialNormSq v :=
    lt_of_le_of_ne (spatialNormSq_nonneg v) (Ne.symm hs)
  unfold phaseFrontSpeedSq
  rw [div_lt_iff₀ hpos]
  have hq := minkowskiQ_eq_speed v
  constructor <;> intro h <;> linarith

theorem spatial_ne_of_spacelike {v : Vec4} (hQ : 0 < minkowskiQ v) : spatialNormSq v ≠ 0 := by
  intro hs
  have hq := minkowskiQ_eq_speed v
  rw [hs] at hq
  nlinarith [sq_nonneg (v 0)]

/-- On one future shell the spatial contraction cannot exceed the time product corrected by `m²`. -/
theorem futureShell_spatial_bound {m : ℝ} {p q : Vec4}
    (hp : minkowskiQ p = -m ^ 2) (hq : minkowskiQ q = -m ^ 2)
    (hp0 : 0 < p 0) (hq0 : 0 < q 0) :
    |spatialDot p q| ≤ p 0 * q 0 - m ^ 2 ∧
      spatialNormSq p = (p 0) ^ 2 - m ^ 2 ∧
        spatialNormSq q = (q 0) ^ 2 - m ^ 2 ∧
          (p 0 * q 0 - m ^ 2) ^ 2 - spatialNormSq p * spatialNormSq q =
            m ^ 2 * (p 0 - q 0) ^ 2 := by
  have hEp : |m| ≤ p 0 := future_shell_time hp hp0
  have hEq : |m| ≤ q 0 := future_shell_time hq hq0
  have hEFm : m ^ 2 ≤ p 0 * q 0 := by
    have hmul : |m| * |m| ≤ p 0 * q 0 :=
      mul_le_mul hEp hEq (abs_nonneg m) hp0.le
    rw [← sq, sq_abs] at hmul
    exact hmul
  have hgap0 : 0 ≤ p 0 * q 0 - m ^ 2 := by linarith
  have hsp := spatial_of_shell hp
  have hsq := spatial_of_shell hq
  have hdiff :
      (p 0 * q 0 - m ^ 2) ^ 2 - spatialNormSq p * spatialNormSq q =
        m ^ 2 * (p 0 - q 0) ^ 2 := by
    rw [hsp, hsq]
    ring
  have hprod : spatialNormSq p * spatialNormSq q ≤ (p 0 * q 0 - m ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg m, hdiff]
  have hdot_sq : spatialDot p q ^ 2 ≤ (p 0 * q 0 - m ^ 2) ^ 2 := by
    calc
      spatialDot p q ^ 2 ≤ spatialNormSq p * spatialNormSq q := spatial_dot_sq_le p q
      _ ≤ (p 0 * q 0 - m ^ 2) ^ 2 := hprod
  exact ⟨abs_le_of_sq_le_sq hdot_sq hgap0, hsp, hsq, hdiff⟩

/-- On one future shell, `η(p, q) ≤ -m²`. Equality holds for `m ≠ 0` exactly when `p = q`, and
for `m = 0` exactly when `p` and `q` are positive multiples of one vector. -/
theorem futureShell_polar_eq_iff {m : ℝ} {p q : Vec4}
    (hp : minkowskiQ p = -m ^ 2) (hq : minkowskiQ q = -m ^ 2)
    (hp0 : 0 < p 0) (hq0 : 0 < q 0) :
    minkowskiPolar p q = -m ^ 2 ↔ (m ≠ 0 ∧ p = q) ∨ (m = 0 ∧ FutureRay p q) := by
  obtain ⟨habs, hsp, hsq, hdiff⟩ := futureShell_spatial_bound hp hq hp0 hq0
  have hpolar : minkowskiPolar p q = -(p 0) * q 0 + spatialDot p q :=
    minkowskiPolar_expand p q
  constructor
  · intro hEqP
    have hdot : spatialDot p q = p 0 * q 0 - m ^ 2 := by linarith
    have hprod : spatialNormSq p * spatialNormSq q ≤ (p 0 * q 0 - m ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg m, hdiff]
    have hsqueeze : spatialNormSq p * spatialNormSq q = spatialDot p q ^ 2 :=
      le_antisymm (by nlinarith [hprod, hdot]) (spatial_dot_sq_le p q)
    have hEF : m ^ 2 * (p 0 - q 0) ^ 2 = 0 := by
      have : (p 0 * q 0 - m ^ 2) ^ 2 - spatialNormSq p * spatialNormSq q = 0 := by
        nlinarith [hsqueeze, hdot]
      linarith [hdiff]
    by_cases hm : m = 0
    · refine Or.inr ⟨hm, ?_⟩
      set t : ℝ := q 0 / p 0
      have ht : 0 < t := div_pos hq0 hp0
      have hE0 : p 0 ≠ 0 := ne_of_gt hp0
      have hdot0 : spatialDot p q = p 0 * q 0 := by simpa [hm] using hdot
      have hsp0 : spatialNormSq p = (p 0) ^ 2 := by simpa [hm] using hsp
      have hsq0 : spatialNormSq q = (q 0) ^ 2 := by simpa [hm] using hsq
      have htE : t * p 0 = q 0 := by
        unfold t
        field_simp [hE0]
      have hspace : spatialNormSq (q - t • p) = 0 := by
        rw [spatialNormSq_sub (t • p) q, spatialNormSq_smul, hsq0, hsp0]
        have hdotq : spatialDot (t • p) q = t * spatialDot p q := by
          rw [spatialDot_comm, spatialDot_smul_right, spatialDot_comm]
        rw [hdotq, hdot0]
        have hsqT : t ^ 2 * (p 0) ^ 2 = (q 0) ^ 2 := by
          calc
            t ^ 2 * (p 0) ^ 2 = (t * p 0) ^ 2 := by ring
            _ = (q 0) ^ 2 := by rw [htE]
        have hcross : t * (p 0 * q 0) = (q 0) ^ 2 := by
          calc
            t * (p 0 * q 0) = (t * p 0) * q 0 := by ring
            _ = q 0 * q 0 := by rw [htE]
            _ = (q 0) ^ 2 := by ring
        rw [hsqT, hcross]
        ring
      have htime : (q - t • p) 0 = 0 := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [htE]
        ring
      have hzero : q - t • p = 0 := vec_eq_zero_of_time_spatial htime hspace
      exact ⟨t, ht, sub_eq_zero.mp hzero⟩
    · refine Or.inl ⟨hm, ?_⟩
      have hEF0 : p 0 = q 0 := by
        have : (p 0 - q 0) ^ 2 = 0 := by
          apply (mul_eq_zero.mp hEF).resolve_left
          exact pow_ne_zero 2 hm
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)
      have hdot' : spatialDot p q = spatialNormSq p := by
        rw [hdot, hsp, hEF0]
        ring
      have hsq' : spatialNormSq q = spatialNormSq p := by rw [hsq, hsp, hEF0]
      have hspace : spatialNormSq (q - p) = 0 := by
        rw [spatialNormSq_sub p q, hsq', hdot']
        ring
      have htime : (q - p) 0 = 0 := by
        simp only [Pi.sub_apply, hEF0]
        ring
      exact (sub_eq_zero.mp (vec_eq_zero_of_time_spatial htime hspace)).symm
  · intro h
    rcases h with ⟨hm, rfl⟩ | ⟨hm, ⟨t, ht, rfl⟩⟩
    · rw [minkowskiPolar_self, hp]
    · rw [minkowskiPolar_smul_right, minkowskiPolar_self, hp, hm]
      ring

theorem futureShell_polar_le {m : ℝ} {p q : Vec4}
    (hp : minkowskiQ p = -m ^ 2) (hq : minkowskiQ q = -m ^ 2)
    (hp0 : 0 < p 0) (hq0 : 0 < q 0) :
    minkowskiPolar p q ≤ -m ^ 2 := by
  obtain ⟨habs, _, _, _⟩ := futureShell_spatial_bound hp hq hp0 hq0
  have hdot : spatialDot p q ≤ p 0 * q 0 - m ^ 2 := (abs_le.mp habs).2
  rw [minkowskiPolar_expand]
  linarith

theorem futureShell_relative_Q {m : ℝ} {p q : Vec4}
    (hp : minkowskiQ p = -m ^ 2) (hq : minkowskiQ q = -m ^ 2)
    (hp0 : 0 < p 0) (hq0 : 0 < q 0) :
    minkowskiQ (q - p) = -2 * (m ^ 2 + minkowskiPolar p q) ∧ 0 ≤ minkowskiQ (q - p) := by
  have hle := futureShell_polar_le hp hq hp0 hq0
  have hQ : minkowskiQ (q - p) = minkowskiQ p + minkowskiQ q - 2 * minkowskiPolar p q :=
    minkowskiQ_sub p q
  refine ⟨?_, ?_⟩
  · rw [hQ, hp, hq]
    ring
  · rw [hQ, hp, hq]
    linarith

theorem massive_fringe_below_light {m : ℝ} {p q : Vec4} (hm : m ≠ 0)
    (hp : minkowskiQ p = -m ^ 2) (hq : minkowskiQ q = -m ^ 2)
    (hp0 : 0 < p 0) (hq0 : 0 < q 0) (hpq : p ≠ q) :
    0 < minkowskiQ (q - p) ∧ phaseFrontSpeedSq (q - p) < 1 := by
  have hrel := futureShell_relative_Q hp hq hp0 hq0
  have hlt : minkowskiPolar p q < -m ^ 2 := by
    refine lt_of_le_of_ne (futureShell_polar_le hp hq hp0 hq0) ?_
    intro hEq
    have hdis := (futureShell_polar_eq_iff hp hq hp0 hq0).mp hEq
    rcases hdis with ⟨_, rfl⟩ | ⟨hm0, _⟩
    · exact hpq rfl
    · exact hm hm0
  have hQ : 0 < minkowskiQ (q - p) := by
    rw [hrel.1]
    linarith
  exact ⟨hQ, (phaseFrontSpeedSq_lt_one_iff (spatial_ne_of_spacelike hQ)).mpr hQ⟩

theorem massless_fringe_light_iff {p q : Vec4}
    (hp : minkowskiQ p = 0) (hq : minkowskiQ q = 0) (hp0 : 0 < p 0) (hq0 : 0 < q 0) :
    phaseFrontSpeedSq (q - p) = 1 ↔ p ≠ q ∧ FutureRay p q := by
  have hp' : minkowskiQ p = -(0 : ℝ) ^ 2 := by simpa using hp
  have hq' : minkowskiQ q = -(0 : ℝ) ^ 2 := by simpa using hq
  have hrel := futureShell_relative_Q hp' hq' hp0 hq0
  constructor
  · intro hspeed
    have hs : spatialNormSq (q - p) ≠ 0 := by
      intro hz
      have : phaseFrontSpeedSq (q - p) = 0 := by simp [phaseFrontSpeedSq, hz]
      linarith
    have hQ : minkowskiQ (q - p) = 0 := (phaseFrontSpeedSq_eq_one_iff hs).mp hspeed
    have hpolar : minkowskiPolar p q = 0 := by
      have hqδ := hrel.1
      rw [hQ] at hqδ
      linarith
    have hdis := (futureShell_polar_eq_iff hp' hq' hp0 hq0).mp (by simpa using hpolar)
    rcases hdis with ⟨hm, _⟩ | ⟨_, hray⟩
    · exact (hm rfl).elim
    · refine ⟨?_, hray⟩
      intro hpq
      apply hs
      rw [hpq, sub_self]
      simp [spatialNormSq]
  · rintro ⟨hpq, hray⟩
    have hpolar0 : minkowskiPolar p q = -(0 : ℝ) ^ 2 :=
      (futureShell_polar_eq_iff hp' hq' hp0 hq0).mpr (Or.inr ⟨rfl, hray⟩)
    have hpolar : minkowskiPolar p q = 0 := by simpa using hpolar0
    have hQ : minkowskiQ (q - p) = 0 := by
      rw [hrel.1, hpolar]
      ring
    have hs : spatialNormSq (q - p) ≠ 0 := by
      intro hz
      have htime : (q - p) 0 = 0 := by
        have hqδ := minkowskiQ_eq_speed (q - p)
        rw [hQ, hz] at hqδ
        nlinarith
      exact hpq (sub_eq_zero.mp (vec_eq_zero_of_time_spatial htime hz)).symm
    exact (phaseFrontSpeedSq_eq_one_iff hs).mpr hQ

/-- A future null coefficient is a massless Dirac carrier. -/
theorem dirac_of_future_null {p : Vec4} (hQ : minkowskiQ p = 0) (h0 : 0 ≤ p 0) :
    DiracMomentum 0 p (weylUpper (spinorOfNull p)) := by
  have hm : manifest (spinorOfNull p) = p :=
    manifest_spinorOfNull (by rw [Q31_eq_minkowskiQ, hQ]) h0
  simpa [hm] using dirac_upper_manifest (spinorOfNull p)

theorem weyl_of_future_null_ne {p : Vec4} (hQ : minkowskiQ p = 0) (h0 : 0 < p 0) :
    weylUpper (spinorOfNull p) ≠ 0 := by
  intro h
  have hu : spinorOfNull p = 0 :=
    weylUpper_injective (h.trans weylUpper_zero.symm)
  have hm : manifest (spinorOfNull p) = p :=
    manifest_spinorOfNull (by rw [Q31_eq_minkowskiQ, hQ]) h0.le
  have hzero : p = 0 := by rw [← hm, hu, (manifest_eq_zero_iff (0 : DualSpinor)).mpr rfl]
  exact ne_of_gt h0 (congrFun hzero 0)

/-- Two future Dirac carriers on one shell. The carrier speed is `1` exactly at `m = 0`.
The positional fringe, which is the phase of `q − p`, stays below light speed for every
distinct massive pair, and it reaches light speed for a massless pair exactly on one ray. -/
theorem diracShell_fringe {m : ℝ} {p q : Vec4} {Ψ Φ : DiracSpinor}
    (hΨ : Ψ ≠ 0) (hΦ : Φ ≠ 0) (hp : DiracMomentum m p Ψ) (hq : DiracMomentum m q Φ)
    (hp0 : 0 < p 0) (hq0 : 0 < q 0) :
    (coordinateSpeedSq p = 1 ↔ m = 0) ∧ (coordinateSpeedSq q = 1 ↔ m = 0) ∧
      (m ≠ 0 → p ≠ q → 0 < minkowskiQ (q - p) ∧ phaseFrontSpeedSq (q - p) < 1) ∧
        (m = 0 → (phaseFrontSpeedSq (q - p) = 1 ↔ p ≠ q ∧ FutureRay p q)) := by
  have hQp := diracMomentum_implies_mass_shell hΨ hp
  have hQq := diracMomentum_implies_mass_shell hΦ hq
  have hpne : p 0 ≠ 0 := ne_of_gt hp0
  have hqne : q 0 ≠ 0 := ne_of_gt hq0
  refine ⟨(onShell_speed hΨ hp hpne).2.1, (onShell_speed hΦ hq hqne).2.1, ?_, ?_⟩
  · intro hm hpq
    exact massive_fringe_below_light hm hQp hQq hp0 hq0 hpq
  · intro hm
    have hp' : minkowskiQ p = 0 := by simpa [hm] using hQp
    have hq' : minkowskiQ q = 0 := by simpa [hm] using hQq
    exact massless_fringe_light_iff hp' hq' hp0 hq0

/-! ### Two null rays, and one massive pair -/

/-- The opposite null ray `e₀ − e₁`. -/
def oppositeRay : Vec4
  | 0 => 1
  | 1 => -1
  | 2 => 0
  | 3 => 0

theorem oppositeRay_atLightSpeed : AtLightSpeed oppositeRay := by
  refine ⟨?_, ?_⟩
  · simp [oppositeRay]
  · simp [spatialNormSq, oppositeRay]

theorem wavePhase_nullLine (δ : Vec4) :
    wavePhase δ nullLineTranslator.lambda = δ 0 - δ 3 := by
  have hsplit : nullLineTranslator.lambda =
      Pi.single (0 : Fin 4) 1 + -Pi.single 3 1 := by
    funext μ
    fin_cases μ <;> simp [nullLineTranslator, Pi.add_apply, Pi.neg_apply]
  rw [hsplit, wavePhase_add_right, wavePhase_neg_right, wavePhase_neg_left,
    wavePhase_single, wavePhase_single]
  ring

theorem opposite_relative :
    (oppositeRay - nullRay) 0 = 0 ∧ (oppositeRay - nullRay) 1 = -2 ∧
      (oppositeRay - nullRay) 2 = 0 ∧ (oppositeRay - nullRay) 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [oppositeRay, nullRay, Pi.sub_apply]
  · simp [oppositeRay, nullRay, Pi.sub_apply]; norm_num
  · simp [oppositeRay, nullRay, Pi.sub_apply]
  · simp [oppositeRay, nullRay, Pi.sub_apply]

/-- Opposite future null carriers are each at speed `1`. Their positional fringe does not move
under a time shift, reads the unit `N_1` translator, and does not read `e₀ − e₃`. -/
theorem opposite_rays_stand (t : ℝ) (x : Vec4) :
    DiracMomentum 0 nullRay (weylUpper (spinorOfNull nullRay)) ∧
      DiracMomentum 0 oppositeRay (weylUpper (spinorOfNull oppositeRay)) ∧
        coordinateSpeedSq nullRay = 1 ∧ coordinateSpeedSq oppositeRay = 1 ∧
          phaseFrontSpeedSq (oppositeRay - nullRay) = 0 ∧
            wavePhase (oppositeRay - nullRay) (x + timeShift t) =
              wavePhase (oppositeRay - nullRay) x ∧
              wavePhase (oppositeRay - nullRay) readTranslator.lambda = -2 ∧
                wavePhase (oppositeRay - nullRay) nullLineTranslator.lambda = 0 := by
  have hQn : minkowskiQ nullRay = 0 := (atLightSpeed_iff.mp nullRay_atLightSpeed).2
  have hQo : minkowskiQ oppositeRay = 0 := (atLightSpeed_iff.mp oppositeRay_atLightSpeed).2
  have hrel := opposite_relative
  have hsp : spatialNormSq (oppositeRay - nullRay) = 4 := by
    rw [spatialNormSq, hrel.2.1, hrel.2.2.1, hrel.2.2.2]
    norm_num
  refine ⟨dirac_of_future_null hQn (by simp [nullRay]),
      dirac_of_future_null hQo (by simp [oppositeRay]),
      coordinateSpeedSq_of_atLightSpeed nullRay_atLightSpeed,
      coordinateSpeedSq_of_atLightSpeed oppositeRay_atLightSpeed, ?_, ?_, ?_, ?_⟩
  · rw [phaseFrontSpeedSq, hrel.1, hsp]
    norm_num
  · exact wavePhase_timeShift hrel.1 t x
  · rw [show readTranslator.lambda = Pi.single (1 : Fin 4) 1 from rfl, wavePhase_single,
      hrel.2.1]
  · rw [wavePhase_nullLine, hrel.1, hrel.2.2.2]
    ring

theorem collinear_relative : (2 : ℝ) • nullRay - nullRay = nullRay := by
  calc
    (2 : ℝ) • nullRay - nullRay
        = (2 : ℝ) • nullRay + (-1 : ℝ) • nullRay := by
          rw [sub_eq_add_neg, neg_one_smul]
      _ = (2 + -1 : ℝ) • nullRay := (add_smul _ _ _).symm
      _ = nullRay := by
          rw [show (2 + -1 : ℝ) = 1 by norm_num, one_smul]

/-- The beat of `nullRay` against twice itself is a lightlike fringe, and that fringe reads the
null line through the time coefficient. -/
theorem collinear_rays_front :
    FutureRay nullRay ((2 : ℝ) • nullRay) ∧
      phaseFrontSpeedSq ((2 : ℝ) • nullRay - nullRay) = 1 ∧
        wavePhase ((2 : ℝ) • nullRay - nullRay) nullLineTranslator.lambda = 1 ∧
          DiracMomentum 0 nullRay (weylUpper (spinorOfNull nullRay)) ∧
            DiracMomentum 0 ((2 : ℝ) • nullRay)
              (weylUpper (spinorOfNull ((2 : ℝ) • nullRay))) := by
  have hQ : minkowskiQ nullRay = 0 := (atLightSpeed_iff.mp nullRay_atLightSpeed).2
  have hQ2 : minkowskiQ ((2 : ℝ) • nullRay) = 0 := by
    rw [minkowskiQ_smul, hQ]
    ring
  have h0 : 0 ≤ nullRay 0 := by simp [nullRay]
  have h02 : 0 ≤ ((2 : ℝ) • nullRay) 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, nullRay]
    norm_num
  refine ⟨⟨2, by norm_num, rfl⟩, ?_, ?_, dirac_of_future_null hQ h0,
      dirac_of_future_null hQ2 h02⟩
  · rw [collinear_relative]
    have hsp : spatialNormSq nullRay = 1 := by simp [spatialNormSq, nullRay]
    have htime : nullRay 0 = 1 := by simp [nullRay]
    rw [phaseFrontSpeedSq, htime, hsp]
    norm_num
  · rw [collinear_relative, wavePhase_nullLine]
    simp [nullRay]

/-- Rest mass `1` and momentum `(5/4, 3/4, 0, 0)` are distinct future carriers on `Q = -1`.
The positional fringe has squared speed `1/9`. -/
theorem massive_pair_front :
    minkowskiQ (restMomentum 1) = -1 ∧
      minkowskiQ (txMomentum (5 / 4) (3 / 4)) = -1 ∧
        0 < restMomentum 1 0 ∧ 0 < txMomentum (5 / 4) (3 / 4) 0 ∧
          restMomentum 1 ≠ txMomentum (5 / 4) (3 / 4) ∧
            phaseFrontSpeedSq (txMomentum (5 / 4) (3 / 4) - restMomentum 1) = 1 / 9 ∧
              ∃ Ψ Φ : DiracSpinor, Ψ ≠ 0 ∧ Φ ≠ 0 ∧
                DiracMomentum 1 (restMomentum 1) Ψ ∧
                  DiracMomentum 1 (txMomentum (5 / 4) (3 / 4)) Φ := by
  have hrest : minkowskiQ (restMomentum 1) = -(1 : ℝ) ^ 2 := minkowskiQ_rest 1
  have hmov : minkowskiQ (txMomentum (5 / 4) (3 / 4)) = -(1 : ℝ) ^ 2 := by
    rw [minkowskiQ_eq]
    simp only [txMomentum]
    norm_num
  have h0r : 0 < restMomentum 1 0 := by simp [restMomentum]
  have h0m : 0 < txMomentum (5 / 4) (3 / 4) 0 := by
    simp only [txMomentum]
    norm_num
  have hne : restMomentum 1 ≠ txMomentum (5 / 4) (3 / 4) := by
    intro h
    have := congrFun h 1
    simp [restMomentum, txMomentum] at this
    norm_num at this
  have hfront : phaseFrontSpeedSq (txMomentum (5 / 4) (3 / 4) - restMomentum 1) = 1 / 9 := by
    have h0 : (txMomentum (5 / 4) (3 / 4) - restMomentum 1) 0 = 1 / 4 := by
      simp [txMomentum, restMomentum, Pi.sub_apply]
      norm_num
    have h1 : (txMomentum (5 / 4) (3 / 4) - restMomentum 1) 1 = 3 / 4 := by
      simp [txMomentum, restMomentum, Pi.sub_apply]
    have h2 : (txMomentum (5 / 4) (3 / 4) - restMomentum 1) 2 = 0 := by
      simp [txMomentum, restMomentum, Pi.sub_apply]
    have h3 : (txMomentum (5 / 4) (3 / 4) - restMomentum 1) 3 = 0 := by
      simp [txMomentum, restMomentum, Pi.sub_apply]
    rw [phaseFrontSpeedSq, spatialNormSq, h0, h1, h2, h3]
    norm_num
  obtain ⟨Ψ, hΨ, hdirΨ⟩ := exists_onShell_particle (m := 1) (by norm_num) hrest
  obtain ⟨Φ, hΦ, hdirΦ⟩ :=
    exists_onShell_particle (m := 1) (by norm_num) hmov
  have hrest' : minkowskiQ (restMomentum 1) = -1 := by
    rw [hrest]
    norm_num
  have hmov' : minkowskiQ (txMomentum (5 / 4) (3 / 4)) = -1 := by
    rw [hmov]
    norm_num
  exact ⟨hrest', hmov', h0r, h0m, hne, hfront, Ψ, Φ, hΨ, hΦ, hdirΨ, hdirΦ⟩

end Logic

end DoubleSpacetime
