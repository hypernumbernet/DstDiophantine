import DoubleSpacetime.Logic.Quantum.MotorReading

/-!
# Laws read off a motor's translational part

A motor is a torsion rotor times a null translator. The packet reads one Euclidean scalar of
the translator coefficients. The rotor preserves the Minkowski scalar of a co-transformed pair.
`J` and `M` are neither scalar. The laws below are what that split produces. None of them
identifies the packet's number with the rotor's number.

The biquaternion dual sends a boost to a rotation and does not preserve the null ideal, so it
does not act on positional information. The reversal that swaps the two scalars is the reversal
of the translator's time coefficient. It preserves `Q(λ)`.

* **Carrier.** `translatorInformation` is `phaseFisher` times the square of `∑ δ_μ λ^μ`.
* **Agreement.** The signed scalars agree for every translator exactly when `δ⁰ λ⁰ = 0`. The
  squares agree exactly when that product or the spatial contraction vanishes.
* **Time reversal.** Negating `λ⁰` swaps the two scalars and preserves `Q`.
* **Composition.** Translators multiply by adding coefficients, and the positional scalar adds.
  The information gains the cross term `2 · phaseFisher · s(λ) · s(μ)`. On the mass-3 mean-rest
  packet, the unit `N_1` translator and the translator `−N_1 + N_2` are each read as
  `34816/625`. Their product is the unit `N_2` translator, which is spacelike, not the identity,
  and is read as `0`.
* **Joint boost.** A `(t, x)` boost preserves the Minkowski scalar. The positional scalar moves
  by `2 sinh (sinh (δ⁰λ⁰ + δ¹λ¹) + cosh (δ⁰λ¹ + δ¹λ⁰))`. It is fixed at every rapidity exactly
  when both boost-plane pairings vanish. The mean-rest pair with unit `N_1` fails that test:
  the positional scalar goes from `-8` to `-328/9`, and the Minkowski scalar stays `-8`.
-/

namespace DoubleSpacetime

namespace Logic

open Motor Operations Real

/-! ### Time reversal of a translator coefficient -/

/-- Reverse the time coefficient. Not `Operations.dual`. -/
def timeReverse (v : Vec4) : Vec4 :=
  fun μ => if μ = 0 then -v 0 else v μ

theorem timeReverse_coord (v : Vec4) :
    timeReverse v 0 = -v 0 ∧ timeReverse v 1 = v 1 ∧ timeReverse v 2 = v 2 ∧
      timeReverse v 3 = v 3 := by
  unfold timeReverse
  refine ⟨by simp, ?_, ?_, ?_⟩
  · simp [show (1 : Fin 4) ≠ 0 by decide]
  · simp [show (2 : Fin 4) ≠ 0 by decide]
  · simp [show (3 : Fin 4) ≠ 0 by decide]

theorem timeReverse_timeReverse (v : Vec4) : timeReverse (timeReverse v) = v := by
  funext μ
  fin_cases μ <;> simp [timeReverse_coord]

/-- The packet's scalar of a translator is the rotor's scalar of its time reversal. -/
theorem wavePhase_timeReverse (a b : Vec4) :
    wavePhase a (timeReverse b) = minkowskiPhase a b := by
  rw [wavePhase_expand, minkowskiPhase_eq]
  have h := timeReverse_coord b
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  ring

/-- The rotor's scalar of a translator is the packet's scalar of its time reversal. -/
theorem minkowskiPhase_timeReverse (a b : Vec4) :
    minkowskiPhase a (timeReverse b) = wavePhase a b := by
  rw [minkowskiPhase_eq, wavePhase_expand]
  have h := timeReverse_coord b
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  ring

theorem Q31_timeReverse (v : Vec4) : Q31 (timeReverse v) = Q31 v := by
  rw [Q31_eq_minkowskiDot, Q31_eq_minkowskiDot, minkowskiDot, minkowskiDot]
  have h := timeReverse_coord v
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  ring

/-- Off mean rest, a pure time translator is the swap: the packet reads `-2` and the rotor
reads `2`. -/
theorem shellLab_time_is_swap :
    wavePhase (restMomentum 3 - shellRestP) (Pi.single 0 1) =
        minkowskiPhase (restMomentum 3 - shellRestP)
          (timeReverse (Pi.single 0 1)) ∧
      minkowskiPhase (restMomentum 3 - shellRestP) (Pi.single 0 1) =
        wavePhase (restMomentum 3 - shellRestP)
          (timeReverse (Pi.single 0 1)) ∧
        wavePhase (restMomentum 3 - shellRestP) (Pi.single 0 1) = -2 ∧
          minkowskiPhase (restMomentum 3 - shellRestP) (Pi.single 0 1) = 2 := by
  have h := shellLab_time_sign
  refine ⟨?_, ?_, h.1, h.2.1⟩
  · rw [minkowskiPhase_timeReverse, h.1]
  · rw [wavePhase_timeReverse, h.2.1]

/-! ### Composition -/

def transAdd (p q : TransParams) : TransParams where
  lambda := fun μ => p.lambda μ + q.lambda μ

theorem transParams_lambda_ext {p q : TransParams} (h : p.lambda = q.lambda) : p = q := by
  cases p
  cases q
  simpa using h

theorem transAdd_lambda (p q : TransParams) :
    (transAdd p q).lambda = p.lambda + q.lambda := by
  funext μ
  simp [transAdd, Pi.add_apply]

theorem expTrans_mul_transAdd (p q : TransParams) :
    expTrans p * expTrans q = expTrans (transAdd p q) := by
  simpa [transAdd] using expTrans_mul p q

theorem positionalScalar_add (δ : Vec4) (p q : TransParams) :
    wavePhase δ (transAdd p q).lambda = wavePhase δ p.lambda + wavePhase δ q.lambda := by
  rw [transAdd_lambda, wavePhase_add_right]

/-- Information of a product is the sum of the informations plus one cross term. -/
theorem translatorInformation_cross (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (x : Vec4) (lam mu : TransParams) (hψ : shellPacket r s α p q u v x ≠ 0) :
    translatorInformation r s α p q u v x (transAdd lam mu) =
      translatorInformation r s α p q u v x lam +
        translatorInformation r s α p q u v x mu +
        2 * phaseFisher r s u v (wavePhase (q - p) x + α) *
          wavePhase (q - p) lam.lambda * wavePhase (q - p) mu.lambda := by
  rw [translatorInformation_eq_phase r s α p q u v x (transAdd lam mu) hψ,
    translatorInformation_eq_phase r s α p q u v x lam hψ,
    translatorInformation_eq_phase r s α p q u v x mu hψ, positionalScalar_add]
  ring

/-- `−N_1 + N_2`. -/
def opposeTranslator : TransParams where
  lambda := Pi.single 1 (-1) + Pi.single 2 1

/-- Unit coefficient of `N_2`. -/
def screenTranslator : TransParams where
  lambda := Pi.single 2 1

theorem opposeTranslator_phase :
    wavePhase (shellRestQ - shellRestP) opposeTranslator.lambda = 8 := by
  have hδ := shellRest_relative
  have h0 : opposeTranslator.lambda 0 = 0 := by
    simp only [opposeTranslator, Pi.add_apply,
      Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 1),
      Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2), add_zero]
  have h1 : opposeTranslator.lambda 1 = -1 := by
    simp only [opposeTranslator, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2), add_zero]
  have h2 : opposeTranslator.lambda 2 = 1 := by
    simp only [opposeTranslator, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (2 : Fin 4) ≠ 1), zero_add]
  have h3 : opposeTranslator.lambda 3 = 0 := by
    simp only [opposeTranslator, Pi.add_apply,
      Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 1),
      Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 2), add_zero]
  rw [wavePhase_expand, h0, h1, h2, h3, hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2]
  norm_num

theorem transAdd_read_oppose :
    transAdd readTranslator opposeTranslator = screenTranslator := by
  apply transParams_lambda_ext
  funext μ
  fin_cases μ <;>
    simp [transAdd, readTranslator, opposeTranslator, screenTranslator, Pi.add_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne]

theorem screenTranslator_phase :
    wavePhase (shellRestQ - shellRestP) screenTranslator.lambda = 0 := by
  have hδ := shellRest_relative
  rw [wavePhase_expand]
  simp only [screenTranslator, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2),
    Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2),
    Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 2), hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2]
  norm_num

theorem screenTranslator_Q : Q31 screenTranslator.lambda = 1 := by
  rw [Q31_eq_minkowskiDot, minkowskiDot]
  simp only [screenTranslator, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2),
    Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2),
    Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 2)]
  norm_num

theorem screenTranslator_ne_zero : screenTranslator.lambda ≠ fun _ => 0 := by
  intro h
  have h2 : screenTranslator.lambda 2 = 0 := congrFun h 2
  simp only [screenTranslator, Pi.single_eq_same] at h2
  exact one_ne_zero h2

/-- Two readable translations compose to an unread spacelike translation. The cross term
cancels the sum of the informations, and the product motor is not `1`. -/
theorem meanRest_cancellation :
    ∃ θ : ℝ,
      phaseFisher 1 1 shellParticleP shellParticleQ θ = 544 / 625 ∧
        translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
            readTranslator = 34816 / 625 ∧
          translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
              opposeTranslator = 34816 / 625 ∧
            translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
                (transAdd readTranslator opposeTranslator) = 0 ∧
              (34816 : ℝ) / 625 + (34816 : ℝ) / 625 +
                  2 * ((544 : ℝ) / 625) * (-8) * 8 = 0 ∧
                expTrans readTranslator * expTrans opposeTranslator =
                  expTrans (transAdd readTranslator opposeTranslator) ∧
                  expTrans (transAdd readTranslator opposeTranslator) ≠ 1 ∧
                    Q31 (transAdd readTranslator opposeTranslator).lambda = 1 := by
  obtain ⟨θ, hF, _, _, _, _, _⟩ := shellRest_translationFisher
  have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
  have hread : translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
      readTranslator = 34816 / 625 := by
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 readTranslator hψ, wavePhase_zero, zero_add, hF, shellRest_read_phase]
    norm_num
  have hoppose : translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
      opposeTranslator = 34816 / 625 := by
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 opposeTranslator hψ, wavePhase_zero, zero_add, hF, opposeTranslator_phase]
    norm_num
  have hzero : translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
      (transAdd readTranslator opposeTranslator) = 0 := by
    rw [transAdd_read_oppose, translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ
        shellParticleP shellParticleQ 0 screenTranslator hψ, wavePhase_zero, zero_add,
      screenTranslator_phase, zero_pow (by norm_num), mul_zero]
  have hcross : (34816 : ℝ) / 625 + (34816 : ℝ) / 625 +
      2 * ((544 : ℝ) / 625) * (-8) * 8 = 0 := by
    norm_num
  have hne : expTrans (transAdd readTranslator opposeTranslator) ≠ 1 := by
    rw [transAdd_read_oppose]
    exact expTrans_ne_one_of_lambda screenTranslator_ne_zero
  have hQ : Q31 (transAdd readTranslator opposeTranslator).lambda = 1 := by
    rw [transAdd_read_oppose]
    exact screenTranslator_Q
  exact ⟨θ, hF, hread, hoppose, hzero, hcross, expTrans_mul_transAdd _ _, hne, hQ⟩

/-! ### Joint boost -/

/-- A joint `(t, x)` boost preserves the Minkowski scalar and shifts the positional scalar by
twice the product of the boosted time coefficients. -/
theorem wavePhase_jointBoost {ch sh : ℝ} (h : ch ^ 2 - sh ^ 2 = 1) (a b : Vec4) :
    wavePhase (boost01 ch sh a) (boost01 ch sh b) =
      minkowskiPhase a b + 2 * boost01 ch sh a 0 * boost01 ch sh b 0 := by
  have hsub := wavePhase_sub_minkowskiPhase (boost01 ch sh a) (boost01 ch sh b)
  have hinv := boost01_minkowskiPhase h a b
  calc
    wavePhase (boost01 ch sh a) (boost01 ch sh b)
      = minkowskiPhase (boost01 ch sh a) (boost01 ch sh b) +
          2 * boost01 ch sh a 0 * boost01 ch sh b 0 := by
        linarith
    _ = minkowskiPhase a b + 2 * boost01 ch sh a 0 * boost01 ch sh b 0 := by rw [hinv]

theorem wavePhase_jointBoost_shift {ch sh : ℝ} (h : ch ^ 2 - sh ^ 2 = 1) (a b : Vec4) :
    wavePhase (boost01 ch sh a) (boost01 ch sh b) - wavePhase a b =
      2 * sh * (sh * (a 0 * b 0 + a 1 * b 1) + ch * (a 0 * b 1 + a 1 * b 0)) := by
  rw [wavePhase_expand, wavePhase_expand]
  simp only [boost01]
  have hsq : ch ^ 2 + sh ^ 2 - 1 = 2 * sh ^ 2 := by nlinarith [h]
  have hrhs :
      (ch * a 0 + sh * a 1) * (ch * b 0 + sh * b 1) +
          (sh * a 0 + ch * a 1) * (sh * b 0 + ch * b 1) + a 2 * b 2 + a 3 * b 3 -
          (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3) =
        (ch ^ 2 + sh ^ 2 - 1) * (a 0 * b 0 + a 1 * b 1) +
          2 * ch * sh * (a 0 * b 1 + a 1 * b 0) := by ring
  rw [hrhs, hsq]
  ring

/-- The positional scalar is unchanged by every joint `(t, x)` boost exactly when both
boost-plane pairings vanish. -/
theorem wavePhase_jointBoost_invariant_iff (a b : Vec4) :
    (∀ ch sh : ℝ, ch ^ 2 - sh ^ 2 = 1 →
      wavePhase (boost01 ch sh a) (boost01 ch sh b) = wavePhase a b) ↔
      a 0 * b 0 + a 1 * b 1 = 0 ∧ a 0 * b 1 + a 1 * b 0 = 0 := by
  set P := a 0 * b 0 + a 1 * b 1
  set C := a 0 * b 1 + a 1 * b 0
  constructor
  · intro h
    have hpos : 0 < sinh 1 := sinh_pos_iff.mpr (by norm_num : (0 : ℝ) < 1)
    have hcosh : 0 < cosh 1 := cosh_pos 1
    have hP : sinh 1 * P + cosh 1 * C = 0 := by
      have hs := wavePhase_jointBoost_shift (cosh_sq_sub_sinh_sq 1) a b
      rw [h (cosh 1) (sinh 1) (cosh_sq_sub_sinh_sq 1), sub_self] at hs
      have hzero : (2 : ℝ) * sinh 1 * (sinh 1 * P + cosh 1 * C) = 0 := by
        simpa [P, C] using hs.symm
      exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) hpos.ne')
    have hN : -(sinh 1) * P + cosh 1 * C = 0 := by
      have hs := wavePhase_jointBoost_shift (cosh_sq_sub_sinh_sq (-1)) a b
      rw [h (cosh (-1)) (sinh (-1)) (cosh_sq_sub_sinh_sq (-1)), sub_self] at hs
      have hzero : (2 : ℝ) * sinh (-1) * (sinh (-1) * P + cosh (-1) * C) = 0 := by
        simpa [P, C] using hs.symm
      have hsh : sinh (-1) ≠ 0 := by
        rw [sinh_neg]
        exact neg_ne_zero.mpr hpos.ne'
      have hprod : sinh (-1) * P + cosh (-1) * C = 0 :=
        (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) hsh)
      simpa [sinh_neg, cosh_neg] using hprod
    have hC0 : C = 0 := by
      have hsum : (sinh 1 * P + cosh 1 * C) + (-(sinh 1) * P + cosh 1 * C) = 0 := by
        rw [hP, hN, zero_add]
      have hC : (2 : ℝ) * cosh 1 * C = 0 := by nlinarith
      exact (mul_eq_zero.mp hC).resolve_left (mul_ne_zero (by norm_num) hcosh.ne')
    have hP0 : P = 0 := by
      rw [hC0, mul_zero, add_zero] at hP
      exact (mul_eq_zero.mp hP).resolve_left hpos.ne'
    exact ⟨hP0, hC0⟩
  · intro h ch sh hhyp
    have hs := wavePhase_jointBoost_shift hhyp a b
    have hpair :
        a 0 * b 0 + a 1 * b 1 = P ∧ a 0 * b 1 + a 1 * b 0 = C :=
      ⟨rfl, rfl⟩
    rw [hpair.1, hpair.2, h.1, h.2] at hs
    have hzero : wavePhase (boost01 ch sh a) (boost01 ch sh b) - wavePhase a b = 0 := by
      calc
        wavePhase (boost01 ch sh a) (boost01 ch sh b) - wavePhase a b
          = 2 * sh * (sh * (0 : ℝ) + ch * 0) := hs
        _ = 0 := by ring
    exact sub_eq_zero.mp hzero

/-- Mean rest against unit `N_1`: the positional scalar moves from `-8` to `-328/9`, and the
Minkowski scalar stays `-8`. -/
theorem shellRest_joint_shift :
    wavePhase (boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP))
        (boost01 (5 / 3) (-4 / 3) readTranslator.lambda) = -328 / 9 ∧
      minkowskiPhase (boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP))
          (boost01 (5 / 3) (-4 / 3) readTranslator.lambda) = -8 ∧
        -328 / 9 ≠ (-8 : ℝ) := by
  have hhyp : ((5 : ℝ) / 3) ^ 2 - (-4 / 3) ^ 2 = 1 := by norm_num
  have hδ := shellRest_relative
  have hD0 : boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP) 0 = 32 / 3 := by
    simp only [boost01, hδ.1, hδ.2.1]
    norm_num
  have hL0 : boost01 (5 / 3) (-4 / 3) readTranslator.lambda 0 = -4 / 3 := by
    simp only [boost01, readTranslator,
      Pi.single_eq_of_ne (show (0 : Fin 4) ≠ 1 by decide), Pi.single_eq_same]
    norm_num
  refine ⟨?_, ?_, by norm_num⟩
  · rw [wavePhase_jointBoost hhyp, shellRest_read_minkowski, hD0, hL0]
    norm_num
  · rw [boost01_minkowskiPhase hhyp, shellRest_read_minkowski]

end Logic

end DoubleSpacetime
