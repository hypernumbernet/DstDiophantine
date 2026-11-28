import DoubleSpacetime.Algebra.BivectorBasis
import DoubleSpacetime.Algebra.Motor
import DoubleSpacetime.Logic.Quantum.TranslationFisher

/-!
# What of a motor carries positional information

A motor is a torsion rotor times a null translator `T(λ) = 1 + Σ_μ (λ^μ / 2) N_μ`. The four
coefficients `λ` are the translational part of the motor. They are not four locations.

A shell packet reads `λ` only through the scalar `(q − p) · λ`. The Fisher information of that
reading is `phaseFisher · ((q − p) · λ)²`, the same quadratic form as `displacementInformation`.
Translators that differ by a vector orthogonal to `q − p` are distinct elements of the algebra,
because the null generators are linearly independent, and they carry the same information. The
zero translator carries none. The torsion rotor does not occur in the formula, so `J` and `M` are
not this number.

On the mass-3 mean-rest packet the relative momentum is `(0, -8, 0, 0)`. The translator along
`N_1` is read. At a quadrature phase its information is `34816/625`, while `positionOp` at the
origin reads `0`. The translator along the null line `e₀ − e₃` — the line a null rotation
preserves, and the line along which that rotation displaces the screen — has information `0` at
every phase, and it is not the identity motor. Adding `N_2` to `N_1` changes the motor and does
not change the information. A packet of one momentum reads every translator as `0`.
-/

namespace DoubleSpacetime

namespace Logic

open Motor

/-! ### The scalar a packet can read -/

/-- Positional information of the translator `λ`, read by one shell packet at one chart point. -/
noncomputable def translatorInformation (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (x : Vec4) (lam : TransParams) : ℝ :=
  displacementInformation (shellPacket r s α p q u v) x lam.lambda

theorem translatorInformation_eq_phase (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (x : Vec4) (lam : TransParams) (hψ : shellPacket r s α p q u v x ≠ 0) :
    translatorInformation r s α p q u v x lam =
      phaseFisher r s u v (wavePhase (q - p) x + α) *
        wavePhase (q - p) lam.lambda ^ 2 := by
  rw [translatorInformation, displacementInformation_shellPacket r s α p q u v x lam.lambda hψ]
  rfl

theorem translatorInformation_congr (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (x : Vec4) {lam lam' : TransParams}
    (h : wavePhase (q - p) lam.lambda = wavePhase (q - p) lam'.lambda)
    (hψ : shellPacket r s α p q u v x ≠ 0) :
    translatorInformation r s α p q u v x lam =
      translatorInformation r s α p q u v x lam' := by
  rw [translatorInformation_eq_phase r s α p q u v x lam hψ,
    translatorInformation_eq_phase r s α p q u v x lam' hψ, h]

theorem translatorInformation_of_phase_zero (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (x : Vec4) {lam : TransParams} (h : wavePhase (q - p) lam.lambda = 0)
    (hψ : shellPacket r s α p q u v x ≠ 0) :
    translatorInformation r s α p q u v x lam = 0 := by
  rw [translatorInformation_eq_phase r s α p q u v x lam hψ, h, zero_pow (by norm_num), mul_zero]

/-- The zero translator is `1`, and a nonzero packet reads it as no positional information. -/
theorem zeroTranslator_unread (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (x : Vec4)
    (hψ : shellPacket r s α p q u v x ≠ 0) :
    translatorInformation r s α p q u v x ⟨fun _ => 0⟩ = 0 := by
  apply translatorInformation_of_phase_zero r s α p q u v x _ hψ
  simp [wavePhase]

theorem sameMomentum_translator_unread (r s α : ℝ) (p : Vec4) (u v : DiracSpinor)
    (x : Vec4) (lam : TransParams) (hψ : shellPacket r s α p p u v x ≠ 0) :
    translatorInformation r s α p p u v x lam = 0 := by
  apply translatorInformation_of_phase_zero r s α p p u v x _ hψ
  simp [wavePhase]

/-! ### Distinct coefficients, one scalar -/

theorem lambda_of_omegaTrans {p q : TransParams} (h : omegaTrans p = omegaTrans q) :
    p.lambda = q.lambda := by
  let d : TransParams := ⟨fun μ => p.lambda μ + -q.lambda μ⟩
  have hneg : omegaTrans ⟨fun μ => -q.lambda μ⟩ = -omegaTrans q := by
    simp only [omegaTrans]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [neg_div, neg_smul]
  have hd : omegaTrans d = omegaTrans p + omegaTrans ⟨fun μ => -q.lambda μ⟩ :=
    (omegaTrans_add p ⟨fun μ => -q.lambda μ⟩).symm
  have hzero : omegaTrans d = 0 := by
    calc
      omegaTrans d = omegaTrans p + omegaTrans ⟨fun μ => -q.lambda μ⟩ := hd
      _ = omegaTrans p + -omegaTrans q := by rw [hneg]
      _ = omegaTrans q + -omegaTrans q := by rw [h]
      _ = 0 := add_neg_cancel _
  have hsum : (∑ μ : Fin 4, ((p.lambda μ + -q.lambda μ) / 2) • Generators.null μ) = 0 := by
    simpa [omegaTrans, d] using hzero
  have hcoef :=
    (Fintype.linearIndependent_iff (v := Generators.null)).mp
      BivectorBasis.linearIndependent_null (fun μ => (p.lambda μ + -q.lambda μ) / 2) hsum
  ext μ
  have hc : (p.lambda μ + -q.lambda μ) / 2 = 0 := hcoef μ
  linarith

theorem expTrans_zero : expTrans ⟨fun _ => 0⟩ = 1 := by
  unfold expTrans omegaTrans
  simp

theorem expTrans_ne_of_lambda {p q : TransParams} (h : p.lambda ≠ q.lambda) :
    expTrans p ≠ expTrans q := by
  intro heq
  apply h
  apply lambda_of_omegaTrans
  have hsum : (1 : PGA) + omegaTrans p = 1 + omegaTrans q := by
    simpa [expTrans] using heq
  exact add_left_cancel hsum

theorem expTrans_ne_one_of_lambda {p : TransParams} (h : p.lambda ≠ fun _ => 0) :
    expTrans p ≠ 1 := by
  rw [← expTrans_zero]
  exact expTrans_ne_of_lambda h

/-- Unit coefficient of `N_1`. -/
def readTranslator : TransParams where
  lambda := Pi.single 1 1

/-- The same `N_1` coefficient, plus a multiple of `N_2`. -/
def kernelTranslator (a : ℝ) : TransParams where
  lambda := Pi.single 1 1 + a • Pi.single 2 1

/-- Translator along the null line `e₀ − e₃`. -/
def nullLineTranslator : TransParams where
  lambda := Pi.single 0 1 - Pi.single 3 1

theorem kernelTranslator_lambda_ne {a : ℝ} (ha : a ≠ 0) :
    (kernelTranslator a).lambda ≠ readTranslator.lambda := by
  intro h
  have hleft : (kernelTranslator a).lambda 2 = a := by
    simp only [kernelTranslator, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 1 by decide)]
    ring
  have hright : readTranslator.lambda 2 = 0 := by
    simp only [readTranslator, Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 1 by decide)]
  exact ha ((hleft.symm.trans (congrFun h 2)).trans hright)

theorem nullLineTranslator_lambda_ne_zero : nullLineTranslator.lambda ≠ fun _ => 0 := by
  intro h
  have hleft : nullLineTranslator.lambda 0 = 1 := by
    simp only [nullLineTranslator, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (show (0 : Fin 4) ≠ 3 by decide), sub_zero]
  exact one_ne_zero (hleft.symm.trans (congrFun h 0))

theorem shellRest_read_phase :
    wavePhase (shellRestQ - shellRestP) readTranslator.lambda = -8 := by
  simp [readTranslator, wavePhase_single, shellRest_relative.2.1]

theorem shellRest_kernel_phase (a : ℝ) :
    wavePhase (shellRestQ - shellRestP) (kernelTranslator a).lambda =
      wavePhase (shellRestQ - shellRestP) readTranslator.lambda := by
  rw [shellRest_read_phase]
  have hsplit : (kernelTranslator a).lambda =
      Pi.single 1 (1 : ℝ) + a • Pi.single 2 (1 : ℝ) := rfl
  rw [hsplit, wavePhase_add_right, wavePhase_smul_right, wavePhase_single, wavePhase_single,
    shellRest_relative.2.1, shellRest_relative.2.2.1]
  ring

theorem shellRest_nullLine_phase :
    wavePhase (shellRestQ - shellRestP) nullLineTranslator.lambda = 0 := by
  have h0 : nullLineTranslator.lambda 0 = 1 := by
    simp only [nullLineTranslator, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (show (0 : Fin 4) ≠ 3 by decide), sub_zero]
  have h1 : nullLineTranslator.lambda 1 = 0 := by
    simp only [nullLineTranslator, Pi.sub_apply,
      Pi.single_eq_of_ne (show (1 : Fin 4) ≠ 0 by decide),
      Pi.single_eq_of_ne (show (1 : Fin 4) ≠ 3 by decide), sub_self]
  have h2 : nullLineTranslator.lambda 2 = 0 := by
    simp only [nullLineTranslator, Pi.sub_apply,
      Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 0 by decide),
      Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 3 by decide), sub_self]
  have h3 : nullLineTranslator.lambda 3 = -1 := by
    simp only [nullLineTranslator, Pi.sub_apply,
      Pi.single_eq_of_ne (show (3 : Fin 4) ≠ 0 by decide), Pi.single_eq_same, zero_sub]
  unfold wavePhase
  simp only [Fin.sum_univ_four, h0, h1, h2, h3, shellRest_relative.1, shellRest_relative.2.1,
    shellRest_relative.2.2.1, shellRest_relative.2.2.2]
  norm_num

theorem shellRest_kernel_same_information (a α : ℝ) (x : Vec4) :
    translatorInformation 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ x
        (kernelTranslator a) =
      translatorInformation 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ x
        readTranslator :=
  translatorInformation_congr 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ x
    (shellRest_kernel_phase a) (shellRest_packet_ne_zero α x)

theorem shellRest_nullLine_unread (α : ℝ) (x : Vec4) :
    translatorInformation 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ x
        nullLineTranslator =
      0 :=
  translatorInformation_of_phase_zero 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ x
    shellRest_nullLine_phase (shellRest_packet_ne_zero α x)

theorem shellRest_translator_split :
    (∃ θ : ℝ,
      translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
          readTranslator = 34816 / 625 ∧
        translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
            nullLineTranslator = 0 ∧
          (inner ℂ (shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0)
              (positionOp 1 (shellPacket 1 1 θ shellRestP shellRestQ shellParticleP
                shellParticleQ) 0)).re /
            ‖shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0‖ ^ 2 = 0) ∧
      expTrans (kernelTranslator 1) ≠ expTrans readTranslator ∧
        expTrans nullLineTranslator ≠ 1 := by
  refine ⟨?_, expTrans_ne_of_lambda (kernelTranslator_lambda_ne (by norm_num : (1 : ℝ) ≠ 0)),
      expTrans_ne_one_of_lambda nullLineTranslator_lambda_ne_zero⟩
  obtain ⟨θ, _, hF, _, _⟩ := shellRest_chartFisher.1
  refine ⟨θ, ?_, shellRest_nullLine_unread θ 0, ?_⟩
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 readTranslator hψ, wavePhase_zero, zero_add, hF, shellRest_read_phase]
    norm_num
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    rw [position_reading (Ψ := shellPacket 1 1 θ shellRestP shellRestQ shellParticleP
        shellParticleQ) (μ := 1) (x := 0) hψ]
    simp

end Logic

end DoubleSpacetime
