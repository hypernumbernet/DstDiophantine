import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Dual-rotor particle action: Euler–Lagrange identities

The written Lagrangian has free mismatch and sources the common channel; it
does not yield the oscillator \(\ddot\delta+m\delta=0\). No value of \(m\) is
fixed, and a constant dual drive is not derived from Faraday helicity. The
conjugate momenta are half the mismatch rate and half the common rate; the
stiffness \(m\) is not a factor in either.
-/

namespace DstDiophantine

namespace Gravity

/-! ### Written Lagrangian and its actual Euler–Lagrange system -/

/-- One-axis density of the paper action, as a function of positions and velocities. -/
noncomputable def paperLagrangian (m φ θ φdot θdot : ℝ) : ℝ :=
  (1 / 2) * φdot ^ 2 - (1 / 2) * θdot ^ 2 - (m / 2) * (φ - θ) ^ 2

/-- Algebraic \(\partial L/\partial\phi\) of the written Lagrangian. -/
def paperForcePhi (m φ θ : ℝ) : ℝ := -m * (φ - θ)

/-- Algebraic \(\partial L/\partial\theta\) of the written Lagrangian. -/
def paperForceTheta (m φ θ : ℝ) : ℝ := m * (φ - θ)

/-- Correct Euler–Lagrange equations of the written Lagrangian. -/
def PaperActualEL (m φ θ φddot θddot : ℝ) : Prop :=
  φddot = paperForcePhi m φ θ ∧ θddot = -paperForceTheta m φ θ

theorem paperActualEL_eq (m φ θ φddot θddot : ℝ) :
    PaperActualEL m φ θ φddot θddot ↔
      φddot = -m * (φ - θ) ∧ θddot = -m * (φ - θ) := by
  simp [PaperActualEL, paperForcePhi, paperForceTheta]

theorem paperLagrangian_eq_mixed (m φ θ φdot θdot : ℝ) :
    paperLagrangian m φ θ φdot θdot =
      (1 / 2) * (φdot + θdot) * (φdot - θdot) - (m / 2) * (φ - θ) ^ 2 := by
  unfold paperLagrangian
  ring

theorem paperActualEL_iff_channels (m φ θ φddot θddot : ℝ) :
    PaperActualEL m φ θ φddot θddot ↔
      φddot - θddot = 0 ∧ φddot + θddot = -2 * m * (φ - θ) := by
  rw [paperActualEL_eq]
  constructor
  · intro ⟨hφ, hθ⟩
    constructor <;> linarith
  · intro ⟨hδ, hσ⟩
    constructor <;> linarith

theorem paperActualEL_free_mismatch {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    φddot - θddot = 0 :=
  (paperActualEL_iff_channels m φ θ φddot θddot).mp h |>.1

theorem paperActualEL_common_driven {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    φddot + θddot = -2 * m * (φ - θ) :=
  (paperActualEL_iff_channels m φ θ φddot θddot).mp h |>.2

/-! ### Conjugate momenta do not carry the stiffness -/

/-- Half the mismatch rate. The stiffness `m` is not an argument. -/
noncomputable def paperMomentumSigma (φdot θdot : ℝ) : ℝ :=
  (1 / 2) * (φdot - θdot)

/-- Half the common rate. The stiffness `m` is not an argument. -/
noncomputable def paperMomentumDelta (φdot θdot : ℝ) : ℝ :=
  (1 / 2) * (φdot + θdot)

/-- Algebraic jet of `paperMomentumSigma`, half the mismatch acceleration. -/
noncomputable def paperMomentumSigmaDot (φddot θddot : ℝ) : ℝ :=
  (1 / 2) * (φddot - θddot)

/-- Algebraic jet of `paperMomentumDelta`, half the common acceleration. -/
noncomputable def paperMomentumDeltaDot (φddot θddot : ℝ) : ℝ :=
  (1 / 2) * (φddot + θddot)

theorem paperMomentum_zero :
    paperMomentumSigma 0 0 = 0 ∧ paperMomentumDelta 0 0 = 0 := by
  constructor <;> simp [paperMomentumSigma, paperMomentumDelta]

/-- On the written flow, `p_σ` is conserved and `p_δ` changes at `-m δ`. -/
theorem paperMomentum_jets_of_actualEL {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    paperMomentumSigmaDot φddot θddot = (1 / 2) * (φddot - θddot) ∧
      paperMomentumSigmaDot φddot θddot = 0 ∧
      paperMomentumDeltaDot φddot θddot = (1 / 2) * (φddot + θddot) ∧
      paperMomentumDeltaDot φddot θddot = -m * (φ - θ) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · rw [paperMomentumSigmaDot, paperActualEL_free_mismatch h]
    ring
  · rw [paperMomentumDeltaDot, paperActualEL_common_driven h]
    ring

/-- Jacobi integral of the written density. -/
noncomputable def paperEnergy (m φ θ φdot θdot : ℝ) : ℝ :=
  (1 / 2) * φdot ^ 2 - (1 / 2) * θdot ^ 2 + (m / 2) * (φ - θ) ^ 2

theorem paperEnergy_eq_mixed (m φ θ φdot θdot : ℝ) :
    paperEnergy m φ θ φdot θdot =
      (1 / 2) * (φdot + θdot) * (φdot - θdot) + (m / 2) * (φ - θ) ^ 2 := by
  unfold paperEnergy
  ring

/-- Formal \(\dot E=\dot\phi\,\ddot\phi-\dot\theta\,\ddot\theta+m\delta(\dot\phi-\dot\theta)\). -/
def paperEnergyDot (m φ θ φdot θdot φddot θddot : ℝ) : ℝ :=
  φdot * φddot - θdot * θddot + m * (φ - θ) * (φdot - θdot)

theorem paperEnergy_conserved {m φ θ φdot θdot φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    paperEnergyDot m φ θ φdot θdot φddot θddot = 0 := by
  rcases (paperActualEL_eq m φ θ φddot θddot).mp h with ⟨hφ, hθ⟩
  simp [paperEnergyDot, hφ, hθ]
  ring

theorem paperEnergy_indefinite :
    (∃ m φ θ φdot θdot : ℝ, 0 < paperEnergy m φ θ φdot θdot) ∧
      (∃ m φ θ φdot θdot : ℝ, paperEnergy m φ θ φdot θdot < 0) :=
  ⟨⟨1, 1, 0, 0, 0, by unfold paperEnergy; norm_num⟩,
    ⟨1, 0, 0, 0, 1, by unfold paperEnergy; norm_num⟩⟩

/-- The written action does not yield the claimed oscillator `δ̈ + mδ = 0`. -/
theorem paperActualEL_not_oscillator :
    ∃ m φ θ φddot θddot : ℝ,
      PaperActualEL m φ θ φddot θddot ∧
        φddot - θddot ≠ -m * (φ - θ) := by
  refine ⟨1, 1, 0, -1, -1, ?_, ?_⟩
  · exact (paperActualEL_eq 1 1 0 (-1) (-1)).mpr ⟨by norm_num, by norm_num⟩
  · norm_num

/-! ### Neighbouring runaway system -/

/-- Neighbouring system, not the Euler–Lagrange equations of the written Lagrangian. -/
def PaperClaimedEL (m φ θ φddot θddot : ℝ) : Prop :=
  φddot = m * (φ - θ) ∧ -θddot = m * (φ - θ)

theorem paperClaimedEL_runaway {m φ θ φddot θddot : ℝ}
    (h : PaperClaimedEL m φ θ φddot θddot) :
    φddot - θddot = 2 * m * (φ - θ) := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem paperClaimedEL_free_common {m φ θ φddot θddot : ℝ}
    (h : PaperClaimedEL m φ θ φddot θddot) :
    φddot + θddot = 0 := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem paperClaimedEL_not_oscillator :
    ∃ m φ θ φddot θddot : ℝ,
      PaperClaimedEL m φ θ φddot θddot ∧
        φddot - θddot ≠ -m * (φ - θ) := by
  refine ⟨1, 1, 0, 1, -1, ⟨by norm_num, by norm_num⟩, ?_⟩
  norm_num

theorem paperClaimedEL_ne_actual :
    ∃ m φ θ φddot θddot : ℝ,
      PaperClaimedEL m φ θ φddot θddot ∧ ¬ PaperActualEL m φ θ φddot θddot := by
  refine ⟨1, 1, 0, 1, -1, ⟨by norm_num, by norm_num⟩, ?_⟩
  intro h
  have := paperActualEL_free_mismatch h
  norm_num at this

/-! ### Working oscillator model (not the written action) -/

/-- Same-sign kinetic density, used only as an explicit working model. -/
noncomputable def oscillatorLagrangian (m φ θ φdot θdot : ℝ) : ℝ :=
  (1 / 2) * φdot ^ 2 + (1 / 2) * θdot ^ 2 - (m / 2) * (φ - θ) ^ 2

def oscillatorForcePhi (m φ θ : ℝ) : ℝ := -m * (φ - θ)
def oscillatorForceTheta (m φ θ : ℝ) : ℝ := m * (φ - θ)

/-- Euler–Lagrange equations of the same-sign working model. -/
def OscillatorEL (m φ θ φddot θddot : ℝ) : Prop :=
  φddot = oscillatorForcePhi m φ θ ∧ θddot = oscillatorForceTheta m φ θ

theorem oscillatorEL_eq (m φ θ φddot θddot : ℝ) :
    OscillatorEL m φ θ φddot θddot ↔
      φddot = -m * (φ - θ) ∧ θddot = m * (φ - θ) := by
  simp [OscillatorEL, oscillatorForcePhi, oscillatorForceTheta]

theorem oscillatorLagrangian_eq_split (m φ θ φdot θdot : ℝ) :
    oscillatorLagrangian m φ θ φdot θdot =
      (1 / 4) * (φdot + θdot) ^ 2 + (1 / 4) * (φdot - θdot) ^ 2 -
        (m / 2) * (φ - θ) ^ 2 := by
  unfold oscillatorLagrangian
  ring

theorem oscillatorEL_harmonic {m φ θ φddot θddot : ℝ}
    (h : OscillatorEL m φ θ φddot θddot) :
    (φddot - θddot) + 2 * m * (φ - θ) = 0 := by
  rcases (oscillatorEL_eq m φ θ φddot θddot).mp h with ⟨hφ, hθ⟩
  linarith

theorem oscillatorEL_free_common {m φ θ φddot θddot : ℝ}
    (h : OscillatorEL m φ θ φddot θddot) :
    φddot + θddot = 0 := by
  rcases (oscillatorEL_eq m φ θ φddot θddot).mp h with ⟨hφ, hθ⟩
  linarith

/-- Jacobi integral of the same-sign working model. -/
noncomputable def oscillatorEnergy (m φ θ φdot θdot : ℝ) : ℝ :=
  (1 / 2) * φdot ^ 2 + (1 / 2) * θdot ^ 2 + (m / 2) * (φ - θ) ^ 2

def oscillatorEnergyDot (m φ θ φdot θdot φddot θddot : ℝ) : ℝ :=
  φdot * φddot + θdot * θddot + m * (φ - θ) * (φdot - θdot)

theorem oscillatorEnergy_conserved {m φ θ φdot θdot φddot θddot : ℝ}
    (h : OscillatorEL m φ θ φddot θddot) :
    oscillatorEnergyDot m φ θ φdot θdot φddot θddot = 0 := by
  rcases (oscillatorEL_eq m φ θ φddot θddot).mp h with ⟨hφ, hθ⟩
  simp [oscillatorEnergyDot, hφ, hθ]
  ring

theorem oscillatorEnergy_nonneg {m φ θ φdot θdot : ℝ} (hm : 0 ≤ m) :
    0 ≤ oscillatorEnergy m φ θ φdot θdot := by
  unfold oscillatorEnergy
  nlinarith [sq_nonneg φdot, sq_nonneg θdot, sq_nonneg (φ - θ)]

/-! ### Dual-channel generalised acceleration \(u\)

The sign convention is kinematic: \(u\) is added to \(\ddot\theta\).
-/

/-- Written Euler–Lagrange with a dual-channel acceleration \(u\). -/
def PaperSourcedEL (m φ θ φddot θddot u : ℝ) : Prop :=
  φddot = -m * (φ - θ) ∧ θddot = -m * (φ - θ) + u

theorem paperSourcedEL_mismatch {m φ θ φddot θddot u : ℝ}
    (h : PaperSourcedEL m φ θ φddot θddot u) :
    φddot - θddot = -u := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem paperSourcedEL_common {m φ θ φddot θddot u : ℝ}
    (h : PaperSourcedEL m φ θ φddot θddot u) :
    φddot + θddot = -2 * m * (φ - θ) + u := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem paperSourcedEL_iff_channels (m φ θ φddot θddot u : ℝ) :
    PaperSourcedEL m φ θ φddot θddot u ↔
      φddot - θddot = -u ∧ φddot + θddot = -2 * m * (φ - θ) + u := by
  constructor
  · intro h
    exact ⟨paperSourcedEL_mismatch h, paperSourcedEL_common h⟩
  · intro ⟨hδ, hσ⟩
    constructor <;> linarith

theorem paperSourcedEL_zero_iff (m φ θ φddot θddot : ℝ) :
    PaperSourcedEL m φ θ φddot θddot 0 ↔ PaperActualEL m φ θ φddot θddot := by
  simp [PaperSourcedEL, PaperActualEL, paperForcePhi, paperForceTheta]

/-- Same-sign working model with a dual-channel acceleration \(u\). -/
def OscillatorSourcedEL (m φ θ φddot θddot u : ℝ) : Prop :=
  φddot = -m * (φ - θ) ∧ θddot = m * (φ - θ) + u

theorem oscillatorSourcedEL_mismatch {m φ θ φddot θddot u : ℝ}
    (h : OscillatorSourcedEL m φ θ φddot θddot u) :
    (φddot - θddot) + 2 * m * (φ - θ) = -u := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem oscillatorSourcedEL_common {m φ θ φddot θddot u : ℝ}
    (h : OscillatorSourcedEL m φ θ φddot θddot u) :
    φddot + θddot = u := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem oscillatorSourcedEL_eq_mismatch {m φ θ u : ℝ} (hm : m ≠ 0)
    (h : OscillatorSourcedEL m φ θ 0 0 u) :
    φ - θ = -u / (2 * m) := by
  have hδ := oscillatorSourcedEL_mismatch h
  have h2 : (2 : ℝ) * m ≠ 0 := mul_ne_zero two_ne_zero hm
  exact (eq_div_iff h2).mpr (by linarith)

theorem oscillatorSourcedEL_zero_iff (m φ θ φddot θddot : ℝ) :
    OscillatorSourcedEL m φ θ φddot θddot 0 ↔ OscillatorEL m φ θ φddot θddot := by
  simp [OscillatorSourcedEL, OscillatorEL, oscillatorForcePhi, oscillatorForceTheta]

/-! ### Dual-only jets are constrained -/

theorem paperSourcedEL_of_phi_ddot_zero {m φ θ φddot θddot u : ℝ}
    (h : PaperSourcedEL m φ θ φddot θddot u) (hφ : φddot = 0) :
    m * (φ - θ) = 0 ∧ θddot = u := by
  rcases h with ⟨hφel, hθel⟩
  have hm : m * (φ - θ) = 0 := by linarith
  exact ⟨hm, by linarith⟩

theorem paperSourcedEL_not_dual_only_of_mismatch {m φ θ φddot θddot u : ℝ}
    (hm : m ≠ 0) (hδ : φ ≠ θ) :
    ¬ (PaperSourcedEL m φ θ φddot θddot u ∧ φddot = 0) := by
  intro ⟨h, hφ⟩
  have hmul := (paperSourcedEL_of_phi_ddot_zero h hφ).1
  exact hδ (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hm))

theorem oscillatorSourcedEL_of_phi_ddot_zero {m φ θ φddot θddot u : ℝ}
    (h : OscillatorSourcedEL m φ θ φddot θddot u) (hφ : φddot = 0) :
    m * (φ - θ) = 0 ∧ θddot = u := by
  rcases h with ⟨hφel, hθel⟩
  have hm : m * (φ - θ) = 0 := by linarith
  exact ⟨hm, by linarith⟩

theorem oscillatorSourcedEL_not_dual_only_of_mismatch {m φ θ φddot θddot u : ℝ}
    (hm : m ≠ 0) (hδ : φ ≠ θ) :
    ¬ (OscillatorSourcedEL m φ θ φddot θddot u ∧ φddot = 0) := by
  intro ⟨h, hφ⟩
  have hmul := (oscillatorSourcedEL_of_phi_ddot_zero h hφ).1
  exact hδ (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hm))

/-! ### Both-channel forces and the constraint that realises dual-only -/

/-- Written Euler–Lagrange with a usual force \(v\) and a dual force \(u\). -/
def PaperBothSourcedEL (m φ θ φddot θddot v u : ℝ) : Prop :=
  φddot = -m * (φ - θ) + v ∧ θddot = -m * (φ - θ) + u

theorem paperSourcedEL_iff_both_zero_usual (m φ θ φddot θddot u : ℝ) :
    PaperSourcedEL m φ θ φddot θddot u ↔
      PaperBothSourcedEL m φ θ φddot θddot 0 u := by
  simp [PaperSourcedEL, PaperBothSourcedEL]

theorem paperEnergyDot_both_sourced {m φ θ φdot θdot φddot θddot v u : ℝ}
    (h : PaperBothSourcedEL m φ θ φddot θddot v u) :
    paperEnergyDot m φ θ φdot θdot φddot θddot = v * φdot - u * θdot := by
  rcases h with ⟨hφ, hθ⟩
  simp [paperEnergyDot, hφ, hθ]
  ring

theorem paperBothSourcedEL_constraint_force {m φ θ φddot θddot v u : ℝ}
    (h : PaperBothSourcedEL m φ θ φddot θddot v u) (hφ : φddot = 0) :
    v = m * (φ - θ) := by
  rcases h with ⟨hφel, _⟩
  linarith

theorem paperEnergyDot_rest_usual {m φ θ φdot θdot φddot θddot v u : ℝ}
    (h : PaperBothSourcedEL m φ θ φddot θddot v u) (hφdot : φdot = 0) :
    paperEnergyDot m φ θ φdot θdot φddot θddot = -u * θdot := by
  simp [paperEnergyDot_both_sourced h, hφdot]

end Gravity

end DstDiophantine
