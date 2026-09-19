import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Dual-rotor particle action: Euler–Lagrange identities

The main paper writes the particle-intrinsic action
\[
S=\int\Bigl(\tfrac12\sum_a\dot\phi_a^2-\tfrac12\sum_a\dot\theta_a^2
-\tfrac m2\sum_a(\phi_a-\theta_a)^2\Bigr)\,dt
\]
and claims the Euler–Lagrange system
\(\ddot\phi=m(\phi-\theta)\), \(-\ddot\theta=m(\phi-\theta)\), hence
\(\ddot{\delta\phi}+m\,\delta\phi=0\).

These are algebraic identities on jets
\((\phi,\theta,\dot\phi,\dot\theta,\ddot\phi,\ddot\theta)\).
No derivation of \(m\) from the dual-rotor algebra is claimed.
The de Broglie reading of free lag, and any identification of
\(J_{\mathrm{osc}}\) with the Weitzenböck density, remain out of scope.

## Proved

* The Euler–Lagrange equations of the written Lagrangian are
  \(\ddot\phi=-m(\phi-\theta)\) and \(\ddot\theta=-m(\phi-\theta)\).
  In the sum and difference \(\sigma=\phi+\theta\), \(\delta=\phi-\theta\),
  the density is \(\tfrac12\dot\sigma\dot\delta-\tfrac m2\delta^2\).
  The mismatch is free, \(\ddot\delta=0\), while the potential sources the
  common channel, \(\ddot\sigma=-2m\delta\).
* The Jacobi integral
  \(E=\tfrac12\dot\phi^2-\tfrac12\dot\theta^2+\tfrac m2\delta^2\)
  is conserved on that jet and is indefinite.
* The written (claimed) system makes \(\ddot\delta=2m\delta\) with a free
  common mode, and is not the harmonic oscillator \(\ddot\delta+m\delta=0\).
* The same-sign kinetic model
  \(L=\tfrac12\dot\phi^2+\tfrac12\dot\theta^2-\tfrac m2(\phi-\theta)^2\)
  yields \(\ddot\delta+2m\delta=0\) with \(\ddot\sigma=0\).
  Its energy is conserved and nonnegative for \(m\ge 0\).
  This is an explicit working model, not the written action.
* A dual-channel generalised acceleration \(u\) on the written action
  yields \(\ddot\delta=-u\) and \(\ddot\sigma=-2m\delta+u\): the mismatch
  is a double integrator, with no restoring frequency. The same \(u\) on
  the working oscillator yields \(\ddot\delta+2m\delta=-u\) and
  \(\ddot\sigma=u\). A constant drive shifts the equilibrium mismatch;
  it is not derived from Faraday helicity.
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

/-- Opposite kinetic signs are the mixed term \(\tfrac12\dot\sigma\dot\delta\). -/
theorem paperLagrangian_eq_mixed (m φ θ φdot θdot : ℝ) :
    paperLagrangian m φ θ φdot θdot =
      (1 / 2) * (φdot + θdot) * (φdot - θdot) - (m / 2) * (φ - θ) ^ 2 := by
  unfold paperLagrangian
  ring

/-- Written Euler–Lagrange is a free mismatch and a sourced common channel. -/
theorem paperActualEL_iff_channels (m φ θ φddot θddot : ℝ) :
    PaperActualEL m φ θ φddot θddot ↔
      φddot - θddot = 0 ∧ φddot + θddot = -2 * m * (φ - θ) := by
  rw [paperActualEL_eq]
  constructor
  · intro ⟨hφ, hθ⟩
    constructor <;> linarith
  · intro ⟨hδ, hσ⟩
    constructor <;> linarith

/-- The written action makes the mismatch free: \(\ddot\phi-\ddot\theta=0\). -/
theorem paperActualEL_free_mismatch {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    φddot - θddot = 0 :=
  (paperActualEL_iff_channels m φ θ φddot θddot).mp h |>.1

/-- The potential sources the common channel: \(\ddot\sigma=-2m\delta\). -/
theorem paperActualEL_common_driven {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    φddot + θddot = -2 * m * (φ - θ) :=
  (paperActualEL_iff_channels m φ θ φddot θddot).mp h |>.2

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

/-- The written Jacobi integral is conserved on the Euler–Lagrange jet. -/
theorem paperEnergy_conserved {m φ θ φdot θdot φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    paperEnergyDot m φ θ φdot θdot φddot θddot = 0 := by
  rcases (paperActualEL_eq m φ θ φddot θddot).mp h with ⟨hφ, hθ⟩
  simp [paperEnergyDot, hφ, hθ]
  ring

/-- Mixed kinetics make the written Jacobi integral indefinite. -/
theorem paperEnergy_indefinite :
    (∃ m φ θ φdot θdot : ℝ, 0 < paperEnergy m φ θ φdot θdot) ∧
      (∃ m φ θ φdot θdot : ℝ, paperEnergy m φ θ φdot θdot < 0) :=
  ⟨⟨1, 1, 0, 0, 0, by unfold paperEnergy; norm_num⟩,
    ⟨1, 0, 0, 0, 1, by unfold paperEnergy; norm_num⟩⟩

/-- The written action does not yield the claimed oscillator \(\ddot\delta+m\delta=0\). -/
theorem paperActualEL_not_oscillator :
    ∃ m φ θ φddot θddot : ℝ,
      PaperActualEL m φ θ φddot θddot ∧
        φddot - θddot ≠ -m * (φ - θ) := by
  refine ⟨1, 1, 0, -1, -1, ?_, ?_⟩
  · exact (paperActualEL_eq 1 1 0 (-1) (-1)).mpr ⟨by norm_num, by norm_num⟩
  · norm_num

/-! ### Claimed Euler–Lagrange system of the paper -/

/-- The system written in the paper, not the Euler–Lagrange equations of its Lagrangian. -/
def PaperClaimedEL (m φ θ φddot θddot : ℝ) : Prop :=
  φddot = m * (φ - θ) ∧ -θddot = m * (φ - θ)

/-- The claimed system makes the mismatch runaway: \(\ddot\delta=2m\delta\). -/
theorem paperClaimedEL_runaway {m φ θ φddot θddot : ℝ}
    (h : PaperClaimedEL m φ θ φddot θddot) :
    φddot - θddot = 2 * m * (φ - θ) := by
  rcases h with ⟨hφ, hθ⟩
  linarith

/-- On the claimed system the common mode is free: \(\ddot\sigma=0\). -/
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

/-- Same-sign kinetics split as \(\tfrac14\dot\sigma^2+\tfrac14\dot\delta^2\). -/
theorem oscillatorLagrangian_eq_split (m φ θ φdot θdot : ℝ) :
    oscillatorLagrangian m φ θ φdot θdot =
      (1 / 4) * (φdot + θdot) ^ 2 + (1 / 4) * (φdot - θdot) ^ 2 -
        (m / 2) * (φ - θ) ^ 2 := by
  unfold oscillatorLagrangian
  ring

/-- The working model yields \(\ddot\delta+2m\delta=0\). -/
theorem oscillatorEL_harmonic {m φ θ φddot θddot : ℝ}
    (h : OscillatorEL m φ θ φddot θddot) :
    (φddot - θddot) + 2 * m * (φ - θ) = 0 := by
  rcases (oscillatorEL_eq m φ θ φddot θddot).mp h with ⟨hφ, hθ⟩
  linarith

/-- On the working model the common mode is free: \(\ddot\sigma=0\). -/
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
No identification \(u\propto\sigma E_0^2\) is claimed.
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

/-- On the written action a dual force freely accelerates the mismatch. -/
theorem paperSourcedEL_iff_channels (m φ θ φddot θddot u : ℝ) :
    PaperSourcedEL m φ θ φddot θddot u ↔
      φddot - θddot = -u ∧ φddot + θddot = -2 * m * (φ - θ) + u := by
  constructor
  · intro h
    exact ⟨paperSourcedEL_mismatch h, paperSourcedEL_common h⟩
  · intro ⟨hδ, hσ⟩
    constructor <;> linarith

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

/-- A constant dual drive shifts the mismatch equilibrium of the oscillator. -/
theorem oscillatorSourcedEL_eq_mismatch {m φ θ u : ℝ} (hm : m ≠ 0)
    (h : OscillatorSourcedEL m φ θ 0 0 u) :
    φ - θ = -u / (2 * m) := by
  have hδ := oscillatorSourcedEL_mismatch h
  have h2 : (2 : ℝ) * m ≠ 0 := mul_ne_zero two_ne_zero hm
  exact (eq_div_iff h2).mpr (by linarith)

end Gravity

end DstDiophantine
