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

These are algebraic identities on jets \((\phi,\theta,\ddot\phi,\ddot\theta)\).
No derivation of \(m\) from the dual-rotor algebra is claimed.

## Proved

* The Euler–Lagrange equations of the written Lagrangian are
  \(\ddot\phi=-m(\phi-\theta)\) and \(\ddot\theta=-m(\phi-\theta)\).
  The mismatch \(\delta=\phi-\theta\) then satisfies \(\ddot\delta=0\).
* The written (claimed) system makes \(\ddot\delta=2m\delta\), which is
  not the harmonic oscillator \(\ddot\delta+m\delta=0\).
* The same-sign kinetic model
  \(L=\tfrac12\dot\phi^2+\tfrac12\dot\theta^2-\tfrac m2(\phi-\theta)^2\)
  yields \(\ddot\delta+2m\delta=0\). This is an explicit working model,
  not the written action.
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

/-- The written action makes the mismatch free: \(\ddot\phi-\ddot\theta=0\). -/
theorem paperActualEL_free_mismatch {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    φddot - θddot = 0 := by
  rcases (paperActualEL_eq m φ θ φddot θddot).mp h with ⟨hφ, hθ⟩
  linarith

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

/-- The working model yields \(\ddot\delta+2m\delta=0\). -/
theorem oscillatorEL_harmonic {m φ θ φddot θddot : ℝ}
    (h : OscillatorEL m φ θ φddot θddot) :
    (φddot - θddot) + 2 * m * (φ - θ) = 0 := by
  rcases (oscillatorEL_eq m φ θ φddot θddot).mp h with ⟨hφ, hθ⟩
  linarith

end Gravity

end DstDiophantine
