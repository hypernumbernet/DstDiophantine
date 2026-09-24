import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rotor rigidity for a mismatch potential

The written action uses one potential, the harmonic stiffness `(m/2) δ²`.
The Euler–Lagrange jets below keep that stiffness as the special case
`slope = m δ`, and compare it with a general slope `V'(δ)` and with the
quartic
`V(δ) = (λ/4) (δ² - v²)²`.

Opposite kinetic signs make `δ̈ = 0` for every slope, and source the common
rapidity by `σ̈ = -2 V'(δ)`. A frozen lag is then inertial if and only if
the slope vanishes. The harmonic stiffness vanishes only at alignment, so
a nonzero constant lag accelerates `σ`.

Same-sign kinetics free `σ` for every slope and set `δ̈ = -2 V'(δ)`.
Constant lag is again the critical set of `V`, but the slope now restores.
The quartic, for `λ > 0`, is minimized at `δ = ±v` and is strictly higher
at the symmetric point `δ = 0`. Inside the interval the same-sign force
points away from the origin. The radial curvature there is `4 λ v²`, which
is not identically a prescribed Compton value `m²`, and the common rate is
not fixed by `(λ, v)`.

No electroweak vacuum, Weinberg angle, or `W`/`Z` mass is claimed.
-/

namespace DstDiophantine

namespace Gravity

/-! ### Jets at a given slope of `V` -/

/-- Opposite-sign Euler–Lagrange jet for an arbitrary mismatch slope. -/
def OppositePotentialEL (slope φddot θddot : ℝ) : Prop :=
  φddot = -slope ∧ θddot = -slope

/-- Same-sign Euler–Lagrange jet for an arbitrary mismatch slope. -/
def SameSignPotentialEL (slope φddot θddot : ℝ) : Prop :=
  φddot = -slope ∧ θddot = slope

theorem opposite_free_mismatch {slope φddot θddot : ℝ}
    (h : OppositePotentialEL slope φddot θddot) :
    φddot - θddot = 0 := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem opposite_common {slope φddot θddot : ℝ}
    (h : OppositePotentialEL slope φddot θddot) :
    φddot + θddot = -2 * slope := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem opposite_rigid_iff (slope : ℝ) :
    OppositePotentialEL slope 0 0 ↔ slope = 0 := by
  constructor
  · intro h
    have := opposite_common h
    linarith
  · intro h
    simp [OppositePotentialEL, h]

theorem sameSign_mismatch {slope φddot θddot : ℝ}
    (h : SameSignPotentialEL slope φddot θddot) :
    φddot - θddot = -2 * slope := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem sameSign_free_common {slope φddot θddot : ℝ}
    (h : SameSignPotentialEL slope φddot θddot) :
    φddot + θddot = 0 := by
  rcases h with ⟨hφ, hθ⟩
  linarith

theorem sameSign_rigid_iff (slope : ℝ) :
    SameSignPotentialEL slope 0 0 ↔ slope = 0 := by
  constructor
  · intro h
    have := sameSign_mismatch h
    linarith
  · intro h
    simp [SameSignPotentialEL, h]

/-- Formal power of the opposite-sign Jacobi integral. -/
def oppositePotentialDot (φdot θdot φddot θddot slope : ℝ) : ℝ :=
  φdot * φddot - θdot * θddot + slope * (φdot - θdot)

/-- Formal power of the same-sign Jacobi integral. -/
def sameSignPotentialDot (φdot θdot φddot θddot slope : ℝ) : ℝ :=
  φdot * φddot + θdot * θddot + slope * (φdot - θdot)

theorem oppositePotentialDot_conserved {slope φdot θdot φddot θddot : ℝ}
    (h : OppositePotentialEL slope φddot θddot) :
    oppositePotentialDot φdot θdot φddot θddot slope = 0 := by
  rcases h with ⟨hφ, hθ⟩
  simp [oppositePotentialDot, hφ, hθ]
  ring

theorem sameSignPotentialDot_conserved {slope φdot θdot φddot θddot : ℝ}
    (h : SameSignPotentialEL slope φddot θddot) :
    sameSignPotentialDot φdot θdot φddot θddot slope = 0 := by
  rcases h with ⟨hφ, hθ⟩
  simp [sameSignPotentialDot, hφ, hθ]
  ring

/-! ### Harmonic stiffness -/

theorem harmonic_critical {m δ : ℝ} (hm : m ≠ 0) : m * δ = 0 ↔ δ = 0 := by
  simp [hm]

/-- A nonzero harmonic lag is not an inertial common rapidity. -/
theorem opposite_harmonic_inertial_iff {m δ φddot θddot : ℝ}
    (h : OppositePotentialEL (m * δ) φddot θddot) :
    φddot + θddot = 0 ↔ m * δ = 0 := by
  have hσ := opposite_common h
  constructor <;> intro h0 <;> linarith

/-- Same-sign harmonic rigidity is alignment, once the rest mass is nonzero. -/
theorem sameSign_harmonic_rigid_iff {m δ : ℝ} (hm : m ≠ 0) :
    SameSignPotentialEL (m * δ) 0 0 ↔ δ = 0 := by
  rw [sameSign_rigid_iff, harmonic_critical hm]

/-! ### Quartic mismatch potential -/

/-- `V(δ) = (λ/4) (δ² - v²)²`. -/
noncomputable def quarticPotential (lam v δ : ℝ) : ℝ :=
  (lam / 4) * (δ ^ 2 - v ^ 2) ^ 2

/-- Slope `V'(δ) = λ δ (δ² - v²)`. -/
noncomputable def quarticSlope (lam v δ : ℝ) : ℝ :=
  lam * δ * (δ ^ 2 - v ^ 2)

/-- Radial curvature `ω² = 4 λ v²` at either nonzero well. -/
noncomputable def radialFreqSq (lam v : ℝ) : ℝ :=
  4 * lam * v ^ 2

theorem quarticSlope_eq_zero {lam v δ : ℝ} (hl : lam ≠ 0) :
    quarticSlope lam v δ = 0 ↔ δ = 0 ∨ δ = v ∨ δ = -v := by
  unfold quarticSlope
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hlamδ | hsq
    · rcases mul_eq_zero.mp hlamδ with hlam | hδ
      · exact absurd hlam hl
      · exact Or.inl hδ
    · have hsq' : δ ^ 2 = v ^ 2 := sub_eq_zero.mp hsq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rintro (h | h | h) <;> simp [h, sub_self, zero_mul, mul_zero]

theorem quarticPotential_vacuum (lam v : ℝ) : quarticPotential lam v v = 0 := by
  unfold quarticPotential
  ring

theorem quarticPotential_symmetric (lam v : ℝ) :
    quarticPotential lam v 0 = (lam / 4) * v ^ 4 := by
  unfold quarticPotential
  ring

theorem quarticPotential_ge_vacuum {lam v δ : ℝ} (hl : 0 ≤ lam) :
    quarticPotential lam v v ≤ quarticPotential lam v δ := by
  rw [quarticPotential_vacuum]
  unfold quarticPotential
  have hsq : 0 ≤ (δ ^ 2 - v ^ 2) ^ 2 := sq_nonneg _
  nlinarith

theorem symmetric_point_above {lam v : ℝ} (hl : 0 < lam) (hv : v ≠ 0) :
    quarticPotential lam v v < quarticPotential lam v 0 := by
  rw [quarticPotential_vacuum, quarticPotential_symmetric]
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hv4 : 0 < v ^ 4 := by nlinarith
  nlinarith

theorem quartic_vacuum_sameSign (lam v : ℝ) :
    SameSignPotentialEL (quarticSlope lam v v) 0 0 := by
  have h : quarticSlope lam v v = 0 := by
    unfold quarticSlope
    ring
  simp [SameSignPotentialEL, h]

theorem quartic_vacuum_opposite (lam v : ℝ) :
    OppositePotentialEL (quarticSlope lam v v) 0 0 := by
  have h : quarticSlope lam v v = 0 := by
    unfold quarticSlope
    ring
  simp [OppositePotentialEL, h]

/-- Inside the wells the same-sign force has the sign of `δ`. -/
theorem sameSign_repels_origin {lam v δ φddot θddot : ℝ}
    (hl : 0 < lam) (hδ : δ ≠ 0) (hinside : δ ^ 2 < v ^ 2)
    (h : SameSignPotentialEL (quarticSlope lam v δ) φddot θddot) :
    0 < (φddot - θddot) * δ := by
  have hmul : (φddot - θddot) * δ = -2 * lam * δ ^ 2 * (δ ^ 2 - v ^ 2) := by
    rw [sameSign_mismatch h]
    unfold quarticSlope
    ring
  rw [hmul]
  have hsq : 0 < δ ^ 2 := sq_pos_of_ne_zero hδ
  have hpos : 0 < lam * δ ^ 2 * (v ^ 2 - δ ^ 2) :=
    mul_pos (mul_pos hl hsq) (by linarith)
  linarith

theorem quarticSlope_linearization (lam v ε : ℝ) :
    quarticSlope lam v (v + ε) - 2 * lam * v ^ 2 * ε =
      lam * (3 * v * ε ^ 2 + ε ^ 3) := by
  unfold quarticSlope
  ring

/-- The curvature `4 λ v²` is not a prescribed Compton value. -/
theorem radial_not_identically_compton :
    ∃ lam v m : ℝ, 0 < lam ∧ v ≠ 0 ∧ 0 < m ∧ radialFreqSq lam v ≠ m ^ 2 := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold radialFreqSq
  norm_num

/-- Curvature and a Compton value can be matched by a choice of well. -/
theorem radial_meets_compton :
    ∃ lam v m : ℝ, 0 < lam ∧ v ≠ 0 ∧ 0 < m ∧ radialFreqSq lam v = m ^ 2 := by
  refine ⟨1, 1, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold radialFreqSq
  norm_num

end Gravity

end DstDiophantine
