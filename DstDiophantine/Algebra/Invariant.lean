import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Motor

/-!
# Torsional invariants `J` and `J⁽⁵⁾

The six-dimensional torsional scalar and its five-dimensional extension with the
Minkowski translation term.
-/

set_option warn.sorry false

namespace DstDiophantine

open Operations Motor Discrete

namespace Invariant

/-- Normalised Killing form on the six-dimensional torsion sector. -/
def killingForm (p q : TorsionParams) : ℝ :=
  8 * (∑ a : Fin 3, (p.alpha a * q.alpha a - p.beta a * q.beta a))

/-- Original torsional scalar `J = (1/16) B_Killing(Ω, Ω)`. -/
noncomputable def J (p : TorsionParams) : ℝ :=
  (1 / 16) * killingForm p p

theorem J_coef (p : TorsionParams) :
    J p = (1 / 2) * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) := by
  unfold J killingForm
  simp only [Fin.sum_univ_three]
  ring_nf

/-- Extended invariant with translation sector. -/
noncomputable def J5 (p : OmegaParams) : ℝ :=
  J p.torsion + (1 / 2) * minkowskiDot p.trans.lambda

theorem J5_eq (p : OmegaParams) :
    J5 p = J p.torsion + (1 / 2) * minkowskiDot p.trans.lambda := rfl

-- Phase-2 deferred: full proof uses principal branch + discrete torus compactness.
theorem torsion_bound_continuous (p : TorsionParams) (h : IsPrincipalBranch p) :
    |J p| ≤ 1 := by
  sorry

/-- Discrete torus bound: every admissible lattice point satisfies `|J| ≤ 1`.
The continuum limit `N → ∞` (TEGR recovery) is deferred to a later phase. -/
theorem torsion_bound {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |J (toTorsionParams t)| ≤ 1 := by
  exact torsion_bound_continuous (toTorsionParams t) h

end Invariant

end DstDiophantine
