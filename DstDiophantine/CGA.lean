import DstDiophantine.Embedding.ConformalInteger

/-!
# 1D CGA probe (Conformal Geometric Algebra)

Diagnostic layer investigating the multiplicative / dilation sector that PGA
`G(3,1,1)` does not supply.  **Not** re-exported from `DstDiophantine.Basic`,
so the Diophantine path does not depend on these modules (same policy as
`DstDiophantine.Gravity`).

## Contents

* `Algebra.CGA.QuadraticForm` — `Cl(2,1)` quadratic form
* `Algebra.CGA.NullCone` — null pair `n₀, n∞`, conformal point `X(x)² = 0`,
  point–point pairing, scale-invariant dilation mismatch, `cgaDilation`
* `Embedding.ConformalInteger` — integer null embedding, DST lattice predicates
  `IsCGAIntegerPoint` / `IsCGAPowerLatticePoint` / `IsCGAIntegerDilation`,
  dilation weights, PGA `integerHeight` unboundedness
-/

namespace DstDiophantine

namespace CGA

open CGA1

/-- Regression: null-cone points square to zero. -/
example (x : ℝ) : CGA1.point x * CGA1.point x = 0 :=
  CGA1.point_sq x

/-- Regression: conformal integers lie on the null cone. -/
example (n : ℤ) :
    Embedding.conformalInteger n * Embedding.conformalInteger n = 0 :=
  Embedding.conformalInteger_sq n

/-- Regression: PGA integer-rotor height is not globally bounded. -/
example : ¬ ∃ M : ℝ, ∀ (n : ℤ) (hn : n ≠ 0),
    Embedding.integerHeight n hn ≤ M :=
  Embedding.integerHeight_not_globally_bounded

/-- Regression: point–point polarisation. -/
example (x y : ℝ) :
    CGA1.bilin21 (CGA1.pointVec x) (CGA1.pointVec y) = -((x - y) ^ 2) / 2 :=
  CGA1.bilin21_pointVec_pointVec x y

/-- Regression: balanced dilation mismatch is positive. -/
example (m : ℕ) (hm : 0 < m) :
    0 < CGA1.cgaDilationMismatch (Real.log 2 / (m : ℝ)) :=
  CGA1.cgaDilationMismatch_balanced_pos m hm

/-- Regression: `k`-fold rapidity on the null cone. -/
example (a δ : ℝ) (k : ℕ) :
    CGA1.pointVec (Real.exp ((k : ℝ) * δ) * a) =
      CGA1.pointVec (Real.exp δ ^ k * a) :=
  CGA1.pointVec_exp_nat_mul a δ k

/-- Regression: nonzero integers are CGA lattice points. -/
example {n : ℤ} (hn : n ≠ 0) : Embedding.IsCGAIntegerPoint (n : ℝ) :=
  Embedding.IsCGAIntegerPoint_conformalInteger hn

/-- Regression: `2^{4/3}` is off the integer null lattice. -/
example : ¬ Embedding.IsCGAIntegerPoint ((2 : ℝ) ^ ((4 : ℝ) / 3)) :=
  Embedding.not_isCGAIntegerPoint_two_rpow_four_thirds

/-- Regression: `2^{4/3}` lies on the 3-power lattice (`(2^{4/3})³ = 16`). -/
example : Embedding.IsCGAPowerLatticePoint ((2 : ℝ) ^ ((4 : ℝ) / 3)) 3 :=
  Embedding.isCGAPowerLatticePoint_two_rpow_four_thirds

/-- Regression: integer lattice points are power-lattice points. -/
example {x : ℝ} {m : ℕ} (hx : Embedding.IsCGAIntegerPoint x) (hm : 0 < m) :
    Embedding.IsCGAPowerLatticePoint x m :=
  Embedding.IsCGAIntegerPoint.isCGAPowerLatticePoint hx hm

/-- Regression: integer dilation group acts on the integer null lattice. -/
example {x : ℝ} {n : ℤ} (hx : Embedding.IsCGAIntegerPoint x) (hn : n ≠ 0) :
    Embedding.IsCGAIntegerPoint ((n : ℝ) * x) :=
  Embedding.IsCGAIntegerPoint_cgaDilation hx (Embedding.IsCGAIntegerDilation_int hn)

/-- Regression: unique scale sending α to γ; ratio integer iff divisibility. -/
example {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) :
    CGA1.cgaDilation (γ / α) α = CGA1.pointVec γ :=
  CGA1.cgaDilation_scale_unique hα hγ

example {a c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) :
    Embedding.IsCGAIntegerDilation ((c.natAbs : ℝ) / (a.natAbs : ℝ)) ↔
      a.natAbs ∣ c.natAbs :=
  Embedding.IsCGAIntegerDilation_div_iff ha hc

end CGA

end DstDiophantine
