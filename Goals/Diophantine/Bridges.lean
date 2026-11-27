import DoubleSpacetime.Theorems.Abc
import DoubleSpacetime.Theorems.Collatz
import DoubleSpacetime.Theorems.Goldbach
import DoubleSpacetime.Theorems.Polignac
import DoubleSpacetime.Theorems.Riemann

/-!
# Live Diophantine bridges

A bridge is a target only while the main library treats it as the live path.
-/

namespace Goals.Diophantine

open DoubleSpacetime.Theorems

/-- Open. The continuous bridge is false; this one recovers the classical conjecture. -/
theorem abcModularBridge : AbcModularBridge := by sorry

/-- Open. Equivalent to the classical conjecture (`collatzAdmissibleBridge_iff`). -/
theorem collatzAdmissibleBridge : CollatzAdmissibleBridge := by sorry

/-- Open. Equivalent to the classical conjecture; for `n ≥ 4` the boost already leaves the cone. -/
theorem goldbachAdmissibleBridge : GoldbachAdmissibleBridge := by sorry

/-- Open. Equivalent to Polignac; twin primes are the case `k = 1`. -/
theorem polignacAdmissibleBridge : PolignacAdmissibleBridge := by sorry

/-- Open. The critical-line statement here, not mathlib's `riemannZeta`. -/
theorem riemannAdmissibleBridge : RiemannAdmissibleBridge := by sorry

end Goals.Diophantine
