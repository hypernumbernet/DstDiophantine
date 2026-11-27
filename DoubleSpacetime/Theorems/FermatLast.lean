import Mathlib.NumberTheory.FLT.Basic

/-!
# Fermat's Last Theorem as an axiom

`fermatLastTheorem` assumes Wiles's statement. It is an axiom, not a Lean proof of FLT.
-/

namespace DoubleSpacetime

namespace Theorems

/-- Wiles's FLT, assumed as an axiom. Not a Lean proof of FLT. -/
axiom fermatLastTheorem : FermatLastTheorem

end Theorems

end DoubleSpacetime
