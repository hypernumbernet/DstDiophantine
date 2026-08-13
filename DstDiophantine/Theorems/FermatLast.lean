import Mathlib.NumberTheory.FLT.Basic

/-!
# Fermat's Last Theorem as an axiom (phase 7i)

mathlib (v4.34) proves FLT for exponents 3 and 4, but not the full theorem.
We take Wiles's classical statement as an `axiom` (same contract as
`mihailescu`), not as a Lean proof of FLT.

Beal's exponent-gcd reduction uses this for the `d ≥ 3` slice. The modular
bridge route (`FermatLastTheorem_of_modular_bridge`) remains available as a
hypothesis-based alternative.
-/

namespace DstDiophantine

namespace Theorems

/--
Fermat's Last Theorem (Wiles, 1995).

Not fully formalised in mathlib at the pin used by this project; recorded
explicitly as an axiom rather than smuggled into a `sorry`. This is **not** an
unconditional Lean proof of FLT.
-/
axiom fermatLastTheorem : FermatLastTheorem

end Theorems

end DstDiophantine
