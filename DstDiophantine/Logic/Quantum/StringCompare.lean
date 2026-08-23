/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Algebra.Cl91
import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.UnitGroup
import DstDiophantine.Logic.Quantum.Spinor10
import DstDiophantine.Logic.Quantum.StringSpectrum
import DstDiophantine.Logic.Quantum.LevelMatch
import DstDiophantine.Logic.Quantum.MinimalIdeal

/-!
# DST versus textbook 10D string kinematics — separation theorems

Same style as `Logic.Quantum.Separation` / `Dictionary`: record numerical
coincidences, reject false identifications, and leave Standard-Model
emergence as an open modelling claim (not a theorem).
-/

namespace DstDiophantine

namespace Logic

open Cl91 StringSpectrum LorentzDim Module UnitGroup

/-- `Cl(3,1)` and `Cl(9,1)` are not isomorphic. -/
theorem not_cl31_algEquiv_cl91 : ¬ Nonempty (Cl31 ≃ₐ[ℝ] Cl91) :=
  not_algEquiv_cl31

/-- Dual spinor `ℂ²` is not the Majorana–Weyl 16. -/
theorem dualSpinor_ne_majoranaWeyl :
    finrank ℂ DualSpinor ≠ finrank ℝ MajoranaWeyl10 :=
  dualSpinor_finrank_ne_majorana

/-- Super-Poincaré N=1 generator count ≠ PGA 10 generators. -/
theorem superPoincare_ne_pga :
    superPoincareN1Dim ≠ pgaGeneratorCount :=
  superPoincareN1_ne_pgaGenerators

/-- Lorentz algebras differ in dimension. -/
theorem so31_ne_so91 : so31Dim ≠ so91Dim :=
  so31Dim_ne_so91Dim

/-- Paper pseudoscalar chirality formula is not idempotent. -/
theorem paper_chirality_rejected :
    paperChiralityL * paperChiralityL ≠ paperChiralityL :=
  paperChiralityL_not_idempotent

/-- Dual map `X ↦ X·i` is right multiplication by the even-grade pseudoscalar;
it is not a Super-Poincaré odd generator. -/
theorem dual_eq_mul_pseudoscalar (x : PGA) :
    Operations.dual x = x * Operations.pseudoscalar :=
  rfl

/-- Discrete rotor image is finite; this is **not** a generation count. -/
theorem discreteRotorImage_finite_not_generations {N : ℕ} [NeZero N] :
    (DiscreteRotorImage N).Finite :=
  discreteRotorImage_finite

/-- Level-matched balanced ray exists (dictionary witness). -/
theorem exists_levelMatched_balanced :
    ∃ p : Operations.TorsionParams, IsLevelMatched p :=
  ⟨Invariant.balancedRay 1, isLevelMatched_balancedRay 1⟩

/-- MW real 16 matches `WeylSU4` real 16 (dimensional reduction label). -/
theorem majorana_dim_eq_weylSU4_real :
    finrank ℝ MajoranaWeyl10 = finrank ℝ WeylSU4 :=
  majoranaWeyl10_finrank.trans weylSU4_finrank_real.symm

end Logic

end DstDiophantine
