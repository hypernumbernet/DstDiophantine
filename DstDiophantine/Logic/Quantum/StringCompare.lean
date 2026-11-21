import DstDiophantine.Algebra.Cl91
import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.UnitGroup
import DstDiophantine.Logic.Quantum.Spinor10
import DstDiophantine.Logic.Quantum.StringSpectrum
import DstDiophantine.Logic.Quantum.LevelMatch
import DstDiophantine.Logic.Quantum.MinimalIdeal

/-!
# DST versus 10D string kinematics

These theorems record numerical coincidences and reject false identifications. Standard-Model emergence is not a theorem.
-/

namespace DstDiophantine

namespace Logic

open Cl91 StringSpectrum LorentzDim Module UnitGroup

theorem not_cl31_algEquiv_cl91 : ¬ Nonempty (Cl31 ≃ₐ[ℝ] Cl91) :=
  not_algEquiv_cl31

theorem dualSpinor_ne_majoranaWeyl :
    finrank ℂ DualSpinor ≠ finrank ℝ MajoranaWeyl10 :=
  dualSpinor_finrank_ne_majorana

theorem superPoincare_ne_pga :
    superPoincareN1Dim ≠ pgaGeneratorCount :=
  superPoincareN1_ne_pgaGenerators

theorem so31_ne_so91 : so31Dim ≠ so91Dim :=
  so31Dim_ne_so91Dim

theorem paper_chirality_rejected :
    paperChiralityL * paperChiralityL ≠ paperChiralityL :=
  paperChiralityL_not_idempotent

/-- Not a Super-Poincaré odd generator. -/
theorem dual_eq_mul_pseudoscalar (x : PGA) :
    Operations.dual x = x * Operations.pseudoscalar :=
  rfl

/-- Not a generation count. -/
theorem discreteRotorImage_finite_not_generations {N : ℕ} [NeZero N] :
    (DiscreteRotorImage N).Finite :=
  discreteRotorImage_finite

/-- Dictionary witness. -/
theorem exists_levelMatched_balanced :
    ∃ p : Operations.TorsionParams, IsLevelMatched p :=
  ⟨Invariant.balancedRay 1, isLevelMatched_balancedRay 1⟩

/-- Dimensional reduction label. -/
theorem majorana_dim_eq_weylSU4_real :
    finrank ℝ MajoranaWeyl10 = finrank ℝ WeylSU4 :=
  majoranaWeyl10_finrank.trans weylSU4_finrank_real.symm

end Logic

end DstDiophantine
