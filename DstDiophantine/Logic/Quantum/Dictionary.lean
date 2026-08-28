import DstDiophantine.Logic.Quantum.QuantumLogic
import DstDiophantine.Logic.Quantum.Separation
import DstDiophantine.Logic.Amplitude
import DstDiophantine.Logic.Geometric
import DstDiophantine.Logic.Interpretation
import Mathlib.Tactic.Linarith

/-!
# Dictionary between the D4L amplitude layer and the dual Hilbert layer

Maps are explicit and one-way. None of them is a lattice isomorphism,
a Born rule, or a Hilbert-space adjoint.
-/

namespace DstDiophantine

namespace Logic

open Invariant Operations Submodule Module

/-- Dual rapidity of a dual-sector amplitude. -/
def Amplitude.dualRapidity (a : Amplitude) (_h : IsDualSector a.params) : DualRapidity :=
  WithLp.toLp 2 a.params.beta

/-- Matrix rotor attached to a dual-sector amplitude. -/
noncomputable def Amplitude.dualMat (a : Amplitude) (h : IsDualSector a.params) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  dualRotorMat (a.dualRapidity h)

/-- Usual–dual swap sends a dual-sector configuration out of the dual sector
whenever the dual rapidity is nonzero. It is not the Hilbert-space adjoint. -/
theorem dagger_leaves_dual_sector {p : TorsionParams}
    (_hd : IsDualSector p) (hn : ¬ IsUsualSector p) :
    ¬ IsDualSector (daggerParams p) := by
  intro h
  -- dagger swaps α and β; dual sector has α = 0, so dagger has β = 0 (usual)
  have : IsUsualSector p := by
    intro a
    have := h a
    -- daggerParams p .alpha a = p.beta a = 0
    simpa [daggerParams] using this
  exact hn this

/-- Killing self-overlap is a multiple of `J`, not a spinor Born probability. -/
theorem overlap_ne_spinor_born :
    ∃ p : TorsionParams, overlap p p < 0 :=
  overlap_self_can_be_neg

/-- Four D4L labels cannot be four pairwise orthogonal lines in `ℂ²`. -/
theorem four_labels_not_orthogonal_pvm :
    ¬ ∃ L : TruthValue → QProp,
        (∀ tv, finrank ℂ (L tv) = 1) ∧
          (∀ tv₁ tv₂, tv₁ ≠ tv₂ → L tv₁ ⟂ L tv₂) := by
  rintro ⟨L, hdim, horth⟩
  exact no_three_pairwise_orthogonal_lines
    (hdim .T) (hdim .U) (hdim .F)
    (horth .T .U (by decide))
    (horth .T .F (by decide))
    (horth .U .F (by decide))

/-- Scalar `min`/`max` distribute; the subspace lattice of `ℂ²` does not.
Hence there is no lattice isomorphism carrying one to the other. -/
theorem scalar_lattice_not_iso_qprop :
    (∀ a b c : ℝ, conjJ a (disjJ b c) = disjJ (conjJ a b) (conjJ a c)) ∧
      lineE0 ⊓ (lineE1 ⊔ lineD) ≠ (lineE0 ⊓ lineE1) ⊔ (lineE0 ⊓ lineD) :=
  ⟨scalar_connectives_distributive, not_distributive⟩

/-- Same-axis interference vanishes (already proved). Compatibility of the
corresponding dual generators is a necessary condition only; the converse
is not claimed. -/
theorem same_axis_compatible (α β : ℝ) :
    interfere
        ⟨fun a => if a = 0 then α else 0, fun _ => 0⟩
        ⟨fun _ => 0, fun a => if a = 0 then β else 0⟩ = 0 :=
  interfere_axis0_self α β

end Logic

end DstDiophantine
