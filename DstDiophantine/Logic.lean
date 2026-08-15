import DstDiophantine.Logic.TruthValue
import DstDiophantine.Logic.Potential
import DstDiophantine.Logic.Connective
import DstDiophantine.Logic.Interpretation
import DstDiophantine.Logic.Amplitude
import DstDiophantine.Logic.Order
import DstDiophantine.Logic.Geometric
import DstDiophantine.Logic.Quantum.Separation
import DstDiophantine.Logic.Quantum.DualSector
import DstDiophantine.Logic.Quantum.Quaternion
import DstDiophantine.Logic.Quantum.Spinor
import DstDiophantine.Logic.Quantum.QuantumLogic
import DstDiophantine.Logic.Quantum.Dictionary
import DstDiophantine.Algebra.Invariant

/-!
# Dual Spacetime 4-valued logic (D4L) — parallel track

The project's logic. A proposition is an admissible torsion configuration.
Measurement is the already-proved PGA invariant `JNormalized`; collapse
yields four labels. Scalar connectives and geometric operations are two
faces of the same system.

**Not** re-exported from `DstDiophantine.Basic`, so the Diophantine path
does not depend on these modules (same policy as `DstDiophantine.Gravity`
and `DstDiophantine.CGA`).

## Contents

* `Logic.Amplitude` — admissible configuration as the primary carrier
* `Logic.TruthValue` — four states from `JNormalized ∈ [-1,1]`
* `Logic.Connective` — min/max/neg, non-explosion, softmin limits
* `Logic.Interpretation` — usual–dual swap is signed negation
* `Logic.Order` — height and information preorders (not Belnap FOUR)
* `Logic.Geometric` — Killing overlap, bivector commutator, rotor composition
* `Logic.Potential` — \(V_\lambda\), large-scale critical points, written-\(U\)
* `Logic.Quantum` — sibling Hilbert / quantum-logic layer (not D4L itself)

Unconditional FLT / Beal / a Gödel-refutation are **not** claimed.
D4L is **not** a Hilbert space, a Born rule, or an orthomodular lattice.
The dual-sector kinematics `DualSpinor ≃ ℂ²` and its subspace lattice are
a sibling construction; see `Logic.Quantum.Separation` and
`Logic.Quantum.Dictionary`.
-/

namespace DstDiophantine

namespace Logic

open Invariant Operations Generators Submodule

/-- Regression: every D4L state is realised by an admissible configuration. -/
example (tv : TruthValue) :
    ∃ (p : TorsionParams) (h : Admissible.IsAdmissibleContinuous p), ofParams p h = tv :=
  exists_ofParams tv

/-- Regression: dual-swap flips `JNormalized`. -/
example (p : TorsionParams) : JNormalized (daggerParams p) = -JNormalized p :=
  JNormalized_dagger p

/-- Regression: conjunction with negation never saturates `F`. -/
example {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem (conjJ j (negJ j)) (abs_conj_neg_le hj) ≠ .F :=
  classify_conj_neg_ne_F hj

/-- Regression: \(V_\infty\) is stable at \(0,\pm 1\) and unstable at \(\pm 1/2\). -/
example : (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (0 : ℝ)) > 0 :=
  VInf_second_pos_at_zero

example : (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (1 : ℝ)) > 0 :=
  VInf_second_pos_at_one

example : (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (-1 : ℝ)) > 0 :=
  VInf_second_pos_at_neg_one

example : (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (1 / 2 : ℝ)) < 0 :=
  VInf_second_neg_at_half

example : (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (-(1 / 2) : ℝ)) < 0 :=
  VInf_second_neg_at_neg_half

/-- Regression: written \(U\) never destroys the \(B\) well. -/
example (lam α : ℝ) (hlam : 0 < lam) :
    VPiece lam α (-1) = VInf (-1) ∧
      0 < (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (-1 : ℝ)) :=
  written_U_no_critical_scale lam α hlam

/-- Regression: the two written \(U\) disagree by a factor of two on \(\{J>0\}\). -/
example {j : ℝ} (h : 0 < j) : USmooth j = 2 * UPiece j :=
  USmooth_eq_two_UPiece_of_pos h

/-- Regression: large-scale potential recovers \(V_\infty\). -/
example (U : ℝ → ℝ) (α j : ℝ) :
    Filter.Tendsto (fun lam : ℝ => V U lam α j) Filter.atTop (nhds (VInf j)) :=
  tendsto_V_atTop U α j

/-- Regression: softmin recovers \(\min\) at infinite inverse temperature. -/
example (a b : ℝ) :
    Filter.Tendsto (fun β : ℝ => softmin β a b) Filter.atTop (nhds (min a b)) :=
  tendsto_softmin_atTop a b

/-- Regression: every label is realised by an amplitude. -/
example (tv : TruthValue) : ∃ a : Amplitude, a.collapse = tv :=
  exists_amplitude tv

/-- Regression: adjoint is involutive and flips the observable. -/
example (a : Amplitude) : a.adjoint.adjoint = a :=
  a.adjoint_involutive

example (a : Amplitude) : a.adjoint.measure = -a.measure :=
  a.measure_adjoint

/-- Regression: information bottom is `T`; tops are the walls `±1`. -/
example {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .T ↔ ∀ k : ℝ, |k| ≤ 1 → InfoLE j k :=
  classify_T_iff_info_bottom hj

example {j : ℝ} (hj : |j| ≤ 1) :
    (∀ k : ℝ, |k| ≤ 1 → InfoLE k j) ↔ j = 1 ∨ j = -1 :=
  info_top_iff hj

/-- Regression: Killing overlap is symmetric; self-overlap is `16 J`. -/
example (p q : TorsionParams) : overlap p q = overlap q p :=
  overlap_symm p q

example (p : TorsionParams) : overlap p p = 16 * J p :=
  overlap_self p

/-- Regression: distinct-axis torsion bivectors need not commute. -/
example : interfere axis0Boost axis1Rotation ≠ 0 :=
  interfere_axis0_axis1_ne_zero

/-- Regression: state-level negation is not a function of the four labels. -/
example :
    ∃ j₁ j₂ : ℝ, ∃ h₁ : |j₁| ≤ 1, ∃ h₂ : |j₂| ≤ 1,
      classifyOfMem j₁ h₁ = .B ∧ classifyOfMem j₂ h₂ = .B ∧
        classifyOfMem (negJ j₁) (by simpa [negJ, abs_neg] using h₁) ≠
          classifyOfMem (negJ j₂) (by simpa [negJ, abs_neg] using h₂) :=
  neg_not_a_function_of_TruthValue

/-- Regression: Killing form is indefinite, hence not a Hilbert inner product. -/
example :
    (∃ p : TorsionParams, 0 < killingForm p p) ∧
      (∃ q : TorsionParams, killingForm q q < 0) :=
  killingForm_indefinite

/-- Regression: self-overlap is not a Born probability. -/
example : ¬ ∀ p : TorsionParams, 0 ≤ overlap p p :=
  overlap_self_not_born_probability

/-- Regression: dual-sector cyclic generators satisfy `I J = K`. -/
example : cyclic 0 * cyclic 1 = cyclic 2 :=
  cyclic_zero_mul_one

/-- Regression: dual-sector pairing is negative definite. -/
example {β : DualRapidity} (h : killingForm (ofDual β) (ofDual β) = 0) : β = 0 :=
  killingForm_ofDual_neg_def h

/-- Regression: `ℂ²` subspace lattice is orthomodular and not distributive. -/
example {A B : QProp} (h : A ≤ B) : A ⊔ Aᗮ ⊓ B = B :=
  orthomodular h

example :
    (lineE0 ⊓ (lineE1 ⊔ lineD) : QProp) ≠
      ((lineE0 ⊓ lineE1) ⊔ (lineE0 ⊓ lineD) : QProp) :=
  not_distributive

/-- Regression: four D4L labels are not four orthogonal rays in `ℂ²`. -/
example :
    ¬ ∃ L : TruthValue → QProp,
        (∀ tv, Module.finrank ℂ (L tv) = 1) ∧
          (∀ tv₁ tv₂, tv₁ ≠ tv₂ → L tv₁ ⟂ L tv₂) :=
  four_labels_not_orthogonal_pvm

end Logic

end DstDiophantine
