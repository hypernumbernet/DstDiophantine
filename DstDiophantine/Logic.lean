import DstDiophantine.Logic.TruthValue
import DstDiophantine.Logic.DiscreteN4
import DstDiophantine.Logic.Potential
import DstDiophantine.Logic.Connective
import DstDiophantine.Logic.Interpretation
import DstDiophantine.Logic.Amplitude
import DstDiophantine.Logic.Order
import DstDiophantine.Logic.Geometric
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.RotorClass

/-!
# Scale-dependent 4-valued logic (D4L) and PQ4L — parallel track

Semantic layer over the already-proved PGA invariant `JNormalized`.
**Not** re-exported from `DstDiophantine.Basic`, so the Diophantine path
does not depend on these modules (same policy as `DstDiophantine.Gravity`
and `DstDiophantine.CGA`).

## Contents

* `Logic.TruthValue` — four states from `JNormalized ∈ [-1,1]`
* `Logic.DiscreteN4` — 27-world census on the smallest complete clock
* `Logic.Potential` — \(V_\lambda\), large-scale critical points, written-\(U\)
  counterexamples
* `Logic.Connective` — min/max/neg, non-explosion, softmin limits
* `Logic.Interpretation` — usual–dual swap is signed negation
* `Logic.Amplitude` — admissible configuration as PQ4L amplitude
* `Logic.Order` — height and information preorders (not Belnap FOUR)
* `Logic.Geometric` — Killing overlap, bivector commutator, rotor composition

Unconditional FLT / Beal / a Gödel-refutation are **not** claimed.
Hilbert space, Born rule, and orthomodular quantum logic are **not** claimed.
-/

namespace DstDiophantine

namespace Logic

open Invariant Framework Discrete Operations
open _root_.DstDiophantine.Embedding

/-- Regression: every D4L state is realised by an admissible configuration. -/
example (tv : TruthValue) :
    ∃ (p : TorsionParams) (h : Admissible.IsAdmissibleContinuous p), ofParams p h = tv :=
  exists_ofParams tv

/-- Regression: admissible \(N=4\) worlds number 27. -/
example : Fintype.card World = 27 :=
  card_world

example : Fintype.card { t : DiscreteTorsion 4 // IsAdmissible t } = 27 :=
  card_admissible_n4

/-- Regression: state cardinalities on the \(N=4\) clock. -/
example : Fintype.card { w : World // classifyWorld w = .T } = 7 :=
  card_state_T

example : Fintype.card { w : World // classifyWorld w = .U } = 9 :=
  card_state_U

example : Fintype.card { w : World // classifyWorld w = .F } = 1 :=
  card_state_F

example : Fintype.card { w : World // classifyWorld w = .B } = 10 :=
  card_state_B

/-- Regression: landmarks. -/
example :
    ofParams (toTorsionParams (pureHyperbolicDiscrete 4))
      (admissible_continuous_of_discrete _ (pureHyperbolicDiscrete_admissible (by decide))) = .F :=
  classify_pureHyperbolic_n4

example :
    ofParams (toTorsionParams (pureEllipticDiscrete 4))
      (admissible_continuous_of_discrete _ (pureEllipticDiscrete_admissible (by decide))) = .B :=
  classify_pureElliptic_n4

example :
    ofParams (toTorsionParams (zeroTorsion 4))
      (admissible_continuous_of_discrete _ (zero_admissible_zeroHeight 4).1) = .T :=
  classify_zero_n4

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

/-- Regression: paper ODE on \((-1,1)\setminus\{0\}\) flows toward \(0\). -/
example {j : ℝ} (hlo : -1 < j) (hhi : j < 1) (hne : j ≠ 0) :
    paperFlow j * j < 0 :=
  paperFlow_towards_zero hlo hhi hne

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

end Logic

end DstDiophantine
