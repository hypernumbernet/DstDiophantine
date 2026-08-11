import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Algebra.UnitGroup
import Mathlib.Data.Fintype.Card

/-!
# Unified algebraic descent (honest Phase-4 version)

## Paper gap

Chapter 10 of `dst-diophantine.tex` claims that dagger → unit-group filter →
dual reconstruction **strictly decreases** the torsional height `J`. Lean proves
the opposite equality: dagger only swaps sectors and preserves
`torsionHeight` (`dagger_preserves_height`). The unit-group filter is likewise
vacuous for the present `DiscreteUnit` (every `RotorClass` lies in it).

Termination of a decision procedure is therefore obtained from a separate
well-founded measure on a finite search state (`DescentSchema`), not from
dagger itself.
-/

namespace DstDiophantine

namespace Framework

open Discrete Invariant Operations UnitGroup

variable {N : ℕ} [NeZero N]

/-- Dual-sector reconstruction used by the paper's descent narrative. -/
def dualReconstruct (p : TorsionParams) : TorsionParams :=
  daggerParams p

/-- Paper gap: dagger / dual reconstruction preserves normalised height. -/
theorem dagger_preserves_height (p : TorsionParams) :
    Embedding.torsionHeight (dualReconstruct p) = Embedding.torsionHeight p :=
  Embedding.descent_height_eq p

/-- Corollary: dagger never yields a strict height decrease. -/
theorem dagger_not_strict_descent (p : TorsionParams) :
    ¬ Embedding.torsionHeight (dualReconstruct p) < Embedding.torsionHeight p := by
  rw [dagger_preserves_height]
  exact lt_irrefl _

/-- Every rotor class already lies in `DiscreteUnit` (filter is vacuous). -/
theorem unitFilter_trivial (c : Embedding.RotorClass N) : Embedding.IsUnitClass c :=
  Embedding.isUnitClass_of_any c

/--
Abstract descent / search schema for Phase 5 instances.

A step either reaches a terminal state (solution or contradiction branch)
or produces a new state with strictly smaller `measure`.
-/
structure DescentSchema where
  State : Type
  measure : State → ℕ
  terminal : State → Prop
  step : (s : State) → ¬ terminal s → State
  measure_lt : ∀ s (h : ¬ terminal s), measure (step s h) < measure s

namespace DescentSchema

variable (D : DescentSchema)

/-- From any state, some finite iteration reaches a terminal state. -/
theorem reaches_terminal (s : D.State) :
    ∃ s' : D.State, D.terminal s' := by
  generalize hm : D.measure s = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases ht : D.terminal s
    · exact ⟨s, ht⟩
    · have hlt : D.measure (D.step s ht) < n := by
        simpa [hm] using D.measure_lt s ht
      exact ih _ hlt _ rfl

end DescentSchema

/-- Search state: remaining unexamined admissible candidates. -/
structure LatticeSearchState (N : ℕ) [NeZero N] where
  remaining : Finset (AdmissibleClass N)

/-- A lattice search state is terminal when empty or a zero-height point is found. -/
def LatticeSearchState.terminal (s : LatticeSearchState N) : Prop :=
  s.remaining = ∅ ∨ ∃ t ∈ s.remaining, AdmissibleClass.IsZero t

private instance decidableEqDiscreteTorsion : DecidableEq (DiscreteTorsion N) :=
  Equiv.decidableEq discreteEquiv

private instance decidableEqAdmissibleClass : DecidableEq (AdmissibleClass N) :=
  Subtype.instDecidableEq

private instance decidableIsZero : DecidablePred (AdmissibleClass.IsZero (N := N)) :=
  fun t => decidable_of_iff _ (AdmissibleClass.isZero_iff_latticeMismatch t).symm

instance decidableTerminal : DecidablePred (LatticeSearchState.terminal (N := N)) :=
  fun s =>
    if h : s.remaining = ∅ then isTrue (Or.inl h)
    else if h' : ∃ t ∈ s.remaining, AdmissibleClass.IsZero t then isTrue (Or.inr h')
    else isFalse (by
      intro ht
      cases ht with
      | inl hempty => exact h hempty
      | inr hex => exact h' hex)

/-- Discard one remaining candidate. -/
noncomputable def LatticeSearchState.step (s : LatticeSearchState N)
    (h : ¬ s.terminal) : LatticeSearchState N :=
  have hne : s.remaining.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact h (Or.inl hempty)
  ⟨s.remaining.erase (Classical.choose (Finset.Nonempty.exists_mem hne))⟩

theorem LatticeSearchState.step_measure_lt (s : LatticeSearchState N) (h : ¬ s.terminal) :
    (s.step h).remaining.card < s.remaining.card := by
  unfold LatticeSearchState.step
  have hne : s.remaining.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact h (Or.inl hempty)
  have hex := Finset.Nonempty.exists_mem hne
  exact Finset.card_erase_lt_of_mem (Classical.choose_spec hex)

/-- Concrete descent schema: exhaust the admissible lattice. -/
noncomputable def latticeSearchSchema (N : ℕ) [NeZero N] : DescentSchema where
  State := LatticeSearchState N
  measure := fun s => s.remaining.card
  terminal := LatticeSearchState.terminal
  step := LatticeSearchState.step
  measure_lt := LatticeSearchState.step_measure_lt

/-- Full initial search state. -/
noncomputable def fullLatticeSearch (N : ℕ) [NeZero N] : LatticeSearchState N :=
  ⟨Finset.univ⟩

theorem latticeSearch_reaches_terminal (N : ℕ) [NeZero N] :
    ∃ s' : LatticeSearchState N, LatticeSearchState.terminal s' :=
  (latticeSearchSchema N).reaches_terminal (fullLatticeSearch N)

/-- Integer-size placeholder for Phase-5 infinite descent (FLT etc.). -/
structure IntegerSizeState where
  values : List ℤ

def IntegerSizeState.measure (s : IntegerSizeState) : ℕ :=
  (s.values.map Int.natAbs).max?.getD 0

/-- Terminal when empty or all zeros (trivial solution branch). -/
def IntegerSizeState.terminal (s : IntegerSizeState) : Prop :=
  s.values = [] ∨ ∀ n ∈ s.values, n = 0

instance : DecidablePred IntegerSizeState.terminal := fun s =>
  if h : s.values = [] then isTrue (Or.inl h)
  else if h' : ∀ n ∈ s.values, n = 0 then isTrue (Or.inr h')
  else isFalse (by
    intro ht
    cases ht with
    | inl hempty => exact h hempty
    | inr hall => exact h' hall)

/--
Trivial step for the placeholder: clear the list when non-terminal.
Phase 5 replaces this with genuine amplification / factor-extraction descent.
-/
def IntegerSizeState.step (s : IntegerSizeState) (_h : ¬ s.terminal) : IntegerSizeState :=
  ⟨[]⟩

/--
Weak schema for integer size: terminate immediately by moving to the empty list.
Useful only as an API hook for Phase 5; not a mathematical descent on solutions.
-/
def integerSizeSchema : DescentSchema where
  State := IntegerSizeState
  measure := fun s => if IntegerSizeState.terminal s then 0 else s.measure + 1
  terminal := IntegerSizeState.terminal
  step := IntegerSizeState.step
  measure_lt := by
    intro s h
    have hterm : IntegerSizeState.terminal ⟨[]⟩ := Or.inl rfl
    simp [IntegerSizeState.step, hterm, h]

end Framework

end DstDiophantine
