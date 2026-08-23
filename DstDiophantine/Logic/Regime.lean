/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.TruthValue
import Mathlib.Data.Set.Basic

/-!
# Proof-status (regime) layer of D4L

The amplitude layer classifies a continuous height, so negation is not a
function of the four labels. A DST *proof artefact* — a core lemma, a live
bridge, a refuted diagnostic, a bookkeeping identity — carries a discrete
status. On that discrete carrier the same four names become a label algebra,
and implication is defined as a table, not as the residuum of `min`.

The four names are shared with `TruthValue`. Measurement is **not**
`JNormalized`. No Belnap-FOUR isomorphism is claimed. This module does not
import `Theorems`.
-/

namespace DstDiophantine

namespace Logic

open scoped Set

/--
Label negation (a function of the four names). Representatives
`T↦0`, `U↦1/2`, `F↦1`, `B↦-1/2` with `j ↦ -j`.
-/
def negR : TruthValue → TruthValue
  | .T => .T
  | .U => .B
  | .B => .U
  | .F => .B

/--
Amplitude-style conjunction (`min` of the same representatives).
In particular `F ∧ ¬F = B`.
-/
def conjR : TruthValue → TruthValue → TruthValue
  | .T, .T => .T
  | .T, .U => .T
  | .T, .F => .T
  | .T, .B => .B
  | .U, .T => .T
  | .U, .U => .U
  | .U, .F => .U
  | .U, .B => .B
  | .F, .T => .T
  | .F, .U => .U
  | .F, .F => .F
  | .F, .B => .B
  | .B, .T => .B
  | .B, .U => .B
  | .B, .F => .B
  | .B, .B => .B

/-- Amplitude-style disjunction (`max` of the same representatives). -/
def disjR : TruthValue → TruthValue → TruthValue
  | .T, .T => .T
  | .T, .U => .U
  | .T, .F => .F
  | .T, .B => .T
  | .U, .T => .U
  | .U, .U => .U
  | .U, .F => .F
  | .U, .B => .T
  | .F, .T => .F
  | .F, .U => .F
  | .F, .F => .F
  | .F, .B => .T
  | .B, .T => .T
  | .B, .U => .T
  | .B, .F => .T
  | .B, .B => .B

/-- Establishedness rank: `F < B < U < T`. -/
def regimeRank : TruthValue → ℕ
  | .F => 0
  | .B => 1
  | .U => 2
  | .T => 3

/-- Meet of establishedness (packaging two artefacts). `T ⊓ U = U`. -/
def meetR (a b : TruthValue) : TruthValue :=
  if regimeRank a ≤ regimeRank b then a else b

/--
Regime implication (not a lattice residuum).

* `T → φ = φ`
* `F → φ = T` (vacuous, from a refuted diagnostic)
* `U → T = U` (an open bridge does not establish a theorem)
* `B → T = U` (a conflicted reading does not explode to a theorem)
-/
def impR : TruthValue → TruthValue → TruthValue
  | .T, φ => φ
  | .F, _ => .T
  | .U, .T => .U
  | .U, .U => .U
  | .U, .F => .F
  | .U, .B => .B
  | .B, .T => .U
  | .B, .U => .B
  | .B, .F => .F
  | .B, .B => .B

theorem impR_of_T (φ : TruthValue) : impR .T φ = φ := by
  cases φ <;> rfl

theorem impR_of_F (φ : TruthValue) : impR .F φ = .T :=
  rfl

theorem impR_U_T : impR .U .T = .U :=
  rfl

theorem impR_B_T : impR .B .T = .U :=
  rfl

theorem meetR_T_U : meetR .T .U = .U :=
  rfl

theorem meetR_T_F : meetR .T .F = .F :=
  rfl

theorem conjR_comm (a b : TruthValue) : conjR a b = conjR b a := by
  cases a <;> cases b <;> rfl

theorem negR_T : negR .T = .T := by decide
theorem negR_U : negR .U = .B := by decide
theorem negR_B : negR .B = .U := by decide
theorem negR_F : negR .F = .B := by decide

/-- `s ∧ ¬s` never saturates `F`. -/
theorem conjR_negR_ne_F (s : TruthValue) : conjR s (negR s) ≠ .F := by
  cases s <;> decide

theorem conjR_negR_T_or_B (s : TruthValue) :
    conjR s (negR s) = .T ∨ conjR s (negR s) = .B := by
  cases s <;> decide

/-- Designated synchrony / “adopt as a theorem”. -/
def HoldsTR (s : TruthValue) : Prop :=
  s = .T

/-- Designated non-refutation: every status except `F`. -/
def HoldsNotFR (s : TruthValue) : Prop :=
  s ≠ .F

theorem holdsTR_holdsNotFR {s : TruthValue} (h : HoldsTR s) : HoldsNotFR s := by
  simp only [HoldsTR] at h
  subst h
  simp [HoldsNotFR]

/-- Named two-valued fragment `{T, F}`. -/
def IsNamedRegime (s : TruthValue) : Prop :=
  s = .T ∨ s = .F

/-- Wall two-valued fragment `{B, F}`. -/
def IsWallRegime (s : TruthValue) : Prop :=
  s = .B ∨ s = .F

theorem namedRegime_not_U {s : TruthValue} (h : IsNamedRegime s) : s ≠ .U := by
  rcases h with h | h <;> simp [h]

theorem namedRegime_not_B {s : TruthValue} (h : IsNamedRegime s) : s ≠ .B := by
  rcases h with h | h <;> simp [h]

theorem wallRegime_not_T {s : TruthValue} (h : IsWallRegime s) : s ≠ .T := by
  rcases h with h | h <;> simp [h]

theorem wallRegime_not_U {s : TruthValue} (h : IsWallRegime s) : s ≠ .U := by
  rcases h with h | h <;> simp [h]

/-- On the named fragment, non-refutation collapses to synchrony. -/
theorem namedRegime_holdsNotFR_iff_holdsTR {s : TruthValue} (h : IsNamedRegime s) :
    HoldsNotFR s ↔ HoldsTR s := by
  rcases h with h | h <;> simp [HoldsNotFR, HoldsTR, h]

/-- Proof-status formulas, including implication. -/
inductive RegimeFormula
  | atom : ℕ → RegimeFormula
  | neg : RegimeFormula → RegimeFormula
  | conj : RegimeFormula → RegimeFormula → RegimeFormula
  | disj : RegimeFormula → RegimeFormula → RegimeFormula
  | imp : RegimeFormula → RegimeFormula → RegimeFormula
  deriving DecidableEq, Repr

namespace RegimeFormula

def eval (φ : RegimeFormula) (v : ℕ → TruthValue) : TruthValue :=
  match φ with
  | atom n => v n
  | neg ψ => negR (ψ.eval v)
  | conj ψ χ => conjR (ψ.eval v) (χ.eval v)
  | disj ψ χ => disjR (ψ.eval v) (χ.eval v)
  | imp ψ χ => impR (ψ.eval v) (χ.eval v)

@[simp] theorem eval_atom (n : ℕ) (v : ℕ → TruthValue) :
    (atom n).eval v = v n :=
  rfl

@[simp] theorem eval_neg (φ : RegimeFormula) (v : ℕ → TruthValue) :
    φ.neg.eval v = negR (φ.eval v) :=
  rfl

@[simp] theorem eval_conj (φ ψ : RegimeFormula) (v : ℕ → TruthValue) :
    (φ.conj ψ).eval v = conjR (φ.eval v) (ψ.eval v) :=
  rfl

@[simp] theorem eval_disj (φ ψ : RegimeFormula) (v : ℕ → TruthValue) :
    (φ.disj ψ).eval v = disjR (φ.eval v) (ψ.eval v) :=
  rfl

@[simp] theorem eval_imp (φ ψ : RegimeFormula) (v : ℕ → TruthValue) :
    (φ.imp ψ).eval v = impR (φ.eval v) (ψ.eval v) :=
  rfl

end RegimeFormula

/-- Assignment of atoms to discrete proof statuses. -/
structure RegimeValuation where
  assign : ℕ → TruthValue

namespace RegimeValuation

def const (s : TruthValue) : RegimeValuation where
  assign := fun _ => s

/-- Atoms `0,1,2,3` independently; remaining atoms are `T`. -/
def quad (c d l k : TruthValue) : RegimeValuation where
  assign := fun n =>
    if n = 0 then c else if n = 1 then d else if n = 2 then l else if n = 3 then k else .T

@[simp] theorem quad_zero (c d l k : TruthValue) :
    (quad c d l k).assign 0 = c := by
  simp [quad]

@[simp] theorem quad_one (c d l k : TruthValue) :
    (quad c d l k).assign 1 = d := by
  simp [quad]

@[simp] theorem quad_two (c d l k : TruthValue) :
    (quad c d l k).assign 2 = l := by
  simp [quad]

@[simp] theorem quad_three (c d l k : TruthValue) :
    (quad c d l k).assign 3 = k := by
  simp [quad]

/--
Atoms `0, …, xs.length - 1` from the list; remaining atoms are `T`.
Extends `quad` when more than four independent statuses are needed.
-/
def ofList (xs : List TruthValue) : RegimeValuation where
  assign := fun n => xs.getD n .T

theorem ofList_get (xs : List TruthValue) (n : ℕ) (hn : n < xs.length) :
    (ofList xs).assign n = xs[n] := by
  simp [ofList, List.getD, hn]

theorem ofList_default (xs : List TruthValue) (n : ℕ) (hn : xs.length ≤ n) :
    (ofList xs).assign n = .T := by
  simp [ofList, List.getD, Nat.not_lt.mpr hn]

@[simp] theorem ofList_nil_assign (n : ℕ) : (ofList []).assign n = .T := by
  simp [ofList]

theorem ofList_cons_zero (s : TruthValue) (xs : List TruthValue) :
    (ofList (s :: xs)).assign 0 = s := by
  simp [ofList]

end RegimeValuation

/-- Finite fold of `meetR` (establishedness meet). Empty list is `T`. -/
def meetRList : List TruthValue → TruthValue
  | [] => .T
  | a :: as => meetR a (meetRList as)

@[simp] theorem meetRList_nil : meetRList [] = .T :=
  rfl

@[simp] theorem meetRList_cons (a : TruthValue) (as : List TruthValue) :
    meetRList (a :: as) = meetR a (meetRList as) :=
  rfl

theorem meetRList_all_T : ∀ n : ℕ, meetRList (List.replicate n .T) = .T
  | 0 => rfl
  | n + 1 => by
    simp [List.replicate_succ, meetR, regimeRank, meetRList_all_T n]

theorem meetR_T_left (a : TruthValue) : meetR .T a = a := by
  cases a <;> rfl

theorem meetR_T_right (a : TruthValue) : meetR a .T = a := by
  cases a <;> rfl

/-- Packaging any established (`T`) slices with a live residual stays live. -/
theorem meetRList_T_append_U (n : ℕ) :
    meetRList (List.replicate n .T ++ [.U]) = .U := by
  induction n with
  | zero => simp [meetR, regimeRank]
  | succ n ih =>
    simp [List.replicate_succ, meetR_T_left, ih]

def ModelsTR (v : RegimeValuation) (Γ : Set RegimeFormula) : Prop :=
  ∀ φ ∈ Γ, HoldsTR (φ.eval v.assign)

def ModelsNotFR (v : RegimeValuation) (Γ : Set RegimeFormula) : Prop :=
  ∀ φ ∈ Γ, HoldsNotFR (φ.eval v.assign)

def EntailsTR (Γ : Set RegimeFormula) (ψ : RegimeFormula) : Prop :=
  ∀ v : RegimeValuation, ModelsTR v Γ → HoldsTR (ψ.eval v.assign)

def EntailsNotFR (Γ : Set RegimeFormula) (ψ : RegimeFormula) : Prop :=
  ∀ v : RegimeValuation, ModelsNotFR v Γ → HoldsNotFR (ψ.eval v.assign)

theorem modelsTR_to_modelsNotFR {v : RegimeValuation} {Γ : Set RegimeFormula}
    (h : ModelsTR v Γ) : ModelsNotFR v Γ :=
  fun φ hφ => holdsTR_holdsNotFR (h φ hφ)

end Logic

end DstDiophantine
