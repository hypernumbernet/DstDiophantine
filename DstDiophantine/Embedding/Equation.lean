import DstDiophantine.Embedding.IntegerRotor
import DstDiophantine.Embedding.NullTranslator
import DstDiophantine.Embedding.PowerMap
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Diophantine equations as rotor–translator motors
-/

namespace DstDiophantine

namespace Embedding

open Motor CliffordAlgebra PGA

/-- A simple additive Diophantine relation `a + b = c`. -/
structure AdditiveEquation where
  a : ℤ
  b : ℤ
  c : ℤ

/-- Algebraic motor encoding an additive relation via null translators. -/
noncomputable def additiveMotor (e : AdditiveEquation) : PGA :=
  nullTranslator e.a * nullTranslator e.b * (reverse (nullTranslator e.c))

theorem additiveMotor_eq (e : AdditiveEquation) :
    additiveMotor e =
      nullTranslator e.a * nullTranslator e.b * reverse (nullTranslator e.c) := rfl

theorem additive_faithful (a b c : ℤ) :
    nullTranslator a * nullTranslator b = nullTranslator c ↔ a + b = c := by
  constructor
  · intro h
    have hT : nullTranslator (a + b - c) = 1 := by
      calc nullTranslator (a + b - c)
          = nullTranslator (a + b) * nullTranslator (-c) := by
              rw [← nullTranslator_add, sub_eq_add_neg]
          _ = nullTranslator c * nullTranslator (-c) := by rw [← h, nullTranslator_add]
          _ = nullTranslator (c + -c) := by rw [← nullTranslator_add]
          _ = nullTranslator 0 := by ring_nf
          _ = 1 := nullTranslator_zero
    exact sub_eq_zero.mp ((nullTranslator_faithful (a + b - c)).mp hT)
  · intro h
    subst h
    rw [← nullTranslator_add]

/-- Monomial rotor factor `R(n)^k` for `n ≠ 0`. -/
noncomputable def monomialRotor (n : ℤ) (hn : n ≠ 0) (k : ℕ) : PGA :=
  (integerRotor n hn) ^ k

inductive DiophantineExpr where
  | const (c : ℤ)
  | add (x y : DiophantineExpr)
  | mul (x y : DiophantineExpr)

/-- Evaluate a Diophantine expression as an integer. -/
def evalExpr : DiophantineExpr → ℤ
  | .const c => c
  | .add x y => evalExpr x + evalExpr y
  | .mul x y => evalExpr x * evalExpr y

/-- Rotor part of a Diophantine expression (multiplicative sector only). -/
noncomputable def exprRotor : DiophantineExpr → Option PGA
  | .const c => if h : c ≠ 0 then some (integerRotor c h) else none
  | .add _ _ => none
  | .mul x y =>
    match exprRotor x, exprRotor y with
    | some rx, some ry => some (rx * ry)
    | _, _ => none

/-- Null-translator part for additive expressions. -/
noncomputable def exprTranslator : DiophantineExpr → PGA
  | .const c => nullTranslator c
  | .add x y => exprTranslator x * exprTranslator y
  | .mul _ _ => 1

/-- Combined motor for a polynomial expression (additive part in null sector). -/
noncomputable def diophantineMotor (e : DiophantineExpr) : PGA :=
  exprTranslator e

theorem diophantineMotor_add (a b : ℤ) :
    diophantineMotor (.add (.const a) (.const b)) = nullTranslator a * nullTranslator b := by
  simp [diophantineMotor, exprTranslator]

theorem diophantineMotor_const (c : ℤ) :
    diophantineMotor (.const c) = nullTranslator c := by
  simp [diophantineMotor, exprTranslator]

private theorem diophantineMotor_sub_const (a b c : ℤ) :
    diophantineMotor (.add (.add (.const a) (.const b)) (.const (-c))) =
      nullTranslator (a + b - c) := by
  simp [diophantineMotor, exprTranslator, nullTranslator_add, sub_eq_add_neg]

theorem diophantine_zero_iff (a b c : ℤ) :
    diophantineMotor (.add (.add (.const a) (.const b)) (.const (-c))) = 1 ↔ a + b = c := by
  rw [diophantineMotor_sub_const, nullTranslator_faithful, sub_eq_zero]

end Embedding

end DstDiophantine
