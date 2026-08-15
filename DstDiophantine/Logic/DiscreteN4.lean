/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.TruthValue
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.RotorClass
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.IntervalCases

/-!
# Smallest complete D4L clock: admissible \(N=4\)

The anti-synchronisation cutoff \(\pi/2\) is a lattice point iff \(4\mid N\).
On \(N=4\) each axis has exactly three admissible ticks, giving \(3^3=27\)
worlds. Their heights are the seven values
\(-1,-2/3,-1/3,0,1/3,2/3,+1\), grouped into the four D4L states.

Enumeration of the full torus \(4^6=4096\) is avoided: the census is the
product of the three-tick axis alphabet. Finite cardinalities are decided
on that 27-element type.
-/

namespace DstDiophantine

namespace Logic

open Discrete Framework Invariant Operations Real
open _root_.DstDiophantine.Embedding

/-- Admissible tick on one \(N=4\) axis. -/
inductive AxisTick
  | rest
  | boost
  | rotation
  deriving DecidableEq, Repr

instance : Fintype AxisTick where
  elems := {AxisTick.rest, .boost, .rotation}
  complete x := by cases x <;> simp

/-- Vote \(e_a\in\{-1,0,+1\}\): boost, rest, rotation. -/
def AxisTick.vote : AxisTick → ℤ
  | .rest => 0
  | .boost => 1
  | .rotation => -1

def AxisTick.dual : AxisTick → AxisTick
  | .rest => .rest
  | .boost => .rotation
  | .rotation => .boost

@[simp] theorem vote_rest : AxisTick.rest.vote = 0 := rfl
@[simp] theorem vote_boost : AxisTick.boost.vote = 1 := rfl
@[simp] theorem vote_rotation : AxisTick.rotation.vote = -1 := rfl

@[simp] theorem vote_dual (t : AxisTick) : t.dual.vote = -t.vote := by
  cases t <;> simp [AxisTick.dual]

@[simp] theorem dual_dual (t : AxisTick) : t.dual.dual = t := by
  cases t <;> rfl

/-- An admissible \(N=4\) world is a vote on each of the three axes. -/
abbrev World := Fin 3 → AxisTick

instance : Fintype World := Pi.instFintype

def mismatch (w : World) : ℤ :=
  ∑ a : Fin 3, (w a).vote

def World.dual (w : World) : World :=
  fun a => (w a).dual

@[simp] theorem mismatch_dual (w : World) : mismatch w.dual = -mismatch w := by
  simp [mismatch, World.dual]

theorem card_world : Fintype.card World = 27 := by
  decide

def AxisTick.toZMod : AxisTick → ZMod 4 × ZMod 4
  | .rest => (0, 0)
  | .boost => (1, 0)
  | .rotation => (0, 1)

def toDiscrete (w : World) : DiscreteTorsion 4 where
  n := fun a => (w a).toZMod.1
  m := fun a => (w a).toZMod.2

private theorem zmod4_zero_ne_one : (0 : ZMod 4) ≠ 1 := by decide

private theorem zmod4_val_one : (1 : ZMod 4).val = 1 := by decide

theorem toDiscrete_admissible (w : World) : IsAdmissible (toDiscrete w) := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  cases ha : w a <;> simp [toDiscrete, AxisTick.toZMod, ha, zmod4_val_one]

theorem axis_sq_vote (t : AxisTick) :
    ((t.toZMod.1.val : ℤ) ^ 2 - (t.toZMod.2.val : ℤ) ^ 2) = t.vote := by
  cases t <;> simp [AxisTick.toZMod, AxisTick.vote, zmod4_val_one]

theorem latticeMismatch_toDiscrete (w : World) :
    latticeMismatch (toDiscrete w) = mismatch w := by
  simp only [latticeMismatch, mismatch, toDiscrete]
  congr 1
  ext a
  simpa using axis_sq_vote (w a)

/-- On \(N=4\), normalised height is the average of the three votes. -/
theorem JNormalized_toDiscrete (w : World) :
    JNormalized (toTorsionParams (toDiscrete w)) = (mismatch w : ℝ) / 3 := by
  rw [JNormalized_eq_sixteen_lattice, latticeMismatch_toDiscrete]
  ring

private theorem zmod4_eq_of_val {x : ZMod 4} {n : ℕ} (h : x.val = n) :
    x = n := by
  rw [← ZMod.natCast_zmod_val x, h]

theorem admissible_axis_n4 {t : DiscreteTorsion 4} (h : IsAdmissible t) (a : Fin 3) :
    (t.n a = 0 ∧ t.m a = 0) ∨ (t.n a = 1 ∧ t.m a = 0) ∨ (t.n a = 0 ∧ t.m a = 1) := by
  have hsum : 4 * ((t.n a).val + (t.m a).val) ≤ 4 :=
    (AdmissibleClass.isAdmissible_iff_four_le t).mp h a
  have hle : (t.n a).val + (t.m a).val ≤ 1 := by omega
  have _hnlt : (t.n a).val < 4 := ZMod.val_lt _
  have _hmlt : (t.m a).val < 4 := ZMod.val_lt _
  interval_cases hn : (t.n a).val <;> interval_cases hm : (t.m a).val
  · exact Or.inl ⟨zmod4_eq_of_val hn, zmod4_eq_of_val hm⟩
  · exact Or.inr (Or.inr ⟨zmod4_eq_of_val hn, zmod4_eq_of_val hm⟩)
  · omega
  · omega
  · exact Or.inr (Or.inl ⟨zmod4_eq_of_val hn, zmod4_eq_of_val hm⟩)
  all_goals omega

def ofDiscrete {t : DiscreteTorsion 4} (_h : IsAdmissible t) : World :=
  fun a =>
    if t.n a = 1 then .boost
    else if t.m a = 1 then .rotation
    else .rest

theorem ofDiscrete_toZMod {t : DiscreteTorsion 4} (h : IsAdmissible t) (a : Fin 3) :
    ((ofDiscrete h a).toZMod.1 = t.n a) ∧ ((ofDiscrete h a).toZMod.2 = t.m a) := by
  rcases admissible_axis_n4 h a with h00 | h10 | h01
  · simp [ofDiscrete, AxisTick.toZMod, h00.1, h00.2, zmod4_zero_ne_one]
  · simp [ofDiscrete, AxisTick.toZMod, h10.1, h10.2]
  · have hn : t.n a ≠ 1 := by
      rw [h01.1]; exact zmod4_zero_ne_one
    simp [ofDiscrete, AxisTick.toZMod, h01.1, h01.2, zmod4_zero_ne_one]

theorem toDiscrete_ofDiscrete {t : DiscreteTorsion 4} (h : IsAdmissible t) :
    toDiscrete (ofDiscrete h) = t := by
  obtain ⟨n, m⟩ := t
  refine congrArg₂ DiscreteTorsion.mk ?_ ?_
  · funext a; exact (ofDiscrete_toZMod (t := ⟨n, m⟩) h a).1
  · funext a; exact (ofDiscrete_toZMod (t := ⟨n, m⟩) h a).2

theorem ofDiscrete_toDiscrete (w : World) :
    ofDiscrete (toDiscrete_admissible w) = w := by
  funext a
  cases hw : w a <;>
    simp [ofDiscrete, toDiscrete, AxisTick.toZMod, hw, zmod4_zero_ne_one]

/-- Admissible \(N=4\) configurations are exactly the 27 vote-worlds. -/
def worldEquiv : World ≃ { t : DiscreteTorsion 4 // IsAdmissible t } where
  toFun w := ⟨toDiscrete w, toDiscrete_admissible w⟩
  invFun t := ofDiscrete t.property
  left_inv := ofDiscrete_toDiscrete
  right_inv t := Subtype.ext (toDiscrete_ofDiscrete t.property)

theorem card_admissible_n4 :
    Fintype.card { t : DiscreteTorsion 4 // IsAdmissible t } = 27 := by
  rw [← Fintype.card_congr worldEquiv, card_world]

/-! ### Heights and D4L states -/

theorem vote_le_one (t : AxisTick) : t.vote ≤ 1 := by cases t <;> decide

theorem vote_ge_neg_one (t : AxisTick) : -1 ≤ t.vote := by cases t <;> decide

theorem mismatch_le_three (w : World) : mismatch w ≤ 3 := by
  have h0 := vote_le_one (w 0)
  have h1 := vote_le_one (w 1)
  have h2 := vote_le_one (w 2)
  simp only [mismatch, Fin.sum_univ_three]
  omega

theorem mismatch_ge_neg_three (w : World) : -3 ≤ mismatch w := by
  have h0 := vote_ge_neg_one (w 0)
  have h1 := vote_ge_neg_one (w 1)
  have h2 := vote_ge_neg_one (w 2)
  simp only [mismatch, Fin.sum_univ_three]
  omega

theorem mismatch_mem_range (w : World) :
    mismatch w = -3 ∨ mismatch w = -2 ∨ mismatch w = -1 ∨
      mismatch w = 0 ∨ mismatch w = 1 ∨ mismatch w = 2 ∨ mismatch w = 3 := by
  have hle := mismatch_le_three w
  have hge := mismatch_ge_neg_three w
  omega

theorem abs_JNormalized_toDiscrete (w : World) :
    |JNormalized (toTorsionParams (toDiscrete w))| ≤ 1 := by
  rw [JNormalized_toDiscrete]
  have hle := mismatch_le_three w
  have hge := mismatch_ge_neg_three w
  have habs : |(mismatch w : ℝ)| ≤ 3 := by
    have : |mismatch w| ≤ (3 : ℤ) := abs_le.mpr ⟨hge, hle⟩
    exact_mod_cast this
  have : 0 < (3 : ℝ) := by norm_num
  rw [abs_div, abs_of_pos this]
  exact (div_le_one this).mpr habs

noncomputable def classifyWorld (w : World) : TruthValue :=
  classifyOfMem (JNormalized (toTorsionParams (toDiscrete w))) (abs_JNormalized_toDiscrete w)

theorem classifyWorld_T_iff (w : World) :
    classifyWorld w = .T ↔ mismatch w = 0 := by
  unfold classifyWorld
  rw [classifyOfMem_eq_T_iff, JNormalized_toDiscrete]
  constructor
  · intro h
    have : (mismatch w : ℝ) = 0 := (div_eq_zero_iff.mp h).resolve_right (by norm_num)
    exact_mod_cast this
  · intro h
    simp [h]

theorem classifyWorld_F_iff (w : World) :
    classifyWorld w = .F ↔ mismatch w = 3 := by
  unfold classifyWorld
  rw [classifyOfMem_eq_F_iff, JNormalized_toDiscrete]
  constructor
  · intro h
    have : (mismatch w : ℝ) = 3 := by linarith
    exact_mod_cast this
  · intro h
    simp [h]

theorem classifyWorld_U_iff (w : World) :
    classifyWorld w = .U ↔ mismatch w = 1 ∨ mismatch w = 2 := by
  unfold classifyWorld
  rw [classifyOfMem_eq_U_iff, JNormalized_toDiscrete]
  constructor
  · intro h
    have hpos : 0 < (mismatch w : ℝ) := by nlinarith [h.1]
    have hposI : 0 < mismatch w := Int.cast_pos.mp hpos
    have hlt : (mismatch w : ℝ) < 3 := by nlinarith [h.2]
    have hltI : mismatch w < 3 := by exact_mod_cast hlt
    have hge := mismatch_ge_neg_three w
    omega
  · intro h
    rcases h with h | h <;> simp [h] <;> norm_num

theorem classifyWorld_B_iff (w : World) :
    classifyWorld w = .B ↔
      mismatch w = -1 ∨ mismatch w = -2 ∨ mismatch w = -3 := by
  unfold classifyWorld
  rw [classifyOfMem_eq_B_iff, JNormalized_toDiscrete]
  constructor
  · intro h
    have hlt : (mismatch w : ℝ) < 0 := by nlinarith [h.2]
    have hltI : mismatch w < 0 := Int.cast_lt_zero.mp hlt
    have hle : -3 ≤ (mismatch w : ℝ) := by nlinarith [h.1]
    have hleI : (-3 : ℤ) ≤ mismatch w := by exact_mod_cast hle
    have hbound := mismatch_le_three w
    omega
  · intro h
    rcases h with h | h | h <;> simp [h] <;> norm_num

theorem card_mismatch_zero :
    Fintype.card { w : World // mismatch w = 0 } = 7 := by
  decide

theorem card_mismatch_one :
    Fintype.card { w : World // mismatch w = 1 } = 6 := by
  decide

theorem card_mismatch_two :
    Fintype.card { w : World // mismatch w = 2 } = 3 := by
  decide

theorem card_mismatch_three :
    Fintype.card { w : World // mismatch w = 3 } = 1 := by
  decide

theorem card_mismatch_neg_one :
    Fintype.card { w : World // mismatch w = -1 } = 6 := by
  decide

theorem card_mismatch_neg_two :
    Fintype.card { w : World // mismatch w = -2 } = 3 := by
  decide

theorem card_mismatch_neg_three :
    Fintype.card { w : World // mismatch w = -3 } = 1 := by
  decide

theorem card_state_T :
    Fintype.card { w : World // classifyWorld w = .T } = 7 := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun w => classifyWorld_T_iff w)]
  exact card_mismatch_zero

theorem card_state_F :
    Fintype.card { w : World // classifyWorld w = .F } = 1 := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun w => classifyWorld_F_iff w)]
  exact card_mismatch_three

theorem card_state_U :
    Fintype.card { w : World // classifyWorld w = .U } = 9 := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun w => classifyWorld_U_iff w)]
  have : Fintype.card { w : World // mismatch w = 1 ∨ mismatch w = 2 } = 9 := by
    decide
  exact this

theorem card_state_B :
    Fintype.card { w : World // classifyWorld w = .B } = 10 := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun w => classifyWorld_B_iff w)]
  have : Fintype.card
      { w : World // mismatch w = -1 ∨ mismatch w = -2 ∨ mismatch w = -3 } = 10 := by
    decide
  exact this

theorem JNormalized_world_mem (w : World) :
    JNormalized (toTorsionParams (toDiscrete w)) ∈
      ({(-1 : ℝ), -2 / 3, -1 / 3, 0, 1 / 3, 2 / 3, 1} : Set ℝ) := by
  rw [JNormalized_toDiscrete]
  rcases mismatch_mem_range w with h | h | h | h | h | h | h
    <;> simp [h]

theorem classify_pureHyperbolic_n4 :
    ofParams (toTorsionParams (pureHyperbolicDiscrete 4))
      (admissible_continuous_of_discrete _ (pureHyperbolicDiscrete_admissible (by decide))) =
      .F := by
  rw [ofParams_eq_F_iff, JNormalized_pureHyperbolicDiscrete (by decide)]

theorem classify_pureElliptic_n4 :
    ofParams (toTorsionParams (pureEllipticDiscrete 4))
      (admissible_continuous_of_discrete _ (pureEllipticDiscrete_admissible (by decide))) =
      .B := by
  rw [ofParams_eq_B_iff, JNormalized_pureEllipticDiscrete (by decide)]
  constructor <;> norm_num

theorem classify_zero_n4 :
    ofParams (toTorsionParams (zeroTorsion 4))
      (admissible_continuous_of_discrete _ (zero_admissible_zeroHeight 4).1) = .T := by
  rw [ofParams_eq_T_iff, ← isZeroHeight_iff_JNormalized]
  exact (zero_admissible_zeroHeight 4).2

end Logic

end DstDiophantine
