import DstDiophantine.Framework.Lattice
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cardinality of the admissible discrete cone

The admissible locus in `(ℤ/Nℤ)⁶` is a product of three triangular cones of
side `⌊N/4⌋`. Consequently its cardinality depends only on `⌊N/4⌋`.
-/

namespace DstDiophantine

namespace Framework

open Discrete Finset

/-- One-axis admissible pairs `(n, m)` on `ZMod N`. -/
def AxisPair (N : ℕ) [NeZero N] :=
  { p : ZMod N × ZMod N // 4 * (p.1.val + p.2.val) ≤ N }

noncomputable instance {N : ℕ} [NeZero N] : Fintype (AxisPair N) :=
  Subtype.fintype _

/-- Triangular number `T(K) = (K+1)(K+2)/2`. -/
def triangleNum (K : ℕ) : ℕ :=
  (K + 1) * (K + 2) / 2

private theorem val_add_le_div_four {N : ℕ} {n m : ZMod N}
    (h : 4 * (n.val + m.val) ≤ N) :
    n.val + m.val ≤ N / 4 :=
  (Nat.le_div_iff_mul_le (by decide : 0 < (4 : ℕ))).2 (by
    simpa [mul_comm (4 : ℕ)] using h)

private theorem val_lt_succ_div_four {N : ℕ} {n m : ZMod N}
    (h : 4 * (n.val + m.val) ≤ N) :
    n.val < N / 4 + 1 :=
  Nat.lt_succ_of_le <| Nat.le_trans (Nat.le_add_right n.val m.val) (val_add_le_div_four h)

private theorem val_lt_succ_div_four_right {N : ℕ} {n m : ZMod N}
    (h : 4 * (n.val + m.val) ≤ N) :
    m.val < N / 4 + 1 :=
  Nat.lt_succ_of_le <| Nat.le_trans (Nat.le_add_left m.val n.val) (val_add_le_div_four h)

private theorem fin_val_lt_N {N : ℕ} [NeZero N] {i : Fin (N / 4 + 1)} :
    i.val < N :=
  Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp i.isLt)
    (Nat.div_lt_self (NeZero.pos N) (by decide : 1 < 4))

private theorem triangle_sum (K : ℕ) :
    ∑ i ∈ range (K + 1), (K + 1 - i) = (K + 1) * (K + 2) / 2 := by
  have hreflect := sum_range_reflect (fun j : ℕ => j + 1) (K + 1)
  have hL : ∑ i ∈ range (K + 1), (K + 1 - i) =
      ∑ i ∈ range (K + 1), (K + 1 - 1 - i + 1) := by
    refine sum_congr rfl fun i hi => ?_
    have : i < K + 1 := mem_range.mp hi
    omega
  have hsplit :
      ∑ i ∈ range (K + 1), (i + (1 : ℕ)) =
        ∑ i ∈ range (K + 1), i + ∑ _ ∈ range (K + 1), (1 : ℕ) :=
    sum_add_distrib
  rw [hL, hreflect, hsplit, sum_range_id, sum_const, card_range, nsmul_one]
  simp only [Nat.add_sub_cancel]
  convert_to (K + 1) * K / 2 + (K + 1) = (K + 1) * (K + 2) / 2
  · norm_cast
  rw [← Nat.add_mul_div_right ((K + 1) * K) (K + 1) (by decide : 0 < 2)]
  congr 1
  ring

private def triangleSigma (K : ℕ) :
    { p : Fin (K + 1) × Fin (K + 1) // p.1.val + p.2.val ≤ K } ≃
      (i : Fin (K + 1)) × Fin (K - i.val + 1) where
  toFun p :=
    ⟨p.val.1, ⟨p.val.2.val, by
      have hcomm : p.val.2.val + p.val.1.val ≤ K := by
        rw [add_comm]; exact p.property
      exact Nat.lt_succ_of_le (Nat.le_sub_of_add_le hcomm)⟩⟩
  invFun s := by
    refine ⟨(s.1, ⟨s.2.val, ?hlt⟩), ?hsum⟩
    · exact lt_of_lt_of_le s.2.isLt (Nat.succ_le_succ (Nat.sub_le K s.1.val))
    · have hi : s.1.val ≤ K := Nat.lt_succ_iff.mp s.1.isLt
      have hj : s.2.val ≤ K - s.1.val := Nat.lt_succ_iff.mp s.2.isLt
      have : s.1.val + s.2.val ≤ K := by
        calc s.1.val + s.2.val
            ≤ s.1.val + (K - s.1.val) := Nat.add_le_add_left hj _
          _ = K := add_tsub_cancel_of_le hi
      simpa using this
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Fin.ext rfl
  right_inv s := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Fin.ext rfl)

private theorem card_triangle (K : ℕ) :
    Fintype.card { p : Fin (K + 1) × Fin (K + 1) // p.1.val + p.2.val ≤ K } =
      triangleNum K := by
  rw [Fintype.card_congr (triangleSigma K), Fintype.card_sigma]
  simp only [Fintype.card_fin, triangleNum]
  have hsum : ∑ i : Fin (K + 1), (K - (i : ℕ) + 1) =
      ∑ i ∈ range (K + 1), (K + 1 - i) := by
    rw [sum_fin_eq_sum_range]
    refine sum_congr rfl fun i hi => ?_
    have hlt : i < K + 1 := mem_range.mp hi
    simp [hlt]
    omega
  exact hsum.trans (triangle_sum K)

variable {N : ℕ} [NeZero N]

private def axisPairEquivFin :
    AxisPair N ≃
      { p : Fin (N / 4 + 1) × Fin (N / 4 + 1) // p.1.val + p.2.val ≤ N / 4 } where
  toFun p :=
    ⟨(⟨p.val.1.val, val_lt_succ_div_four p.property⟩,
      ⟨p.val.2.val, val_lt_succ_div_four_right p.property⟩),
      val_add_le_div_four p.property⟩
  invFun q :=
    ⟨((q.val.1.val : ZMod N), (q.val.2.val : ZMod N)), by
      have hsum : q.val.1.val + q.val.2.val ≤ N / 4 := q.property
      have hmul : 4 * (q.val.1.val + q.val.2.val) ≤ 4 * (N / 4) :=
        Nat.mul_le_mul_left 4 hsum
      have hle : 4 * (N / 4) ≤ N := Nat.mul_div_le N 4
      have hv1 : ((q.val.1.val : ZMod N).val) = q.val.1.val :=
        ZMod.val_natCast_of_lt (fin_val_lt_N (i := q.val.1))
      have hv2 : ((q.val.2.val : ZMod N).val) = q.val.2.val :=
        ZMod.val_natCast_of_lt (fin_val_lt_N (i := q.val.2))
      rw [hv1, hv2]
      exact hmul.trans hle⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact ZMod.natCast_zmod_val p.val.1
    · exact ZMod.natCast_zmod_val p.val.2
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (ZMod.val_natCast_of_lt (fin_val_lt_N (i := q.val.1)))
    · exact Fin.ext (ZMod.val_natCast_of_lt (fin_val_lt_N (i := q.val.2)))

theorem card_axisPair : Fintype.card (AxisPair N) = triangleNum (N / 4) := by
  rw [Fintype.card_congr axisPairEquivFin, card_triangle]

private def admissibleEquivAxes : AdmissibleClass N ≃ (Fin 3 → AxisPair N) where
  toFun t := fun a =>
    ⟨(t.val.n a, t.val.m a),
      (AdmissibleClass.isAdmissible_iff_four_le t.val).mp t.property a⟩
  invFun f :=
    ⟨{ n := fun a => (f a).val.1, m := fun a => (f a).val.2 }, by
      rw [AdmissibleClass.isAdmissible_iff_four_le]
      intro a
      exact (f a).property⟩
  left_inv t := by
    apply Subtype.ext
    cases t.val
    rfl
  right_inv f := by
    funext a
    apply Subtype.ext
    rfl

/--
The admissible class has cardinality `T(⌊N/4⌋)³`, where
`T(K)=(K+1)(K+2)/2` is the triangular number.
-/
theorem card_admissibleClass :
    Fintype.card (AdmissibleClass N) = triangleNum (N / 4) ^ 3 := by
  rw [Fintype.card_congr admissibleEquivAxes, Fintype.card_fun, Fintype.card_fin,
    card_axisPair]

theorem card_admissibleClass_eq_of_div_four {N M : ℕ} [NeZero N] [NeZero M]
    (h : N / 4 = M / 4) :
    Fintype.card (AdmissibleClass N) = Fintype.card (AdmissibleClass M) := by
  rw [card_admissibleClass, card_admissibleClass, h]

theorem card_admissibleClass_one_of_lt_four (hN : N < 4) :
    Fintype.card (AdmissibleClass N) = 1 := by
  have hdiv : N / 4 = 0 := Nat.div_eq_of_lt hN
  rw [card_admissibleClass, hdiv]
  simp [triangleNum]

theorem card_admissibleClass_four :
    Fintype.card (AdmissibleClass 4) = 27 := by
  have : NeZero 4 := ⟨by decide⟩
  rw [card_admissibleClass]
  simp [triangleNum]

theorem card_admissibleClass_eight :
    Fintype.card (AdmissibleClass 8) = 216 := by
  have : NeZero 8 := ⟨by decide⟩
  rw [card_admissibleClass]
  simp [triangleNum]

end Framework

end DstDiophantine
