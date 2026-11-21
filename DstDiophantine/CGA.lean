import DstDiophantine.Embedding.ConformalInteger

/-!
# 1D CGA probe

Diagnostic dilation layer that PGA does not supply. Not re-exported from `DstDiophantine.Basic`.
-/

namespace DstDiophantine

namespace CGA

open CGA1

example (x : ℝ) : CGA1.point x * CGA1.point x = 0 :=
  CGA1.point_sq x

example (n : ℤ) :
    Embedding.conformalInteger n * Embedding.conformalInteger n = 0 :=
  Embedding.conformalInteger_sq n

example : ¬ ∃ M : ℝ, ∀ (n : ℤ) (hn : n ≠ 0),
    Embedding.integerHeight n hn ≤ M :=
  Embedding.integerHeight_not_globally_bounded

example (x y : ℝ) :
    CGA1.bilin21 (CGA1.pointVec x) (CGA1.pointVec y) = -((x - y) ^ 2) / 2 :=
  CGA1.bilin21_pointVec_pointVec x y

example (m : ℕ) (hm : 0 < m) :
    0 < CGA1.cgaDilationMismatch (Real.log 2 / (m : ℝ)) :=
  CGA1.cgaDilationMismatch_balanced_pos m hm

example (a δ : ℝ) (k : ℕ) :
    CGA1.pointVec (Real.exp ((k : ℝ) * δ) * a) =
      CGA1.pointVec (Real.exp δ ^ k * a) :=
  CGA1.pointVec_exp_nat_mul a δ k

example {n : ℤ} (hn : n ≠ 0) : Embedding.IsCGAIntegerPoint (n : ℝ) :=
  Embedding.IsCGAIntegerPoint_conformalInteger hn

example : ¬ Embedding.IsCGAIntegerPoint ((2 : ℝ) ^ ((4 : ℝ) / 3)) :=
  Embedding.not_isCGAIntegerPoint_two_rpow_four_thirds

example : Embedding.IsCGAPowerLatticePoint ((2 : ℝ) ^ ((4 : ℝ) / 3)) 3 :=
  Embedding.isCGAPowerLatticePoint_two_rpow_four_thirds

example {x : ℝ} {m : ℕ} (hx : Embedding.IsCGAIntegerPoint x) (hm : 0 < m) :
    Embedding.IsCGAPowerLatticePoint x m :=
  Embedding.IsCGAIntegerPoint.isCGAPowerLatticePoint hx hm

example {x : ℝ} {n : ℤ} (hx : Embedding.IsCGAIntegerPoint x) (hn : n ≠ 0) :
    Embedding.IsCGAIntegerPoint ((n : ℝ) * x) :=
  Embedding.IsCGAIntegerPoint_cgaDilation hx (Embedding.IsCGAIntegerDilation_int hn)

example {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) :
    CGA1.cgaDilation (γ / α) α = CGA1.pointVec γ :=
  CGA1.cgaDilation_scale_unique hα hγ

example {a c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) :
    Embedding.IsCGAIntegerDilation ((c.natAbs : ℝ) / (a.natAbs : ℝ)) ↔
      a.natAbs ∣ c.natAbs :=
  Embedding.IsCGAIntegerDilation_div_iff ha hc

example : ¬ Embedding.IsCGAIntegerDilation ((5 : ℝ) / 3) :=
  Embedding.not_isCGAIntegerDilation_five_div_three

end CGA

end DstDiophantine
