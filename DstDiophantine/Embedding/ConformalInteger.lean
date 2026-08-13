import DstDiophantine.Algebra.CGA.NullCone
import DstDiophantine.Embedding.Height
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Conformal integer embedding (1D CGA probe)

PGA integer rotors `R(n) = exp(log|n| · B)` are **not** homogeneous: the
torsional height `integerHeight n ≍ (log|n|)²` diverges as `|n| → ∞`, which is
the quantisation gap behind continuous / coarse bridges.

1D CGA places nonzero integers on the null cone via
`X(n) = n₀ + n e + (1/2) n² n∞` with `X(n)² = 0`.
Dilation acts by the algebraic weight pattern `(1, c, c²)` on
`(n₀, e, n∞)` components — the multiplicative layer that PGA Poincaré-type
null translators do not supply.
-/

namespace DstDiophantine

namespace Embedding

open CGA CGA.CGA1 Real

/-- Conformal embedding of a real coordinate as a null point in `Cl(2,1)`. -/
noncomputable def conformalPoint (x : ℝ) : CGA1 :=
  CGA1.point x

theorem conformalPoint_sq (x : ℝ) : conformalPoint x * conformalPoint x = 0 :=
  CGA1.point_sq x

/-- Conformal embedding of an integer as a null point. -/
noncomputable def conformalInteger (n : ℤ) : CGA1 :=
  conformalPoint (n : ℝ)

theorem conformalInteger_sq (n : ℤ) :
    conformalInteger n * conformalInteger n = 0 :=
  conformalPoint_sq _

/-- Multiplicative dilation on conformal integers. -/
theorem conformalInteger_mul (m n : ℤ) :
    conformalInteger (m * n) =
      CliffordAlgebra.ι CGA.Q21
        (CGA1.n0Vec + ((m : ℝ) * (n : ℝ)) • CGA1.eLineVec
          + (1 / 2 * ((m : ℝ) * (n : ℝ)) ^ 2) • CGA1.nInfVec) := by
  simpa [conformalInteger, conformalPoint] using CGA1.point_mul m n

/-- Algebraic dilation weights `(1, c, c²)` on the null-cone embedding. -/
theorem conformalPoint_smul (c x : ℝ) :
    conformalPoint (c * x) =
      CliffordAlgebra.ι CGA.Q21
        (CGA1.n0Vec + c • (x • CGA1.eLineVec)
          + (c ^ 2) • ((1 / 2 * x ^ 2) • CGA1.nInfVec)) := by
  simp only [conformalPoint, CGA1.point, CGA1.pointVec_smul_weights]

theorem pointVec_on_null_cone (x : ℝ) : CGA.Q21 (CGA1.pointVec x) = 0 :=
  CGA1.Q21_pointVec x

/-- Dilation rapidity is injective for positive null-cone seeds (not a torus). -/
theorem conformalPoint_dilation_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective fun δ : ℝ => CGA1.pointVec (Real.exp δ * a) :=
  CGA1.pointVec_dilation_injective ha

/-- CGA dilation is not `2π`-periodic — contrast with PGA rapidity quantisation. -/
theorem conformalPoint_dilation_not_two_pi_periodic {a : ℝ} (ha : 0 < a) (δ : ℝ) :
    CGA1.pointVec (Real.exp (δ + 2 * Real.pi) * a) ≠
      CGA1.pointVec (Real.exp δ * a) :=
  CGA1.pointVec_dilation_not_two_pi_periodic ha δ

theorem bilin21_conformalPoint_nInf (x : ℝ) :
    CGA1.bilin21 (CGA1.pointVec x) CGA1.nInfVec = -1 :=
  CGA1.bilin21_pointVec_nInf x

theorem bilin21_conformalPoint_conformalPoint (x y : ℝ) :
    CGA1.bilin21 (CGA1.pointVec x) (CGA1.pointVec y) = -((x - y) ^ 2) / 2 :=
  CGA1.bilin21_pointVec_pointVec x y

/-- Scale-invariant CGA dilation mismatch `(e^δ − 1)²`. -/
noncomputable abbrev cgaDilationMismatch : ℝ → ℝ :=
  CGA1.cgaDilationMismatch

theorem cgaDilationMismatch_eq (a δ : ℝ) (ha : 0 < a) :
    cgaDilationMismatch δ =
      -2 * CGA1.bilin21 (CGA1.pointVec a) (CGA1.pointVec (Real.exp δ * a)) /
        a ^ 2 :=
  CGA1.cgaDilationMismatch_eq_of_pos a δ ha

/--
Nonzero real coordinate lying on the DST discrete null lattice:
`∃ n ≠ 0, x = n` (i.e. the conformal point is `X(n)` for a nonzero integer).
Not identified with PGA `IsAdmissibleContinuous`.
-/
def IsCGAIntegerPoint (x : ℝ) : Prop :=
  ∃ n : ℤ, n ≠ 0 ∧ x = (n : ℝ)

theorem IsCGAIntegerPoint_conformalInteger {n : ℤ} (hn : n ≠ 0) :
    IsCGAIntegerPoint (n : ℝ) :=
  ⟨n, hn, rfl⟩

theorem IsCGAIntegerPoint_natAbs {n : ℤ} (hn : n ≠ 0) :
    IsCGAIntegerPoint (n.natAbs : ℝ) :=
  ⟨(n.natAbs : ℤ), by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hn), rfl⟩

theorem IsCGAIntegerPoint_of_eq {x : ℝ} {k : ℤ} (hk : k ≠ 0)
    (heq : x = (k : ℝ)) : IsCGAIntegerPoint x :=
  ⟨k, hk, heq⟩

/-- Diagnostic: `2^{4/3}` is not an integer null-lattice point. -/
theorem not_isCGAIntegerPoint_two_rpow_four_thirds :
    ¬ IsCGAIntegerPoint ((2 : ℝ) ^ ((4 : ℝ) / 3)) := by
  rintro ⟨k, hk, heq⟩
  have hkpos : 0 < (k : ℝ) := by
    have : (0 : ℝ) < (2 : ℝ) ^ ((4 : ℝ) / 3) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rwa [heq] at this
  have hk0 : 0 < k := Int.cast_pos.mp hkpos
  have h16R : (k : ℝ) ^ 3 = 16 := by
    have hnn : (0 : ℝ) ≤ 2 := by norm_num
    have hpow : ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = (k : ℝ) ^ 3 := by rw [heq]
    have hleft : ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = (16 : ℝ) := by
      have hstep :
          ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) =
            (2 : ℝ) ^ (((4 : ℝ) / 3) * (3 : ℝ)) := by
        rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hnn]; norm_cast
      rw [hstep]; norm_num
    linarith [hleft, hpow]
  have hk3 : k ^ 3 = (16 : ℤ) := by exact_mod_cast h16R
  -- No integer cube equals 16: 2³ = 8 < 16 < 27 = 3³.
  have hle : k ≤ 2 := by
    by_contra h
    have : (3 : ℤ) ^ 3 ≤ k ^ 3 :=
      pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 3) (by omega : (3 : ℤ) ≤ k) 3
    omega
  have hge : 2 ≤ k := by
    by_contra h
    have : k ^ 3 ≤ (1 : ℤ) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt hk0) (by omega : k ≤ 1) 3
    omega
  rw [le_antisymm hle hge] at hk3
  norm_num at hk3

/--
PGA integer-rotor height is unbounded: for every real bound `M` there is a
nonzero integer whose torsional height exceeds `M`.
-/
theorem exists_integerHeight_gt (M : ℝ) :
    ∃ (n : ℤ) (hn : n ≠ 0), M < integerHeight n hn := by
  have hcoef : (0 : ℝ) < 16 / (3 * Real.pi ^ 2) := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  let target : ℝ := max M 0 + 1
  have htarget : 0 < target := by
    have : 0 ≤ max M 0 := le_max_right _ _
    linarith
  let thresh : ℝ :=
    Real.sqrt (target / (16 / (3 * Real.pi ^ 2))) / Real.log 2
  obtain ⟨k, hk⟩ := exists_nat_gt thresh
  refine ⟨(2 : ℤ) ^ (k + 1), pow_ne_zero _ (by decide), ?_⟩
  have hn : (2 : ℤ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by decide)
  rw [integerHeight_eq _ hn]
  have habs : Int.natAbs ((2 : ℤ) ^ (k + 1)) = 2 ^ (k + 1) := by
    rw [Int.natAbs_pow]; simp
  rw [habs, Nat.cast_pow]
  -- Goal contains `log (↑2 ^ (k+1))`.
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [h2]
  have hlog : Real.log ((2 : ℝ) ^ (k + 1)) = (↑(k + 1) : ℝ) * Real.log 2 := by
    rw [Real.log_pow (2 : ℝ) (k + 1)]
  rw [hlog, abs_of_nonneg (mul_nonneg hcoef.le (sq_nonneg _))]
  have hk1 : thresh < (↑(k + 1) : ℝ) := by
    have : (k : ℝ) < ↑(k + 1) := by exact_mod_cast Nat.lt_succ_self k
    exact hk.trans this
  have hsqrt :
      Real.sqrt (target / (16 / (3 * Real.pi ^ 2))) <
        (↑(k + 1) : ℝ) * Real.log 2 := by
    have hden : Real.log 2 ≠ 0 := ne_of_gt hlog2
    calc Real.sqrt (target / (16 / (3 * Real.pi ^ 2)))
        = thresh * Real.log 2 := by
          change _ = (_ / Real.log 2) * Real.log 2
          field_simp [hden]
      _ < (↑(k + 1) : ℝ) * Real.log 2 := mul_lt_mul_of_pos_right hk1 hlog2
  have ha : 0 ≤ target / (16 / (3 * Real.pi ^ 2)) := by positivity
  have hsq :
      target / (16 / (3 * Real.pi ^ 2)) < ((↑(k + 1) : ℝ) * Real.log 2) ^ 2 := by
    have hnn' : 0 ≤ (↑(k + 1) : ℝ) * Real.log 2 := by positivity
    have hlt := (sq_lt_sq₀ (Real.sqrt_nonneg _) hnn').mpr hsqrt
    rwa [Real.sq_sqrt ha] at hlt
  have hgt :
      target < (16 / (3 * Real.pi ^ 2)) * ((↑(k + 1) : ℝ) * Real.log 2) ^ 2 := by
    have hc : (16 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := ne_of_gt hcoef
    calc target
        = (16 / (3 * Real.pi ^ 2)) *
            (target / (16 / (3 * Real.pi ^ 2))) := by field_simp [hc]
      _ < (16 / (3 * Real.pi ^ 2)) * ((↑(k + 1) : ℝ) * Real.log 2) ^ 2 :=
          mul_lt_mul_of_pos_left hsq hcoef
  have hMlt : M < target := by
    have : M ≤ max M 0 := le_max_left _ _
    linarith
  exact hMlt.trans hgt

/-- Convenience form of the unboundedness diagnostic. -/
theorem integerHeight_not_globally_bounded :
    ¬ ∃ M : ℝ, ∀ (n : ℤ) (hn : n ≠ 0), integerHeight n hn ≤ M := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn, hlt⟩ := exists_integerHeight_gt M
  exact not_le_of_gt hlt (hM n hn)

end Embedding

end DstDiophantine
