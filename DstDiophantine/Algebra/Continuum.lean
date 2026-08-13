import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Invariant
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity

/-!
# Continuum limit: density of admissible discrete configurations

Parameter approximation (`exists_discrete_approx`) implies approximation of the
torsional scalar `J` on the admissible cone (`exists_discrete_approx_J`).
-/

namespace DstDiophantine

open Operations Real Discrete Invariant

namespace Continuum

def AdmissibleContinuous : Set TorsionParams :=
  { p | Discrete.IsAdmissibleContinuous p }

theorem mem_admissibleContinuous_iff (p : TorsionParams) :
    p ∈ AdmissibleContinuous ↔ Discrete.IsAdmissibleContinuous p :=
  Iff.rfl

theorem lattice_in_interval {N : ℕ} (hNpos : 0 < N) (k : ℕ) (hk : k * 4 ≤ N) :
    0 ≤ 2 * Real.pi * k / N ∧ 2 * Real.pi * k / N ≤ Real.pi / 2 := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg _))
      hN.le
  · apply (div_le_iff₀ hN).2
    nlinarith [Real.pi_pos.le, show (4 : ℝ) * k ≤ (N : ℝ) from by
      rw [mul_comm (4 : ℝ) k]; exact_mod_cast hk]

private theorem natFloor_le {N : ℕ} (hNpos : 0 < N) {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.pi * (⌊x * N / (2 * Real.pi)⌋₊ : ℝ) / N ≤ x := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hπ : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hf' : (⌊x * N / (2 * Real.pi)⌋₊ : ℝ) ≤ x * N / (2 * Real.pi) := by
    exact_mod_cast Nat.floor_le (a := x * N / (2 * Real.pi)) (by positivity)
  have hmul : 2 * Real.pi * (⌊x * N / (2 * Real.pi)⌋₊ : ℝ) ≤ x * N := by
    calc 2 * Real.pi * (⌊x * N / (2 * Real.pi)⌋₊ : ℝ)
        ≤ 2 * Real.pi * (x * N / (2 * Real.pi)) := by gcongr
      _ = x * N := by field_simp [hπ.ne']
  apply (div_le_iff₀ hN).2
  exact hmul

private theorem natFloor_near {N : ℕ} (hNpos : 0 < N) (x : ℝ) :
    x - 2 * Real.pi * (⌊x * N / (2 * Real.pi)⌋₊ : ℝ) / N < 2 * Real.pi / N := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hπ : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hf' : x * N / (2 * Real.pi) < (⌊x * N / (2 * Real.pi)⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (x * N / (2 * Real.pi))
  have hbound : x * N < 2 * Real.pi * ((⌊x * N / (2 * Real.pi)⌋₊ : ℝ) + 1) := by
    calc x * N
        = (x * N / (2 * Real.pi)) * (2 * Real.pi) := by field_simp [hπ.ne']
      _ < ((⌊x * N / (2 * Real.pi)⌋₊ : ℝ) + 1) * (2 * Real.pi) := by gcongr
      _ = 2 * Real.pi * ((⌊x * N / (2 * Real.pi)⌋₊ : ℝ) + 1) := by ring
  have hlt : x < 2 * Real.pi / N + 2 * Real.pi * (⌊x * N / (2 * Real.pi)⌋₊ : ℝ) / N := by
    field_simp [hN.ne']
    nlinarith [Real.pi_pos, hbound]
  rw [sub_lt_iff_lt_add]
  exact hlt

theorem exists_discrete_approx {p : TorsionParams} (h : Discrete.IsAdmissibleContinuous p) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : NeZero N),
      ∃ t : Discrete.DiscreteTorsion N, Discrete.IsAdmissible t ∧
        (∀ a : Fin 3, |p.alpha a - (Discrete.toTorsionParams t).alpha a| < ε) ∧
        (∀ a : Fin 3, |p.beta a - (Discrete.toTorsionParams t).beta a| < ε) := by
  set N₀ := Nat.ceil (4 * Real.pi / ε) + 1
  let N := max 4 N₀
  have hNpos : 0 < N := lt_max_iff.mpr (Or.inl four_pos)
  have hNe : NeZero N := ⟨ne_of_gt hNpos⟩
  have hNbound : 4 * Real.pi / ε ≤ (N : ℝ) := by
    have hNge : N₀ ≤ N := le_max_right _ _
    calc 4 * Real.pi / ε ≤ (Nat.ceil (4 * Real.pi / ε) : ℝ) := by exact_mod_cast Nat.le_ceil _
      _ ≤ (N₀ : ℝ) := by dsimp [N₀]; exact_mod_cast Nat.le_succ _
      _ ≤ N := by exact_mod_cast hNge
  have hstep : 2 * Real.pi / N < ε := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hNpos)]
    nlinarith [Real.pi_pos, hε, (div_le_iff₀ hε).1 hNbound]
  let αk (a : Fin 3) : ℕ := ⌊p.alpha a * N / (2 * Real.pi)⌋₊
  let βk (a : Fin 3) : ℕ := ⌊p.beta a * N / (2 * Real.pi)⌋₊
  let t : Discrete.DiscreteTorsion N :=
    { n := fun a => (αk a : ZMod N), m := fun a => (βk a : ZMod N) }
  have hαklt (a : Fin 3) : αk a < N := by
    have hα : p.alpha a < 2 * Real.pi := by
      have hle : p.alpha a ≤ Real.pi / 2 := by linarith [(h a).1, (h a).2.1, (h a).2.2]
      linarith [Real.pi_pos, hle,
        show (Real.pi / 2 : ℝ) < 2 * Real.pi from by nlinarith [Real.pi_pos]]
    have hlt : p.alpha a * (N : ℝ) < (N : ℝ) * (2 * Real.pi) := by
      rw [mul_comm (p.alpha a)]
      exact mul_lt_mul_of_pos_left hα (Nat.cast_pos.mpr hNpos)
    have hπ : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
    have hpos : 0 ≤ p.alpha a * (N : ℝ) / (2 * Real.pi) :=
      div_nonneg (mul_nonneg (h a).1 (Nat.cast_nonneg _)) (by nlinarith [Real.pi_pos])
    exact (Nat.floor_lt hpos).2 ((div_lt_iff₀ hπ).2 hlt)
  have hβklt (a : Fin 3) : βk a < N := by
    have hβ : p.beta a < 2 * Real.pi := by
      have hle : p.beta a ≤ Real.pi / 2 := by linarith [(h a).2.1, (h a).1, (h a).2.2]
      linarith [Real.pi_pos, hle,
        show (Real.pi / 2 : ℝ) < 2 * Real.pi from by nlinarith [Real.pi_pos]]
    have hlt : p.beta a * (N : ℝ) < (N : ℝ) * (2 * Real.pi) := by
      rw [mul_comm (p.beta a)]
      exact mul_lt_mul_of_pos_left hβ (Nat.cast_pos.mpr hNpos)
    have hπ : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
    have hpos : 0 ≤ p.beta a * (N : ℝ) / (2 * Real.pi) :=
      div_nonneg (mul_nonneg (h a).2.1 (Nat.cast_nonneg _)) (by nlinarith [Real.pi_pos])
    exact (Nat.floor_lt hpos).2 ((div_lt_iff₀ hπ).2 hlt)
  have hαval (a : Fin 3) : (t.n a : ZMod N).val = αk a := by
    simp [t, ZMod.val_natCast, Nat.mod_eq_of_lt (hαklt a)]
  have hβval (a : Fin 3) : (t.m a : ZMod N).val = βk a := by
    simp [t, ZMod.val_natCast, Nat.mod_eq_of_lt (hβklt a)]
  refine ⟨N, hNe, t, ?_, ?_, ?_⟩
  · -- `IsAdmissible` = continuous admissibility of the embedding
    intro a
    have hαle := natFloor_le hNpos (h a).1
    have hβle := natFloor_le hNpos (h a).2.1
    rw [Discrete.toTorsionParams_alpha, Discrete.toTorsionParams_beta, hαval, hβval]
    have hαnn' : 0 ≤ 2 * Real.pi * (αk a : ℝ) / N := by
      simpa [Discrete.toTorsionParams_alpha, hαval] using
        Discrete.toTorsionParams_alpha_nonneg t a
    have hβnn' : 0 ≤ 2 * Real.pi * (βk a : ℝ) / N := by
      simpa [Discrete.toTorsionParams_beta, hβval] using
        Discrete.toTorsionParams_beta_nonneg t a
    exact ⟨hαnn', hβnn', add_le_add hαle hβle |>.trans (h a).2.2⟩
  · intro a
    have hαnn := (h a).1
    rw [Discrete.toTorsionParams_alpha, hαval, abs_lt]
    constructor
    · linarith [natFloor_near hNpos (p.alpha a), natFloor_le hNpos hαnn, hstep]
    · linarith [natFloor_le hNpos hαnn, natFloor_near hNpos (p.alpha a), hstep]
  · intro a
    have hβnn := (h a).2.1
    rw [Discrete.toTorsionParams_beta, hβval, abs_lt]
    constructor
    · linarith [natFloor_near hNpos (p.beta a), natFloor_le hNpos hβnn, hstep]
    · linarith [natFloor_le hNpos hβnn, natFloor_near hNpos (p.beta a), hstep]

private theorem abs_sq_sub_le_of_coord_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxle : x ≤ Real.pi / 2) (hyle : y ≤ Real.pi / 2) {δ : ℝ}
    (hδnn : 0 ≤ δ) (hδ : |x - y| ≤ δ) :
    |x ^ 2 - y ^ 2| ≤ δ * Real.pi := by
  have hfac : |x ^ 2 - y ^ 2| = |x - y| * |x + y| := by
    rw [← abs_mul, axis_sq_diff_eq]
  have hsum : |x + y| ≤ Real.pi := by
    rw [abs_of_nonneg (add_nonneg hx hy)]
    linarith
  calc |x ^ 2 - y ^ 2|
      = |x - y| * |x + y| := hfac
    _ ≤ δ * Real.pi := mul_le_mul hδ hsum (abs_nonneg _) hδnn

private theorem abs_J_sub_le_of_coord_bound {p q : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hq : IsAdmissibleContinuous q) {δ : ℝ}
    (hδnn : 0 ≤ δ)
    (hα : ∀ a, |p.alpha a - q.alpha a| ≤ δ) (hβ : ∀ a, |p.beta a - q.beta a| ≤ δ) :
    |J p - J q| ≤ 3 * δ * Real.pi := by
  have haxis (a : Fin 3) :
      |(p.alpha a ^ 2 - p.beta a ^ 2) - (q.alpha a ^ 2 - q.beta a ^ 2)| ≤
        2 * δ * Real.pi := by
    have h1 := abs_sq_sub_le_of_coord_bound (hp a).1 (hq a).1
      (by linarith [(hp a).2.1, (hp a).2.2]) (by linarith [(hq a).2.1, (hq a).2.2])
      hδnn (hα a)
    have h2 := abs_sq_sub_le_of_coord_bound (hp a).2.1 (hq a).2.1
      (by linarith [(hp a).1, (hp a).2.2]) (by linarith [(hq a).1, (hq a).2.2])
      hδnn (hβ a)
    calc |(p.alpha a ^ 2 - p.beta a ^ 2) - (q.alpha a ^ 2 - q.beta a ^ 2)|
        = |(p.alpha a ^ 2 - q.alpha a ^ 2) - (p.beta a ^ 2 - q.beta a ^ 2)| := by ring_nf
      _ ≤ |p.alpha a ^ 2 - q.alpha a ^ 2| + |p.beta a ^ 2 - q.beta a ^ 2| := abs_sub _ _
      _ ≤ δ * Real.pi + δ * Real.pi := by gcongr
      _ = 2 * δ * Real.pi := by ring
  have hJp : J p = (1 / 2) * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) := J_coef p
  have hJq : J q = (1 / 2) * ∑ a : Fin 3, (q.alpha a ^ 2 - q.beta a ^ 2) := J_coef q
  have hsum :
      |∑ a : Fin 3, ((p.alpha a ^ 2 - p.beta a ^ 2) - (q.alpha a ^ 2 - q.beta a ^ 2))| ≤
        3 * (2 * δ * Real.pi) := by
    simp only [Fin.sum_univ_three]
    have h01 := abs_add_le
      ((p.alpha 0 ^ 2 - p.beta 0 ^ 2) - (q.alpha 0 ^ 2 - q.beta 0 ^ 2))
      ((p.alpha 1 ^ 2 - p.beta 1 ^ 2) - (q.alpha 1 ^ 2 - q.beta 1 ^ 2))
    have h2 := abs_add_le
      (((p.alpha 0 ^ 2 - p.beta 0 ^ 2) - (q.alpha 0 ^ 2 - q.beta 0 ^ 2)) +
        ((p.alpha 1 ^ 2 - p.beta 1 ^ 2) - (q.alpha 1 ^ 2 - q.beta 1 ^ 2)))
      ((p.alpha 2 ^ 2 - p.beta 2 ^ 2) - (q.alpha 2 ^ 2 - q.beta 2 ^ 2))
    linarith [haxis 0, haxis 1, haxis 2, h01, h2]
  have hdiff :
      |J p - J q| =
        (1 / 2) *
          |∑ a : Fin 3, ((p.alpha a ^ 2 - p.beta a ^ 2) - (q.alpha a ^ 2 - q.beta a ^ 2))| := by
    rw [hJp, hJq, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    congr 1
    rw [← Finset.sum_sub_distrib]
  rw [hdiff]
  calc (1 / 2 : ℝ) *
        |∑ a : Fin 3, ((p.alpha a ^ 2 - p.beta a ^ 2) - (q.alpha a ^ 2 - q.beta a ^ 2))|
      ≤ (1 / 2) * (3 * (2 * δ * Real.pi)) := by gcongr
    _ = 3 * δ * Real.pi := by ring

/-- Discrete configurations approximate the torsional scalar `J` arbitrarily closely. -/
theorem exists_discrete_approx_J {p : TorsionParams} (h : IsAdmissibleContinuous p) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : NeZero N),
      ∃ t : DiscreteTorsion N, IsAdmissible t ∧
        |J p - J (toTorsionParams t)| < ε := by
  -- Choose coordinate tolerance so that `3 δ π < ε`.
  set δ := ε / (6 * Real.pi) with hδdef
  have hπ : 0 < Real.pi := Real.pi_pos
  have hδ : 0 < δ := by
    dsimp [δ]; positivity
  obtain ⟨N, hNe, t, hadm, hα, hβ⟩ := exists_discrete_approx h hδ
  refine ⟨N, hNe, t, hadm, ?_⟩
  have hq : IsAdmissibleContinuous (toTorsionParams t) :=
    (Discrete.isAdmissible_iff_admissibleContinuous t).mp hadm
  have hle := abs_J_sub_le_of_coord_bound h hq hδ.le
    (fun a => (hα a).le) (fun a => (hβ a).le)
  have hbound : 3 * δ * Real.pi = ε / 2 := by
    rw [hδdef]; field_simp; ring
  calc |J p - J (toTorsionParams t)|
      ≤ 3 * δ * Real.pi := hle
    _ = ε / 2 := hbound
    _ < ε := by linarith

end Continuum

end DstDiophantine
