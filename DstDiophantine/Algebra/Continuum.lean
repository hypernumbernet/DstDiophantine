import DstDiophantine.Algebra.Discrete
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Continuum limit: density of admissible discrete configurations
-/

namespace DstDiophantine

open Operations Real

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
  · intro a
    have hαle := natFloor_le hNpos (h a).1
    have hβle := natFloor_le hNpos (h a).2.1
    rw [Discrete.toTorsionParams_alpha, Discrete.toTorsionParams_beta, hαval, hβval]
    have hαnn' : 0 ≤ 2 * Real.pi * (αk a : ℝ) / N := by
      simpa [Discrete.toTorsionParams_alpha, hαval] using
        Discrete.toTorsionParams_alpha_nonneg t a
    have hβnn' : 0 ≤ 2 * Real.pi * (βk a : ℝ) / N := by
      simpa [Discrete.toTorsionParams_beta, hβval] using
        Discrete.toTorsionParams_beta_nonneg t a
    rw [abs_of_nonneg (add_nonneg hαnn' hβnn')]
    exact add_le_add hαle hβle |>.trans (h a).2.2
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

end Continuum

end DstDiophantine
