import DstDiophantine.Embedding.IntegerRotor
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.UnitGroup
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Amplification
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Rotor equivalence classes modulo the discrete unit group

Each admissible rotor class is represented by a point on `(ℤ/Nℤ)⁶`. Continuous
integer rotors are quantised to the nearest lattice representative.
-/

namespace DstDiophantine

namespace Embedding

open Discrete UnitGroup Operations Motor Amplification Real CliffordAlgebra PGA

variable {N : ℕ} [NeZero N]

/-- The zero point on the discrete torsion torus. -/
def zeroTorsion (N : ℕ) [NeZero N] : DiscreteTorsion N :=
  { n := fun _ => 0, m := fun _ => 0 }

theorem discreteRotor_zero (N : ℕ) [NeZero N] : discreteRotor (zeroTorsion N) = 1 := by
  simp [discreteRotor, rotorTorsion, toTorsionParams, zeroTorsion, omegaTorsion]

/-- Right-multiplication by a discrete unit: `r ~ s` when `r = s · u`. -/
def RotorRel (N : ℕ) [NeZero N] (r s : PGA) : Prop :=
  ∃ u ∈ DiscreteUnit N, r = s * u

theorem rotorRel_refl (r : PGA) : RotorRel N r r := by
  refine ⟨discreteRotor (zeroTorsion N), ⟨zeroTorsion N, rfl⟩, ?_⟩
  simp [discreteRotor_zero]

/-- Rotor class represented by a discrete torus point (canonical representative). -/
structure RotorClass (N : ℕ) [NeZero N] where
  rep : DiscreteTorsion N

def rotorClassOf (t : DiscreteTorsion N) : RotorClass N := ⟨t⟩

noncomputable def rotorOfClass (c : RotorClass N) : PGA :=
  discreteRotor c.rep

/-- Lattice index for a continuous pure-boost rapidity on axis `0`. -/
noncomputable def quantizeRapidity (N : ℕ) [NeZero N] (θ : ℝ) : ℤ :=
  ⌊θ * N / (2 * Real.pi)⌋

/-- Principal rapidity in `[0, 2π)` for nonnegative `θ`. -/
noncomputable def principalRapidity (θ : ℝ) : ℝ :=
  θ - 2 * Real.pi * ⌊θ / (2 * Real.pi)⌋

theorem principalRapidity_nonneg {θ : ℝ} (_hθ : 0 ≤ θ) :
    0 ≤ principalRapidity θ := by
  unfold principalRapidity
  have hden : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : (⌊θ / (2 * Real.pi)⌋ : ℝ) ≤ θ / (2 * Real.pi) := Int.floor_le _
  have hmul : (⌊θ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ θ :=
    (le_div_iff₀ hden).mp hle
  linarith

theorem principalRapidity_lt_two_pi {θ : ℝ} (_hθ : 0 ≤ θ) :
    principalRapidity θ < 2 * Real.pi := by
  unfold principalRapidity
  have hden : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlt : θ / (2 * Real.pi) < (⌊θ / (2 * Real.pi)⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hmul : θ < ((⌊θ / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) :=
    (div_lt_iff₀ hden).mp hlt
  linarith

theorem quantizeRapidity_add_two_pi (N : ℕ) [NeZero N] (θ : ℝ) :
    quantizeRapidity N (θ + 2 * Real.pi) = quantizeRapidity N θ + (N : ℤ) := by
  unfold quantizeRapidity
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h :
      (θ + 2 * Real.pi) * N / (2 * Real.pi) =
        θ * N / (2 * Real.pi) + (N : ℝ) := by
    field_simp [hN, hden]
  rw [h, Int.floor_add_natCast]

theorem quantizeRapidity_add_two_pi_nsmul (N : ℕ) [NeZero N] (θ : ℝ) (n : ℕ) :
    quantizeRapidity N (θ + 2 * Real.pi * n) =
      quantizeRapidity N θ + (n : ℤ) * (N : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h :
        θ + 2 * Real.pi * (n + 1 : ℕ) =
          (θ + 2 * Real.pi * (n : ℕ)) + 2 * Real.pi := by
      simp [Nat.cast_succ]; ring
    rw [h, quantizeRapidity_add_two_pi, ih]
    push_cast
    ring

theorem quantizeRapidity_principal (N : ℕ) [NeZero N] {θ : ℝ} (hθ : 0 ≤ θ) :
    quantizeRapidity N (principalRapidity θ) =
      quantizeRapidity N θ - (⌊θ / (2 * Real.pi)⌋ : ℤ) * (N : ℤ) := by
  have hden : (0 : ℝ) < 2 * Real.pi := by positivity
  set n := ⌊θ / (2 * Real.pi)⌋
  have hn0 : 0 ≤ n := Int.floor_nonneg.mpr (div_nonneg hθ hden.le)
  have hnR : (n : ℝ) = (n.toNat : ℝ) := by
    rw [← Int.cast_natCast n.toNat, Int.toNat_of_nonneg hn0]
  have hprin : principalRapidity θ = θ - 2 * Real.pi * n := rfl
  have hθeq : θ = principalRapidity θ + 2 * Real.pi * (n.toNat : ℝ) := by
    rw [hprin, ← hnR]; ring
  have hmul := quantizeRapidity_add_two_pi_nsmul N (principalRapidity θ) n.toNat
  have hθq : quantizeRapidity N θ =
      quantizeRapidity N (principalRapidity θ) + (n.toNat : ℤ) * (N : ℤ) := by
    rw [← hθeq] at hmul; exact hmul
  have hnZ : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  rw [hθq, hnZ]
  abel

theorem quantizeRapidity_zmod_eq_principal (N : ℕ) [NeZero N] {θ : ℝ}
    (hθ : 0 ≤ θ) :
    (quantizeRapidity N θ : ZMod N) =
      (quantizeRapidity N (principalRapidity θ) : ZMod N) := by
  have h := quantizeRapidity_principal N hθ
  rw [h]
  simp

/-- Quantise `log|n|` to the nearest lattice rapidity on axis `0`.

Uses the integer-rotor convention `pureBoost (2 log|n|)`, so the index is
`⌊(2 log|n|) N / (2π)⌋ = ⌊N log|n| / π⌋`.
-/
noncomputable def quantizeInt (N : ℕ) [NeZero N] (n : ℤ) (_hn : n ≠ 0) : DiscreteTorsion N :=
  { n := fun a => match a with
      | 0 => (quantizeRapidity N (2 * Real.log (Int.natAbs n)) : ZMod N)
      | _ => 0
    m := fun _ => 0 }

/--
Quantise the continuous log-mismatch `logMismatch a c` to a pure-boost lattice
seed.  Uses the same floor map as `quantizeInt`, applied to the mismatch
rapidity `log|c| - log|a|` (so index `⌊N (log|c|-log|a|) / (2π)⌋`).
-/
noncomputable def quantizeMismatch (N : ℕ) [NeZero N] (a c : ℤ)
    (_ha : a ≠ 0) (_hc : c ≠ 0) : DiscreteTorsion N :=
  { n := fun i => match i with
      | 0 =>
        (quantizeRapidity N
          (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)) : ZMod N)
      | _ => 0
    m := fun _ => 0 }

noncomputable def integerClass (n : ℤ) (hn : n ≠ 0) : RotorClass N :=
  rotorClassOf (quantizeInt N n hn)

theorem mem_discreteUnit_of_class (c : RotorClass N) :
    rotorOfClass c ∈ DiscreteUnit N :=
  ⟨c.rep, rfl⟩

noncomputable def rotorClassEquiv : RotorClass N ≃ DiscreteTorsion N where
  toFun c := c.rep
  invFun t := ⟨t⟩
  left_inv c := by cases c; rfl
  right_inv _ := rfl

noncomputable instance : Fintype (RotorClass N) :=
  Fintype.ofEquiv _ rotorClassEquiv.symm

theorem rotorClass_finite : (Set.univ : Set (RotorClass N)).Finite :=
  Set.finite_univ

/-! ### Quantisation lemmas -/

theorem quantizeInt_m_eq_zero (n : ℤ) (hn : n ≠ 0) (a : Fin 3) :
    (quantizeInt N n hn).m a = 0 := rfl

theorem quantizeInt_n_of_ne_zero (n : ℤ) (hn : n ≠ 0) {a : Fin 3} (ha : a ≠ 0) :
    (quantizeInt N n hn).n a = 0 := by
  fin_cases a <;> first | exact (ha rfl).elim | rfl

/-- `quantizeInt` is a pure-boost seed (only axis `0` of `n` may be nonzero). -/
theorem quantizeInt_pureBoost (n : ℤ) (hn : n ≠ 0) :
    (∀ a : Fin 3, a ≠ 0 → (quantizeInt N n hn).n a = 0) ∧
      (∀ a : Fin 3, (quantizeInt N n hn).m a = 0) :=
  ⟨fun _a ha => quantizeInt_n_of_ne_zero n hn ha, fun a => quantizeInt_m_eq_zero n hn a⟩

theorem quantizeMismatch_m_eq_zero (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) (i : Fin 3) :
    (quantizeMismatch N a c ha hc).m i = 0 := rfl

theorem quantizeMismatch_n_of_ne_zero (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0)
    {i : Fin 3} (hi : i ≠ 0) :
    (quantizeMismatch N a c ha hc).n i = 0 := by
  fin_cases i <;> first | exact (hi rfl).elim | rfl

theorem quantizeMismatch_pureBoost (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    (∀ i : Fin 3, i ≠ 0 → (quantizeMismatch N a c ha hc).n i = 0) ∧
      (∀ i : Fin 3, (quantizeMismatch N a c ha hc).m i = 0) :=
  ⟨fun _i hi => quantizeMismatch_n_of_ne_zero a c ha hc hi,
    fun i => quantizeMismatch_m_eq_zero a c ha hc i⟩

theorem quantizeRapidity_zero : quantizeRapidity N 0 = 0 := by
  simp [quantizeRapidity]

theorem quantizeInt_one (n : ℤ) (hn : n ≠ 0) (habs : Int.natAbs n = 1) :
    quantizeInt N n hn = zeroTorsion N := by
  refine congr_arg₂ DiscreteTorsion.mk ?_ ?_
  · funext a; fin_cases a <;>
      simp [quantizeRapidity, habs, Real.log_one]
  · funext a; rfl

/--
Floor error for the continuous lift of a quantised rapidity: the reconstructed
axis-`0` angle differs from `θ` by less than one lattice step `2π/N`, after
accounting for the integral part that is reduced mod `N`.

Here we record the standard floor inequality before modular reduction:
`quantizeRapidity N θ ≤ θ N / (2π) < quantizeRapidity N θ + 1`.
-/
theorem quantizeRapidity_le (θ : ℝ) :
    (quantizeRapidity N θ : ℝ) ≤ θ * N / (2 * Real.pi) :=
  Int.floor_le _

theorem lt_quantizeRapidity_add_one (θ : ℝ) :
    θ * N / (2 * Real.pi) < (quantizeRapidity N θ : ℝ) + 1 :=
  Int.lt_floor_add_one _

/-- Reconstructed rapidity on the principal real line (before `ZMod` wrap). -/
noncomputable def rapidityOfIndex (N : ℕ) [NeZero N] (k : ℤ) : ℝ :=
  2 * Real.pi * k / N

theorem quantizeRapidity_error (θ : ℝ) :
    |θ - rapidityOfIndex N (quantizeRapidity N θ)| < 2 * Real.pi / N := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hden : 0 < (2 * Real.pi : ℝ) := by positivity
  unfold rapidityOfIndex quantizeRapidity
  set k := ⌊θ * N / (2 * Real.pi)⌋
  have hle : (k : ℝ) ≤ θ * N / (2 * Real.pi) := Int.floor_le _
  have hlt : θ * N / (2 * Real.pi) < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have h1 : 2 * Real.pi * k / N ≤ θ := by
    have := mul_le_mul_of_nonneg_left hle (le_of_lt hden)
    have hL : 2 * Real.pi * (k : ℝ) = 2 * Real.pi * k := by ring
    field_simp [hN.ne'] at this ⊢
    linarith
  have h2 : θ < 2 * Real.pi * k / N + 2 * Real.pi / N := by
    have := mul_lt_mul_of_pos_left hlt hden
    field_simp [hN.ne'] at this ⊢
    linarith
  have hnonneg : 0 ≤ θ - 2 * Real.pi * k / N := sub_nonneg.mpr h1
  rw [abs_of_nonneg hnonneg]
  linarith

theorem quantizeMismatch_error (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    |(logMismatch a c ha hc).alpha 0 -
        rapidityOfIndex N (quantizeRapidity N
          (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)))| <
      2 * Real.pi / N := by
  simp only [logMismatch, pureBoost]
  exact quantizeRapidity_error _

end Embedding

end DstDiophantine
