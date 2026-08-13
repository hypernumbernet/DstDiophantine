import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Framework.Lattice
import DstDiophantine.Framework.Amplification
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.nativeDecide false

/-!
# Modular torsional amplification with winding

Real `k`-fold scaling of rapidities is incompatible with coarseness: the legacy
`CoarseAmplificationWitness` is structurally empty.  The replacement tracks
multiplication on `(ℤ/Nℤ)⁶` and records the integer winding forced by reduction
modulo `N`.

For each coordinate `x : ZMod N`,
`k * x.val = (k • x).val + N * winding`,
and the continuous lift satisfies
`k * (2π x.val / N) = 2π (k • x).val / N + 2π * winding`.

Consequently `JNormalized` after modular amplification equals the naive
`k²`-scaled seed plus an explicit winding error term — the live bridge target
is a number-theoretic lower bound on that error, not a vacuous coarse witness.
-/

namespace DstDiophantine

open Operations Discrete Amplification Invariant Framework Real
open _root_.DstDiophantine.Embedding

namespace ModularAmplification

variable {N : ℕ} [NeZero N]

/-! ### Coordinate winding -/

/-- Nat division witnessing `k * x.val = (k • x).val + N * windingCoord`. -/
def windingCoord (k : ℕ) (x : ZMod N) : ℕ :=
  k * x.val / N

theorem mul_val_eq_val_add_winding (k : ℕ) (x : ZMod N) :
    k * x.val = (k • x).val + N * windingCoord k x := by
  unfold windingCoord
  have hmod : (k * x.val) % N = (k • x).val := by
    rw [nsmul_eq_mul, ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod,
      Nat.mod_eq_of_lt (ZMod.val_lt x)]
  have hdiv := Nat.div_add_mod (k * x.val) N
  linarith [hdiv, hmod]

/-- Strict upper bound: each coordinate winds fewer than `k` times. -/
theorem windingCoord_lt (k : ℕ) (x : ZMod N) (hk : 0 < k) :
    windingCoord k x < k := by
  unfold windingCoord
  have hN : 0 < N := NeZero.pos N
  have hval : x.val < N := ZMod.val_lt x
  rw [Nat.div_lt_iff_lt_mul hN]
  exact Nat.mul_lt_mul_of_pos_left hval hk

/-- Positive winding is exactly the overflow `N ≤ k · x.val`. -/
theorem windingCoord_pos_iff (k : ℕ) (x : ZMod N) :
    0 < windingCoord k x ↔ N ≤ k * x.val := by
  unfold windingCoord
  exact Nat.div_pos_iff.trans (and_iff_right (NeZero.pos N))

omit [NeZero N] in
theorem windingCoord_eq_zero_of_lt {N : ℕ} (k : ℕ) (x : ZMod N) (h : k * x.val < N) :
    windingCoord k x = 0 :=
  Nat.div_eq_of_lt h

/-- Continuous-angle form of the winding identity. -/
theorem scale_angle_eq_mod_plus_winding (k : ℕ) (x : ZMod N) :
    (k : ℝ) * (2 * Real.pi * x.val / N) =
      2 * Real.pi * (k • x).val / N + 2 * Real.pi * windingCoord k x := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hinter : (k * x.val : ℝ) = ((k • x).val : ℝ) + (N : ℝ) * windingCoord k x := by
    exact_mod_cast mul_val_eq_val_add_winding k x
  calc (k : ℝ) * (2 * Real.pi * x.val / N)
      = 2 * Real.pi * (k * x.val : ℝ) / N := by ring
    _ = 2 * Real.pi * (((k • x).val : ℝ) + (N : ℝ) * windingCoord k x) / N := by
        rw [hinter]
    _ = 2 * Real.pi * (k • x).val / N + 2 * Real.pi * windingCoord k x := by
        field_simp [hN]

/-! ### Discrete modular amplification -/

/-- Multiply every torus coordinate by `k` in `ZMod N`. -/
def amplifyDiscrete (k : ℕ) (t : DiscreteTorsion N) : DiscreteTorsion N where
  n := fun a => k • t.n a
  m := fun a => k • t.m a

@[simp] theorem amplifyDiscrete_n (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) :
    (amplifyDiscrete k t).n a = k • t.n a := rfl

@[simp] theorem amplifyDiscrete_m (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) :
    (amplifyDiscrete k t).m a = k • t.m a := rfl

/-- Total winding across all six coordinates. -/
def windingTotal (k : ℕ) (t : DiscreteTorsion N) : ℕ :=
  ∑ a : Fin 3, (windingCoord k (t.n a) + windingCoord k (t.m a))

/--
Real `k`-fold scaling that stays continuously admissible forces every lattice
coordinate below the wrap threshold, hence total winding vanishes.

Consequently a modular witness with `has_winding` cannot feed the continuous
amplification no-go directly — the live gap is a conformal / gauge condition
that is not the PGA real-scale cone.
-/
private theorem four_mul_le_implies_mul_lt (k v N : ℕ) [NeZero N]
    (h : 4 * k * v ≤ N) : k * v < N := by
  have hle : k * v ≤ 4 * k * v := by
    simpa [Nat.mul_assoc] using
      (Nat.le_mul_of_pos_left (k * v) (by decide : 0 < (4 : ℕ)))
  have hleN : k * v ≤ N := hle.trans h
  cases Nat.lt_or_eq_of_le hleN with
  | inl hlt => exact hlt
  | inr heq =>
    have h4N : 4 * N ≤ N := by
      calc 4 * N = 4 * (k * v) := by rw [heq]
        _ = 4 * k * v := by ring
        _ ≤ N := h
    have hNpos : 0 < N := NeZero.pos N
    have hlt : N < 4 * N := by
      have : 1 * N < 4 * N := Nat.mul_lt_mul_of_pos_right (by decide : 1 < 4) hNpos
      simpa using this
    exact absurd h4N (not_le_of_gt hlt)

theorem admissible_scale_implies_windingTotal_eq_zero (k : ℕ)
    (t : DiscreteTorsion N)
    (hadm : IsAdmissibleContinuous (scaleTorsion (k : ℝ) (toTorsionParams t))) :
    windingTotal k t = 0 := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hfour := (scale_admissible_iff_four_mul_le t hk0).mp hadm
  apply Finset.sum_eq_zero
  intro a _
  have hn : windingCoord k (t.n a) = 0 := by
    apply windingCoord_eq_zero_of_lt
    have hbound : 4 * k * (t.n a).val ≤ N := by
      have := hfour a
      have hle : 4 * k * (t.n a).val ≤ 4 * k * ((t.n a).val + (t.m a).val) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      exact hle.trans this
    exact four_mul_le_implies_mul_lt k (t.n a).val N hbound
  have hm : windingCoord k (t.m a) = 0 := by
    apply windingCoord_eq_zero_of_lt
    have hbound : 4 * k * (t.m a).val ≤ N := by
      have := hfour a
      have hle : 4 * k * (t.m a).val ≤ 4 * k * ((t.n a).val + (t.m a).val) :=
        Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
      exact hle.trans this
    exact four_mul_le_implies_mul_lt k (t.m a).val N hbound
  simp [hn, hm]
/-- Dual form: nonzero total winding rules out real-scale continuous admissibility. -/
theorem windingTotal_ne_zero_implies_not_admissible_scale (k : ℕ)
    (t : DiscreteTorsion N) (hw : windingTotal k t ≠ 0) :
    ¬ IsAdmissibleContinuous (scaleTorsion (k : ℝ) (toTorsionParams t)) := by
  intro hadm
  exact hw (admissible_scale_implies_windingTotal_eq_zero k t hadm)

/-! ### Lifted torsion parameters and the `J` error identity -/

/-- Continuous parameters of the modularly amplified point (principal values). -/
noncomputable def amplifiedParams (k : ℕ) (t : DiscreteTorsion N) : TorsionParams :=
  toTorsionParams (amplifyDiscrete k t)

theorem scale_alpha_eq_amplified_plus_winding (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) :
    (scaleTorsion (k : ℝ) (toTorsionParams t)).alpha a =
      (amplifiedParams k t).alpha a + 2 * Real.pi * windingCoord k (t.n a) := by
  simp only [scaleTorsion, toTorsionParams_alpha, amplifiedParams, amplifyDiscrete_n]
  exact scale_angle_eq_mod_plus_winding k (t.n a)

theorem scale_beta_eq_amplified_plus_winding (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) :
    (scaleTorsion (k : ℝ) (toTorsionParams t)).beta a =
      (amplifiedParams k t).beta a + 2 * Real.pi * windingCoord k (t.m a) := by
  simp only [scaleTorsion, toTorsionParams_beta, amplifiedParams, amplifyDiscrete_m]
  exact scale_angle_eq_mod_plus_winding k (t.m a)

/-- Per-axis winding correction inside the quadratic form for `J`. -/
noncomputable def axisWindingError (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) : ℝ :=
  let α := (amplifiedParams k t).alpha a
  let β := (amplifiedParams k t).beta a
  let wn := (windingCoord k (t.n a) : ℝ)
  let wm := (windingCoord k (t.m a) : ℝ)
  (2 * α * (2 * Real.pi * wn) + (2 * Real.pi * wn) ^ 2) -
    (2 * β * (2 * Real.pi * wm) + (2 * Real.pi * wm) ^ 2)

private theorem sq_diff_expand (α β δε δφ : ℝ) :
    (α + δε) ^ 2 - (β + δφ) ^ 2 =
      α ^ 2 - β ^ 2 + (2 * α * δε + δε ^ 2 - (2 * β * δφ + δφ ^ 2)) := by
  ring

theorem axis_sq_scale_eq_amplified_add_error (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) :
    (scaleTorsion (k : ℝ) (toTorsionParams t)).alpha a ^ 2 -
        (scaleTorsion (k : ℝ) (toTorsionParams t)).beta a ^ 2 =
      (amplifiedParams k t).alpha a ^ 2 - (amplifiedParams k t).beta a ^ 2 +
        axisWindingError k t a := by
  rw [scale_alpha_eq_amplified_plus_winding, scale_beta_eq_amplified_plus_winding]
  unfold axisWindingError
  exact sq_diff_expand _ _ _ _

/--
Real `k`-scaling of `J` equals the modular lift plus an explicit winding error.
The simple identity `J(scale k p) = k² J(p)` therefore fails for modular
amplification; bridges must control this error term.
-/
theorem J_scale_eq_J_amplified_add_error (k : ℕ) (t : DiscreteTorsion N) :
    J (scaleTorsion (k : ℝ) (toTorsionParams t)) =
      J (amplifiedParams k t) + (1 / 2) * ∑ a : Fin 3, axisWindingError k t a := by
  rw [J_coef, J_coef]
  simp only [Fin.sum_univ_three]
  have h0 := axis_sq_scale_eq_amplified_add_error k t 0
  have h1 := axis_sq_scale_eq_amplified_add_error k t 1
  have h2 := axis_sq_scale_eq_amplified_add_error k t 2
  linarith [h0, h1, h2]

theorem JNormalized_scale_eq_JNormalized_amplified_add_error (k : ℕ)
    (t : DiscreteTorsion N) :
    JNormalized (scaleTorsion (k : ℝ) (toTorsionParams t)) =
      JNormalized (amplifiedParams k t) +
        (8 / (3 * Real.pi ^ 2)) * ((1 / 2) * ∑ a : Fin 3, axisWindingError k t a) := by
  unfold JNormalized
  rw [J_scale_eq_J_amplified_add_error]
  ring

/-- Pure-boost seed: only axis `0` of `n` is possibly nonzero. -/
def IsPureBoostSeed (t : DiscreteTorsion N) : Prop :=
  (∀ a : Fin 3, a ≠ 0 → t.n a = 0) ∧ (∀ a : Fin 3, t.m a = 0)

theorem axisWindingError_pureBoost_of_ne_zero (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) {a : Fin 3} (ha : a ≠ 0) :
    axisWindingError k t a = 0 := by
  unfold axisWindingError amplifiedParams
  have hn : t.n a = 0 := hp.1 a ha
  have hm : t.m a = 0 := hp.2 a
  simp [hn, hm, windingCoord, amplifyDiscrete, toTorsionParams]

theorem axisWindingError_pureBoost_zero (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) :
    axisWindingError k t 0 =
      2 * (amplifiedParams k t).alpha 0 * (2 * Real.pi * windingCoord k (t.n 0)) +
        (2 * Real.pi * windingCoord k (t.n 0)) ^ 2 := by
  unfold axisWindingError
  have hm : t.m 0 = 0 := hp.2 0
  simp [hm, windingCoord]
theorem J_scale_eq_J_amplified_add_error_pureBoost (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) :
    J (scaleTorsion (k : ℝ) (toTorsionParams t)) =
      J (amplifiedParams k t) + (1 / 2) * axisWindingError k t 0 := by
  rw [J_scale_eq_J_amplified_add_error]
  simp only [Fin.sum_univ_three]
  have h1 := axisWindingError_pureBoost_of_ne_zero k t hp (by decide : (1 : Fin 3) ≠ 0)
  have h2 := axisWindingError_pureBoost_of_ne_zero k t hp (by decide : (2 : Fin 3) ≠ 0)
  simp [h1, h2]

/-! ### Pure-boost winding criterion -/

theorem windingTotal_pureBoost (k : ℕ) (t : DiscreteTorsion N) (hp : IsPureBoostSeed t) :
    windingTotal k t = windingCoord k (t.n 0) := by
  unfold windingTotal
  simp only [Fin.sum_univ_three]
  have hn1 : t.n 1 = 0 := hp.1 1 (by decide)
  have hn2 : t.n 2 = 0 := hp.1 2 (by decide)
  have hm0 : t.m 0 = 0 := hp.2 0
  have hm1 : t.m 1 = 0 := hp.2 1
  have hm2 : t.m 2 = 0 := hp.2 2
  simp [hn1, hn2, hm0, hm1, hm2, windingCoord]

theorem windingTotal_pureBoost_pos_iff (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) :
    0 < windingTotal k t ↔ N ≤ k * (t.n 0).val := by
  rw [windingTotal_pureBoost k t hp, windingCoord_pos_iff]

theorem windingTotal_pureBoost_ne_zero_iff (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) :
    windingTotal k t ≠ 0 ↔ N ≤ k * (t.n 0).val := by
  constructor
  · intro h
    exact (windingTotal_pureBoost_pos_iff k t hp).mp (Nat.pos_of_ne_zero h)
  · intro h
    exact ne_of_gt ((windingTotal_pureBoost_pos_iff k t hp).mpr h)

/-! ### Pure-boost quantisation helpers (shared by abc / Beal / FLT) -/

/-- Pure-boost lattice seed from a continuous rapidity on axis `0`. -/
noncomputable def pureBoostSeedOfRapidity (N : ℕ) [NeZero N] (θ : ℝ) : DiscreteTorsion N where
  n := fun i => match i with
    | 0 => (quantizeRapidity N θ : ZMod N)
    | _ => 0
  m := fun _ => 0

theorem pureBoostSeedOfRapidity_isPureBoost (N : ℕ) [NeZero N] (θ : ℝ) :
    IsPureBoostSeed (pureBoostSeedOfRapidity N θ) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    fin_cases a <;> first | exact (ha rfl).elim | rfl
  · intro a; rfl

/--
If `0 ≤ θ < 2π`, the floor index lies in `[0, N)` and agrees with the
`ZMod` representative after casting.
-/
theorem quantizeRapidity_of_lt_two_pi (N : ℕ) [NeZero N] (θ : ℝ)
    (h0 : 0 ≤ θ) (hlt : θ < 2 * Real.pi) :
    0 ≤ quantizeRapidity N θ ∧
      quantizeRapidity N θ < (N : ℤ) ∧
        ((quantizeRapidity N θ : ZMod N).val : ℤ) = quantizeRapidity N θ := by
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hden : 0 < (2 * Real.pi : ℝ) := by positivity
  have hfrac0 : 0 ≤ θ * N / (2 * Real.pi) :=
    div_nonneg (mul_nonneg h0 (Nat.cast_nonneg _)) hden.le
  have hfrac_lt : θ * N / (2 * Real.pi) < (N : ℝ) := by
    have : θ * N < 2 * Real.pi * N := mul_lt_mul_of_pos_right hlt hNpos
    exact (div_lt_iff₀ hden).mpr (by linarith [this])
  have hfloor0 : 0 ≤ quantizeRapidity N θ := Int.floor_nonneg.mpr hfrac0
  have hfloor_lt : quantizeRapidity N θ < (N : ℤ) :=
    Int.floor_lt.mpr hfrac_lt
  refine ⟨hfloor0, hfloor_lt, ?_⟩
  set k := quantizeRapidity N θ
  have hk0 : 0 ≤ k := hfloor0
  have hklt : k < (N : ℤ) := hfloor_lt
  have htoNat : k.toNat < N := by
    have : (k.toNat : ℤ) < N := by
      rw [Int.toNat_of_nonneg hk0]; exact hklt
    exact Nat.cast_lt.mp this
  have hcast : (k : ZMod N) = (k.toNat : ZMod N) := by
    rw [← Int.cast_natCast (R := ZMod N), Int.toNat_of_nonneg hk0]
  calc ((k : ZMod N).val : ℤ)
      = ((k.toNat : ZMod N).val : ℤ) := by rw [hcast]
    _ = ↑(k.toNat % N) := by rw [ZMod.val_natCast]
    _ = ↑k.toNat := by rw [Nat.mod_eq_of_lt htoNat]
    _ = k := Int.toNat_of_nonneg hk0

private theorem rapidity_frac_ge_of_ge (N k : ℕ) [NeZero N] (hk : 0 < k) (θ : ℝ)
    (hle : 2 * Real.pi / k ≤ θ) :
    (N : ℝ) / k ≤ θ * N / (2 * Real.pi) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have hden : 0 < (2 * Real.pi : ℝ) := by positivity
  calc (N : ℝ) / k
      = (2 * Real.pi / k) * N / (2 * Real.pi) := by field_simp [hk0]
    _ ≤ θ * N / (2 * Real.pi) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)) hden.le

/--
Pure-boost quantisation of a rapidity in `[0, 2π)` winds under `k`-fold modular
amplification whenever `2π / k ≤ θ` and `k ∣ N`.
-/
theorem windingTotal_ne_zero_of_rapidity_ge (N k : ℕ) [NeZero N] (hk : 0 < k)
    (θ : ℝ) (h0 : 0 ≤ θ) (hle : 2 * Real.pi / k ≤ θ) (hlt : θ < 2 * Real.pi)
    (hdvd : k ∣ N) :
    windingTotal k (pureBoostSeedOfRapidity N θ) ≠ 0 := by
  set t := pureBoostSeedOfRapidity N θ
  have hp : IsPureBoostSeed t := pureBoostSeedOfRapidity_isPureBoost N θ
  have hbounds := quantizeRapidity_of_lt_two_pi N θ h0 hlt
  obtain ⟨m, hm⟩ := hdvd
  have hfrac := rapidity_frac_ge_of_ge N k hk θ hle
  have hfloor : (m : ℤ) ≤ quantizeRapidity N θ := by
    have hmR : (m : ℝ) = (N : ℝ) / k := by
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
      rw [hm, Nat.cast_mul]
      exact (mul_div_cancel_left₀ (m : ℝ) hk0).symm
    have hleR : (m : ℝ) ≤ θ * N / (2 * Real.pi) := by
      rw [hmR]; exact hfrac
    exact Int.le_floor.mpr hleR
  have hvalZ : ((t.n 0).val : ℤ) = quantizeRapidity N θ := hbounds.2.2
  have hmul : N ≤ k * (t.n 0).val := by
    have hkN : (N : ℤ) = k * m := by rw [hm, Nat.cast_mul]
    have hle' : (m : ℤ) ≤ (t.n 0).val := by
      rw [hvalZ]; exact hfloor
    have : (N : ℤ) ≤ (k : ℤ) * (t.n 0).val := by
      rw [hkN]
      exact mul_le_mul_of_nonneg_left hle' (Nat.cast_nonneg _)
    exact_mod_cast this
  exact (windingTotal_pureBoost_ne_zero_iff k t hp).mpr hmul

/-! ### Modular amplification witness (non-vacuous) -/

/--
Non-vacuous discrete amplification certificate: a nonzero admissible seed whose
*modular* `k`-fold image remains admissible and wraps at least once.

Unlike `CoarseAmplificationWitness`, this type is inhabited for concrete
`(N,k)` (see `modularWitness_example`).
-/
structure ModularAmplificationWitness (N k : ℕ) [NeZero N] where
  t : AdmissibleClass N
  nonzero_seed : latticeMismatch t.val ≠ 0
  amplified_admissible : IsAdmissible (amplifyDiscrete k t.val)
  has_winding : windingTotal k t.val ≠ 0

private def exampleSeed : DiscreteTorsion 16 where
  n := fun a => match a with | 0 => (4 : ZMod 16) | _ => 0
  m := fun _ => 0

private theorem exampleSeed_admissible : IsAdmissible exampleSeed := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a; fin_cases a <;> decide

private theorem exampleSeed_mismatch : latticeMismatch exampleSeed ≠ 0 := by
  decide

private theorem example_amplified_admissible :
    IsAdmissible (amplifyDiscrete 5 exampleSeed) := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  fin_cases a <;> native_decide

private theorem example_has_winding : windingTotal 5 exampleSeed ≠ 0 := by
  native_decide

/-- Concrete inhabited example: `N = 16`, `k = 5`, pure boost `n₀ = 4`. -/
def modularWitness_example : ModularAmplificationWitness 16 5 where
  t := ⟨exampleSeed, exampleSeed_admissible⟩
  nonzero_seed := exampleSeed_mismatch
  amplified_admissible := example_amplified_admissible
  has_winding := example_has_winding

theorem ModularAmplificationWitness.nonempty_example :
    Nonempty (ModularAmplificationWitness 16 5) :=
  ⟨modularWitness_example⟩

/-- Pure-boost nonzero winding forces a nonzero lattice mismatch. -/
theorem latticeMismatch_ne_zero_of_winding_pureBoost (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) (hw : windingTotal k t ≠ 0) :
    latticeMismatch t ≠ 0 := by
  have hpos : N ≤ k * (t.n 0).val :=
    (windingTotal_pureBoost_ne_zero_iff k t hp).mp hw
  have hval : 0 < (t.n 0).val := by
    have hk : 0 < k * (t.n 0).val := Nat.lt_of_lt_of_le (NeZero.pos N) hpos
    exact Nat.pos_of_mul_pos_left hk
  have hn1 : t.n 1 = 0 := hp.1 1 (by decide)
  have hn2 : t.n 2 = 0 := hp.1 2 (by decide)
  have hm0 : t.m 0 = 0 := hp.2 0
  have hm1 : t.m 1 = 0 := hp.2 1
  have hm2 : t.m 2 = 0 := hp.2 2
  have hform : latticeMismatch t = ((t.n 0).val : ℤ) ^ 2 := by
    unfold latticeMismatch
    simp only [Fin.sum_univ_three, hn1, hn2, hm0, hm1, hm2, ZMod.val_zero]
    ring
  rw [hform]
  have hne : ((t.n 0).val : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hval
  exact pow_ne_zero 2 hne

/-- Assemble a modular witness from an already-checked pure-boost seed. -/
def modularWitness_of_pureBoost (k : ℕ) (t : DiscreteTorsion N)
    (_hp : IsPureBoostSeed t) (hadm : IsAdmissible t)
    (hamp : IsAdmissible (amplifyDiscrete k t))
    (hwind : windingTotal k t ≠ 0)
    (hne : latticeMismatch t ≠ 0) :
    ModularAmplificationWitness N k where
  t := ⟨t, hadm⟩
  nonzero_seed := hne
  amplified_admissible := hamp
  has_winding := hwind

/-- Convenience: derive `nonzero_seed` from pure-boost winding. -/
def modularWitness_of_pureBoost_winding (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) (hadm : IsAdmissible t)
    (hamp : IsAdmissible (amplifyDiscrete k t))
    (hwind : windingTotal k t ≠ 0) :
    ModularAmplificationWitness N k :=
  modularWitness_of_pureBoost k t hp hadm hamp hwind
    (latticeMismatch_ne_zero_of_winding_pureBoost k t hp hwind)

/-- A modular witness with nonzero winding is not continuously admissible after
real `k`-scaling — it cannot be fed to `continuous_amplification_contradiction`. -/
theorem ModularAmplificationWitness.not_admissible_real_scale
    {N k : ℕ} [NeZero N] (w : ModularAmplificationWitness N k) :
    ¬ IsAdmissibleContinuous
        (scaleTorsion (k : ℝ) (toTorsionParams w.t.val)) :=
  windingTotal_ne_zero_implies_not_admissible_scale k w.t.val w.has_winding

/--
Explicit residual gap label for modular bridges: "conformal / CGA gauge
admissibility" of a torsion configuration.

In this cycle it is **provisionally identified** with the PGA continuous
admissible cone `IsAdmissibleContinuous`.  A modular witness with nonzero
winding is never conformally admissible under this identification
(`not_admissible_real_scale`).  The 1D CGA probe investigates whether a
homogeneous null-cone gauge can replace this identification without collapsing
to the same obstruction.
-/
abbrev ConformalGaugeAdmissible (p : TorsionParams) : Prop :=
  IsAdmissibleContinuous p

end ModularAmplification

end DstDiophantine
