import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Framework.Lattice
import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Framework.Amplification
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.native false

/-!
# Modular torsional amplification with winding

Scaling on `(ℤ/Nℤ)⁶` records an integer winding. The live gap is that winding error, not the empty
coarse witness.
-/

namespace DstDiophantine

open Operations Discrete Amplification Invariant Framework Real MismatchAngle
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

theorem windingCoord_lt (k : ℕ) (x : ZMod N) (hk : 0 < k) :
    windingCoord k x < k := by
  unfold windingCoord
  have hN : 0 < N := NeZero.pos N
  have hval : x.val < N := ZMod.val_lt x
  rw [Nat.div_lt_iff_lt_mul hN]
  exact Nat.mul_lt_mul_of_pos_left hval hk

theorem windingCoord_pos_iff (k : ℕ) (x : ZMod N) :
    0 < windingCoord k x ↔ N ≤ k * x.val := by
  unfold windingCoord
  exact Nat.div_pos_iff.trans (and_iff_right (NeZero.pos N))

omit [NeZero N] in
theorem windingCoord_eq_zero_of_lt {N : ℕ} (k : ℕ) (x : ZMod N) (h : k * x.val < N) :
    windingCoord k x = 0 :=
  Nat.div_eq_of_lt h

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

private theorem coord_lt_of_two_mul_sum (k v s N : ℕ) [NeZero N]
    (h : 2 * k * s ≤ N) (hle : v ≤ s) : k * v < N := by
  omega

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
    have hbound := hfour a
    have hle : k * (t.n a).val ≤ k * ((t.n a).val + (t.m a).val) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have hboundNat : 2 * k * ((t.n a).val + (t.m a).val) ≤ N := by exact_mod_cast hfour a
    exact windingCoord_eq_zero_of_lt
      (coord_lt_of_two_mul_sum k (t.n a).val ((t.n a).val + (t.m a).val) N hboundNat hle)
  have hm : windingCoord k (t.m a) = 0 := by
    apply windingCoord_eq_zero_of_lt
    have hbound := hfour a
    have hle : k * (t.m a).val ≤ k * ((t.n a).val + (t.m a).val) :=
      Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
    have hboundNat : 2 * k * ((t.n a).val + (t.m a).val) ≤ N := by exact_mod_cast hfour a
    exact windingCoord_eq_zero_of_lt
      (coord_lt_of_two_mul_sum k (t.m a).val ((t.n a).val + (t.m a).val) N hboundNat hle)
  simp [hn, hm]
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

/-- Per-axis winding correction in the rapidity squared difference (`α²−β²` bookkeeping). -/
noncomputable def axisWindingError (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) : ℝ :=
  let α := (amplifiedParams k t).alpha a
  let β := (amplifiedParams k t).beta a
  let wn := (windingCoord k (t.n a) : ℝ)
  let wm := (windingCoord k (t.m a) : ℝ)
  (2 * α * (2 * Real.pi * wn) + (2 * Real.pi * wn) ^ 2) -
    (2 * β * (2 * Real.pi * wm) + (2 * Real.pi * wm) ^ 2)

/-- Same winding data as a correction to mismatch half-square sums (coefficient `1/4`). -/
noncomputable def axisMismatchHalfWindingError (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) : ℝ :=
  (1 / 4) * axisWindingError k t a

noncomputable def mismatchHalfWindingSqSum (k : ℕ) (t : DiscreteTorsion N) : ℝ :=
  ∑ a : Fin 3, axisMismatchHalfWindingError k t a

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

/-- Modular amplification adds a winding error, so `J(scale k p) = k² J(p)` fails. -/
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

theorem mismatchHalfWindingSqSum_eq (k : ℕ) (t : DiscreteTorsion N) :
    mismatchHalfWindingSqSum k t = (1 / 4) * ∑ a : Fin 3, axisWindingError k t a := by
  unfold mismatchHalfWindingSqSum axisMismatchHalfWindingError
  simp only [Fin.sum_univ_three]
  ring

/-- Primary scale law: mismatch half-square bookkeeping plus winding on the lattice. -/
theorem mismatch_half_sq_diff_scale_eq_amplified_add_winding
    (k : ℕ) (t : DiscreteTorsion N) :
    mismatchBoostHalfSqSum (scaleTorsion (k : ℝ) (toTorsionParams t)) -
        mismatchRotationHalfSqSum (scaleTorsion (k : ℝ) (toTorsionParams t)) =
      mismatchBoostHalfSqSum (amplifiedParams k t) -
          mismatchRotationHalfSqSum (amplifiedParams k t) +
        mismatchHalfWindingSqSum k t := by
  rw [mismatchHalfWindingSqSum_eq]
  have hJ := J_eq_mismatch_half_sq_diff (scaleTorsion (k : ℝ) (toTorsionParams t))
  have hJa := J_eq_mismatch_half_sq_diff (amplifiedParams k t)
  linarith [J_scale_eq_J_amplified_add_error k t, hJ, hJa]

theorem mismatch_sq_scale_primary (k : ℕ) (t : DiscreteTorsion N) :
    mismatchBoostHalfSqSum (scaleTorsion (k : ℝ) (toTorsionParams t)) -
        mismatchRotationHalfSqSum (scaleTorsion (k : ℝ) (toTorsionParams t)) =
      mismatchBoostHalfSqSum (amplifiedParams k t) -
          mismatchRotationHalfSqSum (amplifiedParams k t) +
        mismatchHalfWindingSqSum k t :=
  mismatch_half_sq_diff_scale_eq_amplified_add_winding k t

theorem J_scale_eq_amplified_add_winding_diagnostic (k : ℕ) (t : DiscreteTorsion N) :
    J (scaleTorsion (k : ℝ) (toTorsionParams t)) =
      J (amplifiedParams k t) + 2 * mismatchHalfWindingSqSum k t := by
  have hdiff := mismatch_sq_scale_primary k t
  have hJ := J_eq_mismatch_half_sq_diff (scaleTorsion (k : ℝ) (toTorsionParams t))
  have hJa := J_eq_mismatch_half_sq_diff (amplifiedParams k t)
  linarith

theorem J_scale_eq_J_amplified_add_error_via_mismatch (k : ℕ) (t : DiscreteTorsion N) :
    J (scaleTorsion (k : ℝ) (toTorsionParams t)) =
      J (amplifiedParams k t) + (1 / 2) * ∑ a : Fin 3, axisWindingError k t a := by
  rw [J_scale_eq_amplified_add_winding_diagnostic, mismatchHalfWindingSqSum_eq]
  ring

theorem mismatch_half_sq_diff_scale_eq_amplified_add_winding_pureBoost
    (k : ℕ) (t : DiscreteTorsion N) (hp : IsPureBoostSeed t) :
    mismatchBoostHalfSqSum (scaleTorsion (k : ℝ) (toTorsionParams t)) -
        mismatchRotationHalfSqSum (scaleTorsion (k : ℝ) (toTorsionParams t)) =
      mismatchBoostHalfSqSum (amplifiedParams k t) -
          mismatchRotationHalfSqSum (amplifiedParams k t) +
        axisMismatchHalfWindingError k t 0 := by
  rw [mismatch_half_sq_diff_scale_eq_amplified_add_winding k t]
  simp only [Fin.sum_univ_three, mismatchHalfWindingSqSum, axisMismatchHalfWindingError]
  have h1 := axisWindingError_pureBoost_of_ne_zero k t hp (by decide : (1 : Fin 3) ≠ 0)
  have h2 := axisWindingError_pureBoost_of_ne_zero k t hp (by decide : (2 : Fin 3) ≠ 0)
  simp [h1, h2]

theorem J_scale_mismatch_half_sq_diagnostic (k : ℕ) (t : DiscreteTorsion N) :
    mismatchBoostHalfSqSum (scaleTorsion (k : ℝ) (toTorsionParams t)) -
        mismatchRotationHalfSqSum (scaleTorsion (k : ℝ) (toTorsionParams t)) =
      (1 / 2) * J (scaleTorsion (k : ℝ) (toTorsionParams t)) := by
  linarith [J_eq_mismatch_half_sq_diff (scaleTorsion (k : ℝ) (toTorsionParams t))]

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

/-- A rapidity below `2π/k` has winding zero, so the balanced gap never winds. -/
theorem windingTotal_eq_zero_of_rapidity_lt (N k : ℕ) [NeZero N] (hk : 0 < k)
    (θ : ℝ) (h0 : 0 ≤ θ) (hlt : θ < 2 * Real.pi / k) :
    windingTotal k (pureBoostSeedOfRapidity N θ) = 0 := by
  set t := pureBoostSeedOfRapidity N θ
  have hp : IsPureBoostSeed t := pureBoostSeedOfRapidity_isPureBoost N θ
  have hθlt2π : θ < 2 * Real.pi := by
    have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (Nat.succ_le_of_lt hk)
    have hupper : 2 * Real.pi / k ≤ 2 * Real.pi := by
      have : 2 * Real.pi / k ≤ 2 * Real.pi / 1 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hk1
      simpa using this
    exact hlt.trans_le hupper
  have hbounds := quantizeRapidity_of_lt_two_pi N θ h0 hθlt2π
  have hfrac : θ * (N : ℝ) / (2 * Real.pi) < (N : ℝ) / k := by
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
    have hden : 0 < (2 * Real.pi : ℝ) := by positivity
    calc θ * (N : ℝ) / (2 * Real.pi)
        < (2 * Real.pi / k) * (N : ℝ) / (2 * Real.pi) :=
          div_lt_div_of_pos_right
            (mul_lt_mul_of_pos_right hlt (Nat.cast_pos.mpr (NeZero.pos N))) hden
      _ = (N : ℝ) / k := by field_simp [hk0]
  have hmul_lt : (k : ℝ) * ((t.n 0).val : ℝ) < (N : ℝ) := by
    have hvalZ : ((t.n 0).val : ℤ) = quantizeRapidity N θ := hbounds.2.2
    have hfloor_le : (quantizeRapidity N θ : ℝ) ≤
        θ * (N : ℝ) / (2 * Real.pi) := Int.floor_le _
    have : (k : ℝ) * (quantizeRapidity N θ : ℝ) < (N : ℝ) := by
      have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
      calc (k : ℝ) * (quantizeRapidity N θ : ℝ)
          ≤ (k : ℝ) * (θ * (N : ℝ) / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hfloor_le hkpos.le
        _ < (k : ℝ) * ((N : ℝ) / k) :=
            mul_lt_mul_of_pos_left hfrac hkpos
        _ = (N : ℝ) := by
          field_simp [ne_of_gt (Nat.cast_pos.mpr hk)]
    have hcast : ((t.n 0).val : ℝ) = (quantizeRapidity N θ : ℝ) := by
      exact_mod_cast hvalZ
    rwa [← hcast] at this
  have hnot : ¬ N ≤ k * (t.n 0).val := by
    intro hle
    have : (N : ℝ) ≤ (k : ℝ) * ((t.n 0).val : ℝ) := by exact_mod_cast hle
    exact not_le_of_gt hmul_lt this
  by_contra hne
  exact hnot ((windingTotal_pureBoost_ne_zero_iff k t hp).mp hne)

/-! ### Modular amplification witness (non-vacuous) -/

/-- Non-vacuous certificate: admissible seed, admissible modular image, and a wrap. -/
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

/-- Witness: `N = 16`, `k = 5`, pure boost `n₀ = 4`. -/
def modularWitness_example : ModularAmplificationWitness 16 5 where
  t := ⟨exampleSeed, exampleSeed_admissible⟩
  nonzero_seed := exampleSeed_mismatch
  amplified_admissible := example_amplified_admissible
  has_winding := example_has_winding

theorem ModularAmplificationWitness.nonempty_example :
    Nonempty (ModularAmplificationWitness 16 5) :=
  ⟨modularWitness_example⟩

theorem not_exists_modularWitness_of_rapidity_lt (N k : ℕ) [NeZero N] (hk : 0 < k)
    (θ : ℝ) (h0 : 0 ≤ θ) (hlt : θ < 2 * Real.pi / k)
    (hw : ∃ w : ModularAmplificationWitness N k,
      w.t.val = pureBoostSeedOfRapidity N θ) :
    False := by
  obtain ⟨w, heq⟩ := hw
  have hwind : windingTotal k (pureBoostSeedOfRapidity N θ) ≠ 0 := by
    simpa [heq] using w.has_winding
  exact hwind (windingTotal_eq_zero_of_rapidity_lt N k hk θ h0 hlt)

/-- The balanced gap `log 2 / m` never yields a modular winding witness. -/
theorem not_exists_modularWitness_of_balanced_gap (N m k : ℕ) [NeZero N]
    (hk : 0 < k)
    (hgap : Real.log 2 / (m : ℝ) < 2 * Real.pi / (k : ℝ))
    (hw : ∃ w : ModularAmplificationWitness N k,
      w.t.val = pureBoostSeedOfRapidity N (Real.log 2 / (m : ℝ))) :
    False := by
  have h0 : 0 ≤ Real.log 2 / (m : ℝ) :=
    div_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (Nat.cast_nonneg _)
  exact not_exists_modularWitness_of_rapidity_lt N k hk _ h0 hgap hw

/-- Nonzero winding and admissibility force `k ≥ 4`; factor `3` is vacuous. -/
theorem modularWitness_four_le {N k : ℕ} [NeZero N]
    (w : ModularAmplificationWitness N k) : 4 ≤ k := by
  have hadm := (AdmissibleClass.isAdmissible_iff_four_le w.t.val).mp w.t.property
  have hw : windingTotal k w.t.val ≠ 0 := w.has_winding
  have hex :
      ∃ a : Fin 3,
        0 < windingCoord k (w.t.val.n a) ∨ 0 < windingCoord k (w.t.val.m a) := by
    by_contra h
    push Not at h
    have hz : windingTotal k w.t.val = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      have ⟨hn, hm⟩ := h a
      simp [Nat.eq_zero_of_le_zero hn, Nat.eq_zero_of_le_zero hm]
    exact hw hz
  obtain ⟨a, hpos⟩ := hex
  cases hpos with
  | inl hn =>
    have hN : N ≤ k * (w.t.val.n a).val := (windingCoord_pos_iff k _).mp hn
    have h4 : 4 * ((w.t.val.n a).val + (w.t.val.m a).val) ≤ N := hadm a
    have hval : 0 < (w.t.val.n a).val := by
      have : 0 < k * (w.t.val.n a).val := Nat.lt_of_lt_of_le (NeZero.pos N) hN
      exact Nat.pos_of_mul_pos_left this
    have h4n : 4 * (w.t.val.n a).val ≤ N :=
      Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) h4
    have : 4 * (w.t.val.n a).val ≤ k * (w.t.val.n a).val := h4n.trans hN
    exact Nat.le_of_mul_le_mul_right this hval
  | inr hm =>
    have hN : N ≤ k * (w.t.val.m a).val := (windingCoord_pos_iff k _).mp hm
    have h4 : 4 * ((w.t.val.n a).val + (w.t.val.m a).val) ≤ N := hadm a
    have hval : 0 < (w.t.val.m a).val := by
      have : 0 < k * (w.t.val.m a).val := Nat.lt_of_lt_of_le (NeZero.pos N) hN
      exact Nat.pos_of_mul_pos_left this
    have h4m : 4 * (w.t.val.m a).val ≤ N :=
      Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) h4
    have : 4 * (w.t.val.m a).val ≤ k * (w.t.val.m a).val := h4m.trans hN
    exact Nat.le_of_mul_le_mul_right this hval

theorem modularWitness_empty_of_lt_four {N k : ℕ} [NeZero N] (hk : k < 4) :
    IsEmpty (ModularAmplificationWitness N k) :=
  ⟨fun w => Nat.not_lt.mpr (modularWitness_four_le w) hk⟩

theorem modularWitness_empty_of_eq_three {N : ℕ} [NeZero N] :
    IsEmpty (ModularAmplificationWitness N 3) :=
  modularWitness_empty_of_lt_four (by decide : (3 : ℕ) < 4)

theorem latticeMismatch_pureBoost (t : DiscreteTorsion N) (hp : IsPureBoostSeed t) :
    latticeMismatch t = ((t.n 0).val : ℤ) ^ 2 := by
  unfold latticeMismatch
  simp only [Fin.sum_univ_three, hp.1 1 (by decide), hp.1 2 (by decide),
    hp.2 0, hp.2 1, hp.2 2, ZMod.val_zero]
  ring

theorem latticeMismatch_ne_zero_of_winding_pureBoost (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) (hw : windingTotal k t ≠ 0) :
    latticeMismatch t ≠ 0 := by
  have hpos : N ≤ k * (t.n 0).val :=
    (windingTotal_pureBoost_ne_zero_iff k t hp).mp hw
  have hval : 0 < (t.n 0).val := by
    have hk : 0 < k * (t.n 0).val := Nat.lt_of_lt_of_le (NeZero.pos N) hpos
    exact Nat.pos_of_mul_pos_left hk
  rw [latticeMismatch_pureBoost t hp]
  exact pow_ne_zero 2 (by exact_mod_cast ne_of_gt hval)

theorem isAdmissible_of_pureBoost_n0_le (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) (h : 4 * (t.n 0).val ≤ N) :
    IsAdmissible t := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  fin_cases a
  · simpa [hp.2 0, ZMod.val_zero] using h
  · simp [hp.1 1 (by decide), hp.2 1, ZMod.val_zero]
  · simp [hp.1 2 (by decide), hp.2 2, ZMod.val_zero]

theorem isAdmissible_amplifyDiscrete_of_pureBoost_smul_n0
    (k : ℕ) (t : DiscreteTorsion N) (hp : IsPureBoostSeed t)
    (h0 : k • t.n 0 = 0) :
    IsAdmissible (amplifyDiscrete k t) := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  fin_cases a
  · simp [amplifyDiscrete_n, amplifyDiscrete_m, h0, hp.2 0, ZMod.val_zero]
  · simp [amplifyDiscrete_n, amplifyDiscrete_m, hp.1 1 (by decide), hp.2 1,
      ZMod.val_zero]
  · simp [amplifyDiscrete_n, amplifyDiscrete_m, hp.1 2 (by decide), hp.2 2,
      ZMod.val_zero]

/-- Assemble a modular witness from an already-checked pure-boost seed. -/
def modularWitness_of_pureBoost (k : ℕ) (t : DiscreteTorsion N)
    (hadm : IsAdmissible t)
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
  modularWitness_of_pureBoost k t hadm hamp hwind
    (latticeMismatch_ne_zero_of_winding_pureBoost k t hp hwind)

/-- A winding witness is not real-scale admissible. -/
theorem ModularAmplificationWitness.not_admissible_real_scale
    {N k : ℕ} [NeZero N] (w : ModularAmplificationWitness N k) :
    ¬ IsAdmissibleContinuous
        (scaleTorsion (k : ℝ) (toTorsionParams w.t.val)) :=
  windingTotal_ne_zero_implies_not_admissible_scale k w.t.val w.has_winding

/-- Alias of `IsAdmissibleContinuous`. -/
abbrev ConformalGaugeAdmissible (p : TorsionParams) : Prop :=
  IsAdmissibleContinuous p

end ModularAmplification

end DstDiophantine
