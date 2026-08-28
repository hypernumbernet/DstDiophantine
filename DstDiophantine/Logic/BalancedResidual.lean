import DstDiophantine.Logic.MotorProp
import DstDiophantine.Algebra.Amplification

/-!
# Phase 7r L3: balanced residual class

`BalancedResidualClass` packages `IsBalancedMassive` as the seat that
continuous / winding no-go miss. Mutually exclusive with window seeds
(pure hyperbolic, height in `(0,1)`). No `Theorems` import; no new arithmetic.
-/

namespace DstDiophantine

namespace Logic

open Admissible Amplification Invariant

/-- Label `T` with positive mass. Signed height alone conflates this with vacuum. -/
def BalancedResidualClass (a : Amplitude) : Prop :=
  a.IsBalancedMassive

theorem balancedResidualClass_iff_measure (a : Amplitude) :
    BalancedResidualClass a ↔ a.measure = 0 ∧ 0 < a.mass :=
  Amplitude.isBalancedMassive_iff a

theorem balancedAmplitude_mem_balancedResidualClass :
    BalancedResidualClass balancedAmplitude :=
  balancedAmplitude_isBalancedMassive

theorem vacuum_not_mem_balancedResidualClass :
    ¬ BalancedResidualClass vacuumAmplitude := by
  intro h
  exact (not_le.mpr h.2) (le_of_eq vacuumAmplitude_isVacuum.2)

/-! ### Window seeds (exclusive) -/

/-- Pure hyperbolic ray with height in `(0,1)` (boost-dominant, label `U`). -/
def IsWindowSeed (a : Amplitude) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧ a.params = pureHyperbolicRay t

theorem windowSeed_measure {a : Amplitude} {t : ℝ}
    (hp : a.params = pureHyperbolicRay t) :
    a.measure = t ^ 2 := by
  simp [Amplitude.measure, hp, JNormalized_pureHyperbolicRay]

theorem windowSeed_collapse_U {a : Amplitude} (h : IsWindowSeed a) :
    a.collapse = .U := by
  obtain ⟨t, ht0, ht1, hp⟩ := h
  have hmeas : a.measure = t ^ 2 := windowSeed_measure hp
  have h0 : 0 < a.measure := by rw [hmeas]; exact sq_pos_of_pos ht0
  have h1 : a.measure < 1 := by
    rw [hmeas]
    exact (sq_lt_one_iff_abs_lt_one t).mpr (by rwa [abs_of_nonneg (le_of_lt ht0)])
  exact (ofParams_eq_U_iff a.admissible).mpr ⟨h0, h1⟩

theorem windowSeed_not_mem_balancedResidualClass {a : Amplitude}
    (h : IsWindowSeed a) : ¬ BalancedResidualClass a := by
  intro hb
  have hU := windowSeed_collapse_U h
  have hT := hb.1
  rw [hU] at hT
  cases hT

noncomputable def halfWindowSeed : Amplitude :=
  ⟨pureHyperbolicRay (1 / 2),
    isAdmissibleContinuous_pureHyperbolicRay (by norm_num) (by norm_num)⟩

theorem halfWindowSeed_isWindowSeed : IsWindowSeed halfWindowSeed :=
  ⟨1 / 2, by norm_num, by norm_num, rfl⟩

theorem halfWindowSeed_not_balanced :
    ¬ BalancedResidualClass halfWindowSeed :=
  windowSeed_not_mem_balancedResidualClass halfWindowSeed_isWindowSeed

/-- Admissible scaling of a balanced seat keeps label `T`. -/
theorem balancedResidual_scale_stays_T {k : ℕ} (hk : 1 ≤ k)
    {a : Amplitude} (ha : BalancedResidualClass a)
    (h : IsAdmissibleContinuous (scaleTorsion (k : ℝ) a.params)) :
    (⟨scaleTorsion (k : ℝ) a.params, h⟩ : Amplitude).collapse = .T :=
  (scale_balancedMassive_stays_balanced hk ha h).1

end Logic

end DstDiophantine
