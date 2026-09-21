import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.Invariant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Dual-only control of the particle mismatch \(J\)

Kinematic identities on the admissible cone. An electromagnetic coupling,
a resonance frequency, a laboratory protocol, and helicity drive of \(J\)
are **not** derived.

## What is proved

* The formal jet \(\dot J=\sum_a(\alpha_a\dot\alpha_a-\beta_a\dot\beta_a)\).
  Dual-only motion (\(\dot\alpha=0\)) yields \(\dot J=-\sum\beta_a\dot\beta_a\).
  At \(\beta=0\) the first variation vanishes; a dual ray \(\beta=tv\)
  lowers \(J\) at second order.
* The admissible cone is convex. Affine dual interpolation between two
  admissible endpoints of equal usual rapidity stays admissible.
* On the dual wall \(\beta_a=\pi/2-\alpha_a\),
  \(J=\frac\pi2\sum_a(\alpha_a-\pi/4)\). Dual-only \(J\) cannot fall below
  that wall value. Dual-only shielding (\(J=0\)) is possible if and only
  if the wall is nonpositive, equivalently \(\sum\alpha_a\le 3\pi/4\).
  Dual-only repulsion (\(J<0\)) requires a strictly negative wall.
* Unconditionally \(J+M=\sum\alpha^2\) and \(M-J=\sum\beta^2\). Dual-only
  motion conserves \(J+M\); usual-only motion conserves \(M-J\). Every
  dual-only drop in \(J\) is paid for, one-for-one, by unsigned mass.
  Dual-only \(J=0\) therefore has unique mass \(\sum\alpha^2\), twice the
  pure-usual seed, and dual-only admissible \(J\) fills the closed
  interval from the wall up to that seed.
* The balanced target \(\beta=\alpha\) lies in the cone iff
  \(\alpha_a\le\pi/4\) on every axis, which is strictly stronger than
  dual-only shielding. A single-axis usual seed with
  \(\pi/4<\alpha\le\pi/2\) has a strictly negative wall, so dual-only
  \(J=0\) exists by cross-axis compensation, while \(\beta=\alpha\) on
  that axis leaves the cone. Two silent axes give two distinct shields
  of the same mass. When the wall vanishes, the shield is unique: the
  wall itself. Dual-only conserves \(\sum\alpha^2\), so the vacuum
  \(M=0\) is unreachable unless the usual seed already vanishes.
* When the wall is positive, mixed control still reaches a massive
  shield by unwinding each usual rapidity to at most \(\pi/4\) and
  matching the dual angle. Uniform \(\alpha=\pi/6\) admits dual-only
  shielding and repulsion; uniform \(\alpha=\pi/3\) cannot reach
  \(J=0\) dual-only, but the mixed unwind does.
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-! ### Axis density and the formal jet -/

/-- One-axis contribution to \(J=\tfrac12\sum(\alpha^2-\beta^2)\). -/
noncomputable def JAxis (α β : ℝ) : ℝ :=
  (1 / 2) * (α ^ 2 - β ^ 2)

theorem J_eq_sum_JAxis (p : TorsionParams) :
    J p = ∑ a : Fin 3, JAxis (p.alpha a) (p.beta a) := by
  rw [J_coef]
  simp only [JAxis, Fin.sum_univ_three]
  ring

/-- Formal \(\dot J\) along a jet \((p,\dot p)\). -/
def JDot (p pdot : TorsionParams) : ℝ :=
  ∑ a : Fin 3, (p.alpha a * pdot.alpha a - p.beta a * pdot.beta a)

theorem JDot_dual_only (p pdot : TorsionParams)
    (hα : ∀ a, pdot.alpha a = 0) :
    JDot p pdot = -∑ a : Fin 3, p.beta a * pdot.beta a := by
  unfold JDot
  simp [hα, Fin.sum_univ_three]

theorem JDot_dual_only_zero_of_beta_zero (p pdot : TorsionParams)
    (hα : ∀ a, pdot.alpha a = 0) (hβ : ∀ a, p.beta a = 0) :
    JDot p pdot = 0 := by
  rw [JDot_dual_only p pdot hα]
  simp [hβ]

/-! ### Dual ray from a pure usual seed: first order vanishes -/

/-- Dual-only ray \(\alpha\) fixed, \(\beta=tv\). -/
def dualRay (α v : Fin 3 → ℝ) (t : ℝ) : TorsionParams where
  alpha := α
  beta := fun a => t * v a

theorem J_dualRay (α v : Fin 3 → ℝ) (t : ℝ) :
    J (dualRay α v t) =
      J { alpha := α, beta := fun _ => 0 } -
        (t ^ 2 / 2) * ∑ a : Fin 3, v a ^ 2 := by
  rw [J_coef, J_coef]
  simp only [dualRay, Fin.sum_univ_three]
  ring

theorem J_dualRay_lt_seed {α v : Fin 3 → ℝ} {t : ℝ}
    (hv : ∑ a : Fin 3, v a ^ 2 ≠ 0) (ht : t ≠ 0) :
    J (dualRay α v t) < J { alpha := α, beta := fun _ => 0 } := by
  rw [J_dualRay]
  have hs : 0 < ∑ a : Fin 3, v a ^ 2 := by
    have hnn : 0 ≤ ∑ a : Fin 3, v a ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact lt_of_le_of_ne hnn hv.symm
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have : 0 < (t ^ 2 / 2) * ∑ a : Fin 3, v a ^ 2 := by positivity
  linarith

/-! ### Dual wall -/

/-- Maximal dual angle on an axis of usual rapidity \(\alpha\). -/
noncomputable def dualWall (α : ℝ) : ℝ :=
  Real.pi / 2 - α

theorem JAxis_wall (α : ℝ) :
    JAxis α (dualWall α) = (Real.pi / 2) * (α - Real.pi / 4) := by
  unfold JAxis dualWall
  ring

/-- Dual wall of a usual-rapidity triple: \(\beta_a=\pi/2-\alpha_a\). -/
noncomputable def dualWallParams (p : TorsionParams) : TorsionParams where
  alpha := p.alpha
  beta := fun a => dualWall (p.alpha a)

theorem J_dualWallParams (p : TorsionParams) :
    J (dualWallParams p) =
      (Real.pi / 2) * ∑ a : Fin 3, (p.alpha a - Real.pi / 4) := by
  rw [J_eq_sum_JAxis]
  simp only [dualWallParams, JAxis_wall, Fin.sum_univ_three]
  ring

theorem J_dualWallParams_eq_sum_alpha (p : TorsionParams) :
    J (dualWallParams p) =
      (Real.pi / 2) * (∑ a : Fin 3, p.alpha a - 3 * Real.pi / 4) := by
  rw [J_dualWallParams]
  simp only [Fin.sum_univ_three]
  ring

theorem J_dualWall_nonpos_iff (p : TorsionParams) :
    J (dualWallParams p) ≤ 0 ↔ ∑ a : Fin 3, p.alpha a ≤ 3 * Real.pi / 4 := by
  rw [J_dualWallParams_eq_sum_alpha]
  have hπ : 0 < Real.pi / 2 := by positivity
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem J_dualWall_neg_iff (p : TorsionParams) :
    J (dualWallParams p) < 0 ↔ ∑ a : Fin 3, p.alpha a < 3 * Real.pi / 4 := by
  rw [J_dualWallParams_eq_sum_alpha]
  have hπ : 0 < Real.pi / 2 := by positivity
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem isAdmissibleContinuous_dualWallParams {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    IsAdmissibleContinuous (dualWallParams p) := by
  intro a
  have hα := admissibleContinuous_alpha_nonneg p h a
  have hαle := admissibleContinuous_alpha_le_half_pi p h a
  refine ⟨hα, ?_, ?_⟩
  · unfold dualWallParams dualWall
    linarith
  · unfold dualWallParams dualWall
    linarith

theorem admissibleContinuous_beta_le_dualWall {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.beta a ≤ dualWall (p.alpha a) := by
  have := admissibleContinuous_sum_le p h a
  unfold dualWall
  linarith

/-! ### Affine dual interpolation -/

/-- Usual rapidity held fixed; dual angles interpolated. -/
def dualInterp (p : TorsionParams) (β' : Fin 3 → ℝ) (t : ℝ) : TorsionParams where
  alpha := p.alpha
  beta := fun a => (1 - t) * p.beta a + t * β' a

@[simp] theorem dualInterp_alpha (p : TorsionParams) (β' : Fin 3 → ℝ) (t : ℝ)
    (a : Fin 3) :
    (dualInterp p β' t).alpha a = p.alpha a :=
  rfl

@[simp] theorem dualInterp_beta (p : TorsionParams) (β' : Fin 3 → ℝ) (t : ℝ)
    (a : Fin 3) :
    (dualInterp p β' t).beta a = (1 - t) * p.beta a + t * β' a :=
  rfl

theorem torsionParams_ext {p q : TorsionParams}
    (hα : p.alpha = q.alpha) (hβ : p.beta = q.beta) : p = q := by
  rcases p with ⟨α, β⟩
  rcases q with ⟨α', β'⟩
  simp at hα hβ
  simp [hα, hβ]

theorem dualInterp_zero (p : TorsionParams) (β' : Fin 3 → ℝ) :
    dualInterp p β' 0 = p := by
  refine torsionParams_ext rfl ?_
  funext a
  simp [dualInterp]

theorem dualInterp_one (p : TorsionParams) (β' : Fin 3 → ℝ) :
    dualInterp p β' 1 = { alpha := p.alpha, beta := β' } := by
  refine torsionParams_ext rfl ?_
  funext a
  simp [dualInterp]

private theorem combo_nonneg {x y t : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 - t) * x + t * y :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hx) (mul_nonneg ht0 hy)

private theorem combo_sum_le {α β β' t C : ℝ}
    (h : α + β ≤ C) (h' : α + β' ≤ C)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    α + ((1 - t) * β + t * β') ≤ C := by
  have : α + ((1 - t) * β + t * β') = (1 - t) * (α + β) + t * (α + β') := by
    ring
  rw [this]
  calc (1 - t) * (α + β) + t * (α + β')
      ≤ (1 - t) * C + t * C :=
        add_le_add
          (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left h' ht0)
    _ = C := by ring

/-- The admissible cone is convex along dual interpolation of equal usual
rapidity. -/
theorem isAdmissibleContinuous_dualInterp {p : TorsionParams} {β' : Fin 3 → ℝ}
    {t : ℝ} (hp : IsAdmissibleContinuous p)
    (hβ' : IsAdmissibleContinuous { alpha := p.alpha, beta := β' })
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsAdmissibleContinuous (dualInterp p β' t) := by
  intro a
  have hpα := (hp a).1
  have hpβ := (hp a).2.1
  have hpsum := (hp a).2.2
  have hβ'β := (hβ' a).2.1
  have hβ'sum := (hβ' a).2.2
  refine ⟨hpα, combo_nonneg hpβ hβ'β ht0 ht1, ?_⟩
  simpa [dualInterp] using combo_sum_le hpsum hβ'sum ht0 ht1

/-- Dual-only \(J\) is nonincreasing along increasing dual angles. -/
theorem J_dualInterp_anti {p : TorsionParams} {β' : Fin 3 → ℝ} {t s : ℝ}
    (hβ : ∀ a, 0 ≤ p.beta a) (hmono : ∀ a, p.beta a ≤ β' a)
    (ht0 : 0 ≤ t) (hts : t ≤ s) :
    J (dualInterp p β' s) ≤ J (dualInterp p β' t) := by
  rw [J_eq_sum_JAxis, J_eq_sum_JAxis]
  refine Finset.sum_le_sum fun a _ => ?_
  unfold JAxis dualInterp
  set βt := (1 - t) * p.beta a + t * β' a
  set βs := (1 - s) * p.beta a + s * β' a
  have hge : βt ≤ βs := by
    have hdiff : βs - βt = (s - t) * (β' a - p.beta a) := by ring
    have : 0 ≤ βs - βt := by
      rw [hdiff]
      exact mul_nonneg (sub_nonneg.mpr hts) (sub_nonneg.mpr (hmono a))
    linarith
  have hβt_nn : 0 ≤ βt := by
    have hdiff : βt - p.beta a = t * (β' a - p.beta a) := by ring
    have : 0 ≤ βt - p.beta a := by
      rw [hdiff]
      exact mul_nonneg ht0 (sub_nonneg.mpr (hmono a))
    linarith [hβ a]
  have hsq : βt ^ 2 ≤ βs ^ 2 := pow_le_pow_left₀ hβt_nn hge 2
  linarith

/-! ### Dual-only lower bound is the wall -/

def zeroDual (p : TorsionParams) : TorsionParams where
  alpha := p.alpha
  beta := fun _ => 0

theorem dualRay_zero (α v : Fin 3 → ℝ) :
    dualRay α v 0 = zeroDual { alpha := α, beta := v } := by
  refine torsionParams_ext rfl ?_
  funext a
  simp [dualRay, zeroDual]

theorem isAdmissibleContinuous_zeroDual {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    IsAdmissibleContinuous (zeroDual p) := by
  intro a
  refine ⟨(h a).1, by simp [zeroDual], ?_⟩
  simp [zeroDual]
  linarith [(h a).2.2, (h a).2.1]

theorem J_le_zeroDual (p : TorsionParams) :
    J p ≤ J (zeroDual p) := by
  rw [J_eq_sum_JAxis, J_eq_sum_JAxis]
  refine Finset.sum_le_sum fun a _ => ?_
  unfold JAxis zeroDual
  have : 0 ≤ p.beta a ^ 2 := sq_nonneg _
  linarith

theorem zeroDual_eq_of_alpha {p q : TorsionParams} (hα : q.alpha = p.alpha) :
    zeroDual q = zeroDual p := by
  refine torsionParams_ext hα ?_
  funext a
  simp [zeroDual]

theorem mass_zeroDual (p : TorsionParams) :
    mass (zeroDual p) = (1 / 2) * ∑ a : Fin 3, p.alpha a ^ 2 := by
  rw [mass_coef]
  simp only [zeroDual, Fin.sum_univ_three]
  ring

theorem J_zeroDual_eq_mass (p : TorsionParams) :
    J (zeroDual p) = mass (zeroDual p) :=
  J_eq_mass_of_forall_beta_eq_zero fun _ => rfl

theorem dual_only_conserves_J_add_mass {p q : TorsionParams}
    (hα : q.alpha = p.alpha) :
    J q + mass q = J p + mass p := by
  rw [J_add_mass, J_add_mass, hα]

theorem usual_only_conserves_mass_sub_J {p q : TorsionParams}
    (hβ : q.beta = p.beta) :
    mass q - J q = mass p - J p := by
  rw [mass_sub_J, mass_sub_J, hβ]

theorem J_dual_only_le_zeroDual {p q : TorsionParams}
    (hα : q.alpha = p.alpha) :
    J q ≤ J (zeroDual p) := by
  rw [← zeroDual_eq_of_alpha hα]
  exact J_le_zeroDual q

/-- Dual-only configurations cannot undercut the wall value of \(J\). -/
theorem J_dual_only_ge_wall {p q : TorsionParams}
    (hα : q.alpha = p.alpha) (hq : IsAdmissibleContinuous q) :
    J (dualWallParams p) ≤ J q := by
  rw [J_eq_sum_JAxis, J_eq_sum_JAxis]
  refine Finset.sum_le_sum fun a _ => ?_
  unfold JAxis dualWallParams
  have hβnn := admissibleContinuous_beta_nonneg q hq a
  have hβle : q.beta a ≤ dualWall (p.alpha a) := by
    have := admissibleContinuous_beta_le_dualWall hq a
    rwa [hα] at this
  have hsq : q.beta a ^ 2 ≤ dualWall (p.alpha a) ^ 2 :=
    pow_le_pow_left₀ hβnn hβle 2
  simp [hα]
  linarith

theorem J_dual_only_mem_interval {p q : TorsionParams}
    (hα : q.alpha = p.alpha) (hq : IsAdmissibleContinuous q) :
    J (dualWallParams p) ≤ J q ∧ J q ≤ J (zeroDual p) :=
  ⟨J_dual_only_ge_wall hα hq, J_dual_only_le_zeroDual hα⟩

/-! ### Equal-scale shielding target -/

def equalScaleOf (p : TorsionParams) : TorsionParams where
  alpha := p.alpha
  beta := p.alpha

theorem J_equalScaleOf (p : TorsionParams) : J (equalScaleOf p) = 0 := by
  rw [J_coef]
  simp [equalScaleOf]

theorem mass_equalScaleOf (p : TorsionParams) :
    mass (equalScaleOf p) = ∑ a : Fin 3, p.alpha a ^ 2 := by
  rw [mass_coef]
  simp only [equalScaleOf, Fin.sum_univ_three]
  ring

theorem isAdmissibleContinuous_equalScaleOf_iff {p : TorsionParams}
    (hα : ∀ a, 0 ≤ p.alpha a) :
    IsAdmissibleContinuous (equalScaleOf p) ↔ ∀ a, p.alpha a ≤ Real.pi / 4 := by
  constructor
  · intro h a
    have hsum := (h a).2.2
    simp only [equalScaleOf] at hsum
    linarith
  · intro h a
    refine ⟨hα a, hα a, ?_⟩
    simp only [equalScaleOf]
    linarith [h a]

/-! ### Existence of a dual-only shield when the wall is nonpositive -/

def sumAlphaSq (p : TorsionParams) : ℝ :=
  ∑ a : Fin 3, p.alpha a ^ 2

noncomputable def sumWallSq (p : TorsionParams) : ℝ :=
  ∑ a : Fin 3, dualWall (p.alpha a) ^ 2

theorem J_dualWall_eq_half_diff (p : TorsionParams) :
    J (dualWallParams p) = (1 / 2) * (sumAlphaSq p - sumWallSq p) := by
  rw [J_coef]
  simp only [dualWallParams, sumAlphaSq, sumWallSq, Fin.sum_univ_three]
  ring

theorem sumAlphaSq_eq_J_add_mass (p : TorsionParams) :
    sumAlphaSq p = J p + mass p :=
  (J_add_mass p).symm

theorem J_zeroDual_eq_half_sumAlphaSq (p : TorsionParams) :
    J (zeroDual p) = (1 / 2) * sumAlphaSq p := by
  rw [J_zeroDual_eq_mass, mass_zeroDual, sumAlphaSq]

/-- Dual interpolation from \(\beta=0\) to the wall. -/
noncomputable def dualShieldInterp (p : TorsionParams) (t : ℝ) : TorsionParams :=
  dualInterp (zeroDual p) (fun a => dualWall (p.alpha a)) t

theorem J_dualShieldInterp (p : TorsionParams) (t : ℝ) :
    J (dualShieldInterp p t) =
      (1 / 2) * (sumAlphaSq p - t ^ 2 * sumWallSq p) := by
  rw [J_coef]
  simp only [dualShieldInterp, dualInterp, zeroDual, sumAlphaSq, sumWallSq,
    Fin.sum_univ_three]
  ring

/-- Vanishing wall squares would force every \(\alpha_a=\pi/2\), hence a
strictly positive wall value of \(J\). -/
theorem sumWallSq_pos_of_wall_nonpos {p : TorsionParams}
    (h : J (dualWallParams p) ≤ 0) :
    0 < sumWallSq p := by
  have hnn : 0 ≤ sumWallSq p := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine lt_of_le_of_ne hnn ?_
  intro h0
  have hSw0 : ∑ a : Fin 3, dualWall (p.alpha a) ^ 2 = 0 := by
    simpa [sumWallSq] using h0.symm
  have hα : ∀ a, p.alpha a = Real.pi / 2 := by
    intro a
    have hnnW : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        0 ≤ dualWall (p.alpha i) ^ 2 := fun _ _ => sq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnnW).mp hSw0 a (Finset.mem_univ a)
    have hw : dualWall (p.alpha a) = 0 := sq_eq_zero_iff.mp this
    unfold dualWall at hw
    linarith
  have hJ : J (dualWallParams p) = 3 * Real.pi ^ 2 / 8 := by
    rw [J_dualWallParams]
    simp only [hα, Fin.sum_univ_three]
    ring
  have hpos : 0 < (3 : ℝ) * Real.pi ^ 2 / 8 := by
    have hπ : 0 < Real.pi := Real.pi_pos
    positivity
  linarith

/-- Time parameter that lands on \(J=0\) along the zero-to-wall dual ray. -/
noncomputable def dualShieldT (p : TorsionParams) : ℝ :=
  Real.sqrt (sumAlphaSq p / sumWallSq p)

theorem dualShieldT_nonneg (p : TorsionParams) :
    0 ≤ dualShieldT p :=
  Real.sqrt_nonneg _

theorem dualShieldT_le_one {p : TorsionParams}
    (h : J (dualWallParams p) ≤ 0) (hSw : sumWallSq p ≠ 0) :
    dualShieldT p ≤ 1 := by
  unfold dualShieldT
  have hSα : 0 ≤ sumAlphaSq p := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSwN : 0 ≤ sumWallSq p := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hle : sumAlphaSq p ≤ sumWallSq p := by
    have := J_dualWall_eq_half_diff p
    linarith
  have hquot : sumAlphaSq p / sumWallSq p ≤ 1 := by
    exact (div_le_one (lt_of_le_of_ne hSwN hSw.symm)).mpr hle
  have hquot_nn : 0 ≤ sumAlphaSq p / sumWallSq p := div_nonneg hSα hSwN
  rw [Real.sqrt_le_iff]
  constructor
  · exact zero_le_one
  · simpa using hquot

theorem J_dualShieldInterp_at_T {p : TorsionParams}
    (h : J (dualWallParams p) ≤ 0) :
    J (dualShieldInterp p (dualShieldT p)) = 0 := by
  have hSw : 0 < sumWallSq p := sumWallSq_pos_of_wall_nonpos h
  rw [J_dualShieldInterp]
  unfold dualShieldT
  have hSα : 0 ≤ sumAlphaSq p := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hquot : 0 ≤ sumAlphaSq p / sumWallSq p := div_nonneg hSα hSw.le
  rw [Real.sq_sqrt hquot]
  have : sumAlphaSq p / sumWallSq p * sumWallSq p = sumAlphaSq p :=
    div_mul_cancel₀ _ hSw.ne'
  rw [this, sub_self, mul_zero]

theorem isAdmissibleContinuous_dualShieldInterp_at_T {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (h : J (dualWallParams p) ≤ 0) :
    IsAdmissibleContinuous (dualShieldInterp p (dualShieldT p)) := by
  have hSw : 0 < sumWallSq p := sumWallSq_pos_of_wall_nonpos h
  refine isAdmissibleContinuous_dualInterp
    (isAdmissibleContinuous_zeroDual hp) ?_ (dualShieldT_nonneg p)
    (dualShieldT_le_one h hSw.ne')
  simpa [zeroDual, dualWallParams] using isAdmissibleContinuous_dualWallParams hp

/-- Dual-only shielding exists precisely when the wall is nonpositive. -/
theorem exists_dual_only_J_eq_zero {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (h : J (dualWallParams p) ≤ 0) :
    ∃ q : TorsionParams,
      q.alpha = p.alpha ∧ IsAdmissibleContinuous q ∧ J q = 0 :=
  ⟨dualShieldInterp p (dualShieldT p), rfl,
    isAdmissibleContinuous_dualShieldInterp_at_T hp h,
    J_dualShieldInterp_at_T h⟩

theorem not_dual_only_J_eq_zero_of_wall_pos {p q : TorsionParams}
    (hα : q.alpha = p.alpha) (hq : IsAdmissibleContinuous q)
    (hwall : 0 < J (dualWallParams p)) :
    0 < J q :=
  lt_of_lt_of_le hwall (J_dual_only_ge_wall hα hq)

theorem exists_dual_only_J_lt_zero {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (h : J (dualWallParams p) < 0) :
    ∃ q : TorsionParams,
      q.alpha = p.alpha ∧ IsAdmissibleContinuous q ∧ J q < 0 :=
  ⟨dualWallParams p, rfl, isAdmissibleContinuous_dualWallParams hp, h⟩

/-! ### Unsigned-mass cost of a dual-only shield -/

theorem mass_eq_sum_alpha_of_J_eq_zero {p : TorsionParams} (hJ : J p = 0) :
    mass p = ∑ a : Fin 3, p.alpha a ^ 2 := by
  have := J_add_mass p
  linarith

theorem mass_dual_only_of_J_eq_zero {p q : TorsionParams}
    (hα : q.alpha = p.alpha) (hJ : J q = 0) :
    mass q = ∑ a : Fin 3, p.alpha a ^ 2 := by
  rw [mass_eq_sum_alpha_of_J_eq_zero hJ, hα]

/-- Every dual-only shield from a given usual seed has the same unsigned
mass, twice the pure-usual value. -/
theorem mass_eq_two_zeroDual_of_dual_only_J_eq_zero {p q : TorsionParams}
    (hα : q.alpha = p.alpha) (hJ : J q = 0) :
    mass q = 2 * mass (zeroDual p) := by
  have hM := mass_dual_only_of_J_eq_zero hα hJ
  have h0 := mass_zeroDual p
  linarith

/-! ### Dual-only \(J\) fills the wall-to-seed interval -/

noncomputable def dualTargetT (p : TorsionParams) (c : ℝ) : ℝ :=
  Real.sqrt ((sumAlphaSq p - 2 * c) / sumWallSq p)

theorem dualTargetT_nonneg (p : TorsionParams) (c : ℝ) :
    0 ≤ dualTargetT p c :=
  Real.sqrt_nonneg _

private theorem dualTarget_num_nonneg {p : TorsionParams} {c : ℝ}
    (hc' : c ≤ J (zeroDual p)) :
    0 ≤ sumAlphaSq p - 2 * c := by
  have := J_zeroDual_eq_half_sumAlphaSq p
  linarith

private theorem dualTarget_num_le_wall {p : TorsionParams} {c : ℝ}
    (hc : J (dualWallParams p) ≤ c) :
    sumAlphaSq p - 2 * c ≤ sumWallSq p := by
  have := J_dualWall_eq_half_diff p
  linarith

theorem dualTargetT_le_one {p : TorsionParams} {c : ℝ}
    (hSw : sumWallSq p ≠ 0)
    (hc : J (dualWallParams p) ≤ c) (hc' : c ≤ J (zeroDual p)) :
    dualTargetT p c ≤ 1 := by
  unfold dualTargetT
  have hSwN : 0 ≤ sumWallSq p := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSwPos : 0 < sumWallSq p := lt_of_le_of_ne hSwN hSw.symm
  have hle := dualTarget_num_le_wall hc
  have hquot : (sumAlphaSq p - 2 * c) / sumWallSq p ≤ 1 :=
    (div_le_one hSwPos).mpr hle
  have hnum := dualTarget_num_nonneg hc'
  rw [Real.sqrt_le_iff]
  exact ⟨zero_le_one, by simpa [hnum] using hquot⟩

theorem J_dualShieldInterp_at_target {p : TorsionParams} {c : ℝ}
    (hSw : 0 < sumWallSq p)
    (_hc : J (dualWallParams p) ≤ c) (hc' : c ≤ J (zeroDual p)) :
    J (dualShieldInterp p (dualTargetT p c)) = c := by
  rw [J_dualShieldInterp]
  unfold dualTargetT
  have hnum := dualTarget_num_nonneg hc'
  have hquot : 0 ≤ (sumAlphaSq p - 2 * c) / sumWallSq p :=
    div_nonneg hnum hSw.le
  rw [Real.sq_sqrt hquot]
  have hcancel :
      (sumAlphaSq p - 2 * c) / sumWallSq p * sumWallSq p =
        sumAlphaSq p - 2 * c :=
    div_mul_cancel₀ _ hSw.ne'
  rw [hcancel]
  ring

theorem isAdmissibleContinuous_dualShieldInterp_at_target {p : TorsionParams}
    {c : ℝ} (hp : IsAdmissibleContinuous p) (hSw : 0 < sumWallSq p)
    (hc : J (dualWallParams p) ≤ c) (hc' : c ≤ J (zeroDual p)) :
    IsAdmissibleContinuous (dualShieldInterp p (dualTargetT p c)) := by
  refine isAdmissibleContinuous_dualInterp
    (isAdmissibleContinuous_zeroDual hp) ?_ (dualTargetT_nonneg p c)
    (dualTargetT_le_one hSw.ne' hc hc')
  simpa [zeroDual, dualWallParams] using isAdmissibleContinuous_dualWallParams hp

theorem J_dualWall_eq_zeroDual_of_sumWallSq_eq_zero {p : TorsionParams}
    (h : sumWallSq p = 0) :
    J (dualWallParams p) = J (zeroDual p) := by
  rw [J_dualWall_eq_half_diff, J_zeroDual_eq_half_sumAlphaSq, h, sub_zero]

/-- Dual-only admissible \(J\) attains every value between the wall and
the pure-usual seed. -/
theorem exists_dual_only_J_eq {p : TorsionParams} {c : ℝ}
    (hp : IsAdmissibleContinuous p)
    (hc : J (dualWallParams p) ≤ c) (hc' : c ≤ J (zeroDual p)) :
    ∃ q : TorsionParams,
      q.alpha = p.alpha ∧ IsAdmissibleContinuous q ∧ J q = c := by
  by_cases hSw : sumWallSq p = 0
  · have hEq := J_dualWall_eq_zeroDual_of_sumWallSq_eq_zero hSw
    have hc0 : c = J (zeroDual p) := le_antisymm hc' (hEq ▸ hc)
    exact ⟨zeroDual p, rfl, isAdmissibleContinuous_zeroDual hp, hc0.symm⟩
  · have hne : sumWallSq p ≠ 0 := hSw
    have hpos : 0 < sumWallSq p :=
      lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) hne.symm
    refine ⟨dualShieldInterp p (dualTargetT p c), rfl, ?_, ?_⟩
    · exact isAdmissibleContinuous_dualShieldInterp_at_target hp hpos hc hc'
    · exact J_dualShieldInterp_at_target hpos hc hc'

/-! ### Uniform examples \(\alpha=\pi/6\) and \(\alpha=\pi/3\) -/

def uniformTorsion (α β : ℝ) : TorsionParams where
  alpha := fun _ => α
  beta := fun _ => β

theorem isAdmissibleContinuous_uniform {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ Real.pi / 2) :
    IsAdmissibleContinuous (uniformTorsion α β) := fun _ => ⟨hα, hβ, hsum⟩

theorem J_uniform (α β : ℝ) :
    J (uniformTorsion α β) = (3 / 2) * (α ^ 2 - β ^ 2) := by
  rw [J_coef]
  simp [uniformTorsion]
  ring

theorem J_uniform_wall (α : ℝ) :
    J (dualWallParams (uniformTorsion α 0)) =
      (3 * Real.pi / 2) * (α - Real.pi / 4) := by
  rw [J_dualWallParams]
  simp [uniformTorsion]
  ring

theorem pi_div_six_lt_pi_div_four : Real.pi / 6 < Real.pi / 4 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem pi_div_four_lt_pi_div_three : Real.pi / 4 < Real.pi / 3 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem pi_div_three_le_pi_div_two : Real.pi / 3 ≤ Real.pi / 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem uniform_pi_div_six_admissible :
    IsAdmissibleContinuous (uniformTorsion (Real.pi / 6) 0) :=
  isAdmissibleContinuous_uniform (by positivity) le_rfl (by
    have hπ : 0 < Real.pi := Real.pi_pos
    nlinarith)

theorem uniform_pi_div_six_equalScale_admissible :
    IsAdmissibleContinuous (equalScaleOf (uniformTorsion (Real.pi / 6) 0)) := by
  refine (isAdmissibleContinuous_equalScaleOf_iff ?_).mpr ?_
  · intro a
    simp only [uniformTorsion]
    positivity
  · intro a
    simp only [uniformTorsion]
    exact le_of_lt pi_div_six_lt_pi_div_four

theorem uniform_pi_div_six_shields :
    J (equalScaleOf (uniformTorsion (Real.pi / 6) 0)) = 0 :=
  J_equalScaleOf _

theorem uniform_pi_div_six_massive :
    0 < mass (equalScaleOf (uniformTorsion (Real.pi / 6) 0)) := by
  rw [mass_equalScaleOf]
  simp only [uniformTorsion, Fin.sum_univ_three]
  have hπ : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem uniform_pi_div_six_wall_neg :
    J (dualWallParams (uniformTorsion (Real.pi / 6) 0)) < 0 := by
  rw [J_uniform_wall]
  have hπ : 0 < Real.pi := Real.pi_pos
  nlinarith [pi_div_six_lt_pi_div_four]

theorem uniform_pi_div_three_admissible :
    IsAdmissibleContinuous (uniformTorsion (Real.pi / 3) 0) :=
  isAdmissibleContinuous_uniform (by positivity) le_rfl (by
    have hπ : 0 < Real.pi := Real.pi_pos
    nlinarith)

theorem uniform_pi_div_three_equalScale_not_admissible :
    ¬ IsAdmissibleContinuous (equalScaleOf (uniformTorsion (Real.pi / 3) 0)) := by
  intro h
  have := (isAdmissibleContinuous_equalScaleOf_iff
    (fun a => by simp only [uniformTorsion]; positivity)).mp h 0
  simp only [uniformTorsion] at this
  exact (not_le_of_gt pi_div_four_lt_pi_div_three) this

theorem uniform_pi_div_three_wall_pos :
    0 < J (dualWallParams (uniformTorsion (Real.pi / 3) 0)) := by
  rw [J_uniform_wall]
  have hπ : 0 < Real.pi := Real.pi_pos
  nlinarith [pi_div_four_lt_pi_div_three]

/-- A uniform usual boost \(\alpha=\pi/3\) cannot be dual-only shielded. -/
theorem uniform_pi_div_three_no_dual_shield {q : TorsionParams}
    (hα : ∀ a, q.alpha a = Real.pi / 3)
    (hq : IsAdmissibleContinuous q) :
    0 < J q := by
  have hαp : q.alpha = (uniformTorsion (Real.pi / 3) 0).alpha := by
    funext a; exact hα a
  exact not_dual_only_J_eq_zero_of_wall_pos hαp hq uniform_pi_div_three_wall_pos

/-! ### Mixed unwind onto the equal-scale cone -/

/-- Usual rapidities truncated to \(\pi/4\), dual angles matched. -/
noncomputable def equalScaleUnwind (p : TorsionParams) : TorsionParams where
  alpha := fun a => min (p.alpha a) (Real.pi / 4)
  beta := fun a => min (p.alpha a) (Real.pi / 4)

theorem J_equalScaleUnwind (p : TorsionParams) : J (equalScaleUnwind p) = 0 := by
  rw [J_coef]
  simp [equalScaleUnwind]

theorem isAdmissibleContinuous_equalScaleUnwind {p : TorsionParams}
    (hα : ∀ a, 0 ≤ p.alpha a) :
    IsAdmissibleContinuous (equalScaleUnwind p) := by
  intro a
  have hπ : 0 ≤ Real.pi / 4 := by
    have : 0 < Real.pi := Real.pi_pos
    linarith
  have hmin : 0 ≤ min (p.alpha a) (Real.pi / 4) := le_min (hα a) hπ
  have hle : min (p.alpha a) (Real.pi / 4) ≤ Real.pi / 4 := min_le_right _ _
  refine ⟨hmin, hmin, ?_⟩
  simp only [equalScaleUnwind]
  linarith

theorem mass_equalScaleUnwind (p : TorsionParams) :
    mass (equalScaleUnwind p) =
      ∑ a : Fin 3, (min (p.alpha a) (Real.pi / 4)) ^ 2 := by
  rw [mass_coef]
  simp only [equalScaleUnwind, Fin.sum_univ_three]
  ring

theorem mass_equalScaleUnwind_pos {p : TorsionParams}
    (h : ∃ a, 0 < p.alpha a) :
    0 < mass (equalScaleUnwind p) := by
  rw [mass_equalScaleUnwind]
  rcases h with ⟨a, ha⟩
  have hπ : 0 < Real.pi / 4 := by
    have : 0 < Real.pi := Real.pi_pos
    linarith
  refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ?_
  exact ⟨a, Finset.mem_univ a, sq_pos_of_pos (lt_min ha hπ)⟩

/-- Mixed control still reaches a massive shield when dual-only cannot:
unwind each usual rapidity to at most \(\pi/4\). -/
theorem exists_mixed_equalScale_J_eq_zero {p : TorsionParams}
    (hα : ∀ a, 0 ≤ p.alpha a) (hpos : ∃ a, 0 < p.alpha a) :
    ∃ q : TorsionParams,
      IsAdmissibleContinuous q ∧ J q = 0 ∧ 0 < mass q :=
  ⟨equalScaleUnwind p, isAdmissibleContinuous_equalScaleUnwind hα,
    J_equalScaleUnwind p, mass_equalScaleUnwind_pos hpos⟩

theorem uniform_pi_div_three_mixed_shield :
    J (equalScaleUnwind (uniformTorsion (Real.pi / 3) 0)) = 0 ∧
      IsAdmissibleContinuous
        (equalScaleUnwind (uniformTorsion (Real.pi / 3) 0)) ∧
      0 < mass (equalScaleUnwind (uniformTorsion (Real.pi / 3) 0)) := by
  refine ⟨J_equalScaleUnwind _, ?_, ?_⟩
  · refine isAdmissibleContinuous_equalScaleUnwind ?_
    intro a
    simp only [uniformTorsion]
    positivity
  · refine mass_equalScaleUnwind_pos ?_
    refine ⟨0, ?_⟩
    simp only [uniformTorsion]
    have hπ : 0 < Real.pi := Real.pi_pos
    nlinarith

/-! ### Cross-axis dual compensation

Equal-scale \(\beta=\alpha\) is an isotropic target. Dual-only shielding
is a scalar budget: idle axes can carry the dual rapidity that cancels a
boosted usual axis.
-/

/-- Value `x` on index `i`, else `0`. -/
def finCoord (i : Fin 3) (x : ℝ) : Fin 3 → ℝ :=
  fun a => if a = i then x else 0

theorem finCoord_nonneg {i : Fin 3} {x : ℝ} (hx : 0 ≤ x) (a : Fin 3) :
    0 ≤ finCoord i x a := by
  simp [finCoord]
  split_ifs <;> simp [hx]

theorem sum_sq_finCoord (i : Fin 3) (x : ℝ) :
    ∑ a : Fin 3, finCoord i x a ^ 2 = x ^ 2 := by
  fin_cases i <;> simp [finCoord]

theorem J_finCoord_pair (i j : Fin 3) (α : ℝ) :
    J ⟨finCoord i α, finCoord j α⟩ = 0 := by
  rw [J_coef]
  dsimp
  rw [Finset.sum_sub_distrib, sum_sq_finCoord, sum_sq_finCoord]
  ring

/-- Pure usual rapidity on axis \(0\). -/
def axisUsual (α : ℝ) : TorsionParams where
  alpha := finCoord 0 α
  beta := fun _ => 0

/-- Usual on axis \(0\), dual on axis \(1\). -/
def crossAxisDual (α : ℝ) : TorsionParams where
  alpha := finCoord 0 α
  beta := finCoord 1 α

/-- Usual on axis \(0\), dual on axis \(2\). -/
def crossAxisDual' (α : ℝ) : TorsionParams where
  alpha := finCoord 0 α
  beta := finCoord 2 α

theorem axisUsual_alpha_nonneg {α : ℝ} (hα : 0 ≤ α) :
    ∀ a, 0 ≤ (axisUsual α).alpha a :=
  fun _ => finCoord_nonneg hα _

theorem isAdmissibleContinuous_axisUsual {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ Real.pi / 2) :
    IsAdmissibleContinuous (axisUsual α) := by
  intro a
  refine ⟨finCoord_nonneg hα0 a, le_rfl, ?_⟩
  simp [axisUsual, finCoord]
  split_ifs <;> linarith [hα0, hα]

theorem J_crossAxisDual (α : ℝ) : J (crossAxisDual α) = 0 :=
  J_finCoord_pair 0 1 α

theorem J_crossAxisDual' (α : ℝ) : J (crossAxisDual' α) = 0 :=
  J_finCoord_pair 0 2 α

theorem crossAxisDual_alpha_eq_axisUsual (α : ℝ) :
    (crossAxisDual α).alpha = (axisUsual α).alpha :=
  rfl

theorem crossAxisDual'_alpha_eq_axisUsual (α : ℝ) :
    (crossAxisDual' α).alpha = (axisUsual α).alpha :=
  rfl

theorem isAdmissibleContinuous_crossAxisDual {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ Real.pi / 2) :
    IsAdmissibleContinuous (crossAxisDual α) := by
  intro a
  refine ⟨finCoord_nonneg hα0 a, finCoord_nonneg hα0 a, ?_⟩
  fin_cases a
  · simpa [crossAxisDual, finCoord] using hα
  · simpa [crossAxisDual, finCoord] using hα
  · have : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    simpa [crossAxisDual, finCoord] using this

theorem isAdmissibleContinuous_crossAxisDual' {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ Real.pi / 2) :
    IsAdmissibleContinuous (crossAxisDual' α) := by
  intro a
  refine ⟨finCoord_nonneg hα0 a, finCoord_nonneg hα0 a, ?_⟩
  fin_cases a
  · simpa [crossAxisDual', finCoord] using hα
  · have : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    simpa [crossAxisDual', finCoord] using this
  · simpa [crossAxisDual', finCoord] using hα

theorem crossAxisDual_ne_crossAxisDual' {α : ℝ} (hα : α ≠ 0) :
    crossAxisDual α ≠ crossAxisDual' α := by
  intro h
  have hβ := congrArg (fun p : TorsionParams => p.beta 1) h
  simp only [crossAxisDual, crossAxisDual', finCoord, ↓reduceIte] at hβ
  exact hα hβ

/-- Equal-scale on a single axis leaves the cone once \(\alpha>\pi/4\). -/
theorem equalScale_axisUsual_not_admissible {α : ℝ}
    (h : Real.pi / 4 < α) :
    ¬ IsAdmissibleContinuous (equalScaleOf (axisUsual α)) := by
  intro hAdm
  have hnn : ∀ a, 0 ≤ (axisUsual α).alpha a :=
    axisUsual_alpha_nonneg
      (le_of_lt (lt_trans (by positivity : (0 : ℝ) < Real.pi / 4) h))
  have := (isAdmissibleContinuous_equalScaleOf_iff hnn).mp hAdm 0
  simp only [axisUsual, finCoord] at this
  exact (not_le_of_gt h) this

/-- Dual-only shielding of a single-axis seed does not require the
equal-scale point. -/
theorem exists_dual_only_shield_axisUsual {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ Real.pi / 2) :
    ∃ q : TorsionParams,
      q.alpha = (axisUsual α).alpha ∧ IsAdmissibleContinuous q ∧ J q = 0 :=
  ⟨crossAxisDual α, rfl, isAdmissibleContinuous_crossAxisDual hα0 hα,
    J_crossAxisDual α⟩

/-- The isotropic target is strictly stronger than dual-only shielding. -/
theorem equalScale_strictly_stronger_than_dual_only_shield :
    ∃ p : TorsionParams,
      IsAdmissibleContinuous p ∧
        (∃ q : TorsionParams,
          q.alpha = p.alpha ∧ IsAdmissibleContinuous q ∧ J q = 0) ∧
          ¬ IsAdmissibleContinuous (equalScaleOf p) :=
  ⟨axisUsual (Real.pi / 3),
    isAdmissibleContinuous_axisUsual (by positivity) pi_div_three_le_pi_div_two,
    exists_dual_only_shield_axisUsual (by positivity) pi_div_three_le_pi_div_two,
    equalScale_axisUsual_not_admissible pi_div_four_lt_pi_div_three⟩

/-- Two silent axes give two distinct dual-only shields of the same seed. -/
theorem exists_two_dual_only_shields_axisUsual {α : ℝ}
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    ∃ q₁ q₂ : TorsionParams,
      q₁.alpha = (axisUsual α).alpha ∧ q₂.alpha = (axisUsual α).alpha ∧
        IsAdmissibleContinuous q₁ ∧ IsAdmissibleContinuous q₂ ∧
          J q₁ = 0 ∧ J q₂ = 0 ∧ q₁ ≠ q₂ :=
  ⟨crossAxisDual α, crossAxisDual' α, rfl, rfl,
    isAdmissibleContinuous_crossAxisDual (le_of_lt hα0) hα,
    isAdmissibleContinuous_crossAxisDual' (le_of_lt hα0) hα,
    J_crossAxisDual α, J_crossAxisDual' α,
    crossAxisDual_ne_crossAxisDual' hα0.ne'⟩

/-! ### Unique dual-only shield on the wall, and vacuum obstruction -/

/-- When the wall vanishes, the only dual-only shield is the wall itself. -/
theorem dual_only_shield_unique_of_wall_zero {p q : TorsionParams}
    (hα : q.alpha = p.alpha) (hq : IsAdmissibleContinuous q)
    (hwall : J (dualWallParams p) = 0) (hJ : J q = 0) :
    q = dualWallParams p := by
  refine torsionParams_ext hα ?_
  have hβW : ∑ i : Fin 3, q.beta i ^ 2 =
      ∑ i : Fin 3, dualWall (p.alpha i) ^ 2 := by
    have hq' := (J_eq_zero_iff q).mp hJ
    have hp' := (J_eq_zero_iff (dualWallParams p)).mp hwall
    simp only [dualWallParams] at hp'
    rw [← hq', hα]
    exact hp'
  have hle (i : Fin 3) : q.beta i ≤ dualWall (p.alpha i) := by
    have := admissibleContinuous_beta_le_dualWall hq i
    rwa [hα] at this
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ dualWall (p.alpha i) ^ 2 - q.beta i ^ 2 := fun i _ =>
    sub_nonneg.mpr <|
      pow_le_pow_left₀ (admissibleContinuous_beta_nonneg q hq i) (hle i) 2
  have hdiff0 :
      ∑ i : Fin 3, (dualWall (p.alpha i) ^ 2 - q.beta i ^ 2) = 0 := by
    simp [Finset.sum_sub_distrib, hβW]
  funext a
  have hsq : dualWall (p.alpha a) ^ 2 = q.beta a ^ 2 := by
    linarith [(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hdiff0 a
      (Finset.mem_univ a)]
  have hWnn : 0 ≤ dualWall (p.alpha a) :=
    le_trans (admissibleContinuous_beta_nonneg q hq a) (hle a)
  simp only [dualWallParams]
  exact ((sq_eq_sq₀ hWnn (admissibleContinuous_beta_nonneg q hq a)).mp
    hsq).symm

/-- Dual-only motion conserves \(\sum\alpha^2\), so a massive usual seed
cannot reach the vacuum. -/
theorem dual_only_not_vacuum_of_usual_pos {p q : TorsionParams}
    (hα : q.alpha = p.alpha)
    (hU : ∑ a : Fin 3, p.alpha a ^ 2 ≠ 0)
    (hM : mass q = 0) : False := by
  rw [← hα] at hU
  exact hU <| Finset.sum_eq_zero fun a _ => by
    simp [((mass_eq_zero_iff q).mp hM a).1]

end Gravity

end DstDiophantine
