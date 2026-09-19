import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.Invariant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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
* The balanced target \(\beta=\alpha\) (equal-scale shielding) lies in the
  cone if and only if \(\alpha_a\le\pi/4\) on every axis.
* Uniform examples: \(\alpha=\pi/6\) admits both shielding and repulsion
  by dual-only motion; \(\alpha=\pi/3\) cannot reach \(J=0\) dual-only.
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

private theorem torsionParams_ext {p q : TorsionParams}
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

/-- Dual-only configurations cannot undercut the wall value of \(J\). -/
theorem J_dual_only_ge_wall {p q : TorsionParams}
    (hα : q.alpha = p.alpha) (hq : IsAdmissibleContinuous q) :
    J (dualWallParams p) ≤ J q := by
  rw [J_eq_sum_JAxis, J_eq_sum_JAxis]
  refine Finset.sum_le_sum fun a _ => ?_
  unfold JAxis dualWallParams dualWall
  have hβnn := admissibleContinuous_beta_nonneg q hq a
  have hsum := admissibleContinuous_sum_le q hq a
  have hβle : q.beta a ≤ Real.pi / 2 - p.alpha a := by
    rw [← hα]
    linarith
  have hwall_nn : 0 ≤ Real.pi / 2 - p.alpha a := by
    have := admissibleContinuous_alpha_le_half_pi q hq a
    rw [hα] at this
    linarith
  have hsq : q.beta a ^ 2 ≤ (Real.pi / 2 - p.alpha a) ^ 2 :=
    pow_le_pow_left₀ hβnn hβle 2
  simp [hα]
  linarith

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

end Gravity

end DstDiophantine
