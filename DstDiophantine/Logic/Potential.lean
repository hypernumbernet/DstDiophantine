/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Scale-dependent potential

The D4L potential is
\[
V_\lambda(J)=-\cos(2\pi J)+\frac{\alpha}{\lambda}U(J)
\]
with two candidate \(U\). We formalise both, prove they disagree by a
factor of two on \(\{J>0\}\), and record what the written \(U\) actually
does to the negative-torsion well.

The large-scale skeleton \(V_\infty=-\cos(2\pi J)\) is independent of \(U\).
The binder `lam` is the scale \(\lambda>0\) (Lean reserves `λ` for `fun`).
-/

namespace DstDiophantine

namespace Logic

open Filter Real Topology

/-- Piecewise \(U\): \(0\) on negatives, \(J^2\) on non-negatives. -/
noncomputable def UPiece (j : ℝ) : ℝ :=
  if j < 0 then 0 else j ^ 2

/-- Smooth candidate \(U(J)=\tfrac12(J+|J|)^2\). -/
noncomputable def USmooth (j : ℝ) : ℝ :=
  (1 / 2) * (j + |j|) ^ 2

theorem UPiece_of_neg {j : ℝ} (h : j < 0) : UPiece j = 0 := by
  simp [UPiece, h]

theorem UPiece_of_nonneg {j : ℝ} (h : 0 ≤ j) : UPiece j = j ^ 2 := by
  simp [UPiece, not_lt.mpr h]

theorem USmooth_of_neg {j : ℝ} (h : j < 0) : USmooth j = 0 := by
  unfold USmooth
  rw [abs_of_neg h]
  ring

theorem USmooth_of_nonneg {j : ℝ} (h : 0 ≤ j) : USmooth j = 2 * j ^ 2 := by
  unfold USmooth
  rw [abs_of_nonneg h]
  ring

/-- On the positive ray the two written \(U\) differ by a factor of two. -/
theorem USmooth_eq_two_UPiece_of_pos {j : ℝ} (h : 0 < j) :
    USmooth j = 2 * UPiece j := by
  rw [USmooth_of_nonneg h.le, UPiece_of_nonneg h.le]

theorem USmooth_eq_UPiece_of_neg {j : ℝ} (h : j < 0) :
    USmooth j = UPiece j := by
  rw [USmooth_of_neg h, UPiece_of_neg h]

/-- Large-scale skeleton. -/
noncomputable def VInf (j : ℝ) : ℝ :=
  -Real.cos (2 * Real.pi * j)

/-- Scale-dependent potential for a choice of \(U\). `lam` is \(\lambda\). -/
noncomputable def V (U : ℝ → ℝ) (lam α j : ℝ) : ℝ :=
  VInf j + (α / lam) * U j

noncomputable def VPiece (lam α j : ℝ) : ℝ :=
  V UPiece lam α j

noncomputable def VSmooth (lam α j : ℝ) : ℝ :=
  V USmooth lam α j

/-- Usual-spacetime bias term from the note. -/
noncomputable def VBias (U : ℝ → ℝ) (lam α γ j : ℝ) : ℝ :=
  V U lam α j + γ * j

theorem VPiece_eq_VInf_of_neg (lam α j : ℝ) (hj : j < 0) :
    VPiece lam α j = VInf j := by
  unfold VPiece V
  rw [UPiece_of_neg hj, mul_zero, add_zero]

theorem tendsto_V_atTop (U : ℝ → ℝ) (α j : ℝ) :
    Tendsto (fun lam : ℝ => V U lam α j) atTop (𝓝 (VInf j)) := by
  unfold V
  have hinv : Tendsto (fun lam : ℝ => lam⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hcoef : Tendsto (fun lam : ℝ => (α * lam⁻¹) * U j) atTop (𝓝 0) := by
    simpa using (hinv.const_mul α).mul_const (U j)
  have : Tendsto (fun lam : ℝ => (α / lam) * U j) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hcoef
  simpa using tendsto_const_nhds.add this

/-- Explicit first derivative of \(V_\infty\) (equals \(\partial_J(-\cos(2\pi J))\)). -/
noncomputable def VInfDeriv (j : ℝ) : ℝ :=
  2 * Real.pi * Real.sin (2 * Real.pi * j)

/-- Explicit second derivative of \(V_\infty\). -/
noncomputable def VInfDeriv2 (j : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * j)

theorem VInfDeriv_eq_zero_iff (j : ℝ) :
    VInfDeriv j = 0 ↔ ∃ k : ℤ, j = (k : ℝ) / 2 := by
  unfold VInfDeriv
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [mul_eq_zero, or_iff_right hπ, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have : 2 * Real.pi * j = n * Real.pi := hn.symm
    have hπ0 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hπ0] at this ⊢
    linarith
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    ring

theorem VInf_second_pos_at_zero :
    (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (0 : ℝ)) > 0 := by
  simp only [mul_zero, Real.cos_zero, mul_one]
  positivity

theorem VInf_second_pos_at_one :
    (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (1 : ℝ)) > 0 := by
  simp only [mul_one, Real.cos_two_pi]
  positivity

theorem VInf_second_pos_at_neg_one :
    (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (-1 : ℝ)) > 0 := by
  simp only [mul_neg, mul_one, Real.cos_neg, Real.cos_two_pi]
  positivity

theorem VInf_second_neg_at_half :
    (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (1 / 2 : ℝ)) < 0 := by
  have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  rw [harg, Real.cos_pi]
  nlinarith [Real.pi_pos]

theorem VInf_second_neg_at_neg_half :
    (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (-(1 / 2) : ℝ)) < 0 := by
  have harg : 2 * Real.pi * (-(1 / 2) : ℝ) = -Real.pi := by ring
  rw [harg, Real.cos_neg, Real.cos_pi]
  nlinarith [Real.pi_pos]

/-- Gradient flow of \(V_\infty\): \(\dot J=-V_\infty'(J)\). -/
noncomputable def flowInf (j : ℝ) : ℝ :=
  -VInfDeriv j

private theorem sin_pos_of_mem_Ioo_neg_period {j : ℝ}
    (hlo : -1 < j) (hhi : j < -1 / 2) :
    0 < Real.sin (2 * Real.pi * j) := by
  have hsin : Real.sin (2 * Real.pi * j) = Real.sin (2 * Real.pi * (j + 1)) :=
    calc Real.sin (2 * Real.pi * j)
        = Real.sin (2 * Real.pi * j + 2 * Real.pi) := (Real.sin_periodic _).symm
      _ = Real.sin (2 * Real.pi * (j + 1)) := congrArg _ (by ring)
  rw [hsin]
  apply Real.sin_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

private theorem sin_neg_of_mem_Ioo_neg_half_zero {j : ℝ}
    (hlo : -1 / 2 < j) (hhi : j < 0) :
    Real.sin (2 * Real.pi * j) < 0 := by
  have : Real.sin (2 * Real.pi * j) = -Real.sin (2 * Real.pi * (-j)) := by
    rw [← Real.sin_neg]; ring_nf
  have hpos : 0 < Real.sin (2 * Real.pi * (-j)) := by
    apply Real.sin_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  linarith

theorem flowInf_neg_of_Ioo_neg_one_neg_half {j : ℝ}
    (hlo : -1 < j) (hhi : j < -1 / 2) :
    flowInf j < 0 := by
  unfold flowInf VInfDeriv
  have := sin_pos_of_mem_Ioo_neg_period hlo hhi
  nlinarith [Real.pi_pos]

theorem flowInf_pos_of_Ioo_neg_half_zero {j : ℝ}
    (hlo : -1 / 2 < j) (hhi : j < 0) :
    0 < flowInf j := by
  unfold flowInf VInfDeriv
  have := sin_neg_of_mem_Ioo_neg_half_zero hlo hhi
  nlinarith [Real.pi_pos]

theorem flowInf_neg_of_Ioo_zero_half {j : ℝ}
    (hlo : 0 < j) (hhi : j < 1 / 2) :
    flowInf j < 0 := by
  unfold flowInf VInfDeriv
  have hsin : 0 < Real.sin (2 * Real.pi * j) := by
    apply Real.sin_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  nlinarith [Real.pi_pos]

theorem flowInf_pos_of_Ioo_half_one {j : ℝ}
    (hlo : 1 / 2 < j) (hhi : j < 1) :
    0 < flowInf j := by
  unfold flowInf VInfDeriv
  have hsin : Real.sin (2 * Real.pi * j) < 0 := by
    have hper : Real.sin (2 * Real.pi * j) = Real.sin (2 * Real.pi * (j - 1)) :=
      calc Real.sin (2 * Real.pi * j)
          = Real.sin (2 * Real.pi * j - 2 * Real.pi) := (Real.sin_periodic.sub_eq _).symm
        _ = Real.sin (2 * Real.pi * (j - 1)) := congrArg _ (by ring)
    rw [hper]
    exact sin_neg_of_mem_Ioo_neg_half_zero (by linarith) (by linarith)
  nlinarith [Real.pi_pos]

/-- Written \(U\) leaves \(V\) equal to \(V_\infty\) on the whole negative half-line.
The second derivative at \(-1\) is therefore \(4\pi^2>0\) at every scale. -/
theorem written_U_B_well_survives (lam α : ℝ) (_hlam : 0 < lam) :
    VPiece lam α (-1) = VInf (-1) ∧
      (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (-1 : ℝ)) > 0 :=
  ⟨VPiece_eq_VInf_of_neg lam α (-1) (by norm_num), VInf_second_pos_at_neg_one⟩

/-- There is no critical scale at which the written piecewise \(U\) destroys
the local minimum at \(J=-1\). -/
theorem written_U_no_critical_scale (lam α : ℝ) (hlam : 0 < lam) :
    VPiece lam α (-1) = VInf (-1) ∧
      0 < (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (-1 : ℝ)) :=
  written_U_B_well_survives lam α hlam

theorem VBias_sub (U : ℝ → ℝ) (lam α γ j : ℝ) :
    VBias U lam α γ j - V U lam α j = γ * j := by
  simp [VBias]

/-- Under energy minimisation, a linear bias \(\gamma J\) favours the sign
*opposite* to \(\gamma\). -/
theorem bias_lowers_opposite_sign (U : ℝ → ℝ) (lam α γ j : ℝ) (h : γ * j < 0) :
    VBias U lam α γ j < V U lam α j := by
  linarith [VBias_sub U lam α γ j]

end Logic

end DstDiophantine
