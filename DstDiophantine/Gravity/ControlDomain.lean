import DstDiophantine.Gravity.ShieldCeiling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Kinematic domain of \((J,M)\) on the admissible cone

The parabola \(\pi^2 M\le 5\pi^4/16+4J^2\) of `ShieldCeiling` is valid
everywhere and sharp on the central band \(|J|\le\pi^2/8\). Outside that
band two axes lock to the same sector at the cone's edge, and a strictly
tighter envelope takes over. Together with \(|J|\le M\), this envelope is
the exact image of the admissible cone in the \((J,M)\)-plane.

## Paper boundary (do **not** claim)

No electromagnetic coupling, no laboratory protocol, and no identification
of the dual-channel force \(u\) with Faraday coefficients.

## What is proved

* Three quadratic upper bounds hold on the whole cone. Their pointwise
  minimum is the sharp envelope
  \(M\le 5\pi^2/16+\min\bigl(4J^2,(2J-\pi^2/2)^2,(2J+\pi^2/2)^2\bigr)/\pi^2\),
  equivalently
  \(M_{\mathrm{norm}}\le\tfrac56+\tfrac16\min\bigl(9J_n^2,(3J_n-2)^2,(3J_n+2)^2\bigr)\).
* The central arc \(|J|\le\pi^2/8\) recovers the shield parabola; the
  attractive lobe \(J\ge\pi^2/8\) is attained by two pure-usual axes plus
  a wall; the repulsive lobe is its usual–dual swap.
* The envelope meets the absolute mass ceiling \(M=3\pi^2/8\) at
  \(|J|=\pi^2/8\) and at \(|J|=3\pi^2/8\), and falls back to the shield
  value \(5\pi^2/16\) at \(|J|=\pi^2/4\).
* Every pair with \(|J|\le M\le\) the envelope is realised by an
  admissible configuration.
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-! ### Axis densities and the three pairings -/

def axisSigned (p : TorsionParams) (a : Fin 3) : ℝ :=
  p.alpha a ^ 2 - p.beta a ^ 2

def axisUnsigned (p : TorsionParams) (a : Fin 3) : ℝ :=
  p.alpha a ^ 2 + p.beta a ^ 2

theorem signedSum_eq_two_J (p : TorsionParams) :
    ∑ a : Fin 3, axisSigned p a = 2 * J p := by
  rw [J_coef]
  simp only [axisSigned, Fin.sum_univ_three]
  ring

theorem unsignedSum_eq_two_mass (p : TorsionParams) :
    ∑ a : Fin 3, axisUnsigned p a = 2 * mass p := by
  rw [mass_coef]
  simp only [axisUnsigned, Fin.sum_univ_three]
  ring

private theorem axis_sum_sq_le {k α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ k) :
    (α + β) ^ 2 ≤ k ^ 2 := by
  nlinarith

private theorem axis_diff_sq_le {k α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ k) :
    (α - β) ^ 2 ≤ k ^ 2 := by
  nlinarith

private theorem axis_trade_off {k α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ k) :
    2 * k ^ 2 * (α ^ 2 + β ^ 2) ≤ k ^ 4 + (α ^ 2 - β ^ 2) ^ 2 := by
  have h1 : (0 : ℝ) ≤ k ^ 2 - (α + β) ^ 2 :=
    sub_nonneg.mpr (axis_sum_sq_le hα hβ hs)
  have h2 : (0 : ℝ) ≤ k ^ 2 - (α - β) ^ 2 :=
    sub_nonneg.mpr (axis_diff_sq_le hα hβ hs)
  nlinarith [mul_nonneg h1 h2]

private theorem axis_signed_le {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    axisSigned p a ≤ (Real.pi / 2) ^ 2 := by
  have hα := (h a).1
  have hβ := (h a).2.1
  have hs := (h a).2.2
  unfold axisSigned
  nlinarith

private theorem axis_signed_ge {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    -(Real.pi / 2) ^ 2 ≤ axisSigned p a := by
  have hα := (h a).1
  have hβ := (h a).2.1
  have hs := (h a).2.2
  unfold axisSigned
  nlinarith

private theorem e2_ge_two_K_T_sub_three_K_sq {K t₀ t₁ t₂ : ℝ}
    (h₀ : t₀ ≤ K) (h₁ : t₁ ≤ K) (h₂ : t₂ ≤ K) :
    2 * K * (t₀ + t₁ + t₂) - 3 * K ^ 2 ≤ t₀ * t₁ + t₀ * t₂ + t₁ * t₂ := by
  have h01 : (0 : ℝ) ≤ (K - t₀) * (K - t₁) :=
    mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₁)
  have h02 : (0 : ℝ) ≤ (K - t₀) * (K - t₂) :=
    mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₂)
  have h12 : (0 : ℝ) ≤ (K - t₁) * (K - t₂) :=
    mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)
  nlinarith [h01, h02, h12]

private theorem e2_ge_neg_two_K_T_sub_three_K_sq {K t₀ t₁ t₂ : ℝ}
    (h₀ : -K ≤ t₀) (h₁ : -K ≤ t₁) (h₂ : -K ≤ t₂) :
    -2 * K * (t₀ + t₁ + t₂) - 3 * K ^ 2 ≤ t₀ * t₁ + t₀ * t₂ + t₁ * t₂ := by
  have ht₀ : (0 : ℝ) ≤ K + t₀ := by linarith
  have ht₁ : (0 : ℝ) ≤ K + t₁ := by linarith
  have ht₂ : (0 : ℝ) ≤ K + t₂ := by linarith
  have h01 : (0 : ℝ) ≤ (K + t₀) * (K + t₁) := mul_nonneg ht₀ ht₁
  have h02 : (0 : ℝ) ≤ (K + t₀) * (K + t₂) := mul_nonneg ht₀ ht₂
  have h12 : (0 : ℝ) ≤ (K + t₁) * (K + t₂) := mul_nonneg ht₁ ht₂
  nlinarith [h01, h02, h12]

private theorem sum_sq_eq_T_sq_sub_two_e2 (t₀ t₁ t₂ : ℝ) :
    t₀ ^ 2 + t₁ ^ 2 + t₂ ^ 2 =
      (t₀ + t₁ + t₂) ^ 2 - 2 * (t₀ * t₁ + t₀ * t₂ + t₁ * t₂) := by
  ring

private theorem sum_signed_sq_le_attractive_lobe {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2 ≤
      (2 * J p - Real.pi ^ 2 / 2) ^ 2 + 2 * ((Real.pi / 2) ^ 2) ^ 2 := by
  set K := (Real.pi / 2) ^ 2
  set t₀ := axisSigned p 0
  set t₁ := axisSigned p 1
  set t₂ := axisSigned p 2
  have hT : t₀ + t₁ + t₂ = 2 * J p := by
    simpa [t₀, t₁, t₂, Fin.sum_univ_three] using signedSum_eq_two_J p
  have he : 2 * K * (t₀ + t₁ + t₂) - 3 * K ^ 2 ≤ t₀ * t₁ + t₀ * t₂ + t₁ * t₂ :=
    e2_ge_two_K_T_sub_three_K_sq (axis_signed_le h 0) (axis_signed_le h 1)
      (axis_signed_le h 2)
  have hsq := sum_sq_eq_T_sq_sub_two_e2 t₀ t₁ t₂
  have hK : 2 * K = Real.pi ^ 2 / 2 := by unfold K; ring
  have hbody :
      t₀ ^ 2 + t₁ ^ 2 + t₂ ^ 2 ≤
        (t₀ + t₁ + t₂ - 2 * K) ^ 2 + 2 * K ^ 2 := by
    nlinarith [hsq, he]
  rw [hT, hK] at hbody
  simpa [t₀, t₁, t₂] using hbody

private theorem sum_signed_sq_le_repulsive_lobe {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2 ≤
      (2 * J p + Real.pi ^ 2 / 2) ^ 2 + 2 * ((Real.pi / 2) ^ 2) ^ 2 := by
  set K := (Real.pi / 2) ^ 2
  set t₀ := axisSigned p 0
  set t₁ := axisSigned p 1
  set t₂ := axisSigned p 2
  have hT : t₀ + t₁ + t₂ = 2 * J p := by
    simpa [t₀, t₁, t₂, Fin.sum_univ_three] using signedSum_eq_two_J p
  have he : -2 * K * (t₀ + t₁ + t₂) - 3 * K ^ 2 ≤ t₀ * t₁ + t₀ * t₂ + t₁ * t₂ :=
    e2_ge_neg_two_K_T_sub_three_K_sq (axis_signed_ge h 0) (axis_signed_ge h 1)
      (axis_signed_ge h 2)
  have hsq := sum_sq_eq_T_sq_sub_two_e2 t₀ t₁ t₂
  have hK : 2 * K = Real.pi ^ 2 / 2 := by unfold K; ring
  have hbody :
      t₀ ^ 2 + t₁ ^ 2 + t₂ ^ 2 ≤
        (t₀ + t₁ + t₂ + 2 * K) ^ 2 + 2 * K ^ 2 := by
    nlinarith [hsq, he]
  rw [hT, hK] at hbody
  simpa [t₀, t₁, t₂] using hbody

private theorem four_K_mass_le_three_K_sq_add_sum_sq {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p ≤
      3 * (Real.pi / 2) ^ 4 +
        (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) := by
  have hax : ∀ a : Fin 3,
      2 * (Real.pi / 2) ^ 2 * axisUnsigned p a ≤
        (Real.pi / 2) ^ 4 + axisSigned p a ^ 2 := fun a => by
    simpa [axisUnsigned, axisSigned] using
      axis_trade_off (h a).1 (h a).2.1 (h a).2.2
  have hsum :
      2 * (Real.pi / 2) ^ 2 *
          (axisUnsigned p 0 + axisUnsigned p 1 + axisUnsigned p 2) ≤
        3 * (Real.pi / 2) ^ 4 +
          (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) := by
    nlinarith [hax 0, hax 1, hax 2]
  have hU : axisUnsigned p 0 + axisUnsigned p 1 + axisUnsigned p 2 =
      2 * mass p := by
    simpa [Fin.sum_univ_three] using unsignedSum_eq_two_mass p
  have hπ : 2 * (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 2 := by ring
  have : (Real.pi ^ 2 / 2) * (2 * mass p) ≤
      3 * (Real.pi / 2) ^ 4 +
        (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) := by
    rw [← hπ, ← hU]; exact hsum
  nlinarith [this]

theorem pi_sq_mass_le_attractive_lobe (p : TorsionParams)
    (h : IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p ≤
      5 * Real.pi ^ 4 / 16 + (2 * J p - Real.pi ^ 2 / 2) ^ 2 := by
  have hsum := four_K_mass_le_three_K_sq_add_sum_sq h
  have hsq := sum_signed_sq_le_attractive_lobe h
  have hK4 : 3 * (Real.pi / 2) ^ 4 + 2 * ((Real.pi / 2) ^ 2) ^ 2 =
      5 * Real.pi ^ 4 / 16 := by ring
  nlinarith [hsum, hsq, hK4]

theorem pi_sq_mass_le_repulsive_lobe (p : TorsionParams)
    (h : IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p ≤
      5 * Real.pi ^ 4 / 16 + (2 * J p + Real.pi ^ 2 / 2) ^ 2 := by
  have hsum := four_K_mass_le_three_K_sq_add_sum_sq h
  have hsq := sum_signed_sq_le_repulsive_lobe h
  have hK4 : 3 * (Real.pi / 2) ^ 4 + 2 * ((Real.pi / 2) ^ 2) ^ 2 =
      5 * Real.pi ^ 4 / 16 := by ring
  nlinarith [hsum, hsq, hK4]

/-! ### The sharp envelope -/

noncomputable def controlEnvelopeNum (Jval : ℝ) : ℝ :=
  min (4 * Jval ^ 2)
    (min ((2 * Jval - Real.pi ^ 2 / 2) ^ 2)
      ((2 * Jval + Real.pi ^ 2 / 2) ^ 2))

noncomputable def controlCeiling (Jval : ℝ) : ℝ :=
  5 * Real.pi ^ 2 / 16 + controlEnvelopeNum Jval / Real.pi ^ 2

theorem controlEnvelopeNum_nonneg (Jval : ℝ) : 0 ≤ controlEnvelopeNum Jval :=
  le_min (by positivity) (le_min (sq_nonneg _) (sq_nonneg _))

theorem controlEnvelopeNum_neg (Jval : ℝ) :
    controlEnvelopeNum (-Jval) = controlEnvelopeNum Jval := by
  unfold controlEnvelopeNum
  have h4 : 4 * (-Jval) ^ 2 = 4 * Jval ^ 2 := by ring
  have hA : (2 * (-Jval) - Real.pi ^ 2 / 2) ^ 2 =
      (2 * Jval + Real.pi ^ 2 / 2) ^ 2 := by ring
  have hB : (2 * (-Jval) + Real.pi ^ 2 / 2) ^ 2 =
      (2 * Jval - Real.pi ^ 2 / 2) ^ 2 := by ring
  rw [h4, hA, hB, min_comm (a := (2 * Jval - Real.pi ^ 2 / 2) ^ 2)]

theorem controlCeiling_neg (Jval : ℝ) :
    controlCeiling (-Jval) = controlCeiling Jval := by
  unfold controlCeiling
  rw [controlEnvelopeNum_neg]

theorem pi_sq_mass_le_envelope (p : TorsionParams)
    (h : IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p ≤ 5 * Real.pi ^ 4 / 16 + controlEnvelopeNum (J p) := by
  have hC := pi_sq_mass_le_shield_ceiling_add_J_sq p h
  have hA := pi_sq_mass_le_attractive_lobe p h
  have hR := pi_sq_mass_le_repulsive_lobe p h
  have ha : Real.pi ^ 2 * mass p - 5 * Real.pi ^ 4 / 16 ≤ 4 * J p ^ 2 := by
    linarith [hC]
  have hb : Real.pi ^ 2 * mass p - 5 * Real.pi ^ 4 / 16 ≤
      (2 * J p - Real.pi ^ 2 / 2) ^ 2 := by
    linarith [hA]
  have hc : Real.pi ^ 2 * mass p - 5 * Real.pi ^ 4 / 16 ≤
      (2 * J p + Real.pi ^ 2 / 2) ^ 2 := by
    linarith [hR]
  have : Real.pi ^ 2 * mass p - 5 * Real.pi ^ 4 / 16 ≤
      controlEnvelopeNum (J p) :=
    le_min ha (le_min hb hc)
  linarith

theorem mass_le_control_ceiling (p : TorsionParams)
    (h : IsAdmissibleContinuous p) :
    mass p ≤ controlCeiling (J p) := by
  have hraw := pi_sq_mass_le_envelope p h
  have hπ : 0 < Real.pi ^ 2 := by positivity
  unfold controlCeiling
  have hsub : Real.pi ^ 2 * mass p - 5 * Real.pi ^ 4 / 16 ≤
      controlEnvelopeNum (J p) := by linarith
  have hid : Real.pi ^ 2 * (mass p - 5 * Real.pi ^ 2 / 16) =
      Real.pi ^ 2 * mass p - 5 * Real.pi ^ 4 / 16 := by ring
  have : mass p - 5 * Real.pi ^ 2 / 16 ≤
      controlEnvelopeNum (J p) / Real.pi ^ 2 :=
    (le_div_iff₀ hπ).mpr (by linarith [hid, hsub])
  linarith

private theorem nine_Jn_sq_mul (Jval : ℝ) :
    9 * ((8 / (3 * Real.pi ^ 2)) * Jval) ^ 2 * (Real.pi ^ 4 / 16) =
      4 * Jval ^ 2 := by
  field_simp
  ring

private theorem three_Jn_sub_two_sq_mul (Jval : ℝ) :
    (3 * ((8 / (3 * Real.pi ^ 2)) * Jval) - 2) ^ 2 * (Real.pi ^ 4 / 16) =
      (2 * Jval - Real.pi ^ 2 / 2) ^ 2 := by
  field_simp
  ring

private theorem three_Jn_add_two_sq_mul (Jval : ℝ) :
    (3 * ((8 / (3 * Real.pi ^ 2)) * Jval) + 2) ^ 2 * (Real.pi ^ 4 / 16) =
      (2 * Jval + Real.pi ^ 2 / 2) ^ 2 := by
  field_simp
  ring

private theorem controlEnvelopeNum_eq_scaled (Jval : ℝ) :
    controlEnvelopeNum Jval =
      (Real.pi ^ 4 / 16) *
        min (9 * ((8 / (3 * Real.pi ^ 2)) * Jval) ^ 2)
          (min ((3 * ((8 / (3 * Real.pi ^ 2)) * Jval) - 2) ^ 2)
            ((3 * ((8 / (3 * Real.pi ^ 2)) * Jval) + 2) ^ 2)) := by
  have hpos : (0 : ℝ) ≤ Real.pi ^ 4 / 16 := by positivity
  have hmul : ∀ x y : ℝ,
      min x y * (Real.pi ^ 4 / 16) =
        min (x * (Real.pi ^ 4 / 16)) (y * (Real.pi ^ 4 / 16)) :=
    fun x y => min_mul_of_nonneg x y hpos
  unfold controlEnvelopeNum
  rw [eq_comm]
  calc (Real.pi ^ 4 / 16) *
        min (9 * ((8 / (3 * Real.pi ^ 2)) * Jval) ^ 2)
          (min ((3 * ((8 / (3 * Real.pi ^ 2)) * Jval) - 2) ^ 2)
            ((3 * ((8 / (3 * Real.pi ^ 2)) * Jval) + 2) ^ 2))
      = min (9 * ((8 / (3 * Real.pi ^ 2)) * Jval) ^ 2)
          (min ((3 * ((8 / (3 * Real.pi ^ 2)) * Jval) - 2) ^ 2)
            ((3 * ((8 / (3 * Real.pi ^ 2)) * Jval) + 2) ^ 2)) *
        (Real.pi ^ 4 / 16) := by ring
    _ = min (4 * Jval ^ 2)
          (min ((2 * Jval - Real.pi ^ 2 / 2) ^ 2)
            ((2 * Jval + Real.pi ^ 2 / 2) ^ 2)) := by
        rw [hmul, hmul, nine_Jn_sq_mul, three_Jn_sub_two_sq_mul,
          three_Jn_add_two_sq_mul]

theorem massNormalized_le_control_curve (p : TorsionParams)
    (h : IsAdmissibleContinuous p) :
    massNormalized p ≤
      5 / 6 + (1 / 6) *
        min (9 * JNormalized p ^ 2)
          (min ((3 * JNormalized p - 2) ^ 2)
            ((3 * JNormalized p + 2) ^ 2)) := by
  have hraw := mass_le_control_ceiling p h
  have hpos : (0 : ℝ) ≤ 8 / (3 * Real.pi ^ 2) := by positivity
  have hmul : massNormalized p ≤
      (8 / (3 * Real.pi ^ 2)) * controlCeiling (J p) := by
    unfold massNormalized
    exact mul_le_mul_of_nonneg_left hraw hpos
  have hscale := controlEnvelopeNum_eq_scaled (J p)
  have hid : (8 / (3 * Real.pi ^ 2)) * controlCeiling (J p) =
      5 / 6 + (1 / 6) *
        min (9 * JNormalized p ^ 2)
          (min ((3 * JNormalized p - 2) ^ 2)
            ((3 * JNormalized p + 2) ^ 2)) := by
    unfold controlCeiling JNormalized
    rw [hscale]
    field_simp
    try ring
  linarith

/-! ### Wall families attaining the envelope -/

noncomputable def twoUsualWitness (γ : ℝ) : TorsionParams where
  alpha := fun a => if a.val = 0 then Real.pi / 2 else if a.val = 1 then Real.pi / 2 else γ
  beta := fun a =>
    if a.val = 0 then 0 else if a.val = 1 then 0 else Real.pi / 2 - γ

noncomputable def twoDualWitness (γ : ℝ) : TorsionParams :=
  daggerParams (twoUsualWitness γ)

theorem J_twoUsualWitness (γ : ℝ) :
    J (twoUsualWitness γ) = Real.pi ^ 2 / 8 + (Real.pi / 2) * γ := by
  rw [J_coef]
  simp only [twoUsualWitness, Fin.sum_univ_three]
  norm_num
  ring

theorem mass_twoUsualWitness (γ : ℝ) :
    mass (twoUsualWitness γ) =
      5 * Real.pi ^ 2 / 16 + (γ - Real.pi / 4) ^ 2 := by
  rw [mass_coef]
  simp only [twoUsualWitness, Fin.sum_univ_three]
  norm_num
  ring

theorem isAdmissibleContinuous_twoUsualWitness {γ : ℝ}
    (h0 : 0 ≤ γ) (h1 : γ ≤ Real.pi / 2) :
    IsAdmissibleContinuous (twoUsualWitness γ) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hcase : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  intro a
  rcases hcase a with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    simp only [twoUsualWitness] <;>
    norm_num <;>
    linarith

theorem twoUsualWitness_attains (γ : ℝ) :
    Real.pi ^ 2 * mass (twoUsualWitness γ) =
      5 * Real.pi ^ 4 / 16 +
        (2 * J (twoUsualWitness γ) - Real.pi ^ 2 / 2) ^ 2 := by
  rw [mass_twoUsualWitness, J_twoUsualWitness]
  ring

theorem J_twoDualWitness (γ : ℝ) :
    J (twoDualWitness γ) = -(Real.pi ^ 2 / 8 + (Real.pi / 2) * γ) := by
  unfold twoDualWitness
  rw [J_dagger, J_twoUsualWitness]

theorem mass_twoDualWitness (γ : ℝ) :
    mass (twoDualWitness γ) = mass (twoUsualWitness γ) := by
  unfold twoDualWitness
  exact mass_dagger _

theorem isAdmissibleContinuous_twoDualWitness {γ : ℝ}
    (h0 : 0 ≤ γ) (h1 : γ ≤ Real.pi / 2) :
    IsAdmissibleContinuous (twoDualWitness γ) := by
  intro a
  have ha := isAdmissibleContinuous_twoUsualWitness h0 h1 a
  refine ⟨ha.2.1, ha.1, ?_⟩
  simpa [twoDualWitness, daggerParams, add_comm] using ha.2.2

theorem twoDualWitness_attains (γ : ℝ) :
    Real.pi ^ 2 * mass (twoDualWitness γ) =
      5 * Real.pi ^ 4 / 16 +
        (2 * J (twoDualWitness γ) + Real.pi ^ 2 / 2) ^ 2 := by
  rw [mass_twoDualWitness, J_twoDualWitness, mass_twoUsualWitness]
  ring

theorem mass_le_shield_of_abs_J_eq_quarter {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hJ : |J p| = Real.pi ^ 2 / 4) :
    mass p ≤ 5 * Real.pi ^ 2 / 16 := by
  have hA := pi_sq_mass_le_attractive_lobe p h
  have hR := pi_sq_mass_le_repulsive_lobe p h
  have hπ : 0 < Real.pi ^ 2 := by positivity
  rcases eq_or_eq_neg_of_abs_eq hJ with hp | hn
  · have : 2 * J p - Real.pi ^ 2 / 2 = 0 := by linarith
    rw [this, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hA
    nlinarith [hA, hπ]
  · have : 2 * J p + Real.pi ^ 2 / 2 = 0 := by linarith
    rw [this, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hR
    nlinarith [hR, hπ]

private theorem pi_div_four_nonneg : (0 : ℝ) ≤ Real.pi / 4 := by
  have : 0 < Real.pi := Real.pi_pos
  linarith

private theorem pi_div_four_le_pi_div_two : Real.pi / 4 ≤ Real.pi / 2 := by
  have : 0 < Real.pi := Real.pi_pos
  linarith

theorem exists_admissible_J_quarter_mass_eq_shield :
    ∃ p : TorsionParams, IsAdmissibleContinuous p ∧
      J p = Real.pi ^ 2 / 4 ∧ mass p = 5 * Real.pi ^ 2 / 16 :=
  ⟨twoUsualWitness (Real.pi / 4),
    isAdmissibleContinuous_twoUsualWitness pi_div_four_nonneg
      pi_div_four_le_pi_div_two,
    by rw [J_twoUsualWitness]; ring,
    by rw [mass_twoUsualWitness, sub_self]; ring⟩

/-! ### Independent-axis and opposed-wall constructors -/

noncomputable def crossUsualDual (x y : ℝ) : TorsionParams where
  alpha := fun a => if a.val = 0 then x else 0
  beta := fun a => if a.val = 1 then y else 0

theorem J_crossUsualDual (x y : ℝ) :
    J (crossUsualDual x y) = (1 / 2) * (x ^ 2 - y ^ 2) := by
  rw [J_coef]
  simp only [crossUsualDual, Fin.sum_univ_three]
  norm_num
  try ring

theorem mass_crossUsualDual (x y : ℝ) :
    mass (crossUsualDual x y) = (1 / 2) * (x ^ 2 + y ^ 2) := by
  rw [mass_coef]
  simp only [crossUsualDual, Fin.sum_univ_three]
  norm_num
  try ring

theorem isAdmissibleContinuous_crossUsualDual {x y : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ Real.pi / 2)
    (hy : y ≤ Real.pi / 2) :
    IsAdmissibleContinuous (crossUsualDual x y) := by
  have hcase : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  intro a
  rcases hcase a with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    simp only [crossUsualDual] <;>
    norm_num <;>
    linarith [hx0, hy0, hx, hy]

/-- Opposed pair of strength `s` plus a wall of split `γ`. -/
noncomputable def opposedWall (s γ : ℝ) : TorsionParams where
  alpha := fun a => if a.val = 0 then s else if a.val = 1 then 0 else γ
  beta := fun a =>
    if a.val = 0 then 0 else if a.val = 1 then s else Real.pi / 2 - γ

theorem J_opposedWall (s γ : ℝ) :
    J (opposedWall s γ) = (Real.pi / 2) * (γ - Real.pi / 4) := by
  rw [J_coef]
  simp only [opposedWall, Fin.sum_univ_three]
  norm_num
  ring

theorem mass_opposedWall (s γ : ℝ) :
    mass (opposedWall s γ) =
      s ^ 2 + (1 / 2) * (γ ^ 2 + (Real.pi / 2 - γ) ^ 2) := by
  rw [mass_coef]
  simp only [opposedWall, Fin.sum_univ_three]
  norm_num
  ring

theorem isAdmissibleContinuous_opposedWall {s γ : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ Real.pi / 2)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ Real.pi / 2) :
    IsAdmissibleContinuous (opposedWall s γ) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hcase : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  intro a
  rcases hcase a with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    simp only [opposedWall] <;>
    norm_num <;>
    linarith [hs0, hs, hγ0, hγ, hπ]

/-- One axis locked purely usual; the other two carry an independent pair. -/
noncomputable def oneUsualCross (x y : ℝ) : TorsionParams where
  alpha := fun a => if a.val = 0 then Real.pi / 2 else if a.val = 1 then x else 0
  beta := fun a => if a.val = 2 then y else 0

theorem J_oneUsualCross (x y : ℝ) :
    J (oneUsualCross x y) = Real.pi ^ 2 / 8 + (1 / 2) * (x ^ 2 - y ^ 2) := by
  rw [J_coef]
  simp only [oneUsualCross, Fin.sum_univ_three]
  norm_num
  ring

theorem mass_oneUsualCross (x y : ℝ) :
    mass (oneUsualCross x y) = Real.pi ^ 2 / 8 + (1 / 2) * (x ^ 2 + y ^ 2) := by
  rw [mass_coef]
  simp only [oneUsualCross, Fin.sum_univ_three]
  norm_num
  ring

theorem isAdmissibleContinuous_oneUsualCross {x y : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ Real.pi / 2)
    (hy : y ≤ Real.pi / 2) :
    IsAdmissibleContinuous (oneUsualCross x y) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hcase : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  intro a
  rcases hcase a with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    simp only [oneUsualCross] <;>
    norm_num <;>
    linarith [hx0, hy0, hx, hy, hπ]

/-- Two axes locked purely usual; the third is a free cone axis. -/
noncomputable def twoUsualRest (x y : ℝ) : TorsionParams where
  alpha := fun a =>
    if a.val = 0 then Real.pi / 2 else if a.val = 1 then Real.pi / 2 else x
  beta := fun a => if a.val = 2 then y else 0

theorem J_twoUsualRest (x y : ℝ) :
    J (twoUsualRest x y) = Real.pi ^ 2 / 4 + (1 / 2) * (x ^ 2 - y ^ 2) := by
  rw [J_coef]
  simp only [twoUsualRest, Fin.sum_univ_three]
  norm_num
  ring

theorem mass_twoUsualRest (x y : ℝ) :
    mass (twoUsualRest x y) = Real.pi ^ 2 / 4 + (1 / 2) * (x ^ 2 + y ^ 2) := by
  rw [mass_coef]
  simp only [twoUsualRest, Fin.sum_univ_three]
  norm_num
  ring

theorem isAdmissibleContinuous_twoUsualRest {x y : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hsum : x + y ≤ Real.pi / 2) :
    IsAdmissibleContinuous (twoUsualRest x y) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hcase : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  intro a
  rcases hcase a with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    simp only [twoUsualRest] <;>
    norm_num <;>
    linarith [hx0, hy0, hsum, hπ]

/-! ### Square-root comparison on a single cone axis -/

private theorem le_of_sq_le_sq₀ {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (sq_le_sq₀ ha hb).mp h


private theorem m_le_pi_sq_div_eight_of_axis {j m : ℝ}
    (hJ : |j| ≤ Real.pi ^ 2 / 8)
    (hceil : m ≤ Real.pi ^ 2 / 16 + 4 * j ^ 2 / Real.pi ^ 2) :
    m ≤ Real.pi ^ 2 / 8 := by
  have hπ : 0 < Real.pi ^ 2 := by positivity
  have hj2 : j ^ 2 ≤ (Real.pi ^ 2 / 8) ^ 2 :=
    sq_le_sq.mpr (by
      have : |Real.pi ^ 2 / 8| = Real.pi ^ 2 / 8 := abs_of_nonneg (by positivity)
      rwa [this])
  have : 4 * j ^ 2 / Real.pi ^ 2 ≤ Real.pi ^ 2 / 16 := by
    have hnum : 4 * j ^ 2 ≤ 4 * (Real.pi ^ 2 / 8) ^ 2 := by gcongr
    have hid : 4 * (Real.pi ^ 2 / 8) ^ 2 / Real.pi ^ 2 = Real.pi ^ 2 / 16 := by
      field_simp; try ring
    calc 4 * j ^ 2 / Real.pi ^ 2
        ≤ 4 * (Real.pi ^ 2 / 8) ^ 2 / Real.pi ^ 2 :=
          div_le_div_of_nonneg_right hnum (le_of_lt hπ)
      _ = Real.pi ^ 2 / 16 := hid
  linarith

/-- \(\sqrt{m+j}+\sqrt{m-j}\le\pi/2\) on a single admissible axis. -/
theorem sqrt_pair_sum_le_half_pi {j m : ℝ}
    (habs : |j| ≤ m)
    (hJ : |j| ≤ Real.pi ^ 2 / 8)
    (hceil : m ≤ Real.pi ^ 2 / 16 + 4 * j ^ 2 / Real.pi ^ 2) :
    Real.sqrt (m + j) + Real.sqrt (m - j) ≤ Real.pi / 2 := by
  have hm8 := m_le_pi_sq_div_eight_of_axis hJ hceil
  have hmj : 0 ≤ m - j := sub_nonneg.mpr (abs_le.mp habs).2
  have hmj' : 0 ≤ m + j := by linarith [(abs_le.mp habs).1]
  have hrad : 0 ≤ m ^ 2 - j ^ 2 := by
    nlinarith [sq_abs j, mul_self_nonneg (m - |j|), habs]
  have hs : 0 ≤ Real.pi ^ 2 / 4 - 2 * m := by nlinarith
  have hπ : 0 < Real.pi ^ 2 := by positivity
  have hceil' : Real.pi ^ 2 * m ≤ Real.pi ^ 4 / 16 + 4 * j ^ 2 := by
    have := mul_le_mul_of_nonneg_right hceil (le_of_lt hπ)
    have : (Real.pi ^ 2 / 16 + 4 * j ^ 2 / Real.pi ^ 2) * Real.pi ^ 2 =
        Real.pi ^ 4 / 16 + 4 * j ^ 2 := by
      field_simp
      try ring
    linarith
  have hsq : (2 * Real.sqrt (m ^ 2 - j ^ 2)) ^ 2 ≤
      (Real.pi ^ 2 / 4 - 2 * m) ^ 2 := by
    have : (2 * Real.sqrt (m ^ 2 - j ^ 2)) ^ 2 = 4 * (m ^ 2 - j ^ 2) := by
      ring_nf
      rw [Real.sq_sqrt hrad]
      ring
    rw [this]
    nlinarith [hceil']
  have hsqrt0 : (0 : ℝ) ≤ 2 * Real.sqrt (m ^ 2 - j ^ 2) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have h2 : 2 * Real.sqrt (m ^ 2 - j ^ 2) ≤ Real.pi ^ 2 / 4 - 2 * m :=
    le_of_sq_le_sq₀ hsqrt0 hs hsq
  have hcross : Real.sqrt (m + j) * Real.sqrt (m - j) =
      Real.sqrt (m ^ 2 - j ^ 2) := by
    have hmul := Real.sqrt_mul hmj' (m - j)
    have : (m + j) * (m - j) = m ^ 2 - j ^ 2 := by ring
    rw [← hmul, this]
  have hsumsq :
      (Real.sqrt (m + j) + Real.sqrt (m - j)) ^ 2 =
        2 * m + 2 * Real.sqrt (m ^ 2 - j ^ 2) := by
    ring_nf
    nlinarith [Real.sq_sqrt hmj', Real.sq_sqrt hmj, hcross]
  have : (Real.sqrt (m + j) + Real.sqrt (m - j)) ^ 2 ≤ (Real.pi / 2) ^ 2 := by
    have : 2 * m + 2 * Real.sqrt (m ^ 2 - j ^ 2) ≤ Real.pi ^ 2 / 4 := by
      linarith [h2]
    have : (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 := by ring
    linarith
  exact le_of_sq_le_sq₀
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (le_of_lt Real.pi_div_two_pos) this

/-! ### Filling the envelope -/

private theorem exists_nonneg_J_of_JM (Jval Mval : ℝ)
    (hJ0 : 0 ≤ Jval) (hJmax : Jval ≤ 3 * Real.pi ^ 2 / 8)
    (hMlo : Jval ≤ Mval) (hMhi : Mval ≤ controlCeiling Jval) :
    ∃ p : TorsionParams, IsAdmissibleContinuous p ∧ J p = Jval ∧
      mass p = Mval := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ2 : 0 < Real.pi ^ 2 := by positivity
  by_cases h8 : Jval ≤ Real.pi ^ 2 / 8
  · -- Central band: independent axes, then opposed wall.
    by_cases hcross : Mval ≤ Real.pi ^ 2 / 4 - Jval
    · refine ⟨crossUsualDual (Real.sqrt (Mval + Jval)) (Real.sqrt (Mval - Jval)),
        ?_, ?_, ?_⟩
      · refine isAdmissibleContinuous_crossUsualDual (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _) ?_ ?_
        · have : Mval + Jval ≤ Real.pi ^ 2 / 4 := by linarith
          have hnn : 0 ≤ Mval + Jval := add_nonneg (le_trans hJ0 hMlo) hJ0
          have := Real.sqrt_le_sqrt this
          have : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring,
              Real.sqrt_sq (by positivity)]
          linarith
        · have : Mval - Jval ≤ Real.pi ^ 2 / 4 := by linarith
          have hnn : 0 ≤ Mval - Jval := sub_nonneg.mpr hMlo
          have := Real.sqrt_le_sqrt this
          have : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring,
              Real.sqrt_sq (by positivity)]
          linarith
      · rw [J_crossUsualDual, Real.sq_sqrt (add_nonneg (le_trans hJ0 hMlo) hJ0),
          Real.sq_sqrt (sub_nonneg.mpr hMlo)]
        ring
      · rw [mass_crossUsualDual, Real.sq_sqrt (add_nonneg (le_trans hJ0 hMlo) hJ0),
          Real.sq_sqrt (sub_nonneg.mpr hMlo)]
        ring
    · -- Opposed wall. The split is the central-family parameter.
      set γ := Real.pi / 4 + 2 * Jval / Real.pi with hγdef
      have hγ0 : 0 ≤ γ := by
        unfold γ
        have : 0 ≤ 2 * Jval / Real.pi := div_nonneg (by linarith) (le_of_lt hπ)
        linarith [pi_div_four_nonneg]
      have hγ1 : γ ≤ Real.pi / 2 := by
        unfold γ
        have : 2 * Jval / Real.pi ≤ Real.pi / 4 := by
          have : 2 * Jval ≤ Real.pi ^ 2 / 4 := by nlinarith [h8]
          have := div_le_div_of_nonneg_right this (le_of_lt hπ)
          have hid : Real.pi ^ 2 / 4 / Real.pi = Real.pi / 4 := by
            field_simp; try ring
          linarith
        linarith
      have hwall :
          (1 / 2) * (γ ^ 2 + (Real.pi / 2 - γ) ^ 2) =
            Real.pi ^ 2 / 16 + 4 * Jval ^ 2 / Real.pi ^ 2 := by
        have : γ - Real.pi / 4 = 2 * Jval / Real.pi := by unfold γ; ring
        have hγ2 : γ ^ 2 + (Real.pi / 2 - γ) ^ 2 =
            Real.pi ^ 2 / 8 + 2 * (2 * Jval / Real.pi) ^ 2 := by
          have h1 : Real.pi / 2 - γ = Real.pi / 4 - (2 * Jval / Real.pi) := by
            unfold γ; ring
          rw [h1]
          nlinarith [this]
        have : 2 * (2 * Jval / Real.pi) ^ 2 = 8 * Jval ^ 2 / Real.pi ^ 2 := by
          field_simp; ring
        rw [hγ2, this]
        field_simp
        ring
      have hs2 : 0 ≤ Mval - (Real.pi ^ 2 / 16 + 4 * Jval ^ 2 / Real.pi ^ 2) := by
        have hfrac :
            4 * Jval ^ 2 / Real.pi ^ 2 + Jval - 3 * Real.pi ^ 2 / 16 =
              (8 * Jval - Real.pi ^ 2) * (8 * Jval + 3 * Real.pi ^ 2) /
                (16 * Real.pi ^ 2) := by
          field_simp; ring
        have hnum :
            (8 * Jval - Real.pi ^ 2) * (8 * Jval + 3 * Real.pi ^ 2) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by nlinarith [h8])
            (by nlinarith [hJ0, hπ2])
        have hoverlap :
            Real.pi ^ 2 / 16 + 4 * Jval ^ 2 / Real.pi ^ 2 ≤
              Real.pi ^ 2 / 4 - Jval := by
          have : 4 * Jval ^ 2 / Real.pi ^ 2 + Jval - 3 * Real.pi ^ 2 / 16 ≤ 0 := by
            rw [hfrac]
            exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
          linarith
        linarith [not_le.mp hcross]
      set s := Real.sqrt (Mval - (Real.pi ^ 2 / 16 + 4 * Jval ^ 2 / Real.pi ^ 2))
        with hsdef
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs : s ≤ Real.pi / 2 := by
        have hM : Mval ≤ 5 * Real.pi ^ 2 / 16 + 4 * Jval ^ 2 / Real.pi ^ 2 := by
          have : controlEnvelopeNum Jval ≤ 4 * Jval ^ 2 := min_le_left _ _
          have : controlCeiling Jval ≤
              5 * Real.pi ^ 2 / 16 + 4 * Jval ^ 2 / Real.pi ^ 2 := by
            unfold controlCeiling
            gcongr
          linarith
        have : s ^ 2 ≤ (Real.pi / 2) ^ 2 := by
          rw [hsdef, Real.sq_sqrt hs2]
          nlinarith [hM]
        exact le_of_sq_le_sq₀ hs0 (le_of_lt Real.pi_div_two_pos) this
      refine ⟨opposedWall s γ, isAdmissibleContinuous_opposedWall hs0 hs hγ0 hγ1,
        ?_, ?_⟩
      · rw [J_opposedWall, hγdef]
        field_simp
        ring
      · rw [mass_opposedWall, hwall, hsdef, Real.sq_sqrt hs2]
        ring
  · -- Outside the central band: `π²/8 < J ≤ 3π²/8`.
    have h8lt : Real.pi ^ 2 / 8 < Jval := lt_of_not_ge h8
    by_cases h4 : Jval ≤ Real.pi ^ 2 / 4
    · by_cases hpin : Mval ≤ Real.pi ^ 2 / 2 - Jval
      · refine ⟨oneUsualCross (Real.sqrt (Mval + Jval - Real.pi ^ 2 / 4))
            (Real.sqrt (Mval - Jval)), ?_, ?_, ?_⟩
        · have hx2 : 0 ≤ Mval + Jval - Real.pi ^ 2 / 4 := by
            nlinarith [hMlo, h8lt]
          have hy2 : 0 ≤ Mval - Jval := sub_nonneg.mpr hMlo
          refine isAdmissibleContinuous_oneUsualCross (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _) ?_ ?_
          · have : Mval + Jval - Real.pi ^ 2 / 4 ≤ Real.pi ^ 2 / 4 := by
              nlinarith [hpin]
            have := Real.sqrt_le_sqrt this
            have : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
              rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring,
                Real.sqrt_sq (by positivity)]
            linarith
          · have : Mval - Jval ≤ Real.pi ^ 2 / 4 := by nlinarith [hpin, h4]
            have := Real.sqrt_le_sqrt this
            have : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
              rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring,
                Real.sqrt_sq (by positivity)]
            linarith
        · have hx2 : 0 ≤ Mval + Jval - Real.pi ^ 2 / 4 := by
            nlinarith [hMlo, h8lt]
          have hy2 : 0 ≤ Mval - Jval := sub_nonneg.mpr hMlo
          rw [J_oneUsualCross, Real.sq_sqrt hx2, Real.sq_sqrt hy2]
          ring
        · have hx2 : 0 ≤ Mval + Jval - Real.pi ^ 2 / 4 := by
            nlinarith [hMlo, h8lt]
          have hy2 : 0 ≤ Mval - Jval := sub_nonneg.mpr hMlo
          rw [mass_oneUsualCross, Real.sq_sqrt hx2, Real.sq_sqrt hy2]
          ring
      · -- Two usual rest, third axis on the cone.
        set j := Jval - Real.pi ^ 2 / 4
        set m := Mval - Real.pi ^ 2 / 4
        have habs : |j| ≤ m := by
          have : Jval ≤ Mval := hMlo
          unfold j m
          rw [abs_of_nonpos (by linarith [h4])]
          nlinarith [not_le.mp hpin]
        have hjB : |j| ≤ Real.pi ^ 2 / 8 := by
          unfold j
          rw [abs_of_nonpos (by linarith [h4])]
          nlinarith [h8lt]
        have hceilA : m ≤ Real.pi ^ 2 / 16 + 4 * j ^ 2 / Real.pi ^ 2 := by
          have hnumle : controlEnvelopeNum Jval ≤
              (2 * Jval - Real.pi ^ 2 / 2) ^ 2 :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          have hdiv : controlEnvelopeNum Jval / Real.pi ^ 2 ≤
              (2 * Jval - Real.pi ^ 2 / 2) ^ 2 / Real.pi ^ 2 :=
            div_le_div_of_nonneg_right hnumle (le_of_lt hπ2)
          have hM : Mval ≤ 5 * Real.pi ^ 2 / 16 +
              (2 * Jval - Real.pi ^ 2 / 2) ^ 2 / Real.pi ^ 2 := by
            unfold controlCeiling at hMhi
            linarith [hMhi, hdiv]
          unfold j m
          have hid : (2 * Jval - Real.pi ^ 2 / 2) ^ 2 / Real.pi ^ 2 =
              4 * (Jval - Real.pi ^ 2 / 4) ^ 2 / Real.pi ^ 2 := by
            ring
          linarith [hM, hid]
        have hsum := sqrt_pair_sum_le_half_pi habs hjB hceilA
        have hx0 : 0 ≤ Real.sqrt (m + j) := Real.sqrt_nonneg _
        have hy0 : 0 ≤ Real.sqrt (m - j) := Real.sqrt_nonneg _
        refine ⟨twoUsualRest (Real.sqrt (m + j)) (Real.sqrt (m - j)),
          isAdmissibleContinuous_twoUsualRest hx0 hy0 hsum, ?_, ?_⟩
        · have hmj : 0 ≤ m + j := by
            unfold j m; nlinarith [hMlo]
          have hmj' : 0 ≤ m - j := by
            unfold j m; nlinarith [not_le.mp hpin]
          rw [J_twoUsualRest, Real.sq_sqrt hmj, Real.sq_sqrt hmj']
          unfold j m
          ring
        · have hmj : 0 ≤ m + j := by
            unfold j m; nlinarith [hMlo]
          have hmj' : 0 ≤ m - j := by
            unfold j m; nlinarith [not_le.mp hpin]
          rw [mass_twoUsualRest, Real.sq_sqrt hmj, Real.sq_sqrt hmj']
          unfold j m
          ring
    · -- High band `π²/4 < J ≤ 3π²/8`.
      have h4lt : Real.pi ^ 2 / 4 < Jval := lt_of_not_ge h4
      set j := Jval - Real.pi ^ 2 / 4
      set m := Mval - Real.pi ^ 2 / 4
      have habs : |j| ≤ m := by
        unfold j m
        rw [abs_of_nonneg (le_of_lt (sub_pos.mpr h4lt))]
        linarith [hMlo]
      have hjB : |j| ≤ Real.pi ^ 2 / 8 := by
        unfold j
        rw [abs_of_nonneg (le_of_lt (sub_pos.mpr h4lt))]
        nlinarith [hJmax]
      have hceilA : m ≤ Real.pi ^ 2 / 16 + 4 * j ^ 2 / Real.pi ^ 2 := by
        have hnumle : controlEnvelopeNum Jval ≤
            (2 * Jval - Real.pi ^ 2 / 2) ^ 2 :=
          le_trans (min_le_right _ _) (min_le_left _ _)
        have hdiv : controlEnvelopeNum Jval / Real.pi ^ 2 ≤
            (2 * Jval - Real.pi ^ 2 / 2) ^ 2 / Real.pi ^ 2 :=
          div_le_div_of_nonneg_right hnumle (le_of_lt hπ2)
        have hM : Mval ≤ 5 * Real.pi ^ 2 / 16 +
            (2 * Jval - Real.pi ^ 2 / 2) ^ 2 / Real.pi ^ 2 := by
          unfold controlCeiling at hMhi
          linarith [hMhi, hdiv]
        unfold j m
        have hid : (2 * Jval - Real.pi ^ 2 / 2) ^ 2 / Real.pi ^ 2 =
            4 * (Jval - Real.pi ^ 2 / 4) ^ 2 / Real.pi ^ 2 := by
          ring
        linarith [hM, hid]
      have hsum := sqrt_pair_sum_le_half_pi habs hjB hceilA
      have hx0 : 0 ≤ Real.sqrt (m + j) := Real.sqrt_nonneg _
      have hy0 : 0 ≤ Real.sqrt (m - j) := Real.sqrt_nonneg _
      refine ⟨twoUsualRest (Real.sqrt (m + j)) (Real.sqrt (m - j)),
        isAdmissibleContinuous_twoUsualRest hx0 hy0 hsum, ?_, ?_⟩
      · have hmj : 0 ≤ m + j := by unfold j m; nlinarith
        have hmj' : 0 ≤ m - j := by unfold j m; nlinarith [hMlo]
        rw [J_twoUsualRest, Real.sq_sqrt hmj, Real.sq_sqrt hmj']
        unfold j m
        ring
      · have hmj : 0 ≤ m + j := by unfold j m; nlinarith
        have hmj' : 0 ≤ m - j := by unfold j m; nlinarith [hMlo]
        rw [mass_twoUsualRest, Real.sq_sqrt hmj, Real.sq_sqrt hmj']
        unfold j m
        ring

/-- Every pair under the envelope is realised. -/
theorem exists_admissible_of_JM {Jval Mval : ℝ}
    (hJmax : |Jval| ≤ 3 * Real.pi ^ 2 / 8)
    (hMlo : |Jval| ≤ Mval) (hMhi : Mval ≤ controlCeiling Jval) :
    ∃ p : TorsionParams, IsAdmissibleContinuous p ∧ J p = Jval ∧
      mass p = Mval := by
  rcases le_or_gt 0 Jval with hpos | hneg
  · exact exists_nonneg_J_of_JM Jval Mval hpos
      (abs_le.mp hJmax).2 (by rwa [abs_of_nonneg hpos] at hMlo) hMhi
  · have hJ0 : 0 ≤ -Jval := by linarith
    have hJmax' : -Jval ≤ 3 * Real.pi ^ 2 / 8 := by
      have := (abs_le.mp hJmax).1
      linarith
    have hMlo' : -Jval ≤ Mval := by
      have : |Jval| = -Jval := abs_of_neg hneg
      rwa [← this]
    have hMhi' : Mval ≤ controlCeiling (-Jval) := by
      rwa [controlCeiling_neg]
    obtain ⟨q, hq, hJq, hMq⟩ :=
      exists_nonneg_J_of_JM (-Jval) Mval hJ0 hJmax' hMlo' hMhi'
    refine ⟨daggerParams q, ?_, ?_, ?_⟩
    · intro a
      have ha := hq a
      refine ⟨ha.2.1, ha.1, ?_⟩
      simpa [daggerParams, add_comm] using ha.2.2
    · rw [J_dagger, hJq, neg_neg]
    · rw [mass_dagger, hMq]

end Gravity

end DstDiophantine
