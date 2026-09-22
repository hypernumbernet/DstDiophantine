import DstDiophantine.Gravity.ControlDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The envelope is a lock

`ControlDomain` shows that the admissible cone fills the three-lobed region
under the envelope, and names families that attain it. Attainment is
exhaustive. A configuration lies on the envelope if and only if every axis
is on the wall and at least two axes occupy corners of the cone. The usual
rotor then determines the dual angles, so a dual-only motion meets the
envelope at most once.

## Paper boundary (do **not** claim)

No electromagnetic coupling, no laboratory protocol, and no identification
of the dual-channel force \(u\).
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-! ### Wall, corners, and the two same-sector patterns -/

def OnWall (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, p.alpha a + p.beta a = Real.pi / 2

def IsPureUsual (p : TorsionParams) (a : Fin 3) : Prop :=
  p.alpha a = Real.pi / 2 ∧ p.beta a = 0

def IsPureDual (p : TorsionParams) (a : Fin 3) : Prop :=
  p.alpha a = 0 ∧ p.beta a = Real.pi / 2

def IsCorner (p : TorsionParams) (a : Fin 3) : Prop :=
  IsPureUsual p a ∨ IsPureDual p a

/-- At least two axes occupy corners of the cone. -/
def TwoCorners (p : TorsionParams) : Prop :=
  (IsCorner p 0 ∧ IsCorner p 1) ∨
    (IsCorner p 0 ∧ IsCorner p 2) ∨
    (IsCorner p 1 ∧ IsCorner p 2)

private def TwoPureUsual (p : TorsionParams) : Prop :=
  (IsPureUsual p 0 ∧ IsPureUsual p 1) ∨
    (IsPureUsual p 0 ∧ IsPureUsual p 2) ∨
    (IsPureUsual p 1 ∧ IsPureUsual p 2)

private def TwoPureDual (p : TorsionParams) : Prop :=
  (IsPureDual p 0 ∧ IsPureDual p 1) ∨
    (IsPureDual p 0 ∧ IsPureDual p 2) ∨
    (IsPureDual p 1 ∧ IsPureDual p 2)

/-- One axis purely usual and another purely dual. -/
private def OpposedCorners (p : TorsionParams) : Prop :=
  (IsPureUsual p 0 ∧ IsPureDual p 1) ∨ (IsPureDual p 0 ∧ IsPureUsual p 1) ∨
    (IsPureUsual p 0 ∧ IsPureDual p 2) ∨ (IsPureDual p 0 ∧ IsPureUsual p 2) ∨
    (IsPureUsual p 1 ∧ IsPureDual p 2) ∨ (IsPureDual p 1 ∧ IsPureUsual p 2)

private theorem beta_eq_wall {p : TorsionParams} (hw : OnWall p) (a : Fin 3) :
    p.beta a = Real.pi / 2 - p.alpha a := by
  have := hw a
  linarith

/-! ### Axis trade-off, equality case -/

private theorem axis_trade_off_eq_iff {k α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ k) (hk : 0 ≤ k) :
    2 * k ^ 2 * (α ^ 2 + β ^ 2) = k ^ 4 + (α ^ 2 - β ^ 2) ^ 2 ↔
      α + β = k := by
  have hdiff :
      k ^ 4 + (α ^ 2 - β ^ 2) ^ 2 - 2 * k ^ 2 * (α ^ 2 + β ^ 2) =
        (k ^ 2 - (α + β) ^ 2) * (k ^ 2 - (α - β) ^ 2) := by ring
  constructor
  · intro h
    have hprod : (k ^ 2 - (α + β) ^ 2) * (k ^ 2 - (α - β) ^ 2) = 0 := by
      linarith
    rcases mul_eq_zero.mp hprod with hsum | hdiffax
    · have hsq : (α + β) ^ 2 = k ^ 2 := by linarith
      have habs : |α + β| = |k| := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
      rwa [abs_of_nonneg (add_nonneg hα hβ), abs_of_nonneg hk] at habs
    · have hsq : (α - β) ^ 2 = k ^ 2 := by linarith
      have habs : |α - β| = |k| := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
      rw [abs_of_nonneg hk] at habs
      have hcmp : |α - β| ≤ α + β := by
        have hsqle : (α - β) ^ 2 ≤ (α + β) ^ 2 := by nlinarith
        have := sq_le_sq.mp hsqle
        rwa [abs_of_nonneg (add_nonneg hα hβ)] at this
      linarith [hs]
  · intro h
    have : (α + β) ^ 2 = k ^ 2 := by rw [h]
    nlinarith [hdiff]

private theorem isPureUsual_iff_axisSigned {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    IsPureUsual p a ↔ axisSigned p a = (Real.pi / 2) ^ 2 := by
  constructor
  · intro hu
    rw [axisSigned, hu.1, hu.2]
    ring
  · intro ht
    have hα := (h a).1
    have hβ := (h a).2.1
    have hαle : p.alpha a ≤ Real.pi / 2 :=
      admissibleContinuous_alpha_le_half_pi p h a
    have : p.beta a = 0 ∧ p.alpha a = Real.pi / 2 := by
      have hsq : p.alpha a ^ 2 ≤ (Real.pi / 2) ^ 2 := by
        nlinarith [sq_nonneg (p.alpha a - Real.pi / 2)]
      have hle : p.alpha a ^ 2 - p.beta a ^ 2 ≤ p.alpha a ^ 2 := by
        nlinarith [sq_nonneg (p.beta a)]
      have : p.alpha a ^ 2 = (Real.pi / 2) ^ 2 := by
        rw [axisSigned] at ht
        linarith
      have hβ0 : p.beta a = 0 := by
        rw [axisSigned] at ht
        nlinarith
      have hαeq : p.alpha a = Real.pi / 2 := by nlinarith
      exact ⟨hβ0, hαeq⟩
    exact ⟨this.2, this.1⟩

private theorem isPureDual_iff_axisSigned {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    IsPureDual p a ↔ axisSigned p a = -((Real.pi / 2) ^ 2) := by
  constructor
  · intro hd
    rw [axisSigned, hd.1, hd.2]
    ring
  · intro ht
    have hα := (h a).1
    have hβ := (h a).2.1
    have hβle : p.beta a ≤ Real.pi / 2 :=
      admissibleContinuous_beta_le_half_pi p h a
    have : p.alpha a = 0 ∧ p.beta a = Real.pi / 2 := by
      have hsq : p.beta a ^ 2 ≤ (Real.pi / 2) ^ 2 := by
        nlinarith [sq_nonneg (p.beta a - Real.pi / 2)]
      have : p.beta a ^ 2 = (Real.pi / 2) ^ 2 := by
        rw [axisSigned] at ht
        nlinarith [sq_nonneg (p.alpha a)]
      have hα0 : p.alpha a = 0 := by
        rw [axisSigned] at ht
        nlinarith
      have hβeq : p.beta a = Real.pi / 2 := by nlinarith
      exact ⟨hα0, hβeq⟩
    exact ⟨this.1, this.2⟩

private theorem signedSum3 (p : TorsionParams) :
    axisSigned p 0 + axisSigned p 1 + axisSigned p 2 = 2 * J p := by
  simpa [Fin.sum_univ_three] using signedSum_eq_two_J p

private theorem axisSigned_le_K {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    axisSigned p a ≤ (Real.pi / 2) ^ 2 :=
  (abs_le.mp (axis_abs_density_le (h a).1 (h a).2.1 (h a).2.2)).2

private theorem axisSigned_ge_negK {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    -((Real.pi / 2) ^ 2) ≤ axisSigned p a :=
  (abs_le.mp (axis_abs_density_le (h a).1 (h a).2.1 (h a).2.2)).1

private theorem le_J_of_twoPureUsual {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hUU : TwoPureUsual p) :
    Real.pi ^ 2 / 8 ≤ J p := by
  have hT := signedSum3 p
  have hK : (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 := by ring
  rcases hUU with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
  · have ht0 := (isPureUsual_iff_axisSigned h 0).mp h0
    have ht1 := (isPureUsual_iff_axisSigned h 1).mp h1
    have ht2 := axisSigned_ge_negK h 2
    nlinarith [hT, ht0, ht1, ht2, hK]
  · have ht0 := (isPureUsual_iff_axisSigned h 0).mp h0
    have ht2 := (isPureUsual_iff_axisSigned h 2).mp h2
    have ht1 := axisSigned_ge_negK h 1
    nlinarith [hT, ht0, ht2, ht1, hK]
  · have ht1 := (isPureUsual_iff_axisSigned h 1).mp h1
    have ht2 := (isPureUsual_iff_axisSigned h 2).mp h2
    have ht0 := axisSigned_ge_negK h 0
    nlinarith [hT, ht1, ht2, ht0, hK]

private theorem J_le_of_twoPureDual {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hDD : TwoPureDual p) :
    J p ≤ -(Real.pi ^ 2 / 8) := by
  have hT := signedSum3 p
  have hK : (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 := by ring
  rcases hDD with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
  · have ht0 := (isPureDual_iff_axisSigned h 0).mp h0
    have ht1 := (isPureDual_iff_axisSigned h 1).mp h1
    have ht2 := axisSigned_le_K h 2
    nlinarith [hT, ht0, ht1, ht2, hK]
  · have ht0 := (isPureDual_iff_axisSigned h 0).mp h0
    have ht2 := (isPureDual_iff_axisSigned h 2).mp h2
    have ht1 := axisSigned_le_K h 1
    nlinarith [hT, ht0, ht2, ht1, hK]
  · have ht1 := (isPureDual_iff_axisSigned h 1).mp h1
    have ht2 := (isPureDual_iff_axisSigned h 2).mp h2
    have ht0 := axisSigned_le_K h 0
    nlinarith [hT, ht1, ht2, ht0, hK]

/-! ### Pairing of the three axis densities -/

private theorem pair_abs_le {K x y : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ K)
    (hK : 0 ≤ K) :
    K * |x + y| ≤ |K ^ 2 + x * y| := by
  have hx2 : x ^ 2 ≤ K ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg hK]
    exact hx
  have hy2 : y ^ 2 ≤ K ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg hK]
    exact hy
  have hnonneg : 0 ≤ (K ^ 2 - x ^ 2) * (K ^ 2 - y ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hx2) (sub_nonneg.mpr hy2)
  have hdiff :
      (K ^ 2 + x * y) ^ 2 - (K * (x + y)) ^ 2 =
        (K ^ 2 - x ^ 2) * (K ^ 2 - y ^ 2) := by ring
  have hsq : (K * (x + y)) ^ 2 ≤ (K ^ 2 + x * y) ^ 2 := by linarith
  have habs : |K * (x + y)| ≤ |K ^ 2 + x * y| := sq_le_sq.mp hsq
  rwa [abs_mul, abs_of_nonneg hK] at habs

private theorem pair_abs_eq_iff {K x y : ℝ} (hK : 0 ≤ K) :
    K * |x + y| = |K ^ 2 + x * y| ↔ |x| = K ∨ |y| = K := by
  constructor
  · intro h
    have hsq : (K * (x + y)) ^ 2 = (K ^ 2 + x * y) ^ 2 := by
      have h1 : (K * |x + y|) ^ 2 = |K ^ 2 + x * y| ^ 2 :=
        congrArg (fun t : ℝ => t ^ 2) h
      calc
        (K * (x + y)) ^ 2 = K ^ 2 * (x + y) ^ 2 := by ring
        _ = K ^ 2 * |x + y| ^ 2 := by rw [sq_abs]
        _ = (K * |x + y|) ^ 2 := by ring
        _ = |K ^ 2 + x * y| ^ 2 := h1
        _ = (K ^ 2 + x * y) ^ 2 := by rw [sq_abs]
    have hdiff :
        (K ^ 2 + x * y) ^ 2 - (K * (x + y)) ^ 2 =
          (K ^ 2 - x ^ 2) * (K ^ 2 - y ^ 2) := by ring
    have hprod : (K ^ 2 - x ^ 2) * (K ^ 2 - y ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp hprod with hx0 | hy0
    · left
      have : x ^ 2 = K ^ 2 := by linarith
      have : |x| = |K| := (sq_eq_sq_iff_abs_eq_abs _ _).mp this
      simpa [abs_of_nonneg hK] using this
    · right
      have : y ^ 2 = K ^ 2 := by linarith
      have : |y| = |K| := (sq_eq_sq_iff_abs_eq_abs _ _).mp this
      simpa [abs_of_nonneg hK] using this
  · rintro (hxK | hyK)
    · have hx2 : x ^ 2 = K ^ 2 := by
        have : |x| ^ 2 = K ^ 2 := by rw [hxK]
        simpa [sq_abs] using this
      have hdiff :
          (K ^ 2 + x * y) ^ 2 - (K * (x + y)) ^ 2 =
            (K ^ 2 - x ^ 2) * (K ^ 2 - y ^ 2) := by ring
      have hsq : (K * (x + y)) ^ 2 = (K ^ 2 + x * y) ^ 2 := by
        have : (K ^ 2 - x ^ 2) * (K ^ 2 - y ^ 2) = 0 := by rw [hx2]; ring
        linarith [hdiff, this]
      have habs : |K * (x + y)| = |K ^ 2 + x * y| :=
        (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
      simpa [abs_mul, abs_of_nonneg hK] using habs
    · have hy2 : y ^ 2 = K ^ 2 := by
        have : |y| ^ 2 = K ^ 2 := by rw [hyK]
        simpa [sq_abs] using this
      have hdiff :
          (K ^ 2 + x * y) ^ 2 - (K * (x + y)) ^ 2 =
            (K ^ 2 - x ^ 2) * (K ^ 2 - y ^ 2) := by ring
      have hsq : (K * (x + y)) ^ 2 = (K ^ 2 + x * y) ^ 2 := by
        have : (K ^ 2 - x ^ 2) * (K ^ 2 - y ^ 2) = 0 := by rw [hy2]; ring
        linarith [hdiff, this]
      have habs : |K * (x + y)| = |K ^ 2 + x * y| :=
        (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
      simpa [abs_mul, abs_of_nonneg hK] using habs

private theorem three_mul_eq_zero_iff (a b c : ℝ) :
    a * b = 0 ∧ a * c = 0 ∧ b * c = 0 ↔
      (a = 0 ∧ b = 0) ∨ (a = 0 ∧ c = 0) ∨ (b = 0 ∧ c = 0) := by
  constructor
  · intro ⟨hab, hac, hbc⟩
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · left
        exact ⟨ha, hb⟩
      · right
        left
        exact ⟨ha, (mul_eq_zero.mp hbc).resolve_left hb⟩
    · have hb : b = 0 := (mul_eq_zero.mp hab).resolve_left ha
      have hc : c = 0 := (mul_eq_zero.mp hac).resolve_left ha
      right
      right
      exact ⟨hb, hc⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩)
    · simp [ha, hb]
    · simp [ha, hc]
    · simp [hb, hc]

private theorem elem_eq_iff {K t0 t1 t2 : ℝ} (hK : 0 ≤ K)
    (h0 : |t0| ≤ K) (h1 : |t1| ≤ K) (h2 : |t2| ≤ K) :
    t0 * t1 + t0 * t2 + t1 * t2 = -(K ^ 2) ↔
      (t0 = K ∧ t1 = -K) ∨ (t0 = -K ∧ t1 = K) ∨
        (t0 = K ∧ t2 = -K) ∨ (t0 = -K ∧ t2 = K) ∨
        (t1 = K ∧ t2 = -K) ∨ (t1 = -K ∧ t2 = K) := by
  constructor
  · intro he
    by_cases hsum : t0 + t1 = 0
    · have ht1 : t1 = -t0 := by linarith
      have hprod : t0 * t1 = -(K ^ 2) := by
        have : t0 * t1 + t0 * t2 + t1 * t2 = t0 * t1 + t2 * (t0 + t1) := by ring
        rw [this, hsum, mul_zero, add_zero] at he
        exact he
      rw [ht1] at hprod
      have hsq : t0 ^ 2 = K ^ 2 := by linarith
      have habs : |t0| = K := by
        have : |t0| = |K| := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
        simpa [abs_of_nonneg hK] using this
      rcases (abs_eq hK).mp habs with ht0 | ht0
      · left
        exact ⟨ht0, by simpa [ht0] using ht1⟩
      · right
        left
        exact ⟨ht0, by simpa [ht0] using ht1⟩
    · have hpair : t0 * t1 + (t0 + t1) * t2 = -(K ^ 2) := by
        have : t0 * t1 + t0 * t2 + t1 * t2 = t0 * t1 + (t0 + t1) * t2 := by ring
        linarith [he, this]
      have ht2 : t2 = -(K ^ 2 + t0 * t1) / (t0 + t1) := by
        rw [eq_div_iff hsum]
        linarith [hpair]
      have hle : |K ^ 2 + t0 * t1| ≤ K * |t0 + t1| := by
        have habs : |t2| ≤ K := h2
        rw [ht2, abs_div, abs_neg] at habs
        have habs' : |K ^ 2 + t0 * t1| / |t0 + t1| ≤ K := habs
        have hden : 0 < |t0 + t1| := abs_pos.mpr hsum
        exact (div_le_iff₀ hden).mp habs'
      have hge := pair_abs_le h0 h1 hK
      have heq : K * |t0 + t1| = |K ^ 2 + t0 * t1| := le_antisymm hge hle
      rcases (pair_abs_eq_iff hK).mp heq with h0K | h1K
      · rcases (abs_eq hK).mp h0K with ht0 | ht0
        · right; right; left
          refine ⟨ht0, ?_⟩
          have hden : K + t1 ≠ 0 := by simpa [ht0] using hsum
          have hlin : (K + t1) * t2 = -K * (K + t1) := by
            rw [ht0] at hpair
            linarith
          apply mul_left_cancel₀ hden
          linarith
        · right; right; right; left
          refine ⟨ht0, ?_⟩
          have hden : t1 + (-K) ≠ 0 := by
            have : t0 + t1 = t1 + (-K) := by rw [ht0]; ring
            exact this ▸ hsum
          have hlin : (t1 - K) * t2 = K * (t1 - K) := by
            rw [ht0] at hpair
            linarith
          have hden' : t1 - K ≠ 0 := by
            have : t1 - K = t1 + (-K) := by ring
            exact this ▸ hden
          apply mul_left_cancel₀ hden'
          linarith
      · rcases (abs_eq hK).mp h1K with ht1 | ht1
        · right; right; right; right; left
          refine ⟨ht1, ?_⟩
          have hden : t0 + K ≠ 0 := by simpa [ht1] using hsum
          have hlin : (t0 + K) * t2 = -K * (t0 + K) := by
            rw [ht1] at hpair
            linarith
          apply mul_left_cancel₀ hden
          linarith
        · right; right; right; right; right
          refine ⟨ht1, ?_⟩
          have hden : t0 + (-K) ≠ 0 := by
            have : t0 + t1 = t0 + (-K) := by rw [ht1]
            exact this ▸ hsum
          have hlin : (t0 - K) * t2 = K * (t0 - K) := by
            rw [ht1] at hpair
            linarith
          have hden' : t0 - K ≠ 0 := by
            have : t0 - K = t0 + (-K) := by ring
            exact this ▸ hden
          apply mul_left_cancel₀ hden'
          linarith
  · rintro (⟨ht0, ht1⟩ | ⟨ht0, ht1⟩ | ⟨ht0, ht2⟩ | ⟨ht0, ht2⟩ | ⟨ht1, ht2⟩ |
      ⟨ht1, ht2⟩)
    · rw [ht0, ht1]; ring
    · rw [ht0, ht1]; ring
    · rw [ht0, ht2]; ring
    · rw [ht0, ht2]; ring
    · rw [ht1, ht2]; ring
    · rw [ht1, ht2]; ring

private theorem upper_products_zero_iff {K t0 t1 t2 : ℝ}
    (h0 : t0 ≤ K) (h1 : t1 ≤ K) (h2 : t2 ≤ K) :
    (K - t0) * (K - t1) + (K - t0) * (K - t2) + (K - t1) * (K - t2) = 0 ↔
      (t0 = K ∧ t1 = K) ∨ (t0 = K ∧ t2 = K) ∨ (t1 = K ∧ t2 = K) := by
  have ha : 0 ≤ K - t0 := by linarith
  have hb : 0 ≤ K - t1 := by linarith
  have hc : 0 ≤ K - t2 := by linarith
  have hprod :
      (K - t0) * (K - t1) ≥ 0 ∧ (K - t0) * (K - t2) ≥ 0 ∧
        (K - t1) * (K - t2) ≥ 0 := by
    exact ⟨mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc⟩
  constructor
  · intro hsum
    have hz :
        (K - t0) * (K - t1) = 0 ∧ (K - t0) * (K - t2) = 0 ∧
          (K - t1) * (K - t2) = 0 := by
      have h01 : (K - t0) * (K - t1) = 0 := by linarith [hprod.1, hprod.2.1, hprod.2.2]
      have h02 : (K - t0) * (K - t2) = 0 := by linarith [hprod.1, hprod.2.1, hprod.2.2]
      have h12 : (K - t1) * (K - t2) = 0 := by linarith [hprod.1, hprod.2.1, hprod.2.2]
      exact ⟨h01, h02, h12⟩
    rcases (three_mul_eq_zero_iff (K - t0) (K - t1) (K - t2)).mp hz with
      ⟨ha0, hb0⟩ | ⟨ha0, hc0⟩ | ⟨hb0, hc0⟩
    · left
      exact ⟨by linarith, by linarith⟩
    · right
      left
      exact ⟨by linarith, by linarith⟩
    · right
      right
      exact ⟨by linarith, by linarith⟩
  · rintro (⟨ht0, ht1⟩ | ⟨ht0, ht2⟩ | ⟨ht1, ht2⟩)
    · rw [ht0, ht1]; ring
    · rw [ht0, ht2]; ring
    · rw [ht1, ht2]; ring

private theorem lower_products_zero_iff {K t0 t1 t2 : ℝ}
    (h0 : -K ≤ t0) (h1 : -K ≤ t1) (h2 : -K ≤ t2) :
    (K + t0) * (K + t1) + (K + t0) * (K + t2) + (K + t1) * (K + t2) = 0 ↔
      (t0 = -K ∧ t1 = -K) ∨ (t0 = -K ∧ t2 = -K) ∨ (t1 = -K ∧ t2 = -K) := by
  have := upper_products_zero_iff (K := K) (t0 := -t0) (t1 := -t1) (t2 := -t2)
    (by linarith) (by linarith) (by linarith)
  constructor
  · intro h
    have hsum :
        (K - -t0) * (K - -t1) + (K - -t0) * (K - -t2) + (K - -t1) * (K - -t2) =
          0 := by simpa using h
    rcases this.mp hsum with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left
      exact ⟨by linarith, by linarith⟩
    · right
      left
      exact ⟨by linarith, by linarith⟩
    · right
      right
      exact ⟨by linarith, by linarith⟩
  · rintro (⟨ht0, ht1⟩ | ⟨ht0, ht2⟩ | ⟨ht1, ht2⟩)
    · rw [ht0, ht1]; ring
    · rw [ht0, ht2]; ring
    · rw [ht1, ht2]; ring

/-! ### Equality on each leaf -/

private theorem three_mass_gap (p : TorsionParams) :
    3 * (Real.pi / 2) ^ 4 +
        (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) -
      Real.pi ^ 2 * mass p =
      ((Real.pi / 2) ^ 4 + axisSigned p 0 ^ 2 -
          2 * (Real.pi / 2) ^ 2 * axisUnsigned p 0) +
        ((Real.pi / 2) ^ 4 + axisSigned p 1 ^ 2 -
          2 * (Real.pi / 2) ^ 2 * axisUnsigned p 1) +
        ((Real.pi / 2) ^ 4 + axisSigned p 2 ^ 2 -
          2 * (Real.pi / 2) ^ 2 * axisUnsigned p 2) := by
  have hm : mass p =
      (1 / 2) * (axisUnsigned p 0 + axisUnsigned p 1 + axisUnsigned p 2) := by
    rw [mass_coef]
    simp [axisUnsigned, Fin.sum_univ_three]
  rw [hm]
  ring

private theorem onWall_iff_three_gap {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p =
        3 * (Real.pi / 2) ^ 4 +
          (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) ↔
      OnWall p := by
  have hgap := three_mass_gap p
  have hπ : 0 ≤ Real.pi / 2 := le_of_lt Real.pi_div_two_pos
  have hslack : ∀ a : Fin 3,
      0 ≤ (Real.pi / 2) ^ 4 + axisSigned p a ^ 2 -
        2 * (Real.pi / 2) ^ 2 * axisUnsigned p a := by
    intro a
    have := axis_trade_off (k := Real.pi / 2) (h a).1 (h a).2.1 (h a).2.2
    simpa [axisSigned, axisUnsigned] using this
  constructor
  · intro hid
    have hsum0 :
        ((Real.pi / 2) ^ 4 + axisSigned p 0 ^ 2 -
            2 * (Real.pi / 2) ^ 2 * axisUnsigned p 0) +
          ((Real.pi / 2) ^ 4 + axisSigned p 1 ^ 2 -
            2 * (Real.pi / 2) ^ 2 * axisUnsigned p 1) +
          ((Real.pi / 2) ^ 4 + axisSigned p 2 ^ 2 -
            2 * (Real.pi / 2) ^ 2 * axisUnsigned p 2) = 0 := by
      linarith
    have h0 : (Real.pi / 2) ^ 4 + axisSigned p 0 ^ 2 -
        2 * (Real.pi / 2) ^ 2 * axisUnsigned p 0 = 0 := by
      linarith [hslack 0, hslack 1, hslack 2]
    have h1 : (Real.pi / 2) ^ 4 + axisSigned p 1 ^ 2 -
        2 * (Real.pi / 2) ^ 2 * axisUnsigned p 1 = 0 := by
      linarith [hslack 0, hslack 1, hslack 2]
    have h2 : (Real.pi / 2) ^ 4 + axisSigned p 2 ^ 2 -
        2 * (Real.pi / 2) ^ 2 * axisUnsigned p 2 = 0 := by
      linarith [hslack 0, hslack 1, hslack 2]
    have hfin : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
    intro a
    have h0eq : 2 * (Real.pi / 2) ^ 2 * axisUnsigned p 0 =
        (Real.pi / 2) ^ 4 + axisSigned p 0 ^ 2 := by linarith
    have h1eq : 2 * (Real.pi / 2) ^ 2 * axisUnsigned p 1 =
        (Real.pi / 2) ^ 4 + axisSigned p 1 ^ 2 := by linarith
    have h2eq : 2 * (Real.pi / 2) ^ 2 * axisUnsigned p 2 =
        (Real.pi / 2) ^ 4 + axisSigned p 2 ^ 2 := by linarith
    rcases hfin a with rfl | rfl | rfl
    · exact (axis_trade_off_eq_iff (h 0).1 (h 0).2.1 (h 0).2.2 hπ).mp
        (by simpa [axisSigned, axisUnsigned] using h0eq)
    · exact (axis_trade_off_eq_iff (h 1).1 (h 1).2.1 (h 1).2.2 hπ).mp
        (by simpa [axisSigned, axisUnsigned] using h1eq)
    · exact (axis_trade_off_eq_iff (h 2).1 (h 2).2.1 (h 2).2.2 hπ).mp
        (by simpa [axisSigned, axisUnsigned] using h2eq)
  · intro hw
    have heq : ∀ a : Fin 3,
        2 * (Real.pi / 2) ^ 2 * axisUnsigned p a =
          (Real.pi / 2) ^ 4 + axisSigned p a ^ 2 := by
      intro a
      have :=
        (axis_trade_off_eq_iff (h a).1 (h a).2.1 (h a).2.2 hπ).mpr (hw a)
      simpa [axisSigned, axisUnsigned] using this
    linarith [heq 0, heq 1, heq 2, hgap]

private theorem shield_gap_identity (t0 t1 t2 : ℝ) :
    5 * (Real.pi / 2) ^ 4 + (t0 + t1 + t2) ^ 2 -
        (3 * (Real.pi / 2) ^ 4 + (t0 ^ 2 + t1 ^ 2 + t2 ^ 2)) =
      2 * (t0 * t1 + t0 * t2 + t1 * t2 + ((Real.pi / 2) ^ 2) ^ 2) := by
  ring

private theorem attractive_gap_identity (t0 t1 t2 : ℝ) :
    5 * (Real.pi / 2) ^ 4 +
        (t0 + t1 + t2 - 2 * (Real.pi / 2) ^ 2) ^ 2 -
        (3 * (Real.pi / 2) ^ 4 + (t0 ^ 2 + t1 ^ 2 + t2 ^ 2)) =
      2 * (((Real.pi / 2) ^ 2 - t0) * ((Real.pi / 2) ^ 2 - t1) +
            ((Real.pi / 2) ^ 2 - t0) * ((Real.pi / 2) ^ 2 - t2) +
            ((Real.pi / 2) ^ 2 - t1) * ((Real.pi / 2) ^ 2 - t2)) := by
  ring

private theorem repulsive_gap_identity (t0 t1 t2 : ℝ) :
    5 * (Real.pi / 2) ^ 4 +
        (t0 + t1 + t2 + 2 * (Real.pi / 2) ^ 2) ^ 2 -
        (3 * (Real.pi / 2) ^ 4 + (t0 ^ 2 + t1 ^ 2 + t2 ^ 2)) =
      2 * (((Real.pi / 2) ^ 2 + t0) * ((Real.pi / 2) ^ 2 + t1) +
            ((Real.pi / 2) ^ 2 + t0) * ((Real.pi / 2) ^ 2 + t2) +
            ((Real.pi / 2) ^ 2 + t1) * ((Real.pi / 2) ^ 2 + t2)) := by
  ring

private theorem twoPureUsual_iff_densities {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    TwoPureUsual p ↔
      (axisSigned p 0 = (Real.pi / 2) ^ 2 ∧
          axisSigned p 1 = (Real.pi / 2) ^ 2) ∨
        (axisSigned p 0 = (Real.pi / 2) ^ 2 ∧
          axisSigned p 2 = (Real.pi / 2) ^ 2) ∨
        (axisSigned p 1 = (Real.pi / 2) ^ 2 ∧
          axisSigned p 2 = (Real.pi / 2) ^ 2) := by
  constructor
  · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩)
    · left
      exact ⟨(isPureUsual_iff_axisSigned h 0).mp h0,
        (isPureUsual_iff_axisSigned h 1).mp h1⟩
    · right
      left
      exact ⟨(isPureUsual_iff_axisSigned h 0).mp h0,
        (isPureUsual_iff_axisSigned h 2).mp h2⟩
    · right
      right
      exact ⟨(isPureUsual_iff_axisSigned h 1).mp h1,
        (isPureUsual_iff_axisSigned h 2).mp h2⟩
  · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩)
    · left
      exact ⟨(isPureUsual_iff_axisSigned h 0).mpr h0,
        (isPureUsual_iff_axisSigned h 1).mpr h1⟩
    · right
      left
      exact ⟨(isPureUsual_iff_axisSigned h 0).mpr h0,
        (isPureUsual_iff_axisSigned h 2).mpr h2⟩
    · right
      right
      exact ⟨(isPureUsual_iff_axisSigned h 1).mpr h1,
        (isPureUsual_iff_axisSigned h 2).mpr h2⟩

private theorem twoPureDual_iff_densities {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    TwoPureDual p ↔
      (axisSigned p 0 = -((Real.pi / 2) ^ 2) ∧
          axisSigned p 1 = -((Real.pi / 2) ^ 2)) ∨
        (axisSigned p 0 = -((Real.pi / 2) ^ 2) ∧
          axisSigned p 2 = -((Real.pi / 2) ^ 2)) ∨
        (axisSigned p 1 = -((Real.pi / 2) ^ 2) ∧
          axisSigned p 2 = -((Real.pi / 2) ^ 2)) := by
  constructor
  · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩)
    · left
      exact ⟨(isPureDual_iff_axisSigned h 0).mp h0,
        (isPureDual_iff_axisSigned h 1).mp h1⟩
    · right
      left
      exact ⟨(isPureDual_iff_axisSigned h 0).mp h0,
        (isPureDual_iff_axisSigned h 2).mp h2⟩
    · right
      right
      exact ⟨(isPureDual_iff_axisSigned h 1).mp h1,
        (isPureDual_iff_axisSigned h 2).mp h2⟩
  · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩)
    · left
      exact ⟨(isPureDual_iff_axisSigned h 0).mpr h0,
        (isPureDual_iff_axisSigned h 1).mpr h1⟩
    · right
      left
      exact ⟨(isPureDual_iff_axisSigned h 0).mpr h0,
        (isPureDual_iff_axisSigned h 2).mpr h2⟩
    · right
      right
      exact ⟨(isPureDual_iff_axisSigned h 1).mpr h1,
        (isPureDual_iff_axisSigned h 2).mpr h2⟩

private theorem opposed_iff_densities {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    OpposedCorners p ↔
      (axisSigned p 0 = (Real.pi / 2) ^ 2 ∧
          axisSigned p 1 = -((Real.pi / 2) ^ 2)) ∨
        (axisSigned p 0 = -((Real.pi / 2) ^ 2) ∧
          axisSigned p 1 = (Real.pi / 2) ^ 2) ∨
        (axisSigned p 0 = (Real.pi / 2) ^ 2 ∧
          axisSigned p 2 = -((Real.pi / 2) ^ 2)) ∨
        (axisSigned p 0 = -((Real.pi / 2) ^ 2) ∧
          axisSigned p 2 = (Real.pi / 2) ^ 2) ∨
        (axisSigned p 1 = (Real.pi / 2) ^ 2 ∧
          axisSigned p 2 = -((Real.pi / 2) ^ 2)) ∨
        (axisSigned p 1 = -((Real.pi / 2) ^ 2) ∧
          axisSigned p 2 = (Real.pi / 2) ^ 2) := by
  constructor
  · rintro (⟨hu, hd⟩ | ⟨hd, hu⟩ | ⟨hu, hd⟩ | ⟨hd, hu⟩ | ⟨hu, hd⟩ | ⟨hd, hu⟩)
    · left
      exact ⟨(isPureUsual_iff_axisSigned h 0).mp hu,
        (isPureDual_iff_axisSigned h 1).mp hd⟩
    · right; left
      exact ⟨(isPureDual_iff_axisSigned h 0).mp hd,
        (isPureUsual_iff_axisSigned h 1).mp hu⟩
    · right; right; left
      exact ⟨(isPureUsual_iff_axisSigned h 0).mp hu,
        (isPureDual_iff_axisSigned h 2).mp hd⟩
    · right; right; right; left
      exact ⟨(isPureDual_iff_axisSigned h 0).mp hd,
        (isPureUsual_iff_axisSigned h 2).mp hu⟩
    · right; right; right; right; left
      exact ⟨(isPureUsual_iff_axisSigned h 1).mp hu,
        (isPureDual_iff_axisSigned h 2).mp hd⟩
    · right; right; right; right; right
      exact ⟨(isPureDual_iff_axisSigned h 1).mp hd,
        (isPureUsual_iff_axisSigned h 2).mp hu⟩
  · rintro (⟨hu, hd⟩ | ⟨hd, hu⟩ | ⟨hu, hd⟩ | ⟨hd, hu⟩ | ⟨hu, hd⟩ | ⟨hd, hu⟩)
    · left
      exact ⟨(isPureUsual_iff_axisSigned h 0).mpr hu,
        (isPureDual_iff_axisSigned h 1).mpr hd⟩
    · right; left
      exact ⟨(isPureDual_iff_axisSigned h 0).mpr hd,
        (isPureUsual_iff_axisSigned h 1).mpr hu⟩
    · right; right; left
      exact ⟨(isPureUsual_iff_axisSigned h 0).mpr hu,
        (isPureDual_iff_axisSigned h 2).mpr hd⟩
    · right; right; right; left
      exact ⟨(isPureDual_iff_axisSigned h 0).mpr hd,
        (isPureUsual_iff_axisSigned h 2).mpr hu⟩
    · right; right; right; right; left
      exact ⟨(isPureUsual_iff_axisSigned h 1).mpr hu,
        (isPureDual_iff_axisSigned h 2).mpr hd⟩
    · right; right; right; right; right
      exact ⟨(isPureDual_iff_axisSigned h 1).mpr hd,
        (isPureUsual_iff_axisSigned h 2).mpr hu⟩

private theorem elem_ge {K t0 t1 t2 : ℝ}
    (h0 : |t0| ≤ K) (h1 : |t1| ≤ K) (h2 : |t2| ≤ K) :
    -(K ^ 2) ≤ t0 * t1 + t0 * t2 + t1 * t2 := by
  obtain ⟨_, h0u⟩ := abs_le.mp h0
  obtain ⟨_, h1u⟩ := abs_le.mp h1
  obtain ⟨h2l, _⟩ := abs_le.mp h2
  rcases le_total 0 (t0 + t1) with hsum | hsum
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K - t0)
      (by linarith : (0 : ℝ) ≤ K - t1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ t2 + K) hsum]
  · obtain ⟨h0l, _⟩ := abs_le.mp h0
    obtain ⟨h1l, _⟩ := abs_le.mp h1
    obtain ⟨_, h2u⟩ := abs_le.mp h2
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K + t0)
      (by linarith : (0 : ℝ) ≤ K + t1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ K - t2)
        (by linarith : (0 : ℝ) ≤ -(t0 + t1))]

private theorem three_slack_nonneg {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    0 ≤ 3 * (Real.pi / 2) ^ 4 +
      (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) -
      Real.pi ^ 2 * mass p := by
  have hgap := three_mass_gap p
  have hslack : ∀ a : Fin 3,
      0 ≤ (Real.pi / 2) ^ 4 + axisSigned p a ^ 2 -
        2 * (Real.pi / 2) ^ 2 * axisUnsigned p a := by
    intro a
    have := axis_trade_off (k := Real.pi / 2) (h a).1 (h a).2.1 (h a).2.2
    simpa [axisSigned, axisUnsigned] using this
  linarith [hslack 0, hslack 1, hslack 2, hgap]

private theorem pi_sq_mass_eq_shield_iff {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p = 5 * Real.pi ^ 4 / 16 + 4 * J p ^ 2 ↔
      OnWall p ∧ OpposedCorners p := by
  have hT := signedSum3 p
  have hsq : (axisSigned p 0 + axisSigned p 1 + axisSigned p 2) ^ 2 =
      (2 * J p) ^ 2 := by rw [hT]
  have hthree := onWall_iff_three_gap h
  have hK : 0 ≤ (Real.pi / 2) ^ 2 := by positivity
  have habs0 : |axisSigned p 0| ≤ (Real.pi / 2) ^ 2 :=
    axis_abs_density_le (h 0).1 (h 0).2.1 (h 0).2.2
  have habs1 : |axisSigned p 1| ≤ (Real.pi / 2) ^ 2 :=
    axis_abs_density_le (h 1).1 (h 1).2.1 (h 1).2.2
  have habs2 : |axisSigned p 2| ≤ (Real.pi / 2) ^ 2 :=
    axis_abs_density_le (h 2).1 (h 2).2.1 (h 2).2.2
  have hBA := shield_gap_identity (axisSigned p 0) (axisSigned p 1) (axisSigned p 2)
  have hBA' := hBA
  rw [hsq] at hBA'
  have hC : 5 * (Real.pi / 2) ^ 4 + (2 * J p) ^ 2 =
      5 * Real.pi ^ 4 / 16 + 4 * J p ^ 2 := by ring
  have hS := three_slack_nonneg h
  have hE : 0 ≤
      axisSigned p 0 * axisSigned p 1 + axisSigned p 0 * axisSigned p 2 +
        axisSigned p 1 * axisSigned p 2 + ((Real.pi / 2) ^ 2) ^ 2 := by
    linarith [elem_ge habs0 habs1 habs2]
  constructor
  · intro hid
    have hsplit :
        5 * Real.pi ^ 4 / 16 + 4 * J p ^ 2 - Real.pi ^ 2 * mass p =
          (3 * (Real.pi / 2) ^ 4 +
              (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) -
            Real.pi ^ 2 * mass p) +
            2 * (axisSigned p 0 * axisSigned p 1 + axisSigned p 0 * axisSigned p 2 +
              axisSigned p 1 * axisSigned p 2 + ((Real.pi / 2) ^ 2) ^ 2) := by
      linarith [hBA', hC]
    have hzero : 5 * Real.pi ^ 4 / 16 + 4 * J p ^ 2 - Real.pi ^ 2 * mass p = 0 := by
      linarith [hid]
    have hS0 : 3 * (Real.pi / 2) ^ 4 +
        (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) -
        Real.pi ^ 2 * mass p = 0 := by
      linarith [hsplit, hzero, hS, hE]
    have he2 :
        axisSigned p 0 * axisSigned p 1 + axisSigned p 0 * axisSigned p 2 +
            axisSigned p 1 * axisSigned p 2 =
          -(((Real.pi / 2) ^ 2) ^ 2) := by
      linarith [hsplit, hzero, hS, hE]
    exact ⟨hthree.mp (by linarith [hS0]),
      (opposed_iff_densities h).mpr ((elem_eq_iff hK habs0 habs1 habs2).mp he2)⟩
  · rintro ⟨hw, hopp⟩
    have hthreeEq := hthree.mpr hw
    have he2 :
        axisSigned p 0 * axisSigned p 1 + axisSigned p 0 * axisSigned p 2 +
            axisSigned p 1 * axisSigned p 2 =
          -(((Real.pi / 2) ^ 2) ^ 2) :=
      (elem_eq_iff hK habs0 habs1 habs2).mpr ((opposed_iff_densities h).mp hopp)
    linarith [hthreeEq, he2, hBA', hC]

private theorem pi_sq_mass_eq_attractive_iff {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p =
        5 * Real.pi ^ 4 / 16 + (2 * J p - Real.pi ^ 2 / 2) ^ 2 ↔
      OnWall p ∧ TwoPureUsual p := by
  have hT := signedSum3 p
  have hsq :
      (axisSigned p 0 + axisSigned p 1 + axisSigned p 2 -
          2 * (Real.pi / 2) ^ 2) ^ 2 =
        (2 * J p - 2 * (Real.pi / 2) ^ 2) ^ 2 := by rw [hT]
  have hthree := onWall_iff_three_gap h
  have hBA := attractive_gap_identity (axisSigned p 0) (axisSigned p 1)
    (axisSigned p 2)
  have hBA' := hBA
  rw [hsq] at hBA'
  have hC : 5 * (Real.pi / 2) ^ 4 + (2 * J p - 2 * (Real.pi / 2) ^ 2) ^ 2 =
      5 * Real.pi ^ 4 / 16 + (2 * J p - Real.pi ^ 2 / 2) ^ 2 := by ring
  have hS := three_slack_nonneg h
  have hP : 0 ≤
      ((Real.pi / 2) ^ 2 - axisSigned p 0) * ((Real.pi / 2) ^ 2 - axisSigned p 1) +
        ((Real.pi / 2) ^ 2 - axisSigned p 0) * ((Real.pi / 2) ^ 2 - axisSigned p 2) +
        ((Real.pi / 2) ^ 2 - axisSigned p 1) * ((Real.pi / 2) ^ 2 - axisSigned p 2) := by
    have ha : 0 ≤ (Real.pi / 2) ^ 2 - axisSigned p 0 := by
      linarith [axisSigned_le_K h 0]
    have hb : 0 ≤ (Real.pi / 2) ^ 2 - axisSigned p 1 := by
      linarith [axisSigned_le_K h 1]
    have hc : 0 ≤ (Real.pi / 2) ^ 2 - axisSigned p 2 := by
      linarith [axisSigned_le_K h 2]
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
  constructor
  · intro hid
    have hsplit :
        5 * Real.pi ^ 4 / 16 + (2 * J p - Real.pi ^ 2 / 2) ^ 2 -
            Real.pi ^ 2 * mass p =
          (3 * (Real.pi / 2) ^ 4 +
              (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) -
            Real.pi ^ 2 * mass p) +
            2 * (((Real.pi / 2) ^ 2 - axisSigned p 0) *
                ((Real.pi / 2) ^ 2 - axisSigned p 1) +
              ((Real.pi / 2) ^ 2 - axisSigned p 0) *
                ((Real.pi / 2) ^ 2 - axisSigned p 2) +
              ((Real.pi / 2) ^ 2 - axisSigned p 1) *
                ((Real.pi / 2) ^ 2 - axisSigned p 2)) := by
      linarith [hBA', hC]
    have hzero :
        5 * Real.pi ^ 4 / 16 + (2 * J p - Real.pi ^ 2 / 2) ^ 2 -
          Real.pi ^ 2 * mass p = 0 := by linarith [hid]
    have hS0 : 3 * (Real.pi / 2) ^ 4 +
        (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) -
        Real.pi ^ 2 * mass p = 0 := by linarith [hsplit, hzero, hS, hP]
    have hprod :
        ((Real.pi / 2) ^ 2 - axisSigned p 0) * ((Real.pi / 2) ^ 2 - axisSigned p 1) +
          ((Real.pi / 2) ^ 2 - axisSigned p 0) * ((Real.pi / 2) ^ 2 - axisSigned p 2) +
          ((Real.pi / 2) ^ 2 - axisSigned p 1) * ((Real.pi / 2) ^ 2 - axisSigned p 2) =
          0 := by linarith [hsplit, hzero, hS, hP]
    exact ⟨hthree.mp (by linarith [hS0]),
      (twoPureUsual_iff_densities h).mpr
        ((upper_products_zero_iff (axisSigned_le_K h 0) (axisSigned_le_K h 1)
          (axisSigned_le_K h 2)).mp hprod)⟩
  · rintro ⟨hw, hUU⟩
    have hthreeEq := hthree.mpr hw
    have hprod :
        ((Real.pi / 2) ^ 2 - axisSigned p 0) * ((Real.pi / 2) ^ 2 - axisSigned p 1) +
          ((Real.pi / 2) ^ 2 - axisSigned p 0) * ((Real.pi / 2) ^ 2 - axisSigned p 2) +
          ((Real.pi / 2) ^ 2 - axisSigned p 1) * ((Real.pi / 2) ^ 2 - axisSigned p 2) =
          0 :=
      (upper_products_zero_iff (axisSigned_le_K h 0) (axisSigned_le_K h 1)
        (axisSigned_le_K h 2)).mpr ((twoPureUsual_iff_densities h).mp hUU)
    linarith [hthreeEq, hprod, hBA', hC]

private theorem pi_sq_mass_eq_repulsive_iff {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p =
        5 * Real.pi ^ 4 / 16 + (2 * J p + Real.pi ^ 2 / 2) ^ 2 ↔
      OnWall p ∧ TwoPureDual p := by
  have hT := signedSum3 p
  have hsq :
      (axisSigned p 0 + axisSigned p 1 + axisSigned p 2 +
          2 * (Real.pi / 2) ^ 2) ^ 2 =
        (2 * J p + 2 * (Real.pi / 2) ^ 2) ^ 2 := by rw [hT]
  have hthree := onWall_iff_three_gap h
  have hBA := repulsive_gap_identity (axisSigned p 0) (axisSigned p 1)
    (axisSigned p 2)
  have hBA' := hBA
  rw [hsq] at hBA'
  have hC : 5 * (Real.pi / 2) ^ 4 + (2 * J p + 2 * (Real.pi / 2) ^ 2) ^ 2 =
      5 * Real.pi ^ 4 / 16 + (2 * J p + Real.pi ^ 2 / 2) ^ 2 := by ring
  have hS := three_slack_nonneg h
  have hP : 0 ≤
      ((Real.pi / 2) ^ 2 + axisSigned p 0) * ((Real.pi / 2) ^ 2 + axisSigned p 1) +
        ((Real.pi / 2) ^ 2 + axisSigned p 0) * ((Real.pi / 2) ^ 2 + axisSigned p 2) +
        ((Real.pi / 2) ^ 2 + axisSigned p 1) * ((Real.pi / 2) ^ 2 + axisSigned p 2) := by
    have ha : 0 ≤ (Real.pi / 2) ^ 2 + axisSigned p 0 := by
      linarith [axisSigned_ge_negK h 0]
    have hb : 0 ≤ (Real.pi / 2) ^ 2 + axisSigned p 1 := by
      linarith [axisSigned_ge_negK h 1]
    have hc : 0 ≤ (Real.pi / 2) ^ 2 + axisSigned p 2 := by
      linarith [axisSigned_ge_negK h 2]
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
  constructor
  · intro hid
    have hsplit :
        5 * Real.pi ^ 4 / 16 + (2 * J p + Real.pi ^ 2 / 2) ^ 2 -
            Real.pi ^ 2 * mass p =
          (3 * (Real.pi / 2) ^ 4 +
              (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) -
            Real.pi ^ 2 * mass p) +
            2 * (((Real.pi / 2) ^ 2 + axisSigned p 0) *
                ((Real.pi / 2) ^ 2 + axisSigned p 1) +
              ((Real.pi / 2) ^ 2 + axisSigned p 0) *
                ((Real.pi / 2) ^ 2 + axisSigned p 2) +
              ((Real.pi / 2) ^ 2 + axisSigned p 1) *
                ((Real.pi / 2) ^ 2 + axisSigned p 2)) := by
      linarith [hBA', hC]
    have hzero :
        5 * Real.pi ^ 4 / 16 + (2 * J p + Real.pi ^ 2 / 2) ^ 2 -
          Real.pi ^ 2 * mass p = 0 := by linarith [hid]
    have hS0 : 3 * (Real.pi / 2) ^ 4 +
        (axisSigned p 0 ^ 2 + axisSigned p 1 ^ 2 + axisSigned p 2 ^ 2) -
        Real.pi ^ 2 * mass p = 0 := by linarith [hsplit, hzero, hS, hP]
    have hprod :
        ((Real.pi / 2) ^ 2 + axisSigned p 0) * ((Real.pi / 2) ^ 2 + axisSigned p 1) +
          ((Real.pi / 2) ^ 2 + axisSigned p 0) * ((Real.pi / 2) ^ 2 + axisSigned p 2) +
          ((Real.pi / 2) ^ 2 + axisSigned p 1) * ((Real.pi / 2) ^ 2 + axisSigned p 2) =
          0 := by linarith [hsplit, hzero, hS, hP]
    exact ⟨hthree.mp (by linarith [hS0]),
      (twoPureDual_iff_densities h).mpr
        ((lower_products_zero_iff (axisSigned_ge_negK h 0) (axisSigned_ge_negK h 1)
          (axisSigned_ge_negK h 2)).mp hprod)⟩
  · rintro ⟨hw, hDD⟩
    have hthreeEq := hthree.mpr hw
    have hprod :
        ((Real.pi / 2) ^ 2 + axisSigned p 0) * ((Real.pi / 2) ^ 2 + axisSigned p 1) +
          ((Real.pi / 2) ^ 2 + axisSigned p 0) * ((Real.pi / 2) ^ 2 + axisSigned p 2) +
          ((Real.pi / 2) ^ 2 + axisSigned p 1) * ((Real.pi / 2) ^ 2 + axisSigned p 2) =
          0 :=
      (lower_products_zero_iff (axisSigned_ge_negK h 0) (axisSigned_ge_negK h 1)
        (axisSigned_ge_negK h 2)).mpr ((twoPureDual_iff_densities h).mp hDD)
    linarith [hthreeEq, hprod, hBA', hC]

/-! ### Which leaf is the envelope -/

private theorem controlEnvelopeNum_eq_shield {Jval : ℝ}
    (h : |Jval| ≤ Real.pi ^ 2 / 8) :
    controlEnvelopeNum Jval = 4 * Jval ^ 2 := by
  have hJ := abs_le.mp h
  have hnonpos : 2 * Jval - Real.pi ^ 2 / 2 ≤ 0 := by linarith
  have hA : 4 * Jval ^ 2 ≤ (2 * Jval - Real.pi ^ 2 / 2) ^ 2 := by
    rw [show 4 * Jval ^ 2 = (2 * Jval) ^ 2 by ring]
    apply sq_le_sq.mpr
    rw [abs_of_nonpos hnonpos, abs_le]
    constructor <;> linarith [show (0 : ℝ) < Real.pi ^ 2 by positivity]
  have hpos : 0 ≤ 2 * Jval + Real.pi ^ 2 / 2 := by
    have : 0 ≤ Real.pi ^ 2 / 2 := by positivity
    linarith
  have hB : 4 * Jval ^ 2 ≤ (2 * Jval + Real.pi ^ 2 / 2) ^ 2 := by
    rw [show 4 * Jval ^ 2 = (2 * Jval) ^ 2 by ring]
    apply sq_le_sq.mpr
    rw [abs_of_nonneg hpos, abs_le]
    constructor <;> linarith [show (0 : ℝ) < Real.pi ^ 2 by positivity]
  unfold controlEnvelopeNum
  rw [min_eq_left (le_min hA hB)]

private theorem controlEnvelopeNum_eq_attractive {Jval : ℝ}
    (h : Real.pi ^ 2 / 8 ≤ Jval) :
    controlEnvelopeNum Jval = (2 * Jval - Real.pi ^ 2 / 2) ^ 2 := by
  have hJ : 0 ≤ Jval := by
    have : (0 : ℝ) < Real.pi ^ 2 / 8 := by positivity
    linarith
  have h4 : (2 * Jval - Real.pi ^ 2 / 2) ^ 2 ≤ 4 * Jval ^ 2 := by
    rw [show 4 * Jval ^ 2 = (2 * Jval) ^ 2 by ring]
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * Jval), abs_le]
    constructor <;> linarith [show (0 : ℝ) < Real.pi ^ 2 by positivity]
  have hpos : 0 ≤ 2 * Jval + Real.pi ^ 2 / 2 := by
    have : 0 ≤ Real.pi ^ 2 / 2 := by positivity
    linarith
  have hR : (2 * Jval - Real.pi ^ 2 / 2) ^ 2 ≤
      (2 * Jval + Real.pi ^ 2 / 2) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg hpos, abs_le]
    constructor <;> linarith [show (0 : ℝ) < Real.pi ^ 2 by positivity]
  unfold controlEnvelopeNum
  rw [min_eq_left hR, min_eq_right h4]

private theorem controlEnvelopeNum_eq_repulsive {Jval : ℝ}
    (h : Jval ≤ -(Real.pi ^ 2 / 8)) :
    controlEnvelopeNum Jval = (2 * Jval + Real.pi ^ 2 / 2) ^ 2 := by
  have hpos : Real.pi ^ 2 / 8 ≤ -Jval := by linarith
  have hneg := controlEnvelopeNum_eq_attractive hpos
  rw [← controlEnvelopeNum_neg Jval]
  have hsq :
      (2 * (-Jval) - Real.pi ^ 2 / 2) ^ 2 =
        (2 * Jval + Real.pi ^ 2 / 2) ^ 2 := by ring
  rw [hneg, hsq]

private theorem mass_eq_controlCeiling_iff_raw {p : TorsionParams} :
    mass p = controlCeiling (J p) ↔
      Real.pi ^ 2 * mass p =
        5 * Real.pi ^ 4 / 16 + controlEnvelopeNum (J p) := by
  have hπ : Real.pi ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    unfold controlCeiling at h
    have := congrArg (fun x : ℝ => Real.pi ^ 2 * x) h
    have hid :
        Real.pi ^ 2 *
            (5 * Real.pi ^ 2 / 16 + controlEnvelopeNum (J p) / Real.pi ^ 2) =
          5 * Real.pi ^ 4 / 16 + controlEnvelopeNum (J p) := by
      field_simp
    linarith
  · intro h
    unfold controlCeiling
    have hid :
        Real.pi ^ 2 *
            (5 * Real.pi ^ 2 / 16 + controlEnvelopeNum (J p) / Real.pi ^ 2) =
          5 * Real.pi ^ 4 / 16 + controlEnvelopeNum (J p) := by
      field_simp
    apply mul_left_cancel₀ hπ
    linarith

private theorem envelopeNum_trichotomy (Jval : ℝ) :
    controlEnvelopeNum Jval = 4 * Jval ^ 2 ∨
      controlEnvelopeNum Jval = (2 * Jval - Real.pi ^ 2 / 2) ^ 2 ∨
      controlEnvelopeNum Jval = (2 * Jval + Real.pi ^ 2 / 2) ^ 2 := by
  unfold controlEnvelopeNum
  rcases le_or_gt (4 * Jval ^ 2)
      (min ((2 * Jval - Real.pi ^ 2 / 2) ^ 2)
        ((2 * Jval + Real.pi ^ 2 / 2) ^ 2)) with hle | hgt
  · left
    exact min_eq_left hle
  · right
    have hmin :
        min ((2 * Jval - Real.pi ^ 2 / 2) ^ 2)
            ((2 * Jval + Real.pi ^ 2 / 2) ^ 2) <
          4 * Jval ^ 2 := hgt
    rcases le_total ((2 * Jval - Real.pi ^ 2 / 2) ^ 2)
        ((2 * Jval + Real.pi ^ 2 / 2) ^ 2) with hab | hba
    · left
      rw [min_eq_left hab, min_eq_right (le_of_lt (by simpa [min_eq_left hab] using hmin))]
    · right
      rw [min_eq_right hba, min_eq_right (le_of_lt (by simpa [min_eq_right hba] using hmin))]

private theorem corners_of_twoPatterns {p : TorsionParams}
    (h : TwoPureUsual p ∨ TwoPureDual p ∨ OpposedCorners p) :
    TwoCorners p := by
  rcases h with hUU | hDD | hopp
  · rcases hUU with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨Or.inl h0, Or.inl h1⟩
    · right
      left
      exact ⟨Or.inl h0, Or.inl h2⟩
    · right
      right
      exact ⟨Or.inl h1, Or.inl h2⟩
  · rcases hDD with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨Or.inr h0, Or.inr h1⟩
    · right
      left
      exact ⟨Or.inr h0, Or.inr h2⟩
    · right
      right
      exact ⟨Or.inr h1, Or.inr h2⟩
  · rcases hopp with ⟨hu, hd⟩ | ⟨hd, hu⟩ | ⟨hu, hd⟩ | ⟨hd, hu⟩ | ⟨hu, hd⟩ | ⟨hd, hu⟩
    · left
      exact ⟨Or.inl hu, Or.inr hd⟩
    · left
      exact ⟨Or.inr hd, Or.inl hu⟩
    · right
      left
      exact ⟨Or.inl hu, Or.inr hd⟩
    · right
      left
      exact ⟨Or.inr hd, Or.inl hu⟩
    · right
      right
      exact ⟨Or.inl hu, Or.inr hd⟩
    · right
      right
      exact ⟨Or.inr hd, Or.inl hu⟩

private theorem opposed_of_twoCorners_not_same {p : TorsionParams}
    (hT : TwoCorners p) (hU : ¬ TwoPureUsual p) (hD : ¬ TwoPureDual p) :
    OpposedCorners p := by
  rcases hT with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
  · rcases h0 with hu0 | hd0 <;> rcases h1 with hu1 | hd1
    · exact (hU (Or.inl ⟨hu0, hu1⟩)).elim
    · exact Or.inl ⟨hu0, hd1⟩
    · exact Or.inr (Or.inl ⟨hd0, hu1⟩)
    · exact (hD (Or.inl ⟨hd0, hd1⟩)).elim
  · rcases h0 with hu0 | hd0 <;> rcases h2 with hu2 | hd2
    · exact (hU (Or.inr (Or.inl ⟨hu0, hu2⟩))).elim
    · exact Or.inr (Or.inr (Or.inl ⟨hu0, hd2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd0, hu2⟩)))
    · exact (hD (Or.inr (Or.inl ⟨hd0, hd2⟩))).elim
  · rcases h1 with hu1 | hd1 <;> rcases h2 with hu2 | hd2
    · exact (hU (Or.inr (Or.inr ⟨hu1, hu2⟩))).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu1, hd2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hd1, hu2⟩))))
    · exact (hD (Or.inr (Or.inr ⟨hd1, hd2⟩))).elim

private theorem abs_J_le_of_free_density {Jval t : ℝ}
    (hJ : 2 * Jval = t)
    (hlo : -((Real.pi / 2) ^ 2) ≤ t)
    (hhi : t ≤ (Real.pi / 2) ^ 2) :
    |Jval| ≤ Real.pi ^ 2 / 8 := by
  have hK : (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 := by ring
  have habs : |2 * Jval| ≤ (Real.pi / 2) ^ 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_le] at habs ⊢
  constructor <;> nlinarith [hK]

private theorem abs_J_le_of_opposed {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hopp : OpposedCorners p) :
    |J p| ≤ Real.pi ^ 2 / 8 := by
  have hT := signedSum3 p
  have hopp' := (opposed_iff_densities h).mp hopp
  rcases hopp' with ⟨ht0, ht1⟩ | ⟨ht0, ht1⟩ | ⟨ht0, ht2⟩ | ⟨ht0, ht2⟩ |
      ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
  · exact abs_J_le_of_free_density (by linarith [hT, ht0, ht1])
      (axisSigned_ge_negK h 2) (axisSigned_le_K h 2)
  · exact abs_J_le_of_free_density (by linarith [hT, ht0, ht1])
      (axisSigned_ge_negK h 2) (axisSigned_le_K h 2)
  · exact abs_J_le_of_free_density (by linarith [hT, ht0, ht2])
      (axisSigned_ge_negK h 1) (axisSigned_le_K h 1)
  · exact abs_J_le_of_free_density (by linarith [hT, ht0, ht2])
      (axisSigned_ge_negK h 1) (axisSigned_le_K h 1)
  · exact abs_J_le_of_free_density (by linarith [hT, ht1, ht2])
      (axisSigned_ge_negK h 0) (axisSigned_le_K h 0)
  · exact abs_J_le_of_free_density (by linarith [hT, ht1, ht2])
      (axisSigned_ge_negK h 0) (axisSigned_le_K h 0)

/-! ### The lock -/

/-- An admissible configuration meets the envelope if and only if every
axis is on the wall and at least two axes are corners. -/
theorem onEnvelope_iff {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    mass p = controlCeiling (J p) ↔ OnWall p ∧ TwoCorners p := by
  constructor
  · intro hmass
    have hraw := (mass_eq_controlCeiling_iff_raw (p := p)).mp hmass
    rcases envelopeNum_trichotomy (J p) with hS | hA | hR
    · have hshield :
          Real.pi ^ 2 * mass p = 5 * Real.pi ^ 4 / 16 + 4 * J p ^ 2 := by
        rw [hraw, hS]
      have ⟨hw, hopp⟩ := (pi_sq_mass_eq_shield_iff h).mp hshield
      exact ⟨hw, corners_of_twoPatterns (Or.inr (Or.inr hopp))⟩
    · have hattr :
          Real.pi ^ 2 * mass p =
            5 * Real.pi ^ 4 / 16 + (2 * J p - Real.pi ^ 2 / 2) ^ 2 := by
        rw [hraw, hA]
      have ⟨hw, hUU⟩ := (pi_sq_mass_eq_attractive_iff h).mp hattr
      exact ⟨hw, corners_of_twoPatterns (Or.inl hUU)⟩
    · have hrep :
          Real.pi ^ 2 * mass p =
            5 * Real.pi ^ 4 / 16 + (2 * J p + Real.pi ^ 2 / 2) ^ 2 := by
        rw [hraw, hR]
      have ⟨hw, hDD⟩ := (pi_sq_mass_eq_repulsive_iff h).mp hrep
      exact ⟨hw, corners_of_twoPatterns (Or.inr (Or.inl hDD))⟩
  · rintro ⟨hw, hcorn⟩
    by_cases hUU : TwoPureUsual p
    · have hJ := le_J_of_twoPureUsual h hUU
      have heq := (pi_sq_mass_eq_attractive_iff h).mpr ⟨hw, hUU⟩
      have hnum := controlEnvelopeNum_eq_attractive hJ
      exact (mass_eq_controlCeiling_iff_raw (p := p)).mpr (by rw [heq, hnum])
    · by_cases hDD : TwoPureDual p
      · have hJ := J_le_of_twoPureDual h hDD
        have heq := (pi_sq_mass_eq_repulsive_iff h).mpr ⟨hw, hDD⟩
        have hnum := controlEnvelopeNum_eq_repulsive hJ
        exact (mass_eq_controlCeiling_iff_raw (p := p)).mpr (by rw [heq, hnum])
      · have hopp := opposed_of_twoCorners_not_same hcorn hUU hDD
        have hJ := abs_J_le_of_opposed h hopp
        have heq := (pi_sq_mass_eq_shield_iff h).mpr ⟨hw, hopp⟩
        have hnum := controlEnvelopeNum_eq_shield hJ
        exact (mass_eq_controlCeiling_iff_raw (p := p)).mpr (by rw [heq, hnum])

/-- On the wall the usual rotor determines the dual angles, so two ceiling
configurations in the same dual-only slice coincide. -/
theorem eq_of_onEnvelope_of_alpha_eq {p q : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hq : IsAdmissibleContinuous q)
    (hα : q.alpha = p.alpha)
    (hpE : mass p = controlCeiling (J p))
    (hqE : mass q = controlCeiling (J q)) : p = q := by
  have hpw := ((onEnvelope_iff hp).mp hpE).1
  have hqw := ((onEnvelope_iff hq).mp hqE).1
  have hβ : q.beta = p.beta := by
    funext a
    rw [beta_eq_wall hqw a, beta_eq_wall hpw a, hα]
  exact torsionParams_ext hα.symm hβ.symm

private theorem controlCeiling_zero :
    controlCeiling 0 = 5 * Real.pi ^ 2 / 16 := by
  have hnum : controlEnvelopeNum 0 = 0 := by
    unfold controlEnvelopeNum
    rw [show (4 : ℝ) * 0 ^ 2 = 0 by ring]
    exact min_eq_left (le_min (by positivity) (by positivity))
  unfold controlCeiling
  rw [hnum, zero_div, add_zero]

private theorem quarter_of_density_zero {p : TorsionParams}
    (hw : OnWall p) (a : Fin 3) (ht : axisSigned p a = 0) :
    p.alpha a = Real.pi / 4 ∧ p.beta a = Real.pi / 4 := by
  have hβ := beta_eq_wall hw a
  rw [axisSigned, hβ] at ht
  have hα : p.alpha a = Real.pi / 4 := by nlinarith [Real.pi_pos]
  refine ⟨hα, ?_⟩
  rw [hβ, hα]
  ring

/-- The heaviest shield assigns the three roles once each: one axis purely
usual, one purely dual, and the third split evenly, every axis on the wall. -/
theorem exists_heaviest_shield_roles {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hJ : J p = 0)
    (hM : mass p = 5 * Real.pi ^ 2 / 16) :
    ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsPureUsual p a ∧ IsPureDual p b ∧
      p.alpha c = Real.pi / 4 ∧ p.beta c = Real.pi / 4 := by
  have henv : mass p = controlCeiling (J p) := by
    rw [hJ, hM, controlCeiling_zero]
  have ⟨hw, hcorn⟩ := (onEnvelope_iff h).mp henv
  have hUU : ¬ TwoPureUsual p := by
    intro hUU
    have := le_J_of_twoPureUsual h hUU
    rw [hJ] at this
    have : (0 : ℝ) < Real.pi ^ 2 / 8 := by positivity
    linarith
  have hDD : ¬ TwoPureDual p := by
    intro hDD
    have := J_le_of_twoPureDual h hDD
    rw [hJ] at this
    have : (0 : ℝ) < Real.pi ^ 2 / 8 := by positivity
    linarith
  have hopp := opposed_of_twoCorners_not_same hcorn hUU hDD
  have hT := signedSum3 p
  rw [hJ, mul_zero] at hT
  rcases hopp with ⟨hu, hd⟩ | ⟨hd, hu⟩ | ⟨hu, hd⟩ | ⟨hd, hu⟩ | ⟨hu, hd⟩ | ⟨hd, hu⟩
  · have ht0 := (isPureUsual_iff_axisSigned h 0).mp hu
    have ht1 := (isPureDual_iff_axisSigned h 1).mp hd
    have ht2 : axisSigned p 2 = 0 := by linarith
    have hq := quarter_of_density_zero hw 2 ht2
    exact ⟨0, 1, 2, by decide, by decide, by decide, hu, hd, hq.1, hq.2⟩
  · have ht0 := (isPureDual_iff_axisSigned h 0).mp hd
    have ht1 := (isPureUsual_iff_axisSigned h 1).mp hu
    have ht2 : axisSigned p 2 = 0 := by linarith
    have hq := quarter_of_density_zero hw 2 ht2
    exact ⟨1, 0, 2, by decide, by decide, by decide, hu, hd, hq.1, hq.2⟩
  · have ht0 := (isPureUsual_iff_axisSigned h 0).mp hu
    have ht2 := (isPureDual_iff_axisSigned h 2).mp hd
    have ht1 : axisSigned p 1 = 0 := by linarith
    have hq := quarter_of_density_zero hw 1 ht1
    exact ⟨0, 2, 1, by decide, by decide, by decide, hu, hd, hq.1, hq.2⟩
  · have ht0 := (isPureDual_iff_axisSigned h 0).mp hd
    have ht2 := (isPureUsual_iff_axisSigned h 2).mp hu
    have ht1 : axisSigned p 1 = 0 := by linarith
    have hq := quarter_of_density_zero hw 1 ht1
    exact ⟨2, 0, 1, by decide, by decide, by decide, hu, hd, hq.1, hq.2⟩
  · have ht1 := (isPureUsual_iff_axisSigned h 1).mp hu
    have ht2 := (isPureDual_iff_axisSigned h 2).mp hd
    have ht0 : axisSigned p 0 = 0 := by linarith
    have hq := quarter_of_density_zero hw 0 ht0
    exact ⟨1, 2, 0, by decide, by decide, by decide, hu, hd, hq.1, hq.2⟩
  · have ht1 := (isPureDual_iff_axisSigned h 1).mp hd
    have ht2 := (isPureUsual_iff_axisSigned h 2).mp hu
    have ht0 : axisSigned p 0 = 0 := by linarith
    have hq := quarter_of_density_zero hw 0 ht0
    exact ⟨2, 1, 0, by decide, by decide, by decide, hu, hd, hq.1, hq.2⟩

end Gravity

end DstDiophantine
