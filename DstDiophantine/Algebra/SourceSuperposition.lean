import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.Invariant
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Superposition of source bivectors

Sources add in the six-dimensional coefficient space. That internal sum is
commutative and has no ceiling: the quadratic `J` on it may exceed `3π²/8`.

The configuration a particle expresses is the unique admissible point closest
to the internal sum in the squared Euclidean distance of the six coefficients.
The cone is a product of triangles, so the closest point is taken axis by
axis. Inside the cone the closest point is the sum itself. On an axis with
nonnegative coefficients, once their sum is at least `π/2` and their
difference is still within `π/2`, the expressed sum is `π/2` and the
expressed difference is the internal difference. Once the difference reaches
`π/2`, the expressed state locks at a pure corner.

## What is not claimed

The nearest-point readout is not a derivation of the Newtonian multi-body
law, and it does not alter the coefficient-wise Faraday addition. A Faraday
increment that leaves the cone is an internal departure; the mismatch then
expressed is the closest admissible point.
-/

namespace DstDiophantine

namespace SourceSuperposition

open Admissible Invariant Operations Real

/-- One axis of the admissible cone: `α ≥ 0`, `β ≥ 0`, `α + β ≤ π/2`. -/
def InTriangle (x y : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ Real.pi / 2

/-- Voronoi cell of the pure-boost corner `(π/2, 0)`. -/
def InPureUsual (x y : ℝ) : Prop :=
  Real.pi / 2 ≤ x ∧ y ≤ x - Real.pi / 2

/-- Voronoi cell of the pure-rotation corner `(0, π/2)`. -/
def InPureDual (x y : ℝ) : Prop :=
  Real.pi / 2 ≤ y ∧ x ≤ y - Real.pi / 2

/-- Slab whose orthogonal foot lands on the hypotenuse, including the triangle. -/
def InWall (x y : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧ |x - y| ≤ Real.pi / 2

/-- Outward slab of the usual edge, including its corners. -/
def InUsualEdge (x y : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ Real.pi / 2 ∧ y ≤ 0

/-- Outward slab of the dual edge, including its corners. -/
def InDualEdge (x y : ℝ) : Prop :=
  0 ≤ y ∧ y ≤ Real.pi / 2 ∧ x ≤ 0

theorem admissible_iff_axes (p : TorsionParams) :
    IsAdmissibleContinuous p ↔ ∀ a, InTriangle (p.alpha a) (p.beta a) := by
  unfold IsAdmissibleContinuous InTriangle
  rfl

/-- Orthogonal foot of `(x, y)` on the line `α + β = π/2`. -/
noncomputable def wallPoint (x y : ℝ) : ℝ × ℝ :=
  ((x - y + Real.pi / 2) / 2, (y - x + Real.pi / 2) / 2)

theorem wallPoint_sum_diff (x y : ℝ) :
    (wallPoint x y).1 + (wallPoint x y).2 = Real.pi / 2 ∧
      (wallPoint x y).1 - (wallPoint x y).2 = x - y := by
  unfold wallPoint
  constructor <;> ring

/-- Expressed coefficients on one axis: the nearest point of the triangle. -/
noncomputable def axisExpress (x y : ℝ) : ℝ × ℝ :=
  open Classical in
  if InTriangle x y then (x, y)
  else if InPureUsual x y then (Real.pi / 2, 0)
  else if InPureDual x y then (0, Real.pi / 2)
  else if InWall x y then wallPoint x y
  else if InUsualEdge x y then (x, 0)
  else if InDualEdge x y then (0, y)
  else (0, 0)

theorem axisExpress_triangle {x y : ℝ} (h : InTriangle x y) :
    axisExpress x y = (x, y) := by
  unfold axisExpress
  rw [ite_eq_left h]

theorem axisExpress_pureUsual {x y : ℝ} (h : InPureUsual x y) :
    axisExpress x y = (Real.pi / 2, 0) := by
  classical
  unfold axisExpress
  by_cases ht : InTriangle x y
  · have hy : y = 0 := by
      have hy_nonneg : 0 ≤ y := ht.2.1
      have hy_le : y ≤ 0 := by linarith [h.1, h.2, ht.2.2]
      linarith
    have hx : x = Real.pi / 2 := by linarith [h.1, ht.2.2, hy]
    rw [ite_eq_left ht]
    simp [hx, hy]
  · rw [ite_eq_right ht, ite_eq_left h]

theorem axisExpress_pureDual {x y : ℝ} (h : InPureDual x y) :
    axisExpress x y = (0, Real.pi / 2) := by
  classical
  unfold axisExpress
  by_cases ht : InTriangle x y
  · have hx : x = 0 := by
      have hx_nonneg : 0 ≤ x := ht.1
      have hx_le : x ≤ 0 := by linarith [h.1, h.2, ht.2.2]
      linarith
    have hy : y = Real.pi / 2 := by linarith [h.1, ht.2.2, hx]
    rw [ite_eq_left ht]
    simp [hx, hy]
  · by_cases hu : InPureUsual x y
    · exfalso
      have hyx : y + Real.pi / 2 ≤ x := by linarith [hu.2]
      have hxy : x + Real.pi / 2 ≤ y := by linarith [h.2]
      linarith [hyx, hxy, Real.pi_pos]
    · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_left h]

/-- Nonnegative coefficients with `σ ≥ π/2` and `|δ| ≤ π/2` express the wall formula. -/
theorem axisExpress_eq_wallPoint {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : Real.pi / 2 ≤ x + y)
    (hd : |x - y| ≤ Real.pi / 2) :
    axisExpress x y = wallPoint x y := by
  classical
  have hwall : InWall x y := ⟨hx, hy, hd⟩
  by_cases ht : InTriangle x y
  · have hsum : x + y = Real.pi / 2 := by linarith [ht.2.2, hs]
    have hid : (x, y) = wallPoint x y := by
      unfold wallPoint
      ext <;> linarith [hsum]
    rw [axisExpress_triangle ht, hid]
  · by_cases hu : InPureUsual x y
    · have hd_eq : x - y = Real.pi / 2 := by
        have hd_ge : Real.pi / 2 ≤ x - y := by linarith [hu.2]
        have hd_le : x - y ≤ Real.pi / 2 := (abs_le.mp hd).2
        linarith
      rw [axisExpress_pureUsual hu]
      unfold wallPoint
      ext <;> linarith [hd_eq]
    · by_cases hdual : InPureDual x y
      · have hd_eq : y - x = Real.pi / 2 := by
          have hd_ge : Real.pi / 2 ≤ y - x := by linarith [hdual.2]
          have hd_le : y - x ≤ Real.pi / 2 := by
            have := (abs_le.mp hd).1
            linarith
          linarith
        rw [axisExpress_pureDual hdual]
        unfold wallPoint
        ext <;> linarith [hd_eq]
      · unfold axisExpress
        rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hdual, ite_eq_left hwall]

/-- A nonnegative excess of usual over dual locks the axis at `(π/2, 0)`. -/
theorem axisExpress_lock_usual {x y : ℝ}
    (_hx : 0 ≤ x) (hy : 0 ≤ y) (hd : Real.pi / 2 ≤ x - y) :
    axisExpress x y = (Real.pi / 2, 0) := by
  have h : InPureUsual x y := by
    constructor
    · linarith
    · linarith
  exact axisExpress_pureUsual h

/-- A nonnegative excess of dual over usual locks the axis at `(0, π/2)`. -/
theorem axisExpress_lock_dual {x y : ℝ}
    (hx : 0 ≤ x) (_hy : 0 ≤ y) (hd : Real.pi / 2 ≤ y - x) :
    axisExpress x y = (0, Real.pi / 2) := by
  have h : InPureDual x y := by
    constructor
    · linarith
    · linarith
  exact axisExpress_pureDual h

private theorem outside_nonpos {x y : ℝ}
    (h1 : ¬ InTriangle x y) (h2 : ¬ InPureUsual x y) (h3 : ¬ InPureDual x y)
    (h4 : ¬ InWall x y) (h5 : ¬ InUsualEdge x y) (h6 : ¬ InDualEdge x y) :
    x ≤ 0 ∧ y ≤ 0 := by
  classical
  have hy : y ≤ 0 := by
    by_contra hy
    have hy0 : 0 < y := (not_le).mp hy
    by_cases hx : 0 ≤ x
    · by_cases hs : x + y ≤ Real.pi / 2
      · exact h1 ⟨hx, le_of_lt hy0, hs⟩
      · by_cases hd : |x - y| ≤ Real.pi / 2
        · exact h4 ⟨hx, le_of_lt hy0, hd⟩
        · by_cases hxy : Real.pi / 2 ≤ x - y
          · exact h2 ⟨by linarith, by linarith⟩
          · have hrev : Real.pi / 2 < y - x := by
              have habs : Real.pi / 2 < |x - y| := (not_le).mp hd
              have hdlt : x - y < 0 := by
                by_contra hnn
                have hge : 0 ≤ x - y := (not_lt).mp hnn
                rw [abs_of_nonneg hge] at habs
                linarith [habs, (not_le).mp hxy]
              rw [abs_of_neg hdlt] at habs
              linarith
            exact h3 ⟨by linarith, by linarith⟩
    · have hxlt : x < 0 := (not_le).mp hx
      by_cases hyh : y ≤ Real.pi / 2
      · exact h6 ⟨le_of_lt hy0, hyh, le_of_lt hxlt⟩
      · exact h3 ⟨le_of_lt ((not_le).mp hyh), by linarith⟩
  have hx : x ≤ 0 := by
    by_contra hx
    have hx0 : 0 < x := (not_le).mp hx
    by_cases hxh : x ≤ Real.pi / 2
    · exact h5 ⟨le_of_lt hx0, hxh, hy⟩
    · exact h2 ⟨le_of_lt ((not_le).mp hxh), by linarith⟩
  exact ⟨hx, hy⟩

theorem axisExpress_mem (x y : ℝ) : InTriangle (axisExpress x y).1 (axisExpress x y).2 := by
  classical
  unfold axisExpress
  by_cases ht : InTriangle x y
  · simpa [ite_eq_left ht] using ht
  · by_cases hu : InPureUsual x y
    · rw [ite_eq_right ht, ite_eq_left hu]
      exact ⟨le_of_lt (div_pos Real.pi_pos (by norm_num)), le_refl 0,
        le_of_eq (by ring)⟩
    · by_cases hd : InPureDual x y
      · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_left hd]
        exact ⟨le_refl 0, le_of_lt (div_pos Real.pi_pos (by norm_num)),
          le_of_eq (by ring)⟩
      · by_cases hw : InWall x y
        · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hd, ite_eq_left hw]
          have hsum := (wallPoint_sum_diff x y).1
          have habs := abs_le.mp hw.2.2
          constructor
          · unfold wallPoint
            linarith
          · constructor
            · unfold wallPoint
              linarith
            · linarith
        · by_cases he : InUsualEdge x y
          · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hd, ite_eq_right hw, ite_eq_left he]
            exact ⟨he.1, le_refl 0, by linarith [he.2.1]⟩
          · by_cases hf : InDualEdge x y
            · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hd, ite_eq_right hw,
                ite_eq_right he, ite_eq_left hf]
              exact ⟨le_refl 0, hf.1, by linarith [hf.2.1]⟩
            · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hd, ite_eq_right hw,
                ite_eq_right he, ite_eq_right hf]
              exact ⟨le_refl 0, le_refl 0, by linarith [Real.pi_pos]⟩

/-- Squared-distance pairing of an internal point against a comparison point. -/
def dot2 (x y ex ey vx vy : ℝ) : ℝ :=
  (x - ex) * (vx - ex) + (y - ey) * (vy - ey)

private theorem vertexDots (x y : ℝ) :
    let e := axisExpress x y
    dot2 x y e.1 e.2 0 0 ≤ 0 ∧
      dot2 x y e.1 e.2 (Real.pi / 2) 0 ≤ 0 ∧
      dot2 x y e.1 e.2 0 (Real.pi / 2) ≤ 0 := by
  classical
  unfold axisExpress
  by_cases ht : InTriangle x y
  · rw [ite_eq_left ht]
    simp [dot2]
  · by_cases hu : InPureUsual x y
    · rw [ite_eq_right ht, ite_eq_left hu]
      refine ⟨?_, ?_, ?_⟩
      · have : 0 ≤ x - Real.pi / 2 := by linarith [hu.1]
        unfold dot2
        nlinarith [Real.pi_pos, hu.1]
      · exact le_of_eq (by unfold dot2; ring)
      · unfold dot2
        nlinarith [Real.pi_pos, hu.2]
    · by_cases hd : InPureDual x y
      · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_left hd]
        refine ⟨?_, ?_, ?_⟩
        · have : 0 ≤ y - Real.pi / 2 := by linarith [hd.1]
          unfold dot2
          nlinarith [Real.pi_pos, hd.1]
        · unfold dot2
          nlinarith [Real.pi_pos, hd.2]
        · exact le_of_eq (by unfold dot2; ring)
      · by_cases hw : InWall x y
        · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hd, ite_eq_left hw]
          have hsum_gt : Real.pi / 2 ≤ x + y := by
            have hnot : ¬ x + y ≤ Real.pi / 2 := by
              intro hs
              exact ht ⟨hw.1, hw.2.1, hs⟩
            exact le_of_lt ((not_le).mp hnot)
          set t : ℝ := (x + y - Real.pi / 2) / 2
          have ht0 : 0 ≤ t := by unfold t; linarith
          have hx' : (wallPoint x y).1 = (x - y + Real.pi / 2) / 2 := rfl
          have hy' : (wallPoint x y).2 = (y - x + Real.pi / 2) / 2 := rfl
          have hxt : x - (wallPoint x y).1 = t := by unfold t; rw [hx']; ring
          have hyt : y - (wallPoint x y).2 = t := by unfold t; rw [hy']; ring
          have hsum' : (wallPoint x y).1 + (wallPoint x y).2 = Real.pi / 2 :=
            (wallPoint_sum_diff x y).1
          refine ⟨?_, ?_, ?_⟩
          · unfold dot2
            rw [hxt, hyt]
            nlinarith [ht0, hsum', Real.pi_pos]
          · unfold dot2
            rw [hxt, hyt]
            nlinarith [hsum']
          · unfold dot2
            rw [hxt, hyt]
            nlinarith [hsum']
        · by_cases he : InUsualEdge x y
          · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hd, ite_eq_right hw, ite_eq_left he]
            refine ⟨?_, ?_, ?_⟩
            · exact le_of_eq (by unfold dot2; ring)
            · exact le_of_eq (by unfold dot2; ring)
            · unfold dot2
              nlinarith [he.2.2, Real.pi_pos]
          · by_cases hf : InDualEdge x y
            · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hd, ite_eq_right hw,
                ite_eq_right he, ite_eq_left hf]
              refine ⟨?_, ?_, ?_⟩
              · exact le_of_eq (by unfold dot2; ring)
              · unfold dot2
                nlinarith [hf.2.2, Real.pi_pos]
              · exact le_of_eq (by unfold dot2; ring)
            · have hout := outside_nonpos ht hu hd hw he hf
              rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hd, ite_eq_right hw,
                ite_eq_right he, ite_eq_right hf]
              refine ⟨?_, ?_, ?_⟩
              · exact le_of_eq (by unfold dot2; ring)
              · unfold dot2
                nlinarith [hout.1, Real.pi_pos]
              · unfold dot2
                nlinarith [hout.2, Real.pi_pos]

private theorem dot_bary {x y ex ey qx qy : ℝ} :
    dot2 x y ex ey qx qy =
      ((Real.pi / 2 - qx - qy) / (Real.pi / 2)) * dot2 x y ex ey 0 0 +
        (qx / (Real.pi / 2)) * dot2 x y ex ey (Real.pi / 2) 0 +
        (qy / (Real.pi / 2)) * dot2 x y ex ey 0 (Real.pi / 2) := by
  have hh : Real.pi / 2 ≠ 0 := by positivity
  unfold dot2
  field_simp [hh]
  ring

theorem axisDot_le {x y qx qy : ℝ} (hq : InTriangle qx qy) :
    dot2 x y (axisExpress x y).1 (axisExpress x y).2 qx qy ≤ 0 := by
  have hv := vertexDots x y
  rw [dot_bary]
  have ha : 0 ≤ (Real.pi / 2 - qx - qy) / (Real.pi / 2) := by
    apply div_nonneg
    · linarith [hq.2.2]
    · positivity
  have hb : 0 ≤ qx / (Real.pi / 2) := div_nonneg hq.1 (by positivity)
  have hc : 0 ≤ qy / (Real.pi / 2) := div_nonneg hq.2.1 (by positivity)
  have h1 : ((Real.pi / 2 - qx - qy) / (Real.pi / 2)) *
      dot2 x y (axisExpress x y).1 (axisExpress x y).2 0 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha hv.1
  have h2 : (qx / (Real.pi / 2)) *
      dot2 x y (axisExpress x y).1 (axisExpress x y).2 (Real.pi / 2) 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hb hv.2.1
  have h3 : (qy / (Real.pi / 2)) *
      dot2 x y (axisExpress x y).1 (axisExpress x y).2 0 (Real.pi / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc hv.2.2
  linarith

theorem axisSq_le {x y qx qy : ℝ} (hq : InTriangle qx qy) :
    (x - (axisExpress x y).1) ^ 2 + (y - (axisExpress x y).2) ^ 2 ≤
      (x - qx) ^ 2 + (y - qy) ^ 2 := by
  have hdot := axisDot_le (x := x) (y := y) hq
  have hgap :
      (x - qx) ^ 2 + (y - qy) ^ 2 -
          ((x - (axisExpress x y).1) ^ 2 + (y - (axisExpress x y).2) ^ 2) =
        ((axisExpress x y).1 - qx) ^ 2 + ((axisExpress x y).2 - qy) ^ 2 -
          2 * dot2 x y (axisExpress x y).1 (axisExpress x y).2 qx qy := by
    unfold dot2
    ring
  have hnn : 0 ≤ ((axisExpress x y).1 - qx) ^ 2 + ((axisExpress x y).2 - qy) ^ 2 := by
    positivity
  linarith

theorem axisSq_eq_zero_iff {x y qx qy : ℝ} (hq : InTriangle qx qy) :
    (x - qx) ^ 2 + (y - qy) ^ 2 =
        (x - (axisExpress x y).1) ^ 2 + (y - (axisExpress x y).2) ^ 2 ↔
      qx = (axisExpress x y).1 ∧ qy = (axisExpress x y).2 := by
  constructor
  · intro h
    have hdot := axisDot_le (x := x) (y := y) hq
    have hgap :
        (x - qx) ^ 2 + (y - qy) ^ 2 -
            ((x - (axisExpress x y).1) ^ 2 + (y - (axisExpress x y).2) ^ 2) =
          ((axisExpress x y).1 - qx) ^ 2 + ((axisExpress x y).2 - qy) ^ 2 -
            2 * dot2 x y (axisExpress x y).1 (axisExpress x y).2 qx qy := by
      unfold dot2
      ring
    have hzero : ((axisExpress x y).1 - qx) ^ 2 + ((axisExpress x y).2 - qy) ^ 2 = 0 := by
      nlinarith [hdot, hgap, h]
    have hx0 : ((axisExpress x y).1 - qx) ^ 2 = 0 := by nlinarith [hzero]
    have hy0 : ((axisExpress x y).2 - qy) ^ 2 = 0 := by nlinarith [hzero]
    exact ⟨by linarith [sq_eq_zero_iff.mp hx0], by linarith [sq_eq_zero_iff.mp hy0]⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The admissible point a particle expresses. -/
noncomputable def express (p : TorsionParams) : TorsionParams where
  alpha := fun a => (axisExpress (p.alpha a) (p.beta a)).1
  beta := fun a => (axisExpress (p.alpha a) (p.beta a)).2

theorem express_admissible (p : TorsionParams) : IsAdmissibleContinuous (express p) := by
  rw [admissible_iff_axes]
  intro a
  simpa [express] using axisExpress_mem (p.alpha a) (p.beta a)

theorem express_eq_of_admissible {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    express p = p := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a
    have he := axisExpress_triangle ((admissible_iff_axes p).mp h a)
    simp [he]
  · funext a
    have he := axisExpress_triangle ((admissible_iff_axes p).mp h a)
    simp [he]

theorem express_idempotent (p : TorsionParams) : express (express p) = express p :=
  express_eq_of_admissible (express_admissible p)

theorem abs_J_express_le (p : TorsionParams) :
    |J (express p)| ≤ 3 * Real.pi ^ 2 / 8 :=
  torsion_bound_raw_continuous_pi_sq _ (express_admissible p)

theorem mass_express_le (p : TorsionParams) :
    mass (express p) ≤ 3 * Real.pi ^ 2 / 8 :=
  mass_bound_raw_continuous _ (express_admissible p)

/-- Squared Euclidean distance of the six coefficients. -/
def sqDist (p q : TorsionParams) : ℝ :=
  ∑ a : Fin 3, ((p.alpha a - q.alpha a) ^ 2 + (p.beta a - q.beta a) ^ 2)

private theorem sq_sub_comm (a b : ℝ) : (a - b) ^ 2 = (b - a) ^ 2 := by
  ring

theorem sqDist_express_le (p q : TorsionParams) (hq : IsAdmissibleContinuous q) :
    sqDist (express p) p ≤ sqDist q p := by
  unfold sqDist
  refine Finset.sum_le_sum fun a _ => ?_
  have h := axisSq_le (x := p.alpha a) (y := p.beta a) ((admissible_iff_axes q).mp hq a)
  have h1 := sq_sub_comm ((express p).alpha a) (p.alpha a)
  have h2 := sq_sub_comm ((express p).beta a) (p.beta a)
  have h3 := sq_sub_comm (q.alpha a) (p.alpha a)
  have h4 := sq_sub_comm (q.beta a) (p.beta a)
  simp only [express] at h h1 h2 ⊢
  linarith

theorem eq_express_of_sqDist_le {p q : TorsionParams}
    (hq : IsAdmissibleContinuous q)
    (hle : sqDist q p ≤ sqDist (express p) p) :
    q = express p := by
  have hgap : ∀ a : Fin 3,
      0 ≤ (p.alpha a - q.alpha a) ^ 2 + (p.beta a - q.beta a) ^ 2 -
        ((p.alpha a - (express p).alpha a) ^ 2 + (p.beta a - (express p).beta a) ^ 2) := by
    intro a
    have := axisSq_le (x := p.alpha a) (y := p.beta a) ((admissible_iff_axes q).mp hq a)
    simpa [express] using this
  have hsum :
      ∑ a : Fin 3,
          ((p.alpha a - q.alpha a) ^ 2 + (p.beta a - q.beta a) ^ 2 -
            ((p.alpha a - (express p).alpha a) ^ 2 +
              (p.beta a - (express p).beta a) ^ 2)) =
        sqDist q p - sqDist (express p) p := by
    unfold sqDist
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sq_sub_comm (q.alpha a) (p.alpha a), sq_sub_comm (q.beta a) (p.beta a),
      sq_sub_comm ((express p).alpha a) (p.alpha a),
      sq_sub_comm ((express p).beta a) (p.beta a)]
  have hnonneg :
      0 ≤ ∑ a : Fin 3,
          ((p.alpha a - q.alpha a) ^ 2 + (p.beta a - q.beta a) ^ 2 -
            ((p.alpha a - (express p).alpha a) ^ 2 +
              (p.beta a - (express p).beta a) ^ 2)) :=
    Finset.sum_nonneg fun a _ => hgap a
  have hzero : ∑ a : Fin 3,
      ((p.alpha a - q.alpha a) ^ 2 + (p.beta a - q.beta a) ^ 2 -
        ((p.alpha a - (express p).alpha a) ^ 2 +
          (p.beta a - (express p).beta a) ^ 2)) = 0 := by
    linarith [hle, hsum, hnonneg]
  have haxis : ∀ a : Fin 3,
      (p.alpha a - q.alpha a) ^ 2 + (p.beta a - q.beta a) ^ 2 =
        (p.alpha a - (express p).alpha a) ^ 2 + (p.beta a - (express p).beta a) ^ 2 := by
    intro a
    have hterm :
        (p.alpha a - q.alpha a) ^ 2 + (p.beta a - q.beta a) ^ 2 -
          ((p.alpha a - (express p).alpha a) ^ 2 +
            (p.beta a - (express p).beta a) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hgap a)).mp hzero a (Finset.mem_univ a)
    linarith
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a
    exact ((axisSq_eq_zero_iff ((admissible_iff_axes q).mp hq a)).mp (by
      simpa [express] using haxis a)).1
  · funext a
    exact ((axisSq_eq_zero_iff ((admissible_iff_axes q).mp hq a)).mp (by
      simpa [express] using haxis a)).2

/-- Componentwise sum of two torsional bivectors. -/
def addParams (p q : TorsionParams) : TorsionParams where
  alpha := fun a => p.alpha a + q.alpha a
  beta := fun a => p.beta a + q.beta a

theorem addParams_comm (p q : TorsionParams) : addParams p q = addParams q p := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a; ring
  · funext a; ring

theorem addParams_assoc (p q r : TorsionParams) :
    addParams (addParams p q) r = addParams p (addParams q r) := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a; simp only [addParams]; ring
  · funext a; simp only [addParams]; ring

theorem addParams_left_comm (p q r : TorsionParams) :
    addParams p (addParams q r) = addParams q (addParams p r) := by
  rw [← addParams_assoc, addParams_comm p q, addParams_assoc]

/-- Internal sum of source bivectors. Order is immaterial. -/
def sumParams (ps : List TorsionParams) : TorsionParams where
  alpha := fun a => (ps.map (fun p => p.alpha a)).sum
  beta := fun a => (ps.map (fun p => p.beta a)).sum

theorem sumParams_cons (p : TorsionParams) (ps : List TorsionParams) :
    sumParams (p :: ps) = addParams p (sumParams ps) := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a; simp [sumParams, List.map_cons, List.sum_cons]
  · funext a; simp [sumParams, List.map_cons, List.sum_cons]

theorem sumParams_perm {ps qs : List TorsionParams} (h : ps.Perm qs) :
    sumParams ps = sumParams qs := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    rw [sumParams_cons, sumParams_cons, ih]
  | swap x y _ =>
    rw [sumParams_cons, sumParams_cons, sumParams_cons, sumParams_cons, addParams_left_comm]
  | trans _ _ ih1 ih2 =>
    exact ih1.trans ih2

/-- The mismatch expressed by a list of sources. -/
noncomputable def expressedSuperposition (ps : List TorsionParams) : TorsionParams :=
  express (sumParams ps)

/-- A pure boost of rapidity `φ` on one axis. -/
def axisBoost (a0 : Fin 3) (φ : ℝ) : TorsionParams where
  alpha := fun a => if a = a0 then φ else 0
  beta := fun _ => 0

theorem J_axisBoost (a0 : Fin 3) (φ : ℝ) :
    J (axisBoost a0 φ) = φ ^ 2 / 2 := by
  rw [J_coef, Fin.sum_univ_three]
  fin_cases a0 <;> simp [axisBoost] <;> ring

theorem axisBoost_admissible {a0 : Fin 3} {φ : ℝ}
    (h0 : 0 ≤ φ) (hφ : φ ≤ Real.pi / 2) :
    IsAdmissibleContinuous (axisBoost a0 φ) := by
  intro a
  by_cases h : a = a0
  · simp only [axisBoost, h, ite_true]
    exact ⟨h0, le_refl 0, by linarith⟩
  · simp only [axisBoost, h, ite_false]
    exact ⟨le_refl 0, le_refl 0, by linarith [Real.pi_pos]⟩

theorem sumParams_replicate_axisBoost (n : ℕ) (a0 : Fin 3) (φ : ℝ) :
    sumParams (List.replicate n (axisBoost a0 φ)) = axisBoost a0 ((n : ℝ) * φ) := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a
    simp only [axisBoost, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
    split_ifs <;> ring
  · funext a
    simp [axisBoost, List.map_replicate, List.sum_replicate]

theorem express_axisBoost_saturated {a0 : Fin 3} {φ : ℝ} (hφ : Real.pi / 2 ≤ φ) :
    express (axisBoost a0 φ) = axisBoost a0 (Real.pi / 2) := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a
    by_cases h : a = a0
    · have he := axisExpress_pureUsual (x := φ) (y := 0)
        ⟨hφ, by linarith⟩
      simp [axisBoost, h, he]
    · have he := axisExpress_triangle (x := (0 : ℝ)) (y := 0)
        ⟨le_refl 0, le_refl 0, by linarith [Real.pi_pos]⟩
      simp [axisBoost, h, he]
  · funext a
    by_cases h : a = a0
    · have he := axisExpress_pureUsual (x := φ) (y := 0)
        ⟨hφ, by linarith⟩
      simp [axisBoost, h, he]
    · have he := axisExpress_triangle (x := (0 : ℝ)) (y := 0)
        ⟨le_refl 0, le_refl 0, by linarith [Real.pi_pos]⟩
      simp [axisBoost, h, he]

/-- `n ≥ 1` coincident pure boosts of rapidity `π/2` express `J = π²/8` on that axis. -/
theorem J_express_repeat_pure_boost {n : ℕ} (hn : 1 ≤ n) (a0 : Fin 3) :
    J (expressedSuperposition (List.replicate n (axisBoost a0 (Real.pi / 2)))) =
      Real.pi ^ 2 / 8 := by
  have hsum := sumParams_replicate_axisBoost n a0 (Real.pi / 2)
  have hφ : Real.pi / 2 ≤ (n : ℝ) * (Real.pi / 2) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  unfold expressedSuperposition
  rw [hsum, express_axisBoost_saturated hφ, J_axisBoost]
  ring

/-- The quadratic on the same internal sum is `n² π²/8`, with no ceiling. -/
theorem J_internal_repeat_pure_boost (n : ℕ) (a0 : Fin 3) :
    J (sumParams (List.replicate n (axisBoost a0 (Real.pi / 2)))) =
      (n : ℝ) ^ 2 * (Real.pi ^ 2 / 8) := by
  rw [sumParams_replicate_axisBoost, J_axisBoost]
  ring

theorem J_internal_repeat_gt_ceiling {n : ℕ} (hn : 2 ≤ n) (a0 : Fin 3) :
    3 * Real.pi ^ 2 / 8 <
      J (sumParams (List.replicate n (axisBoost a0 (Real.pi / 2)))) := by
  rw [J_internal_repeat_pure_boost]
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hπ : 0 < Real.pi ^ 2 := by positivity
  nlinarith [hn2, hπ]

/-- The internal quadratic is unbounded, while every expressed mismatch stays within the ceiling. -/
theorem internal_unbounded_expressed_bounded :
    (∀ p : TorsionParams, |J (express p)| ≤ 3 * Real.pi ^ 2 / 8) ∧
      (∀ C : ℝ, ∃ p : TorsionParams, C < J p) := by
  refine ⟨abs_J_express_le, ?_⟩
  intro C
  refine ⟨axisBoost 0 (2 * |C| + 1), ?_⟩
  rw [J_axisBoost]
  have habs : 0 ≤ |C| := abs_nonneg C
  nlinarith [sq_abs C, sq_nonneg (|C|)]

/-- Two aligned boosts of rapidity `π/4` express `J = π²/8`, not the sum `π²/16` of their values. -/
theorem J_two_quarter_boosts (a0 : Fin 3) :
    let p := axisBoost a0 (Real.pi / 4)
    let s := sumParams [p, p]
    IsAdmissibleContinuous p ∧ IsAdmissibleContinuous s ∧ express s = s ∧
      J p = Real.pi ^ 2 / 32 ∧ J s = Real.pi ^ 2 / 8 ∧
      J p + J p = Real.pi ^ 2 / 16 ∧ J s ≠ J p + J p := by
  set p : TorsionParams := axisBoost a0 (Real.pi / 4)
  set s : TorsionParams := sumParams [p, p]
  change
    IsAdmissibleContinuous p ∧ IsAdmissibleContinuous s ∧ express s = s ∧
      J p = Real.pi ^ 2 / 32 ∧ J s = Real.pi ^ 2 / 8 ∧
      J p + J p = Real.pi ^ 2 / 16 ∧ J s ≠ J p + J p
  have hp : IsAdmissibleContinuous p :=
    axisBoost_admissible (a0 := a0) (φ := Real.pi / 4) (by positivity) (by linarith [Real.pi_pos])
  have hs_eq : s = axisBoost a0 (Real.pi / 2) := by
    simp only [s, p, sumParams, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    refine congrArg₂ TorsionParams.mk ?_ ?_
    · funext a
      simp only [axisBoost]
      split_ifs <;> ring
    · funext a
      simp [axisBoost]
  have hs : IsAdmissibleContinuous s := by
    rw [hs_eq]
    exact axisBoost_admissible (a0 := a0) (φ := Real.pi / 2) (by positivity) le_rfl
  have hJ : J p = Real.pi ^ 2 / 32 := by
    rw [J_axisBoost]
    ring
  have hJs : J s = Real.pi ^ 2 / 8 := by
    rw [hs_eq, J_axisBoost]
    ring
  refine ⟨hp, hs, express_eq_of_admissible hs, hJ, hJs, ?_, ?_⟩
  · rw [hJ]
    ring
  · rw [hJs, hJ]
    intro h
    exfalso
    nlinarith [h, Real.pi_pos]

end SourceSuperposition

end DstDiophantine
