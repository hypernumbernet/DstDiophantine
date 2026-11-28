import DoubleSpacetime.Gravity.BothChannels
import DoubleSpacetime.Gravity.ElectronOrbit
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Gravity-only layer force on a finite set

The radial term is the gravitational piece of `pairChannelForce`, with the
charge term absent. It points along the separation and is positive where
`gammaSEqual` is negative, which is a repulsive layer on the equal-scale
locus `J = 0`. The length `ℓ` and the prefactor `G` stay inputs. No
electromagnetic term is included, and no time step is taken. A vanishing
separation is not a contact law. The sign is this chart reading.
`RepulsionMomentum` computes the same coefficient as a motor separation and
shows that the relational momentum does not accelerate there. On a torsion
star the areal radius is a chart input, not that coefficient.
-/

namespace DoubleSpacetime

namespace Gravity

open Real
open scoped RealInnerProductSpace

/-- Gravity-only radial term. Positive increases the separation.
`κ` is the input `G m₁ m₂`, and the phase is `ℓ / (2r)`. -/
noncomputable def gravityLayerTerm (κ ℓ r : ℝ) : ℝ :=
  -κ / (gammaSEqual (ℓ / (2 * r)) * r ^ 2)

theorem gravityLayerTerm_eq_channel (κ ℓ r : ℝ) :
    gravityLayerTerm κ ℓ r =
      pairChannelForce κ 0 (gammaSEqual (ℓ / (2 * r))) 1 r := by
  unfold gravityLayerTerm pairChannelForce
  simp

theorem gravityLayerTerm_pos_of_repulsive {κ ℓ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hγ : gammaSEqual (ℓ / (2 * r)) < 0) :
    0 < gravityLayerTerm κ ℓ r := by
  unfold gravityLayerTerm
  have hr2 : 0 < r ^ 2 := by positivity
  have hden : gammaSEqual (ℓ / (2 * r)) * r ^ 2 < 0 := mul_neg_of_neg_of_pos hγ hr2
  exact div_pos_of_neg_of_neg (neg_lt_zero.mpr hκ) hden

theorem gravityLayerTerm_neg_of_attractive {κ ℓ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hγ : 0 < gammaSEqual (ℓ / (2 * r))) :
    gravityLayerTerm κ ℓ r < 0 := by
  unfold gravityLayerTerm
  have hr2 : 0 < r ^ 2 := by positivity
  have hden : 0 < gammaSEqual (ℓ / (2 * r)) * r ^ 2 := mul_pos hγ hr2
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hκ) hden

/-- On the first repulsive shell the gravity-only term increases the separation. -/
theorem gravityLayerTerm_pos_on_first_shell {κ ℓ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hx : ℓ / (2 * r) ∈ Set.Ioo resonanceRoot1 π) :
    0 < gravityLayerTerm κ ℓ r :=
  gravityLayerTerm_pos_of_repulsive hκ hr (gammaSEqual_neg_right_of_first_node hx)

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Force on the body at `p` from the body at `c`, along the separation `p - c`.
Its component on the outward unit separation is `gravityLayerTerm`. -/
noncomputable def gravityLayerPush (κ ℓ : ℝ) (c p : E) : E :=
  (gravityLayerTerm κ ℓ ‖p - c‖ / ‖p - c‖) • (p - c)

theorem gravityLayerPush_antisymm (κ ℓ : ℝ) (c p : E) :
    gravityLayerPush κ ℓ c p = -gravityLayerPush κ ℓ p c := by
  unfold gravityLayerPush
  rw [show p - c = -(c - p) by abel, norm_neg, smul_neg]

theorem gravityLayerPush_radial (κ ℓ : ℝ) (c p : E) (hpc : p ≠ c) :
    ⟪gravityLayerPush κ ℓ c p, (‖p - c‖)⁻¹ • (p - c)⟫ =
      gravityLayerTerm κ ℓ ‖p - c‖ := by
  have hr0 : ‖p - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpc)
  unfold gravityLayerPush
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp [hr0]

theorem gravityLayerPush_increases_separation {κ ℓ : ℝ} {c p : E}
    (hκ : 0 < κ) (hpc : p ≠ c)
    (hγ : gammaSEqual (ℓ / (2 * ‖p - c‖)) < 0) :
    0 < ⟪gravityLayerPush κ ℓ c p, (‖p - c‖)⁻¹ • (p - c)⟫ := by
  rw [gravityLayerPush_radial κ ℓ c p hpc]
  exact gravityLayerTerm_pos_of_repulsive hκ (norm_pos_iff.mpr (sub_ne_zero.mpr hpc)) hγ

theorem gravityLayerPush_mutual {κ ℓ : ℝ} {c p : E}
    (hκ : 0 < κ) (hpc : p ≠ c)
    (hγ : gammaSEqual (ℓ / (2 * ‖p - c‖)) < 0) :
    0 < ⟪gravityLayerPush κ ℓ c p - gravityLayerPush κ ℓ p c,
      (‖p - c‖)⁻¹ • (p - c)⟫ := by
  rw [gravityLayerPush_antisymm κ ℓ p c, sub_neg_eq_add, ← two_smul ℝ,
    real_inner_smul_left]
  exact mul_pos (by norm_num) (gravityLayerPush_increases_separation hκ hpc hγ)

/-- Sum, on body `i`, of the gravity-only pushes from the other bodies in `S`. -/
noncomputable def gravityLayerForce {ι : Type*} [DecidableEq ι]
    (ℓ G : ℝ) (mass : ι → ℝ) (pos : ι → E) (S : Finset ι) (i : ι) : E :=
  ∑ j ∈ S.erase i, gravityLayerPush (G * mass i * mass j) ℓ (pos j) (pos i)

theorem gravityLayerForce_each_increases {ι : Type*} [DecidableEq ι]
    {ℓ G : ℝ} {mass : ι → ℝ} {pos : ι → E} {S : Finset ι} {i : ι}
    (hi : i ∈ S) (hG : 0 < G) (hm : ∀ k ∈ S, 0 < mass k)
    (hdist : ∀ j ∈ S.erase i, pos i ≠ pos j)
    (hγ : ∀ j ∈ S.erase i, gammaSEqual (ℓ / (2 * ‖pos i - pos j‖)) < 0) :
    ∀ j ∈ S.erase i,
      0 < ⟪gravityLayerPush (G * mass i * mass j) ℓ (pos j) (pos i),
        (‖pos i - pos j‖)⁻¹ • (pos i - pos j)⟫ := by
  intro j hj
  have hjS : j ∈ S := Finset.mem_of_mem_erase hj
  have hκ : 0 < G * mass i * mass j := mul_pos (mul_pos hG (hm i hi)) (hm j hjS)
  exact gravityLayerPush_increases_separation hκ (hdist j hj) (hγ j hj)

end Space

end Gravity

end DoubleSpacetime
