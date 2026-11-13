import DstDiophantine.Gravity.ElectronExclusion
import DstDiophantine.Gravity.HeliumBody
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Spin and the exclusion of a repeated ray

The place of an electron is an element of the three-sphere. Its spin factor
is a dual spinor. Spin reversal keeps the place and reverses the spin vector.
The repeated ray is a joint state of two spin factors. It is not the singlet,
at every place, including places at which the mass channel attracts.

## Not claimed

* A derivation of the spin-statistics theorem.
* That the outward pole is absent as a force. Two electron masses whose
  laboratory separation has crossed the first gravitational node still meet it.
* An identification of the three cosines with the separations that enter `γ_s`.

## What is proved

* Spin reversal keeps the place, is not the same ray, and reverses the spin
  vector.
* One place occurs with opposite rays, and the joint state is the singlet. A
  symmetric amplitude of the places does not vanish there. The identity and
  its antipode occur with one ray, and that joint state is not the singlet.
* The two arrangements of the rays share a frame, hence share the three
  cosines, while one arrangement is a repeated ray and the other is not.
  One ray has electron–electron cosine `1` at one place and `-1` at the
  antipode.
* Above the Bohr radius, with the stated length windows, the gravitational
  term decreases the separation and the net force increases it, and a repeated
  ray is still not the singlet.
-/

noncomputable section

namespace DstDiophantine.Gravity.SpinVersusExclusion

open RelationalPosition HeliumBody
open DstDiophantine.Logic

/-- A carrier is a place together with a spin factor. -/
structure Carrier where
  place : S3
  spin : DualSpinor

def samePlace (a b : Carrier) : Prop :=
  a.place = b.place

def sameRay (a b : Carrier) : Prop :=
  ∃ c : ℂ, b.spin = c • a.spin

/-- Spin reversal acts on the spin factor and leaves the place. -/
def spinReverse (a : Carrier) : Carrier where
  place := a.place
  spin := quatJ a.spin

theorem spinReverse_place (a : Carrier) : (spinReverse a).place = a.place := rfl

theorem spinReverse_not_sameRay {a : Carrier} (ha : a.spin ≠ 0) :
    ¬ sameRay a (spinReverse a) := by
  rintro ⟨c, hc⟩
  exact not_smul_quatJ ha c hc.symm

theorem spinReverse_spinVec (a : Carrier) :
    spinVec (spinReverse a).spin = fun k => -spinVec a.spin k :=
  spinVec_quatJ a.spin

/-- Computational spin up, the `+1` eigenvector of `σ_z`. -/
def axisUp : DualSpinor :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

theorem axisUp_ne_zero : axisUp ≠ 0 := by
  intro h
  have := congrArg (fun u : DualSpinor => u 0) h
  simp [axisUp] at this

theorem axisUp_norm : ‖axisUp‖ = 1 := by
  have hsq : ‖axisUp‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [axisUp, PiLp.single_apply, Fin.sum_univ_two]
  rw [← Real.sqrt_sq (norm_nonneg axisUp), hsq, Real.sqrt_one]

def atPlace (p : S3) (u : DualSpinor) : Carrier where
  place := p
  spin := u

def frameOf (a b : Carrier) : Frame where
  elecA := a.place
  elecB := b.place

theorem frame_spinReverse (a b : Carrier) :
    frameOf (spinReverse a) b = frameOf a b ∧
      frameOf a (spinReverse b) = frameOf a b := by
  simp [frameOf, spinReverse]

theorem not_samePlace_antipode :
    ¬ samePlace (atPlace 1 axisUp) (atPlace negOne axisUp) := by
  intro h
  exact one_ne_negOne (by simpa [atPlace, samePlace] using h)

/-- Opposite rays at one place. The joint state is the singlet, and a symmetric
amplitude of the places does not vanish. -/
theorem singlet_at_one_place :
    samePlace (atPlace 1 axisUp) (spinReverse (atPlace 1 axisUp)) ∧
      ¬ sameRay (atPlace 1 axisUp) (spinReverse (atPlace 1 axisUp)) ∧
        pairTensor (quatJ axisUp) axisUp - pairTensor axisUp (quatJ axisUp) = singlet ∧
          (fun _ : Frame => (1 : ℂ))
              (frameOf (atPlace 1 axisUp) (spinReverse (atPlace 1 axisUp))) ≠ 0 := by
  refine ⟨rfl, spinReverse_not_sameRay (a := atPlace 1 axisUp) axisUp_ne_zero, ?_, ?_⟩
  · exact quatJ_pair_eq_singlet_of_norm axisUp_norm
  · simp

/-- One ray at the identity and at its antipode is not the singlet. -/
theorem repeated_ray_at_antipodes (c : ℂ) :
    sameRay (atPlace 1 axisUp) (atPlace negOne axisUp) ∧
      ¬ samePlace (atPlace 1 axisUp) (atPlace negOne axisUp) ∧
        pairTensor axisUp axisUp ≠ c • singlet := by
  exact ⟨⟨1, by simp [atPlace]⟩, not_samePlace_antipode,
    repeated_ray_not_smul_singlet axisUp_ne_zero c⟩

theorem cosEE_one_place :
    cosEE (frameOf (atPlace 1 axisUp) (atPlace 1 axisUp)) = 1 := by
  have hrel : relative (1 : S3) (1 : S3) = 1 := (relative_eq_one_iff _ _).2 rfl
  simp [cosEE, frameOf, atPlace, ee, hrel, one_val]

theorem cosEE_antipodes :
    cosEE (frameOf (atPlace 1 axisUp) (atPlace negOne axisUp)) = -1 := by
  have hanti : antipode (1 : S3) = negOne := by
    apply S3.ext
    simp [antipode, negOne, one_val]
  have hrel : relative (1 : S3) negOne = negOne := by
    simpa [hanti] using relative_antipode (1 : S3)
  simp only [cosEE, frameOf, atPlace, ee]
  rw [hrel]
  simp [negOne]

/-- The three cosines do not record the ray. The two ray arrangements share a
frame, one is a repeated ray, and the other is not. -/
theorem cosines_miss_the_ray :
    frameOf (atPlace 1 axisUp) (atPlace 1 axisUp) =
        frameOf (atPlace 1 axisUp) (spinReverse (atPlace 1 axisUp)) ∧
      sameRay (atPlace 1 axisUp) (atPlace 1 axisUp) ∧
        ¬ sameRay (atPlace 1 axisUp) (spinReverse (atPlace 1 axisUp)) :=
  ⟨rfl, ⟨1, by simp [atPlace]⟩, spinReverse_not_sameRay (a := atPlace 1 axisUp) axisUp_ne_zero⟩

/-- One ray does not record the places. The electron–electron cosine is `1` at
one place and `-1` at the antipode. -/
theorem ray_misses_the_places :
    sameRay (atPlace 1 axisUp) (atPlace 1 axisUp) ∧
      sameRay (atPlace 1 axisUp) (atPlace negOne axisUp) ∧
        cosEE (frameOf (atPlace 1 axisUp) (atPlace 1 axisUp)) = 1 ∧
          cosEE (frameOf (atPlace 1 axisUp) (atPlace negOne axisUp)) = -1 ∧
            ¬ samePlace (atPlace 1 axisUp) (atPlace negOne axisUp) :=
  ⟨⟨1, by simp [atPlace]⟩, ⟨1, by simp [atPlace]⟩, cosEE_one_place, cosEE_antipodes,
    not_samePlace_antipode⟩

/-- Above the Bohr radius the masses attract and the net force increases the
separation, while a repeated ray is still not the singlet. -/
theorem repeated_ray_where_masses_attract {ℓE ℓG a coul r : ℝ}
    (hE0 : 0 < ℓE) (hE : ℓE < 387)
    (hG0 : 0 < ℓG) (hG : ℓG < 19 / 10)
    (ha : 52917 < a) (hc : 0 < coul) (hr : r ≠ 0) (c : ℂ) :
    pairTensor axisUp axisUp ≠ c • singlet ∧
      -(electronElectronGravToCoulomb : ℝ) * coul /
          (gammaSEqual (ℓG / (2 * a)) * r ^ 2) < 0 ∧
        0 < pairChannelForce
          ((electronElectronGravToCoulomb : ℝ) * coul) coul
          (gammaSEqual (ℓG / (2 * a))) (gammaSEqual (ℓE / (2 * a))) r := by
  have h := shell_electron_net_repels hE0 hE hG0 hG ha hc hr
  exact ⟨repeated_ray_not_smul_singlet axisUp_ne_zero c, h.2.1, h.2.2⟩

end DstDiophantine.Gravity.SpinVersusExclusion

end
