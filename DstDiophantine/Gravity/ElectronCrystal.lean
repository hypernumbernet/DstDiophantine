import DstDiophantine.Gravity.ElectronMetal
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Crystals in the signed electrostatic force

Lengths are in units of `ℓ` and forces in units of `k e²/ℓ²`, as in
`ElectronMetal`. A test charge `q` (in units of `e`) at `p` feels the force
`(-q) • pointForce Q c p` from a point charge `Q` at `c`; the electron is
`q = -1`.

## Paper boundary (do **not** claim)

No infinite lattice sum is taken: every statement counts a finite set of
sites. No cohesive energy, no lattice constant, no elastic constant of a
whole crystal, and no conductivity is derived. Ions are point charges, and
the electrons of an ion core are not counted. The length `ℓ` is not derived.

## What is proved

* The three-direction outflow `16x⁴ cosh x sin x / γ_s²` has the sign of
  `sin x`: it is positive for every phase in `(0, π)` off the first node, on
  both sides of that node, it vanishes at `π`, and it is negative on
  `(π, 2π)` wherever `γ_s ≠ 0`.
* A finite set of point charges about a site, carried into itself, charges
  included, by the rotations of a regular tetrahedron (the three-fold turn
  about a body diagonal and the half-turn about a coordinate axis), exerts
  no force at the site. Along every direction a displacement of a test
  charge changes the outward component at one rate, `-q/3` times
  `∑ Q · outflow`. With `γ_s = 1` the same rate is zero.
* Truncations of the simple cubic, body-centred cubic, and face-centred
  cubic lattices to any box and any radius are such sets.
* On the outer well `outflow(x)/x⁴` is strictly increasing. Hence a site
  whose nearest shell is unlike and whose next shell is like is pushed off
  in every direction once `N₂ Q₂ k₁² ≤ N₁ Q₁ k₂²` (`kᵢ` squared distances).
  Rock salt, caesium chloride, zincblende, and both sites of fluorite meet
  this with their nearest two shells.
* A linear map carrying a lattice into itself has an integer trace. A
  rotation, proper or improper, through `2π/n` carries a lattice of a
  three-dimensional space into itself only for `n ∈ {1, 2, 3, 4, 6}`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set
open scoped RealInnerProductSpace

/-! ### Sign of the outflow -/

theorem gammaSEqual_ne_zero_below_pi {x : ℝ} (hx0 : 0 < x) (hxπ : x < π)
    (hx1 : x ≠ resonanceRoot1) : gammaSEqual x ≠ 0 := by
  rcases lt_or_gt_of_ne hx1 with h | h
  · exact (gammaSEqual_pos_left_of_first_node ⟨hx0, h⟩).ne'
  · exact (gammaSEqual_neg_right_of_first_node ⟨h, hxπ⟩).ne

/-- Below `π` the outflow is positive on both sides of the first node. -/
theorem ionOutflow_pos_below_pi {x : ℝ} (hx0 : 0 < x) (hxπ : x < π)
    (hx1 : x ≠ resonanceRoot1) : 0 < ionOutflow x :=
  ionOutflow_pos hx0 hxπ (gammaSEqual_ne_zero_below_pi hx0 hxπ hx1)

theorem ionOutflow_pi : ionOutflow π = 0 := by
  unfold ionOutflow
  simp [sin_pi]

theorem ionOutflow_neg_of_pi_lt {x : ℝ} (hπ : π < x) (h2π : x < 2 * π)
    (hγ : gammaSEqual x ≠ 0) : ionOutflow x < 0 := by
  unfold ionOutflow
  have hs : sin x < 0 := by
    have h := sin_pos_of_pos_of_lt_pi (x := x - π) (by linarith) (by linarith)
    rw [sin_sub_pi] at h
    linarith
  have hx0 : 0 < x := by linarith [pi_pos]
  have hpos : 0 < 16 * x ^ 4 * cosh x := by positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hpos hs)
    (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hγ)))

/-! ### Sites with the rotations of a tetrahedron -/

/-- Three-fold turn about the body diagonal. -/
def cyc3 (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (t.2.1, t.2.2, t.1)

/-- Half-turn about the third axis. -/
def flip3 (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (-t.1, -t.2.1, t.2.2)

/-- A finite set of integer sites carried into itself by both turns. -/
def TetraClosed (T : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∀ t ∈ T, cyc3 t ∈ T ∧ flip3 t ∈ T

/-- Squared length of an integer site. -/
def sq3 (t : ℤ × ℤ × ℤ) : ℤ := t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2

@[simp] theorem sq3_cyc3 (t : ℤ × ℤ × ℤ) : sq3 (cyc3 t) = sq3 t := by
  unfold sq3 cyc3
  ring

@[simp] theorem sq3_flip3 (t : ℤ × ℤ × ℤ) : sq3 (flip3 t) = sq3 t := by
  unfold sq3 flip3
  ring

theorem sq3_pos {t : ℤ × ℤ × ℤ} (ht : t ≠ 0) : 0 < sq3 t := by
  unfold sq3
  rcases lt_or_eq_of_le (show 0 ≤ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 by positivity) with h | h
  · exact h
  exfalso
  apply ht
  have h1 : t.1 ^ 2 = 0 := by nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2]
  have h2 : t.2.1 ^ 2 = 0 := by nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2]
  have h3 : t.2.2 ^ 2 = 0 := by nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2]
  exact Prod.ext (pow_eq_zero_iff (by norm_num) |>.mp h1)
    (Prod.ext (pow_eq_zero_iff (by norm_num) |>.mp h2) (pow_eq_zero_iff (by norm_num) |>.mp h3))

section Tetra

variable {T : Finset (ℤ × ℤ × ℤ)}

theorem sum_cyc3 (hT : TetraClosed T) (f : ℤ × ℤ × ℤ → ℝ) :
    ∑ t ∈ T, f (cyc3 t) = ∑ t ∈ T, f t :=
  Finset.sum_nbij' cyc3 (fun t => cyc3 (cyc3 t)) (fun t ht => (hT t ht).1)
    (fun t ht => (hT _ (hT t ht).1).1) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem sum_flip3 (hT : TetraClosed T) (f : ℤ × ℤ × ℤ → ℝ) :
    ∑ t ∈ T, f (flip3 t) = ∑ t ∈ T, f t :=
  Finset.sum_nbij' flip3 flip3 (fun t ht => (hT t ht).2) (fun t ht => (hT t ht).2)
    (fun _ _ => by simp [flip3]) (fun _ _ => by simp [flip3]) (fun _ _ => rfl)

variable (β : ℤ × ℤ × ℤ → ℝ)

private theorem mom1 (hT : TetraClosed T) (hβ : ∀ t, β (flip3 t) = β t) :
    ∑ t ∈ T, β t * t.1 = 0 := by
  have h := sum_flip3 hT (fun t => β t * t.1)
  simp only [hβ] at h
  simp only [flip3, Int.cast_neg] at h
  have : ∑ t ∈ T, β t * -(t.1 : ℝ) = -∑ t ∈ T, β t * t.1 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  linarith

private theorem mom2 (hT : TetraClosed T) (hβ : ∀ t, β (flip3 t) = β t) :
    ∑ t ∈ T, β t * t.2.1 = 0 := by
  have h := sum_flip3 hT (fun t => β t * t.2.1)
  simp only [hβ] at h
  simp only [flip3, Int.cast_neg] at h
  have : ∑ t ∈ T, β t * -(t.2.1 : ℝ) = -∑ t ∈ T, β t * t.2.1 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  linarith

private theorem mom3 (hT : TetraClosed T) (hβc : ∀ t, β (cyc3 t) = β t)
    (hβ : ∀ t, β (flip3 t) = β t) : ∑ t ∈ T, β t * t.2.2 = 0 := by
  have h := sum_cyc3 hT (fun t => β t * t.2.2)
  simp only [hβc] at h
  simp only [cyc3] at h
  rw [← h]
  exact mom1 β hT hβ

private theorem cross13 (hT : TetraClosed T) (hβ : ∀ t, β (flip3 t) = β t) :
    ∑ t ∈ T, β t * (t.1 * t.2.2) = 0 := by
  have h := sum_flip3 hT (fun t => β t * (t.1 * t.2.2))
  simp only [hβ] at h
  simp only [flip3, Int.cast_neg] at h
  have : ∑ t ∈ T, β t * (-(t.1 : ℝ) * t.2.2) = -∑ t ∈ T, β t * (t.1 * t.2.2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  linarith

private theorem cross23 (hT : TetraClosed T) (hβ : ∀ t, β (flip3 t) = β t) :
    ∑ t ∈ T, β t * (t.2.1 * t.2.2) = 0 := by
  have h := sum_flip3 hT (fun t => β t * (t.2.1 * t.2.2))
  simp only [hβ] at h
  simp only [flip3, Int.cast_neg] at h
  have : ∑ t ∈ T, β t * (-(t.2.1 : ℝ) * t.2.2) =
      -∑ t ∈ T, β t * (t.2.1 * t.2.2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  linarith

private theorem cross12 (hT : TetraClosed T) (hβc : ∀ t, β (cyc3 t) = β t)
    (hβ : ∀ t, β (flip3 t) = β t) : ∑ t ∈ T, β t * (t.1 * t.2.1) = 0 := by
  have h := sum_cyc3 hT (fun t => β t * (t.1 * t.2.1))
  simp only [hβc] at h
  simp only [cyc3] at h
  rw [← h]
  exact cross23 β hT hβ

private theorem diag12 (hT : TetraClosed T) (hβc : ∀ t, β (cyc3 t) = β t) :
    ∑ t ∈ T, β t * (t.2.1 : ℝ) ^ 2 = ∑ t ∈ T, β t * (t.1 : ℝ) ^ 2 := by
  have h := sum_cyc3 hT (fun t => β t * (t.1 : ℝ) ^ 2)
  simp only [hβc] at h
  simp only [cyc3] at h
  exact h

private theorem diag23 (hT : TetraClosed T) (hβc : ∀ t, β (cyc3 t) = β t) :
    ∑ t ∈ T, β t * (t.2.2 : ℝ) ^ 2 = ∑ t ∈ T, β t * (t.2.1 : ℝ) ^ 2 := by
  have h := sum_cyc3 hT (fun t => β t * (t.2.1 : ℝ) ^ 2)
  simp only [hβc] at h
  simp only [cyc3] at h
  exact h

end Tetra

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The site `t`, scaled by `h`, in the orthonormal frame `b`. -/
noncomputable def latticeVec (b : OrthonormalBasis (Fin 3) ℝ E) (h : ℝ) (t : ℤ × ℤ × ℤ) : E :=
  (h * t.1) • b 0 + (h * t.2.1) • b 1 + (h * t.2.2) • b 2

theorem inner_latticeVec (b : OrthonormalBasis (Fin 3) ℝ E) (h : ℝ) (t : ℤ × ℤ × ℤ)
    (v : E) :
    ⟪latticeVec b h t, v⟫ =
      h * (t.1 * ⟪b 0, v⟫ + t.2.1 * ⟪b 1, v⟫ + t.2.2 * ⟪b 2, v⟫) := by
  unfold latticeVec
  simp only [inner_add_left, real_inner_smul_left]
  ring

theorem norm_sq_latticeVec (b : OrthonormalBasis (Fin 3) ℝ E) (h : ℝ) (t : ℤ × ℤ × ℤ) :
    ‖latticeVec b h t‖ ^ 2 = h ^ 2 * (sq3 t : ℝ) := by
  rw [← b.sum_sq_inner_left, Fin.sum_univ_three, inner_latticeVec, inner_latticeVec,
    inner_latticeVec]
  simp only [b.inner_eq_ite]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  unfold sq3
  push_cast
  ring

/-- Phase of the site `t` at scale `h`. -/
noncomputable def sitePhase (h : ℝ) (t : ℤ × ℤ × ℤ) : ℝ :=
  1 / (2 * (h * √(sq3 t : ℝ)))

theorem norm_latticeVec (b : OrthonormalBasis (Fin 3) ℝ E) {h : ℝ} (hh : 0 ≤ h)
    (t : ℤ × ℤ × ℤ) : ‖latticeVec b h t‖ = h * √(sq3 t : ℝ) := by
  have hs : (0 : ℝ) ≤ (sq3 t : ℝ) := by
    unfold sq3
    positivity
  have h2 : (h * √(sq3 t : ℝ)) ^ 2 = h ^ 2 * (sq3 t : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hs]
  rw [← norm_sq_latticeVec b h t] at h2
  exact ((pow_left_inj₀ (norm_nonneg _) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp
    h2.symm)

theorem vecPhase_latticeVec (b : OrthonormalBasis (Fin 3) ℝ E) {h : ℝ} (hh : 0 ≤ h)
    (t : ℤ × ℤ × ℤ) : vecPhase (latticeVec b h t) = sitePhase h t := by
  unfold vecPhase sitePhase
  rw [norm_latticeVec b hh]

private theorem parseval3' (b : OrthonormalBasis (Fin 3) ℝ E) (v : E) :
    ⟪b 0, v⟫ ^ 2 + ⟪b 1, v⟫ ^ 2 + ⟪b 2, v⟫ ^ 2 = ‖v‖ ^ 2 := by
  have h := b.sum_sq_inner_right v
  rwa [Fin.sum_univ_three] at h

variable {T : Finset (ℤ × ℤ × ℤ)}

/-- Isotropy of the second moment under the rotations of a tetrahedron. -/
theorem tetra_quad_sum (b : OrthonormalBasis (Fin 3) ℝ E) (h : ℝ) (hT : TetraClosed T)
    (β : ℤ × ℤ × ℤ → ℝ) (hβc : ∀ t, β (cyc3 t) = β t) (hβf : ∀ t, β (flip3 t) = β t)
    (v : E) :
    ∑ t ∈ T, β t * ⟪latticeVec b h t, v⟫ ^ 2 =
      (∑ t ∈ T, β t * (h ^ 2 * (sq3 t : ℝ))) / 3 * ‖v‖ ^ 2 := by
  set v1 := ⟪b 0, v⟫
  set v2 := ⟪b 1, v⟫
  set v3 := ⟪b 2, v⟫
  have hp : v1 ^ 2 + v2 ^ 2 + v3 ^ 2 = ‖v‖ ^ 2 := parseval3' b v
  have expand : ∑ t ∈ T, β t * ⟪latticeVec b h t, v⟫ ^ 2 =
      ∑ t ∈ T, (h ^ 2 * v1 ^ 2 * (β t * (t.1 : ℝ) ^ 2) +
        h ^ 2 * v2 ^ 2 * (β t * (t.2.1 : ℝ) ^ 2) +
        h ^ 2 * v3 ^ 2 * (β t * (t.2.2 : ℝ) ^ 2) +
        2 * h ^ 2 * v1 * v2 * (β t * (t.1 * t.2.1)) +
        2 * h ^ 2 * v1 * v3 * (β t * (t.1 * t.2.2)) +
        2 * h ^ 2 * v2 * v3 * (β t * (t.2.1 * t.2.2))) :=
    Finset.sum_congr rfl fun t _ => by rw [inner_latticeVec]; ring
  have expand2 : ∑ t ∈ T, β t * (h ^ 2 * (sq3 t : ℝ)) =
      ∑ t ∈ T, (h ^ 2 * (β t * (t.1 : ℝ) ^ 2) + h ^ 2 * (β t * (t.2.1 : ℝ) ^ 2) +
        h ^ 2 * (β t * (t.2.2 : ℝ) ^ 2)) :=
    Finset.sum_congr rfl fun t _ => by unfold sq3; push_cast; ring
  rw [expand, expand2]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [cross12 β hT hβc hβf, cross13 β hT hβf, cross23 β hT hβf, diag23 β hT hβc,
    diag12 β hT hβc]
  rw [← hp]
  ring

/-- The first moment vanishes under the rotations of a tetrahedron. -/
theorem tetra_lin_sum (b : OrthonormalBasis (Fin 3) ℝ E) (h : ℝ) (hT : TetraClosed T)
    (β : ℤ × ℤ × ℤ → ℝ) (hβc : ∀ t, β (cyc3 t) = β t) (hβf : ∀ t, β (flip3 t) = β t) :
    ∑ t ∈ T, β t • latticeVec b h t = 0 := by
  have e : ∀ t, β t • latticeVec b h t =
      (h * (β t * t.1)) • b 0 + (h * (β t * t.2.1)) • b 1 + (h * (β t * t.2.2)) • b 2 := by
    intro t
    unfold latticeVec
    simp only [smul_add, smul_smul]
    congr 2 <;> ring_nf
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.mul_sum]
  rw [mom1 β hT hβf, mom2 β hT hβf, mom3 β hT hβc hβf]
  simp

/-- Isotropic rate of a tetrahedrally symmetric site, per unit `‖v‖²`, for
an electron. A test charge `q` has `-q` times this rate. -/
noncomputable def siteRate (h : ℝ) (T : Finset (ℤ × ℤ × ℤ)) (Q : ℤ × ℤ × ℤ → ℝ) : ℝ :=
  (∑ t ∈ T, Q t * ionOutflow (sitePhase h t)) / 3

/-- Total force on a test charge `q` at `x` from charges `Q t` at `p - h t`. -/
noncomputable def siteForce (b : OrthonormalBasis (Fin 3) ℝ E) (h : ℝ)
    (T : Finset (ℤ × ℤ × ℤ)) (Q : ℤ × ℤ × ℤ → ℝ) (q : ℝ) (p x : E) : E :=
  ∑ t ∈ T, (-q) • pointForce (Q t) (p - latticeVec b h t) x

/-- A site carried into itself by the rotations of a tetrahedron: the force
vanishes, and along every direction the outward component changes at one
rate, `-q · siteRate`. -/
theorem tetra_site (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    (hT : TetraClosed T) (Q : ℤ × ℤ × ℤ → ℝ) (hQc : ∀ t, Q (cyc3 t) = Q t)
    (hQf : ∀ t, Q (flip3 t) = Q t) (h0 : ∀ t ∈ T, t ≠ 0)
    (hγ : ∀ t ∈ T, gammaSEqual (sitePhase h t) ≠ 0) (q : ℝ) :
    siteForce b h T Q q p p = 0 ∧
      ∀ v : E, HasDerivAt (fun s : ℝ => ⟪siteForce b h T Q q p (p + s • v), v⟫)
        (-q * siteRate h T Q * ‖v‖ ^ 2) 0 := by
  have hsub : ∀ t, p - (p - latticeVec b h t) = latticeVec b h t := fun t => sub_sub_cancel _ _
  have hphc : ∀ t, sitePhase h (cyc3 t) = sitePhase h t := fun t => by
    unfold sitePhase; rw [sq3_cyc3]
  have hphf : ∀ t, sitePhase h (flip3 t) = sitePhase h t := fun t => by
    unfold sitePhase; rw [sq3_flip3]
  refine ⟨?_, fun v => ?_⟩
  · unfold siteForce pointForce
    simp only [hsub, vecPhase_latticeVec b hh.le, smul_smul]
    have := tetra_lin_sum b h hT (fun t => -q * -(Q t * pullRate (sitePhase h t)))
      (fun t => by simp only [hQc, hphc]) (fun t => by simp only [hQf, hphf])
    exact this
  · have hne : ∀ t ∈ T, p ≠ p - latticeVec b h t := by
      intro t ht hp
      have h1 : latticeVec b h t = 0 := by
        have := congrArg (fun y => p - y) hp
        simpa [hsub] using this.symm
      have h2 := norm_sq_latticeVec b h t
      rw [h1, norm_zero] at h2
      have h3 : (0 : ℝ) < (sq3 t : ℝ) := by exact_mod_cast sq3_pos (h0 t ht)
      have : (0 : ℝ) < h ^ 2 * (sq3 t : ℝ) := by positivity
      linarith [show (0 : ℝ) ^ 2 = 0 by norm_num]
    have hγ' : ∀ t ∈ T, gammaSEqual (vecPhase (p - (p - latticeVec b h t))) ≠ 0 := by
      intro t ht
      rw [hsub, vecPhase_latticeVec b hh.le]
      exact hγ t ht
    have hd : HasDerivAt (fun s : ℝ => ⟪siteForce b h T Q q p (p + s • v), v⟫)
        (∑ t ∈ T, -q * lineStiff (Q t) (p - (p - latticeVec b h t)) v) 0 := by
      have hfun : (fun s : ℝ => ⟪siteForce b h T Q q p (p + s • v), v⟫) =
          fun s => ∑ t ∈ T, -q * ⟪pointForce (Q t) (p - latticeVec b h t) (p + s • v), v⟫ := by
        funext s
        unfold siteForce
        rw [sum_inner]
        exact Finset.sum_congr rfl fun t _ => real_inner_smul_left _ _ _
      rw [hfun]
      exact HasDerivAt.fun_sum fun t ht =>
        (hasDerivAt_pointForce_line (Q t) v (hne t ht) (hγ' t ht)).const_mul (-q)
    refine hd.congr_deriv ?_
    simp only [hsub]
    have hnorm : ∀ t ∈ T, ‖latticeVec b h t‖ = h * √(sq3 t : ℝ) := fun t _ =>
      norm_latticeVec b hh.le t
    have hterm : ∀ t ∈ T, -q * lineStiff (Q t) (latticeVec b h t) v =
        -q * (-(Q t * pullRate (sitePhase h t)) * ‖v‖ ^ 2) +
          (-q * (Q t * pullRateDeriv (sitePhase h t) / (2 * (h * √(sq3 t : ℝ)) ^ 3))) *
            ⟪latticeVec b h t, v⟫ ^ 2 := by
      intro t ht
      unfold lineStiff
      rw [vecPhase_latticeVec b hh.le, hnorm t ht]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    rw [tetra_quad_sum b h hT _ (fun t => by simp only [hQc, hphc, sq3_cyc3])
      (fun t => by simp only [hQf, hphf, sq3_flip3]) v]
    have hrad : ∀ t ∈ T,
        (-q * (Q t * pullRateDeriv (sitePhase h t) / (2 * (h * √(sq3 t : ℝ)) ^ 3))) *
          (h ^ 2 * (sq3 t : ℝ)) =
        -q * (Q t * (sitePhase h t * pullRateDeriv (sitePhase h t))) := by
      intro t ht
      have hs : (0 : ℝ) < (sq3 t : ℝ) := by exact_mod_cast sq3_pos (h0 t ht)
      have hsq : √(sq3 t : ℝ) ^ 2 = (sq3 t : ℝ) := Real.sq_sqrt hs.le
      have hr : 0 < √(sq3 t : ℝ) := Real.sqrt_pos.mpr hs
      unfold sitePhase
      set r := √(sq3 t : ℝ)
      rw [← hsq]
      field_simp
    rw [Finset.sum_congr rfl hrad]
    unfold siteRate
    have hout : ∀ t ∈ T, Q t * ionOutflow (sitePhase h t) =
        Q t * (sitePhase h t * pullRateDeriv (sitePhase h t)) -
          3 * (Q t * pullRate (sitePhase h t)) := by
      intro t ht
      rw [← pullRate_outflow (hγ t ht)]
      ring
    rw [Finset.sum_congr rfl hout, Finset.sum_sub_distrib]
    simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

theorem ne_zero_of_sitePhase_pos {h : ℝ} {t : ℤ × ℤ × ℤ} (ht : 0 < sitePhase h t) :
    t ≠ 0 := by
  rintro rfl
  simp [sitePhase, sq3] at ht

theorem siteRate_pos {h : ℝ} {Q : ℤ × ℤ × ℤ → ℝ} (hQ : ∀ t ∈ T, 0 ≤ Q t)
    (hne : ∃ t ∈ T, 0 < Q t)
    (hx : ∀ t ∈ T, sitePhase h t ∈ Ioo 0 π ∧ sitePhase h t ≠ resonanceRoot1) :
    0 < siteRate h T Q := by
  unfold siteRate
  have hS : ∀ t ∈ T, 0 < ionOutflow (sitePhase h t) := fun t ht =>
    ionOutflow_pos_below_pi (hx t ht).1.1 (hx t ht).1.2 (hx t ht).2
  obtain ⟨t0, ht0, hq0⟩ := hne
  have hsum : 0 < ∑ t ∈ T, Q t * ionOutflow (sitePhase h t) :=
    Finset.sum_pos' (fun t ht => mul_nonneg (hQ t ht) (hS t ht).le)
      ⟨t0, ht0, mul_pos hq0 (hS t0 ht0)⟩
  positivity

/-- Like charges about a tetrahedrally symmetric site, every separation with
phase below `π` and off the first node: a positive test charge is held, at
one rate in every direction. -/
theorem tetra_site_like_held (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    (hT : TetraClosed T) (Q : ℤ × ℤ × ℤ → ℝ) (hQc : ∀ t, Q (cyc3 t) = Q t)
    (hQf : ∀ t, Q (flip3 t) = Q t)
    (hx : ∀ t ∈ T, sitePhase h t ∈ Ioo 0 π ∧ sitePhase h t ≠ resonanceRoot1)
    (hQ : ∀ t ∈ T, 0 ≤ Q t) (hne : ∃ t ∈ T, 0 < Q t) {q : ℝ} (hq : 0 < q) :
    siteForce b h T Q q p p = 0 ∧ -q * siteRate h T Q < 0 ∧
      ∀ v : E, HasDerivAt (fun s : ℝ => ⟪siteForce b h T Q q p (p + s • v), v⟫)
        (-q * siteRate h T Q * ‖v‖ ^ 2) 0 := by
  have hγ : ∀ t ∈ T, gammaSEqual (sitePhase h t) ≠ 0 := fun t ht =>
    gammaSEqual_ne_zero_below_pi (hx t ht).1.1 (hx t ht).1.2 (hx t ht).2
  have h0 : ∀ t ∈ T, t ≠ 0 := fun t ht => ne_zero_of_sitePhase_pos (hx t ht).1.1
  obtain ⟨hF, hD⟩ := tetra_site b p hh hT Q hQc hQf h0 hγ q
  have hr := siteRate_pos hQ hne hx
  exact ⟨hF, by nlinarith, hD⟩

/-- The same site pushes an electron off in every direction. -/
theorem tetra_site_electron_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ}
    (hh : 0 < h) (hT : TetraClosed T) (Q : ℤ × ℤ × ℤ → ℝ) (hQc : ∀ t, Q (cyc3 t) = Q t)
    (hQf : ∀ t, Q (flip3 t) = Q t)
    (hx : ∀ t ∈ T, sitePhase h t ∈ Ioo 0 π ∧ sitePhase h t ≠ resonanceRoot1)
    (hQ : ∀ t ∈ T, 0 ≤ Q t) (hne : ∃ t ∈ T, 0 < Q t) :
    siteForce b h T Q (-1) p p = 0 ∧ 0 < -(-1) * siteRate h T Q ∧
      ∀ v : E, HasDerivAt (fun s : ℝ => ⟪siteForce b h T Q (-1) p (p + s • v), v⟫)
        (-(-1) * siteRate h T Q * ‖v‖ ^ 2) 0 := by
  have hγ : ∀ t ∈ T, gammaSEqual (sitePhase h t) ≠ 0 := fun t ht =>
    gammaSEqual_ne_zero_below_pi (hx t ht).1.1 (hx t ht).1.2 (hx t ht).2
  have h0 : ∀ t ∈ T, t ≠ 0 := fun t ht => ne_zero_of_sitePhase_pos (hx t ht).1.1
  obtain ⟨hF, hD⟩ := tetra_site b p hh hT Q hQc hQf h0 hγ (-1)
  have hr := siteRate_pos hQ hne hx
  exact ⟨hF, by linarith, hD⟩

/-- Line derivative of the Coulomb force (`γ_s = 1`) of one point charge. -/
noncomputable def coulombLineStiff (Q : ℝ) (w v : E) : ℝ :=
  -(Q * (8 * vecPhase w ^ 3 * ‖v‖ ^ 2 -
    24 * vecPhase w ^ 2 * ⟪w, v⟫ ^ 2 / (2 * ‖w‖ ^ 3)))

/-- Under the Coulomb law the rate of every tetrahedrally symmetric site is zero. -/
theorem coulomb_tetra_site_zero (b : OrthonormalBasis (Fin 3) ℝ E) {h : ℝ} (hh : 0 < h)
    (hT : TetraClosed T) (Q : ℤ × ℤ × ℤ → ℝ) (hQc : ∀ t, Q (cyc3 t) = Q t)
    (hQf : ∀ t, Q (flip3 t) = Q t) (h0 : ∀ t ∈ T, t ≠ 0) (v : E) :
    ∑ t ∈ T, coulombLineStiff (Q t) (latticeVec b h t) v = 0 := by
  have hphc : ∀ t, sitePhase h (cyc3 t) = sitePhase h t := fun t => by
    unfold sitePhase; rw [sq3_cyc3]
  have hphf : ∀ t, sitePhase h (flip3 t) = sitePhase h t := fun t => by
    unfold sitePhase; rw [sq3_flip3]
  have hterm : ∀ t ∈ T, coulombLineStiff (Q t) (latticeVec b h t) v =
      -(Q t * (8 * sitePhase h t ^ 3)) * ‖v‖ ^ 2 +
        (Q t * (24 * sitePhase h t ^ 2) / (2 * (h * √(sq3 t : ℝ)) ^ 3)) *
          ⟪latticeVec b h t, v⟫ ^ 2 := by
    intro t _
    unfold coulombLineStiff
    rw [vecPhase_latticeVec b hh.le, norm_latticeVec b hh.le]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    tetra_quad_sum b h hT _ (fun t => by simp only [hQc, hphc, sq3_cyc3])
      (fun t => by simp only [hQf, hphf, sq3_flip3]) v]
  have hrad : ∀ t ∈ T,
      Q t * (24 * sitePhase h t ^ 2) / (2 * (h * √(sq3 t : ℝ)) ^ 3) * (h ^ 2 * (sq3 t : ℝ)) =
        3 * (Q t * (8 * sitePhase h t ^ 3)) := by
    intro t ht
    have hs : (0 : ℝ) < (sq3 t : ℝ) := by exact_mod_cast sq3_pos (h0 t ht)
    have hsq : √(sq3 t : ℝ) ^ 2 = (sq3 t : ℝ) := Real.sq_sqrt hs.le
    have hr : 0 < √(sq3 t : ℝ) := Real.sqrt_pos.mpr hs
    unfold sitePhase
    set r := √(sq3 t : ℝ)
    rw [← hsq]
    field_simp
    ring
  rw [Finset.sum_congr rfl hrad, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_neg_distrib]
  ring

end Space

/-! ### Cubic lattices to any distance -/

/-- Sites `t ≠ 0` of a box of half-width `N` with `P t` and `|t|² ≤ R`. -/
noncomputable def cubicBox (P : ℤ × ℤ × ℤ → Prop) [DecidablePred P] (N : ℕ) (R : ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-(N : ℤ)) N) ×ˢ (Finset.Icc (-(N : ℤ)) N) ×ˢ (Finset.Icc (-(N : ℤ)) N)).filter
    (fun t => P t ∧ t ≠ 0 ∧ sq3 t ≤ R)

theorem cyc3_ne_zero {t : ℤ × ℤ × ℤ} (ht : t ≠ 0) : cyc3 t ≠ 0 := by
  intro h
  apply ht
  simp only [cyc3, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h ⊢
  exact ⟨h.2.2, h.1, h.2.1⟩

theorem flip3_ne_zero {t : ℤ × ℤ × ℤ} (ht : t ≠ 0) : flip3 t ≠ 0 := by
  intro h
  apply ht
  simp only [flip3, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h ⊢
  exact h

theorem cubicBox_closed (P : ℤ × ℤ × ℤ → Prop) [DecidablePred P]
    (hPc : ∀ t, P t → P (cyc3 t)) (hPf : ∀ t, P t → P (flip3 t)) (N : ℕ) (R : ℤ) :
    TetraClosed (cubicBox P N R) := by
  intro t ht
  simp only [cubicBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
  obtain ⟨⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩, hP, h0, hR⟩ := ht
  refine ⟨⟨?_, hPc t hP, cyc3_ne_zero h0, by rw [sq3_cyc3]; exact hR⟩,
    ⟨?_, hPf t hP, flip3_ne_zero h0, by rw [sq3_flip3]; exact hR⟩⟩
  · simp only [cyc3]
    exact ⟨⟨b1, b2⟩, ⟨c1, c2⟩, ⟨a1, a2⟩⟩
  · simp only [flip3]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨c1, c2⟩⟩

/-- Body-centred cubic sites in half-edge units: all coordinates of one parity. -/
def bccSite (t : ℤ × ℤ × ℤ) : Prop := t.1 % 2 = t.2.1 % 2 ∧ t.2.1 % 2 = t.2.2 % 2

/-- Face-centred cubic sites in half-edge units: even coordinate sum. -/
def fccSite (t : ℤ × ℤ × ℤ) : Prop := (t.1 + t.2.1 + t.2.2) % 2 = 0

instance : DecidablePred bccSite := fun t => by unfold bccSite; infer_instance

instance : DecidablePred fccSite := fun t => by unfold fccSite; infer_instance

theorem sc_closed (N : ℕ) (R : ℤ) : TetraClosed (cubicBox (fun _ => True) N R) :=
  cubicBox_closed _ (fun _ _ => trivial) (fun _ _ => trivial) N R

theorem bcc_closed (N : ℕ) (R : ℤ) : TetraClosed (cubicBox bccSite N R) :=
  cubicBox_closed _ (fun t h => by simp only [bccSite, cyc3] at *; omega)
    (fun t h => by simp only [bccSite, flip3] at *; omega) N R

theorem fcc_closed (N : ℕ) (R : ℤ) : TetraClosed (cubicBox fccSite N R) :=
  cubicBox_closed _ (fun t h => by simp only [fccSite, cyc3] at *; omega)
    (fun t h => by simp only [fccSite, flip3] at *; omega) N R

/-! ### Unlike nearest shells -/

/-- On the outer well the outflow falls at least as the fourth power of the
phase: `outflow(y) x⁴ < outflow(x) y⁴` for `0 < y < x < x₁`. -/
theorem ionOutflow_fourth {x y : ℝ} (hy0 : 0 < y) (hyx : y < x) (hx1 : x < resonanceRoot1) :
    ionOutflow y * x ^ 4 < ionOutflow x * y ^ 4 := by
  have hx0 : 0 < x := lt_trans hy0 hyx
  have hx' : x ∈ Ioo 0 resonanceRoot1 := ⟨hx0, hx1⟩
  have hy' : y ∈ Ioo 0 resonanceRoot1 := ⟨hy0, lt_trans hyx hx1⟩
  have hxl : x < 1 := lt_trans hx1 resonanceRoot1_bounds.2
  have hγx := gammaSEqual_pos_left_of_first_node hx'
  have hγy := gammaSEqual_pos_left_of_first_node hy'
  have hγlt : gammaSEqual x < gammaSEqual y := by
    have hxI : x ∈ Icc (0 : ℝ) π := ⟨hx0.le, by linarith [pi_gt_three]⟩
    have hyI : y ∈ Icc (0 : ℝ) π := ⟨hy0.le, by linarith [pi_gt_three]⟩
    exact strictAntiOn_gammaSEqual_even 0 (by simpa using hyI) (by simpa using hxI) hyx
  have hsin : sin y < sin x :=
    sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) (by linarith [pi_gt_three]) hyx
  have hsy : 0 < sin y := sin_pos_of_pos_of_lt_pi hy0 (by linarith [pi_gt_three])
  have hcosh : cosh y < cosh x := by
    rw [cosh_lt_cosh, abs_of_pos hy0, abs_of_pos hx0]
    exact hyx
  have hcy := cosh_pos y
  have hnum : cosh y * sin y < cosh x * sin x := mul_lt_mul'' hcosh hsin hcy.le hsy.le
  have hden : gammaSEqual x ^ 2 < gammaSEqual y ^ 2 := by nlinarith
  have hA : cosh y * sin y / gammaSEqual y ^ 2 < cosh x * sin x / gammaSEqual x ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hny : 0 < cosh y * sin y := by positivity
    calc cosh y * sin y * gammaSEqual x ^ 2 < cosh y * sin y * gammaSEqual y ^ 2 :=
          mul_lt_mul_of_pos_left hden hny
      _ < cosh x * sin x * gammaSEqual y ^ 2 :=
          mul_lt_mul_of_pos_right hnum (by positivity)
  have ey : ionOutflow y = 16 * y ^ 4 * (cosh y * sin y / gammaSEqual y ^ 2) := by
    unfold ionOutflow; ring
  have ex : ionOutflow x = 16 * x ^ 4 * (cosh x * sin x / gammaSEqual x ^ 2) := by
    unfold ionOutflow; ring
  rw [ey, ex]
  have hk : 0 < 16 * x ^ 4 * y ^ 4 := by positivity
  nlinarith

/-- Two shells at squared distances `k₁ < k₂` (scale `h`), the nearer in the
outer well: `outflow₂ · k₂² < outflow₁ · k₁²`. -/
theorem shell_outflow_compare {h k₁ k₂ : ℝ} (hh : 0 < h) (hk₁ : 0 < k₁) (hk : k₁ < k₂)
    (hx : 1 / (2 * (h * √k₁)) < resonanceRoot1) :
    ionOutflow (1 / (2 * (h * √k₂))) * k₂ ^ 2 < ionOutflow (1 / (2 * (h * √k₁))) * k₁ ^ 2 := by
  have hk₂ : 0 < k₂ := lt_trans hk₁ hk
  have hr1 : 0 < √k₁ := Real.sqrt_pos.mpr hk₁
  have hr12 : √k₁ < √k₂ := Real.sqrt_lt_sqrt hk₁.le hk
  have hr2 : 0 < √k₂ := lt_trans hr1 hr12
  have hs1 : √k₁ ^ 2 = k₁ := Real.sq_sqrt hk₁.le
  have hs2 : √k₂ ^ 2 = k₂ := Real.sq_sqrt hk₂.le
  set r1 := √k₁
  set r2 := √k₂
  have hy0 : 0 < 1 / (2 * (h * r2)) := by positivity
  have hyx : 1 / (2 * (h * r2)) < 1 / (2 * (h * r1)) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  have h4 := ionOutflow_fourth hy0 hyx hx
  set S1 := ionOutflow (1 / (2 * (h * r1)))
  set S2 := ionOutflow (1 / (2 * (h * r2)))
  have e1 : (1 / (2 * (h * r1))) ^ 4 = 1 / (16 * h ^ 4 * k₁ ^ 2) := by
    rw [← hs1]; field_simp; ring
  have e2 : (1 / (2 * (h * r2))) ^ 4 = 1 / (16 * h ^ 4 * k₂ ^ 2) := by
    rw [← hs2]; field_simp; ring
  rw [e1, e2] at h4
  have hc : 0 < 16 * h ^ 4 * k₁ ^ 2 * k₂ ^ 2 := by positivity
  have h5 := mul_lt_mul_of_pos_right h4 hc
  have l : S2 * (1 / (16 * h ^ 4 * k₁ ^ 2)) * (16 * h ^ 4 * k₁ ^ 2 * k₂ ^ 2) = S2 * k₂ ^ 2 := by
    field_simp
  have r : S1 * (1 / (16 * h ^ 4 * k₂ ^ 2)) * (16 * h ^ 4 * k₁ ^ 2 * k₂ ^ 2) = S1 * k₁ ^ 2 := by
    field_simp
  rw [l, r] at h5
  exact h5

section Ionic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {T : Finset (ℤ × ℤ × ℤ)}

/-- Charges `-Q₁` on the shell `|t|² = k₁` and `Q₂` elsewhere. -/
noncomputable def shellCharge (k₁ : ℤ) (Q₁ Q₂ : ℝ) (t : ℤ × ℤ × ℤ) : ℝ :=
  if sq3 t = k₁ then -Q₁ else Q₂

/-- A tetrahedrally symmetric site with two shells, the nearer unlike and in
the outer well: when `N₂ Q₂ k₁² ≤ N₁ Q₁ k₂²` a positive test charge is pushed
off in every direction. -/
theorem two_shell_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    (hT : TetraClosed T) {k₁ k₂ : ℤ} (hk₁ : 0 < k₁) (hk : k₁ < k₂)
    (hmem : ∀ t ∈ T, sq3 t = k₁ ∨ sq3 t = k₂) {N₁ N₂ : ℕ}
    (hN₁ : (T.filter (fun t => sq3 t = k₁)).card = N₁)
    (hN₂ : (T.filter (fun t => sq3 t = k₂)).card = N₂) (hN₁0 : 0 < N₁)
    {Q₁ Q₂ q : ℝ} (hQ₁ : 0 < Q₁) (_hQ₂ : 0 ≤ Q₂) (hq : 0 < q)
    (hx : 1 / (2 * (h * √(k₁ : ℝ))) < resonanceRoot1)
    (hcond : (N₂ : ℝ) * Q₂ * (k₁ : ℝ) ^ 2 ≤ N₁ * Q₁ * (k₂ : ℝ) ^ 2) :
    siteForce b h T (shellCharge k₁ Q₁ Q₂) q p p = 0 ∧
      0 < -q * siteRate h T (shellCharge k₁ Q₁ Q₂) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ => ⟪siteForce b h T (shellCharge k₁ Q₁ Q₂) q p (p + s • v), v⟫)
        (-q * siteRate h T (shellCharge k₁ Q₁ Q₂) * ‖v‖ ^ 2) 0 := by
  have hk₁r : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hkr : (k₁ : ℝ) < k₂ := by exact_mod_cast hk
  have hk₂r : (0 : ℝ) < k₂ := lt_trans hk₁r hkr
  set x₁ := 1 / (2 * (h * √(k₁ : ℝ)))
  set x₂ := 1 / (2 * (h * √(k₂ : ℝ)))
  have hx₁0 : 0 < x₁ := by have := Real.sqrt_pos.mpr hk₁r; positivity
  have hx₂0 : 0 < x₂ := by have := Real.sqrt_pos.mpr hk₂r; positivity
  have hx₂1 : x₂ < x₁ := by
    apply one_div_lt_one_div_of_lt (by have := Real.sqrt_pos.mpr hk₁r; positivity)
    have := Real.sqrt_lt_sqrt hk₁r.le hkr
    nlinarith
  have hphase : ∀ t ∈ T, sitePhase h t = if sq3 t = k₁ then x₁ else x₂ := by
    intro t ht
    unfold sitePhase
    rcases hmem t ht with e | e
    · simp [e, x₁]
    · have hne' : k₂ ≠ k₁ := hk.ne'
      simp [e, hne', x₂]
  have hout : ∀ t ∈ T, sitePhase h t ∈ Ioo 0 resonanceRoot1 := by
    intro t ht
    rw [hphase t ht]
    split_ifs
    · exact ⟨hx₁0, hx⟩
    · exact ⟨hx₂0, lt_trans hx₂1 hx⟩
  have hγ : ∀ t ∈ T, gammaSEqual (sitePhase h t) ≠ 0 := fun t ht =>
    (gammaSEqual_pos_left_of_first_node (hout t ht)).ne'
  have h0 : ∀ t ∈ T, t ≠ 0 := fun t ht => ne_zero_of_sitePhase_pos (hout t ht).1
  have hQc : ∀ t, shellCharge k₁ Q₁ Q₂ (cyc3 t) = shellCharge k₁ Q₁ Q₂ t := fun t => by
    unfold shellCharge; rw [sq3_cyc3]
  have hQf : ∀ t, shellCharge k₁ Q₁ Q₂ (flip3 t) = shellCharge k₁ Q₁ Q₂ t := fun t => by
    unfold shellCharge; rw [sq3_flip3]
  obtain ⟨hF, hD⟩ := tetra_site b p hh hT _ hQc hQf h0 hγ q
  refine ⟨hF, ?_, hD⟩
  have hsum : ∑ t ∈ T, shellCharge k₁ Q₁ Q₂ t * ionOutflow (sitePhase h t) =
      N₁ * (-Q₁ * ionOutflow x₁) + N₂ * (Q₂ * ionOutflow x₂) := by
    rw [← Finset.sum_filter_add_sum_filter_not T (fun t => sq3 t = k₁)]
    have hnot : T.filter (fun t => ¬ sq3 t = k₁) = T.filter (fun t => sq3 t = k₂) := by
      apply Finset.filter_congr
      intro t ht
      rcases hmem t ht with e | e
      · constructor
        · intro hn; exact absurd e hn
        · intro e2; omega
      · constructor
        · intro _; exact e
        · intro _; omega
    rw [hnot]
    have s1 : ∑ t ∈ T.filter (fun t => sq3 t = k₁),
        shellCharge k₁ Q₁ Q₂ t * ionOutflow (sitePhase h t) =
        ∑ _t ∈ T.filter (fun t => sq3 t = k₁), -Q₁ * ionOutflow x₁ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_filter] at ht
      rw [hphase t ht.1]
      simp [shellCharge, ht.2]
    have s2 : ∑ t ∈ T.filter (fun t => sq3 t = k₂),
        shellCharge k₁ Q₁ Q₂ t * ionOutflow (sitePhase h t) =
        ∑ _t ∈ T.filter (fun t => sq3 t = k₂), Q₂ * ionOutflow x₂ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_filter] at ht
      have hne : sq3 t ≠ k₁ := by omega
      rw [hphase t ht.1]
      simp [shellCharge, hne]
    rw [s1, s2, Finset.sum_const, Finset.sum_const, hN₁, hN₂, nsmul_eq_mul, nsmul_eq_mul]
  unfold siteRate
  rw [hsum]
  have hS₂ : 0 < ionOutflow x₂ := ionOutflow_pos_outer ⟨hx₂0, lt_trans hx₂1 hx⟩
  have hcmp := shell_outflow_compare hh hk₁r hkr hx
  have hN₁r : (0 : ℝ) < N₁ := by exact_mod_cast hN₁0
  have hA : (N₂ : ℝ) * Q₂ * ionOutflow x₂ * (k₁ : ℝ) ^ 2 ≤
      N₁ * Q₁ * ((k₂ : ℝ) ^ 2 * ionOutflow x₂) := by
    nlinarith [mul_le_mul_of_nonneg_right hcond hS₂.le]
  have hB : (N₁ : ℝ) * Q₁ * (ionOutflow x₂ * (k₂ : ℝ) ^ 2) <
      N₁ * Q₁ * (ionOutflow x₁ * (k₁ : ℝ) ^ 2) :=
    mul_lt_mul_of_pos_left hcmp (by positivity)
  have hC : (N₂ : ℝ) * Q₂ * ionOutflow x₂ < N₁ * Q₁ * ionOutflow x₁ := by
    have hk2 : (0 : ℝ) < (k₁ : ℝ) ^ 2 := by positivity
    nlinarith
  have : (N₁ : ℝ) * (-Q₁ * ionOutflow x₁) + N₂ * (Q₂ * ionOutflow x₂) < 0 := by nlinarith
  have hq3 : 0 < q / 3 := by positivity
  nlinarith

end Ionic

/-! ### The nearest two shells of four ionic arrangements -/

/-- Zincblende, in units of a quarter of the cube edge: the face-centred
sites of even coordinate sum divisible by four, and one tetrahedron of the
odd sites. -/
def zincblendeSite (t : ℤ × ℤ × ℤ) : Prop :=
  (t.1 % 2 = 0 ∧ t.2.1 % 2 = 0 ∧ t.2.2 % 2 = 0 ∧ (t.1 + t.2.1 + t.2.2) % 4 = 0) ∨
    (t.1 % 2 = 1 ∧ t.2.1 % 2 = 1 ∧ t.2.2 % 2 = 1 ∧ (t.1 + t.2.1 + t.2.2) % 4 = 3)

instance : DecidablePred zincblendeSite := fun t => by unfold zincblendeSite; infer_instance

/-- Fluorite, seen from a cation: the same face-centred sites, and every
odd site. -/
def fluoriteCationSite (t : ℤ × ℤ × ℤ) : Prop :=
  (t.1 % 2 = 0 ∧ t.2.1 % 2 = 0 ∧ t.2.2 % 2 = 0 ∧ (t.1 + t.2.1 + t.2.2) % 4 = 0) ∨
    (t.1 % 2 = 1 ∧ t.2.1 % 2 = 1 ∧ t.2.2 % 2 = 1)

instance : DecidablePred fluoriteCationSite := fun t => by
  unfold fluoriteCationSite; infer_instance

/-- Fluorite, seen from an anion: every even site, and the odd sites whose
coordinate sum is congruent to one modulo four. -/
def fluoriteAnionSite (t : ℤ × ℤ × ℤ) : Prop :=
  (t.1 % 2 = 1 ∧ t.2.1 % 2 = 1 ∧ t.2.2 % 2 = 1 ∧ (t.1 + t.2.1 + t.2.2) % 4 = 1) ∨
    (t.1 % 2 = 0 ∧ t.2.1 % 2 = 0 ∧ t.2.2 % 2 = 0)

instance : DecidablePred fluoriteAnionSite := fun t => by
  unfold fluoriteAnionSite; infer_instance

theorem zincblende_closed (N : ℕ) (R : ℤ) : TetraClosed (cubicBox zincblendeSite N R) :=
  cubicBox_closed _ (fun t h => by simp only [zincblendeSite, cyc3] at *; omega)
    (fun t h => by simp only [zincblendeSite, flip3] at *; omega) N R

theorem fluoriteCation_closed (N : ℕ) (R : ℤ) :
    TetraClosed (cubicBox fluoriteCationSite N R) :=
  cubicBox_closed _ (fun t h => by simp only [fluoriteCationSite, cyc3] at *; omega)
    (fun t h => by simp only [fluoriteCationSite, flip3] at *; omega) N R

theorem fluoriteAnion_closed (N : ℕ) (R : ℤ) :
    TetraClosed (cubicBox fluoriteAnionSite N R) :=
  cubicBox_closed _ (fun t h => by simp only [fluoriteAnionSite, cyc3] at *; omega)
    (fun t h => by simp only [fluoriteAnionSite, flip3] at *; omega) N R

noncomputable def rockSaltShells : Finset (ℤ × ℤ × ℤ) :=
  cubicBox (fun _ => True) 1 2

noncomputable def caesiumChlorideShells : Finset (ℤ × ℤ × ℤ) :=
  cubicBox bccSite 2 4

noncomputable def zincblendeShells : Finset (ℤ × ℤ × ℤ) :=
  cubicBox zincblendeSite 2 8

noncomputable def fluoriteCationShells : Finset (ℤ × ℤ × ℤ) :=
  cubicBox fluoriteCationSite 2 8

noncomputable def fluoriteAnionShells : Finset (ℤ × ℤ × ℤ) :=
  cubicBox fluoriteAnionSite 2 4

theorem rockSalt_shells :
    (∀ t ∈ rockSaltShells, sq3 t = 1 ∨ sq3 t = 2) ∧
      (rockSaltShells.filter (fun t => sq3 t = 1)).card = 6 ∧
      (rockSaltShells.filter (fun t => sq3 t = 2)).card = 12 := by
  decide

theorem caesiumChloride_shells :
    (∀ t ∈ caesiumChlorideShells, sq3 t = 3 ∨ sq3 t = 4) ∧
      (caesiumChlorideShells.filter (fun t => sq3 t = 3)).card = 8 ∧
      (caesiumChlorideShells.filter (fun t => sq3 t = 4)).card = 6 := by
  decide

theorem zincblende_shells :
    (∀ t ∈ zincblendeShells, sq3 t = 3 ∨ sq3 t = 8) ∧
      (zincblendeShells.filter (fun t => sq3 t = 3)).card = 4 ∧
      (zincblendeShells.filter (fun t => sq3 t = 8)).card = 12 := by
  decide

theorem fluoriteCation_shells :
    (∀ t ∈ fluoriteCationShells, sq3 t = 3 ∨ sq3 t = 8) ∧
      (fluoriteCationShells.filter (fun t => sq3 t = 3)).card = 8 ∧
      (fluoriteCationShells.filter (fun t => sq3 t = 8)).card = 12 := by
  decide

theorem fluoriteAnion_shells :
    (∀ t ∈ fluoriteAnionShells, sq3 t = 3 ∨ sq3 t = 4) ∧
      (fluoriteAnionShells.filter (fun t => sq3 t = 3)).card = 4 ∧
      (fluoriteAnionShells.filter (fun t => sq3 t = 4)).card = 6 := by
  decide

section Ionic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem sqrt_one_phase {h : ℝ} :
    1 / (2 * (h * √(1 : ℝ))) = 1 / (2 * h) := by
  simp [Real.sqrt_one]

/-- Rock salt, nearest two shells, the nearer unlike and in the outer well.
Six unlike neighbours at squared distance `1` and twelve like neighbours at
squared distance `2`: a positive test charge is pushed off in every direction
once `Q₂ ≤ 2 Q₁`. -/
theorem rockSalt_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    {Q₁ Q₂ q : ℝ} (hQ₁ : 0 < Q₁) (hQ₂ : 0 ≤ Q₂) (hq : 0 < q)
    (hx : 1 / (2 * h) < resonanceRoot1) (hcond : Q₂ ≤ 2 * Q₁) :
    siteForce b h rockSaltShells (shellCharge 1 Q₁ Q₂) q p p = 0 ∧
      0 < -q * siteRate h rockSaltShells (shellCharge 1 Q₁ Q₂) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ => ⟪siteForce b h rockSaltShells (shellCharge 1 Q₁ Q₂) q p (p + s • v), v⟫)
        (-q * siteRate h rockSaltShells (shellCharge 1 Q₁ Q₂) * ‖v‖ ^ 2) 0 := by
  have hs := rockSalt_shells
  exact two_shell_pushed (k₁ := 1) (k₂ := 2) (N₁ := 6) (N₂ := 12) b p hh (sc_closed 1 2)
    (by norm_num) (by norm_num) hs.1 hs.2.1 hs.2.2 (by norm_num) hQ₁ hQ₂ hq
    (by simpa [sqrt_one_phase] using hx) (by push_cast; nlinarith)

/-- Caesium chloride, nearest two shells. Eight unlike neighbours at squared
distance `3` and six like neighbours at squared distance `4`: a positive test
charge is pushed off once `27 Q₂ ≤ 64 Q₁`. -/
theorem caesiumChloride_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    {Q₁ Q₂ q : ℝ} (hQ₁ : 0 < Q₁) (hQ₂ : 0 ≤ Q₂) (hq : 0 < q)
    (hx : 1 / (2 * (h * √(3 : ℝ))) < resonanceRoot1) (hcond : 27 * Q₂ ≤ 64 * Q₁) :
    siteForce b h caesiumChlorideShells (shellCharge 3 Q₁ Q₂) q p p = 0 ∧
      0 < -q * siteRate h caesiumChlorideShells (shellCharge 3 Q₁ Q₂) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ =>
          ⟪siteForce b h caesiumChlorideShells (shellCharge 3 Q₁ Q₂) q p (p + s • v), v⟫)
        (-q * siteRate h caesiumChlorideShells (shellCharge 3 Q₁ Q₂) * ‖v‖ ^ 2) 0 := by
  have hs := caesiumChloride_shells
  exact two_shell_pushed (k₁ := 3) (k₂ := 4) (N₁ := 8) (N₂ := 6) b p hh (bcc_closed 2 4)
    (by norm_num) (by norm_num) hs.1 hs.2.1 hs.2.2 (by norm_num) hQ₁ hQ₂ hq hx
    (by push_cast; nlinarith)

/-- Zincblende, nearest two shells. Four unlike neighbours at squared distance
`3` and twelve like neighbours at squared distance `8`: a positive test charge
is pushed off once `27 Q₂ ≤ 64 Q₁`. -/
theorem zincblende_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    {Q₁ Q₂ q : ℝ} (hQ₁ : 0 < Q₁) (hQ₂ : 0 ≤ Q₂) (hq : 0 < q)
    (hx : 1 / (2 * (h * √(3 : ℝ))) < resonanceRoot1) (hcond : 27 * Q₂ ≤ 64 * Q₁) :
    siteForce b h zincblendeShells (shellCharge 3 Q₁ Q₂) q p p = 0 ∧
      0 < -q * siteRate h zincblendeShells (shellCharge 3 Q₁ Q₂) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ =>
          ⟪siteForce b h zincblendeShells (shellCharge 3 Q₁ Q₂) q p (p + s • v), v⟫)
        (-q * siteRate h zincblendeShells (shellCharge 3 Q₁ Q₂) * ‖v‖ ^ 2) 0 := by
  have hs := zincblende_shells
  exact two_shell_pushed (k₁ := 3) (k₂ := 8) (N₁ := 4) (N₂ := 12) b p hh
    (zincblende_closed 2 8) (by norm_num) (by norm_num) hs.1 hs.2.1 hs.2.2
    (by norm_num) hQ₁ hQ₂ hq hx (by push_cast; nlinarith)

/-- Fluorite, seen from a cation. Eight unlike neighbours at squared distance
`3` and twelve like neighbours at squared distance `8`: a positive test charge
is pushed off once `27 Q₂ ≤ 128 Q₁`. -/
theorem fluoriteCation_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    {Q₁ Q₂ q : ℝ} (hQ₁ : 0 < Q₁) (hQ₂ : 0 ≤ Q₂) (hq : 0 < q)
    (hx : 1 / (2 * (h * √(3 : ℝ))) < resonanceRoot1) (hcond : 27 * Q₂ ≤ 128 * Q₁) :
    siteForce b h fluoriteCationShells (shellCharge 3 Q₁ Q₂) q p p = 0 ∧
      0 < -q * siteRate h fluoriteCationShells (shellCharge 3 Q₁ Q₂) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ =>
          ⟪siteForce b h fluoriteCationShells (shellCharge 3 Q₁ Q₂) q p (p + s • v), v⟫)
        (-q * siteRate h fluoriteCationShells (shellCharge 3 Q₁ Q₂) * ‖v‖ ^ 2) 0 := by
  have hs := fluoriteCation_shells
  exact two_shell_pushed (k₁ := 3) (k₂ := 8) (N₁ := 8) (N₂ := 12) b p hh
    (fluoriteCation_closed 2 8) (by norm_num) (by norm_num) hs.1 hs.2.1 hs.2.2
    (by norm_num) hQ₁ hQ₂ hq hx (by push_cast; nlinarith)

/-- Fluorite, seen from an anion. Four unlike neighbours at squared distance
`3` and six like neighbours at squared distance `4`: a positive test charge is
pushed off once `27 Q₂ ≤ 32 Q₁`. -/
theorem fluoriteAnion_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    {Q₁ Q₂ q : ℝ} (hQ₁ : 0 < Q₁) (hQ₂ : 0 ≤ Q₂) (hq : 0 < q)
    (hx : 1 / (2 * (h * √(3 : ℝ))) < resonanceRoot1) (hcond : 27 * Q₂ ≤ 32 * Q₁) :
    siteForce b h fluoriteAnionShells (shellCharge 3 Q₁ Q₂) q p p = 0 ∧
      0 < -q * siteRate h fluoriteAnionShells (shellCharge 3 Q₁ Q₂) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ =>
          ⟪siteForce b h fluoriteAnionShells (shellCharge 3 Q₁ Q₂) q p (p + s • v), v⟫)
        (-q * siteRate h fluoriteAnionShells (shellCharge 3 Q₁ Q₂) * ‖v‖ ^ 2) 0 := by
  have hs := fluoriteAnion_shells
  exact two_shell_pushed (k₁ := 3) (k₂ := 4) (N₁ := 4) (N₂ := 6) b p hh
    (fluoriteAnion_closed 2 4) (by norm_num) (by norm_num) hs.1 hs.2.1 hs.2.2
    (by norm_num) hQ₁ hQ₂ hq hx (by push_cast; nlinarith)

theorem rockSalt_equal_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q) (hx : 1 / (2 * h) < resonanceRoot1) :
    siteForce b h rockSaltShells (shellCharge 1 Q Q) q p p = 0 ∧
      0 < -q * siteRate h rockSaltShells (shellCharge 1 Q Q) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ => ⟪siteForce b h rockSaltShells (shellCharge 1 Q Q) q p (p + s • v), v⟫)
        (-q * siteRate h rockSaltShells (shellCharge 1 Q Q) * ‖v‖ ^ 2) 0 :=
  rockSalt_pushed b p hh hQ hQ.le hq hx (by nlinarith)

theorem caesiumChloride_equal_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ}
    (hh : 0 < h) {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q)
    (hx : 1 / (2 * (h * √(3 : ℝ))) < resonanceRoot1) :
    siteForce b h caesiumChlorideShells (shellCharge 3 Q Q) q p p = 0 ∧
      0 < -q * siteRate h caesiumChlorideShells (shellCharge 3 Q Q) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ =>
          ⟪siteForce b h caesiumChlorideShells (shellCharge 3 Q Q) q p (p + s • v), v⟫)
        (-q * siteRate h caesiumChlorideShells (shellCharge 3 Q Q) * ‖v‖ ^ 2) 0 :=
  caesiumChloride_pushed b p hh hQ hQ.le hq hx (by nlinarith)

theorem zincblende_equal_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ} (hh : 0 < h)
    {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q)
    (hx : 1 / (2 * (h * √(3 : ℝ))) < resonanceRoot1) :
    siteForce b h zincblendeShells (shellCharge 3 Q Q) q p p = 0 ∧
      0 < -q * siteRate h zincblendeShells (shellCharge 3 Q Q) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ => ⟪siteForce b h zincblendeShells (shellCharge 3 Q Q) q p (p + s • v), v⟫)
        (-q * siteRate h zincblendeShells (shellCharge 3 Q Q) * ‖v‖ ^ 2) 0 :=
  zincblende_pushed b p hh hQ hQ.le hq hx (by nlinarith)

/-- The cation carries twice the anion's charge. -/
theorem fluoriteCation_twice_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ}
    (hh : 0 < h) {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q)
    (hx : 1 / (2 * (h * √(3 : ℝ))) < resonanceRoot1) :
    siteForce b h fluoriteCationShells (shellCharge 3 Q (2 * Q)) q p p = 0 ∧
      0 < -q * siteRate h fluoriteCationShells (shellCharge 3 Q (2 * Q)) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ =>
          ⟪siteForce b h fluoriteCationShells (shellCharge 3 Q (2 * Q)) q p (p + s • v), v⟫)
        (-q * siteRate h fluoriteCationShells (shellCharge 3 Q (2 * Q)) * ‖v‖ ^ 2) 0 :=
  fluoriteCation_pushed b p hh hQ (by positivity) hq hx (by nlinarith)

/-- The cation carries twice the anion's charge, seen from the anion. -/
theorem fluoriteAnion_twice_pushed (b : OrthonormalBasis (Fin 3) ℝ E) (p : E) {h : ℝ}
    (hh : 0 < h) {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q)
    (hx : 1 / (2 * (h * √(3 : ℝ))) < resonanceRoot1) :
    siteForce b h fluoriteAnionShells (shellCharge 3 (2 * Q) Q) q p p = 0 ∧
      0 < -q * siteRate h fluoriteAnionShells (shellCharge 3 (2 * Q) Q) ∧
      ∀ v : E, HasDerivAt
        (fun s : ℝ =>
          ⟪siteForce b h fluoriteAnionShells (shellCharge 3 (2 * Q) Q) q p (p + s • v), v⟫)
        (-q * siteRate h fluoriteAnionShells (shellCharge 3 (2 * Q) Q) * ‖v‖ ^ 2) 0 :=
  fluoriteAnion_pushed b p hh (by positivity) hQ.le hq hx (by nlinarith)

end Ionic

/-! ### Which rotations preserve a lattice -/

section Symmetry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A linear map carrying each basis vector to an integer combination of the
basis has an integer trace. -/
theorem latticeMap_trace_int (b : OrthonormalBasis (Fin 3) ℝ E) (f : E →ₗ[ℝ] E)
    (m : Fin 3 → Fin 3 → ℤ) (hf : ∀ i, f (b i) = ∑ j, (m i j : ℝ) • b j) :
    ∃ n : ℤ, LinearMap.trace ℝ E f = (n : ℝ) := by
  refine ⟨m 0 0 + m 1 1 + m 2 2, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, Matrix.trace_fin_three]
  have hdiag (i : Fin 3) :
      LinearMap.toMatrix b.toBasis b.toBasis f i i = (m i i : ℝ) := by
    rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply, b.repr_apply_apply,
      hf i, inner_sum]
    simp_rw [real_inner_smul_right, b.inner_eq_ite, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_ite_eq i (fun j => (m i j : ℝ))]
  rw [hdiag, hdiag, hdiag]
  push_cast
  ring

/-- A rotation through `θ` about `b 2`, proper when `ε = 1` and improper when
`ε = -1`, has trace `2 cos θ + ε`. -/
theorem rotation_trace (b : OrthonormalBasis (Fin 3) ℝ E) (f : E →ₗ[ℝ] E) {θ ε : ℝ}
    (h0 : f (b 0) = cos θ • b 0 + sin θ • b 1)
    (h1 : f (b 1) = -sin θ • b 0 + cos θ • b 1) (h2 : f (b 2) = ε • b 2) :
    LinearMap.trace ℝ E f = 2 * cos θ + ε := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, Matrix.trace_fin_three]
  have hd (i : Fin 3) : LinearMap.toMatrix b.toBasis b.toBasis f i i = ⟪b i, f (b i)⟫ := by
    rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply, b.repr_apply_apply]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  rw [hd, hd, hd, h0, h1, h2]
  simp [h01, h10, inner_add_right, real_inner_smul_right, b.inner_eq_ite]
  ring

/-- `2 cos(2π/n) + ε` is an integer, with `ε = ±1`, only for
`n ∈ {1, 2, 3, 4, 6}`. -/
theorem rotation_order_of_int_trace {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {k : ℤ} (h : 2 * cos (2 * π / n) + ε = (k : ℝ)) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  by_cases h1 : n = 1
  · exact Or.inl h1
  by_cases h2 : n = 2
  · exact Or.inr (Or.inl h2)
  by_cases h3 : n = 3
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : n = 4
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  by_cases h6 : n = 6
  · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))
  have hsplit : n = 5 ∨ 7 ≤ n := by omega
  rcases hsplit with rfl | hn7
  · exfalso
    have hlo : π / 3 < 2 * π / 5 := by
      rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [pi_pos]
    have hhi : 2 * π / 5 < π / 2 := by
      rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [pi_pos]
    have hcHi : cos (π / 2) < cos (2 * π / 5) :=
      cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos]) hhi
    have hcLo : cos (2 * π / 5) < cos (π / 3) :=
      cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos]) hlo
    rw [cos_pi_div_two] at hcHi
    rw [cos_pi_div_three] at hcLo
    rcases hε with rfl | rfl
    · have hgt : ((1 : ℤ) : ℝ) < (k : ℝ) := by rw [← h]; nlinarith [hcHi]
      have hlt : (k : ℝ) < 2 := by rw [← h]; nlinarith [hcLo]
      have ha : 1 < k := Int.cast_lt.mp hgt
      have hb : k < 2 := Int.cast_lt.mp hlt
      omega
    · have hgt : ((-1 : ℤ) : ℝ) < (k : ℝ) := by rw [← h]; nlinarith [hcHi]
      have hlt : (k : ℝ) < ((0 : ℤ) : ℝ) := by rw [← h]; nlinarith [hcLo]
      have ha : -1 < k := Int.cast_lt.mp hgt
      have hb : k < 0 := Int.cast_lt.mp hlt
      omega
  · exfalso
    have hhi : 2 * π / n < π / 3 := by
      have hn' : (7 : ℝ) ≤ n := by exact_mod_cast hn7
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pi_pos]
    have hpos : 0 < 2 * π / n := by positivity
    have hcHi : cos (2 * π / n) < cos 0 :=
      cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (lt_trans hhi (by linarith [pi_pos])).le hpos
    have hcLo : cos (π / 3) < cos (2 * π / n) :=
      cos_lt_cos_of_nonneg_of_le_pi hpos.le (by linarith [pi_pos]) hhi
    rw [cos_zero] at hcHi
    rw [cos_pi_div_three] at hcLo
    rcases hε with rfl | rfl
    · have hgt : (2 : ℝ) < (k : ℝ) := by rw [← h]; nlinarith [hcLo]
      have hlt : (k : ℝ) < 3 := by rw [← h]; nlinarith [hcHi]
      have ha : 2 < k := Int.cast_lt.mp hgt
      have hb : k < 3 := Int.cast_lt.mp hlt
      omega
    · have hgt : ((0 : ℤ) : ℝ) < (k : ℝ) := by rw [← h]; nlinarith [hcLo]
      have hlt : (k : ℝ) < ((1 : ℤ) : ℝ) := by rw [← h]; nlinarith [hcHi]
      have ha : 0 < k := Int.cast_lt.mp hgt
      have hb : k < 1 := Int.cast_lt.mp hlt
      omega

/-- A rotation through `2π/n`, proper or improper, carries a lattice of a
three-dimensional space into itself only for `n ∈ {1, 2, 3, 4, 6}`. -/
theorem lattice_rotation_order {n : ℕ} (hn : 0 < n) (b : OrthonormalBasis (Fin 3) ℝ E)
    (f : E →ₗ[ℝ] E) (m : Fin 3 → Fin 3 → ℤ)
    (hf : ∀ i, f (b i) = ∑ j, (m i j : ℝ) • b j) {θ ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hθ : θ = 2 * π / n) (h0 : f (b 0) = cos θ • b 0 + sin θ • b 1)
    (h1 : f (b 1) = -sin θ • b 0 + cos θ • b 1) (h2 : f (b 2) = ε • b 2) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  obtain ⟨k, hk⟩ := latticeMap_trace_int b f m hf
  have hr := rotation_trace b f h0 h1 h2
  exact rotation_order_of_int_trace hn hε (by rw [← hθ, ← hr, hk])

end Symmetry

end Gravity

end DstDiophantine
