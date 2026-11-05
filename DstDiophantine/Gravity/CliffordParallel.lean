import DstDiophantine.Gravity.RelationalPosition
import DstDiophantine.Gravity.SI
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Clifford parallels on the three-sphere

The three-sphere carries two global framings. Left translation along a pure
unit imaginary draws a great circle whose relative rotor depends only on the
parameter increment. Right translation draws another, with the same increment
standing on the left. Conjugation swaps the two families and reverses the
parameter, so the two parallelisms are mirrors.

At the identity the frames agree. At geodesic angle `φ` along `I`, the right
frame's `J` direction is the left frame's `cos(2φ) J - sin(2φ) K`. The frames
therefore differ by `2φ`. That double angle is the twist the twistor
correspondence reads in the Hopf fibration. No twistor space is constructed.

On a sphere of radius `ρ` the same mismatch at physical distance `s` is
`2s/ρ`. The gravitational channel reads it on the galactic radius `R`, the
electromagnetic channel on `Λ`. The ratio of the two mismatches is `Λ/R`, and
their difference is `2s(Λ-R)/(RΛ)`.

## Hubble reading (external)

Reading `Λ` as the Hubble length `c/H₀`, with `H₀` in km s⁻¹ Mpc⁻¹, gives
`Λ` in kiloparsecs as `c/H₀` once `c` is the SI metre-per-second value: one
megaparsec is a thousand kiloparsecs, and the kilometres in `c` cancel the
kilometres in `H₀`. For `8 ≤ R ≤ 9` and `67 ≤ H₀ ≤ 74` the edge mismatch of
the electromagnetic frame lies strictly between `3.57×10⁻⁶` and `4.45×10⁻⁶`,
while the gravitational mismatch is `2`. The gravitational mismatch exceeds
the electromagnetic one by a factor strictly between `450138` and `559315`.

`H₀` is an input, as `a₀` is. No theorem asserts `dst_derives_lambda`.
-/

namespace DstDiophantine.Gravity.CliffordParallel

open Quaternion Real RelationalPosition

/-! ### The two Hopf fields -/

/-- Pure unit `I`. -/
def qI : ℍ := ⟨0, 1, 0, 0⟩

/-- Pure unit `J`. -/
def qJ : ℍ := ⟨0, 0, 1, 0⟩

/-- Pure unit `K`. -/
def qK : ℍ := ⟨0, 0, 0, 1⟩

theorem qI_norm : normSq qI = 1 := by
  simp [normSq_def', qI]

theorem qJ_norm : normSq qJ = 1 := by
  simp [normSq_def', qJ]

theorem qK_norm : normSq qK = 1 := by
  simp [normSq_def', qK]

theorem qI_ne_zero : qI ≠ 0 := by
  intro h
  have hI := congrArg (fun z : ℍ => z.imI) h
  simp [qI] at hI

theorem star_qI : star qI = -qI := by
  ext <;> simp [qI]

theorem star_qJ : star qJ = -qJ := by
  ext <;> simp [qJ]

theorem star_qK : star qK = -qK := by
  ext <;> simp [qK]

/-- Left Clifford circle through the identity, parallel to `I`. -/
noncomputable def hopfI (t : ℝ) : S3 where
  val := ⟨Real.cos t, Real.sin t, 0, 0⟩
  norm_one := by
    rw [normSq_def']
    simp

theorem hopfI_zero : hopfI 0 = 1 := by
  apply S3.ext
  ext <;> simp [hopfI, one_val]

theorem hopfI_mul (t s : ℝ) : hopfI t * hopfI s = hopfI (t + s) := by
  apply S3.ext
  ext
  · simp [mul_val, hopfI, Real.cos_add]; ring
  · simp [mul_val, hopfI, Real.sin_add]; ring
  · simp [mul_val, hopfI]
  · simp [mul_val, hopfI]

theorem hopfI_inv (t : ℝ) : (hopfI t)⁻¹ = hopfI (-t) := by
  apply S3.ext
  simp [inv_val, hopfI, Real.cos_neg, Real.sin_neg]

/-- Left parallel through `q`: the relative rotor depends only on the step. -/
noncomputable def leftParallel (q : S3) (t : ℝ) : S3 :=
  q * hopfI t

/-- Right parallel through `q`. The same step stands on the left. -/
noncomputable def rightParallel (q : S3) (t : ℝ) : S3 :=
  hopfI t * q

theorem leftParallel_zero (q : S3) : leftParallel q 0 = q := by
  simp [leftParallel, hopfI_zero]

theorem rightParallel_zero (q : S3) : rightParallel q 0 = q := by
  simp [rightParallel, hopfI_zero]

/-- Along a left parallel the displacement rotor is `hopfI s` at every base
point and every instant. -/
theorem leftParallel_step (q : S3) (t s : ℝ) :
    (leftParallel q t)⁻¹ * leftParallel q (t + s) = hopfI s := by
  unfold leftParallel
  calc
    (q * hopfI t)⁻¹ * (q * hopfI (t + s))
        = (hopfI t)⁻¹ * q⁻¹ * (q * hopfI (t + s)) := by rw [mul_inv_rev]
    _ = (hopfI t)⁻¹ * (q⁻¹ * (q * hopfI (t + s))) := by rw [mul_assoc]
    _ = (hopfI t)⁻¹ * ((q⁻¹ * q) * hopfI (t + s)) := by
      rw [← mul_assoc q⁻¹ q (hopfI (t + s))]
    _ = (hopfI t)⁻¹ * (1 * hopfI (t + s)) := by rw [inv_mul_cancel]
    _ = (hopfI t)⁻¹ * hopfI (t + s) := by rw [one_mul]
    _ = hopfI (-t) * hopfI (t + s) := by rw [hopfI_inv]
    _ = hopfI (-t + (t + s)) := by rw [← hopfI_mul (-t) (t + s)]
    _ = hopfI s := by
      congr 1
      ring

/-- Along a right parallel the same displacement stands on the left. -/
theorem rightParallel_step (q : S3) (t s : ℝ) :
    rightParallel q (t + s) * (rightParallel q t)⁻¹ = hopfI s := by
  unfold rightParallel
  calc
    (hopfI (t + s) * q) * (hopfI t * q)⁻¹
        = (hopfI (t + s) * q) * (q⁻¹ * (hopfI t)⁻¹) := by rw [mul_inv_rev]
    _ = hopfI (t + s) * (q * (q⁻¹ * (hopfI t)⁻¹)) := by rw [mul_assoc]
    _ = hopfI (t + s) * ((q * q⁻¹) * (hopfI t)⁻¹) := by
      rw [← mul_assoc q q⁻¹ (hopfI t)⁻¹]
    _ = hopfI (t + s) * (1 * (hopfI t)⁻¹) := by rw [mul_inv_cancel]
    _ = hopfI (t + s) * (hopfI t)⁻¹ := by rw [one_mul]
    _ = hopfI (t + s) * hopfI (-t) := by rw [hopfI_inv]
    _ = hopfI (t + s + -t) := by rw [← hopfI_mul (t + s) (-t)]
    _ = hopfI s := by
      congr 1
      ring

/-- Conjugation sends a left parallel to the right parallel of the conjugate
point and reverses the parameter. The two families are mirrors. -/
theorem mirror_parallel (q : S3) (t : ℝ) :
    (leftParallel q t)⁻¹ = rightParallel q⁻¹ (-t) := by
  unfold leftParallel rightParallel
  rw [mul_inv_rev, hopfI_inv]

theorem hopfI_nontrivial : hopfI 0 ≠ hopfI (Real.pi / 2) := by
  intro h
  have hre := congrArg (fun p : S3 => p.val.re) h
  simp [hopfI] at hre

/-! ### The global frame and its twist -/

theorem parallel_dir_ne_zero (q : S3) {u : ℍ} (hu : u ≠ 0) : q.val * u ≠ 0 := by
  intro h
  have h0 : star q.val * (q.val * u) = 0 := by simp [h]
  rw [← mul_assoc, star_mul_self, q.norm_one, coe_one, one_mul] at h0
  exact hu h0

theorem left_dir_ne_zero (q : S3) : q.val * qI ≠ 0 :=
  parallel_dir_ne_zero q qI_ne_zero

/-- Pulling a pair of directions back by left translation recovers their
inner product at the identity. -/
theorem left_inner (q : S3) (u v : ℍ) :
    (star (q.val * u) * (q.val * v)).re = (star u * v).re := by
  rw [star_mul, mul_assoc, ← mul_assoc (star q.val) q.val v, star_mul_self, q.norm_one,
    coe_one, one_mul]

theorem qI_qJ_orthogonal : (star qI * qJ).re = 0 := by
  simp [qI, qJ]

theorem qI_qK_orthogonal : (star qI * qK).re = 0 := by
  simp [qI, qK]

theorem qJ_qK_orthogonal : (star qJ * qK).re = 0 := by
  simp [qJ, qK]

theorem normSq_left_axis (q : S3) {u : ℍ} (hu : normSq u = 1) :
    normSq (q.val * u) = 1 := by
  have h1 : star (q.val * u) * (q.val * u) = 1 := by
    rw [star_mul, mul_assoc, ← mul_assoc (star q.val) q.val u, star_mul_self, q.norm_one,
      coe_one, one_mul, star_mul_self, hu, coe_one]
  rw [star_mul_self] at h1
  have hre := congrArg (fun z : ℍ => z.re) h1
  simpa using hre

theorem left_frame_orthonormal (q : S3) :
    normSq (q.val * qI) = 1 ∧ normSq (q.val * qJ) = 1 ∧ normSq (q.val * qK) = 1 ∧
      (star (q.val * qI) * (q.val * qJ)).re = 0 ∧
      (star (q.val * qI) * (q.val * qK)).re = 0 ∧
      (star (q.val * qJ) * (q.val * qK)).re = 0 := by
  refine ⟨normSq_left_axis q qI_norm, normSq_left_axis q qJ_norm, normSq_left_axis q qK_norm,
    ?_, ?_, ?_⟩
  · rw [left_inner, qI_qJ_orthogonal]
  · rw [left_inner, qI_qK_orthogonal]
  · rw [left_inner, qJ_qK_orthogonal]

/-- Right frame, the mirror of the left frame: conjugation swaps the order. -/
theorem star_left_dir (q : S3) (u : ℍ) :
    star (q.val * u) = star u * star q.val :=
  star_mul q.val u

/-- Body representative of the right-hand `J` direction after angle `φ` along `I`. -/
noncomputable def twistedJ (φ : ℝ) : ℍ :=
  ⟨0, 0, Real.cos (2 * φ), -Real.sin (2 * φ)⟩

theorem frames_agree_at_identity :
    qJ * (hopfI 0).val = (hopfI 0).val * qJ := by
  simp [hopfI, qJ]

theorem right_eq_left_twisted (φ : ℝ) :
    qJ * (hopfI φ).val = (hopfI φ).val * twistedJ φ := by
  ext
  · simp [qJ, hopfI, twistedJ]
  · simp [qJ, hopfI, twistedJ]
  · have hL : (qJ * (hopfI φ).val).imJ = Real.cos φ := by
      simp [qJ, hopfI]
    have hR : ((hopfI φ).val * twistedJ φ).imJ =
        Real.cos φ * Real.cos (2 * φ) + Real.sin φ * Real.sin (2 * φ) := by
      simp [hopfI, twistedJ]
    rw [hL, hR, ← Real.cos_sub]
    rw [show φ - 2 * φ = -φ by ring, Real.cos_neg]
  · have hL : (qJ * (hopfI φ).val).imK = -Real.sin φ := by
      simp [qJ, hopfI]
    have hR : ((hopfI φ).val * twistedJ φ).imK =
        Real.sin φ * Real.cos (2 * φ) - Real.cos φ * Real.sin (2 * φ) := by
      simp [hopfI, twistedJ]
      ring
    rw [hL, hR, ← Real.sin_sub]
    rw [show φ - 2 * φ = -φ by ring, Real.sin_neg]

theorem twist_cosine (φ : ℝ) :
    (star qJ * twistedJ φ).re = Real.cos (2 * φ) := by
  simp [qJ, twistedJ]

/-- On `[0, π/2]` the unsigned angle between the two `J` directions is `2φ`. -/
theorem twist_angle {φ : ℝ} (h0 : 0 ≤ φ) (hπ : φ ≤ Real.pi / 2) :
    Real.arccos ((star qJ * twistedJ φ).re) = 2 * φ := by
  rw [twist_cosine, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]

/-- Reversing the geodesic angle reverses the sense of the twist and keeps
the cosine. -/
theorem mirror_twist_sense (φ : ℝ) :
    (twistedJ (-φ)).imJ = (twistedJ φ).imJ ∧
      (twistedJ (-φ)).imK = -((twistedJ φ).imK) := by
  simp [twistedJ, Real.cos_neg, Real.sin_neg]

theorem frames_differ_at_quarter :
    qJ * (hopfI (Real.pi / 4)).val ≠ (hopfI (Real.pi / 4)).val * qJ := by
  intro h
  have htwist := right_eq_left_twisted (Real.pi / 4)
  have heq : (hopfI (Real.pi / 4)).val * twistedJ (Real.pi / 4) =
      (hopfI (Real.pi / 4)).val * qJ := htwist.symm.trans h
  have hunit : star (hopfI (Real.pi / 4)).val * (hopfI (Real.pi / 4)).val = 1 := by
    rw [star_mul_self, (hopfI (Real.pi / 4)).norm_one, coe_one]
  have hbody : twistedJ (Real.pi / 4) = qJ := by
    have hmul := congrArg (fun z : ℍ => star (hopfI (Real.pi / 4)).val * z) heq
    simpa [← mul_assoc, hunit] using hmul
  have hne : (twistedJ (Real.pi / 4)).imK ≠ qJ.imK := by
    rw [twistedJ, qJ, show (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
    norm_num
  exact hne (congrArg (fun z : ℍ => z.imK) hbody)

/-! ### The two channels -/

/-- Mirror mismatch at physical distance `s` on a three-sphere of radius `ρ`.
Twice the geodesic angle `s/ρ`. -/
noncomputable def mirrorTwist (s ρ : ℝ) : ℝ :=
  2 * s / ρ

theorem mirrorTwist_edge {R : ℝ} (hR : R ≠ 0) : mirrorTwist R R = 2 := by
  unfold mirrorTwist
  field_simp [hR]

theorem mirrorTwist_ratio {s R Λ : ℝ} (hs : s ≠ 0) (hR : R ≠ 0) (hΛ : Λ ≠ 0) :
    mirrorTwist s R / mirrorTwist s Λ = Λ / R := by
  unfold mirrorTwist
  field_simp

theorem mirrorTwist_gap {s R Λ : ℝ} (hR : R ≠ 0) (hΛ : Λ ≠ 0) :
    mirrorTwist s R - mirrorTwist s Λ = 2 * s * (Λ - R) / (R * Λ) := by
  unfold mirrorTwist
  field_simp

/-! ### Hubble window, external -/

theorem speedOfLight_coe : (SI.speedOfLight : ℝ) = 299792458 := by
  unfold SI.speedOfLight SI.speedOfLightNat
  norm_num

/-- For a galactic radius in kiloparsecs between `8` and `9`, and a Hubble
parameter between `67` and `74` km s⁻¹ Mpc⁻¹, the electromagnetic mirror
mismatch at the patch edge lies in `(3.57×10⁻⁶, 4.45×10⁻⁶)`, and the
gravitational mismatch `2` exceeds it by a factor in `(450138, 559315)`. -/
theorem hubble_frame_window {R H : ℝ}
    (hRlo : (8 : ℝ) ≤ R) (hRhi : R ≤ 9)
    (hHlo : (67 : ℝ) ≤ H) (hHhi : H ≤ 74) :
    (450138 : ℝ) < ((SI.speedOfLight : ℝ) / H) / R ∧
      ((SI.speedOfLight : ℝ) / H) / R < 559315 ∧
      (357 : ℝ) / 10 ^ 8 < 2 * R / ((SI.speedOfLight : ℝ) / H) ∧
      2 * R / ((SI.speedOfLight : ℝ) / H) < (445 : ℝ) / 10 ^ 8 := by
  rw [speedOfLight_coe]
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hRlo
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num) hHlo
  have hprod_lo : (536 : ℝ) ≤ H * R := by nlinarith
  have hprod_hi : H * R ≤ 666 := by nlinarith
  have hprod_pos : (0 : ℝ) < H * R := by nlinarith
  have hratio : (299792458 / H) / R = 299792458 / (H * R) := by
    field_simp
  have htwist : 2 * R / (299792458 / H) = 2 * (H * R) / 299792458 := by
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hratio]
    have hfloor : (450138 : ℝ) < 299792458 / 666 := by norm_num
    have hcomp : 299792458 / 666 ≤ 299792458 / (H * R) :=
      div_le_div_of_nonneg_left (by norm_num) hprod_pos hprod_hi
    exact hfloor.trans_le hcomp
  · rw [hratio]
    have hceil : 299792458 / 536 < (559315 : ℝ) := by norm_num
    have hcomp : 299792458 / (H * R) ≤ 299792458 / 536 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hprod_lo
    exact lt_of_le_of_lt hcomp hceil
  · rw [htwist]
    have hfloor : (357 : ℝ) / 10 ^ 8 < 1072 / 299792458 := by norm_num
    have hcomp : 1072 / 299792458 ≤ 2 * (H * R) / 299792458 := by
      have hnum : (1072 : ℝ) ≤ 2 * (H * R) := by linarith
      exact div_le_div_of_nonneg_right hnum (by norm_num)
    exact hfloor.trans_le hcomp
  · rw [htwist]
    have hceil : 1332 / 299792458 < (445 : ℝ) / 10 ^ 8 := by norm_num
    have hcomp : 2 * (H * R) / 299792458 ≤ 1332 / 299792458 := by
      have hnum : 2 * (H * R) ≤ (1332 : ℝ) := by linarith
      exact div_le_div_of_nonneg_right hnum (by norm_num)
    exact lt_of_le_of_lt hcomp hceil

end DstDiophantine.Gravity.CliffordParallel
