import DstDiophantine.Gravity.RelationalPosition
import DstDiophantine.Logic.Quantum.DualOccupancy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Two electrons as elements of the three-sphere

The nucleus and the two electrons are three elements of the three-sphere. In the
nucleus frame the electrons are the two relative rotors. A common left rotation
leaves that frame fixed. A common right rotation preserves the three cosines of
the angles: each electron from the nucleus, and the electrons from each other.
Those three cosines classify the frame. A spatial amplitude unchanged by every
common right rotation is therefore an amplitude of the three cosines.

Exchange of the electrons swaps the two angles from the nucleus, preserves the
angle between them, and inverts the relative rotor. The singlet changes sign
under exchange of the spin factors, so the spatial amplitude that accompanies it
is the symmetric one, and the joint state changes sign once. An amplitude that
changes sign under exchange of the elements vanishes when the elements coincide.
A symmetric amplitude is not forced to vanish there.

## Not claimed

* An identification of these angles with the laboratory separations that enter
  `γ_s`. The three cosines are relations of three elements. At an atomic
  separation the curvature of a three-sphere of galactic or cosmic
  compactification radius does not enter the force.
* An energy, a spectrum, a dissociation energy, or a value of `ℓ`.
* A position operator, or a derivation of the spin-statistics theorem.
* That coincidence of the two elements is the repeated ray of one dual spinor.
  The ray is the spin factor. The element is the place. `SpinVersusExclusion`
  separates the two.
-/

noncomputable section

namespace DstDiophantine.Gravity.HeliumBody

open Quaternion Real RelationalPosition
open DstDiophantine.Logic

def qI : ℍ := ⟨0, 1, 0, 0⟩

def qJ : ℍ := ⟨0, 0, 1, 0⟩

def imNormSq (q : ℍ) : ℝ := q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

lemma imNormSq_nonneg (q : ℍ) : 0 ≤ imNormSq q := by
  unfold imNormSq
  nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]

lemma imNormSq_of_unit (a : S3) : imNormSq a.val = 1 - a.val.re ^ 2 := by
  have h := a.norm_one
  rw [normSq_def'] at h
  unfold imNormSq
  linarith

lemma qI_mul_re_zero {p : ℍ} (hp : p.re = 0) :
    qI * p = ⟨-p.imI, 0, -p.imK, p.imJ⟩ := by
  ext <;> simp [qI, hp]

lemma qI_sq : qI * qI = (-1 : ℍ) := by
  ext <;> simp [qI]

lemma qJ_sends_negI : star qJ * (-qI) * qJ = qI := by
  apply Quaternion.ext <;> simp [qJ, qI]

lemma mul_plane_right (c s : ℝ) (v : ℍ) :
    v * ⟨c, s, 0, 0⟩ =
      ⟨v.re * c - v.imI * s, v.re * s + v.imI * c,
        v.imJ * c + v.imK * s, v.imK * c - v.imJ * s⟩ := by
  apply Quaternion.ext
  · simp
  · simp
  · simp
  · simp; ring

lemma mul_plane_left (c s : ℝ) (v : ℍ) :
    (⟨c, -s, 0, 0⟩ : ℍ) * v =
      ⟨c * v.re + s * v.imI, c * v.imI - s * v.re,
        c * v.imJ + s * v.imK, c * v.imK - s * v.imJ⟩ := by
  apply Quaternion.ext
  · simp
  · simp; ring
  · simp
  · simp; ring

lemma conj_plane (c s : ℝ) (v : ℍ) (hcs : c ^ 2 + s ^ 2 = 1) :
    star (⟨c, s, 0, 0⟩ : ℍ) * v * ⟨c, s, 0, 0⟩ =
      ⟨v.re, v.imI,
        v.imJ * (c ^ 2 - s ^ 2) + v.imK * (2 * s * c),
        -(v.imJ * (2 * s * c)) + v.imK * (c ^ 2 - s ^ 2)⟩ := by
  have hs : star (⟨c, s, 0, 0⟩ : ℍ) = ⟨c, -s, 0, 0⟩ := by ext <;> simp
  rw [hs, mul_assoc, mul_plane_right, mul_plane_left]
  ext
  · simp only
    have : c * (v.re * c - v.imI * s) + s * (v.re * s + v.imI * c) =
        (c ^ 2 + s ^ 2) * v.re := by ring
    rw [this, hcs, one_mul]
  · simp only
    have : c * (v.re * s + v.imI * c) - s * (v.re * c - v.imI * s) =
        (c ^ 2 + s ^ 2) * v.imI := by ring
    rw [this, hcs, one_mul]
  · simp only
    ring
  · simp only
    ring

lemma conj_add (h : S3) (x y : ℍ) :
    star h.val * (x + y) * h.val =
      star h.val * x * h.val + star h.val * y * h.val := by
  simp [mul_add, add_mul, mul_assoc]

lemma conj_smul (h : S3) (r : ℝ) (x : ℍ) :
    star h.val * (r • x) * h.val = r • (star h.val * x * h.val) := by
  rw [← coe_mul_eq_smul, coe_commutes]
  calc
    star h.val * (x * (r : ℍ)) * h.val = star h.val * x * ((r : ℍ) * h.val) := by
      simp [mul_assoc]
    _ = star h.val * x * (h.val * (r : ℍ)) := by rw [coe_commutes]
    _ = star h.val * x * h.val * (r : ℍ) := by simp [mul_assoc]
    _ = r • (star h.val * x * h.val) := by rw [mul_coe_eq_smul]

lemma conj_coe (h : S3) (r : ℝ) : star h.val * (r : ℍ) * h.val = (r : ℍ) := by
  calc
    star h.val * (r : ℍ) * h.val = star h.val * ((r : ℍ) * h.val) := by rw [mul_assoc]
    _ = star h.val * (h.val * (r : ℍ)) := by rw [coe_commutes]
    _ = (star h.val * h.val) * (r : ℍ) := by rw [← mul_assoc]
    _ = (1 : ℍ) * (r : ℍ) := by rw [star_mul_self, h.norm_one, coe_one]
    _ = (r : ℍ) := by simp

def unitOf (q : ℍ) (hq : normSq q ≠ 0) : S3 where
  val := (1 / Real.sqrt (normSq q)) • q
  norm_one := by
    have hs2 : (Real.sqrt (normSq q)) ^ 2 = normSq q :=
      Real.sq_sqrt (normSq_nonneg (a := q))
    have hpos : Real.sqrt (normSq q) ≠ 0 := by
      intro h0
      apply hq
      have hsq : (Real.sqrt (normSq q)) ^ 2 = 0 := by rw [h0]; ring
      rwa [hs2] at hsq
    rw [normSq_smul]
    calc
      (1 / Real.sqrt (normSq q)) ^ 2 * normSq q =
          normSq q / (Real.sqrt (normSq q)) ^ 2 := by field_simp [hpos]
      _ = normSq q / normSq q := by rw [hs2]
      _ = 1 := by field_simp [hq]

lemma pure_sq {p : ℍ} (hre : p.re = 0) (hn : p.imI ^ 2 + p.imJ ^ 2 + p.imK ^ 2 = 1) :
    p * p = (-1 : ℍ) := by
  ext
  · simp [hre]
    linarith
  · simp [hre]; ring
  · simp [hre]; ring
  · simp [hre]; ring

lemma align_raw_pos {p : ℍ} (hre : p.re = 0) (hn : normSq p = 1) (hneg : p ≠ -qI) :
    0 < normSq ((1 : ℍ) - qI * p) := by
  have hmul := qI_mul_re_zero hre
  have him : p.imI ^ 2 + p.imJ ^ 2 + p.imK ^ 2 = 1 := by
    have hn' := hn
    rw [normSq_def'] at hn'
    simp only [hre] at hn'
    linarith
  have hx : -1 < p.imI := by
    by_contra hle
    push Not at hle
    have heq : p.imI = -1 := by nlinarith [sq_nonneg p.imI]
    have hy : p.imJ = 0 := by nlinarith [heq, him]
    have hz : p.imK = 0 := by nlinarith [heq, him]
    apply hneg
    ext <;> simp [qI, hre, heq, hy, hz]
  have hraw : (1 : ℍ) - qI * p = ⟨1 + p.imI, 0, p.imK, -p.imJ⟩ := by
    rw [hmul]
    ext <;> simp
  rw [hraw, normSq_def']
  simp only
  nlinarith [him, hx]

lemma raw_mul_eq {p : ℍ} (hre : p.re = 0) (hn : normSq p = 1) :
    ((1 : ℍ) - qI * p) * p = qI * ((1 : ℍ) - qI * p) := by
  have him : p.imI ^ 2 + p.imJ ^ 2 + p.imK ^ 2 = 1 := by
    have hn' := hn
    rw [normSq_def'] at hn'
    simp only [hre] at hn'
    linarith
  have hp2 : p * p = (-1 : ℍ) := pure_sq hre him
  calc
    ((1 : ℍ) - qI * p) * p = p - qI * (p * p) := by simp [sub_mul, mul_assoc]
    _ = p - qI * (-1 : ℍ) := by rw [hp2]
    _ = p + qI := by rw [mul_neg, mul_one]; abel
    _ = qI + p := by abel
    _ = qI - (qI * qI) * p := by
      have hI : (qI * qI) * p = (-1 : ℍ) * p := by rw [qI_sq]
      rw [hI, neg_one_mul]
      abel
    _ = qI * (1 : ℍ) - qI * (qI * p) := by rw [mul_one, mul_assoc]
    _ = qI * ((1 : ℍ) - qI * p) := by rw [← mul_sub]

lemma align_sends {p : ℍ} (hre : p.re = 0) (hn : normSq p = 1) (hneg : p ≠ -qI) :
    let raw := (1 : ℍ) - qI * p
    let s := Real.sqrt (normSq raw)
    star ((1 / s) • star raw) * p * ((1 / s) • star raw) = qI := by
  intro raw s
  have hpos : 0 < normSq raw := by
    dsimp [raw]
    exact align_raw_pos hre hn hneg
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = normSq raw := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt hpos)
  have hmul : raw * p = qI * raw := by
    dsimp [raw]
    exact raw_mul_eq hre hn
  have hself : raw * star raw = ⟨normSq raw, 0, 0, 0⟩ := by
    apply Quaternion.ext
    · simp [normSq_def]
    · simp; ring
    · simp; ring
    · simp; ring
  have hqI_real (n : ℝ) : qI * ⟨n, 0, 0, 0⟩ = n • qI := by
    apply Quaternion.ext <;> simp [qI]
  have real_smul_smul (r t : ℝ) (x : ℍ) : r • (t • x) = (r * t) • x := by
    apply Quaternion.ext <;> simp <;> ring
  have hc_left : ((1 / s) • raw) * p = (1 / s) • (raw * p) := by
    rw [← coe_mul_eq_smul, mul_assoc, coe_mul_eq_smul]
  have hc_right (x : ℍ) : x * ((1 / s) • star raw) = (1 / s) • (x * star raw) := by
    rw [← coe_mul_eq_smul]
    calc
      x * (↑(1 / s) * star raw) = x * (star raw * ↑(1 / s)) := by rw [coe_commutes]
      _ = x * star raw * ↑(1 / s) := by rw [← mul_assoc]
      _ = (1 / s) • (x * star raw) := mul_coe_eq_smul _ _
  have hscale : ((1 / s) • raw) * p * ((1 / s) • star raw) =
      ((1 / s) * (1 / s) * normSq raw) • qI := by
    calc
      ((1 / s) • raw) * p * ((1 / s) • star raw) =
          ((1 / s) • (raw * p)) * ((1 / s) • star raw) := by rw [hc_left]
      _ = ((1 / s) • (qI * raw)) * ((1 / s) • star raw) := by rw [hmul]
      _ = (1 / s) • ((qI * raw) * ((1 / s) • star raw)) := by
        rw [← coe_mul_eq_smul, mul_assoc, coe_mul_eq_smul]
      _ = (1 / s) • ((1 / s) • ((qI * raw) * star raw)) := by rw [hc_right]
      _ = ((1 / s) * (1 / s)) • (qI * (raw * star raw)) := by
        rw [mul_assoc, real_smul_smul]
      _ = ((1 / s) * (1 / s)) • (normSq raw • qI) := by
        rw [hself, hqI_real]
      _ = ((1 / s) * (1 / s) * normSq raw) • qI := by
        rw [real_smul_smul]
  have hstar : star ((1 / s) • star raw) = (1 / s) • raw := by
    rw [Quaternion.star_smul, star_star]
  rw [hstar, hscale]
  have hcoef : (1 / s) * (1 / s) * normSq raw = 1 := by
    field_simp [hspos.ne']
    linarith
  rw [hcoef, one_smul]

/-- Right rotation carrying the imaginary part onto the positive `I` axis. -/
theorem exists_align (q : ℍ) :
    ∃ h : S3, (star h.val * q * h.val).re = q.re ∧
      (star h.val * q * h.val).imJ = 0 ∧
      (star h.val * q * h.val).imK = 0 ∧
      0 ≤ (star h.val * q * h.val).imI := by
  classical
  by_cases hs : imNormSq q = 0
  · refine ⟨1, ?_⟩
    have hI : q.imI = 0 := by
      unfold imNormSq at hs
      nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hJ : q.imJ = 0 := by
      unfold imNormSq at hs
      nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hK : q.imK = 0 := by
      unfold imNormSq at hs
      nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    simp [one_val, star_one, hJ, hK, hI]
  · set s : ℝ := Real.sqrt (imNormSq q)
    have hspos : 0 < s := Real.sqrt_pos.mpr
      (lt_of_le_of_ne (imNormSq_nonneg q) (by
        intro h0
        exact hs h0.symm))
    have hs2 : s ^ 2 = imNormSq q := Real.sq_sqrt (imNormSq_nonneg q)
    set pure : ℍ := ⟨0, q.imI / s, q.imJ / s, q.imK / s⟩
    have hre : pure.re = 0 := rfl
    have hpure : normSq pure = 1 := by
      rw [normSq_def']
      simp only [pure]
      have : (q.imI / s) ^ 2 + (q.imJ / s) ^ 2 + (q.imK / s) ^ 2 = 1 := by
        field_simp [hspos.ne']
        unfold imNormSq at hs2
        linarith
      simpa [normSq_def'] using this
    have hdec : q = (q.re : ℍ) + s • pure := by
      ext
      · simp [pure]
      · simp [pure]; field_simp [hspos.ne']
      · simp [pure]; field_simp [hspos.ne']
      · simp [pure]; field_simp [hspos.ne']
    by_cases hneg : pure = -qI
    · let sJ : S3 := ⟨qJ, by rw [normSq_def']; simp [qJ]⟩
      refine ⟨sJ, ?_⟩
      have hpure' : star sJ.val * pure * sJ.val = qI := by
        simpa [sJ, hneg] using qJ_sends_negI
      have hw : star sJ.val * q * sJ.val = (q.re : ℍ) + s • qI := by
        calc
          star sJ.val * q * sJ.val =
              star sJ.val * ((q.re : ℍ) + s • pure) * sJ.val := by
            exact congrArg (fun z => star sJ.val * z * sJ.val) hdec
          _ = star sJ.val * (q.re : ℍ) * sJ.val +
              star sJ.val * (s • pure) * sJ.val := by
            rw [mul_add, add_mul]
          _ = (q.re : ℍ) + s • (star sJ.val * pure * sJ.val) := by
            rw [conj_coe, conj_smul]
          _ = (q.re : ℍ) + s • qI := by rw [hpure']
      have hw' : star sJ.val * q * sJ.val = ⟨q.re, s, 0, 0⟩ := by
        rw [hw]
        apply Quaternion.ext <;> simp [qI]
      rw [hw']
      exact ⟨rfl, rfl, rfl, le_of_lt hspos⟩
    · have hrawpos : 0 < normSq ((1 : ℍ) - qI * pure) := align_raw_pos hre hpure hneg
      let h : S3 := unitOf (star ((1 : ℍ) - qI * pure)) (by
        rw [normSq_star]
        exact hrawpos.ne')
      refine ⟨h, ?_⟩
      have hsent : star h.val * pure * h.val = qI := by
        have hs_eq : Real.sqrt (normSq (star ((1 : ℍ) - qI * pure))) =
            Real.sqrt (normSq ((1 : ℍ) - qI * pure)) := by rw [normSq_star]
        simp only [h, unitOf, hs_eq]
        exact align_sends hre hpure hneg
      have hw : star h.val * q * h.val = (q.re : ℍ) + s • qI := by
        calc
          star h.val * q * h.val =
              star h.val * ((q.re : ℍ) + s • pure) * h.val := by
            exact congrArg (fun z => star h.val * z * h.val) hdec
          _ = star h.val * (q.re : ℍ) * h.val + star h.val * (s • pure) * h.val := by
            rw [mul_add, add_mul]
          _ = (q.re : ℍ) + s • (star h.val * pure * h.val) := by
            rw [conj_coe, conj_smul]
          _ = (q.re : ℍ) + s • qI := by rw [hsent]
      have hw' : star h.val * q * h.val = ⟨q.re, s, 0, 0⟩ := by
        rw [hw]
        apply Quaternion.ext <;> simp [qI]
      rw [hw']
      exact ⟨rfl, rfl, rfl, le_of_lt hspos⟩

def plane (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : S3 where
  val := ⟨c, s, 0, 0⟩
  norm_one := by rw [normSq_def']; simp [hcs]

lemma plane_val (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (plane c s hcs).val = ⟨c, s, 0, 0⟩ := rfl

lemma plane_fixes_axis (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (a : S3)
    (haJ : a.val.imJ = 0) (haK : a.val.imK = 0) :
    (plane c s hcs)⁻¹ * a * plane c s hcs = a := by
  apply S3.ext
  have hv : ((plane c s hcs)⁻¹ * a * plane c s hcs).val =
      star (⟨c, s, 0, 0⟩ : ℍ) * a.val * ⟨c, s, 0, 0⟩ := by
    simp [mul_val, inv_val, plane_val]
  rw [hv, conj_plane c s a.val hcs]
  apply Quaternion.ext <;> simp [haJ, haK]

/-- Two electrons relative to a nucleus placed at the identity. -/
@[ext]
structure Frame where
  elecA : S3
  elecB : S3

def toFrame (n a b : S3) : Frame where
  elecA := relative n a
  elecB := relative n b

theorem toFrame_left (g n a b : S3) : toFrame (g * n) (g * a) (g * b) = toFrame n a b := by
  simp [toFrame, relative_left]

def ee (p : Frame) : S3 := relative p.elecA p.elecB

theorem ee_toFrame (n a b : S3) : ee (toFrame n a b) = relative a b := by
  simp only [ee, toFrame, relative]
  exact relative_left n⁻¹ a b

theorem relative_inv (a b : S3) : (relative a b)⁻¹ = relative b a := by
  simp [relative, mul_inv_rev, inv_inv]

def exchange (p : Frame) : Frame where
  elecA := p.elecB
  elecB := p.elecA

theorem exchange_exchange (p : Frame) : exchange (exchange p) = p := by
  cases p
  simp [exchange]

theorem ee_exchange (p : Frame) : ee (exchange p) = (ee p)⁻¹ := by
  simp [ee, exchange, relative_inv]

theorem re_inv (a : S3) : (a⁻¹).val.re = a.val.re := by
  simp [inv_val]

def conjFrame (h : S3) (p : Frame) : Frame where
  elecA := h⁻¹ * p.elecA * h
  elecB := h⁻¹ * p.elecB * h

theorem conjFrame_mul (h₁ h₂ : S3) (p : Frame) :
    conjFrame h₂ (conjFrame h₁ p) = conjFrame (h₁ * h₂) p := by
  ext <;> simp [conjFrame, mul_inv_rev, mul_assoc]

theorem toFrame_right (n a b h : S3) :
    toFrame (n * h) (a * h) (b * h) = conjFrame h (toFrame n a b) := by
  simp [toFrame, conjFrame, relative_right]

def cosA (p : Frame) : ℝ := p.elecA.val.re

def cosB (p : Frame) : ℝ := p.elecB.val.re

def cosEE (p : Frame) : ℝ := (ee p).val.re

theorem cos_exchange (p : Frame) :
    cosA (exchange p) = cosB p ∧ cosB (exchange p) = cosA p ∧
      cosEE (exchange p) = cosEE p := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cosA, cosB, exchange]
  · simp [cosA, cosB, exchange]
  · simp [cosEE, ee_exchange]

theorem ee_conj (h : S3) (p : Frame) : ee (conjFrame h p) = h⁻¹ * ee p * h := by
  simp only [ee, conjFrame]
  have hA : h⁻¹ * p.elecA * h = h⁻¹ * (p.elecA * h) := by rw [mul_assoc]
  have hB : h⁻¹ * p.elecB * h = h⁻¹ * (p.elecB * h) := by rw [mul_assoc]
  rw [hA, hB, relative_left, relative_right]

theorem cos_conj (h : S3) (p : Frame) :
    cosA (conjFrame h p) = cosA p ∧ cosB (conjFrame h p) = cosB p ∧
      cosEE (conjFrame h p) = cosEE p := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [cosA, conjFrame, mul_val, inv_val] using re_conj h p.elecA.val
  · simpa [cosB, conjFrame, mul_val, inv_val] using re_conj h p.elecB.val
  · rw [cosEE, cosEE, ee_conj]
    simpa [mul_val, inv_val] using re_conj h (ee p).val

/-- Axis form. If the first element is real, the second lies on the same axis. -/
def IsNormal (p : Frame) : Prop :=
  p.elecA.val.imJ = 0 ∧ p.elecA.val.imK = 0 ∧ 0 ≤ p.elecA.val.imI ∧
    p.elecB.val.imK = 0 ∧
    (p.elecA.val.imI = 0 → p.elecB.val.imJ = 0 ∧ 0 ≤ p.elecB.val.imI) ∧
    (p.elecA.val.imI ≠ 0 → 0 ≤ p.elecB.val.imJ)

lemma aligned_unique {a b : S3}
    (haJ : a.val.imJ = 0) (haK : a.val.imK = 0) (haI : 0 ≤ a.val.imI)
    (hbJ : b.val.imJ = 0) (hbK : b.val.imK = 0) (hbI : 0 ≤ b.val.imI)
    (hre : a.val.re = b.val.re) : a = b := by
  apply S3.ext
  ext
  · exact hre
  · have ha := imNormSq_of_unit a
    have hb := imNormSq_of_unit b
    unfold imNormSq at ha hb
    rw [haJ, haK] at ha
    rw [hbJ, hbK] at hb
    have ha2 : a.val.imI ^ 2 = 1 - a.val.re ^ 2 := by nlinarith [ha]
    have hb2 : b.val.imI ^ 2 = 1 - b.val.re ^ 2 := by nlinarith [hb]
    have hsq : a.val.imI ^ 2 = b.val.imI ^ 2 := by rw [ha2, hb2, hre]
    have hdiff : (a.val.imI - b.val.imI) * (a.val.imI + b.val.imI) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hdiff with h | h
    · linarith
    · linarith
  · exact haJ.trans hbJ.symm
  · exact haK.trans hbK.symm

lemma cosEE_axis {p : Frame} (haJ : p.elecA.val.imJ = 0) (haK : p.elecA.val.imK = 0) :
    cosEE p = cosA p * cosB p + p.elecA.val.imI * p.elecB.val.imI := by
  simp only [cosEE, ee, relative, cosA, cosB, mul_val, inv_val, re_mul, re_star, imI_star,
    imJ_star, imK_star, haJ, haK]
  ring

theorem normal_unique {p q : Frame} (hp : IsNormal p) (hq : IsNormal q)
    (hA : cosA p = cosA q) (hB : cosB p = cosB q) (hE : cosEE p = cosEE q) : p = q := by
  classical
  rcases hp with ⟨hpJ, hpK, hpI, hpBK, hp0, hp1⟩
  rcases hq with ⟨hqJ, hqK, hqI, hqBK, hq0, hq1⟩
  have hAe : p.elecA = q.elecA :=
    aligned_unique hpJ hpK hpI hqJ hqK hqI hA
  have hEp := cosEE_axis (p := p) hpJ hpK
  have hEq := cosEE_axis (p := q) hqJ hqK
  have hIm : p.elecA.val.imI = q.elecA.val.imI := by
    have := congrArg (fun a : S3 => a.val.imI) hAe
    simpa using this
  by_cases hzero : p.elecA.val.imI = 0
  · have hzeroq : q.elecA.val.imI = 0 := by rw [← hIm, hzero]
    obtain ⟨hpBJ, hpBI⟩ := hp0 hzero
    obtain ⟨hqBJ, hqBI⟩ := hq0 hzeroq
    have hBe : p.elecB = q.elecB :=
      aligned_unique hpBJ hpBK hpBI hqBJ hqBK hqBI hB
    exact Frame.ext hAe hBe
  · have hzeroq : q.elecA.val.imI ≠ 0 := by
      intro h
      apply hzero
      rw [hIm, h]
    have hpBJ : 0 ≤ p.elecB.val.imJ := hp1 hzero
    have hqBJ : 0 ≤ q.elecB.val.imJ := hq1 hzeroq
    have hbi : p.elecB.val.imI = q.elecB.val.imI := by
      have hlinp : p.elecA.val.imI * p.elecB.val.imI =
          cosEE p - cosA p * cosB p := by linarith [hEp]
      have hlinq : q.elecA.val.imI * q.elecB.val.imI =
          cosEE q - cosA q * cosB q := by linarith [hEq]
      have hnum : p.elecA.val.imI * p.elecB.val.imI =
          q.elecA.val.imI * q.elecB.val.imI := by rw [hlinp, hlinq, hA, hB, hE]
      rw [hIm] at hnum
      exact mul_left_cancel₀ hzeroq hnum
    have hbj2 : p.elecB.val.imJ ^ 2 = q.elecB.val.imJ ^ 2 := by
      have hpN := imNormSq_of_unit p.elecB
      have hqN := imNormSq_of_unit q.elecB
      unfold imNormSq at hpN hqN
      rw [hpBK] at hpN
      rw [hqBK] at hqN
      have hp2 : p.elecB.val.imJ ^ 2 =
          1 - p.elecB.val.re ^ 2 - p.elecB.val.imI ^ 2 := by linarith
      have hq2 : q.elecB.val.imJ ^ 2 =
          1 - q.elecB.val.re ^ 2 - q.elecB.val.imI ^ 2 := by linarith
      have hreB : q.elecB.val.re = p.elecB.val.re := by simpa [cosB] using hB.symm
      rw [hreB, hbi.symm] at hq2
      linarith
    have hbj : p.elecB.val.imJ = q.elecB.val.imJ := by
      have hdiff : (p.elecB.val.imJ - q.elecB.val.imJ) *
          (p.elecB.val.imJ + q.elecB.val.imJ) = 0 := by linarith
      rcases mul_eq_zero.mp hdiff with h | h
      · linarith
      · linarith
    have hBe : p.elecB = q.elecB := by
      apply S3.ext
      ext
      · exact hB
      · exact hbi
      · exact hbj
      · rw [hpBK, hqBK]
    exact Frame.ext hAe hBe

lemma exists_residual {a b : S3} (haJ : a.val.imJ = 0) (haK : a.val.imK = 0) :
    ∃ h : S3, h⁻¹ * a * h = a ∧
      ((h⁻¹ * b * h).val.imK = 0) ∧
      (a.val.imI = 0 → (h⁻¹ * b * h).val.imJ = 0 ∧ 0 ≤ (h⁻¹ * b * h).val.imI) ∧
      (a.val.imI ≠ 0 → 0 ≤ (h⁻¹ * b * h).val.imJ) := by
  classical
  by_cases hzero : a.val.imI = 0
  · obtain ⟨h, hre, hJ, hK, hI⟩ := exists_align b.val
    refine ⟨h, ?_, ?_, ?_, ?_⟩
    · apply S3.ext
      have ha : a.val = (a.val.re : ℍ) := by
        apply Quaternion.ext <;> simp [haJ, haK, hzero]
      rw [mul_val, mul_val, inv_val, ha]
      exact conj_coe h a.val.re
    · simpa [mul_val, inv_val] using hK
    · intro _
      refine ⟨?_, ?_⟩
      · simpa [mul_val, inv_val] using hJ
      · simpa [mul_val, inv_val] using hI
    · intro hne
      exact absurd hzero hne
  · set r : ℝ := Real.sqrt (b.val.imJ ^ 2 + b.val.imK ^ 2)
    by_cases hr : r = 0
    · refine ⟨1, ?_, ?_, ?_, ?_⟩
      · simp
      · have hsum : b.val.imJ ^ 2 + b.val.imK ^ 2 = 0 := by
          have := Real.sq_sqrt (add_nonneg (sq_nonneg b.val.imJ) (sq_nonneg b.val.imK))
          rw [← this]
          simp [r, hr]
        have hJ : b.val.imJ = 0 := by nlinarith [sq_nonneg b.val.imJ, sq_nonneg b.val.imK, hsum]
        have hK : b.val.imK = 0 := by nlinarith [sq_nonneg b.val.imJ, sq_nonneg b.val.imK, hsum]
        simp [hK]
      · intro hz
        exact absurd hz hzero
      · intro _
        have hsum : b.val.imJ ^ 2 + b.val.imK ^ 2 = 0 := by
          have := Real.sq_sqrt (add_nonneg (sq_nonneg b.val.imJ) (sq_nonneg b.val.imK))
          rw [← this]
          simp [r, hr]
        have hJ : b.val.imJ = 0 := by nlinarith [sq_nonneg b.val.imJ, sq_nonneg b.val.imK, hsum]
        simp [hJ]
    · have hrpos : 0 < r := lt_of_le_of_ne
        (Real.sqrt_nonneg (b.val.imJ ^ 2 + b.val.imK ^ 2)) (Ne.symm hr)
      set cφ : ℝ := b.val.imJ / r
      set sφ : ℝ := b.val.imK / r
      have hφ : cφ ^ 2 + sφ ^ 2 = 1 := by
        have hr2 : r ^ 2 = b.val.imJ ^ 2 + b.val.imK ^ 2 :=
          Real.sq_sqrt (add_nonneg (sq_nonneg b.val.imJ) (sq_nonneg b.val.imK))
        simp only [cφ, sφ]
        field_simp [hrpos.ne']
        nlinarith [hr2]
      have hφle : -1 ≤ cφ := by nlinarith [hφ, sq_nonneg sφ]
      set ct : ℝ := Real.sqrt ((1 + cφ) / 2)
      have hctnn : 0 ≤ (1 + cφ) / 2 := by linarith
      by_cases hct : ct = 0
      · have hcφ : cφ = -1 := by
          have hsq : ct ^ 2 = (1 + cφ) / 2 := Real.sq_sqrt hctnn
          rw [hct] at hsq
          linarith
        have hsφ : sφ = 0 := by nlinarith [hφ, hcφ]
        have hcs : (0 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = 1 := by norm_num
        refine ⟨plane 0 1 hcs, ?_, ?_, ?_, ?_⟩
        · exact plane_fixes_axis 0 1 hcs a haJ haK
        · have hvk : b.val.imK = 0 := by
            have : b.val.imK = sφ * r := by
              simp [sφ]
              field_simp [hrpos.ne']
            rw [this, hsφ, zero_mul]
          have hw := conj_plane 0 1 b.val hcs
          have hv : ((plane 0 1 hcs)⁻¹ * b * plane 0 1 hcs).val =
              star (⟨0, 1, 0, 0⟩ : ℍ) * b.val * ⟨0, 1, 0, 0⟩ := by
            simp [mul_val, inv_val, plane_val]
          rw [hv, hw, hvk]
          simp
        · intro hz
          exact absurd hz hzero
        · intro _
          have hvj : b.val.imJ = -r := by
            have : b.val.imJ = cφ * r := by
              simp only [cφ]
              field_simp [hrpos.ne']
            rw [this, hcφ]
            ring
          have hvk0 : b.val.imK = 0 := by
            have : b.val.imK = sφ * r := by
              simp only [sφ]
              field_simp [hrpos.ne']
            rw [this, hsφ, zero_mul]
          have hv : ((plane 0 1 hcs)⁻¹ * b * plane 0 1 hcs).val =
              ⟨b.val.re, b.val.imI, -b.val.imJ, -b.val.imK⟩ := by
            have hw := conj_plane 0 1 b.val hcs
            have hval : ((plane 0 1 hcs)⁻¹ * b * plane 0 1 hcs).val =
                star (⟨0, 1, 0, 0⟩ : ℍ) * b.val * ⟨0, 1, 0, 0⟩ := by
              simp [mul_val, inv_val, plane_val]
            rw [hval, hw]
            apply Quaternion.ext <;> simp
          rw [hv, hvj, hvk0]
          simpa using (le_of_lt hrpos)
      · set st : ℝ := sφ / (2 * ct)
        have hct2 : ct ^ 2 = (1 + cφ) / 2 := Real.sq_sqrt hctnn
        have hst_mul : st * (2 * ct) = sφ := by
          simp only [st]
          field_simp [hct]
        have hst2 : st ^ 2 = (1 - cφ) / 2 := by
          have hden : 1 + cφ ≠ 0 := by
            intro h0
            apply hct
            rw [Real.sqrt_eq_zero hctnn]
            linarith
          have : (2 * ct) ^ 2 * st ^ 2 = sφ ^ 2 := by
            calc
              (2 * ct) ^ 2 * st ^ 2 = (st * (2 * ct)) ^ 2 := by ring
              _ = sφ ^ 2 := by rw [hst_mul]
          have hφ2 : sφ ^ 2 = (1 - cφ) * (1 + cφ) := by nlinarith [hφ]
          have hctφ : (2 * ct) ^ 2 = 2 * (1 + cφ) := by
            calc
              (2 * ct) ^ 2 = 4 * ct ^ 2 := by ring
              _ = 4 * ((1 + cφ) / 2) := by rw [hct2]
              _ = 2 * (1 + cφ) := by ring
          have : 2 * (1 + cφ) * st ^ 2 = (1 - cφ) * (1 + cφ) := by
            rw [← hctφ, this, hφ2]
          have hcancel := congrArg (fun t => t / (1 + cφ)) this
          field_simp [hden] at hcancel
          linarith
        have hcs : ct ^ 2 + st ^ 2 = 1 := by linarith [hct2, hst2]
        have hdiff : ct ^ 2 - st ^ 2 = cφ := by linarith [hct2, hst2]
        have hcross : 2 * st * ct = sφ := by
          have : 2 * st * ct = st * (2 * ct) := by ring
          rw [this, hst_mul]
        refine ⟨plane ct st hcs, ?_, ?_, ?_, ?_⟩
        · exact plane_fixes_axis ct st hcs a haJ haK
        · have hw := conj_plane ct st b.val hcs
          have hv : ((plane ct st hcs)⁻¹ * b * plane ct st hcs).val =
              star (plane ct st hcs).val * b.val * (plane ct st hcs).val := by
            simp [mul_val, inv_val]
          rw [hv, plane_val, hw, hdiff, hcross]
          have hvj : b.val.imJ = cφ * r := by simp [cφ]; field_simp [hrpos.ne']
          have hvk : b.val.imK = sφ * r := by simp [sφ]; field_simp [hrpos.ne']
          rw [hvj, hvk]
          ring
        · intro hz
          exact absurd hz hzero
        · intro _
          have hw := conj_plane ct st b.val hcs
          have hv : ((plane ct st hcs)⁻¹ * b * plane ct st hcs).val =
              star (plane ct st hcs).val * b.val * (plane ct st hcs).val := by
            simp [mul_val, inv_val]
          rw [hv, plane_val, hw, hdiff, hcross]
          have hvj : b.val.imJ = cφ * r := by simp [cφ]; field_simp [hrpos.ne']
          have hvk : b.val.imK = sφ * r := by simp [sφ]; field_simp [hrpos.ne']
          have himJ : cφ * r * cφ + sφ * r * sφ = r := by
            have : cφ * cφ + sφ * sφ = 1 := by simpa [pow_two] using hφ
            calc
              cφ * r * cφ + sφ * r * sφ = r * (cφ * cφ + sφ * sφ) := by ring
              _ = r := by rw [this, mul_one]
          rw [hvj, hvk, himJ]
          exact le_of_lt hrpos

theorem exists_normal (p : Frame) : ∃ h : S3, IsNormal (conjFrame h p) := by
  obtain ⟨h₁, hre, hJ, hK, hI⟩ := exists_align p.elecA.val
  let a₁ : S3 := h₁⁻¹ * p.elecA * h₁
  let b₁ : S3 := h₁⁻¹ * p.elecB * h₁
  have ha₁ : a₁.val = star h₁.val * p.elecA.val * h₁.val := by simp [a₁, mul_val, inv_val]
  have haJ : a₁.val.imJ = 0 := by rw [ha₁]; exact hJ
  have haK : a₁.val.imK = 0 := by rw [ha₁]; exact hK
  have haI : 0 ≤ a₁.val.imI := by rw [ha₁]; exact hI
  obtain ⟨h₂, hfix, hBK, h0, h1⟩ := exists_residual (a := a₁) (b := b₁) haJ haK
  refine ⟨h₁ * h₂, ?_⟩
  have hpair : conjFrame h₁ p = ⟨a₁, b₁⟩ := by
    cases p
    simp [conjFrame, a₁, b₁]
  rw [(conjFrame_mul h₁ h₂ p).symm, hpair]
  have hA : (h₂⁻¹ * a₁ * h₂) = a₁ := hfix
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [conjFrame, hA] using haJ
  · simpa [conjFrame, hA] using haK
  · simpa [conjFrame, hA] using haI
  · simpa [conjFrame] using hBK
  · intro hz
    have him : a₁.val.imI = 0 := by simpa [conjFrame, hA] using hz
    simpa [conjFrame] using h0 him
  · intro hne
    have him : a₁.val.imI ≠ 0 := by
      intro hz
      exact hne (by simpa [conjFrame, hA] using hz)
    simpa [conjFrame] using h1 him

def Symmetric (F : Frame → ℂ) : Prop := ∀ p, F (exchange p) = F p

def Antisymmetric (F : Frame → ℂ) : Prop := ∀ p, F (exchange p) = -F p

def RotationInvariant (F : Frame → ℂ) : Prop := ∀ h p, F (conjFrame h p) = F p

/-- A rotation-invariant amplitude of the two elements is an amplitude of the
three cosines. -/
theorem rotationInvariant_eq_of_cos {F : Frame → ℂ} (hF : RotationInvariant F) {p q : Frame}
    (hA : cosA p = cosA q) (hB : cosB p = cosB q) (hE : cosEE p = cosEE q) : F p = F q := by
  obtain ⟨h₁, hn₁⟩ := exists_normal p
  obtain ⟨h₂, hn₂⟩ := exists_normal q
  have hc₁ := cos_conj h₁ p
  have hc₂ := cos_conj h₂ q
  have hsame := normal_unique hn₁ hn₂
    (hc₁.1.trans (hA.trans hc₂.1.symm))
    (hc₁.2.1.trans (hB.trans hc₂.2.1.symm))
    (hc₁.2.2.trans (hE.trans hc₂.2.2.symm))
  calc
    F p = F (conjFrame h₁ p) := (hF h₁ p).symm
    _ = F (conjFrame h₂ q) := by rw [hsame]
    _ = F q := hF h₂ q

/-- The symmetric rotation-invariant amplitudes are symmetric in the two angles
from the nucleus. -/
theorem symmetric_invariant_swap {F : Frame → ℂ} (hR : RotationInvariant F) (hS : Symmetric F)
    {p q : Frame} (hA : cosA p = cosB q) (hB : cosB p = cosA q) (hE : cosEE p = cosEE q) :
    F p = F q := by
  have hc := cos_exchange q
  have hF := rotationInvariant_eq_of_cos hR (p := p) (q := exchange q)
    (hA.trans hc.1.symm) (hB.trans hc.2.1.symm) (hE.trans hc.2.2.symm)
  rw [hF, hS]

theorem pairSwap_smul (c : ℂ) (Ψ : PairState) : pairSwap (c • Ψ) = c • pairSwap Ψ := by
  simp [pairSwap, Matrix.transpose_smul]

/-- Symmetric spatial amplitude times the singlet: joint exchange changes the sign. -/
theorem singlet_sector_exchange (F : Frame → ℂ) (hF : Symmetric F) (c : ℂ) (p : Frame) :
    F (exchange p) • pairSwap (c • singlet) = -(F p • (c • singlet)) := by
  rw [hF p, pairSwap_smul, pairSwap_singlet]
  simp [smul_neg]

theorem antisym_vanish {F : Frame → ℂ} (hF : Antisymmetric F) {p : Frame}
    (h : p.elecA = p.elecB) : F p = 0 := by
  have hex : exchange p = p := by
    cases p
    simp only [exchange]
    exact Frame.ext h.symm h
  have hneg : F p = -F p := by simpa [hex] using hF p
  have h2 : (2 : ℂ) * F p = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

theorem constant_symmetric : Symmetric (fun _ => (1 : ℂ)) := fun _ => rfl

theorem symmetric_nonzero_at_coincidence (p : Frame) (_h : p.elecA = p.elecB) :
    (fun _ : Frame => (1 : ℂ)) p ≠ 0 := by
  simp

end DstDiophantine.Gravity.HeliumBody
