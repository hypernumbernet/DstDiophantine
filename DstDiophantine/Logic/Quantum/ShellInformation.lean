import DstDiophantine.Logic.Quantum.PhaseInformation

/-!
# Phase information on one mass shell

`PhaseInformation` reads `I = V²` from two weights on one carrier. A nonzero mass forbids that
reading. `diracMomentum_unique` puts one nonzero spinor on one momentum, so two momenta on one
shell use two carriers.

The Born density of weights `r`, `s` and relative phase `α` is
`r² ‖u‖² + s² ‖v‖² + 2 r s Re(e^{i((q − p)·x + α)} ⟨u, v⟩)`.
The visibility of the cross term is at most the single-carrier visibility of the two Born weights,
and the ratio is the fidelity `|⟨u, v⟩| / (‖u‖ ‖v‖)`. Orthogonal carriers give information `0` and
no chart contrast. On a common shell the relative momentum is Minkowski-orthogonal to the mean
momentum. In the mean rest frame that relative momentum is spatial, so the fringe does not move
under a time translation.

The number is still not a location, and it is not a Newton–Wigner operator. A shared carrier with
equal weights has `I = 1` and is not a pair of Dirac solutions of one nonzero mass. On the shell
`Q = -9`, the mean-rest pair with a common Weyl seed has information `81/625`.
-/

namespace DstDiophantine

namespace Logic

open Complex

/-! ### The relative momentum is orthogonal to the mean momentum -/

/-- Minkowski polar form `η(p, q)`. -/
def minkowskiPolar (p q : Vec4) : ℝ :=
  ∑ μ : Fin 4, minkowskiEta μ μ * p μ * q μ

theorem minkowskiPolar_sub_add (p q : Vec4) :
    minkowskiPolar (q - p) (q + p) = minkowskiQ q - minkowskiQ p := by
  unfold minkowskiPolar minkowskiQ
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

theorem sameShell_polar_ortho {p q : Vec4} {c : ℝ}
    (hp : minkowskiQ p = c) (hq : minkowskiQ q = c) :
    minkowskiPolar (q - p) (q + p) = 0 := by
  rw [minkowskiPolar_sub_add, hq, hp, sub_self]

/-- The mean momentum has no spatial part. -/
def MeanRestFrame (p q : Vec4) : Prop :=
  (p + q) 1 = 0 ∧ (p + q) 2 = 0 ∧ (p + q) 3 = 0

theorem sameShell_meanRest_timeComponent {p q : Vec4}
    (hQ : minkowskiQ p = minkowskiQ q) (hrest : MeanRestFrame p q)
    (h0 : (p + q) 0 ≠ 0) : (q - p) 0 = 0 := by
  have hpolar : minkowskiPolar (q - p) (q + p) = 0 :=
    sameShell_polar_ortho hQ rfl
  unfold minkowskiPolar at hpolar
  simp only [Fin.sum_univ_four, minkowskiEta_diag, w31, Pi.add_apply, Pi.sub_apply] at hpolar
  have h1 : q 1 + p 1 = 0 := by simpa [Pi.add_apply, add_comm] using hrest.1
  have h2 : q 2 + p 2 = 0 := by simpa [Pi.add_apply, add_comm] using hrest.2.1
  have h3 : q 3 + p 3 = 0 := by simpa [Pi.add_apply, add_comm] using hrest.2.2
  have htime : q 0 + p 0 = (p + q) 0 := by simp [Pi.add_apply, add_comm]
  rw [h1, h2, h3] at hpolar
  simp only [mul_zero, add_zero] at hpolar
  have hsub0 : (q - p) 0 = q 0 - p 0 := by simp [Pi.sub_apply]
  have hprod : (q 0 - p 0) * (q 0 + p 0) = 0 := by
    nlinarith
  rw [htime] at hprod
  rw [hsub0]
  exact (mul_eq_zero.mp hprod).resolve_right h0

/-- Displacement along the chart time axis. -/
def timeShift (t : ℝ) : Vec4 :=
  Pi.single 0 t

theorem wavePhase_timeShift {δ : Vec4} (h0 : δ 0 = 0) (t : ℝ) (x : Vec4) :
    wavePhase δ (x + timeShift t) = wavePhase δ x := by
  rw [wavePhase_add_right]
  have hsingle : timeShift t = t • Pi.single 0 (1 : ℝ) := by
    ext μ
    fin_cases μ <;> simp [timeShift]
  rw [hsingle, wavePhase_smul_right, wavePhase_single, h0, mul_zero, add_zero]

/-! ### Two carriers -/

/-- Modulus of the carrier inner product. -/
noncomputable def carrierOverlap (u v : DiracSpinor) : ℝ :=
  ‖inner ℂ u v‖

/-- Fidelity `|⟨u, v⟩| / (‖u‖ ‖v‖)`. The Lean zero when either carrier vanishes. -/
noncomputable def carrierFidelity (u v : DiracSpinor) : ℝ :=
  carrierOverlap u v / (‖u‖ * ‖v‖)

theorem carrierFidelity_nonneg (u v : DiracSpinor) : 0 ≤ carrierFidelity u v := by
  unfold carrierFidelity carrierOverlap
  exact div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem carrierFidelity_le_one (u v : DiracSpinor) : carrierFidelity u v ≤ 1 := by
  unfold carrierFidelity carrierOverlap
  by_cases h : ‖u‖ * ‖v‖ = 0
  · simp [h]
  · rw [div_le_one (lt_of_le_of_ne (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm h))]
    exact norm_inner_le_norm u v

theorem carrierFidelity_self {u : DiracSpinor} (hu : u ≠ 0) : carrierFidelity u u = 1 := by
  unfold carrierFidelity carrierOverlap
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
  field_simp [norm_ne_zero_iff.mpr hu]

/-- `r` on `(p, u)`, weight `s` and phase `α` on `(q, v)`. -/
noncomputable def shellPacket (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) :
    Vec4 → DiracSpinor :=
  fun x => (r : ℂ) • planeWave p u x +
    ((s : ℂ) * exp (I * (α : ℂ))) • planeWave q v x

/-- Born weight `c² ‖u‖²` of one plane wave. -/
noncomputable def shellWeight (c : ℝ) (u : DiracSpinor) : ℝ :=
  c ^ 2 * ‖u‖ ^ 2

private theorem star_exp_I (θ : ℝ) :
    star (exp (I * (θ : ℂ))) = exp (I * ((-θ) : ℂ)) := by
  rw [Complex.star_def, ← exp_conj]
  congr 1
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

private theorem phase_coefficient (r s α : ℝ) (p q x : Vec4) :
    starRingEnd ℂ ((r : ℂ) * exp (I * (wavePhase p x : ℂ))) *
        ((s : ℂ) * exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ))) =
      ((r * s : ℝ) : ℂ) * exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) := by
  rw [starRingEnd_apply, star_mul, star_exp_I, Complex.star_def, Complex.conj_ofReal,
    mul_comm (exp (I * ((-wavePhase p x) : ℂ))) (r : ℂ)]
  have hexp :
      exp (I * ((-wavePhase p x) : ℂ)) * exp (I * (α : ℂ)) *
          exp (I * (wavePhase q x : ℂ)) =
        exp (I * (((-wavePhase p x) + α + wavePhase q x : ℝ) : ℂ)) := by
    rw [← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  calc
    (r : ℂ) * exp (I * ((-wavePhase p x) : ℂ)) *
        ((s : ℂ) * exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ)))
      = ((r * s : ℝ) : ℂ) *
          (exp (I * ((-wavePhase p x) : ℂ)) * exp (I * (α : ℂ)) *
            exp (I * (wavePhase q x : ℂ))) := by
        push_cast
        ring
    _ = ((r * s : ℝ) : ℂ) *
          exp (I * (((-wavePhase p x) + α + wavePhase q x : ℝ) : ℂ)) := by
        rw [hexp]
    _ = ((r * s : ℝ) : ℂ) * exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) := by
        rw [show (((-wavePhase p x) + α + wavePhase q x : ℝ) : ℂ) =
            (wavePhase (q - p) x : ℂ) + (α : ℂ) by
          rw [wavePhase_sub_left]
          push_cast
          ring]

theorem bornDensity_shellPacket (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (x : Vec4) :
    bornDensity (shellPacket r s α p q u v) x =
      shellWeight r u + shellWeight s v +
        2 * r * s *
          (exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) * inner ℂ u v).re := by
  unfold bornDensity shellPacket shellWeight
  set zp : ℂ := (r : ℂ) * exp (I * (wavePhase p x : ℂ))
  set zq : ℂ := (s : ℂ) * exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ))
  have hψ :
      (r : ℂ) • planeWave p u x + ((s : ℂ) * exp (I * (α : ℂ))) • planeWave q v x =
        zp • u + zq • v := by
    unfold planeWave zp zq
    rw [smul_smul, smul_smul]
  rw [hψ, norm_add_sq (𝕜 := ℂ)]
  have hzpu : ‖zp • u‖ ^ 2 = r ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul, mul_pow]
    have hz : ‖zp‖ ^ 2 = r ^ 2 := by
      unfold zp
      have hr : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r
      rw [norm_mul, norm_exp_I, mul_one, hr, sq_abs]
    rw [hz]
  have hzqv : ‖zq • v‖ ^ 2 = s ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, mul_pow]
    have hz : ‖zq‖ ^ 2 = s ^ 2 := by
      unfold zq
      have hs : ‖(s : ℂ)‖ = |s| := RCLike.norm_ofReal s
      rw [norm_mul, norm_mul, norm_exp_I, norm_exp_I, mul_one, mul_one, hs, sq_abs]
    rw [hz]
  have hre : RCLike.re (inner ℂ (zp • u) (zq • v)) =
      r * s * (exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) * inner ℂ u v).re := by
    unfold zp zq
    rw [inner_smul_left, inner_smul_right]
    rw [← mul_assoc (starRingEnd ℂ ((r : ℂ) * exp (I * (wavePhase p x : ℂ))))
        (((s : ℂ) * exp (I * (α : ℂ))) * exp (I * (wavePhase q x : ℂ)))
        (inner ℂ u v)]
    have hphase :
        (starRingEnd ℂ ((r : ℂ) * exp (I * (wavePhase p x : ℂ))) *
            ((s : ℂ) * exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ)))) *
            inner ℂ u v =
          (((r * s : ℝ) : ℂ) *
              exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ)))) *
            inner ℂ u v := by
      conv_lhs =>
        arg 1
        rw [phase_coefficient r s α p q x]
    rw [hphase, mul_assoc]
    exact RCLike.re_ofReal_mul (r * s)
      (exp (I * ((wavePhase (q - p) x : ℂ) + (α : ℂ))) * inner ℂ u v)
  rw [hzpu, hzqv, hre]
  ring

/-! ### Visibility, fidelity, and the single-carrier bound -/

/-- Amplitude of the cross term over the sum of the Born weights. -/
noncomputable def shellVisibility (r s : ℝ) (u v : DiracSpinor) : ℝ :=
  2 * |r| * |s| * carrierOverlap u v / (shellWeight r u + shellWeight s v)

/-- Phase information of a two-carrier packet: the square of `shellVisibility`. -/
noncomputable def shellInformation (r s : ℝ) (u v : DiracSpinor) : ℝ :=
  shellVisibility r s u v ^ 2

private theorem phaseInformation_abs (a b : ℝ) :
    phaseInformation |a| |b| = phaseInformation a b := by
  by_cases h : a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    simp [ha, hb, phaseInformation, momentumVariance, momentumShare]
  · have h2 : |a| ^ 2 + |b| ^ 2 ≠ 0 := by simpa [sq_abs] using h
    rw [phaseInformation_eq _ _ h2, phaseInformation_eq _ _ h]
    simp [sq_abs]

private theorem phaseInformation_smul (c a b : ℝ) (hc : c ≠ 0) :
    phaseInformation (c * a) (c * b) = phaseInformation a b := by
  by_cases h : a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    simp [ha, hb, phaseInformation, momentumVariance, momentumShare]
  · have h2 : (c * a) ^ 2 + (c * b) ^ 2 ≠ 0 := by
      have hprod : (c * a) ^ 2 + (c * b) ^ 2 = c ^ 2 * (a ^ 2 + b ^ 2) := by ring
      rw [hprod]
      exact mul_ne_zero (pow_ne_zero 2 hc) h
    rw [phaseInformation_eq _ _ h2, phaseInformation_eq _ _ h]
    field_simp [hc, h]

theorem shellInformation_eq_fidelity_sq (r s : ℝ) (u v : DiracSpinor) :
    shellInformation r s u v =
      carrierFidelity u v ^ 2 * phaseInformation (|r| * ‖u‖) (|s| * ‖v‖) := by
  set a : ℝ := |r| * ‖u‖
  set b : ℝ := |s| * ‖v‖
  have hden_ab : a ^ 2 + b ^ 2 = r ^ 2 * ‖u‖ ^ 2 + s ^ 2 * ‖v‖ ^ 2 := by
    simp only [a, b, mul_pow, sq_abs]
  by_cases hden : a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    have hv0 : shellVisibility r s u v = 0 := by
      unfold shellVisibility shellWeight
      rw [← hden_ab, hden, div_zero]
    rw [shellInformation, hv0, sq, zero_mul]
    simp [ha, hb, carrierFidelity, phaseInformation, momentumVariance, momentumShare]
  · rw [shellInformation, phaseInformation_eq_visibility_sq a b hden]
    unfold shellVisibility shellWeight carrierFidelity carrierOverlap
    rw [← hden_ab]
    have hfr : fringeVisibility a b = 2 * a * b / (a ^ 2 + b ^ 2) := rfl
    rw [hfr]
    by_cases hprod : ‖u‖ * ‖v‖ = 0
    · have hov : ‖inner ℂ u v‖ = 0 := by
        rcases mul_eq_zero.mp hprod with hu0 | hv0
        · simp [norm_eq_zero.mp hu0]
        · simp [norm_eq_zero.mp hv0]
      simp [hov, hprod]
    · have hcoeff : ‖inner ℂ u v‖ * (2 * a * b) =
          (‖u‖ * ‖v‖) * (2 * |r| * |s| * ‖inner ℂ u v‖) := by
        simp only [a, b]
        ring
      have hmain :
          2 * |r| * |s| * ‖inner ℂ u v‖ / (a ^ 2 + b ^ 2) =
            (‖inner ℂ u v‖ / (‖u‖ * ‖v‖)) * (2 * a * b / (a ^ 2 + b ^ 2)) := by
        symm
        calc
          (‖inner ℂ u v‖ / (‖u‖ * ‖v‖)) * (2 * a * b / (a ^ 2 + b ^ 2))
              = (‖inner ℂ u v‖ * (2 * a * b)) / ((‖u‖ * ‖v‖) * (a ^ 2 + b ^ 2)) := by
                rw [div_mul_div_comm]
          _ = ((‖u‖ * ‖v‖) * (2 * |r| * |s| * ‖inner ℂ u v‖)) /
                ((‖u‖ * ‖v‖) * (a ^ 2 + b ^ 2)) := by
                rw [hcoeff]
          _ = 2 * |r| * |s| * ‖inner ℂ u v‖ / (a ^ 2 + b ^ 2) := by
                rw [mul_div_mul_left _ _ hprod]
      rw [hmain, mul_pow]

theorem shellInformation_same_carrier (r s : ℝ) {u : DiracSpinor} (hu : u ≠ 0) :
    shellInformation r s u u = phaseInformation r s := by
  rw [shellInformation_eq_fidelity_sq, carrierFidelity_self hu, one_pow, one_mul]
  rw [show |r| * ‖u‖ = ‖u‖ * |r| by ring, show |s| * ‖u‖ = ‖u‖ * |s| by ring,
    phaseInformation_smul ‖u‖ |r| |s| (norm_ne_zero_iff.mpr hu), phaseInformation_abs]

theorem shellInformation_le_phaseInformation (r s : ℝ) (u v : DiracSpinor) :
    shellInformation r s u v ≤ phaseInformation (|r| * ‖u‖) (|s| * ‖v‖) := by
  rw [shellInformation_eq_fidelity_sq]
  have hf := carrierFidelity_le_one u v
  have h0 := carrierFidelity_nonneg u v
  have hI := phaseInformation_nonneg (|r| * ‖u‖) (|s| * ‖v‖)
  have hsq : carrierFidelity u v ^ 2 ≤ 1 := by nlinarith
  simpa using mul_le_mul_of_nonneg_right hsq hI

theorem shellVisibility_le_one (r s : ℝ) (u v : DiracSpinor) :
    shellVisibility r s u v ≤ 1 := by
  unfold shellVisibility shellWeight carrierOverlap
  set den := r ^ 2 * ‖u‖ ^ 2 + s ^ 2 * ‖v‖ ^ 2
  by_cases hden : den = 0
  · simp [hden]
  · have hpos : 0 < den :=
      lt_of_le_of_ne (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))) (Ne.symm hden)
    rw [div_le_one hpos]
    have hcs : ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
    have hnum : 2 * |r| * |s| * ‖inner ℂ u v‖ ≤ 2 * |r| * |s| * (‖u‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    have hAm : 2 * (|r| * ‖u‖) * (|s| * ‖v‖) ≤ (|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2 := by
      nlinarith [sq_nonneg (|r| * ‖u‖ - |s| * ‖v‖)]
    have hden_ab : (|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2 = den := by
      simp only [den, mul_pow, sq_abs]
    have hprod : 2 * |r| * |s| * (‖u‖ * ‖v‖) = 2 * (|r| * ‖u‖) * (|s| * ‖v‖) := by ring
    linarith

theorem shellInformation_le_one (r s : ℝ) (u v : DiracSpinor) :
    shellInformation r s u v ≤ 1 := by
  by_cases h : (|r| * ‖u‖) ^ 2 + (|s| * ‖v‖) ^ 2 = 0
  · rw [shellInformation_eq_fidelity_sq]
    have ha : |r| * ‖u‖ = 0 := by nlinarith [sq_nonneg (|s| * ‖v‖)]
    have hb : |s| * ‖v‖ = 0 := by nlinarith [sq_nonneg (|r| * ‖u‖)]
    simp [ha, hb, phaseInformation, momentumVariance, momentumShare]
  · exact le_trans (shellInformation_le_phaseInformation r s u v)
      (phaseInformation_le_one _ _ h)

/-! ### The cross term is the chart reading -/

private theorem re_exp_mul (θ : ℝ) (z : ℂ) :
    (exp (I * (θ : ℂ)) * z).re = Real.cos θ * z.re - Real.sin θ * z.im := by
  rw [show I * (θ : ℂ) = (θ : ℂ) * I by ring, exp_mul_I, mul_re, Complex.add_re, Complex.mul_re,
    Complex.add_im, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem align_overlap (z : ℂ) :
    (exp (I * ((-arg z) : ℂ)) * z).re = ‖z‖ ∧
      (exp (I * ((-arg z + Real.pi) : ℂ)) * z).re = -‖z‖ := by
  have hsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    ring
  by_cases hz : z = 0
  · simp [hz]
  · have hcos : Real.cos (arg z) = z.re / ‖z‖ := cos_arg hz
    have hsin : Real.sin (arg z) = z.im / ‖z‖ := sin_arg z
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hneg : ((-arg z : ℝ) : ℂ) = -((arg z : ℝ) : ℂ) := by simp
    have hpi : ((-arg z + Real.pi : ℝ) : ℂ) =
        -((arg z : ℝ) : ℂ) + (Real.pi : ℂ) := by
      push_cast
      ring
    constructor
    · rw [← hneg, re_exp_mul]
      simp only [Real.cos_neg, Real.sin_neg, hcos, hsin]
      field_simp [hn]
      nlinarith
    · rw [← hpi, re_exp_mul, Real.cos_add_pi, Real.sin_add_pi]
      simp only [Real.cos_neg, Real.sin_neg, hcos, hsin, neg_mul, sub_neg_eq_add]
      field_simp [hn]
      nlinarith

theorem overlap_chartPositionInfo {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) {p q : Vec4}
    (hpq : p ≠ q) {u v : DiracSpinor} (hov : inner ℂ u v ≠ 0) (α : ℝ) :
    ChartPositionInfo (shellPacket r s α p q u v) := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  set z : ℂ := inner ℂ u v
  have hz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hov
  set θ : ℝ := -arg z
  obtain ⟨x, hx⟩ := exists_wavePhase_eq hδ (θ - α)
  obtain ⟨y, hy⟩ := exists_wavePhase_eq hδ (θ + Real.pi - α)
  have hxθ : wavePhase (q - p) x + α = θ := by linarith
  have hyθ : wavePhase (q - p) y + α = θ + Real.pi := by linarith
  have hxC : (wavePhase (q - p) x : ℂ) + (α : ℂ) = (θ : ℂ) := by
    rw [← ofReal_add, hxθ]
  have hyC : (wavePhase (q - p) y : ℂ) + (α : ℂ) = ((θ + Real.pi : ℝ) : ℂ) := by
    rw [← ofReal_add, hyθ]
  refine ⟨x, y, ?_⟩
  intro heq
  have hdiff : bornDensity (shellPacket r s α p q u v) x -
      bornDensity (shellPacket r s α p q u v) y = 4 * r * s * ‖z‖ := by
    rw [bornDensity_shellPacket, bornDensity_shellPacket, hxC, hyC]
    have hzuv : z = inner ℂ u v := rfl
    rw [← hzuv]
    simp only [θ]
    rw [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_neg]
    have halign := align_overlap z
    rw [halign.1, halign.2]
    ring
  rw [heq, sub_self] at hdiff
  exact absurd hdiff.symm
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hr) hs) hz)

theorem orthogonal_bornDensity_const {u v : DiracSpinor} (huv : inner ℂ u v = 0)
    (r s α : ℝ) (p q x y : Vec4) :
    bornDensity (shellPacket r s α p q u v) x =
      bornDensity (shellPacket r s α p q u v) y := by
  rw [bornDensity_shellPacket, bornDensity_shellPacket, huv]
  simp

theorem orthogonal_shellInformation {u v : DiracSpinor} (huv : inner ℂ u v = 0) (r s : ℝ) :
    shellInformation r s u v = 0 := by
  unfold shellInformation shellVisibility carrierOverlap
  simp [huv]

theorem orthogonal_no_chartPositionInfo {u v : DiracSpinor} (huv : inner ℂ u v = 0)
    (r s α : ℝ) (p q : Vec4) : ¬ ChartPositionInfo (shellPacket r s α p q u v) := by
  intro ⟨x, y, hxy⟩
  exact hxy (orthogonal_bornDensity_const huv r s α p q x y)

theorem shellInformation_not_a_location {r : ℝ} (hr : r ≠ 0) {u : DiracSpinor} (hu : u ≠ 0)
    (α : ℝ) (p : Vec4) :
    shellInformation r r u u = 1 ∧ ¬ ChartPositionInfo (shellPacket r r α p p u u) := by
  refine ⟨shellInformation_same_carrier r r hu ▸ phaseInformation_equal hr, ?_⟩
  intro ⟨x, y, hxy⟩
  apply hxy
  rw [bornDensity_shellPacket, bornDensity_shellPacket]
  simp [sub_self, wavePhase]

/-- A vector orthogonal to the time axis realises any relative phase at time coordinate `0`. -/
theorem exists_wavePhase_eq_spatial {δ : Vec4} (h0 : δ 0 = 0) (hδ : δ ≠ 0) (t : ℝ) :
    ∃ x : Vec4, x 0 = 0 ∧ wavePhase δ x = t := by
  have hcomp : ∃ μ : Fin 4, μ ≠ 0 ∧ δ μ ≠ 0 := by
    by_contra h
    push Not at h
    apply hδ
    ext μ
    by_cases hμ : μ = 0
    · exact hμ.symm ▸ h0
    · exact h μ hμ
  obtain ⟨μ, hμ0, hμ⟩ := hcomp
  refine ⟨(t / δ μ) • Pi.single μ (1 : ℝ), ?_, ?_⟩
  · simp [Pi.smul_apply, Pi.single_eq_of_ne hμ0.symm]
  · rw [wavePhase_smul_right, wavePhase_single]
    exact div_mul_cancel₀ t hμ

theorem overlap_spatial_chart {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) {p q : Vec4}
    (h0 : (q - p) 0 = 0) (hpq : p ≠ q) {u v : DiracSpinor} (hov : inner ℂ u v ≠ 0)
    (α : ℝ) :
    ∃ x y : Vec4, x 0 = 0 ∧ y 0 = 0 ∧
      bornDensity (shellPacket r s α p q u v) x ≠
        bornDensity (shellPacket r s α p q u v) y := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  set z : ℂ := inner ℂ u v
  have hz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hov
  set θ : ℝ := -arg z
  obtain ⟨x, hx0, hx⟩ := exists_wavePhase_eq_spatial h0 hδ (θ - α)
  obtain ⟨y, hy0, hy⟩ := exists_wavePhase_eq_spatial h0 hδ (θ + Real.pi - α)
  have hxθ : wavePhase (q - p) x + α = θ := by linarith
  have hyθ : wavePhase (q - p) y + α = θ + Real.pi := by linarith
  have hxC : (wavePhase (q - p) x : ℂ) + (α : ℂ) = (θ : ℂ) := by
    rw [← ofReal_add, hxθ]
  have hyC : (wavePhase (q - p) y : ℂ) + (α : ℂ) = ((θ + Real.pi : ℝ) : ℂ) := by
    rw [← ofReal_add, hyθ]
  refine ⟨x, y, hx0, hy0, ?_⟩
  intro heq
  have hdiff : bornDensity (shellPacket r s α p q u v) x -
      bornDensity (shellPacket r s α p q u v) y = 4 * r * s * ‖z‖ := by
    rw [bornDensity_shellPacket, bornDensity_shellPacket, hxC, hyC]
    have hzuv : z = inner ℂ u v := rfl
    rw [← hzuv]
    simp only [θ]
    rw [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_neg]
    have halign := align_overlap z
    rw [halign.1, halign.2]
    ring
  rw [heq, sub_self] at hdiff
  exact absurd hdiff.symm
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hr) hs) hz)

theorem bornDensity_shellPacket_timeShift {p q : Vec4} (h0 : (q - p) 0 = 0)
    (r s α : ℝ) (u v : DiracSpinor) (t : ℝ) (x : Vec4) :
    bornDensity (shellPacket r s α p q u v) (x + timeShift t) =
      bornDensity (shellPacket r s α p q u v) x := by
  rw [bornDensity_shellPacket, bornDensity_shellPacket, wavePhase_timeShift h0]

/-! ### One nonzero mass -/

theorem diracPair_polar_ortho {m : ℝ} {p q : Vec4} {u v : DiracSpinor}
    (hu : u ≠ 0) (hv : v ≠ 0) (hp : DiracMomentum m p u) (hq : DiracMomentum m q v) :
    minkowskiPolar (q - p) (q + p) = 0 := by
  have hpQ := diracMomentum_implies_mass_shell hu hp
  have hqQ := diracMomentum_implies_mass_shell hv hq
  exact sameShell_polar_ortho hpQ hqQ

theorem one_mass_refuses_shared_carrier {m : ℝ} (hm : m ≠ 0) {p q : Vec4} (hpq : p ≠ q)
    {u : DiracSpinor} (hu : u ≠ 0) :
    ¬ (DiracMomentum m p u ∧ DiracMomentum m q u) := by
  intro ⟨hp, hq⟩
  exact hpq (diracMomentum_unique hm hu hp hq)

theorem shared_carrier_not_one_mass {m : ℝ} (hm : m ≠ 0) {r : ℝ} (hr : r ≠ 0)
    {p q : Vec4} (hpq : p ≠ q) {u : DiracSpinor} (hu : u ≠ 0) (α : ℝ) :
    shellInformation r r u u = 1 ∧
      ChartPositionInfo (shellPacket r r α p q u u) ∧
        ¬ (DiracMomentum m p u ∧ DiracMomentum m q u) := by
  refine ⟨(shellInformation_not_a_location hr hu α p).1, ?_,
      one_mass_refuses_shared_carrier hm hpq hu⟩
  have hinner : inner ℂ u u ≠ 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    exact pow_ne_zero 2 (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu))
  exact overlap_chartPositionInfo hr hr hpq hinner α

theorem dirac_meanRest_reads_space {m : ℝ} {p q : Vec4} {u v : DiracSpinor}
    (hu : u ≠ 0) (hv : v ≠ 0) (hp : DiracMomentum m p u) (hq : DiracMomentum m q v)
    (hrest : MeanRestFrame p q) (hp0 : 0 < p 0) (hq0 : 0 < q 0) :
    (q - p) 0 = 0 ∧
      (∀ r s α t x, bornDensity (shellPacket r s α p q u v) (x + timeShift t) =
        bornDensity (shellPacket r s α p q u v) x) ∧
        ∀ r s, shellInformation r s u v ≤ phaseInformation (|r| * ‖u‖) (|s| * ‖v‖) ∧
          shellInformation r s u v ≤ 1 := by
  have hQ : minkowskiQ p = minkowskiQ q := by
    rw [diracMomentum_implies_mass_shell hu hp, diracMomentum_implies_mass_shell hv hq]
  have hsum : (p + q) 0 ≠ 0 := by
    intro h
    have : p 0 + q 0 = 0 := by simpa [Pi.add_apply] using h
    linarith
  have h0 := sameShell_meanRest_timeComponent hQ hrest hsum
  refine ⟨h0, ?_, ?_⟩
  · intro r s α t x
    exact bornDensity_shellPacket_timeShift h0 r s α u v t x
  · intro r s
    exact ⟨shellInformation_le_phaseInformation r s u v, shellInformation_le_one r s u v⟩

/-! ### The shell `Q = -9` in the mean rest frame -/

/-- Weyl seed `(1, 0)`. -/
noncomputable def shellAxisSeed : DualSpinor :=
  EuclideanSpace.single 0 1

/-- Momentum `(5, 4, 0, 0)`, with `Q = -9`. -/
def shellRestP : Vec4 :=
  Pi.single 0 5 + (4 : ℝ) • Pi.single 1 1

/-- Momentum `(5, -4, 0, 0)`, with `Q = -9`. -/
def shellRestQ : Vec4 :=
  Pi.single 0 5 + (-4 : ℝ) • Pi.single 1 1

/-- On-shell particle at `shellRestP` with seed `shellAxisSeed`. -/
noncomputable def shellParticleP : DiracSpinor :=
  onShellParticleSpinor 3 shellRestP shellAxisSeed

/-- On-shell particle at `shellRestQ` with the same seed. -/
noncomputable def shellParticleQ : DiracSpinor :=
  onShellParticleSpinor 3 shellRestQ shellAxisSeed

private theorem shell_momentum_coord (k : ℝ) :
    ((Pi.single 0 5 + k • Pi.single 1 1 : Vec4) 0 = 5) ∧
      ((Pi.single 0 5 + k • Pi.single 1 1 : Vec4) 1 = k) ∧
        ((Pi.single 0 5 + k • Pi.single 1 1 : Vec4) 2 = 0) ∧
          ((Pi.single 0 5 + k • Pi.single 1 1 : Vec4) 3 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne]

private theorem apply_pauliX_seed :
    applyMat pauliX shellAxisSeed = EuclideanSpace.single (1 : Fin 2) 1 := by
  ext i
  fin_cases i <;>
    simp [applyMat_apply, pauliX, shellAxisSeed, EuclideanSpace.single, PiLp.single_apply]

private theorem slashBar_axis (k : ℝ) :
    applyMat (pauliSlashBar (Pi.single 0 5 + k • Pi.single 1 1)) shellAxisSeed =
      (-5 : ℂ) • shellAxisSeed + (k : ℂ) • EuclideanSpace.single 1 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := shell_momentum_coord k
  have hmat : pauliSlashBar (Pi.single 0 5 + k • Pi.single 1 1) =
      (-5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (k : ℂ) • pauliX := by
    unfold pauliSlashBar
    rw [h0, h1, h2, h3]
    simp [zero_smul]
  rw [hmat, applyMat_add_mat, applyMat_smul_mat, applyMat_smul_mat, applyMat_one,
    apply_pauliX_seed]

private theorem diracLower_onShell (m : ℝ) (p : Vec4) (u : DualSpinor) :
    diracLower (onShellParticleSpinor m p u) =
      -(I / (m : ℂ)) • applyMat (pauliSlashBar p) u := by
  unfold onShellParticleSpinor
  rw [diracLower_add, diracLower_weylUpper, diracLower_weylLower, zero_add]

private theorem diracUpper_onShell (m : ℝ) (p : Vec4) (u : DualSpinor) :
    diracUpper (onShellParticleSpinor m p u) = u := by
  unfold onShellParticleSpinor
  rw [diracUpper_add, diracUpper_weylUpper, diracUpper_weylLower, add_zero]

private theorem shell_lower (k : ℝ) :
    diracLower (onShellParticleSpinor 3 (Pi.single 0 5 + k • Pi.single 1 1) shellAxisSeed) =
      (5 * I / 3 : ℂ) • shellAxisSeed +
        ((-(k : ℂ) * I / 3) • EuclideanSpace.single 1 1) := by
  rw [diracLower_onShell, slashBar_axis, smul_add, smul_smul, smul_smul]
  have h0 : -(I / ((3 : ℝ) : ℂ)) * -5 = 5 * I / 3 := by
    field_simp
    norm_cast
  have h1 : -(I / ((3 : ℝ) : ℂ)) * (k : ℂ) = -(k : ℂ) * I / 3 := by
    field_simp
    norm_cast
    ring
  rw [h0, h1]

private theorem shell_seed_coord :
    shellAxisSeed 0 = 1 ∧ shellAxisSeed 1 = 0 := by
  constructor <;> simp [shellAxisSeed, EuclideanSpace.single]

private theorem shell_particle_coord (k : ℝ) :
    let ψ := onShellParticleSpinor 3 (Pi.single 0 5 + k • Pi.single 1 1) shellAxisSeed
    ψ 0 = 1 ∧ ψ 1 = 0 ∧ ψ 2 = 5 * I / 3 ∧ ψ 3 = -((k : ℂ) * I) / 3 := by
  intro ψ
  have hdec : weylUpper shellAxisSeed +
      weylLower (diracLower ψ) = ψ := by
    simpa [diracUpper_onShell, ψ] using weyl_decompose ψ
  rw [shell_lower k] at hdec
  have hseed := shell_seed_coord
  have hlow0 : (((5 * I / 3 : ℂ) • shellAxisSeed +
      ((-(k : ℂ) * I / 3) • EuclideanSpace.single 1 1) : DualSpinor) 0) = 5 * I / 3 := by
    simp [shellAxisSeed, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single]
  have hlow1 : (((5 * I / 3 : ℂ) • shellAxisSeed +
      ((-(k : ℂ) * I / 3) • EuclideanSpace.single 1 1) : DualSpinor) 1) =
        -(k : ℂ) * I / 3 := by
    simp [shellAxisSeed, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single]
  have hv := weylUpper_add_lower shellAxisSeed
    ((5 * I / 3 : ℂ) • shellAxisSeed + ((-(k : ℂ) * I / 3) • EuclideanSpace.single 1 1))
  rw [hv] at hdec
  have hfun := congrArg (fun w : DiracSpinor => (w 0, w 1, w 2, w 3)) hdec
  suffices 1 = ψ 0 ∧ (0 : ℂ) = ψ 1 ∧ 5 * I / 3 = ψ 2 ∧
      -((k : ℂ) * I) / 3 = ψ 3 by
    refine ⟨this.1.symm, this.2.1.symm, this.2.2.1.symm, this.2.2.2.symm⟩
  simpa [hseed.1, hseed.2] using hfun

theorem shellParticleP_coord :
    shellParticleP 0 = 1 ∧ shellParticleP 1 = 0 ∧
      shellParticleP 2 = 5 * I / 3 ∧
        shellParticleP 3 = -((4 : ℂ) * I) / 3 := by
  simpa [shellParticleP, shellRestP] using shell_particle_coord (4 : ℝ)

theorem shellRest_geometry :
    minkowskiQ shellRestP = -((3 : ℝ) ^ 2) ∧
      minkowskiQ shellRestQ = -((3 : ℝ) ^ 2) ∧
        MeanRestFrame shellRestP shellRestQ ∧
          0 < shellRestP 0 ∧
            0 < shellRestQ 0 ∧
              (shellRestQ - shellRestP) 0 = 0 ∧
                shellRestP ≠ shellRestQ := by
  have hp := shell_momentum_coord 4
  have hq := shell_momentum_coord (-4)
  have hP : minkowskiQ shellRestP = -((3 : ℝ) ^ 2) := by
    rw [minkowskiQ_eq]
    simp [shellRestP, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
    norm_num
  have hQ : minkowskiQ shellRestQ = -((3 : ℝ) ^ 2) := by
    rw [minkowskiQ_eq]
    simp [shellRestQ]
    norm_num
  refine ⟨hP, hQ, ?_, ?_, ?_, ?_, ?_⟩
  · simp [MeanRestFrame, shellRestP, shellRestQ, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne]
  · simp [shellRestP, hp.1]
  · simp [shellRestQ]
  · simp [shellRestP, shellRestQ, Pi.sub_apply, hp.1]
  · intro h
    rw [shellRestP, shellRestQ] at h
    have h1 := congrFun h 1
    rw [hp.2.1, hq.2.1] at h1
    norm_num at h1

private theorem shell_component_inner :
    inner ℂ shellParticleP shellParticleQ = 2 ∧
      inner ℂ shellParticleP shellParticleP = (50 / 9 : ℂ) ∧
        inner ℂ shellParticleQ shellParticleQ = (50 / 9 : ℂ) := by
  have hP := shell_particle_coord 4
  have hQ := shell_particle_coord (-4)
  have hinner (χ ψ : DiracSpinor) (a0 a1 a2 a3 b0 b1 b2 b3 : ℂ)
      (ha0 : χ 0 = a0) (ha1 : χ 1 = a1) (ha2 : χ 2 = a2) (ha3 : χ 3 = a3)
      (hb0 : ψ 0 = b0) (hb1 : ψ 1 = b1) (hb2 : ψ 2 = b2) (hb3 : ψ 3 = b3) :
      inner ℂ χ ψ = star a0 * b0 + star a1 * b1 + star a2 * b2 + star a3 * b3 := by
    rw [diracSpinor_inner_eq, Fin.sum_univ_four, ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
  refine ⟨?_, ?_, ?_⟩
  · have h := hinner shellParticleP shellParticleQ 1 0 (5 * I / 3) _
      1 0 (5 * I / 3) _ hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
      hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2
    rw [h]
    simp [conj_I]
    ring_nf
    norm_num
  · have h := hinner shellParticleP shellParticleP 1 0 (5 * I / 3) _
      1 0 (5 * I / 3) _ hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
      hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
    rw [h]
    simp [conj_I]
    ring_nf
    norm_num
  · have h := hinner shellParticleQ shellParticleQ 1 0 (5 * I / 3) _
      1 0 (5 * I / 3) _ hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2
      hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2
    rw [h]
    simp [conj_I]
    ring_nf
    norm_num

theorem shellRest_norms :
    ‖shellParticleP‖ ^ 2 = 50 / 9 ∧ ‖shellParticleQ‖ ^ 2 = 50 / 9 := by
  have h := shell_component_inner
  have hPeq := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := shellParticleP)
  have hQeq := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := shellParticleQ)
  refine ⟨?_, ?_⟩
  · apply Complex.ofReal_injective
    calc
      Complex.ofReal (‖shellParticleP‖ ^ 2) = (‖shellParticleP‖ : ℂ) ^ 2 :=
        Complex.ofReal_pow ‖shellParticleP‖ 2
      _ = inner ℂ shellParticleP shellParticleP := hPeq.symm
      _ = (50 / 9 : ℂ) := h.2.1
      _ = Complex.ofReal (50 / 9) := by norm_num
  · apply Complex.ofReal_injective
    calc
      Complex.ofReal (‖shellParticleQ‖ ^ 2) = (‖shellParticleQ‖ : ℂ) ^ 2 :=
        Complex.ofReal_pow ‖shellParticleQ‖ 2
      _ = inner ℂ shellParticleQ shellParticleQ := hQeq.symm
      _ = (50 / 9 : ℂ) := h.2.2
      _ = Complex.ofReal (50 / 9) := by norm_num

theorem shellRest_fidelity : carrierFidelity shellParticleP shellParticleQ = 9 / 25 := by
  have hinner := shell_component_inner.1
  have hnorm := shellRest_norms
  unfold carrierFidelity carrierOverlap
  rw [hinner]
  have hnp : ‖shellParticleP‖ = √(50 / 9) := by
    rw [← Real.sqrt_sq (norm_nonneg _), hnorm.1]
  have hnq : ‖shellParticleQ‖ = √(50 / 9) := by
    rw [← Real.sqrt_sq (norm_nonneg _), hnorm.2]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnp, hnq, h2]
  have hsqrt : √(50 / 9) * √(50 / 9) = 50 / 9 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 50 / 9)]
    have hsq : ((50 : ℝ) / 9) * ((50 : ℝ) / 9) = ((50 : ℝ) / 9) ^ 2 := by ring
    conv_lhs =>
      arg 1
      rw [hsq]
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 50 / 9)]
  rw [hsqrt]
  norm_num

/-- Equal weights on this pair have phase information `81/625`, not `1`. -/
theorem shellRest_information :
    shellInformation 1 1 shellParticleP shellParticleQ = 81 / 625 ∧
      phaseInformation ‖shellParticleP‖ ‖shellParticleQ‖ = 1 ∧
        (81 / 625 : ℝ) < 1 := by
  have hfid := shellRest_fidelity
  have hnorm := shellRest_norms
  have hpos : ‖shellParticleP‖ ≠ 0 := by
    intro h
    have : ‖shellParticleP‖ ^ 2 = 0 := by simp [h]
    linarith [hnorm.1]
  have heq : ‖shellParticleP‖ = ‖shellParticleQ‖ := by
    have hdiff : (‖shellParticleP‖ - ‖shellParticleQ‖) *
        (‖shellParticleP‖ + ‖shellParticleQ‖) = 0 := by
      nlinarith [hnorm.1, hnorm.2]
    rcases mul_eq_zero.mp hdiff with hsub | hsum
    · linarith
    · linarith [norm_nonneg shellParticleP, norm_nonneg shellParticleQ]
  refine ⟨?_, ?_, by norm_num⟩
  · rw [shellInformation_eq_fidelity_sq, hfid]
    have honeP : |(1 : ℝ)| * ‖shellParticleP‖ = ‖shellParticleP‖ := by simp
    have honeQ : |(1 : ℝ)| * ‖shellParticleQ‖ = ‖shellParticleQ‖ := by simp
    rw [honeP, honeQ, heq, phaseInformation_equal (heq ▸ hpos)]
    norm_num
  · rw [heq]
    exact phaseInformation_equal (by simpa [heq] using hpos)

theorem shellRest_dirac :
    DiracMomentum 3 shellRestP shellParticleP ∧
      DiracMomentum 3 shellRestQ shellParticleQ ∧
        ¬ (DiracMomentum 3 shellRestP shellParticleP ∧
            DiracMomentum 3 shellRestQ shellParticleP) := by
  have hPne : shellParticleP ≠ 0 :=
    onShellParticleSpinor_ne_zero (by simp [shellAxisSeed, EuclideanSpace.single])
  have hgeom := shellRest_geometry
  refine ⟨onShellParticle_dirac (by norm_num) hgeom.1 shellAxisSeed,
      onShellParticle_dirac (by norm_num) hgeom.2.1 shellAxisSeed, ?_⟩
  intro ⟨hp, hq⟩
  exact hgeom.2.2.2.2.2.2 (diracMomentum_unique (by norm_num) hPne hp hq)

theorem shellRest_regression (α : ℝ) :
    minkowskiQ shellRestP = minkowskiQ shellRestQ ∧
      (shellRestQ - shellRestP) 0 = 0 ∧
        carrierFidelity shellParticleP shellParticleQ = 9 / 25 ∧
          shellInformation 1 1 shellParticleP shellParticleQ = 81 / 625 ∧
            ChartPositionInfo
              (shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ) ∧
              (∀ t x, bornDensity
                (shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ)
                  (x + timeShift t) =
                bornDensity
                  (shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ) x) ∧
                ¬ (DiracMomentum 3 shellRestP shellParticleP ∧
                    DiracMomentum 3 shellRestQ shellParticleP) := by
  have hgeom := shellRest_geometry
  have hinfo := shellRest_information
  have hdirac := shellRest_dirac
  have hinner : inner ℂ shellParticleP shellParticleQ ≠ 0 := by
    rw [shell_component_inner.1]
    norm_num
  have h0 : (shellRestQ - shellRestP) 0 = 0 := hgeom.2.2.2.2.2.1
  refine ⟨hgeom.1.trans hgeom.2.1.symm, h0, shellRest_fidelity, hinfo.1, ?_, ?_, hdirac.2.2⟩
  · exact overlap_chartPositionInfo (by norm_num) (by norm_num) hgeom.2.2.2.2.2.2 hinner α
  · intro t x
    exact bornDensity_shellPacket_timeShift h0 1 1 α shellParticleP shellParticleQ t x

theorem orthogonal_basis_silent (α : ℝ) (p q : Vec4) :
    let u : DiracSpinor := EuclideanSpace.single 0 1
    let v : DiracSpinor := EuclideanSpace.single 1 1
    inner ℂ u v = 0 ∧
      shellInformation 1 1 u v = 0 ∧
        ¬ ChartPositionInfo (shellPacket 1 1 α p q u v) := by
  intro u v
  have hinner : inner ℂ u v = 0 := by
    unfold u v
    rw [EuclideanSpace.inner_single_left]
    simp
  exact ⟨hinner, orthogonal_shellInformation hinner 1 1,
    orthogonal_no_chartPositionInfo hinner 1 1 α p q⟩

end Logic

end DstDiophantine
