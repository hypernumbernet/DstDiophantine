import DoubleSpacetime.Logic.Quantum.NewtonWigner

/-!
# Chart position as complementary information

Newton–Wigner localization, read in `NewtonWigner`, is a contrast of Born densities. That contrast
is two real numbers.

A packet with nonnegative weights `r`, `s` and relative phase `α` has density
`(r² + s² + 2rs cos(((q − p)·x) + α)) ‖u‖²`. The chart enters through one phase. A displacement
orthogonal to `q − p` leaves the density fixed, and `α` only slides the fringe.

The peak and the valley sum to twice the two plane-wave weights, so the cross term is not a weight.
Their ratio is the fringe visibility `V = 2rs / (r² + s²)`. The which-momentum distinguishability
`D = |r² − s²| / (r² + s²)` obeys `D² + V² = 1`. A definite momentum has `D = 1` and `V = 0`, and
carries no chart-position information. Equal weights have `D = 0` and `V = 1`.
-/

namespace DoubleSpacetime

namespace Logic

open Complex

/-! ### One phase, hit exactly -/

theorem exists_wavePhase_eq {δ : Vec4} (hδ : δ ≠ 0) (t : ℝ) :
    ∃ x : Vec4, wavePhase δ x = t := by
  have hcomp : ∃ μ : Fin 4, δ μ ≠ 0 := by
    by_contra h
    push Not at h
    apply hδ
    ext μ
    exact h μ
  obtain ⟨μ, hμ⟩ := hcomp
  refine ⟨(t / δ μ) • Pi.single μ (1 : ℝ), ?_⟩
  rw [wavePhase_smul_right, wavePhase_single]
  exact div_mul_cancel₀ t hμ

theorem exists_wavePhase_kernel {δ : Vec4} (hδ : δ ≠ 0) :
    ∃ v : Vec4, v ≠ 0 ∧ wavePhase δ v = 0 := by
  have hcomp : ∃ μ : Fin 4, δ μ ≠ 0 := by
    by_contra h
    push Not at h
    apply hδ
    ext μ
    exact h μ
  obtain ⟨μ, hμ⟩ := hcomp
  obtain ⟨ν, hν⟩ : ∃ ν : Fin 4, ν ≠ μ := by
    fin_cases μ
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  let v : Vec4 := (δ ν) • Pi.single μ (1 : ℝ) + (-(δ μ)) • Pi.single ν (1 : ℝ)
  refine ⟨v, ?_, ?_⟩
  · intro hv
    have hvν : v ν = 0 := congrFun hv ν
    have hcompν : v ν = -(δ μ) := by
      simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
        Pi.single_eq_of_ne hν, mul_zero, zero_add, mul_one]
    exact hμ (neg_eq_zero.mp (hcompν.symm.trans hvν))
  · rw [wavePhase_add_right, wavePhase_smul_right, wavePhase_smul_right, wavePhase_single,
      wavePhase_single]
    ring

/-! ### Two weights and one relative phase -/

/-- `r` on momentum `p`, weight `s` and phase `α` on momentum `q`, common spinor `u`. -/
noncomputable def phasedPacket (r s α : ℝ) (p q : Vec4) (u : DiracSpinor) :
    Vec4 → DiracSpinor :=
  fun x => (r : ℂ) • planeWave p u x + ((s : ℂ) * exp (I * (α : ℂ))) • planeWave q u x

/-- Which-momentum distinguishability. Zero denominator is the Lean zero. -/
noncomputable def whichMomentum (r s : ℝ) : ℝ :=
  |r ^ 2 - s ^ 2| / (r ^ 2 + s ^ 2)

/-- Fringe visibility. Zero denominator is the Lean zero. -/
noncomputable def fringeVisibility (r s : ℝ) : ℝ :=
  2 * r * s / (r ^ 2 + s ^ 2)

private theorem normSq_add_real_mul_I (x y : ℝ) :
    ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  have hxy : (x : ℂ) + (y : ℂ) * I = ⟨x, y⟩ := by
    apply Complex.ext <;> simp
  rw [hxy, ← Complex.normSq_eq_norm_sq, Complex.normSq_mk]
  ring

private theorem normSq_real_add_scaled_exp (r s β : ℝ) :
    ‖(r : ℂ) + (s : ℂ) * exp (I * (β : ℂ))‖ ^ 2 =
      r ^ 2 + s ^ 2 + 2 * r * s * Real.cos β := by
  rw [show I * (β : ℂ) = (β : ℂ) * I by ring, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hsum : (r : ℂ) + (s : ℂ) * ((Real.cos β : ℂ) + (Real.sin β : ℂ) * I) =
      ((r + s * Real.cos β : ℝ) : ℂ) + ((s * Real.sin β : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hsum, normSq_add_real_mul_I]
  have hcs : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
  calc
    (r + s * Real.cos β) ^ 2 + (s * Real.sin β) ^ 2
      = r ^ 2 + 2 * r * s * Real.cos β +
          s ^ 2 * (Real.cos β ^ 2 + Real.sin β ^ 2) := by ring
    _ = r ^ 2 + s ^ 2 + 2 * r * s * Real.cos β := by rw [hcs]; ring

theorem bornDensity_phasedPacket (r s α : ℝ) (p q : Vec4) (u : DiracSpinor) (x : Vec4) :
    bornDensity (phasedPacket r s α p q u) x =
      (r ^ 2 + s ^ 2 + 2 * r * s * Real.cos (wavePhase (q - p) x + α)) * ‖u‖ ^ 2 := by
  unfold bornDensity phasedPacket
  have hsum :
      (r : ℂ) • planeWave p u x + ((s : ℂ) * exp (I * (α : ℂ))) • planeWave q u x =
        ((r : ℂ) * exp (I * (wavePhase p x : ℂ)) +
          ((s : ℂ) * exp (I * (α : ℂ))) * exp (I * (wavePhase q x : ℂ))) • u := by
    unfold planeWave
    rw [smul_smul, smul_smul, ← add_smul]
  rw [hsum, norm_smul, mul_pow]
  have hfactor :
      ‖(r : ℂ) * exp (I * (wavePhase p x : ℂ)) +
          ((s : ℂ) * exp (I * (α : ℂ))) * exp (I * (wavePhase q x : ℂ))‖ ^ 2 =
        ‖(r : ℂ) + (s : ℂ) * exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ))‖ ^ 2 := by
    have hpull :
        (r : ℂ) * exp (I * (wavePhase p x : ℂ)) +
            ((s : ℂ) * exp (I * (α : ℂ))) * exp (I * (wavePhase q x : ℂ)) =
          exp (I * (wavePhase p x : ℂ)) *
            ((r : ℂ) + (s : ℂ) * exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ))) := by
      have hsecond :
          exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ)) =
            exp (I * (wavePhase p x : ℂ)) *
              exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) := by
        rw [← exp_add, ← exp_add]
        apply congrArg exp
        rw [wavePhase_sub_left, ofReal_add, ofReal_sub]
        ring
      calc
        (r : ℂ) * exp (I * (wavePhase p x : ℂ)) +
            ((s : ℂ) * exp (I * (α : ℂ))) * exp (I * (wavePhase q x : ℂ))
          = (r : ℂ) * exp (I * (wavePhase p x : ℂ)) +
              (s : ℂ) * (exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ))) := by ring
        _ = (r : ℂ) * exp (I * (wavePhase p x : ℂ)) +
              (s : ℂ) * (exp (I * (wavePhase p x : ℂ)) *
                exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ))) := by rw [hsecond]
        _ = exp (I * (wavePhase p x : ℂ)) *
              ((r : ℂ) + (s : ℂ) * exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ))) := by
            ring
    rw [hpull, norm_mul, norm_exp_I, one_mul]
  rw [hfactor, normSq_real_add_scaled_exp]

theorem bornDensity_scaled_planeWave (r : ℝ) (p : Vec4) (u : DiracSpinor) (x : Vec4) :
    bornDensity (planeWave p ((r : ℂ) • u)) x = r ^ 2 * ‖u‖ ^ 2 := by
  rw [bornDensity_planeWave, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The density reads one phase -/

theorem bornDensity_phasedPacket_of_phase (r s α : ℝ) (p q : Vec4) (u : DiracSpinor)
    {x y : Vec4} (h : wavePhase (q - p) x = wavePhase (q - p) y) :
    bornDensity (phasedPacket r s α p q u) x =
      bornDensity (phasedPacket r s α p q u) y := by
  rw [bornDensity_phasedPacket, bornDensity_phasedPacket, h]

theorem bornDensity_phasedPacket_add_kernel (r s α : ℝ) (p q : Vec4) (u : DiracSpinor)
    {v : Vec4} (hv : wavePhase (q - p) v = 0) (x : Vec4) :
    bornDensity (phasedPacket r s α p q u) (x + v) =
      bornDensity (phasedPacket r s α p q u) x := by
  rw [bornDensity_phasedPacket, bornDensity_phasedPacket, wavePhase_add_right, hv, add_zero]

/-- A nonzero chart displacement can leave every density unchanged. Position is not a point. -/
theorem bornDensity_constant_on_phase_kernel {p q : Vec4} (hpq : p ≠ q)
    (r s α : ℝ) (u : DiracSpinor) :
    ∃ v : Vec4, v ≠ 0 ∧ ∀ x,
      bornDensity (phasedPacket r s α p q u) (x + v) =
        bornDensity (phasedPacket r s α p q u) x := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  obtain ⟨v, hv, hphase⟩ := exists_wavePhase_kernel hδ
  exact ⟨v, hv, fun x => bornDensity_phasedPacket_add_kernel r s α p q u hphase x⟩

/-- The relative phase slides the fringe and does not change its shape. -/
theorem phasedPacket_relPhase_shift {p q : Vec4} (hpq : p ≠ q) (r s α : ℝ) (u : DiracSpinor) :
    ∃ a : Vec4, ∀ x,
      bornDensity (phasedPacket r s α p q u) x =
        bornDensity (phasedPacket r s 0 p q u) (x + a) := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  obtain ⟨a, ha⟩ := exists_wavePhase_eq hδ α
  refine ⟨a, fun x => ?_⟩
  rw [bornDensity_phasedPacket, bornDensity_phasedPacket, wavePhase_add_right, ha, add_zero]

/-! ### Peak, valley, and the cancelled cross term -/

theorem bornDensity_phasedPacket_bounds {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (α : ℝ) (p q : Vec4) (u : DiracSpinor) (x : Vec4) :
    (r - s) ^ 2 * ‖u‖ ^ 2 ≤ bornDensity (phasedPacket r s α p q u) x ∧
      bornDensity (phasedPacket r s α p q u) x ≤ (r + s) ^ 2 * ‖u‖ ^ 2 := by
  rw [bornDensity_phasedPacket]
  set β : ℝ := wavePhase (q - p) x + α
  have hrs : 0 ≤ 2 * r * s := by positivity
  have hcosHi : 2 * r * s * Real.cos β ≤ 2 * r * s := by
    simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one β) hrs
  have hcosLo : 2 * r * s * (-1) ≤ 2 * r * s * Real.cos β :=
    mul_le_mul_of_nonneg_left (Real.neg_one_le_cos β) hrs
  have hlo : (r - s) ^ 2 ≤ r ^ 2 + s ^ 2 + 2 * r * s * Real.cos β := by
    have hrw : (r - s) ^ 2 = r ^ 2 + s ^ 2 + 2 * r * s * (-1) := by ring
    linarith
  have hhi : r ^ 2 + s ^ 2 + 2 * r * s * Real.cos β ≤ (r + s) ^ 2 := by
    have hrw : (r + s) ^ 2 = r ^ 2 + s ^ 2 + 2 * r * s := by ring
    linarith
  constructor
  · exact mul_le_mul_of_nonneg_right hlo (sq_nonneg ‖u‖)
  · exact mul_le_mul_of_nonneg_right hhi (sq_nonneg ‖u‖)

theorem phasedPacket_extremes {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) {p q : Vec4} (hpq : p ≠ q)
    (α : ℝ) (u : DiracSpinor) :
    ∃ x y : Vec4,
      bornDensity (phasedPacket r s α p q u) x = (r + s) ^ 2 * ‖u‖ ^ 2 ∧
        bornDensity (phasedPacket r s α p q u) y = (r - s) ^ 2 * ‖u‖ ^ 2 ∧
          bornDensity (phasedPacket r s α p q u) x -
              bornDensity (phasedPacket r s α p q u) y = 4 * r * s * ‖u‖ ^ 2 ∧
            bornDensity (phasedPacket r s α p q u) x +
                bornDensity (phasedPacket r s α p q u) y =
              2 * (bornDensity (planeWave p ((r : ℂ) • u)) 0 +
                bornDensity (planeWave q ((s : ℂ) • u)) 0) ∧
              0 ≤ bornDensity (phasedPacket r s α p q u) x -
                bornDensity (phasedPacket r s α p q u) y := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  obtain ⟨x, hx⟩ := exists_wavePhase_eq hδ (-α)
  obtain ⟨y, hy⟩ := exists_wavePhase_eq hδ (Real.pi - α)
  have hx0 : -α + α = 0 := by ring
  have hyπ : Real.pi - α + α = Real.pi := by ring
  have hxden : bornDensity (phasedPacket r s α p q u) x = (r + s) ^ 2 * ‖u‖ ^ 2 := by
    rw [bornDensity_phasedPacket, hx, hx0, Real.cos_zero]
    ring
  have hyden : bornDensity (phasedPacket r s α p q u) y = (r - s) ^ 2 * ‖u‖ ^ 2 := by
    rw [bornDensity_phasedPacket, hy, hyπ, Real.cos_pi]
    ring
  refine ⟨x, y, hxden, hyden, ?_, ?_, ?_⟩
  · rw [hxden, hyden]
    ring
  · rw [hxden, hyden, bornDensity_scaled_planeWave, bornDensity_scaled_planeWave]
    ring
  · rw [hxden, hyden]
    have hdiff : (r + s) ^ 2 * ‖u‖ ^ 2 - (r - s) ^ 2 * ‖u‖ ^ 2 =
        4 * r * s * ‖u‖ ^ 2 := by ring
    rw [hdiff]
    positivity

theorem fringe_ratio_eq_visibility {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) {p q : Vec4}
    (hpq : p ≠ q) (α : ℝ) {u : DiracSpinor} (hu : u ≠ 0) (hden : r ^ 2 + s ^ 2 ≠ 0) :
    ∃ x y : Vec4,
      (bornDensity (phasedPacket r s α p q u) x -
          bornDensity (phasedPacket r s α p q u) y) /
        (bornDensity (phasedPacket r s α p q u) x +
          bornDensity (phasedPacket r s α p q u) y) =
      fringeVisibility r s := by
  obtain ⟨x, y, hx, hy, hsub, hadd, _⟩ := phasedPacket_extremes hr hs hpq α u
  have hsum : bornDensity (phasedPacket r s α p q u) x +
      bornDensity (phasedPacket r s α p q u) y =
      2 * (r ^ 2 + s ^ 2) * ‖u‖ ^ 2 := by
    rw [hadd, bornDensity_scaled_planeWave, bornDensity_scaled_planeWave]
    ring
  refine ⟨x, y, ?_⟩
  rw [hsub, hsum]
  have hN : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  unfold fringeVisibility
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  field_simp [hden, hN, htwo]
  ring

/-! ### Distinguishability and visibility -/

theorem whichMomentum_sq_add_fringeVisibility (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) :
    whichMomentum r s ^ 2 + fringeVisibility r s ^ 2 = 1 := by
  unfold whichMomentum fringeVisibility
  have hden : (r ^ 2 + s ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h
  rw [div_pow, div_pow, sq_abs, ← add_div]
  have hsum : (r ^ 2 - s ^ 2) ^ 2 + (2 * r * s) ^ 2 = (r ^ 2 + s ^ 2) ^ 2 := by ring
  rw [hsum, div_self hden]

theorem fringeVisibility_of_whichMomentum_one (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0)
    (hD : whichMomentum r s = 1) : fringeVisibility r s = 0 := by
  have hid := whichMomentum_sq_add_fringeVisibility r s h
  have hsq : fringeVisibility r s ^ 2 = 0 := by
    have : (1 : ℝ) ^ 2 + fringeVisibility r s ^ 2 = 1 := by simpa [hD] using hid
    linarith
  exact sq_eq_zero_iff.mp hsq

theorem not_definite_and_full_visibility (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) :
    ¬ (whichMomentum r s = 1 ∧ fringeVisibility r s = 1) := by
  intro ⟨hD, hV⟩
  have h0 := fringeVisibility_of_whichMomentum_one r s h hD
  exact zero_ne_one (h0.symm.trans hV)

theorem whichMomentum_definite {r : ℝ} (hr : r ≠ 0) : whichMomentum r 0 = 1 := by
  unfold whichMomentum
  have hsub : r ^ 2 - 0 ^ 2 = r ^ 2 := by ring
  have hden : r ^ 2 + 0 ^ 2 = r ^ 2 := by ring
  rw [hsub, hden, abs_of_nonneg (sq_nonneg r)]
  exact div_self (pow_ne_zero 2 hr)

theorem fringeVisibility_definite (r : ℝ) : fringeVisibility r 0 = 0 := by
  unfold fringeVisibility
  simp

theorem whichMomentum_equal (r : ℝ) : whichMomentum r r = 0 := by
  unfold whichMomentum
  simp

theorem fringeVisibility_equal {r : ℝ} (hr : r ≠ 0) : fringeVisibility r r = 1 := by
  unfold fringeVisibility
  have hden : r ^ 2 + r ^ 2 ≠ 0 := by
    have hrw : r ^ 2 + r ^ 2 = 2 * r ^ 2 := by ring
    rw [hrw]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
  have hnum : 2 * r * r = r ^ 2 + r ^ 2 := by ring
  rw [hnum, div_self hden]

theorem phasedPacket_zero_second (r α : ℝ) (p q : Vec4) (u : DiracSpinor) :
    phasedPacket r 0 α p q u = planeWave p ((r : ℂ) • u) := by
  funext x
  unfold phasedPacket
  simp only [ofReal_zero, zero_mul, zero_smul, add_zero]
  unfold planeWave
  rw [smul_smul, smul_smul, mul_comm]

theorem phasedPacket_definite_no_chartPositionInfo (r α : ℝ) (p q : Vec4) (u : DiracSpinor) :
    ¬ ChartPositionInfo (phasedPacket r 0 α p q u) := by
  rw [phasedPacket_zero_second]
  exact planeWave_no_chartPositionInfo p ((r : ℂ) • u)

theorem definite_momentum_no_position {r : ℝ} (hr : r ≠ 0) (α : ℝ) (p q : Vec4)
    (u : DiracSpinor) :
    whichMomentum r 0 = 1 ∧ fringeVisibility r 0 = 0 ∧
      ¬ ChartPositionInfo (phasedPacket r 0 α p q u) :=
  ⟨whichMomentum_definite hr, fringeVisibility_definite r,
    phasedPacket_definite_no_chartPositionInfo r α p q u⟩

theorem phasedPacket_equal_chartPositionInfo {r : ℝ} (hr : r ≠ 0) {p q : Vec4} (hpq : p ≠ q)
    {u : DiracSpinor} (hu : u ≠ 0) (α : ℝ) :
    ChartPositionInfo (phasedPacket r r α p q u) := by
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  obtain ⟨x, hx⟩ := exists_wavePhase_eq hδ (-α)
  obtain ⟨y, hy⟩ := exists_wavePhase_eq hδ (Real.pi - α)
  have hx0 : -α + α = 0 := by ring
  have hyπ : Real.pi - α + α = Real.pi := by ring
  refine ⟨x, y, ?_⟩
  intro hden
  have hxden : bornDensity (phasedPacket r r α p q u) x = 4 * r ^ 2 * ‖u‖ ^ 2 := by
    rw [bornDensity_phasedPacket, hx, hx0, Real.cos_zero]
    ring
  have hyden : bornDensity (phasedPacket r r α p q u) y = 0 := by
    rw [bornDensity_phasedPacket, hy, hyπ, Real.cos_pi]
    ring
  have hN : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  rw [hxden, hyden] at hden
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)) hN hden

theorem equal_weights_full_visibility {r : ℝ} (hr : r ≠ 0) {p q : Vec4} (hpq : p ≠ q)
    {u : DiracSpinor} (hu : u ≠ 0) (α : ℝ) :
    whichMomentum r r = 0 ∧ fringeVisibility r r = 1 ∧
      ChartPositionInfo (phasedPacket r r α p q u) :=
  ⟨whichMomentum_equal r, fringeVisibility_equal hr,
    phasedPacket_equal_chartPositionInfo hr hpq hu α⟩

theorem phasedPacket_eq_equalPacket (p q : Vec4) (u : DiracSpinor) :
    phasedPacket 1 1 0 p q u = equalPacket p q u := by
  funext x
  unfold phasedPacket equalPacket momentumSum
  rw [Pi.add_apply]
  simp [Complex.exp_zero, one_smul]

/-! ### Calculated fringes -/

theorem half_weight_information :
    whichMomentum 1 (1 / 2) = 3 / 5 ∧
      fringeVisibility 1 (1 / 2) = 4 / 5 ∧
        whichMomentum 1 (1 / 2) ^ 2 + fringeVisibility 1 (1 / 2) ^ 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold whichMomentum
    norm_num
  · unfold fringeVisibility
    norm_num
  · unfold whichMomentum fringeVisibility
    norm_num

/-- The axis fringe of contrast `4` is the case `V = 1`. -/
theorem axis_fringe_full_visibility :
    fringeVisibility 1 1 = 1 ∧
      chartContrast
        (phasedPacket 1 1 0 (0 : Vec4) (Pi.single 1 (1 : ℝ))
          (EuclideanSpace.single 0 (1 : ℂ)))
        0 (Pi.single 1 Real.pi) = 4 := by
  refine ⟨fringeVisibility_equal (by norm_num), ?_⟩
  rw [phasedPacket_eq_equalPacket]
  exact axis_fringe_contrast

end Logic

end DoubleSpacetime
