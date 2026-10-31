import DstDiophantine.Gravity.EMControl
import DstDiophantine.Gravity.ShieldHold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A circular cycle and the hold it costs

The substitution \(\theta\mapsto\theta+eA\) along a Coulomb-gauge circular
potential is a dual-only increment whose square does not breathe. A full
cycle stays in the admissible cone only inside a two-sided margin on the
axes transverse to the beam.

## Paper boundary (do **not** claim)

No helicity-odd drive of \(J\), no Maxwell equation, and no identification
of the stiffness force with a laboratory field. The bound \(\pi^2/32\) is a
bound on the dual-angle oscillation in the units of \(J\), not a laboratory
field strength. Vanishing stiffness power along the wave is not free fall.

## What is proved

* Write \(\rho=\lvert e E_0/\omega\rvert\). For helicity \(\sigma^2=1\), the
  coupled state lies in the cone at every phase if and only if the seed does
  and each transverse axis has dual bias at least \(\rho\) and wall slack at
  least \(\rho\). Hence \(\rho\le\pi/4\), and the ponderomotive drop of mean
  \(J\) is at most \(\pi^2/32\). Both bounds are attained on a pure-dual
  transverse seed of angle \(\pi/4\).
* The cycle raises mean unsigned mass by that drop, and mean stiffness by
  \(m\) times the drop. When the transverse rapidities already agree, the
  stiffness equals that value at every phase, and the stiffness forces
  exchange no power with the dual velocity along the wave.
* An isotropic aligned seed admits a cycle only for \(\rho\le\pi/6\),
  attained at rapidity \(\pi/6\), where the constant potential is
  \(m\pi^2/72\). A transverse wall, the isotropic wall included, admits
  only \(\rho=0\).
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-! ### Amplitude of the dual-angle oscillation -/

/-- \(\rho=\lvert e E_0/\omega\rvert\). -/
noncomputable def circAmp (e E0 ω : ℝ) : ℝ :=
  |e * (E0 / ω)|

theorem circAmp_nonneg (e E0 ω : ℝ) : 0 ≤ circAmp e E0 ω :=
  abs_nonneg _

theorem ponderomotive_eq_half_circAmp (e E0 ω : ℝ) :
    (e ^ 2 / 2) * (E0 / ω) ^ 2 = (1 / 2) * circAmp e E0 ω ^ 2 := by
  unfold circAmp
  calc (e ^ 2 / 2) * (E0 / ω) ^ 2
      = (1 / 2) * (e * (E0 / ω)) ^ 2 := by ring
    _ = (1 / 2) * |e * (E0 / ω)| ^ 2 := by rw [← sq_abs]

theorem abs_of_helicity {σ : ℝ} (hσ : σ ^ 2 = 1) : |σ| = 1 := by
  rcases sq_eq_one_iff.mp hσ with rfl | rfl <;> simp

theorem circular_increment_zero (e σ E0 ω ψ : ℝ) :
    e * circularPotential σ E0 ω ψ 0 = (e * (E0 / ω)) * Real.sin ψ := by
  simp [circularPotential]
  ring

theorem circular_increment_one (e σ E0 ω ψ : ℝ) :
    e * circularPotential σ E0 ω ψ 1 =
      (-σ) * (e * (E0 / ω)) * Real.cos ψ := by
  simp [circularPotential]
  ring

theorem circular_increment_two (e σ E0 ω ψ : ℝ) :
    e * circularPotential σ E0 ω ψ 2 = 0 := by
  simp [circularPotential]

theorem abs_increment_zero (e σ E0 ω ψ : ℝ) :
    |e * circularPotential σ E0 ω ψ 0| =
      circAmp e E0 ω * |Real.sin ψ| := by
  rw [circular_increment_zero, abs_mul]
  rfl

theorem abs_increment_one {e σ E0 ω ψ : ℝ} (hσ : σ ^ 2 = 1) :
    |e * circularPotential σ E0 ω ψ 1| =
      circAmp e E0 ω * |Real.cos ψ| := by
  rw [circular_increment_one]
  rw [abs_mul, abs_mul, abs_neg, abs_of_helicity hσ, one_mul]
  rfl

/-- Dual bias and wall slack on the two axes transverse to the beam. -/
def TransverseMargin (p : TorsionParams) (ρ : ℝ) : Prop :=
  ρ ≤ p.beta 0 ∧ ρ ≤ p.beta 1 ∧
    p.alpha 0 + p.beta 0 + ρ ≤ Real.pi / 2 ∧
    p.alpha 1 + p.beta 1 + ρ ≤ Real.pi / 2

private theorem beta_ge_abs_of_both {β s : ℝ}
    (hp : 0 ≤ β + s) (hm : 0 ≤ β + (-s)) : |s| ≤ β := by
  rw [abs_le]
  constructor <;> linarith

private theorem sum_ge_abs_of_both {σ β s wall : ℝ}
    (hp : σ + β + s ≤ wall) (hm : σ + β + (-s) ≤ wall) :
    σ + β + |s| ≤ wall := by
  rcases le_total s 0 with hs | hs
  · rw [abs_of_nonpos hs]
    linarith
  · rw [abs_of_nonneg hs]
    linarith

/-! ### The cycle fits in the cone exactly on the margin -/

theorem cycle_admissible_iff {p : TorsionParams} {e σ E0 ω : ℝ}
    (hσ : σ ^ 2 = 1) :
    (∀ ψ : ℝ,
        IsAdmissibleContinuous
          (coupleA p e (circularPotential σ E0 ω ψ))) ↔
      IsAdmissibleContinuous p ∧ TransverseMargin p (circAmp e E0 ω) := by
  constructor
  · intro h
    let s : ℝ := e * (E0 / ω)
    have hs : circAmp e E0 ω = |s| := rfl
    have h0 := h 0
    have hpi := h Real.pi
    have hhalf := h (Real.pi / 2)
    have hthree := h (3 * Real.pi / 2)
    have inc0_zero : e * circularPotential σ E0 ω 0 0 = 0 := by
      simp [circularPotential, Real.sin_zero]
    have inc1_half : e * circularPotential σ E0 ω (Real.pi / 2) 1 = 0 := by
      simp [circularPotential, Real.cos_pi_div_two]
    have inc2 : ∀ ψ, e * circularPotential σ E0 ω ψ 2 = 0 :=
      fun ψ => circular_increment_two e σ E0 ω ψ
    have hseed : IsAdmissibleContinuous p := by
      intro a
      fin_cases a
      · have hβ := (h0 0).2.1
        have hsum := (h0 0).2.2
        refine ⟨(h0 0).1, ?_, ?_⟩
        · simpa [coupleA, inc0_zero] using hβ
        · simpa [coupleA, inc0_zero, add_assoc] using hsum
      · have hβ := (hhalf 1).2.1
        have hsum := (hhalf 1).2.2
        refine ⟨(hhalf 1).1, ?_, ?_⟩
        · simpa [coupleA, inc1_half] using hβ
        · simpa [coupleA, inc1_half, add_assoc] using hsum
      · have hβ := (h0 2).2.1
        have hsum := (h0 2).2.2
        refine ⟨(h0 2).1, ?_, ?_⟩
        · simpa [coupleA, inc2 0] using hβ
        · simpa [coupleA, inc2 0, add_assoc] using hsum
    have inc0_half : e * circularPotential σ E0 ω (Real.pi / 2) 0 = s := by
      simp [circularPotential, Real.sin_pi_div_two, s]
    have inc0_three :
        e * circularPotential σ E0 ω (3 * Real.pi / 2) 0 = -s := by
      simp [circularPotential, sin_three_pi_div_two, s]
    have hβ0 : |s| ≤ p.beta 0 := by
      have hp := (hhalf 0).2.1
      have hm := (hthree 0).2.1
      have hp' : 0 ≤ p.beta 0 + s := by simpa [coupleA, inc0_half] using hp
      have hm' : 0 ≤ p.beta 0 + (-s) := by simpa [coupleA, inc0_three] using hm
      exact beta_ge_abs_of_both hp' hm'
    have hwall0 : p.alpha 0 + p.beta 0 + |s| ≤ Real.pi / 2 := by
      have hp := (hhalf 0).2.2
      have hm := (hthree 0).2.2
      have hp' : p.alpha 0 + p.beta 0 + s ≤ Real.pi / 2 := by
        simpa [coupleA, inc0_half, add_assoc] using hp
      have hm' : p.alpha 0 + p.beta 0 + (-s) ≤ Real.pi / 2 := by
        simpa [coupleA, inc0_three, add_assoc] using hm
      exact sum_ge_abs_of_both hp' hm'
    have inc1_zero : e * circularPotential σ E0 ω 0 1 = -σ * s := by
      simp [circularPotential, Real.cos_zero, s]
      ring
    have inc1_pi : e * circularPotential σ E0 ω Real.pi 1 = σ * s := by
      simp [circularPotential, Real.cos_pi, s]
      ring
    have hβ1 : |s| ≤ p.beta 1 := by
      have hz := (h0 1).2.1
      have hp := (hpi 1).2.1
      have hz' : 0 ≤ p.beta 1 + -(σ * s) := by
        have hz0 : 0 ≤ p.beta 1 + -σ * s := by simpa [coupleA, inc1_zero] using hz
        have heq : -σ * s = -(σ * s) := by ring
        linarith
      have hp' : 0 ≤ p.beta 1 + σ * s := by simpa [coupleA, inc1_pi] using hp
      have habs : |σ * s| ≤ p.beta 1 := beta_ge_abs_of_both hp' hz'
      rwa [abs_mul, abs_of_helicity hσ, one_mul] at habs
    have hwall1 : p.alpha 1 + p.beta 1 + |s| ≤ Real.pi / 2 := by
      have hz := (h0 1).2.2
      have hp := (hpi 1).2.2
      have hz' : p.alpha 1 + p.beta 1 + -(σ * s) ≤ Real.pi / 2 := by
        have hz0 : p.alpha 1 + p.beta 1 + -σ * s ≤ Real.pi / 2 := by
          simpa [coupleA, inc1_zero, add_assoc] using hz
        have heq : -σ * s = -(σ * s) := by ring
        linarith
      have hp' : p.alpha 1 + p.beta 1 + σ * s ≤ Real.pi / 2 := by
        simpa [coupleA, inc1_pi, add_assoc] using hp
      have habs := sum_ge_abs_of_both hp' hz'
      rwa [abs_mul, abs_of_helicity hσ, one_mul] at habs
    refine ⟨hseed, ?_⟩
    rw [hs]
    exact ⟨hβ0, hβ1, hwall0, hwall1⟩
  · intro h ψ a
    rcases h with ⟨hseed, hmargin⟩
    have hρ0 : 0 ≤ circAmp e E0 ω := circAmp_nonneg e E0 ω
    fin_cases a
    · have hd := abs_increment_zero e σ E0 ω ψ
      have hsin : |Real.sin ψ| ≤ 1 := Real.abs_sin_le_one ψ
      have habs : |e * circularPotential σ E0 ω ψ 0| ≤ circAmp e E0 ω := by
        rw [hd]
        exact mul_le_of_le_one_right hρ0 hsin
      rcases abs_le.mp habs with ⟨hlo, hhi⟩
      refine ⟨(hseed 0).1, ?_, ?_⟩
      · have hβ : circAmp e E0 ω ≤ p.beta 0 := hmargin.1
        have hineq :
            0 ≤ p.beta 0 + e * circularPotential σ E0 ω ψ 0 := by
          linarith
        simpa [coupleA] using hineq
      · have hwall := hmargin.2.2.1
        have hineq :
            p.alpha 0 + p.beta 0 + e * circularPotential σ E0 ω ψ 0 ≤
              Real.pi / 2 := by
          linarith
        simpa [coupleA, add_assoc] using hineq
    · have hd := abs_increment_one (e := e) (σ := σ) (E0 := E0) (ω := ω)
        (ψ := ψ) hσ
      have hcos : |Real.cos ψ| ≤ 1 := Real.abs_cos_le_one ψ
      have habs : |e * circularPotential σ E0 ω ψ 1| ≤ circAmp e E0 ω := by
        rw [hd]
        exact mul_le_of_le_one_right hρ0 hcos
      rcases abs_le.mp habs with ⟨hlo, hhi⟩
      refine ⟨(hseed 1).1, ?_, ?_⟩
      · have hβ : circAmp e E0 ω ≤ p.beta 1 := hmargin.2.1
        have hineq :
            0 ≤ p.beta 1 + e * circularPotential σ E0 ω ψ 1 := by
          linarith
        simpa [coupleA] using hineq
      · have hwall := hmargin.2.2.2
        have hineq :
            p.alpha 1 + p.beta 1 + e * circularPotential σ E0 ω ψ 1 ≤
              Real.pi / 2 := by
          linarith
        simpa [coupleA, add_assoc] using hineq
    · have hinc := circular_increment_two e σ E0 ω ψ
      have haxis := hseed 2
      refine ⟨haxis.1, ?_, ?_⟩
      · simpa [coupleA, hinc] using haxis.2.1
      · simpa [coupleA, hinc, add_assoc] using haxis.2.2

theorem circAmp_le_pi_div_four {p : TorsionParams} {e σ E0 ω : ℝ}
    (hσ : σ ^ 2 = 1)
    (h : ∀ ψ : ℝ,
      IsAdmissibleContinuous (coupleA p e (circularPotential σ E0 ω ψ))) :
    circAmp e E0 ω ≤ Real.pi / 4 := by
  rcases (cycle_admissible_iff hσ).mp h with ⟨hseed, hβ, -, hwall, -⟩
  have hα : 0 ≤ p.alpha 0 := (hseed 0).1
  linarith

/-- A full cycle drops mean \(J\) by at most \(\pi^2/32\). -/
theorem ponderomotive_le_pi_sq_div_32 {p : TorsionParams} {e σ E0 ω : ℝ}
    (hσ : σ ^ 2 = 1)
    (h : ∀ ψ : ℝ,
      IsAdmissibleContinuous (coupleA p e (circularPotential σ E0 ω ψ))) :
    (e ^ 2 / 2) * (E0 / ω) ^ 2 ≤ Real.pi ^ 2 / 32 := by
  rw [ponderomotive_eq_half_circAmp]
  have hρ := circAmp_le_pi_div_four hσ h
  have hρ0 := circAmp_nonneg e E0 ω
  have hsq : circAmp e E0 ω ^ 2 ≤ (Real.pi / 4) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hρ0 hρ
  have hhalf : (1 / 2) * (Real.pi / 4) ^ 2 = Real.pi ^ 2 / 32 := by ring
  linarith

/-! ### The bound is attained -/

noncomputable def transversePureDual : TorsionParams where
  alpha := fun _ => 0
  beta := fun
    | 0 => Real.pi / 4
    | 1 => Real.pi / 4
    | _ => 0

theorem transversePureDual_admissible :
    IsAdmissibleContinuous transversePureDual := by
  intro a
  fin_cases a
  · change 0 ≤ (0 : ℝ) ∧ 0 ≤ Real.pi / 4 ∧ 0 + Real.pi / 4 ≤ Real.pi / 2
    exact ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  · change 0 ≤ (0 : ℝ) ∧ 0 ≤ Real.pi / 4 ∧ 0 + Real.pi / 4 ≤ Real.pi / 2
    exact ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  · change 0 ≤ (0 : ℝ) ∧ 0 ≤ (0 : ℝ) ∧ 0 + 0 ≤ Real.pi / 2
    exact ⟨by norm_num, by norm_num, by linarith [Real.pi_pos]⟩

theorem circAmp_transverse_extremal :
    circAmp 1 (Real.pi / 4) 1 = Real.pi / 4 := by
  unfold circAmp
  have hpi : 0 ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  rw [abs_of_nonneg]
  · ring
  · linarith

theorem transverse_extremal_margin :
    TransverseMargin transversePureDual (circAmp 1 (Real.pi / 4) 1) := by
  rw [circAmp_transverse_extremal]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [transversePureDual] <;>
    linarith [Real.pi_pos]

theorem cycle_admissible_transverse_extremal {σ : ℝ} (hσ : σ ^ 2 = 1) :
    ∀ ψ : ℝ,
      IsAdmissibleContinuous
        (coupleA transversePureDual 1
          (circularPotential σ (Real.pi / 4) 1 ψ)) :=
  (cycle_admissible_iff hσ).mpr
    ⟨transversePureDual_admissible, transverse_extremal_margin⟩

theorem ponderomotive_transverse_extremal :
    ((1 : ℝ) ^ 2 / 2) * ((Real.pi / 4) / 1) ^ 2 = Real.pi ^ 2 / 32 := by
  ring

/-! ### Mass and stiffness along the cycle -/

theorem mass_coupleA (p : TorsionParams) (e : ℝ) (A : Fin 3 → ℝ) :
    mass (coupleA p e A) =
      mass p + e * dot3 p.beta A + (e ^ 2 / 2) * ampSq A := by
  have h := coupleA_conserves_J_add_mass p e A
  rw [J_coupleA] at h
  linarith

theorem quadMean_mass_coupleA_circular (p : TorsionParams) (e E0 ω : ℝ)
    {σ : ℝ} (hσ : σ ^ 2 = 1) :
    quadMean (fun ψ =>
        mass (coupleA p e (circularPotential σ E0 ω ψ))) =
      mass p + (e ^ 2 / 2) * (E0 / ω) ^ 2 := by
  have hfun :
      (fun ψ : ℝ => mass (coupleA p e (circularPotential σ E0 ω ψ))) =
        fun ψ => (mass p + (e ^ 2 / 2) * (E0 / ω) ^ 2) +
          e * dot3 p.beta (circularPotential σ E0 ω ψ) := by
    ext ψ
    rw [mass_coupleA, circularPotential_ampSq hσ]
    ring
  rw [hfun, quadMean_add, quadMean_const, quadMean_smul,
    quadMean_dot_circularPotential, mul_zero, add_zero]

theorem lagSq_coupleA (p : TorsionParams) (e : ℝ) (A : Fin 3 → ℝ) :
    lagSq (coupleA p e A) =
      lagSq p -
        2 * e * dot3 (fun a => p.alpha a - p.beta a) A +
        e ^ 2 * ampSq A := by
  rw [lagSq, lagSq, dot3, ampSq]
  simp only [coupleA, Fin.sum_univ_three]
  ring

theorem quadMean_stiffness_coupleA_circular
    (m : ℝ) (p : TorsionParams) (e E0 ω : ℝ) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    quadMean (fun ψ =>
        stiffnessPotential m (coupleA p e (circularPotential σ E0 ω ψ))) =
      stiffnessPotential m p + m * ((e ^ 2 / 2) * (E0 / ω) ^ 2) := by
  have hfun :
      (fun ψ : ℝ =>
          stiffnessPotential m (coupleA p e (circularPotential σ E0 ω ψ))) =
        fun ψ => stiffnessPotential m p +
          m * ((e ^ 2 / 2) * (E0 / ω) ^ 2) +
          -(m * e) * dot3 (fun a => p.alpha a - p.beta a)
            (circularPotential σ E0 ω ψ) := by
    ext ψ
    rw [stiffnessPotential_eq_lag, lagSq_coupleA, circularPotential_ampSq hσ,
      stiffnessPotential_eq_lag]
    ring
  rw [hfun, quadMean_add]
  have hcross :
      quadMean (fun ψ =>
          dot3 (fun a => p.alpha a - p.beta a)
            (circularPotential σ E0 ω ψ)) =
        0 :=
    quadMean_dot_circularPotential (fun a => p.alpha a - p.beta a) σ E0 ω
  have hsmul :
      quadMean (fun ψ =>
          -(m * e) *
            dot3 (fun a => p.alpha a - p.beta a)
              (circularPotential σ E0 ω ψ)) =
        0 := by
    rw [quadMean_smul, hcross, mul_zero]
  rw [hsmul, add_zero, quadMean_const]

theorem stiffness_circular_of_transverse_aligned {m : ℝ} {p : TorsionParams}
    {e σ E0 ω ψ : ℝ}
    (h0 : p.alpha 0 = p.beta 0) (h1 : p.alpha 1 = p.beta 1)
    (hσ : σ ^ 2 = 1) :
    stiffnessPotential m (coupleA p e (circularPotential σ E0 ω ψ)) =
      stiffnessPotential m p + m * ((e ^ 2 / 2) * (E0 / ω) ^ 2) := by
  rw [stiffnessPotential_eq_lag, lagSq_coupleA, circularPotential_ampSq hσ,
    stiffnessPotential_eq_lag]
  have hcross :
      dot3 (fun a => p.alpha a - p.beta a) (circularPotential σ E0 ω ψ) = 0 := by
    simp only [dot3, circularPotential, Fin.sum_univ_three, h0, h1]
    ring
  rw [hcross]
  ring

/-- Stiffness forces do no work on a transversely aligned seed, because a
circular potential is orthogonal to its formal time derivative. -/
theorem stiffness_power_circular_of_transverse_aligned {m : ℝ}
    {p : TorsionParams} {e σ E0 ω ψ : ℝ}
    (h0 : p.alpha 0 = p.beta 0) (h1 : p.alpha 1 = p.beta 1)
    (hσ : σ ^ 2 = 1) :
    holdPower
        (fun a => m * ((coupleA p e (circularPotential σ E0 ω ψ)).alpha a -
          (coupleA p e (circularPotential σ E0 ω ψ)).beta a))
        (fun a => m * ((coupleA p e (circularPotential σ E0 ω ψ)).alpha a -
          (coupleA p e (circularPotential σ E0 ω ψ)).beta a))
        (fun _ => 0)
        (fun a => e * circularPotentialDt σ E0 ψ a) =
      0 := by
  unfold holdPower
  simp only [coupleA, Fin.sum_univ_three, circularPotential, circularPotentialDt,
    h0, h1]
  ring_nf
  rw [hσ]
  ring

/-! ### Isotropic aligned seeds, and a transverse wall -/

noncomputable def isotropicSeed (φ : ℝ) : TorsionParams where
  alpha := fun _ => φ
  beta := fun _ => φ

theorem isotropicSeed_admissible {φ : ℝ} (h0 : 0 ≤ φ) (hφ : φ ≤ Real.pi / 4) :
    IsAdmissibleContinuous (isotropicSeed φ) := by
  intro a
  fin_cases a <;>
    simp only [isotropicSeed] <;>
    refine ⟨h0, h0, ?_⟩ <;>
    linarith

theorem isotropicSeed_aligned (φ : ℝ) :
    (isotropicSeed φ).alpha 0 = (isotropicSeed φ).beta 0 ∧
      (isotropicSeed φ).alpha 1 = (isotropicSeed φ).beta 1 := by
  simp [isotropicSeed]

theorem circAmp_le_pi_div_six_of_isotropic {φ e σ E0 ω : ℝ} (hσ : σ ^ 2 = 1)
    (h : ∀ ψ : ℝ,
      IsAdmissibleContinuous
        (coupleA (isotropicSeed φ) e (circularPotential σ E0 ω ψ))) :
    circAmp e E0 ω ≤ Real.pi / 6 := by
  rcases (cycle_admissible_iff hσ).mp h with ⟨-, hβ0, -, hwall0, -⟩
  have hβ : circAmp e E0 ω ≤ φ := by simpa [isotropicSeed] using hβ0
  have hwall : circAmp e E0 ω ≤ Real.pi / 2 - 2 * φ := by
    simp only [isotropicSeed] at hwall0
    linarith
  rcases le_total φ (Real.pi / 6) with hle | hge
  · linarith
  · have : Real.pi / 2 - 2 * φ ≤ Real.pi / 6 := by linarith
    linarith

theorem circAmp_isotropic_sixth :
    circAmp 1 (Real.pi / 6) 1 = Real.pi / 6 := by
  unfold circAmp
  rw [abs_of_nonneg]
  · ring
  · linarith [Real.pi_pos]

theorem cycle_admissible_isotropic_sixth {σ : ℝ} (hσ : σ ^ 2 = 1) :
    ∀ ψ : ℝ,
      IsAdmissibleContinuous
        (coupleA (isotropicSeed (Real.pi / 6)) 1
          (circularPotential σ (Real.pi / 6) 1 ψ)) := by
  refine (cycle_admissible_iff hσ).mpr ⟨?_, ?_⟩
  · exact isotropicSeed_admissible (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  · rw [circAmp_isotropic_sixth]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [isotropicSeed] <;>
      linarith [Real.pi_pos]

theorem stiffness_isotropic_sixth {m ψ σ : ℝ} (hσ : σ ^ 2 = 1) :
    stiffnessPotential m
        (coupleA (isotropicSeed (Real.pi / 6)) 1
          (circularPotential σ (Real.pi / 6) 1 ψ)) =
      m * (Real.pi ^ 2 / 72) := by
  have halign := isotropicSeed_aligned (Real.pi / 6)
  have hst := stiffness_circular_of_transverse_aligned (m := m)
    (p := isotropicSeed (Real.pi / 6)) (e := 1) (σ := σ)
    (E0 := Real.pi / 6) (ω := 1) (ψ := ψ) halign.1 halign.2 hσ
  have hseed : stiffnessPotential m (isotropicSeed (Real.pi / 6)) = 0 := by
    rw [stiffnessPotential_eq_lag, lagSq]
    simp [isotropicSeed]
  rw [hst, hseed]
  ring

theorem circAmp_eq_zero_of_transverse_wall {p : TorsionParams} {e σ E0 ω : ℝ}
    (hσ : σ ^ 2 = 1)
    (hwall : p.alpha 0 + p.beta 0 = Real.pi / 2 ∨
      p.alpha 1 + p.beta 1 = Real.pi / 2)
    (h : ∀ ψ : ℝ,
      IsAdmissibleContinuous (coupleA p e (circularPotential σ E0 ω ψ))) :
    circAmp e E0 ω = 0 := by
  rcases (cycle_admissible_iff hσ).mp h with ⟨-, -, -, hwall0, hwall1⟩
  have hρ := circAmp_nonneg e E0 ω
  rcases hwall with h0 | h1
  · linarith
  · linarith

theorem circAmp_eq_zero_of_isotropic_wall {e σ E0 ω : ℝ} (hσ : σ ^ 2 = 1)
    (h : ∀ ψ : ℝ,
      IsAdmissibleContinuous
        (coupleA (isotropicSeed (Real.pi / 4)) e
          (circularPotential σ E0 ω ψ))) :
    circAmp e E0 ω = 0 := by
  refine circAmp_eq_zero_of_transverse_wall hσ ?_ h
  left
  simp [isotropicSeed]
  ring

end Gravity

end DstDiophantine
