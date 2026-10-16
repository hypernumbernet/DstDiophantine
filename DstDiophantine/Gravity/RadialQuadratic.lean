import DstDiophantine.Gravity.Weitzenbock
import DstDiophantine.Gravity.Sandwich
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Teleparallel quadratic on the diagonal radial coframe

The coframe \((\sqrt{A},\,A^{-1/2},\,r,\,r\sin\theta)\) induces
\(\mathrm{diag}(-A,\,A^{-1},\,r^2,\,r^2\sin^2\theta)\). Its coordinate torsion
is the spherical-frame anholonomy together with the radial derivative of the
time leg. The quadratic
\[
T=\tfrac14 T_{\rho\mu\nu}T^{\rho\mu\nu}+\tfrac12 T_{\rho\mu\nu}T^{\nu\mu\rho}-T_\rho T^\rho,
\]
indices moved by \(g\), evaluates to \(-2(A+r A')/r^2\).

On the exterior vacuum \(A+r A'=1\) this is \(-2/r^2\), the same value as the
flat spherical frame. The auxiliary expression `(2/r²)(1-√A)²/√A` is not this
quadratic.
-/

namespace DstDiophantine

namespace Gravity

open Real Finset Invariant

noncomputable section

/-- Spacetime metric of the diagonal radial chart, lowered. -/
def radialGDown (A r θ : ℝ) : Fin 4 → ℝ
  | 0 => -A
  | 1 => A⁻¹
  | 2 => r ^ 2
  | 3 => r ^ 2 * sin θ ^ 2

/-- Inverse metric, raised. -/
def radialGUp (A r θ : ℝ) : Fin 4 → ℝ
  | 0 => -A⁻¹
  | 1 => A
  | 2 => (r ^ 2)⁻¹
  | 3 => (r ^ 2 * sin θ ^ 2)⁻¹

/-- Coordinate torsion \(T^\rho{}_{\mu\nu}\) of the diagonal coframe.
`Ap` is the radial derivative \(A'\). Matching on values lets concrete
indices reduce. -/
def radialTUp (A Ap r θ : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  match ρ.1, μ.1, ν.1 with
  | 0, 0, 1 => -(Ap / (2 * A))
  | 0, 1, 0 => Ap / (2 * A)
  | 2, 1, 2 => 1 / r
  | 2, 2, 1 => -(1 / r)
  | 3, 1, 3 => 1 / r
  | 3, 3, 1 => -(1 / r)
  | 3, 2, 3 => cos θ / sin θ
  | 3, 3, 2 => -(cos θ / sin θ)
  | _, _, _ => 0

/-- \(T_{\rho\mu\nu}=g_{\rho\rho}T^\rho{}_{\mu\nu}\). -/
def radialTDown (A Ap r θ : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  radialGDown A r θ ρ * radialTUp A Ap r θ ρ μ ν

/-- \(T^{\rho\mu\nu}=g^{\mu\mu}g^{\nu\nu}T^\rho{}_{\mu\nu}\). -/
def radialTAllUp (A Ap r θ : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  radialGUp A r θ μ * radialGUp A r θ ν * radialTUp A Ap r θ ρ μ ν

/-- Torsion vector \(T_\rho=T^\sigma{}_{\rho\sigma}\). -/
def radialTrace (A Ap r θ : ℝ) (ρ : Fin 4) : ℝ :=
  ∑ σ : Fin 4, radialTUp A Ap r θ σ ρ σ

/-- Raised torsion vector \(T^\rho=g^{\rho\rho}T_\rho\). -/
def radialTraceUp (A Ap r θ : ℝ) (ρ : Fin 4) : ℝ :=
  radialGUp A r θ ρ * radialTrace A Ap r θ ρ

/-- Teleparallel quadratic on the diagonal radial coframe. -/
def radialTeleparallel (A Ap r θ : ℝ) : ℝ :=
  (1 / 4) * (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      radialTDown A Ap r θ ρ μ ν * radialTAllUp A Ap r θ ρ μ ν) +
    (1 / 2) * (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      radialTDown A Ap r θ ρ μ ν * radialTAllUp A Ap r θ ν μ ρ) -
    ∑ ρ : Fin 4, radialTrace A Ap r θ ρ * radialTraceUp A Ap r θ ρ

variable {A Ap r θ : ℝ}

private lemma sum4 (f : Fin 4 → ℝ) : ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_four]

theorem radialTrace_zero (A Ap r θ : ℝ) : radialTrace A Ap r θ 0 = 0 := by
  rw [radialTrace, sum4]
  simp [radialTUp]

theorem radialTrace_one (A Ap r θ : ℝ) :
    radialTrace A Ap r θ 1 = Ap / (2 * A) + 2 / r := by
  rw [radialTrace, sum4]
  simp [radialTUp]
  ring

theorem radialTrace_two (A Ap r θ : ℝ) :
    radialTrace A Ap r θ 2 = cos θ / sin θ := by
  rw [radialTrace, sum4]
  simp [radialTUp]

theorem radialTrace_three (A Ap r θ : ℝ) : radialTrace A Ap r θ 3 = 0 := by
  rw [radialTrace, sum4]
  simp [radialTUp]

private lemma squareTerm_expand :
    ∀ ρ μ ν : Fin 4,
      radialTDown A Ap r θ ρ μ ν * radialTAllUp A Ap r θ ρ μ ν =
        radialGDown A r θ ρ * radialGUp A r θ μ * radialGUp A r θ ν *
          (radialTUp A Ap r θ ρ μ ν) ^ 2 := by
  intro ρ μ ν
  simp only [radialTDown, radialTAllUp]
  ring

private lemma crossTerm_expand :
    ∀ ρ μ ν : Fin 4,
      radialTDown A Ap r θ ρ μ ν * radialTAllUp A Ap r θ ν μ ρ =
        radialGDown A r θ ρ * radialGUp A r θ μ * radialGUp A r θ ρ *
          radialTUp A Ap r θ ρ μ ν * radialTUp A Ap r θ ν μ ρ := by
  intro ρ μ ν
  simp only [radialTDown, radialTAllUp]
  ring

/-- The three quadratic pieces, cleared of the metric factors. -/
private lemma square_contraction (hA : A ≠ 0) (hr : r ≠ 0) (hs : sin θ ≠ 0) :
    ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
        radialTDown A Ap r θ ρ μ ν * radialTAllUp A Ap r θ ρ μ ν =
      4 * A / r ^ 2 + 2 * (cos θ / sin θ) ^ 2 / r ^ 2 + Ap ^ 2 / (2 * A) := by
  simp_rw [sum4, squareTerm_expand]
  simp [radialGDown, radialGUp, radialTUp]
  field_simp [hA, hr, hs]
  ring

private lemma cross_contraction (hA : A ≠ 0) (hr : r ≠ 0) (hs : sin θ ≠ 0) :
    ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
        radialTDown A Ap r θ ρ μ ν * radialTAllUp A Ap r θ ν μ ρ =
      2 * A / r ^ 2 + (cos θ / sin θ) ^ 2 / r ^ 2 + Ap ^ 2 / (4 * A) := by
  simp_rw [sum4, crossTerm_expand]
  simp [radialGDown, radialGUp, radialTUp]
  field_simp [hA, hr, hs]
  ring

private lemma trace_contraction (hA : A ≠ 0) (hr : r ≠ 0) (hs : sin θ ≠ 0) :
    ∑ ρ : Fin 4, radialTrace A Ap r θ ρ * radialTraceUp A Ap r θ ρ =
      4 * A / r ^ 2 + 2 * Ap / r + (cos θ / sin θ) ^ 2 / r ^ 2 +
        Ap ^ 2 / (4 * A) := by
  rw [sum4]
  simp only [radialTraceUp, radialTrace_zero, radialTrace_one, radialTrace_two,
    radialTrace_three, radialGUp]
  field_simp [hA, hr, hs]
  ring

/-- The teleparallel quadratic is \(-2(A + r A')/r^2\). -/
theorem radialTeleparallel_eq (hA : A ≠ 0) (hr : r ≠ 0) (hs : sin θ ≠ 0) :
    radialTeleparallel A Ap r θ = -2 * (A + r * Ap) / r ^ 2 := by
  unfold radialTeleparallel
  rw [square_contraction hA hr hs, cross_contraction hA hr hs, trace_contraction hA hr hs]
  field_simp [hr]
  ring

/-- Departure from the flat spherical value is the vacuum obstruction. -/
theorem radialTeleparallel_sub_spherical (hA : A ≠ 0) (hr : r ≠ 0) (hs : sin θ ≠ 0) :
    radialTeleparallel A Ap r θ - (-2 / r ^ 2) =
      -2 * (A + r * Ap - 1) / r ^ 2 := by
  rw [radialTeleparallel_eq hA hr hs]
  field_simp [hr]
  ring

/-- Flat spherical frame: \(A=1\), \(A'=0\) gives \(T=-2/r^2\). -/
theorem radialTeleparallel_flat (hr : r ≠ 0) (hs : sin θ ≠ 0) :
    radialTeleparallel 1 0 r θ = -2 / r ^ 2 := by
  rw [radialTeleparallel_eq (by norm_num) hr hs]
  ring

theorem schwarzschild_vacuum_obstruction {rs r : ℝ} (hr : r ≠ 0) :
    schwarzschildA rs r + r * (rs / r ^ 2) = 1 := by
  unfold schwarzschildA
  field_simp [hr]
  ring

/-- Exterior Schwarzschild freezes the quadratic at the spherical-frame value. -/
theorem radialTeleparallel_schwarzschild {rs r θ : ℝ}
    (h : IsExterior rs r) (hs : sin θ ≠ 0) :
    radialTeleparallel (schwarzschildA rs r) (rs / r ^ 2) r θ = -2 / r ^ 2 := by
  have hr : r ≠ 0 := (lt_trans h.1 h.2).ne'
  have hA : schwarzschildA rs r ≠ 0 := (schwarzschildA_pos h).ne'
  rw [radialTeleparallel_eq hA hr hs, schwarzschild_vacuum_obstruction hr]
  field_simp [hr]

/-- The auxiliary closed form is positive on the exterior, hence not \(-2/r^2\). -/
theorem schwarzschildTeleparallelT_ne_radial {rs r θ : ℝ}
    (h : IsExterior rs r) (hs : sin θ ≠ 0) :
    schwarzschildTeleparallelT rs r ≠
      radialTeleparallel (schwarzschildA rs r) (rs / r ^ 2) r θ := by
  rw [radialTeleparallel_schwarzschild h hs]
  have hr : 0 < r := lt_trans h.1 h.2
  have hA := schwarzschildA_pos h
  have hA1 : schwarzschildA rs r ≠ 1 := by
    unfold schwarzschildA
    have : 0 < rs / r := div_pos h.1 hr
    linarith
  have hsA : 0 < Real.sqrt (schwarzschildA rs r) := Real.sqrt_pos.mpr hA
  have hsne : Real.sqrt (schwarzschildA rs r) ≠ 1 := by
    intro hs1
    apply hA1
    rw [← Real.sq_sqrt hA.le, hs1]
    norm_num
  have hpos : 0 < schwarzschildTeleparallelT rs r := by
    unfold schwarzschildTeleparallelT
    refine div_pos ?_ hsA
    refine mul_pos (div_pos (by norm_num) (sq_pos_of_pos hr))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hsne.symm))
  have hneg : -2 / r ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hr)
  exact (ne_of_lt (lt_trans hneg hpos)).symm

/-- On the exterior vacuum, \(J=\tfrac12\varphi^2>0\) while \(r^2 T=-2\). -/
theorem schwarzschild_J_pos_T_frozen {rs r θ : ℝ}
    (h : IsExterior rs r) (hs : sin θ ≠ 0) :
    0 < J (radialBoostParams rs r) ∧
      r ^ 2 * radialTeleparallel (schwarzschildA rs r) (rs / r ^ 2) r θ = -2 := by
  have hr : 0 < r := lt_trans h.1 h.2
  refine ⟨?_, ?_⟩
  · rw [J_radialBoostParams]
    have hA := schwarzschildA_pos h
    have hA1 : schwarzschildA rs r < 1 := by
      unfold schwarzschildA
      have : 0 < rs / r := div_pos h.1 hr
      linarith
    have hlog : Real.log (schwarzschildA rs r) < 0 :=
      (Real.log_lt_log hA hA1).trans_eq Real.log_one
    have hφ : 0 < schwarzschildRapidity rs r := by
      have hlog' : Real.log (1 - rs / r) < 0 := by simpa [schwarzschildA] using hlog
      unfold schwarzschildRapidity
      linarith
    positivity
  · rw [radialTeleparallel_schwarzschild h hs]
    field_simp [hr.ne']

end

end Gravity

end DstDiophantine
