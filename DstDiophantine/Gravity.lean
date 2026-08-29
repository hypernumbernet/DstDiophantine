import DstDiophantine.Gravity.Identification
import DstDiophantine.Gravity.JTDictionary
import DstDiophantine.Gravity.Tetrad
import DstDiophantine.Gravity.NewtonFromLight
import DstDiophantine.Gravity.EventBoundary
import DstDiophantine.Gravity.CoulombFromDual
import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Gravity.CompactS3
import DstDiophantine.Gravity.NuclearLayer
import DstDiophantine.Gravity.DualRotorDynamics

/-!
# Gravity / PGA–TEGR chart layer

Re-exports the chart-level TEGR scaffolding (coframe, sandwich scales,
Schwarzschild tetrad, Weitzenböck torsion, motor-induced frame vectors,
and the `J` / `J_field` / `T` dictionary with naive-identification rejections
and the closed radial-boost form in `JTDictionary`),
plus the exploratory SI / \(c\to G\) hypothesis layer (`SI`, `NewtonFromLight`),
the labelled quasi-horizon cutoff (`EventBoundary`), the electromagnetic
exploratory layer (`CoulombFromDual`, `ElectronShell`), the galactic
S³ cotangent exploratory layer (`CompactS3`; no `dst_derives_a0` / `dst_derives_G`),
and the nuclear-layer exploratory diagnostics (`NuclearLayer`; no
`dst_derives_alpha_s` / `dst_derives_lambdaN` / `dst_derives_Amax`),
the closed form of `gammaEff`, and the Euler–Lagrange identities of
`DualRotorDynamics`.
-/

namespace DstDiophantine

namespace Gravity

open Invariant

/-- Regression: closed-form dictionary \(T=(4/r^2)(\cosh\sqrt{2J}-1)\). -/
example {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      teleparallelTofJ (J (radialBoostParams rs r)) r :=
  schwarzschild_T_eq_teleparallelTofJ h

/-- Regression: sandwich \(4J\le r^2 T\) and \(T\le 4J_{\mathrm{field}}\). -/
example {rs r : ℝ} (h : IsExterior rs r) :
    4 * J (radialBoostParams rs r) ≤
      r ^ 2 * schwarzschildTeleparallelT rs r ∧
    schwarzschildTeleparallelT rs r ≤ 4 * J_field rs r :=
  ⟨four_J_le_r_sq_T h, T_le_four_J_field h⟩

/-- Regression: naive \(J_{\mathrm{field}}=\tfrac12 T\) holds on at most one sphere. -/
example {rs r1 r2 : ℝ}
    (h1 : IsExterior rs r1) (h2 : IsExterior rs r2)
    (heq1 : J_field rs r1 = (1 / 2) * schwarzschildTeleparallelT rs r1)
    (heq2 : J_field rs r2 = (1 / 2) * schwarzschildTeleparallelT rs r2) :
    r1 = r2 :=
  naive_half_ratio_at_most_one_sphere h1 h2 heq1 heq2

/-- Regression: admissible ceiling \(r^2 T\le 4(\cosh\varphi_{\max}-1)<27\). -/
example {rs r : ℝ} (h : IsExterior rs r)
    (hφ : schwarzschildRapidity rs r ≤ phiMax) :
    r ^ 2 * schwarzschildTeleparallelT rs r < 27 :=
  lt_of_le_of_lt (r_sq_T_le_ceiling h hφ) four_cosh_phiMax_sub_one_bounds.2

/-- Regression: the proper-time factor is strictly positive. -/
example (α β : ℝ) : 0 < gammaEff α β :=
  gammaEff_pos α β

/-- Regression: special relativity is the unexcited dual sector. -/
example (α : ℝ) : gammaEff α 0 = Real.cosh α :=
  gammaEff_sr_is_beta_zero α

/-- Regression: the written particle action makes the mismatch free. -/
example {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    φddot - θddot = 0 :=
  paperActualEL_free_mismatch h

end Gravity

end DstDiophantine
