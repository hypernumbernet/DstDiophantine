import DstDiophantine.Gravity.Identification
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
and the `J` / `J_field` / `T` dictionary with naive-identification rejections),
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
