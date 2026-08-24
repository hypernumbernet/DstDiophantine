import DstDiophantine.Gravity.Identification
import DstDiophantine.Gravity.Tetrad
import DstDiophantine.Gravity.NewtonFromLight
import DstDiophantine.Gravity.EventBoundary
import DstDiophantine.Gravity.CoulombFromDual
import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Gravity.CompactS3

/-!
# Gravity / PGA–TEGR chart layer

Re-exports the chart-level TEGR scaffolding (coframe, sandwich scales,
Schwarzschild tetrad, Weitzenböck torsion, motor-induced frame vectors,
and the `J` / `J_field` / `T` dictionary with naive-identification rejections),
plus the exploratory SI / \(c\to G\) hypothesis layer (`SI`, `NewtonFromLight`),
the labelled quasi-horizon cutoff (`EventBoundary`), the electromagnetic
exploratory layer (`CoulombFromDual`, `ElectronShell`), and the galactic
S³ cotangent exploratory layer (`CompactS3`; no `dst_derives_a0` / `dst_derives_G`).
-/

namespace DstDiophantine

namespace Gravity

end Gravity

end DstDiophantine
