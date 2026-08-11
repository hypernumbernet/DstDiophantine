import DstDiophantine.Algebra.Invariant

/-!
Core re-exports for the PGA / biquaternion algebra layer (phase 1).

Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/

namespace DstDiophantine

export PGA (ι e4Index e4_sq_zero e4_anticomm e4_inner_anticomm)
export Cl31 (ι toPGA toPGA_ι)
export Generators (hyperbolic cyclic null null_sq null_mul_null hyperbolic_sq cyclic_sq)
export Operations (pseudoscalar dual TorsionParams daggerParams)
export Motor (TransParams OmegaParams omegaTorsion omegaTrans omegaBiv expTrans motor omegaTrans_sq)
export Invariant (J J5 J_coef J5_eq killingForm torsion_bound)

end DstDiophantine
