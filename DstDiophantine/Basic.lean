/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/

import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.UnitGroup

/-!
Core re-exports for the PGA / biquaternion algebra layer (phases 1–2).
-/

namespace DstDiophantine

export PGA (ι e4Index e4_sq_zero e4_anticomm e4_inner_anticomm)
export Cl31 (ι toPGA toPGA_ι)
export Generators (hyperbolic cyclic null null_sq null_mul_null hyperbolic_sq cyclic_sq)
export Operations (pseudoscalar dual TorsionParams daggerParams)
export Discrete (DiscreteTorsion toTorsionParams IsPrincipalBranch IsAdmissibleContinuous
  IsAdmissible toTorsionParams_alpha_nonneg toTorsionParams_beta_nonneg
  admissible_continuous_of_discrete admissible_sum_le admissible_alpha_le_half_pi
  admissible_beta_le_half_pi)
export Motor (TransParams OmegaParams omegaTorsion omegaTrans omegaBiv expTrans rotorTorsion motor
  omegaTrans_sq omegaTorsion_reverse expTrans_unitary rotor_unitary motor_unitary)
export UnitGroup (discreteRotor DiscreteUnit discreteUnit_finite)
export Invariant (J J5 JNormalized counterExampleParams J_coef JNormalized_coef J5_eq killingForm
  axis_sq_diff_eq torsion_bound_raw torsion_bound torsion_bound_continuous JNormalized_extremal
  torsion_bound_naive_false)

end DstDiophantine
