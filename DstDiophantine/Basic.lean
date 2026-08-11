/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/

import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Continuum
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.UnitGroup
import DstDiophantine.Embedding.Equation
import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.IntegerRotor
import DstDiophantine.Embedding.NullTranslator
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Framework.Descent
import DstDiophantine.Framework.Lattice
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Search
import DstDiophantine.Theorems.Fermat

/-!
Core re-exports for the PGA / biquaternion algebra layer (phases 1–5).
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
  axis_sq_diff_eq IsSpatialTrans IsBoundedTrans J5_unbounded J5_bound_spatial
  torsion_bound_raw torsion_bound torsion_bound_continuous JNormalized_extremal
  torsion_bound_naive_false)
export Amplification (scaleTorsion pureBoost J_scale JNormalized_scale J_pow_amplify
  JNormalized_pow_amplify rotorTorsion_pureBoost_pow)
export Continuum (AdmissibleContinuous exists_discrete_approx lattice_in_interval)
export Embedding (integerRotor integerRotor_mul integerRotor_pow nullTranslator nullTranslator_add
  nullTranslator_faithful translateBy logMismatch J_pow_amplify_int RotorClass integerClass
  quantizeInt torsionHeight integerHeight descentCandidate diophantineMotor
  additive_faithful diophantine_zero_iff)
export Framework (PowerSumEquation evalPowerSum powerSumMotor powerSumMotor_one_iff
  fermatEquation fermatMotor_one_iff IsZeroHeight AdmissibleClass ExistsZeroHeight
  latticeMismatch dagger_preserves_height DescentSchema latticeSearchSchema
  findZeroHeight findZeroHeight_isSome phase4_layers)
export Theorems (fermat_solution_iff_motor fermat_pos_lt mismatchRotor_eq_rotorTorsion
  amplification_implies_seed_le fermat_amplification_contradiction
  discrete_nonzero_height_lb discrete_amplification_contradiction
  FermatAdmissibleBridge fermat_last_theorem_of_bridge)

end DstDiophantine
