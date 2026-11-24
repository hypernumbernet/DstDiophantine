# Mismatch angle (relative rotor programme)

Lean path: `DstDiophantine/Algebra/MismatchAngle.lean` (main, sorry-free).
Gravity bridge: `DstDiophantine/Gravity/MismatchAngleBridge.lean`.
Discrete lattice bridge: `DstDiophantine/Framework/MismatchLattice.lean`.
Axis overlap / cone: `DstDiophantine/Algebra/PgaAxisMotor.lean`,
`DstDiophantine/Algebra/RepulsionCone.lean`.
Open general branch: `Goals/Diophantine/MismatchAngle.lean` only (class-(c) winding + principal branch).

## Definition (one-axis family)

Usual and dual rotors factor on `axisParams α β` because `B⁺₀` and `B⁻₀` commute:

- `Ω = R_usual† R_dual = exp(ω)` with
  `ω = mismatchBoostHalf • B⁺₀ + mismatchRotationHalf • B⁻₀`
- `mismatchBoostHalf α β = −α/2` (unbounded boost leg)
- `mismatchRotationHalf α β = β/2` (compact rotation leg; periodic under `β ↦ β + 2π`

The **designated** grade-zero overlap on this motor is `pgaAxisMotorGradeZero α β` (also
`axisOverlapScalar`; matches `gammaS` via `MismatchAngleBridge.axisOverlap_eq_gammaS`).

**Repulsion is overlap-first:** see `Gravity/RepulsionOverlap.lean`. Legacy `J` is a derived diagnostic:

`J = 2 · (Σ mismatchBoostHalf² − Σ mismatchRotationHalf²)` (`J_eq_mismatch_half_sq_diff`).

## Proven properties (main library)

| Property | Lean name |
|----------|-----------|
| Global `J` from half-square sums | `J_eq_mismatch_half_sq_diff`, `J_eq_zero_iff_mismatch_sq_balance` |
| Sign of `J` ↔ which half-square dominates | `J_neg_iff_rotation_sq_dominates`, `J_pos_iff_boost_sq_dominates` |
| Pure hyperbolic / elliptic corners | `pure_hyperbolic_rotation_sq_zero`, `pure_elliptic_boost_sq_zero` |
| `Ω = exp(ω)` on one axis | `relativeRotor_axis_eq_exp` |
| Overlap / `gammaS` | `axisOverlap_eq_gammaS`, `pgaAxisMotorGradeZero_eq_overlap` |
| Dual wall in half-squares | `J_dualWall_neg_iff_rotation_dominates`, `J_dualWall_nonpos_iff_mismatch` |
| Equal-scale shield | `J_equalScaleOf_mismatch_balanced` |
| Regime `T|B|U|F` via half-squares | `ConeLabels.ofParams_eq_*_iff_mismatch_*` |
| Envelope corner patterns | `EnvelopeLock.twoPure*_mismatch_*`, `onEnvelope_J_zero_mismatch_balance` |
| Magnetic control | `SilentControl.balanced_magnetic_rotation_dominates`, `EMControl.magnetic_superpose_rotation_sq_geq_when_J_nonpos` |
| Discrete lattice | `MismatchLattice.mismatch_half_sq_diff`, `pure_boost_mismatch_boost_eq_lattice`, `winding_implies_latticeMismatch_ne` |
| **Wave 3–4** (modular primary, shield jets, graviton overlap) | prior PR sections |
| **Wave 5 — axis structural grade-0** | `PgaAxisMotor.cliffordAxisMotorGradeZero`, `relativeRotor_axis_product_scalar_ne_designated` |
| **Wave 5 — repulsion cone (one direction)** | `RepulsionCone.admissibleContinuous_implies_mismatch_half_box`, `mismatch_half_box_not_implies_admissible` |
| **Wave 5 — DualControl shield** | `sumAlphaSq_eq_four_mismatchBoostHalfSqSum`, `J_dualShieldInterp_mismatch_sq_param`, `mismatchRotationHalfSqSum_dualShieldInterp` |
| **Wave 5 — Graviton heights** | `oneStep_JNormalized_mismatch_rotation_sq`, `collective_square_mismatch_halves`, `expressed_locks_mismatch_diagnostic`, `farHeight_mismatch_rotation_sq` |

**Open (Goals, sorry allowed — 14 total):**

- `Goals.Diophantine.omegaMismatch_principal_branch` — general six-parameter log of `Ω`.
- `Goals.Diophantine.winding_total_equiv_mismatch_rotation_half` — winding vs rotation half-squares (**awaiting author conceptual decision**; frozen).

**Author decision / false leads (incl. wave 5):**

- `overlap < 0` does **not** imply `J < 0` (equal-scale witness in `RepulsionOverlap`).
- Full iff overlap sign on `[0, π]` not proved (monotonicity).
- **Winding ≠ rotation half on pure-boost seeds:** general equivalence stays a Goal until the author picks a bookkeeping convention.
- **`admissible_iff_mismatch_box` is false** — admissible ⇒ per-axis half-box is proved; converse refuted by `RepulsionCone.mismatch_half_box_not_implies_admissible` (`axisParams (0.9π) 0`).
- **Structural grade-0 on the axis family** is the designated chart (`PgaAxisMotor.cliffordAxisMotorGradeZero`); the naive product scalar `cosh(α/2)cos(β/2)` differs when both legs are active.
- **`J_scale_eq_J_amplified_add_error` is derived** from `mismatch_sq_scale_primary` + `J` diagnostic (not an independent axiom).

## Classification of existing `J` / `JNormalized` results

Inventory: **78** modules reference `J` or `JNormalized`; per-theorem tagging still in progress.

| Class | Count (modules) | Role |
|-------|-----------------|------|
| **(a) Survives unchanged** | ~32 | Killing definition, Diophantine cone book-keeping; `J` stays derived |
| **(b) Restatable via angle / overlap (cheap)** | ~20 (**~32 migrated** after wave 5) | Overlap / mismatch headlines + graviton collective heights |
| **(c) Needs real rewrite / may fail** | ~26 (**~5–7 remaining**) | Residual `JNormalized` audit, principal-branch log, deep off-axis Clifford |

### (c) Still substantial (selected)

| Item | Module | Issue |
|------|--------|-------|
| General `Ω` branch | `Goals/MismatchAngle` | six-parameter principal branch log |
| Winding bookkeeping | Goals only | author decision pending (frozen) |
| Off-axis product factorisation | `DualRotorMotor` | not axis half-box programme |
| Bulk `JNormalized` corollaries | `GravitonQuantum` | heights now have mismatch companions; many corollaries still `JNormalized`-worded |

**Rough remainder:** **~5–7 module clusters** with irreducible off-axis or bookkeeping content.

## CI

- `lake build DstDiophantine` — required green
- `scripts/check_main_library.sh` — no `sorry`, allowlisted axioms only
- `lake build Goals` — **14** open sorries (`scripts/count_goals.sh`)