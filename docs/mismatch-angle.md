# Mismatch angle (relative rotor programme)

Lean path: `DstDiophantine/Algebra/MismatchAngle.lean` (main, sorry-free).
Gravity bridge: `DstDiophantine/Gravity/MismatchAngleBridge.lean`.
Discrete lattice bridge: `DstDiophantine/Framework/MismatchLattice.lean`.
Open general branch: `Goals/Diophantine/MismatchAngle.lean`.

## Definition (one-axis family)

Usual and dual rotors factor on `axisParams α β` because `B⁺₀` and `B⁻₀` commute:

- `Ω = R_usual† R_dual = exp(ω)` with
  `ω = mismatchBoostHalf • B⁺₀ + mismatchRotationHalf • B⁻₀`
- `mismatchBoostHalf α β = −α/2` (unbounded boost leg)
- `mismatchRotationHalf α β = β/2` (compact rotation leg; periodic under `β ↦ β + 2π`)

The scalar overlap (shell time-delay factor on this locus) is

`axisOverlapScalar α β = cosh(α/2) cos(β/2) − sinh(α/2) sin(β/2)`,

which agrees with `Gravity.gammaS` (`MismatchAngleBridge.axisOverlap_eq_gammaS`).

**Repulsion is overlap-first:** see `Gravity/RepulsionOverlap.lean`. Legacy `J` is a derived diagnostic:

`J = 2 · (Σ mismatchBoostHalf² − Σ mismatchRotationHalf²)` (`J_eq_mismatch_half_sq_diff`).

## Proven properties (main library, wave 2 additions)

| Property | Lean name |
|----------|-----------|
| Global `J` from half-square sums | `J_eq_mismatch_half_sq_diff`, `J_eq_zero_iff_mismatch_sq_balance` |
| Sign of `J` ↔ which half-square dominates | `J_neg_iff_rotation_sq_dominates`, `J_pos_iff_boost_sq_dominates` |
| Pure hyperbolic / elliptic corners | `pure_hyperbolic_rotation_sq_zero`, `pure_elliptic_boost_sq_zero` |
| `Ω = exp(ω)` on one axis | `relativeRotor_axis_eq_exp` |
| Overlap / `gammaS` | `axisOverlap_eq_gammaS`, `axisOverlap_eq_gammaSEqual_balanced` |
| Dual wall in half-squares | `J_dualWall_neg_iff_rotation_dominates`, `J_dualWall_nonpos_iff_mismatch` |
| Equal-scale shield | `J_equalScaleOf_mismatch_balanced` |
| Regime `T|B|U|F` via half-squares | `ConeLabels.ofParams_eq_*_iff_mismatch_*` |
| Envelope corner patterns | `EnvelopeLock.twoPure*_mismatch_*`, `onEnvelope_J_zero_mismatch_balance` |
| Magnetic control | `SilentControl.balanced_magnetic_rotation_dominates`, `EMControl.magnetic_superpose_rotation_sq_geq_when_J_nonpos` |
| Discrete lattice | `MismatchLattice.mismatch_half_sq_diff`, `pure_boost_mismatch_boost_eq_lattice`, `winding_implies_latticeMismatch_ne` |

**Open (Goals, sorry allowed):**

- `Goals.Diophantine.omegaMismatch_principal_branch` — general six-parameter log of `Ω`.
- `Goals.Diophantine.winding_total_equiv_mismatch_rotation_half` — winding vs rotation half-squares off pure-boost bookkeeping.
- `Goals.Diophantine.admissible_iff_mismatch_box` — cone in overlap half-norm (was `|JNormalized| ≤ 1`).

**Author decision / false lead (unchanged):**

- `overlap < 0` does **not** imply `J < 0` (equal-scale witness in `RepulsionOverlap`).
- Full iff overlap sign on `[0, π]` not proved (monotonicity).
- **Winding ≠ rotation half on pure-boost seeds:** `windingTotal_pureBoost` tracks `n₀`; `mismatchRotationHalf` vanishes. General equivalence is a Goal, not a theorem.

**Not yet in main:** grade-0 extraction of overlap from `Ω` inside PGA without closed `gammaS`.

## Classification of existing `J` / `JNormalized` results

Inventory: **78** modules reference `J` or `JNormalized`; **~420** theorem-level declarations (per-theorem tagging still in progress).

| Class | Count (modules) | Role |
|-------|-----------------|------|
| **(a) Survives unchanged** | ~32 | Killing definition, Diophantine cone book-keeping; `J` stays derived |
| **(b) Restatable via angle / overlap (cheap)** | ~18 (**16 migrated**) | DualControl headline, ConeLabels regimes, EnvelopeLock patterns, lattice bridge, control bridges |
| **(c) Needs real rewrite / may fail** | ~28 (**~8 in progress**) | Full `DualControl` jet calculus, MassCorners bivector classification, modular `J_scale` error, GravitonQuantum |

### (b) Migrated this wave (selected)

| Item | Module | Mismatch-first statement |
|------|--------|--------------------------|
| Global `J` book-keeping | `MismatchAngle` | `mismatchBoostHalfSqSum`, `J_eq_mismatch_half_sq_diff` |
| Dual wall / equal scale | `DualControl` | `J_eq_mismatch_diagnostic`, `J_equalScaleOf_mismatch_balanced`, `J_dualWall_*_mismatch` |
| Four regimes | `ConeLabels` | `ofParams_eq_T/B/U_iff_mismatch_*`, dual-only existence lemmas |
| Envelope lock | `EnvelopeLock` | `twoPureUsual/Dual_mismatch_*` |
| Silent / EM control | `SilentControl`, `EMControl` | balanced magnetic rotation dominance |
| Lattice | `Framework/MismatchLattice` | `mismatch_half_sq_diff`, pure-boost boost-square = `latticeMismatch` |

### (c) Still J-native or open (selected)

| Item | Module | Issue |
|------|--------|-------|
| `DualControl` jets | `DualControl` | `JDot`, shield calculus still on `J` |
| `MassCorners` | `MassCorners` | Corner classification by scalar only |
| Modular amplification | `ModularAmplification` | `J_scale_eq_J_amplified_add_error` |
| Admissible cone box | `RepulsionCone` Goal | mismatch norm vs `JNormalized` |
| Graviton quantum channel | `GravitonQuantum` | angle-first channel statements |

## CI

- `lake build DstDiophantine` — required green
- `scripts/check_main_library.sh` — no `sorry`, allowlisted axioms only
- `lake build Goals` — **15** open sorries (`scripts/count_goals.sh`)