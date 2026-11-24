# Mismatch angle (relative rotor programme)

Lean path: `DstDiophantine/Algebra/MismatchAngle.lean` (main, sorry-free).
Gravity bridge: `DstDiophantine/Gravity/MismatchAngleBridge.lean`.
Discrete lattice bridge: `DstDiophantine/Framework/MismatchLattice.lean`.
Open general branch: `Goals/Diophantine/MismatchAngle.lean`,
`Goals/Diophantine/OverlapGradeZero.lean`.

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

## Proven properties (main library)

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
| **Wave 3 — DualControl jets / shield** | `JDot_eq_mismatch_half_derivative`, `JDot_dual_only_rotation_halves`, `exists_dual_only_mismatch_balance`, `dualShield_interp_mismatch_balanced` |
| **Wave 3 — Mass ceiling corners** | `massCorner_*_mismatch`, `mass_ceiling_not_mismatch_balance`, `mass_ceiling_eq_U_iff_mismatch_one_third` |
| **Wave 3 — modular scale** | `mismatch_half_sq_diff_scale_eq_amplified_add_winding`, `J_scale_mismatch_half_sq_diagnostic` |
| **Wave 3 — graviton chart** | `graviton_*_overlap_*` (via `axisOverlapScalar` / `gammaSEqual`) |

**Open (Goals, sorry allowed — 16 total):**

- `Goals.Diophantine.omegaMismatch_principal_branch` — general six-parameter log of `Ω`.
- `Goals.Diophantine.winding_total_equiv_mismatch_rotation_half` — winding vs rotation half-squares off pure-boost bookkeeping.
- `Goals.Diophantine.admissible_iff_mismatch_box` — cone in overlap half-norm (was `|JNormalized| ≤ 1`).
- `Goals.Diophantine.relativeRotor_axis_gradeZero_eq_overlap` — PGA grade-0 coefficient of `relativeRotor` (`pgaGradeZeroScalar` opaque in Goals only).

**Author decision / false lead (unchanged):**

- `overlap < 0` does **not** imply `J < 0` (equal-scale witness in `RepulsionOverlap`).
- Full iff overlap sign on `[0, π]` not proved (monotonicity).
- **Winding ≠ rotation half on pure-boost seeds:** `windingTotal_pureBoost` tracks `n₀`; `mismatchRotationHalf` vanishes. General equivalence is a Goal, not a theorem.
- **`massCorner_J_eq` denominator:** corner `J` is `(2·usualCount − 3) · π² / 8` from axis rapidities, not `π²/16`; mismatch half-square book-keeping uses the same corner data via `J_eq_mismatch_half_sq_diff` (do not fold corners into a single bivector angle without a new definition).

**Not yet in main:** constructive PGA grade-0 projection matching `axisOverlapScalar` (Goal above; chart formula remains the interface).

## Classification of existing `J` / `JNormalized` results

Inventory: **78** modules reference `J` or `JNormalized`; **~420** theorem-level declarations (per-theorem tagging still in progress).

| Class | Count (modules) | Role |
|-------|-----------------|------|
| **(a) Survives unchanged** | ~32 | Killing definition, Diophantine cone book-keeping; `J` stays derived |
| **(b) Restatable via angle / overlap (cheap)** | ~18 (**21 migrated**) | Wave 1–2 headlines plus wave 3 DualControl / MassCorners / modular / graviton overlap lemmas |
| **(c) Needs real rewrite / may fail** | ~28 (**~12 remaining**) | Legacy `J_scale_eq_J_amplified_add_error` error bookkeeping, deep DualControl `JDot` paths, bulk GravitonQuantum channel physics, scattered `JNormalized`-native corollaries |

### (b) Migrated (waves 1–3, selected)

| Item | Module | Mismatch-first statement |
|------|--------|--------------------------|
| Global `J` book-keeping | `MismatchAngle` | `mismatchBoostHalfSqSum`, `J_eq_mismatch_half_sq_diff` |
| Dual wall / equal scale / shield | `DualControl` | `J_eq_mismatch_diagnostic`, `J_equalScaleOf_mismatch_balanced`, `JDot_eq_mismatch_half_derivative`, dual-only mismatch balance |
| Four regimes | `ConeLabels` | `ofParams_eq_T/B/U_iff_mismatch_*`, dual-only existence lemmas |
| Envelope lock | `EnvelopeLock` | `twoPureUsual/Dual_mismatch_*` |
| Silent / EM control | `SilentControl`, `EMControl` | balanced magnetic rotation dominance |
| Lattice | `Framework/MismatchLattice` | `mismatch_half_sq_diff`, pure-boost boost-square = `latticeMismatch` |
| Mass ceiling | `MassCorners` | corner half-coefficients, ceiling excludes mismatch balance, `U` at one-third height |
| Modular amplification | `ModularAmplification` | scaled mismatch half-square identity, `J_scale_mismatch_half_sq_diagnostic` |
| Graviton quantum | `GravitonQuantum` | channel overlap vs `gammaS` on axis params |

### (c) Still J-native or open (selected)

| Item | Module | Issue |
|------|--------|-------|
| Modular error term | `ModularAmplification` | `J_scale_eq_J_amplified_add_error` still winds via legacy `J` error, not overlap |
| DualControl jets | `DualControl` | general `JDot` and shield interpolation lemmas still `J`-indexed in places |
| Admissible cone box | `RepulsionCone` Goal | mismatch norm vs `JNormalized` |
| Graviton quantum (bulk) | `GravitonQuantum` | interference / channel theorems not yet overlap-first |
| PGA overlap extraction | `OverlapGradeZero` Goal | `pgaGradeZeroScalar` definition and proof |

**Rough remainder:** on the order of **10–15 module clusters** still carrying irreducible `J`/`JNormalized` phrasing (plus **~390** per-theorem tags not yet audited in the inventory spreadsheet sense).

## CI

- `lake build DstDiophantine` — required green
- `scripts/check_main_library.sh` — no `sorry`, allowlisted axioms only
- `lake build Goals` — **16** open sorries (`scripts/count_goals.sh`)