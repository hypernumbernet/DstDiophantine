# Mismatch angle (relative rotor programme)

Lean path: `DstDiophantine/Algebra/MismatchAngle.lean` (main, sorry-free).
Gravity bridge: `DstDiophantine/Gravity/MismatchAngleBridge.lean`.
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

Legacy `J` is expressed on the same locus by

`J = 2 · (mismatchBoostHalf² − mismatchRotationHalf²)` (`J_axis_from_mismatchHalves`).

## Proven properties (main library)

| Property | Lean name |
|----------|-----------|
| `Ω = exp(ω)` on one axis | `relativeRotor_axis_eq_exp` |
| `Ω = 1 ↔` rotors coincide | `relativeRotor_axis_eq_one_iff_rotors` (+ global `relativeRotor_eq_one_iff`) |
| Nontrivial axis bivector ⇒ `Ω ≠ 1` | `relativeRotor_axis_ne_one_of_bivector` |
| Dagger swaps oriented half-coefficients | `mismatchOrientation_dagger_axis`, `dagger_axisParams` |
| `J` flips sign under dagger on axis | `J_dagger_axis` |
| Unsigned mass unchanged under dagger | `mass_dagger_axis` |
| `J` from mismatch half-coefficients | `J_axis_from_mismatchHalves` |
| Overlap sign reversal at equal-scale threshold `π/2` | `axisOverlap_sign_reversal_threshold`, `axisOverlap_balanced_nonpos_at_half_pi` |
| `axisOverlap` on balanced locus = `gammaSEqual` | `axisOverlap_eq_gammaSEqual_balanced` |

**Open (Goals, sorry allowed):** principal-branch mismatch logarithm for full six-parameter
`TorsionParams` (`Goals.Diophantine.omegaMismatch_principal_branch`).

**Not yet in main:** extracting `axisOverlapScalar` as the grade-0 part of `Ω` inside PGA
(without re-using the closed scalar formula). Currently under research.

## Classification of existing `J` / `JNormalized` results

Inventory: **78** Lean modules under `DstDiophantine/` reference `J` or `JNormalized`.
Theorem-level grep (`theorem … J` / `JNormalized` in name or statement): **~420** declarations;
below we group by **module family** (full per-theorem tagging is in progress).

| Class | Count (modules) | Role |
|-------|-----------------|------|
| **(a) Survives unchanged** | ~32 | Killing definition, cone metric book-keeping, Diophantine closure; `J` stays as derived scalar |
| **(b) Restatable via angle / overlap (cheap)** | ~18 | One-axis stiffness, shell factors, balanced-ray diagnostics; use `MismatchAngle` + `gammaS` bridge |
| **(c) Needs real rewrite / may fail** | ~28 | Repulsion tied to `J < 0`, `|JNormalized| ≤ 1` regime labels, lattice amplification error terms |

### (a) Survives unchanged (selected)

- `Algebra/Invariant.lean` — full `J`, `JNormalized`, mass cone, dagger laws (retained as diagnostics).
- `Theorems/*` admissible bridges — cone predicates on `JNormalized`.
- `Logic/ClassicalCore.lean`, `Logic/Connective.lean` — truth-value bookkeeping on `J` labels.
- `Gravity/Identification.lean`, `JTDictionary.lean` — explicit chart warnings that `J ≠ T`.

### (b) Restatable via mismatch angle (selected; partly done)

| Item | Module | Angle-first restatement |
|------|--------|-------------------------|
| Stiffness `−m J` on one axis | `RestMass`, `DualControl` | `J_axis_from_mismatchHalves` |
| Equal-scale shells / sign of `γ_s` | `ElectronShell`, `TorsionalLayer` | `axisOverlap_eq_gammaS`, `axisOverlap_eq_gammaSEqual_balanced` |
| `J = 0` but `γ_s` changes sign | `RelationalPolarization.equalScale_clock_not_mismatch` | overlap threshold theorems |
| Relative rotor transport | `RelativeRotor`, `DualRotorMotor` | `relativeRotor_axis_eq_exp` |
| `latticeMismatch` modulus bounds | `ModularAmplification` | winding on rotation leg (research) |

### (c) Needs rewrite / may fail (key items)

| Item | Module | Issue |
|------|--------|-------|
| `repulsive_requires_negative_J` | `GaugeDictionary` | Repulsion from overlap rotation threshold, not `J < 0` alone |
| `ConeLabels`, `|JNormalized| ≤ 1` | `ConeLabels`, `ControlDomain` | Admissible cone in angle norm; currently under research |
| `MassCorners` | `MassCorners` | Corner classification by scalar; needs bivector direction |
| `DualControl` (40+ `J` theorems) | `DualControl` | Dual-only control phrased entirely in `J` |
| `EnvelopeLock` | `EnvelopeLock` | Envelope tied to `JNormalized` extrema |
| `SilentControl`, `EMControl` | various | Control domain inequalities on `J` |
| `Framework/Lattice.latticeMismatch` | `Framework/Lattice` | Discrete bound on scalar mismatch |
| `Amplification` / modular error | `Algebra/ModularAmplification` | `J_scale_eq_J_amplified_add_error` |
| `GravitonQuantum` balanced channel | `GravitonQuantum` | Partially bridged via `gammaS_balanced`; angle first-class statements desired |
| `J_zero_not_relativeRotor_one` | `RelativeRotor` | Shows scalar zero does not mean vacuum; physics narrative moves to `Ω` |

## What did not work in this iteration

- Full **iff** characterisation of overlap sign by rotation half-angle on `[0, π]` (monotonicity fails
  before `π/2` on equal-scale locus); only threshold certificates at `0` and `π/2` are proved.
- **Grade-projected** scalar part of `Ω` in PGA without importing the closed `gammaS` formula.
- **Non-commuting** six-parameter logarithm of `Ω` (left in Goals).

## CI

- `lake build DstDiophantine` — required green
- `scripts/check_main_library.sh` — no `sorry`, allowlisted axioms only
- `lake build Goals` — principal branch sorry isolated in Goals