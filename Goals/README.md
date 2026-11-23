# Goals — Lean target statements

This directory is **isolated** from the proved library under `DstDiophantine/`.
A target is a `theorem` whose statement is a `Prop` from the main library.
Policy: see [`POLICY.md`](POLICY.md).

Build: `lake build Goals` (sorry allowed). The default `lake build` does not
include this library.

## Breakthrough strategy (status vs new aims)

DST already has a sorry-free algebraic core, a shared amplification no-go, a
Schwarzschild-chart perihelion match for Mercury in `(42, 44)` arcsec/century,
a weak-field solar deflection in `(17/10, 9/5)` arcseconds, and a unique
charged-pion selector for one reversal scale. The Coulomb factor `1` gives the
hydrogen gross-structure ratios; equal-scale nodes do not. On `Σ > 0` and
`Δ > 0` the Kerr coframe induces the Kerr metric, and vanishing spin returns
exterior Schwarzschild. The carrier admits no Newton–Wigner pair; chart
position is phase information `D² + I = 1`. Those close *consistency* and *selection*
claims. They do not yet make DST derive a free laboratory or galactic
constant, nor do they close a classical Diophantine headline without an open
residual or bridge, nor do they put a perihelion or a lensing window on the
Kerr chart.

A breakthrough here means one of three things, in this order of programme
value:

1. **Identity** — a named constant that is an input today becomes a theorem
   of the dual-rotor / channel geometry (no external fit).
2. **Observation** — a second classical GR or scattering observable is stated
   with library definitions and proved in a named window, the way Mercury and
   the pion selector already are.
3. **Amplification** — at least one live Diophantine leaf or bridge is closed
   by the DST encoding itself, not by importing a further number-theory axiom.

Diagnostic or false bridges (`AbcAdmissibleBridge`, modular/admissible Beal
and Fermat packages marked demoted) are not breakthrough routes.

### Current scoreboard

| Layer | Status | Gap for a breakthrough |
| --- | --- | --- |
| Algebra / PGA / \|J_norm\| ≤ 1 | Proved | Not a Goal; keep regression-only |
| Amplification no-go (layer 2) | Proved | Layer 3 (leaf or live bridge) still open |
| Mercury perihelion window | Proved | Closed; do not reopen as a Goal |
| Solar light deflection | Proved | Closed; do not reopen as a Goal |
| Charged-pion reversal selector | Proved | Selects `r₁`; channel theorems still take `r₁` as input |
| Hydrogen gross structure | Proved for the factor `1` | `lyman_two_over_three` is `27/32` and `balmer_alpha_over_beta` is `27/20`. `equalScale_nodes_miss_lyman` and `inv_node_gap_lt_hydrogen` refuse node readings. `a₀` and `ℓ` stay inputs |
| Newton–Wigner / chart position | Refused on the carrier; proved as phase information | `no_newtonWignerPair_dual` and `no_newtonWignerPair_dirac`. `whichMomentum_sq_add_phaseInformation` is `D² + I = 1`, with `I = V²`. `phaseInformation_not_a_location` keeps `I = 1` while the chart contrast vanishes, once the two momenta coincide. A chart sample stays on one carrier ray. Not a spacetime wave, and not `E/ℏ` from rest mass |
| Kerr coframe | Proved | `inducedMetric_kerr` on `Σ > 0` and `Δ > 0`. `kerrCoframe_zero_spin` returns exterior Schwarzschild. `kerr_cross_ne_azimuthBoost` refuses a pure-boost reading of the cross term. No perihelion window |
| Written one-axis action | Proved as the opposite-sign system | `paperActualEL_not_oscillator`. The conjugate momenta do not contain `m`. `RelationalPolarization` evaluates stiffness at the relative rotor; its angle derivative is not that force. `diameter_one_root_iff` holds exactly at `Z = 4` |
| Positive Beal assembly | Conditional on six leaves + FLT axiom | Closest Diophantine stack; leaves remain |
| Other classical headlines | Conditional on five live bridges | Bridges open; continuous abc bridge is false |
| Free scales `G`, `a₀`, `α`, `ℓ` | Scattering signs fix `14/15 < ℓ < 19/10` and refuse a point. Every radius `layerRadius ℓ x` whose phase ignores `ℓ`, including one positive rapidity and the critical phases of `gammaSEqual`, cancels `ℓ`. `phiStar` has no critical phase on `(π/4, π/2)`. A two-channel zero at those phases, and the external electromagnetic ratio, also refuse a point. The hydrogen node reading does not select `ℓ`. `G`, `a₀`, `α`, and one value of `ℓ` stay underived | Identity breakthrough if any one of those single values is derived |
| Rotating source | Chart proved; window not stateable | Perihelion or frame dragging on `kerrCoframe` |
| Dual Hilbert lift / closed dynamics | Partial | Orthomodular law, island comparisons, conjugate momenta, and the Newton–Wigner refusal exist. `PhaseInformation` is the chart complement `D² + I = 1`, not the missing map. The missing pieces are a named D4L fragment ↦ `QProp`, and a global evolution operator |

### Priority targets (new aims)

Work proceeds in priority order. A row becomes a Lean `sorry` target only when
the main library already defines the `Prop`. Until then it stays
*definition-first* in the not-yet-stateable index.

| Pri | Aim | Track | Now | Next concrete step | Success criterion |
| --- | --- | --- | --- | --- | --- |
| **P0** | Derive channel length `ℓ` (or remove free `r₁`) from a scattering observable | Gravity / strong | `layerRadius_scale` and `layerRadius_pair_ratio_scale` cancel `ℓ` for every phase that ignores the length, and `thresholdRadius_scale_not_unique` refuses a point. `deriv_phiStar_ne_zero` gives `phiStar` no critical phase on `(π/4, π/2)`. `gammaSEqual` is critical only where `sin = 0`; `gammaSEqual_deriv_ne_zero_of_mem_Ioo_pi` says `(0, π)` has none, and `gammaSEqual_critical_radius_div_length` keeps the integer multiples of `π` in the family. `pairChannelForce_eq_zero_iff` drops the separation, and `pairChannelForce_layer_zero_not_unique` refuses a point. `charge_over_nuclear_length_not_unique` keeps `3/5` and `9/10` inside the external electromagnetic ratio `(203, 414)`. `fourteenMeV_fractional_widening` still puts the skin under `6/100` of the node and does not select a point. `HydrogenRepulsion` does not select `ℓ`: the factor `1` carries the gross-structure ratios, and node gaps miss `27/32` and `5/27`. `RelationalPolarization` does not use `ℓ`. The sign window and the pion stand-in are unchanged. `1/v` is still not derived | A length that is not `layerRadius ℓ x` for a phase `x` independent of `ℓ`, before any uniqueness `sorry` | One value of `ℓ` on that path, with no free channel input |
| **P0** | Derive `a₀` (or an equivalent MOND scale) from dual-image / compactification data | Gravity / galaxy | `GalaxyCurve` and `DualImage` bound dwarfs from external `a₀` and `G`; `dst_derives_a0` is refused | Define `a₀` from the source geometry (e.g. dual period / baryonic data) so flat curves are theorems without that input | A theorem that does not take `a₀` as an input and still recovers a named flat-speed window |
| **P1** | Solar light deflection in the classical GR window | Gravity / optics | `SolarDeflection.solar_deflection_arcsec_bounds` proves `17/10 < deflectionArcsec < 9/5` for a null ray that turns at the nominal solar radius | Closed in the main library | Do not reopen as a Goal |
| **P1** | Close one Beal leaf *without* a new external axiom | Diophantine | Six leaves open. `IsSharedExpCubeOrFifth` is closed by `darmonMerelCube` and `fermatSignatureNN5`, so `(10,10,9)` has left the even-sum leaf. `(5,5,11)` and `(3,5,7)` do not meet that cut | Chase a signature that is not a shared exponent beside a multiple of `3` or `5`, such as `(22,22,7)`, `(10,10,11)`, `(5,5,11)`, or `(3,5,7)` | That leaf becomes a theorem; `Goals` deletes its `sorry` |
| **P2** | One named window on the Kerr chart | Gravity / rotation | `inducedMetric_kerr` is the Kerr metric on `Σ > 0` and `Δ > 0`. `kerrCoframe_zero_spin` returns exterior Schwarzschild. `kerr_cross_ne_azimuthBoost` refuses a pure-boost reading of the cross term. The horizon `Δ = 0` is not claimed. No perihelion and no lensing on this chart | Name the observable (perihelion or frame dragging) from library definitions, in a window, before any `sorry` | A theorem in that window. Only then a Goal |
| **P2** | `FermatMixedMotorResidual` via the mixed-motor excess already in the library | Diophantine | Excess and odd-prime factorisation lemmas exist; classical FLT not claimed | Strengthen the motor residual until the mixed seat cannot stay admissible for `n ≥ 3` | `fermatMixedMotorResidual` proved; headline follows |
| **P2** | One live admissible bridge (Collatz / Goldbach / Polignac) | Diophantine | Finite certificates exist; infinite bridge open | Prefer Collatz: cone facts and `n ≤ 2^20` certificates are the strongest local base | Bridge theorem in the main library |
| **P3** | Closed-form DST evolution (global operator on coupled rotors) | Gravity / dynamics | `DualRotorDynamics` is the written opposite-sign system. `paperMomentumSigma` and `paperMomentumDelta` are half the mismatch rate and half the common rate, and neither contains `m`. `paperActualEL_not_oscillator` refuses `δ̈ + mδ = 0`. `RelationalPolarization` evaluates the stiffness cross term at the geodesic angle of `ρ = a⁻¹b`; `unit_usualConstraint_ne_angleDeriv` says that angle derivative is not the constraint force. No global closed product on `OmegaParams` | Name the evolution operator; only then state a Goal | Definition landed; target statement no longer “not yet stateable” |
| **P3** | Dual Hilbert lift: named D4L fragment ↦ `QProp` | Logic | Orthomodular law on `ℂ²` and island comparisons exist. `no_newtonWignerPair_dual` and `whichMomentum_sq_add_fringeVisibility` are chart facts, not the missing map | Define the map on a finite fragment before claiming subspace facts become dual-Hilbert theorems | Definition + at least one lifted island theorem |
| **Defer** | `AbcModularBridge`, `RiemannAdmissibleBridge`, electroweak masses, propellantless lab control, cold-fusion rate, Mach `m` from sources | Mixed | Live or not-yet-stateable, but either false-path risk (abc continuous), far from definitions, or not identity-critical | Do not spend identity budget here until a P0/P1 lands | Revisit only after a P0 or P1 closes |

### What this changes in the open-`sorry` list

The twelve Lean targets below stay. This pass adds none: the hydrogen ladder,
the Newton–Wigner refusal, the Kerr coframe, and the written one-axis system
are already theorems, and the Kerr window is not yet a `Prop`. Priority among
the open `sorry`s for near-term work:

1. Beal leaves (P1) — furthest Diophantine stack; closing one is the amplification breakthrough.
2. `fermatMixedMotorResidual` (P2) — motor path is native to DST.
3. `collatzAdmissibleBridge` ahead of Goldbach / Polignac (P2) — strongest certificates.
4. `abcModularBridge` and `riemannAdmissibleBridge` — deferred relative to the above.

Physics P0 aims, and the Kerr window, are **not** yet Lean Goals. Adding a
`True` placeholder is forbidden by policy. Land the missing definition in
`DstDiophantine/` first, then add the `sorry` target in the same PR that
updates this index.

## Index revision

The previous index counted 69 `sorry`s. That count mixed four different
things. They are separated as follows.

| What changed | Reason |
| --- | --- |
| Eight headline conjectures no longer have `sorry` | The main library already proves each one from a named leaf or bridge. `Headlines.lean` applies that proof. The `sorry` stays on the leaf. |
| Nineteen coarser `*Residual` props dropped | Two are already theorems (`BealPosCubeAddTwoCubeResidual_of_euler`, `BealTwoEqualEvenSumExpFiveResidual_of_NN5`). Thirteen are consequences of the six Beal leaves in the main library. Three remain off that path: the even-difference factor and perfect-power packagings, and `BealMordellCubeAddTwoResidual`. `BealCGADilationNoGo` left with the conformal probe. |
| Six diagnostic bridges dropped | `BealAdmissibleBridge`, `FermatAdmissibleBridge`, `FermatCoarseDiscreteBridge`, and `FermatModularBridge` remain in the main library. They are diagnostic, demoted, or vacuous, and they are not research targets. `BealModularBridge` and `BealWindingBridge` left with the conformal probe. `AbcAdmissibleBridge` is false (`AbcAdmissibleBridge_false`) and was already absent. |
| Twenty-four gravity, logic, and PGA entries dropped from Lean | Each statement was `True`, or an existence claim with a witness that does not use a library definition (`42 < Δ < 44`, `0 < θ`). Both elaborate without the claim they were meant to record. They are indexed below as not yet stateable. |
| Two physics frontiers added | Mercury's advance is `Perihelion.radialReturn` on external orbital elements, in arcseconds per Julian century. The charged-pion Compton length selects one sign-reversal scale in `(1/2, 1)` through `lengthOfReversal`. |
| Mercury frontier closed | `Mercury.perihelion_arcsec_bounds` in the main library proves `42 < arcsecPerCentury < 44` from `bound_return_bounds` and the external elements. Removed from Goals. |
| Charged-pion frontier closed | `SignReversal.chargedPionSelectsReversalScale` proves a unique `r₁` in `(1/2, 1)` with `lengthOfReversal r₁ = pionComptonFm`. Removed from Goals. |
| Five exponent leaves exclude `IsSharedExpCubeOrFifth` | A shared divisor `n ≥ 4`, with the third exponent divisible by `3` or by `5`, rewrites to `darmonMerelCube` or `fermatSignatureNN5`. On a difference seat `n` is odd. No new axiom. `(10,10,9)` leaves the even-sum leaf. The `sorry` stays on the narrower statement. `(5,5,11)` and `(3,5,7)` remain |
| Hydrogen ladder, Newton–Wigner, Kerr chart, written action | Recorded as closed or refused. No new `sorry`. `HydrogenRepulsion` proves the Coulomb ratios and refuses the node reading. `NewtonWigner` refuses a carrier position operator. `PositionInformation` proves `D² + V² = 1`, and `PhaseInformation` proves `D² + I = 1` with `I = V²`. `Kerr` induces the metric and refuses a pure-boost reading of the cross term. `DualRotorDynamics` refuses the oscillator. The Kerr window stays definition-first |
| `Algebra/CGA` is off the algebra barrel | `Algebra.lean` does not import it. `BealCGADilationNoGo`, `BealModularBridge`, and `BealWindingBridge` are not in the tree. Do not restore them as Goals |

Open `sorry` count: **12** (`scripts/count_goals.sh`). All are the Diophantine leaves and bridges left by the split.

## Open `sorry` targets

| Module | Count | What is open |
| --- | ---: | --- |
| `Diophantine/Residuals.lean` | 7 | `FermatMixedMotorResidual` and the six Beal leaves |
| `Diophantine/Bridges.lean` | 5 | abc modular; Collatz, Goldbach, Polignac, and the critical-line bridge |
| **Total** | **12** | |

### Beal leaves

Positive Beal follows from these six, together with the FLT axiom already in
the main library (`beal_conjecture_pos_of_fine_residuals_even_split`):

| Leaf | Discharges |
| --- | --- |
| `BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual` | even two-equal sum, via `BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth_fifth`. Phase 7z closes a common exponent divisible by `4`. Phase 8a closes a fifth-power pair (`5` divides both equal exponents and `7` or `19` divides the hypotenuse). `IsSharedExpCubeOrFifth` closes a shared divisor `n ≥ 4` beside a hypotenuse divisible by `3` or by `5`. `(4,4,7)`, `(10,10,7)`, and `(10,10,9)` leave this leaf; `(22,22,7)` and `(10,10,11)` remain |
| `BealTwoEqualEvenDiffOutsideFifthPairResidual` | even two-equal difference, via `BealTwoEqualEvenDiffResidual_of_outside_fifth`. `(7,10,10)` is a fifth-power pair. The same shared-exponent cut applies when the two left exponents share `n ≥ 4` |
| `BealTwoEqualOddOutsideFifthPairResidual` | odd two-equal, via `BealTwoEqualOddResidual_of_outside_fifth_pair`. `(25,25,7)` and `(5,5,21)` are fifth-power pairs. `(9,7,7)` is the shared-exponent cut; `(5,5,11)` remains |
| `BealAllDistinctOutsideFifthPairResidual` | pairwise distinct exponents, via `BealAllDistinctExpResidual_of_outside_fifth_pair`. `(5,10,7)` is a fifth-power pair. `(8,12,9)` is the shared-exponent cut; `(3,5,7)` remains |
| `BealEqualOddTwoFactorExpGeFiveResidual` | equal-odd Gaussian body, via `BealEqualOddTwoFactorResidual_of_ge_five` |
| `BealPythagoreanUnequalOddOutsideFifthPairResidual` | exponent-gcd `2` outside those slices, via `BealPythagoreanUnequalOddResidual_of_outside_fifth_pair`. `(10,10,14)` is a fifth-power pair. `(10,10,18)` is the shared-exponent cut |

`FermatMixedMotorResidual` discharges classical FLT
(`FermatLastTheorem_of_mixed_motor_residual`).

### Live bridges

| Bridge | Headline it discharges |
| --- | --- |
| `AbcModularBridge` | abc conjecture (`abc_conjecture_of_modular_bridge`) |
| `CollatzAdmissibleBridge` | Collatz (`collatz_conjecture_of_bridge`; equivalent, `collatzAdmissibleBridge_iff`) |
| `GoldbachAdmissibleBridge` | Goldbach (`goldbach_conjecture_of_bridge`; equivalent, `goldbachAdmissibleBridge_iff`) |
| `PolignacAdmissibleBridge` | Polignac, and twin primes at `k = 1` |
| `RiemannAdmissibleBridge` | off-line positive-height statement (`riemann_hypothesis_of_bridge`). Not mathlib's `riemannZeta` |

## Assembled headlines (no `sorry`)

`Diophantine/Headlines.lean` states the eight claims and proves them from the
leaves above. The proofs are not unconditional.

| Theorem | Open leaf |
| --- | --- |
| `classical_beal_conjecture` | the six Beal leaves (and the FLT axiom in the main library) |
| `fermat_last_theorem_unconditional` | `fermatMixedMotorResidual` |
| `abc_conjecture_unconditional` | `abcModularBridge` |
| `collatz_conjecture_unconditional` | `collatzAdmissibleBridge` |
| `goldbach_conjecture_unconditional` | `goldbachAdmissibleBridge` |
| `polignac_conjecture_unconditional` | `polignacAdmissibleBridge` |
| `twin_prime_conjecture_unconditional` | `polignacAdmissibleBridge` at `k = 1` |
| `riemann_hypothesis_unconditional` | `riemannAdmissibleBridge` |

### Physics frontiers (closed in the main library)

| Theorem | Statement |
| --- | --- |
| `Mercury.perihelion_arcsec_bounds` | `(radialReturn M α β - 2π)` times Mercury's orbits per Julian century lies in `(42, 44)` arcseconds, with the same external elements and SI stand-ins |
| `SolarDeflection.solar_deflection_arcsec_bounds` | Azimuthal excess of an exterior null ray that turns at the nominal solar radius lies in `(17/10, 9/5)` arcseconds. The excess is strictly above `4GM/(c²R)`. No eclipse residual is claimed |
| `SignReversal.chargedPionSelectsReversalScale` | Unique `r₁` in `(1/2, 1)` with `lengthOfReversal r₁ = pionComptonFm`. The charged-pion Compton stand-in picks one scattering scale; it does not remove `r₁` from the rest of the channel |
| `ScatteringScale.scatteringSignCuts_iff` | Repulsion at `1/2` and attraction throughout `[1, 2]` are exactly `1/2 < r₁ < 1`, hence `14/15 < lengthOfReversal r₁ < 19/10`. `scatteringSignCuts_not_unique` shows `3/5` and `9/10` both match. `gammaSEqual_even` is why the sign of `ℓ` is not chosen by the force signs |
| `HydrogenRepulsion.lyman_two_over_three`, `balmer_alpha_over_beta` | With the constant factor `1`, the Lyman ratio is `27/32` and Hα/Hβ is `27/20`. `equalScale_nodes_miss_lyman` and `inv_node_gap_lt_hydrogen` put the equal-scale node gaps strictly below `27/32` and `5/27`. No fine structure, and `ℓ` is not derived |
| `NewtonWigner.no_newtonWignerPair_dual`, `no_newtonWignerPair_dirac` | No endomorphism pair of `DualSpinor` or `DiracSpinor` has commutator `i I`. A continuous eigenfield of chart multiplication is zero. One momentum has constant Born density |
| `PositionInformation.whichMomentum_sq_add_fringeVisibility` | `D² + V² = 1`. A definite momentum has `D = 1` and `V = 0`. Equal weights have `D = 0` and `V = 1`. This is not a position operator |
| `PhaseInformation.whichMomentum_sq_add_phaseInformation` | `I = 4p(1 − p) = V²`, so `D² + I = 1`. Half weights give `I = 16/25`. `phaseInformation_not_a_location` keeps `I = 1` with no chart contrast when the two momenta coincide. `chart_reads_phaseInformation` reads a positive `I` on the chart, and every sample is a scalar times one carrier spinor. Scaling that spinor drops out of `I` |
| `Kerr.inducedMetric_kerr` | On `Σ > 0` and `Δ > 0` the coframe induces the Kerr metric. `kerrCoframe_zero_spin` returns exterior Schwarzschild. `kerr_cross_ne_azimuthBoost` refuses a pure-boost reading of the cross term. No perihelion window |
| `DualRotorDynamics.paperActualEL_not_oscillator` | The written action does not yield `δ̈ + mδ = 0`. Conjugate momenta are half the mismatch rate and half the common rate, and `m` is not a factor |
| `RelationalPolarization.diameter_one_root_iff` | The diameter angle derivative has a root in `(0, π/2)` exactly when `Z = 4`, and then every such angle is a root. `unit_usualConstraint_ne_angleDeriv` says that derivative is not the constraint force. No `ℓ` enters |

## Not yet stateable (index only)

No definition in the main library states these claims. A `True` placeholder
is not a substitute. Rows tagged **P0** / **P2** / **P3** in the first column
are the definition-first work called out in the breakthrough strategy; untagged
rows stay deferred. The Kerr **P2** already has the chart. What is missing is
the window.

| Pri | Topic | Claim (short) | Missing definition |
| --- | --- | --- | --- |
| | Antiparticle | Standard Model fermion ↔ dual-sector phase; production and annihilation rates | Unified generation–sector identification |
| | Gravitational lensing | Null ray through the freeze chart compared with a named flare | `PhotonReturn` proves a finite Killing-time visit inside the freeze, with brackets in units of `GM/c³`. It does not claim a magnification or a flare. `Lensing` does not integrate a null ray through the freeze |
| **P3** | Dynamic equation | Full DST evolution equation in closed form | Global time-evolution operator on coupled rotors. `DualRotorDynamics` already has the written Euler–Lagrange system and the conjugate momenta, and `paperActualEL_not_oscillator` refuses `δ̈ + mδ = 0`. The angle derivative in `RelationalPolarization` is not that operator |
| | Beta decay | Mass excess as a class difference with no external input | Unsigned mass-class order |
| | De Broglie | A spacetime wave, or `E/ℏ` from rest mass | That wave. `DeBroglie` proves `SU(2)` invariants and states that none of them is a Schrödinger wave or a derivation of `E/ℏ`. `NewtonWigner` refuses the carrier operator. `PositionInformation` is the fringe relation `D² + V² = 1`, and `PhaseInformation` is `D² + I = 1`. Neither is that wave |
| **P2** | Rotating masses | Perihelion or frame dragging on the Kerr chart, in a named window | That window. `Kerr` already induces the metric on `Σ > 0` and `Δ > 0`, returns exterior Schwarzschild at vanishing spin, and refuses a pure-boost reading of the cross term. The horizon `Δ = 0` is not claimed |
| | Interior clocks | A light signal makes the beat of two clocks the carrier's wavelength change, read against the deep-interior surplus | That identification. `InteriorClock` defines `compactness` and `centreAdvance`; the Earth figures are external rounding bins |
| | Mach | Inertial mass from surrounding sources, with stiffness `m` derived | A definition of `m` from the source sum. `MachSource` states that sources do not determine `m` |
| **P0** | Galactic rotation | Flat rotation curves for a general baryonic disk, with `a₀` derived | A theorem that does not take `a₀` as an input. `GalaxyCurve` already bounds stand-in dwarfs (for example `50.2 < v_∞ < 50.3` km/s at `4×10⁸ M_⊙`) from external `a₀` and `G`, and does not assert `dst_derives_a0` |
| **P0** | Channel length, one value | One scattering scale, past the window `14/15 < ℓ < 19/10` | A length that is not `layerRadius ℓ x` for a phase `x` independent of `ℓ`. `layerRadius_scale` cancels every such phase, and `thresholdRadius_scale_not_unique` refuses a point. `deriv_phiStar_ne_zero` gives `phiStar` no critical phase on `(π/4, π/2)`. Critical phases of `gammaSEqual` are integer multiples of `π` and stay in the family; `(0, π)` has none. `pairChannelForce_layer_zero_not_unique` refuses a point, as does `charge_over_nuclear_length_not_unique` for the external electromagnetic ratio. `fourteenMeV_fractional_widening` still bounds the external `14` MeV skin by `6/100` of the static node. `scatteringSignCuts_iff` is still the window `1/2 < r₁ < 1`. `gammaSEqual_even` and the charged-pion selector are unchanged. `HydrogenRepulsion` does not select `ℓ`: the factor `1` carries the gross-structure ratios, and the node gaps miss `27/32` and `5/27`. `RelationalPolarization` does not use `ℓ`. `StrongChannel` does not derive `ℓ` or the laboratory `1/v` law |
| | Neutron capture | Cross section growing as `1/v` | A cross section. `StrongChannel` states that the laboratory `1/v` law is not derived |
| | Magic-number splitting | The oscillator closures arise from the layer nodes | That derivation. The integers themselves are theorems: `oscillatorClosure` is `2, 8, 20` and `shiftedClosure` is `28, 50, 82, 126` (`NuclearLayer`) |
| | Surface pairs | Nucleon-pair forces across a touching surface, summed | That sum. The head-on distance of a `7.69` MeV alpha on gold is already in `(29, 30)` fm (`Rutherford`); no cross section is computed there |
| | Neutron skin | Speed-dependent skin and negative scattering lengths | A close-encounter amplitude |
| | Cold-fusion entrance | Entrance frequency of the octahedral seat | A frequency. `MetalFusion` proves the sign and a unique balance, and states that no rate is derived |
| | Atomic radii | Measured radii match the shell seats, past an external comparison with `n²a₀` | That identification. `ElectronNumbers` proves an order of radii in units of `ℓ` and states that `ℓ` is not derived |
| | Bohr ladder | `n²a₀`, or the gross-structure ratios, derived from the channel factor `γ_s` | That derivation. The ratios themselves are theorems of the factor `1` (`lyman_two_over_three`, `balmer_alpha_over_beta`). `equalScale_nodes_miss_lyman` and `inv_node_gap_lt_hydrogen` refuse reading them off equal-scale nodes. `bohrRadiusApprox` is an SI input. `ℓ` is not derived |
| | Electron exclusion | Pauli exclusion as the same layer mechanism that separates nucleons | An identification. `SpinVersusExclusion` does not provide one. Shell seats `2, 8, 18` are theorems in `ElectronCapacity` |
| | Curved transport | Photon transport identified with the torsional mismatch | That identification. `CurvedTransport` proves that the static boost is parallel along the observer and that an angular leg tilts at rate `κ√A/r`. The module states that this bivector is not the torsional mismatch. Do not reopen the equality as a Goal |
| | Off-equator orbits | Inclined orbits tied to the parent torsional mismatch | An identification of the `OffEquator` constants with `Ω` |
| | Faraday control | Laboratory Weinberg angle and W/Z masses | Those quantities. `Electroweak`, `ChiralCurrent`, and `DualRotorRigidity` state that they are not derived |
| | Node clearance | Every sample stays a full step from a node | A clearance predicate beyond the first-node cap in `ShieldCeiling` |
| | Binding energy | Binding energy from the first-node clearance cap | An operator. `bindingEnergyPerNucleonMeVApprox` is an external SI label. `NuclearLength` produces no binding energy |
| | Channel walls | Finite wall height, with layer positions fixed | A derived finite height |
| **P3** | Dual Hilbert lift | Subspace facts of the ordinary layer become theorems of the dual Hilbert layer | A map from a named D4L fragment into `QProp`. `BooleanIsland` and `BlockReading` compare pairs whose two implications already agree: the expansion detaches on those pairs, and the four positive-wall rules are the classical bit rules on an island. That comparison is not the missing map. `QuantumLogic` already proves the orthomodular law on `ℂ²`. `Separation` proves that `min`/`max` is not that lattice, and `infinite_one_dim_subspaces` shows four labels do not enumerate the atoms. `NewtonWigner`, `PositionInformation`, and `PhaseInformation` are chart facts on the carrier, not this map |
| | Propellantless control | Laboratory inertia coupling by a motor whose translation commutes with torsion | A laboratory observable. `MotorGroup` proves the commuting exponential is a motor and does not claim a closed product law on `OmegaParams` |

## Not targets (recorded in the main library)

| Prop | Why it is not a Goal |
| --- | --- |
| `BealPosCubeAddTwoCubeResidual` | Theorem `BealPosCubeAddTwoCubeResidual_of_euler` |
| `BealTwoEqualEvenSumExpFiveResidual` | Theorem `BealTwoEqualEvenSumExpFiveResidual_of_NN5` |
| `BealAffineCubeAddTwoResidual` | The Euler axiom, by abbreviation |
| `BealMordellCubeAddTwoResidual` | Diagnostic Weierstrass packaging. The cube leaf is the Euler theorem, not this packaging |
| `BealTwoEqualEvenDiffFactorResidual`, `BealTwoEqualEvenDiffPerfectPowerResidual` | Older packaging of the even-difference body. The named leaf is `BealTwoEqualEvenDiffOutsideFifthPairResidual` |
| `BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual` | Follows from `BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual` by `bennettEllenbergNg` |
| `BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual` | Follows from `BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual` by `sumTwoFifthsNotSeventhOrNineteenth` (phase 8a) |
| `BealTwoEqualEvenDiffOutsideCubePairResidual` | Follows from `BealTwoEqualEvenDiffOutsideFifthPairResidual` by the same axiom |
| `BealTwoEqualOddOutsideRepeatedFifthResidual` | Follows from `BealTwoEqualOddOutsideFifthPairResidual` by the same axiom |
| `BealAllDistinctOutsideCubePairResidual` | Follows from `BealAllDistinctOutsideFifthPairResidual` by the same axiom |
| `BealPythagoreanUnequalOddOutsideCubePairResidual` | Follows from `BealPythagoreanUnequalOddOutsideFifthPairResidual` by the same axiom |
| `BealAdmissibleBridge`, `FermatAdmissibleBridge` | Continuous bridges. Balanced seeds sit below the threshold |
| `FermatModularBridge` | Payload incompatible with real-scale admissibility |
| `FermatCoarseDiscreteBridge` | Witness empty under the coarse threshold. Not a research target |
| `AbcAdmissibleBridge` | False (`AbcAdmissibleBridge_false`), from the triple `1 + 8 = 9` |
| `BealCGADilationNoGo`, `BealModularBridge`, `BealWindingBridge` | Not in the tree. `Algebra/CGA` is not on the algebra barrel |
| Carrier Newton–Wigner pair | Refused (`no_newtonWignerPair_dual`, `no_newtonWignerPair_dirac`). Chart position is `whichMomentum_sq_add_phaseInformation`. The weight formula `I` is not itself a location |
| Equal-scale nodes as the gross structure | Refused (`equalScale_nodes_miss_lyman`, `inv_node_gap_lt_hydrogen`). The ratios belong to the factor `1` |
| Written oscillator `δ̈ + mδ = 0` | Refused (`paperActualEL_not_oscillator`). The same-sign working model is not the written action |
| Angle derivative of `RelationalPolarization` as the force | Refused (`unit_usualConstraint_ne_angleDeriv`) |
| Kerr cross term as a pure azimuthal boost | Refused (`kerr_cross_ne_azimuthBoost`) |
| `CurvedTransport` bivector as the torsional mismatch | The module states that the proved transport is not that identification |

The positive-wall cut is a theorem of the main library (`Logic.WallRule`), not a Goal. For a finite set of premises, forcing on the interval depends only on the atoms that occur, and it splits into classical consequence and the balance case. Discharge agrees with classical consequence on the walls at every finite depth. Synchrony, non-refutation, and positive-wall forcing are pairwise incomparable. None of this discharges the twelve open targets above, and `U → T = U` still refuses a promotion from an open bridge to `T`.

## Proved headline results (main library only — no Goals entry)

Examples already sorry-free in `DstDiophantine/`: admissible bound
`|J_norm| ≤ 1`, PGA motor algebra, Schwarzschild exterior leading perihelion
coefficient, Mercury arcseconds per Julian century in `(42, 44)`, solar null
deflection in `(17/10, 9/5)` arcseconds, unique charged-pion reversal scale in
`(1/2, 1)`, sign-reversal window for ℓ, Coulomb hydrogen ratios `27/32` and
`27/20`, Kerr coframe on `Σ > 0` and `Δ > 0`, carrier Newton–Wigner refusal
and `D² + V² = 1`, written one-axis Euler–Lagrange system, Coulomb from the
dual channel, partial metal-fusion sign lemmas, Collatz certificate up to
`2^20`. These are not duplicated as Goals. A sharper observational match,
including a window on the Kerr chart and a channel derivation of `a₀` or `ℓ`,
stays in the not-yet-stateable index until the missing definition exists.
