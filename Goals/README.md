# Goals — Lean target statements

This directory is **isolated** from the proved library under `DstDiophantine/`.
A target is a `theorem` whose statement is a `Prop` from the main library.
Policy: see [`POLICY.md`](POLICY.md).

Build: `lake build Goals` (sorry allowed). The default `lake build` does not
include this library.

Open `sorry` count: **12** (`scripts/count_goals.sh`). All twelve are
Diophantine leaves and bridges. A physics aim below is not a Lean Goal until
the main library defines its `Prop`.

## Breakthrough order

A breakthrough is one of three things, in this order of programme value:

1. **Identity** — a named constant that is an input today becomes a theorem
   of the dual-rotor / channel geometry (no external fit).
2. **Observation** — another classical GR or scattering observable, stated
   with library definitions and proved in a named window.
3. **Amplification** — at least one live Diophantine leaf or bridge is closed
   by the DST encoding itself, not by importing a further number-theory axiom.

Diagnostic or false bridges (`AbcAdmissibleBridge`, and the modular or
admissible Beal and Fermat packages marked demoted) are not breakthrough
routes. The amplification no-go (layer 2) is proved. Layer 3 — a leaf or a
live bridge — is still open.

## Near-term order

Work proceeds in priority order. A row becomes a Lean `sorry` only when the
main library already defines the `Prop`. A `True` placeholder is forbidden.
Land the missing definition in `DstDiophantine/` first, then add the `sorry`
in the same PR that updates this index.

| Pri | Aim | Missing definition | Success |
| --- | --- | --- | --- |
| **P0** | One value of the channel length `ℓ`, or no free `r₁` | A length that is not `layerRadius ℓ x` for a phase `x` independent of `ℓ`, stated before any uniqueness `sorry` | One value of `ℓ` on that path, with no free channel input |
| **P0** | `a₀`, or an equivalent MOND scale, from the source geometry | `a₀` from the dual period or from baryonic data, so a flat curve does not take `a₀` as an input | A named flat-speed window with no `a₀` input |
| **P2** | One named window on the Kerr chart | The observable (perihelion or frame dragging), from library definitions, in a window | A theorem in that window. Only then a Goal |
| **P3** | Closed-form DST evolution | A global time-evolution operator on coupled rotors | The target is no longer not yet stateable |
| **P3** | Dual Hilbert lift | A map from a named D4L fragment into `QProp` | That definition, and at least one lifted island theorem |

Solar deflection is closed. See [Closed and refused](#closed-and-refused).

Open `sorry`s, in order:

1. The six Beal leaves (P1). Closing one is the amplification breakthrough, and Goals deletes that `sorry`.
2. `fermatMixedMotorResidual` (P2). The motor path is native to DST.
3. `collatzAdmissibleBridge`, ahead of Goldbach and Polignac (P2).
4. `abcModularBridge` and `riemannAdmissibleBridge`, after the three above.

Identity budget stays on the P0 rows until a P0 or a P1 closes. `G` and `α`
stay underived, and they are not scheduled ahead of those rows. Electroweak
masses, propellantless control, a cold-fusion rate, and Mach `m` wait with
the untagged rows under Not yet stateable.

## Open `sorry` catalogue

| Module | Count | What is open |
| --- | ---: | --- |
| `Diophantine/Residuals.lean` | 7 | `FermatMixedMotorResidual` and the six Beal leaves |
| `Diophantine/Bridges.lean` | 5 | abc modular; Collatz, Goldbach, Polignac, and the critical-line bridge |
| **Total** | **12** | |

### Beal leaves

Positive Beal follows from these six, together with the FLT axiom already in
the main library (`beal_conjecture_pos_of_fine_residuals_even_split`).
`IsSharedExpCubeOrFifth` is closed by `darmonMerelCube` and
`fermatSignatureNN5`: a shared divisor `n ≥ 4` beside a third exponent
divisible by `3` or by `5` is not a remaining signature. On a difference
seat `n` is odd.

| Leaf | Discharges | Still in this leaf |
| --- | --- | --- |
| `BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual` | Even two-equal sum, via `BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth_fifth` | `(22,22,7)`. A common exponent divisible by `4`, a fifth-power pair (`5` divides two exponents and `7`, `11`, `13`, `17`, or `19` divides the third), and `IsSharedExpCubeOrFifth` have left, including `(4,4,7)`, `(10,10,7)`, `(10,10,9)`, and `(10,10,11)` |
| `BealTwoEqualEvenDiffOutsideFifthPairResidual` | Even two-equal difference, via `BealTwoEqualEvenDiffResidual_of_outside_fifth` | Open except the fifth-power pair `(7,10,10)`, and except the shared-exponent cut when the two left exponents share `n ≥ 4` |
| `BealTwoEqualOddOutsideFifthPairResidual` | Odd two-equal, via `BealTwoEqualOddResidual_of_outside_fifth_pair` | `(5,5,23)` and `(7,7,11)`. `(5,5,11)`, `(5,5,13)`, `(5,5,17)`, `(25,25,7)`, and `(5,5,21)` are fifth-power pairs, and `(9,7,7)` is the shared-exponent cut |
| `BealAllDistinctOutsideFifthPairResidual` | Pairwise distinct exponents, via `BealAllDistinctExpResidual_of_outside_fifth_pair` | `(3,5,7)`. `(5,10,7)` and `(5,10,11)` are fifth-power pairs, and `(8,12,9)` is the shared-exponent cut |
| `BealEqualOddTwoFactorExpGeFiveResidual` | Equal-odd Gaussian body, via `BealEqualOddTwoFactorResidual_of_ge_five` | Open as stated |
| `BealPythagoreanUnequalOddOutsideFifthPairResidual` | Exponent-gcd `2` outside those slices, via `BealPythagoreanUnequalOddResidual_of_outside_fifth_pair` | The leaf outside the fifth-power pair `(10,10,14)` and the shared-exponent cut `(10,10,18)` |

`FermatMixedMotorResidual` discharges classical FLT
(`FermatLastTheorem_of_mixed_motor_residual`). Excess and odd-prime
factorisation lemmas are in the main library; the residual is open.

### Live bridges

Finite certificates exist. The infinite statement is open.
`collatzAdmissibleBridge` is first among them: cone facts and certificates
for `n ≤ 2^20` are the strongest local base.

| Bridge | Headline it discharges |
| --- | --- |
| `AbcModularBridge` | abc conjecture (`abc_conjecture_of_modular_bridge`) |
| `CollatzAdmissibleBridge` | Collatz (`collatz_conjecture_of_bridge`; equivalent, `collatzAdmissibleBridge_iff`) |
| `GoldbachAdmissibleBridge` | Goldbach (`goldbach_conjecture_of_bridge`; equivalent, `goldbachAdmissibleBridge_iff`) |
| `PolignacAdmissibleBridge` | Polignac, and twin primes at `k = 1` |
| `RiemannAdmissibleBridge` | Off-line positive-height statement (`riemann_hypothesis_of_bridge`). Not mathlib's `riemannZeta` |

### Assembled headlines (no `sorry`)

`Diophantine/Headlines.lean` states the eight claims and proves them from the
leaves above. The proofs are not unconditional.

| Theorem | Open leaf |
| --- | --- |
| `classical_beal_conjecture` | The six Beal leaves, and the FLT axiom in the main library |
| `fermat_last_theorem_unconditional` | `fermatMixedMotorResidual` |
| `abc_conjecture_unconditional` | `abcModularBridge` |
| `collatz_conjecture_unconditional` | `collatzAdmissibleBridge` |
| `goldbach_conjecture_unconditional` | `goldbachAdmissibleBridge` |
| `polignac_conjecture_unconditional` | `polignacAdmissibleBridge` |
| `twin_prime_conjecture_unconditional` | `polignacAdmissibleBridge` at `k = 1` |
| `riemann_hypothesis_unconditional` | `riemannAdmissibleBridge` |

## Not yet stateable

No definition in the main library states these claims. A `True` placeholder
is not a substitute. Rows tagged **P0**, **P2**, or **P3** are the
definition-first aims above; the cell points there. Untagged rows stay
deferred.

| Pri | Topic | Claim | Missing definition |
| --- | --- | --- | --- |
| | Antiparticle | Standard Model fermion ↔ dual-sector phase; production and annihilation rates | Unified generation–sector identification |
| | Gravitational lensing | A null ray through the freeze chart, compared with a named flare | A magnification or a flare |
| **P3** | Dynamic equation | Full DST evolution in closed form | See [Near-term order](#near-term-order) |
| | Beta decay | Mass excess as a class difference, with no external input | Unsigned mass-class order |
| | De Broglie | A spacetime wave, or `E/ℏ` from rest mass | That wave |
| **P2** | Rotating masses | Perihelion or frame dragging on the Kerr chart, in a named window | See [Near-term order](#near-term-order) |
| | Interior clocks | The beat of two clocks is the carrier's wavelength change, read against the deep-interior surplus | That identification |
| | Mach | Inertial mass from surrounding sources, with stiffness `m` derived | A definition of `m` from the source sum |
| **P0** | Galactic rotation | Flat rotation curves for a general baryonic disk, with `a₀` derived | See [Near-term order](#near-term-order) |
| **P0** | Channel length | One scattering scale, past the sign window | See [Near-term order](#near-term-order) |
| | Neutron capture | A cross section growing as `1/v` | A cross section |
| | Magic-number splitting | The oscillator closures arise from the layer nodes | That derivation |
| | Surface pairs | Nucleon-pair forces across a touching surface, summed | That sum |
| | Neutron skin | A speed-dependent skin and negative scattering lengths | A close-encounter amplitude |
| | Cold-fusion entrance | Entrance frequency of the octahedral seat | A frequency |
| | Atomic radii | Measured radii match the shell seats, past an external comparison with `n²a₀` | That identification |
| | Bohr ladder | `n²a₀`, or the gross-structure ratios, from the channel factor `γ_s` | That derivation. `bohrRadiusApprox` is an SI input |
| | Electron exclusion | Pauli exclusion as the same layer mechanism that separates nucleons | An identification |
| | Curved transport | Photon transport identified with the torsional mismatch | That identification |
| | Off-equator orbits | Inclined orbits tied to the parent torsional mismatch | An identification of the `OffEquator` constants with `Ω` |
| | Faraday control | Laboratory Weinberg angle and W/Z masses | Those quantities |
| | Node clearance | Every sample stays a full step from a node | A clearance predicate beyond the first-node cap in `ShieldCeiling` |
| | Binding energy | Binding energy from the first-node clearance cap | An operator. `bindingEnergyPerNucleonMeVApprox` is an external SI label, and `NuclearLength` produces none |
| | Channel walls | Finite wall height, with layer positions fixed | A derived finite height |
| **P3** | Dual Hilbert lift | Subspace facts of the ordinary layer become theorems of the dual Hilbert layer | See [Near-term order](#near-term-order) |
| | Propellantless control | Laboratory inertia coupling by a motor whose translation commutes with torsion | A laboratory observable |

## Closed and refused

Proved in the main library, or recorded there as a refusal. None of these is
a Goal.

| Item | Standing |
| --- | --- |
| `\|J_norm\| ≤ 1`, PGA motor algebra | Proved. Regression only |
| Schwarzschild leading perihelion coefficient | Proved for the exterior chart. The arcsecond window is the Mercury row |
| `Mercury.perihelion_arcsec_bounds` | `(radialReturn M α β - 2π)` times Mercury's orbits per Julian century lies in `(42, 44)` arcseconds, from the external elements and SI stand-ins |
| `SolarDeflection.solar_deflection_arcsec_bounds` | Azimuthal excess of an exterior null ray that turns at the nominal solar radius lies in `(17/10, 9/5)` arcseconds, strictly above `4GM/(c²R)`. No eclipse residual |
| `SignReversal.chargedPionSelectsReversalScale` | Unique `r₁` in `(1/2, 1)` with `lengthOfReversal r₁ = pionComptonFm`. The selector does not remove `r₁` from the rest of the channel |
| `ScatteringScale.scatteringSignCuts_iff` | Repulsion at `1/2` and attraction throughout `[1, 2]` are exactly `1/2 < r₁ < 1`, hence `14/15 < lengthOfReversal r₁ < 19/10`. `scatteringSignCuts_not_unique` shows `3/5` and `9/10` both match. `gammaSEqual_even` is why the force signs do not choose the sign of `ℓ` |
| `layerRadius_scale`, `layerRadius_pair_ratio_scale` | Cancel `ℓ` for every phase that ignores the length |
| `thresholdRadius_scale_not_unique` | Refuses a point |
| `deriv_phiStar_ne_zero` | `phiStar` has no critical phase on `(π/4, π/2)` |
| `gammaSEqual_critical_radius_div_length`, `gammaSEqual_deriv_ne_zero_of_mem_Ioo_pi` | `gammaSEqual` is critical only where `sin = 0`. Those integer multiples of `π` stay in the `layerRadius` family, and `(0, π)` has none |
| `pairChannelForce_eq_zero_iff`, `pairChannelForce_layer_zero_not_unique` | The separation drops out, and a layer zero is not a unique point |
| `charge_over_nuclear_length_not_unique` | The external electromagnetic ratio `(203, 414)` does not select a point |
| `fourteenMeV_fractional_widening` | The skin stays under `6/100` of the node |
| `HydrogenRepulsion.lyman_two_over_three`, `balmer_alpha_over_beta` | With the constant factor `1`, the Lyman ratio is `27/32` and Hα/Hβ is `27/20`. `equalScale_nodes_miss_lyman` and `inv_node_gap_lt_hydrogen` put the equal-scale node gaps strictly below `27/32` and `5/27`. No fine structure |
| Coulomb from the dual channel | Proved |
| `NewtonWigner.no_newtonWignerPair_dual`, `no_newtonWignerPair_dirac` | No endomorphism pair of `DualSpinor` or `DiracSpinor` has commutator `i I`. A continuous eigenfield of chart multiplication is zero. One momentum has constant Born density. Not an L² operator |
| `PositionInformation.whichMomentum_sq_add_fringeVisibility` | `D² + V² = 1`. A definite momentum has `D = 1` and `V = 0`. Equal weights have `D = 0` and `V = 1` |
| `PhaseInformation.whichMomentum_sq_add_phaseInformation` | `I = 4p(1 − p) = V²`, so `D² + I = 1`. Half weights give `I = 16/25`. `phaseInformation_not_a_location` keeps `I = 1` with no chart contrast when the two momenta coincide. `chart_reads_phaseInformation` reads a positive `I` on the chart; every sample is a scalar times one carrier spinor, and scaling that spinor drops out of `I` |
| `ShellInformation.shellInformation_eq_fidelity_sq` | On one mass shell, `I = fidelity² · phaseInformation`. Orthogonal carriers give `I = 0`, and `diracMomentum_unique` refuses one spinor at two shell momenta. In the mean rest frame the relative momentum is spatial, so the Born density is invariant under time translation. The mass-3 pair has fidelity `9/25` and information `81/625` |
| `FrameInformation.relativeEnergy_timeContrast` | A nonzero relative energy lies on the time axis. Rest against `(5, 4, 0, 0)` has fidelity `4/5`, weight information `225/289`, and shell information `144/289`. The densities at time `0` and `-π/2` are `116/9` and `20/9`. The origin sample lies on neither carrier ray. The opposite Weyl seed has information `0` |
| `CarrierDeficit.which_shell_deficit` | `D² + I_shell + Δ = 1`, with `Δ = (1 − F²) · phaseInformation`. The extreme chart ratio equals `shellVisibility`, so those two samples do not read `Δ`. One nonzero mass and two momenta force `Δ > 0`, and every chart contrast stays strictly below `4rs‖u‖‖v‖`. Mean rest: `Δ = 544/625`. Rest against `(5, 4, 0, 0)`: `D = 8/17`, visibility `12/17`, `Δ = 81/289`. The opposite seed has `Δ = 1` |
| `PhaseFisher.phaseFisher_quadrature` | At a quadrature phase the projective Fisher information equals `Δ`. The extreme chart ratio still squares to `I_shell`, not to the Fisher number sampled there (`PhaseFisher.shellRest_chart_not_fisher`). Mean rest, mass 3: quadrature `544/625`, peak `136/289`, valley `17/8`. Rest against `(5, 4, 0, 0)`: Fisher `81/841` and `81/25` at the extreme times, and `81/289` at a quadrature. The opposite Weyl seed has Fisher `1` at every phase. `PhaseFisher.phaseSLD_fisher` is the symmetric logarithmic derivative on the weight space |
| `ChartFisher.chartFisher_eq_velocity` | A displacement along axis `μ` has Fisher information `phaseFisher · ((q − p) μ)²`. At a quadrature phase that is `Δ · ((q − p) μ)²`. The number repeats after one fringe period, while `positionOp` multiplies by a different coordinate. Mean rest: time `0`, axis `1` is `34816/625`, which is not `64 · 81/625`. Rest against `(5, 4, 0, 0)`: time-axis Fisher `324/289` at quadrature, `324/841` and `324/25` at the extreme times. The opposite seed has spatial Fisher `64`. The same momentum has chart Fisher `0` |
| `ChartScore.chartScore_normSq` | On a nonzero sample the displacement score is orthogonal to the state, and its squared length is `chartFisher` times the Born density. `positionOp` multiplies by the coordinate. The two vectors are not scalar multiples when the coordinate and the Fisher information are both nonzero. Mean rest, origin, axis `1`, quadrature: the position reads `0` and the score length squared is `139264/225`. At time `1` the score is `0` and the position reads `1`. Rest against `(5, 4, 0, 0)` at time `-π/2`: the position reads `-π/2` and the score length squared is `144/5`. The opposite seed at the origin has position `0` and score length squared `6400/9`. One momentum has score `0` and position `1` |
| `MomentumReading.momentumHorizontal_eq_packetScore` | On a nonzero shell-packet sample the part of `momentumOp` orthogonal to the sample is `-i/2` times the displacement score, so its squared length is `chartFisher` times the Born density over `4`. The Rayleigh quotient's real part is the interference-weighted momentum. Mean rest, quadrature, origin, axis `1`: real part `0`, imaginary part squared `(36/25)²`, horizontal length squared `34816/225`. The time axis is the eigen-sample `5 • Ψ`. Rest against `(5, 4, 0, 0)` at time `-π/2`: the quotient is `28/5` and the horizontal length squared is `36/5`, while the position reads `-π/2`. The opposite seed has quotient `0`, a nonzero momentum operator, and horizontal length squared `1600/9`. The zero-momentum packet has `momentumOp = 0` and position `1` |
| `TranslationFisher.translationFisher_outer` | `F_μν = 4 Cov(P_μ, P_ν) = phaseFisher · (q − p)_μ · (q − p)_ν`. The diagonal is `chartFisher`. The matrix has rank at most one, so the Cramér–Rao floor is the reciprocal of `vᵀ F v` on the support, not an inverse on all four coordinates, and not a reading of `positionOp`. Mean rest, quadrature: time slot `0`, axis `1` is `34816/625`, floor `625/34816`, position reading `0`. The boost `cosh = 5/3`, `sinh = -4/3` preserves the contraction `34816/625` and puts `557056/5625` on the time slot. Rest against `(5, 4, 0, 0)` at time `-π/2`: time floor `25/324`, position reading `-π/2` |
| `BornLorentz.invariantDensity` | The chart Born density is `J⁰`. On a positive-energy shell it equals the Dirac scalar exactly at rest, and off rest the scalar is `(m / p₀)` times the chart density. A longitudinal boost multiplies the chart density by `cosh` and leaves the scalar fixed; they agree for every seed only at rapidity `0`. The fixed-seed mass-3 carriers have chart density `50/9` and scalar `10/3`, ratio `5/3`. Rest has both equal to `2`. A rotor image of that rest spinor at `(5, 4, 0, 0)` has chart density `10/3` and scalar `2`, and is not a complex multiple of the fixed seed. Mean-rest weight information stays `1`. Against rest, the scalar reading is `15/16` and the chart reading is `225/289`. The shell information `144/289` still uses the chart fidelity |
| `Kerr.inducedMetric_kerr` | On `Σ > 0` and `Δ > 0` the coframe induces the Kerr metric. `kerrCoframe_zero_spin` returns exterior Schwarzschild. `kerr_cross_ne_azimuthBoost` refuses a pure-boost reading of the cross term. The horizon `Δ = 0` is not claimed |
| `DualRotorDynamics.paperActualEL_not_oscillator` | The written action refuses `δ̈ + mδ = 0`. The same-sign working model is not that action. `paperMomentumSigma` and `paperMomentumDelta` are half the mismatch rate and half the common rate, and neither contains `m` |
| `RelationalPolarization.diameter_one_root_iff` | The diameter angle derivative, evaluated at the geodesic angle of `ρ = a⁻¹b`, has a root in `(0, π/2)` exactly when `Z = 4`, and then every such angle is a root. `unit_usualConstraint_ne_angleDeriv` says that derivative is not the constraint force. No `ℓ` enters |
| `GalaxyCurve`, `DualImage` | Stand-in dwarfs are bounded from external `a₀` and `G` (for example `50.2 < v_∞ < 50.3` km/s at `4×10⁸ M_⊙`). `dst_derives_a0` is refused |
| `DeBroglie` | Proves `SU(2)` invariants, and states that none of them is a Schrödinger wave or a derivation of `E/ℏ` |
| `MachSource` | Sources do not determine `m` |
| `StrongChannel` | States that the laboratory `1/v` law is not derived |
| `NuclearLayer` | `oscillatorClosure` is `2, 8, 20`. `shiftedClosure` is `28, 50, 82, 126` |
| `Rutherford` | The head-on distance of a `7.69` MeV alpha on gold lies in `(29, 30)` fm. No cross section |
| `MetalFusion` | Proves the sign and a unique balance, and states that no rate is derived |
| `ElectronNumbers` | Proves an order of radii in units of `ℓ` |
| `ElectronCapacity` | Shell seats `2, 8, 18` |
| `SpinVersusExclusion` | Does not identify Pauli exclusion with the nucleon layer mechanism |
| `CurvedTransport` | The static boost is parallel along the observer, and an angular leg tilts at rate `κ√A/r`. The module states that this bivector is not the torsional mismatch |
| `PhotonReturn` | A finite Killing-time visit inside the freeze, with brackets in units of `GM/c³`. Not a magnification or a flare |
| `InteriorClock` | Defines `compactness` and `centreAdvance`. The Earth figures are external rounding bins |
| `Electroweak`, `ChiralCurrent`, `DualRotorRigidity` | State that the laboratory Weinberg angle and the W/Z masses are not derived |
| `MotorGroup` | The commuting exponential is a motor. No closed product law on `OmegaParams` |
| `QuantumLogic`, `BooleanIsland`, `BlockReading`, `Separation` | The orthomodular law holds on `ℂ²`. Island comparisons are pairs whose two implications already agree: the expansion detaches on those pairs, and the four positive-wall rules are the classical bit rules on an island. `min`/`max` is not that lattice, and `infinite_one_dim_subspaces` shows four labels do not enumerate the atoms |
| `Logic.WallRule` | For a finite set of premises, forcing on the interval depends only on the atoms that occur, and it splits into classical consequence and the balance case. Discharge agrees with classical consequence on the walls at every finite depth. Synchrony, non-refutation, and positive-wall forcing are pairwise incomparable. None of this discharges the twelve open targets, and `U → T = U` still refuses a promotion from an open bridge to `T` |

### Not targets

These props are theorems, consequences, diagnostic, false, or absent from the
tree. They are not research targets.

| Prop | Why it is not a Goal |
| --- | --- |
| `BealPosCubeAddTwoCubeResidual` | Theorem `BealPosCubeAddTwoCubeResidual_of_euler` |
| `BealTwoEqualEvenSumExpFiveResidual` | Theorem `BealTwoEqualEvenSumExpFiveResidual_of_NN5` |
| `BealAffineCubeAddTwoResidual` | The Euler axiom, by abbreviation |
| `BealMordellCubeAddTwoResidual` | Diagnostic Weierstrass packaging. The cube leaf is the Euler theorem, not this packaging |
| `BealTwoEqualEvenDiffFactorResidual`, `BealTwoEqualEvenDiffPerfectPowerResidual` | Older packaging of the even-difference body. The named leaf is `BealTwoEqualEvenDiffOutsideFifthPairResidual` |
| `BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual` | Follows from `BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual` by `bennettEllenbergNg` |
| `BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual` | Follows from `BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual` by `sumTwoFifthsNotSeventhOrNineteenth` and `sumTwoFifthsNotStollPrime` |
| `BealTwoEqualEvenDiffOutsideCubePairResidual` | Follows from `BealTwoEqualEvenDiffOutsideFifthPairResidual` by the same two axioms |
| `BealTwoEqualOddOutsideRepeatedFifthResidual` | Follows from `BealTwoEqualOddOutsideFifthPairResidual` by the same two axioms |
| `BealAllDistinctOutsideCubePairResidual` | Follows from `BealAllDistinctOutsideFifthPairResidual` by the same two axioms |
| `BealPythagoreanUnequalOddOutsideCubePairResidual` | Follows from `BealPythagoreanUnequalOddOutsideFifthPairResidual` by the same two axioms |
| `BealAdmissibleBridge`, `FermatAdmissibleBridge` | Continuous bridges. Balanced seeds sit below the threshold |
| `FermatModularBridge` | Payload incompatible with real-scale admissibility |
| `FermatCoarseDiscreteBridge` | Witness empty under the coarse threshold |
| `AbcAdmissibleBridge` | False (`AbcAdmissibleBridge_false`), from the triple `1 + 8 = 9` |
| `BealCGADilationNoGo`, `BealModularBridge`, `BealWindingBridge` | Not in the tree. `Algebra/CGA` is not on the algebra barrel. `Algebra.lean` does not import `Algebra/CGA` |

## Index revision

The previous index counted 69 `sorry`s. That count mixed four different
things. The split is why twelve remain. The sections above hold the surviving
leaves and the closed theorems.

| What changed | Why it left the open-`sorry` list |
| --- | --- |
| Eight headline conjectures | The main library already proves each one from a named leaf or bridge. `Headlines.lean` applies that proof. The `sorry` stays on the leaf |
| Nineteen coarser `*Residual` props | Two are already theorems. Thirteen follow from the six Beal leaves. Three sit off that path: the even-difference factor and perfect-power packagings, and `BealMordellCubeAddTwoResidual`. `BealCGADilationNoGo` left with the conformal probe |
| Six diagnostic bridges | `BealAdmissibleBridge`, `FermatAdmissibleBridge`, `FermatCoarseDiscreteBridge`, and `FermatModularBridge` remain in the main library as diagnostic, demoted, or vacuous. `BealModularBridge` and `BealWindingBridge` left with the conformal probe. `AbcAdmissibleBridge` is false and was already absent |
| Twenty-four gravity, logic, and PGA entries | Each statement was `True`, or an existence claim whose witness does not use a library definition. They are indexed as not yet stateable |
| Mercury and the charged-pion selector | Recorded as frontiers, then proved in the main library and removed from Goals |
| Five exponent leaves | `IsSharedExpCubeOrFifth` was cut by theorems already in the main library. No new axiom. The `sorry` stays on the narrower statement |
| Hydrogen ladder, Newton–Wigner, Kerr chart, written action | Recorded as closed or refused. No new `sorry`. The Kerr window stays definition-first |
| `Algebra/CGA` | Off the algebra barrel. Do not restore those props as Goals |
| Fifth-power pairs at `11`, `13`, and `17` | `sumTwoFifthsNotStollPrime`, Stoll's unconditional range. The `sorry` stays on the narrower leaf. `(5,5,11)` and `(10,10,11)` leave the open column. Primes `p ≥ 23`, and `(7,7,11)`, stay open |
