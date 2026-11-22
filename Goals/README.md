# Goals — Lean target statements

This directory is **isolated** from the proved library under `DstDiophantine/`.
A target is a `theorem` whose statement is a `Prop` from the main library.
Policy: see [`POLICY.md`](POLICY.md).

Build: `lake build Goals` (sorry allowed). The default `lake build` does not
include this library.

## Breakthrough strategy (status vs new aims)

DST already has a sorry-free algebraic core, a shared amplification no-go, a
Schwarzschild-chart perihelion match for Mercury in `(42, 44)` arcsec/century,
and a unique charged-pion selector for one reversal scale. Those close
*consistency* and *selection* claims. They do not yet make DST derive a free
laboratory or galactic constant, nor do they close a classical Diophantine
headline without an open residual or bridge.

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
| Charged-pion reversal selector | Proved | Selects `r₁`; channel theorems still take `r₁` as input |
| Positive Beal assembly | Conditional on six leaves + FLT axiom | Closest Diophantine stack; leaves remain |
| Other classical headlines | Conditional on five live bridges | Bridges open; continuous abc bridge is false |
| Free scales `G`, `a₀`, `α`, `ℓ` | Scattering signs fix `14/15 < ℓ < 19/10` and refuse a point. `G`, `a₀`, `α`, and one value of `ℓ` stay underived | Identity breakthrough if any one of those single values is derived |
| GR solar deflection / rotating source | Not yet stateable | Observation breakthrough once definitions exist |
| Dual Hilbert lift / closed dynamics | Not yet stateable | Foundational unlocks, not near-term Goals |

### Priority targets (new aims)

Work proceeds in priority order. A row becomes a Lean `sorry` target only when
the main library already defines the `Prop`. Until then it stays
*definition-first* in the not-yet-stateable index.

| Pri | Aim | Track | Now | Next concrete step | Success criterion |
| --- | --- | --- | --- | --- | --- |
| **P0** | Derive channel length `ℓ` (or remove free `r₁`) from a scattering observable | Gravity / strong | `ScatteringScale.scatteringSignCuts_iff`: repulsion at `1/2` and attraction on `[1, 2]` are exactly `1/2 < r₁ < 1`, so `14/15 < ℓ < 19/10`, with no pion input. `scatteringSignCuts_not_unique` (`3/5` and `9/10`). `γ_s` is even in `ℓ`. The pion selector is a separate stand-in. `1/v` is still not derived | A threshold radius at one named rapidity, before any uniqueness `sorry` | One value of `ℓ` on that path, with no free channel input |
| **P0** | Derive `a₀` (or an equivalent MOND scale) from dual-image / compactification data | Gravity / galaxy | `GalaxyCurve` and `DualImage` bound dwarfs from external `a₀` and `G`; `dst_derives_a0` is refused | Define `a₀` from the source geometry (e.g. dual period / baryonic data) so flat curves are theorems without that input | A theorem that does not take `a₀` as an input and still recovers a named flat-speed window |
| **P1** | Solar light deflection in the classical GR window | Gravity / optics | `Lensing.interiorDeflection` is a thin-shell map; no solar null-ray deflection angle | Define the weak-field solar deflection angle on the exterior chart; prove a numerical window against the classical GR value | Goal closed in the main library the same way Mercury was |
| **P1** | Close one Beal leaf *without* a new external axiom | Diophantine | Six leaves open; many slices already closed by named axioms and internal lemmas | Prefer a leaf whose remaining signatures are finite or factor through existing motor / fifth-pair structure (e.g. chase `(10,10,9)`, `(5,5,11)`, or `(3,5,7)` inside the existing residual) | That leaf becomes a theorem; `Goals` deletes its `sorry` |
| **P2** | `FermatMixedMotorResidual` via the mixed-motor excess already in the library | Diophantine | Excess and odd-prime factorisation lemmas exist; classical FLT not claimed | Strengthen the motor residual until the mixed seat cannot stay admissible for `n ≥ 3` | `fermatMixedMotorResidual` proved; headline follows |
| **P2** | One live admissible bridge (Collatz / Goldbach / Polignac) | Diophantine | Finite certificates exist; infinite bridge open | Prefer Collatz: cone facts and `n ≤ 2^20` certificates are the strongest local base | Bridge theorem in the main library |
| **P3** | Closed-form DST evolution (global operator on coupled rotors) | Gravity / dynamics | `DualRotorDynamics` is the written opposite-sign EL system; no global closed product on `OmegaParams` | Name the evolution operator; only then state a Goal | Definition landed; target statement no longer “not yet stateable” |
| **P3** | Dual Hilbert lift: named D4L fragment ↦ `QProp` | Logic | Orthomodular law on `ℂ²` and island comparisons exist; the missing map is recorded | Define the map on a finite fragment before claiming subspace facts become dual-Hilbert theorems | Definition + at least one lifted island theorem |
| **Defer** | `AbcModularBridge`, `RiemannAdmissibleBridge`, electroweak masses, propellantless lab control, cold-fusion rate, Mach `m` from sources | Mixed | Live or not-yet-stateable, but either false-path risk (abc continuous), far from definitions, or not identity-critical | Do not spend identity budget here until a P0/P1 lands | Revisit only after a P0 or P1 closes |

### What this changes in the open-`sorry` list

The twelve Lean targets below stay. Priority among them for near-term work:

1. Beal leaves (P1) — furthest Diophantine stack; closing one is the amplification breakthrough.
2. `fermatMixedMotorResidual` (P2) — motor path is native to DST.
3. `collatzAdmissibleBridge` ahead of Goldbach / Polignac (P2) — strongest certificates.
4. `abcModularBridge` and `riemannAdmissibleBridge` — deferred relative to the above.

Physics P0/P1 aims are **not** yet Lean Goals. Adding a `True` placeholder is
forbidden by policy. Land the missing definition in `DstDiophantine/` first,
then add the `sorry` target in the same PR that updates this index.

## Index revision

The previous index counted 69 `sorry`s. That count mixed four different
things. They are separated as follows.

| What changed | Reason |
| --- | --- |
| Eight headline conjectures no longer have `sorry` | The main library already proves each one from a named leaf or bridge. `Headlines.lean` applies that proof. The `sorry` stays on the leaf. |
| Nineteen coarser `*Residual` props dropped | Two are already theorems (`BealPosCubeAddTwoCubeResidual_of_euler`, `BealTwoEqualEvenSumExpFiveResidual_of_NN5`). Thirteen are consequences of the six Beal leaves in the main library. The other four are not on that path: the even-difference factor and perfect-power packagings, `BealMordellCubeAddTwoResidual`, and `BealCGADilationNoGo`. |
| Six diagnostic bridges dropped | `BealAdmissibleBridge`, `BealModularBridge`, `BealWindingBridge`, `FermatAdmissibleBridge`, `FermatCoarseDiscreteBridge`, and `FermatModularBridge` are diagnostic, demoted, or vacuous in the main library. They are not research targets. `AbcAdmissibleBridge` is false (`AbcAdmissibleBridge_false`) and was already absent. |
| Twenty-four gravity, logic, and PGA entries dropped from Lean | Each statement was `True`, or an existence claim with a witness that does not use a library definition (`42 < Δ < 44`, `0 < θ`). Both elaborate without the claim they were meant to record. They are indexed below as not yet stateable. |
| Two physics frontiers added | Mercury's advance is `Perihelion.radialReturn` on external orbital elements, in arcseconds per Julian century. The charged-pion Compton length selects one sign-reversal scale in `(1/2, 1)` through `lengthOfReversal`. |
| Mercury frontier closed | `Mercury.perihelion_arcsec_bounds` in the main library proves `42 < arcsecPerCentury < 44` from `bound_return_bounds` and the external elements. Removed from Goals. |
| Charged-pion frontier closed | `SignReversal.chargedPionSelectsReversalScale` proves a unique `r₁` in `(1/2, 1)` with `lengthOfReversal r₁ = pionComptonFm`. Removed from Goals. |

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
| `BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual` | even two-equal sum, via `BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth_fifth`. Phase 7z closes a common exponent divisible by `4`. Phase 8a closes a fifth-power pair (`5` divides both equal exponents and `7` or `19` divides the hypotenuse). `(4,4,7)` and `(10,10,7)` leave this leaf; `(10,10,9)` remains |
| `BealTwoEqualEvenDiffOutsideFifthPairResidual` | even two-equal difference, via `BealTwoEqualEvenDiffResidual_of_outside_fifth`. `(7,10,10)` is a fifth-power pair |
| `BealTwoEqualOddOutsideFifthPairResidual` | odd two-equal, via `BealTwoEqualOddResidual_of_outside_fifth_pair`. `(25,25,7)` and `(5,5,21)` are fifth-power pairs; `(5,5,11)` remains |
| `BealAllDistinctOutsideFifthPairResidual` | pairwise distinct exponents, via `BealAllDistinctExpResidual_of_outside_fifth_pair`. `(5,10,7)` is a fifth-power pair; `(3,5,7)` remains |
| `BealEqualOddTwoFactorExpGeFiveResidual` | equal-odd Gaussian body, via `BealEqualOddTwoFactorResidual_of_ge_five` |
| `BealPythagoreanUnequalOddOutsideFifthPairResidual` | exponent-gcd `2` outside those slices, via `BealPythagoreanUnequalOddResidual_of_outside_fifth_pair`. `(10,10,14)` is a fifth-power pair |

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
| `SignReversal.chargedPionSelectsReversalScale` | Unique `r₁` in `(1/2, 1)` with `lengthOfReversal r₁ = pionComptonFm`. The charged-pion Compton stand-in picks one scattering scale; it does not remove `r₁` from the rest of the channel |
| `ScatteringScale.scatteringSignCuts_iff` | Repulsion at `1/2` and attraction throughout `[1, 2]` are exactly `1/2 < r₁ < 1`, hence `14/15 < lengthOfReversal r₁ < 19/10`. `scatteringSignCuts_not_unique` shows `3/5` and `9/10` both match. `gammaSEqual_even` is why the sign of `ℓ` is not chosen by the force signs |

## Not yet stateable (index only)

No definition in the main library states these claims. A `True` placeholder
is not a substitute. Rows tagged **P0** / **P1** / **P3** in the first column
are the definition-first work called out in the breakthrough strategy; untagged
rows stay deferred.

| Pri | Topic | Claim (short) | Missing definition |
| --- | --- | --- | --- |
| | Antiparticle | Standard Model fermion ↔ dual-sector phase; production and annihilation rates | Unified generation–sector identification |
| | Gravitational lensing | Null ray through the freeze chart compared with a named flare | `PhotonReturn` proves a finite Killing-time visit inside the freeze, with brackets in units of `GM/c³`. It does not claim a magnification or a flare. `Lensing` does not integrate a null ray through the freeze |
| **P3** | Dynamic equation | Full DST evolution equation in closed form | Global time-evolution operator on coupled rotors |
| | Beta decay | Mass excess as a class difference with no external input | Unsigned mass-class order |
| | De Broglie | Wave–particle bridge past the partial quantum logic | Transport–phase coupling on the exterior chart |
| **P1** | Solar light deflection | Weak-field deflection matches the classical GR angle | Deflection angle of a solar null ray. `Lensing.interiorDeflection` is the thin-shell map |
| | Rotating masses | Perihelion and lensing for a rotating source | Exterior chart of a rotating mass |
| | Interior clocks | A light signal makes the beat of two clocks the carrier's wavelength change, read against the deep-interior surplus | That identification. `InteriorClock` defines `compactness` and `centreAdvance`; the Earth figures are external rounding bins |
| | Mach | Inertial mass from surrounding sources, with stiffness `m` derived | A definition of `m` from the source sum. `MachSource` states that sources do not determine `m` |
| **P0** | Galactic rotation | Flat rotation curves for a general baryonic disk, with `a₀` derived | A theorem that does not take `a₀` as an input. `GalaxyCurve` already bounds stand-in dwarfs (for example `50.2 < v_∞ < 50.3` km/s at `4×10⁸ M_⊙`) from external `a₀` and `G`, and does not assert `dst_derives_a0` |
| **P0** | Channel length, one value | One scattering scale, past the window `14/15 < ℓ < 19/10` | A threshold radius at a named rapidity. `ScatteringScale.scatteringSignCuts_iff` already proves that repulsion at `1/2` and attraction on the whole segment `[1, 2]` are exactly `1/2 < r₁ < 1`. `scatteringSignCuts_not_unique` refuses a point: `3/5` and `9/10` both match, and they place the rapidity wall on opposite sides of `1`. `gammaSEqual_even` shows the opposite length has the same signs, so positivity of `r₁` is the choice of a separation. The charged-pion selector is not this observable. `StrongChannel` does not derive `ℓ` or the laboratory `1/v` law |
| | Neutron capture | Cross section growing as `1/v` | A cross section. `StrongChannel` states that the laboratory `1/v` law is not derived |
| | Magic-number splitting | The oscillator closures arise from the layer nodes | That derivation. The integers themselves are theorems: `oscillatorClosure` is `2, 8, 20` and `shiftedClosure` is `28, 50, 82, 126` (`NuclearLayer`) |
| | Surface pairs | Nucleon-pair forces across a touching surface, summed | That sum. The head-on distance of a `7.69` MeV alpha on gold is already in `(29, 30)` fm (`Rutherford`); no cross section is computed there |
| | Neutron skin | Speed-dependent skin and negative scattering lengths | A close-encounter amplitude |
| | Cold-fusion entrance | Entrance frequency of the octahedral seat | A frequency. `MetalFusion` proves the sign and a unique balance, and states that no rate is derived |
| | Atomic radii | Measured radii match the shell seats, past an external comparison with `n²a₀` | That identification. `ElectronNumbers` proves an order of radii in units of `ℓ` and states that `ℓ` is not derived |
| | Bohr ladder | `n²a₀` derived from the electromagnetic channel | A derivation. `bohrRadiusApprox` is an SI input. `ElectronCapacity` states that no Bohr spectrum is produced |
| | Electron exclusion | Pauli exclusion as the same layer mechanism that separates nucleons | An identification. `SpinVersusExclusion` does not provide one. Shell seats `2, 8, 18` are theorems in `ElectronCapacity` |
| | Curved transport | Photon transport matches the flat pattern and the core mismatch | An equality with the parent mismatch. `CurvedTransport` stops at the paper boundary |
| | Off-equator orbits | Inclined orbits tied to the parent torsional mismatch | An identification of the `OffEquator` constants with `Ω` |
| | Faraday control | Laboratory Weinberg angle and W/Z masses | Those quantities. `Electroweak`, `ChiralCurrent`, and `DualRotorRigidity` state that they are not derived |
| | Node clearance | Every sample stays a full step from a node | A clearance predicate beyond the first-node cap in `ShieldCeiling` |
| | Binding energy | Binding energy from the first-node clearance cap | An operator. `bindingEnergyPerNucleonMeVApprox` is an external SI label. `NuclearLength` produces no binding energy |
| | Channel walls | Finite wall height, with layer positions fixed | A derived finite height |
| **P3** | Dual Hilbert lift | Subspace facts of the ordinary layer become theorems of the dual Hilbert layer | A map from a named D4L fragment into `QProp`. `BooleanIsland` and `BlockReading` compare pairs whose two implications already agree: the expansion detaches on those pairs, and the four positive-wall rules are the classical bit rules on an island. That comparison is not the missing map. `QuantumLogic` already proves the orthomodular law on `ℂ²`. `Separation` proves that `min`/`max` is not that lattice, and `infinite_one_dim_subspaces` shows four labels do not enumerate the atoms |
| | Propellantless control | Laboratory inertia coupling by a motor whose translation commutes with torsion | A laboratory observable. `MotorGroup` proves the commuting exponential is a motor and does not claim a closed product law on `OmegaParams` |

## Not targets (recorded in the main library)

| Prop | Why it is not a Goal |
| --- | --- |
| `BealPosCubeAddTwoCubeResidual` | Theorem `BealPosCubeAddTwoCubeResidual_of_euler` |
| `BealTwoEqualEvenSumExpFiveResidual` | Theorem `BealTwoEqualEvenSumExpFiveResidual_of_NN5` |
| `BealAffineCubeAddTwoResidual` | The Euler axiom, by abbreviation |
| `BealMordellCubeAddTwoResidual` | Diagnostic Weierstrass packaging. The cube leaf is the Euler theorem, not this packaging |
| `BealCGADilationNoGo` | Legacy equal-exponent lattice. Mixed exponents miss it |
| `BealTwoEqualEvenDiffFactorResidual`, `BealTwoEqualEvenDiffPerfectPowerResidual` | Older packaging of the even-difference body. The named leaf is `BealTwoEqualEvenDiffOutsideFifthPairResidual` |
| `BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual` | Follows from `BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual` by `bennettEllenbergNg` |
| `BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual` | Follows from `BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual` by `sumTwoFifthsNotSeventhOrNineteenth` (phase 8a) |
| `BealTwoEqualEvenDiffOutsideCubePairResidual` | Follows from `BealTwoEqualEvenDiffOutsideFifthPairResidual` by the same axiom |
| `BealTwoEqualOddOutsideRepeatedFifthResidual` | Follows from `BealTwoEqualOddOutsideFifthPairResidual` by the same axiom |
| `BealAllDistinctOutsideCubePairResidual` | Follows from `BealAllDistinctOutsideFifthPairResidual` by the same axiom |
| `BealPythagoreanUnequalOddOutsideCubePairResidual` | Follows from `BealPythagoreanUnequalOddOutsideFifthPairResidual` by the same axiom |
| `BealAdmissibleBridge`, `FermatAdmissibleBridge` | Continuous bridges. Balanced seeds sit below the threshold |
| `BealModularBridge`, `FermatModularBridge` | Payload incompatible with the conformal gauge, independently of a solution in the Beal case |
| `BealWindingBridge` | Window regime only |
| `FermatCoarseDiscreteBridge` | Witness empty under the coarse threshold. Not a research target |
| `AbcAdmissibleBridge` | False (`AbcAdmissibleBridge_false`), from the triple `1 + 8 = 9` |

The positive-wall cut is a theorem of the main library (`Logic.WallRule`), not a Goal. For a finite set of premises, forcing on the interval depends only on the atoms that occur, and it splits into classical consequence and the balance case. Discharge agrees with classical consequence on the walls at every finite depth. Synchrony, non-refutation, and positive-wall forcing are pairwise incomparable. None of this discharges the twelve leaves above, and `U → T = U` still refuses a promotion from an open bridge to `T`.

## Proved headline results (main library only — no Goals entry)

Examples already sorry-free in `DstDiophantine/`: admissible bound
`|J_norm| ≤ 1`, PGA motor algebra, Schwarzschild exterior leading perihelion
coefficient, Mercury arcseconds per Julian century in `(42, 44)`, unique
charged-pion reversal scale in `(1/2, 1)`, sign-reversal window for ℓ,
Coulomb from the dual channel, partial metal-fusion sign lemmas, Collatz
certificate up to `2^20`. These are not duplicated as Goals. A sharper
observational match stays in the not-yet-stateable index until the missing
definition exists.
