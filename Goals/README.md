# Goals — Lean target statements

This directory is **isolated** from the proved library under `DstDiophantine/`.
Each target is a `theorem` with `sorry`, a bilingual docstring (where shown
below), a paper pointer, and status. Policy: see [`POLICY.md`](POLICY.md).

Build: `lake build Goals` (sorry allowed). The default `lake build` does not
include this library.

## Not yet stateable (index only)

| Topic | Claim (short) | Missing definition |
| --- | --- | --- |
| Antiparticle | Standard Model fermion ↔ dual-sector phase; production/annihilation rates | Unified generation–sector identification in Lean |
| Gravitational lensing | Null ray through freeze chart; photon-return timing vs I Zwicky 1 flares | Integrated null geodesic in the torsion star chart |
| Dynamic equation | Full DST evolution equation closed form | Global time evolution operator on coupled rotors |
| Beta decay | Mass excess as class difference without input | Unsigned mass class ordering axiom-free |
| De Broglie | Full wave–particle bridge beyond partial quantum logic | Completed transport–phase coupling in exterior chart |

## Diophantine / number-theoretic core

| Target module | Count | Notes |
| --- | ---: | --- |
| `Diophantine/Headlines.lean` | 8 | Classical conjectures (Beal, FLT, abc, Collatz, Goldbach, Polignac, twin, RH) |
| `Diophantine/Residuals.lean` | 26 | Live `*Residual` leaves (Beal programme + Fermat motor) |
| `Diophantine/Bridges.lean` | 11 | `*Bridge` hypotheses (several diagnostic-only in main lib) |

Headline claims map to `papers/dst-diophantine.tex`. Many residuals already
have **partial** closures in the main library (Bruin/Dahmen–Siksek slices,
even two-equal progress); targets here are the unconditional `Prop` definitions.

## PGA G(3,1,1) motor / translator

| Target | Paper |
| --- | --- |
| `PGA/TranslationMotor.lean` (1) | `papers/dst-pga.tex`, `papers/double-spacetime-theory.tex` |

## Teleparallel scalar, Schwarzschild exterior, tests

| Target module | Count | Paper / site |
| --- | ---: | --- |
| `Gravity/SchwarzschildExterior.lean` | 4 | `papers/double-spacetime-theory.tex`, site `gravity.html` |

## Mach's principle

| Target module | Count | Paper |
| --- | ---: | --- |
| `Gravity/MachPrinciple.lean` | 1 | `papers/double-spacetime-theory.tex` |

## Galactic rotation

| Target module | Count | Paper |
| --- | ---: | --- |
| `Gravity/GalacticRotation.lean` | 1 | `papers/dst-galactic-rotation.tex` |

## Strong interaction / nuclear layers

| Target module | Count | Paper / site |
| --- | ---: | --- |
| `Gravity/NuclearStrong.lean` | 7 | `papers/dst-strong-interaction.tex`, `papers/dst-cold-fusion.tex`, site `layers.html` |

Open items include scattering-derived ℓ, magic numbers as seat counts, 1/v
capture, cold-fusion entrance, and neutron skin amplitudes (すべて
**現在研究中** in the site).

## Electron shell

| Target module | Count | Paper / site |
| --- | ---: | --- |
| `Gravity/ElectronShell.lean` | 3 | `papers/dst-electron-shell.tex`, site `layers.html` |

## Transport, off-equator, Faraday control

| Target module | Count | Site |
| --- | ---: | --- |
| `Gravity/TransportControl.lean` | 3 | `transport.html`, `control.html` |

## Renormalization / layer geometry

| Target module | Count | Site |
| --- | ---: | --- |
| `Gravity/RenormalizationLayers.lean` | 3 | `renormalization.html` |

## Four-valued logic / dual Hilbert layer

| Target module | Count | Paper |
| --- | ---: | --- |
| `Logic/DualHilbert.lean` | 1 | `papers/dst-4-valued-logic.tex` |

## Topic totals (open `sorry` targets)

| Topic | Targets |
| --- | ---: |
| Diophantine headlines | 8 |
| Diophantine residuals | 26 |
| Diophantine bridges | 11 |
| PGA | 1 |
| Schwarzschild / solar tests | 4 |
| Mach | 1 |
| Galactic rotation | 1 |
| Nuclear / strong | 7 |
| Electron shell | 3 |
| Transport / control | 3 |
| Renormalization | 3 |
| Logic (D4L) | 1 |
| **Total stateable targets** | **69** (`scripts/count_goals.sh`) |

*(Run `bash scripts/count_goals.sh` after edits — the script counts `sorry`
occurrences.)*

## Proved headline results (main library only — no Goals entry)

Examples already sorry-free in `DstDiophantine/`: admissible bound
`|J_norm| ≤ 1`, PGA motor algebra, Schwarzschild exterior leading perihelion
coefficient, sign-reversal window for ℓ, Coulomb from dual channel, partial
metal-fusion sign lemmas, Collatz certificate up to `2^20`, etc. These are
not duplicated as Goals unless a **sharper** observational matching statement
is still open (see Schwarzschild rows above).