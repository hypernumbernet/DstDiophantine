# Mismatch angle (relative rotor programme)

Lean path: `DstDiophantine/Algebra/MismatchAngle.lean` (main, sorry-free).
Gravity bridge: `DstDiophantine/Gravity/MismatchAngleBridge.lean`.
Discrete lattice bridge: `DstDiophantine/Framework/MismatchLattice.lean`.
Axis overlap: `DstDiophantine/Algebra/PgaAxisMotor.lean` (`cliffordProductGradeZero`).
Open general branch: `Goals/Diophantine/MismatchAngle.lean` only (off-axis principal branch).

## Author decision (this branch only — do not merge)

**Primary overlap** (repulsion, mismatch headlines):

\[
\texttt{axisOverlapScalar}(\alpha,\beta) = \cosh(\alpha/2)\,\cos(\beta/2)
\]

This is the natural Clifford grade-0 scalar of \(\Omega = R_{\mathrm{usual}}^\dagger R_{\mathrm{dual}}\) on
the commuting one-axis family (`PgaAxisMotor.cliffordProductGradeZero`, no separate “designated chart”
alias). Rotation zero occurs when \(\cos(\beta/2)=0\) ⇔ **rotation mismatch \(\beta=\pi\)** (half-angle \(\pi/2\)),
independently of boost; \(\cosh(\alpha/2)\) scales magnitude with boost.

**Legacy overlap** (unchanged numerics in shell / nuclear charts):

\[
\texttt{axisOverlapLegacy}(\alpha,\beta) = \texttt{gammaS}(\alpha,\beta)
  = \cosh(\alpha/2)\cos(\beta/2) - \sinh(\alpha/2)\sin(\beta/2)
\]

`ElectronShell.gammaS`, `TorsionalLayer.gammaSEqual`, nodes \(\tanh\tan=1\),
`resonanceRoot1`, `StrongChannel.phiStar`, `HydrogenRepulsion`, etc. still use **legacy** factors;
main theorems remain sorry-free without silently rewriting those numbers.

### Primary vs legacy — what changes for physics statements

| Topic | Legacy chart (unchanged numbers) | Primary chart (new repulsion / mismatch) |
|-------|-----------------------------------|------------------------------------------|
| Overlap definition | `gammaS` / `axisOverlapLegacy` | `axisOverlapScalar` = grade-0 of \(\Omega\) |
| Zero overlap (equal \(\alpha=\beta\) on axis) | `gammaSEqual(π/2)=0` at \(\alpha=\beta=\pi\) (mixed node) | `axisOverlapScalar α π = 0` for any \(\alpha\); balanced zero at \(\cos(\theta/2)=0\) |
| Sign reversal / “repulsion flip” | Negative overlap at legacy equal-scale node; `gammaSEqual` crosses zero on shell nodes | Overlap **non-negative** on admissible cone with \(\beta\le\pi/2\); reversal only at \(\beta=\pi\) (`axisOverlap_eq_zero_iff`) |
| Pure boost \(\beta=0\) | `gammaS(α,0)=\cosh(\alpha/2)` | Same (`axisOverlap_primary_eq_gammaS_usual` / dual) |
| Graviton step interference | `gammaS` lemmas unchanged | `graviton_*_overlap_*` uses primary; legacy balanced via `graviton_legacy_balanced_overlap` |
| \(J=0\) vs overlap at \(\pi,\pi\) | Legacy overlap \(<0\) while \(J=0\) (`ConeLabels.regime_label_not_overlap_sign`) | Primary overlap \(=0\) **and** legacy \(<0\) (decoupling sharpened) |
| Lattice winding | (bookkeeping) | `windingRotationTotal` on dual \(m\) coords; rotation at scale: `mismatch_rotation_winding_at_scale` |
| Pure-boost winding | Winding on boost leg | Rotation winding \(=0\) (`winding_pureBoost_decomposition`); does not enter rotation mismatch |

### Results that **do not** move (legacy chain intact)

- Shell node positions from \(\tanh(\alpha/2)\tan(\beta/2)=1\) and `resonanceRoot1` / `branchNode` calculus.
- `gammaSEqual` spectrum, equal-scale plateau (`gammaSEqual_nat_mul_pi`), and electron/nuclear lemmas citing `gammaSEqual`.
- Sign-reversal **scale** windows stated through legacy `gammaS` / `gammaSEqual` (e.g. StrongChannel, ScatteringScale).

### Results that **do** move (primary repulsion programme)

- Repulsion overlap sign and magnitude: `Gravity/RepulsionOverlap.lean` (primary); legacy witnesses kept for comparison.
- Graviton admissibility at \(2\pi\): primary overlap at balanced \(2\pi\) is **not** zero (only \(\beta=\pi\) kills primary); legacy remains negative at \(2\pi\) (`graviton_primary_overlap_zero_at_rotation_pi`).
- Cone / regime narrative: overlap decoupled from \(J\) uses primary \(=0\) + legacy \(<0\) at \(\pi,\pi\).

## Definition (one-axis family)

Usual and dual rotors factor on `axisParams α β` because `B⁺₀` and `B⁻₀` commute:

- `Ω = R_usual† R_dual = exp(ω)` with
  `ω = mismatchBoostHalf • B⁺₀ + mismatchRotationHalf • B⁻₀`
- `mismatchBoostHalf α β = −α/2` (unbounded boost leg)
- `mismatchRotationHalf α β = β/2` (compact rotation leg; periodic under `β ↦ β + 2π`)

**Repulsion is overlap-first (primary):** `Gravity/RepulsionOverlap.lean`. Legacy `J` is a derived diagnostic:

`J = 2 · (Σ mismatchBoostHalf² − Σ mismatchRotationHalf²)` (`J_eq_mismatch_half_sq_diff`).

## Proven properties (main library)

| Property | Lean name |
|----------|-----------|
| Global `J` from half-square sums | `J_eq_mismatch_half_sq_diff`, `J_eq_zero_iff_mismatch_sq_balance` |
| Primary overlap ↔ \(\cos(\beta/2)\) | `axisOverlap_eq_zero_iff`, `axisOverlap_nonneg_iff`, `axisOverlap_admissible_nonneg` |
| Legacy = `gammaS` | `axisOverlapLegacy_eq_gammaS`, `MismatchAngleBridge.axisOverlap_eq_gammaSEqual_balanced` |
| Primary = `gammaS` when one leg zero | `axisOverlap_primary_eq_gammaS_usual`, `axisOverlap_primary_eq_gammaS_dual` |
| Grade-0 from Clifford product | `PgaAxisMotor.cliffordProductGradeZero_eq_axis_overlap` |
| Sign reversal threshold | `axisOverlap_sign_reversal_threshold`, `primary_overlap_zero_legacy_neg_witness` |
| Repulsion cone (one direction) | `RepulsionCone.admissibleContinuous_implies_mismatch_half_box`, … |
| Lattice winding (rotation leg) | `MismatchLattice.windingRotationTotal`, `winding_pureBoost_decomposition`, `mismatch_rotation_winding_at_scale` |
| Graviton primary vs legacy | `graviton_primary_*`, `graviton_legacy_*`, `graviton_primary_overlap_zero_at_rotation_pi` |

**Open (Goals, sorry allowed — 13 total):**

- `Goals.Diophantine.omegaMismatch_off_axis_principal_branch` — general six-parameter log of `Ω`.
- Winding on the rotation leg is **closed in main** (not a Goal).

## Primary vs legacy — numerical scan (Nov 2025)

Phase \(x\) is the equal-scale chart argument; radius in units of \(\ell\) is \(r/\ell = 1/(2x)\) via `layerRadius`.
`squareBalance(x) = γ(\sqrt2·x) − 2\sqrt2·γ(x)` with primary \(\gamma = \cosh\cos\); legacy uses `squareBalanceLegacy`.

### Primary `squareBalance` — sign in the well vs zero elsewhere

| Interval / observation | Primary | Legacy (for comparison) |
|------------------------|---------|-------------------------|
| \((3/2,\,8/5)\) covalent well | **No sign change** — stays \(\approx -2.7\) … \(-3.3\) (negative throughout) | Unique zero \(\approx 1.5547\), \(r/\ell \approx 0.3216\) |
| \([0,\,2\pi]\) zero of `squareBalance` | **Yes** at \(x \approx 2.6346\), \(r/\ell \approx 0.1898\) | (well zero as above; additional nodes differ) |
| \(x \approx 5.4155\) (first shell after \(2\pi\)) | **Yes** (balance \(\approx 0\)), \(r/\ell \approx 0.0923\) | not tabulated here |
| \(x \approx 7.781\), \(10.023\), \(12.230\) | Further primary zeros (late odd/even branches) | — |

**Research / theorem status:** existence of a **primary** square shell in \((3/2,8/5)\) is **not** supported (no crossing).
Main library proves **`exists_unique_square_shell` via `squareBalanceLegacy`** on `(3/2,33/20)` with documented research gap for primary.
A **clean primary zero at \(\approx 2.635\)** suggests a **late-branch** shell programme (research: primary shell existence theorem not closed in main).

### Primary electron–proton balance (`forceCrit`, `pairAttraction`)

| Quantity | Location | Value (4 d.p.) | \(r/\ell\) |
|----------|----------|----------------|------------|
| `forceCrit x = 0` (quiet point) | \(x \in (5/2,\,\pi)\) | \(x \approx 2.7984\) | \(\approx 0.1787\) |
| `pairAttraction(5/2)` | quiet band anchor | \(\approx -5.0887\) | \(\approx 0.2000\) |
| Primary \(\gamma(5/2)\) | | \(\approx -4.9128\) | |

### Nuclear selector — `resonanceRoot1 = π/2`

| Chart | \(\gamma(\pi/2)\) | Comment |
|-------|-------------------|---------|
| **Primary** `gammaSEqual` | \(\approx 0\) (\(\cos\) node) | `resonanceRoot1_gammaSEqual_zero` |
| **Legacy** `gammaSEqualLegacy` | \(\approx -2.3013\) | old mixed overlap at same phase |

14 MeV skin uses **legacy** rapidity (\(cosh\phi = 1 + 14/939.565\), \(\phi \approx 0.1724\)); primary vs legacy \(\gamma\) at comparable small phases differ by \(\mathcal{O}(\sinh\sin)\) (e.g. at \(x=0.9\): primary \(\approx 0.891\), legacy \(\approx 0.087\)).

## CI

- `lake build DstDiophantine` — required green
- `scripts/check_main_library.sh` — no `sorry`, allowlisted axioms only
- `lake build Goals` — **13** open sorries (`scripts/count_goals.sh`)