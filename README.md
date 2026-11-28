# DoubleSpacetime

The repository was founded to prove classical number theory in Lean 4, as
an amplification programme for Diophantine conjectures. Its machine-checked
core is an algebraic bound, a motor calculus, and a shared amplification
no-go. That core turned out to be useful in physics as well, and is
developed there as **Double Spacetime Theory** (DST). The work now proceeds
in both directions, mathematics and physics.

Unconditional Fermat, Beal, abc, the Riemann Hypothesis, Goldbach,
Polignac, and Collatz remain open. Open work is named as a residual or a
`*Bridge` proposition. Twelve classical theorems that mathlib does not
supply at this pin are explicit `axiom`s. The main library has no `sorry`.
Open targets that still use `sorry` live in [`Goals/`](Goals/), which the
main library does not import.

Where a paper draft and the Lean development disagree, the Lean development
is the record. A paper title is the title of that source. Checked local
boundaries live in the module docstrings. This file is the map.

Entry point for the Diophantine path:
[`DoubleSpacetime/Basic.lean`](DoubleSpacetime/Basic.lean)
(`import DoubleSpacetime.Basic`). Gravity and four-valued logic are parallel
tracks. Their barrels are not re-exported from `Basic`. The root
[`DoubleSpacetime.lean`](DoubleSpacetime.lean) imports `Basic` and `Gravity`
together.

## Double Spacetime Theory

DST refuses a single shared spacetime continuum. Each massive particle
carries its own pair of Minkowski structures inside the
16-real-dimensional biquaternion algebra
$\mathbb{H} \otimes_{\mathbb{R}} \mathbb{H} \cong \mathrm{Cl}(3,1)$
(not the eight-dimensional direct sum $\mathbb{H}\oplus\mathbb{H}$):

- **usual** spacetime, basis $(j, kI, kJ, kK)$, hyperbolic and not compact
- **dual** spacetime, basis $(k, jI, jJ, jK)$, compact

The dual map reverses the arrow of time and preserves the Minkowski norm.
Lorentz transformations are rotors on each sector. Gravity and inertia are
the **torsional mismatch**

$$
\Omega = R_{\mathrm{usual}}^{\dagger}\, R_{\mathrm{dual}},
\qquad
J = \tfrac12\sum_{a=1}^{3}(\alpha_a^2 - \beta_a^2).
$$

$J$ is dimensionless. Its mass partner is
$M = \tfrac12\sum_a(\alpha_a^2 + \beta_a^2)$. The normalised height is
$J_{\mathrm{norm}} = J / (3\pi^2/8)$, so $|J_{\mathrm{norm}}| \le 1$ is
the same statement as $|J| \le 3\pi^2/8$. Vanishing $J$ does not force
$\Omega = 1$: there is a balanced massive seed with $J = 0$, $M > 0$, and
$\Omega \ne 1$.

Translation comes from projective geometric algebra $G(3,1,1)$: one null
vector, ten bivector generators, and motors $M = RT$. The ten bivectors are
the Poincaré algebra under the commutator. The ordered product equals the
Banach exponential when torsion and translation commute, and there are
motors for which the two disagree. They share a 3-jet with the third-order
Baker–Campbell–Hausdorff exponential.

Physics: [`papers/double-spacetime-theory.tex`](papers/double-spacetime-theory.tex).
Motors and the direction of gravity:
[`papers/dst-pga.tex`](papers/dst-pga.tex).

## Tracks

| Import | Gets |
| --- | --- |
| `DoubleSpacetime.Basic` | Diophantine path: algebra, integer embedding, amplification, problem layers |
| `DoubleSpacetime.Algebra` | Algebra only. Gravity and logic stay out |
| `DoubleSpacetime.Gravity` | Chart, scales, dual-rotor dynamics, signed force, Faraday, control |
| `DoubleSpacetime.Logic` | Four-valued logic (D4L) and the dual Hilbert layer |

`Theorems.BealRegime` is compiled through
[`FoundationRegression.lean`](DoubleSpacetime/FoundationRegression.lean)
and is not re-exported from `Basic`. A `.U → .T` edit of an atlas atom
belongs in `Logic.Example.BealRegime` and does not promote classical Beal.

## Algebraic core

Proved in [`DoubleSpacetime/Algebra.lean`](DoubleSpacetime/Algebra.lean) and
[`papers/discrete-dual-spacetime.tex`](papers/discrete-dual-spacetime.tex).

- Duality is a complex structure on the Lorentz sector: every boost is the
  dual of a rotation, and duality reverses $J$ while preserving $M$.
- A null translator truncates,
  $\exp(\Omega_{\mathrm{trans}}) = 1 + \Omega_{\mathrm{trans}}$, and
  translators multiply by adding coefficients. Sandwich conjugation sends
  translators to translators. A pure boost scales the null coefficients
  diagonally.
- The admissible cone is nonnegative rapidities with
  $\alpha_a + \beta_a \le \pi/2$ on each axis, and
  $|J_{\mathrm{norm}}| \le 1$ on that cone. The bound is sharp.
- Cyclic exponentials are $2\pi$-periodic. Hyperbolic exponentials are not.
  Putting boosts on a $2\pi$-torus is a modelling choice. Admissibility is
  a further hypothesis, not a consequence of discretising the torus.
- The torsion-rotor image of $(\mathbb{Z}/N\mathbb{Z})^6$ is finite. It
  factorises on one axis, and it is not a product of three one-axis images.

The amplification no-go is in
[`Framework/Amplification.lean`](DoubleSpacetime/Framework/Amplification.lean).
A seed that amplifies past the admissible ceiling cannot exist. The
argument does not depend on which equation produced the seed.

## Diophantine programme

Integers embed into PGA motors by rotors and null translators. A power-sum
relation becomes `powerSumMotor = 1`. Dual-spacetime rapidities are
discretised to $(\mathbb{Z}/N\mathbb{Z})^6$, so each problem is a search
over an admissible lattice. Sources:
[`DoubleSpacetime/Framework/`](DoubleSpacetime/Framework/) and
[`papers/dst-diophantine.tex`](papers/dst-diophantine.tex).

| Layer | Content | Status |
| --- | --- | --- |
| 1. Faithful encoding | Additive relations as null-translator motors | Proved |
| 2. Amplification no-go | No seed amplifies past the admissible ceiling | Proved |
| 3. Bridge or residual | A classical solution would produce such a witness, or a named leaf after a closed case split | Open |

The proof challenge is layer 3. Diagnostic bridges are recorded so they
can be told apart from the live route. `FermatAdmissibleBridge`,
`FermatModularBridge`, and `BealAdmissibleBridge` are diagnostic.
`AbcAdmissibleBridge` is false: $(1,8,9)$ has quality greater than $1$
and an admissible mismatch. PGA integer-rotor height is not globally
bounded.

### Live status

| Conjecture | Live layer | Status |
| --- | --- | --- |
| Fermat | [`FermatMixed.lean`](DoubleSpacetime/Theorems/FermatMixed.lean), [`FermatMotor.lean`](DoubleSpacetime/Embedding/FermatMotor.lean) | Dual-axis motor: boost $\alpha = \log(\sqrt{a^2+b^2}/\|c\|)$ on axis 0, cyclic angle $\beta = \arctan(\|b\|/\|a\|)$ on axis 1. Degree $2$ is pure cyclic. For $n \ge 3$ every positive solution is mixed. On a positive integer solution the excess $a^2+b^2-c^2$ is a positive integer, and the boost is at least $\tfrac12\log(1+1/c^2)$. An odd prime exponent dividing none of three coprime positive bases factorises the third base, and those pure powers rebuild the bases. Excess `1` makes the boost lower bound meet the polar radial factor. The full residual follows from `FermatMixedMotorOddPrimeResidual`. The open face is an odd prime `n ≥ 5`. Exponents divisible by `3` or by `4` are mathlib. Classical Fermat is not claimed, and this route does not assume `fermatLastTheorem`. |
| Beal | [`Beal.lean`](DoubleSpacetime/Theorems/Beal.lean) and the slice files | Furthest along. `beal_conjecture_pos_of_fine_residuals_even_split` reduces positive Beal to the FLT axiom and six residuals. Classical Beal remains open. |
| abc | [`Abc.lean`](DoubleSpacetime/Theorems/Abc.lean) | The continuous bridge is false. The live statement is `AbcModularBridge`. |
| Riemann | [`Riemann.lean`](DoubleSpacetime/Theorems/Riemann.lean) | `RiemannAdmissibleBridge`, with rational-grid certificates of denominator $\le 20$. This is not mathlib's `riemannZeta`. |
| Goldbach | [`Goldbach.lean`](DoubleSpacetime/Theorems/Goldbach.lean) | `GoldbachAdmissibleBridge`. Even targets $4 \le n \le 100$ are certified. The integer height of a target does not depend on a prime pair. |
| Polignac | [`Polignac.lean`](DoubleSpacetime/Theorems/Polignac.lean) | `PolignacAdmissibleBridge`. The gap $2k$ lies on the phase iff $k = 1$. Twin pairs have an admissible relative rotor. The normalised mismatch falls under every positive tolerance. |
| Collatz | [`Collatz.lean`](DoubleSpacetime/Theorems/Collatz.lean) | `CollatzAdmissibleBridge`. The admissible integer-boost cone contains only $1$ and $2$. Every start $n \le 2^{20}$ reaches $1$. Any other cycle has normalised height greater than $100$. |

Goldbach and Polignac share one phase, the hyperbola
$(n/2)^2 - k^2 = pq$
([`AdditivePhase.lean`](DoubleSpacetime/Theorems/AdditivePhase.lean)).
Neither conjecture is claimed there.

### Beal frontier

Positive classical Beal follows from `fermatLastTheorem` together with six
residuals. The slices below are closed. What remains is the leaf column.
Finite coprime-free boxes in
[`BealFinite.lean`](DoubleSpacetime/Theorems/BealFinite.lean) do not close
an infinite leaf. Window winding produces a modular witness from a
fractional gap in $[2\pi/k, 4\pi/k)$. The balanced regime sits below that
window, so winding does not close it.

| Closed | By |
| --- | --- |
| Exponent gcd $d \ge 3$ | `fermatLastTheorem`. If $3 \mid d$ or $4 \mid d$, mathlib's Fermat theorems for exponents $3$ and $4$ close the slice with no extra axiom |
| Positive unit base | `mihailescu` |
| Two-equal cubes, and a shared exponent $n \ge 4$ whose third exponent is a multiple of $3$ | `darmonMerelCube` |
| Even-sum slice at hypotenuse exponent $5$, and a shared exponent whose third exponent is a multiple of $5$ | `fermatSignatureNN5` |
| Gaussian leaf $\alpha^3 + 2\beta^3 = \gamma^3$ | `eulerAffineCubeAddTwo` |
| Coprime sum of two cubes equal to an $n$th power, for $3 \le n \le 10^9$, every even $n \ge 4$, and every multiple of such an exponent, together with every cube-pair shape of that form. $(3,3,10^9+1)$ is this closure because $7$ divides the hypotenuse. A prime exponent past $10^9$ is not this closure | `sumTwoCubesNotPerfectPower` |
| Coprime sum of two cubes equal to a prime power $p \ge 17$ with $p \equiv 2 \pmod 3$, and every exponent divisible by such a prime, on a cube-pair seat. A prime past $10^9$ with $p \equiv 1 \pmod 3$ stays open | `freitasSumTwoCubesPrime` |
| Signature $(3,4,5)$ in every order | `siksekStoll345` |
| A repeated five beside $7$ or $19$, and two exponents divisible by $5$ with the third divisible by $7$ or $19$ | `sumTwoFifthsNotSeventhOrNineteenth` |
| Two exponents divisible by $5$, the third by $11$, $13$, or $17$ | `sumTwoFifthsNotStollPrime`. Stoll's chapter removes the GRH hypothesis for these three primes. Primes $p \ge 23$ stay conditional there and are not axioms. $(7,7,11)$ is not this statement |
| Even two-equal sum whose common exponent is divisible by $4$, hypotenuse at least $4$ | `bennettEllenbergNg` |
| Equal exponents $2\ell$ and $2m$, with primes $\ell,m\ge 5$, and hypotenuse divisible by $7$, $11$, or $13$ | `anniSiksekDoublePrimeSum`. Anni–Siksek for $7$ and $11$; Billerey–Chen–Dembélé–Dieulefait–Freitas remove the $\ell,m\neq 7$ exception at $13$. $(22,22,7)$ is this shape |
| Equal exponents $2\ell$ and $2m$, with primes $\ell,m\neq 5$, and hypotenuse divisible by $17$ | `michaudJacobsPrimeSeventeenth`. The case $\ell=m=5$ stays with `sumTwoFifthsNotStollPrime`. $(14,14,17)$ is this shape |
| Pythagorean slice in which $4$ divides at least two reduced exponents | Internal, from coprime Pythagorean triples |

| Live leaf | Still open |
| --- | --- |
| `BealEqualOddTwoFactorExpGeFiveResidual` | Odd Gaussian exponent $e \ge 5$. The case $e = 3$ is the Euler leaf |
| `BealTwoEqualEvenSumExpGeSevenOutsideAnniSeventeenthResidual` | Even common exponent, hypotenuse $z \ge 7$, outside the closed shapes. $(10,10,23)$ and $(14,14,19)$ remain. $(22,22,7)$ is an Anni–Siksek even sum |
| `BealTwoEqualEvenDiffOutsideFifthPairResidual` | Even-difference two-equal body outside the closed shapes |
| `BealTwoEqualOddOutsideFifthPairResidual` | Odd two-equal body outside the closed shapes. $(5,5,23)$ and $(7,7,11)$ remain. $(5,5,11)$ is a fifth-power pair. A prime hypotenuse past $10^9$ with $p \equiv 2 \pmod 3$ is Freitas; $p \equiv 1 \pmod 3$ stays |
| `BealAllDistinctOutsideFifthPairResidual` | Pairwise distinct exponents outside the closed shapes. $(3,5,7)$ remains |
| `BealPythagoreanUnequalOddOutsideAnniSeventeenthResidual` | Exponent gcd $2$, at least two reduced exponents odd, outside the closed shapes. $(22,22,14)$ is an Anni–Siksek even sum |

### Explicit axioms

mathlib at this pin (`v4.35.0`) does not contain these theorems. Each one
is an `axiom` in `Theorems/`, used by the Beal reduction. None of them is
a Lean proof of the cited theorem, and none of them is the live Fermat
route.

| Declaration | File | Statement used here |
| --- | --- | --- |
| `fermatLastTheorem` | [`FermatLast.lean`](DoubleSpacetime/Theorems/FermatLast.lean) | Wiles. Closes Beal exponent gcd $d \ge 3$ |
| `mihailescu` | [`Mihailescu.lean`](DoubleSpacetime/Theorems/Mihailescu.lean) | The only perfect-power difference of $1$ with exponents greater than $1$ is $3^2 - 2^3 = 1$ |
| `darmonMerelCube` | [`DarmonMerel.lean`](DoubleSpacetime/Theorems/DarmonMerel.lean) | No coprime nonzero solution of $a^n + b^n = c^3$ for $n \ge 4$ |
| `fermatSignatureNN5` | [`FermatNN5.lean`](DoubleSpacetime/Theorems/FermatNN5.lean) | No coprime nonzero solution of $a^n + b^n = c^5$ for $n \ge 4$ |
| `eulerAffineCubeAddTwo` | [`EulerCube.lean`](DoubleSpacetime/Theorems/EulerCube.lean) | The only rational points of $X^3 + 2Y^3 = 1$ are $(1,0)$ and $(-1,1)$ |
| `sumTwoCubesNotPerfectPower` | [`Bruin.lean`](DoubleSpacetime/Theorems/Bruin.lean) | No coprime nonzero solution of $a^3 + b^3 = c^n$ in the range above |
| `freitasSumTwoCubesPrime` | [`Bruin.lean`](DoubleSpacetime/Theorems/Bruin.lean) | No coprime nonzero solution of $a^3 + b^3 = c^p$ for a prime $p \ge 17$ with $p \equiv 2 \pmod 3$ |
| `siksekStoll345` | [`SiksekStoll.lean`](DoubleSpacetime/Theorems/SiksekStoll.lean) | Every coprime integer solution of $x^3 + y^4 + z^5 = 0$ has a vanishing coordinate |
| `sumTwoFifthsNotSeventhOrNineteenth` | [`DahmenSiksek.lean`](DoubleSpacetime/Theorems/DahmenSiksek.lean) | No coprime nonzero solution of $a^5 + b^5 = c^l$ for $l = 7$ or $l = 19$ |
| `sumTwoFifthsNotStollPrime` | [`DahmenSiksek.lean`](DoubleSpacetime/Theorems/DahmenSiksek.lean) | No coprime nonzero solution of $a^5 + b^5 = c^l$ for $l = 11$, $13$, or $17$ |
| `bennettEllenbergNg` | [`BennettEllenbergNg.lean`](DoubleSpacetime/Theorems/BennettEllenbergNg.lean) | No coprime nonzero solution of $A^4 + B^2 = C^n$ for $n \ge 4$ |
| `anniSiksekDoublePrimeSum` | [`AnniSiksek.lean`](DoubleSpacetime/Theorems/AnniSiksek.lean) | No coprime nonzero solution of $a^{2\ell}+b^{2m}=c^p$ for primes $\ell,m\ge 5$ and $p\in\{7,11,13\}$ |
| `michaudJacobsPrimeSeventeenth` | [`AnniSiksek.lean`](DoubleSpacetime/Theorems/AnniSiksek.lean) | No coprime nonzero solution of $a^{2\ell}+b^{2m}=c^{17}$ for primes $\ell,m\neq 5$ |

### Finite certificates

`native_decide` searches. Each certificate is exhaustive inside its box
and says nothing about the complement.

| Search | Bound |
| --- | --- |
| Beal, coprime perfect powers | Bases $\le 24$, exponents $3,\ldots,8$ |
| Beal, open-residual filter | Bases $\le 80$, exponents $3,\ldots,7$ |
| Primitive kernel $\alpha^3 + 2\beta^3 = \gamma^3$ | $\alpha,\beta \le 400$ |
| abc | $c \le \mathrm{rad}(abc)^2$ for primitive triples with $c \le 100$; $c \le 2\,\mathrm{rad}(abc)$ for $c \le 80$. The triples $(1,80,81)$ and $(3,125,128)$ lie outside the admissible cone |
| Goldbach | Even sums $4 \le n \le 100$ |
| Polignac | Gap $2k$ on the phase iff $k = 1$; $(3,7)$ outside the cone, $(7,11)$ inside |
| Collatz | Every $n \le 2^{20}$ reaches $1$ |
| Riemann rational grid | Denominator $\le 20$ |

## Gravity

Parallel track, barrel [`DoubleSpacetime/Gravity.lean`](DoubleSpacetime/Gravity.lean).
The module docstring there is the index. Each submodule docstring is the
checked local map. Regression examples live in
[`Gravity/Regression.lean`](DoubleSpacetime/Gravity/Regression.lean) and
add no claim. Algebraic $J$ is not the Weitzenböck density $T$ and not a
dimensionful coupling.

### Chart and checked windows

On the diagonal radial coframe the vacuum condition freezes the
teleparallel quadratic at the flat spherical value $-2/r^2$ and selects
$A = 1 - r_s/r$. The same value of $J$ does not determine $T$. The static
Killing field is a pure boost about an axis displaced inward by $\ell$.
A body released from rest accelerates toward that axis. On the exterior
the powers of the speed cancel and $d^2 r/d\tau^2 = -r_s/(2r^2)$. One
integration recovers $(dr/d\tau)^2 = E^2 - A$.

Two classical windows are proved from external elements, and they do not
derive $G$:

- Mercury's exterior radial return lies in $(42, 44)$ arcseconds per
  Julian century (`Mercury`).
- An exterior null ray that turns at the nominal solar radius has
  azimuthal excess in $(17/10, 9/5)$ arcseconds (`SolarDeflection`).
  No eclipse residual is claimed. This is not `Lensing.interiorDeflection`.

A ray below the photon-sphere value has no turning point on the classical
exterior. On either recorded admissible ceiling the same ray turns inside
the freeze and returns (`PhotonReturn`).

### Scales that stay inputs

`SI` holds external rational stand-ins. Comparing $c$ with $G$ does not
derive $G$. The admissible ceiling, read as a redshift floor, does not
form a one-way horizon $A = 0$ on that chart.

Scattering signs fix a window and refuse a point. Repulsion at $1/2$ and
attraction on $[1, 2]$ are exactly $1/2 < r_1 < 1$, so
$14/15 < \ell < 19/10$. Every radius whose phase ignores $\ell$ cancels
$\ell$. Equating $\ell$ to the charged-pion Compton stand-in selects one
reversal scale in $(1/2, 1)$. Channel theorems still take $r_1$ as an
input (`SignReversal`, `ScatteringScale`, `StrongChannel`, `LengthRule`).

On the three-sphere, $v^2 = (GM/R)\, f(r/R)$ (`CompactS3`). Laying the
same period along the dual direction gives
$g = \sqrt{a_0 g_N}\,\coth\sqrt{a_0/g_N}$ and $v^4 = GMa_0$
(`DualImage`). The acceleration $a_0$ is an input. $G$, $a_0$, $\alpha$,
and one value of $\ell$ stay underived. No numerical baryon yield is
derived.

### Particles, force, and channels

[`DualRotorDynamics.lean`](DoubleSpacetime/Gravity/DualRotorDynamics.lean)
is the Euler–Lagrange system of the written opposite-sign density. In the
sum and difference channels the mismatch is free and the common rapidity
is sourced. Stiffness, unsigned mass, and free fall are three different
quantities. The note is
[`papers/dst-dynamic-equation.tex`](papers/dst-dynamic-equation.tex).

Position and movement are the motor path, a torsion rotor times the
truncated translator. Along a fixed generator the body-frame force is the
commutator of those two parts, and that bivector does not depend on the
flow parameter (`MotorForce`). The translator coefficient is linear in the
parameter, so its acceleration vanishes. What grows linearly is the
body-frame translational velocity. The written lag force `-m δ(t)` grows
the same way, because the written mismatch accelerates by zero, and it is
not this commutator. Reading the exterior rate `rₛ/(2r²)` off the
translator clock applies the field law a second time. The field law still
selects the generator from the separation. The motor clock does not
multiply the force.

On the equal-scale locus the electromagnetic force is the Coulomb force
divided by the interference factor $\gamma_s$. The sign of $\gamma_s$ is
the repulsion. The length $\ell$ is an input. No angular momentum is
assigned, and $\alpha$ is not derived. The constant factor $1$ puts the
gross-structure ladder on the rational Rydberg ratios, so the Balmer and
Lyman ratios are those rationals (`HydrogenRepulsion`). The factor
$\gamma_s$ is a repulsive correction on the outer well. Reading energies
off its nodes does not recover those ratios. No fine structure is claimed.

An unlike pair exerts both channel terms at every separation. Vanishing
of that pair force does not depend on the separation (`BothChannels`).
The counts $2$, $8$, $18$, and $32$ are two chiral seats on directional
patterns through degrees $0$ through $3$. They are not indices of the
nodes of $\gamma_s$, and they are not spectroscopic labels. The note is
[`papers/dst-electron-shell.tex`](papers/dst-electron-shell.tex).

### Faraday and dual-only control

Faraday coefficients occupy the same six generators as the torsional
bivector: electric on the boosts, magnetic on the rotations. Duality
sends $(E, B)$ to $(B, -E)$. Compact $\mathrm{SU}(2)$ in this development
is the dual rotor. It is not a symmetry of one fixed projector.

Dual-only motion conserves $J + M$ and cannot raise $J$. The mass ceiling
on $|J| \le \pi^2/8$ is

$$
M_{\mathrm{norm}} \le \tfrac56 + \tfrac32 J_{\mathrm{norm}}^2.
$$

The exact image of the cone is the three-lobed envelope of
[`ControlDomain.lean`](DoubleSpacetime/Gravity/ControlDomain.lean). A
dual-only motion meets that envelope at most once.

No theorem in this track asserts `dst_derives_G`, `dst_derives_a0`,
`dst_derives_alpha_s`, `dst_derives_lambda`, Maxwell's equations, a
Weinberg angle, $W$ or $Z$ masses, a chiral $\mathrm{SU}(2)$ symmetry of
a fixed projector, a $V$–$A$ coupling, a helicity-odd drive of $J$, or a
numerical baryon yield.

## Four-valued logic

Parallel track, barrel [`DoubleSpacetime/Logic.lean`](DoubleSpacetime/Logic.lean).
The note is [`papers/dst-4-valued-logic.tex`](papers/dst-4-valued-logic.tex).

A proposition is an admissible torsion configuration. Collapse of
$J_{\mathrm{norm}} \in [-1,1]$ yields four labels
([`TruthValue.lean`](DoubleSpacetime/Logic/TruthValue.lean)):
$|T\rangle$ at $0$ (perfect balance), $|U\rangle$ on $(0,1)$
(boost-dominant), $|F\rangle$ at $+1$ (pure boost), and $|B\rangle$ on
$[-1,0)$ (rotation-dominant). Outside $[-1,1]$ classification is refused.
Conjunction with negation never saturates the negative wall, so
$\{P, \neg P\}$ does not explode. The Gödel residuum of $\min$ and the
regime implication disagree at $U \to T$ and at $B \to T$.

Vacuum and a balanced massive seed can share the label $T$, because the
amplitude layer carries a second observable, the mass. The Killing form
is indefinite, so self-overlap is not a Born probability. Beal and Fermat
status boards in `Logic/Example/` label closed slices, diagnostic
bridges, and live residuals differently. The boards do not entail the
classical conjectures.

`Logic/Quantum/` is the same logic, not a separate physics track. The
notes are [`papers/dst-de-broglie-wave.tex`](papers/dst-de-broglie-wave.tex)
and [`papers/dst-quantum-gravity.tex`](papers/dst-quantum-gravity.tex).
The dual rotor is $\mathrm{SU}(2)$. A unit-determinant total rotor
preserves the mass. A joint state of two dual spinors has invariant
$\det\Psi$, which vanishes exactly on product states, and the singlet
reaches the CHSH value $2\sqrt{2}$. The layer does not produce a mass
from torsion. A finite discrete rotor image is not a count of
generations.

## Repository layout

```
DoubleSpacetime.lean            Root: Basic and Gravity
DoubleSpacetime/
  Basic.lean                   Diophantine public API
  Algebra.lean                 Algebra barrel
  Algebra/                     PGA, Cl(3,1), Cl(9,1), motors, J, discrete torus
  Embedding/                   Integer rotors, translators, Fermat motor, height
  Framework/                   Power sums, lattice, descent, amplification
  Theorems/                    Problem layers, thirteen axioms, finite certificates
  FoundationRegression.lean    CI-facing examples, including the Beal atlas
  Gravity.lean                 Gravity barrel and module index
  Gravity/                     Chart, scales, dynamics, force, Faraday, control
  Logic.lean                   D4L barrel
  Logic/                       D4L, and Logic/Quantum
Goals/                         Open targets. Sorry allowed. Not imported by the library
papers/                        English sources
papers/japanese/               Japanese counterparts, luatexja
```

## Papers

English sources live in [`papers/`](papers/). Each one has a Japanese
counterpart in [`papers/japanese/`](papers/japanese/), with the same claims
and the file name `<stem>-ja.tex`. Hosted PDFs are in
[hypernumbernet/double-spacetime-doc](https://github.com/hypernumbernet/double-spacetime-doc).
Both languages compile with LuaLaTeX from the directory that contains the
source. Japanese sources load `luatexja`.

| Track | Source | Subject |
| --- | --- | --- |
| Gravity | [`double-spacetime-theory.tex`](papers/double-spacetime-theory.tex) | Gravity as torsion between usual and dual spacetime |
| Gravity | [`discrete-dual-spacetime.tex`](papers/discrete-dual-spacetime.tex) | Admissible ceiling and the finite discrete rotor image |
| Gravity | [`dst-pga.tex`](papers/dst-pga.tex) | Duality, null translations, motors, and the direction of gravity |
| Gravity | [`dst-galactic-rotation.tex`](papers/dst-galactic-rotation.tex) | Dual-direction images of a spherical source. The acceleration $a_0$ is an input |
| Gravity | [`dst-3-sphere-log.tex`](papers/dst-3-sphere-log.tex) | Log chart of the three-sphere |
| Gravity | [`dst-dynamic-equation.tex`](papers/dst-dynamic-equation.tex) | Written action, free mismatch, neighbouring oscillator |
| Gravity | [`dst-electron-shell.tex`](papers/dst-electron-shell.tex) | Signed electrostatic force, seats, bonds, and the enclosure spectrum |
| Gravity | [`dst-strong-interaction.tex`](papers/dst-strong-interaction.tex) | Repulsive layer, the rapidity threshold, and seat counts |
| Gravity | [`dst-cold-fusion.tex`](papers/dst-cold-fusion.tex) | Restoring seat of a like pair in an octahedral cage |
| Gravity | [`dst-beta-decay.tex`](papers/dst-beta-decay.tex) | Neutron $\beta$ decay as replacement of rotor class |
| Gravity | [`dst-gravitational-lensing.tex`](papers/dst-gravitational-lensing.tex) | Torsion stars and the return of a captured ray |
| Diophantine | [`dst-diophantine.tex`](papers/dst-diophantine.tex) | Amplification programme. The live residuals and bridges above remain open |
| Logic | [`dst-4-valued-logic.tex`](papers/dst-4-valued-logic.tex) | Four labels, amplitudes, and the dual Hilbert layer |
| Logic | [`dst-de-broglie-wave.tex`](papers/dst-de-broglie-wave.tex) | Dual-rotor phase lag |
| Logic | [`dst-quantum-gravity.tex`](papers/dst-quantum-gravity.tex) | Dirac spinor, two-spinor invariant, and torsional mismatch |

## Build

The toolchain is pinned in [`lean-toolchain`](lean-toolchain) at
`leanprover/lean4:v4.35.0`. mathlib is the matching revision in
[`lakefile.toml`](lakefile.toml). Install [elan](https://github.com/leanprover/elan),
then from the repository root:

```bash
lake build
```

That builds the root (Diophantine path and gravity) and the logic barrel.
`Basic` does not re-export the parallel barrels. A module can still be
built on its own:

```bash
lake build DoubleSpacetime.Gravity
lake build DoubleSpacetime.Logic
```

Open targets are a separate library. `sorry` is allowed there, and the
default build does not include it:

```bash
lake build Goals
```

Continuous integration
([`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml))
on a pull request rejects `sorry` and any axiom outside the thirteen names
above ([`scripts/check_main_library.sh`](scripts/check_main_library.sh)) and
reports the open goal count. It does not build Lean. A full build, including
`Goals`, runs only from a manual workflow dispatch, using
[lean-action](https://github.com/leanprover/lean-action). A toolchain change
on `main` or `master` is tagged by
[`.github/workflows/create-release.yml`](.github/workflows/create-release.yml).
Dependency updates are manual, through
[`.github/workflows/update.yml`](.github/workflows/update.yml).

`FoundationRegression` is the CI-facing sample of the Diophantine path,
including the Beal and Fermat atlases. The priority of open aims is
recorded in [`Goals/README.md`](Goals/README.md).
