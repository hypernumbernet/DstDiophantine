import DstDiophantine.Gravity.Regression

/-!
# Gravity / PGA–TEGR chart layer

Parallel track. Not re-exported from `DstDiophantine.Basic`.
Algebraic `J` is a dimensionless parameter-space scalar. It is not the
Weitzenböck density `T`, and it is not \(c^4/(G\,\ell_P^{-2})\).

No theorem asserts `dst_derives_G`, `dst_derives_a0`, `dst_derives_alpha_s`,
`dst_derives_lambda`, `dst_derives_lambdaN`, `dst_derives_Amax`, Maxwell's
equations, a Weinberg angle, \(W/Z\) masses, a chiral \(\mathrm{SU}(2)\),
a V--A coupling, a helicity-odd drive of \(J\), or a numerical baryon yield.

This file is the index. The checked boundary of each claim is the module
doc of the file named below. `Gravity.Regression` restates those theorems
as smoke tests and adds none.

On the diagonal radial coframe the teleparallel quadratic is
\(T=-2(A+r A')/r^2\). The vacuum condition \((rA)'=1\) freezes it at
\(-2/r^2\), the value of the flat spherical frame, and selects
\(A=1-r_s/r\). The mismatch \(J=\tfrac12\varphi^2\) on that chart is not
\(T\). The auxiliary expression `(2/r²)(1-√A)²/√A` is not the quadratic;
lemmas about it live in `JTDictionary` and `GaugeDictionary`.

A pure boost of the inertial frame in a fixed plane, of any rapidity
profile \(\varphi(t,x)\), induces the Minkowski metric. Its coordinate
torsion is \(T^t{}_{tx}=\partial_t\varphi\) and \(T^x{}_{xt}=\partial_x\varphi\),
and the teleparallel quadratic vanishes for every jet. The same
\(J=\tfrac12\varphi^2\) does not determine \(T\): the inertial jet has
\(T=0\), and the exterior Schwarzschild coframe has \(T=-2/r^2\).
Distinct squared rapidities give the same metric and distinct \(J\).

`Coframe`, `Sandwich`, `Weitzenbock`, `Schwarzschild`, `SI`, and
`LineWindow` are imported by the modules below. They are not named in the
import list of `Gravity.Regression`.

## Chart dictionary

* `Tetrad` — motor sandwich of the reference frame. A pure translator does not reproduce the
  classical Schwarzschild diagonal gauge.
* `Identification` — parameter-space `J` against the teleparallel scalar. No pointwise map sends
  `J` to `T` on every tetrad.
* `RadialQuadratic` — the teleparallel quadratic on the diagonal radial coframe.
* `JTDictionary`, `GaugeDictionary` — the auxiliary chart expressions. They are not a dictionary
  between `J` and the Weitzenböck scalar.
* `ClassicalSchwarzschild` — exterior Schwarzschild as the vacuum gauge. Far-field statements about
  `schwarzschildTeleparallelT` concern the auxiliary expression.
* `LorentzGauge` — an inertial-plane boost keeps the Minkowski metric and kills the quadratic.

## The direction of gravity

* `KillingAxis` — the static Killing field as a pure boost about an inward axis at distance `ℓ`.
  The squared Killing norm has d'Alembertian `8J`.
* `RadialFall` — the same release law on the exterior chart. The speed cancels and
  \(d^2r/d\tau^2=-r_s/(2r^2)\).

## Scales that are inputs

* `SI` — external rational stand-ins. They are not derived from the algebra.
* `NewtonFromLight` — a comparison of `c` with `G`. It does not derive `G`.
* `EventBoundary` — the admissible ceiling read as a finite redshift floor. A one-way horizon `A=0`
  does not form on that chart.
* `Godel` — the Gödel coframe. The azimuthal norm changes sign at `log(1+√2)`, with finite
  coframe legs. Every real rapidity of the tilt `√2 tanh r` is attained strictly before that
  radius, where the circles are still spacelike. A pure `(t,φ)` boost writes no cross term.
* `Algebra.SourceSuperposition` — source bivectors add without a ceiling. The expressed point is
  the nearest admissible configuration, so its `|J|` stays at most \(3\pi^2/8\).
* `MachSource` — surrounding matter fixes the expressed point, not the stiffness `m`. No `F=ma`,
  and no laboratory acceleration ceiling.
* `MassOrigin` — the time-reversing dual map fixes a configuration only at vanishing unsigned mass.
* `MassCoefficient` — a pure lag off equal rapidity adds to the unsigned mass at every common
  rapidity. The value of `m` is not fixed.
* `CoulombFromDual` — a labelled pairing of the lattice floor with `α`. It does not derive `α`.
* `ElectronShell` — Coulomb rewritten with `γ_s`. The length `ℓ` is not a theorem, and no theorem
  asserts `dst_derives_lambda`.
* `ForceScale` — one integer read as the Planck ratio places the floor at `(16/3)α_G`. It derives
  neither `G` nor `α`.
* `CompactS3` — \(v^2=(GM/R)\,f(r/R)\) on the three-sphere. `a₀` is an input.
* `DualImage` — the same period laid along the dual direction. The lattice sum is
  \((GM/(rR))\coth(r/R)\).
* `GalaxyCurve` — a spherical dwarf on those stand-ins. Outside the ball the curve is the
  point-mass law.
* `SlerpTorque` — the pull follows a great circle. `chordMoment` vanishes on a common ray and at
  the chart origin.
* `RelationalPosition` — relative position is the rotor `ρ(a,b)=a⁻¹b`. It is not the intra-particle
  mismatch `Ω`. No position operator is claimed.
* `ChannelRange` — the same enhancement on two compactification radii. `Λ` is an input, and the
  comparison does not subtract the Coulomb coupling from `G`.
* `CliffordParallel` — the two Hopf families on the three-sphere. `H₀` is an input. No theorem
  asserts `dst_derives_lambda`, and none names which family the universe carries.
* `WeakLinearity` — at a fixed compactification radius the dual acceleration is linear in mass, and
  the mass-scaled relation is strictly subadditive.
* `NuclearLayer` — saturation density, binding energy per nucleon, and the pion-length window. The
  estimate `A∼300` is an external heuristic.
* `NuclearLength` — the charged-pion Compton wavelength against laboratory caps. Not the definition
  of the sign-reversal scale.
* `SignReversal` — the sign-reversal scale `r₁` is an observational constant. The channel length is
  the definition `ℓ=2 x₁ r₁`.
* `StrongChannel` — the rapidity threshold on `(π/4,π/2)`. The prefactor `κ`, a fusion rate, and
  the `1/v` law are not derived.
* `LengthRule` — both channels at once. Nothing here fixes `κ` or computes a binding.
* `BothChannels` — an unlike pair exerts both terms at every separation. Where the factors have the
  same sign, the separation-increasing force does not vanish.
* `ChannelBridge` — where both factors are nonzero, the mass-to-charge ratio is
  `(κ/coul)·(γ_E/γ_G)`. Nothing here derives a radius at which the two factors vanish together.
* `BaryonAsymmetry` — both signs of a vacuum rapidity. `J` and `M` are even in that rapidity. No
  numerical baryon yield is derived.
* `ParticleStability` — a balanced massive seed is not emptied by either rapidity budget alone.

## Layers and particle dynamics

* `TorsionalLayer` — the equal-scale spectrum: one node in each `π`-interval, and inward screening
  of the plateau force.
* `DualRotorDynamics` — the Euler–Lagrange system of the written action. Dual-only motion is a
  constraint unless `m(φ-θ)=0`.
* `DualRotorRigidity` — an arbitrary mismatch slope. The quartic well's curvature is not a
  prescribed Compton value.
* `DualRotorFlow` — closed integrals of those jets. `√(2m)` meets the Compton frequency `m` only at
  `m=0` and `m=2`.
* `DualRotorVacuum` — on one axis, written alignment keeps `J=0` while `M` coasts with `σ²/4`.
* `DualRotorMotor` — the factorised rotor splits the null ideal. Off axis the sign of `p²-q²`
  selects one rotor.
* `NullRotation` — that parabolic rotor is a one-parameter group of Minkowski isometries. No
  position operator is claimed.
* `ExponentialFamily` — one exponential covers the elliptic and null limits. No position operator
  is claimed.
* `RestMass` — stiffness, unsigned mass, and free fall are three different quantities. No `F=ma` is
  claimed.
* `ElectronOrbit` — the first Coulombic node lies in `(π/4,1)`. Equal-scale radii are not the Bohr
  radii.
* `ElectronSquare` — on the square the midplane pair has no outer-well equilibrium. In the first
  repulsive shell there is exactly one restoring square.
* `ElectronHelium` — charge `Z>0` with `Z≠1` is not that square equilibrium wherever both factors
  are nonzero.
* `HeliumBody` — two electrons relative to a nucleus are two elements of the three-sphere.
  The three cosines classify the pair. They are not the laboratory separations. At an
  atomic separation the curvature of a galactic or cosmic compactification does not
  enter the force.
* `ElectronForce` — counted with attraction positive, the outer-well force strengthens with phase.
  A circular path is radially restoring on one side of a single phase.
* `HydrogenAlpha` — single-valuedness and the centripetal identity place a circular path at `r=n²
  a₀ γ_s`. The interference node is not that point.
* `LineWindow` — a rational bracket for `π` carries a rational window up to the real vacuum
  wavelength.
* `OrbitClosure` — one revolution restores the orbital point and leaves the dual rotor at `-1`.
  That is not `pr=nℏ`.
* `SpectralLines` — vacuum-wavelength windows of four hydrogen lines on the SI stand-ins.
* `ElectronNumbers` — the circular radius, the first node, the diagonal, the side, the one-electron
  extremum, and the second node stand in that order.
* `ElectronLength` — an outer-well radius caps `ℓ`. The radius `a₀/Z` is not an input.
* `Rutherford` — the electromagnetic scale on the SI stand-ins, and the head-on distance of a
  `7.69` MeV alpha particle on gold.
* `NeutronScatter` — outside the rapidity wall a neutron is pulled inward. A scattering length in
  femtometres is not derived.
* `ElectronCapacity` — diameter, cube, and seat counts. Those counts are not indices of the
  equal-scale nodes.
* `ElectronShape` — a seat is a pattern on directions, not a path.
* `ElectronAngular` — the square of the angular momentum is the degree times one more than the
  degree. No fine-structure splitting is claimed.
* `ElectronBoundary` — tetrahedron, octahedron, cube, and icosahedron have no outer radial root
  once the nuclear charge is large enough. An unlike pair is driven toward the first node.
* `ElectronDodeca` — for every `Z≥8` the dodecahedron has one restoring root before the nearest
  chord meets the first node.
* `ElectronWater` — while the bonding electrons repel, the other bond drives each toward a wider
  angle. The nuclear charge does not enter that comparison.
* `ElectronAngle` — four rays of a regular tetrahedron. A non-shared electron is driven inward
  while every separation lies in the outer well.
* `ElectronTrio` — three coplanar rays. An axial electron drives each ray off the plane. The
  nuclear charge does not enter that sign.
* `ElectronMetal` — at the centre of a regular octahedron, a cube, or a cuboctahedron the force
  vanishes and every displacement of an electron is pushed further. No cohesive energy is claimed.
* `ElectronCrystal` — a finite set closed under the rotations of a tetrahedron exerts no force at
  the site. A lattice rotation through `2π/n` requires `n∈{1,2,3,4,6}`.
* `MetalFusion` — two protons on one axis of a regular octahedron of ions have one restoring
  separation. No rate and no heat are derived.
* `Blackbody` — mean occupation `1/(eˣ-1)` on a harmonic ladder. The constants `h`, `k_B`, `c`, and
  the mode growth are not roots of `γ_s`.
* `Lensing` — weak deflection by one thin shell. A repulsive shell has neither critical curve on
  its disk.
* `PhotonReturn` — a ray below the photon sphere has no turning point on the classical exterior. On
  either recorded ceiling the same ray turns inside the freeze.

## One Faraday six-space

* `Faraday` — electric coefficients on the boosts and magnetic coefficients on the rotations. The
  quadratic is \(J=\tfrac12(E^2-B^2)\). The outer product is not the first-order sandwich increment.
* `Electroweak` — the six-space against an axis. Maxwell's equations, a Weinberg angle, and \(W/Z\)
  masses are not derived.
* `CircularPolarization` — a circular wave is null at every phase. A helicity drive of `J` is not
  derived.
* `ChiralSpectrum` — a spatial axis splits the six-space into an `so(2,1)` stabilizer and a
  complement. Compact `SU(2)` here is the dual rotor, not a symmetry of a fixed projector.
* `ChiralityStabilizer` — the stabilizer of one chirality axis. A chiral `SU(2)` gauge symmetry is
  not derived.
* `ChiralCurrent` — a charged generator exchanges the two projectors and its cross sandwich does
  not vanish. A Cartan generator preserves each projector.
* `EMControl` — a dual-only increment read as magnetic superposition and as `θ↦θ+eA`. Neither
  raises `J` against a nonnegative dual seed.
* `CircularHold` — one cycle of that potential stays in the cone exactly when each transverse axis
  has dual bias and wall slack at least `ρ`.
* `NeutronMagnet` — the charge-silent magnet. On `J=0` the magnetic square equals the unsigned
  mass. The ratio of nucleon moments is not derived.
* `SilentControl` — that magnet joined to dual-only control. With the charge label off, a circular
  potential drops no ponderomotive mean.
* `ParityBridge` — spatial inversion exchanges the two projectors of every axis and acts by
  `(E,B)↦(-E,B)`. The bridge is not identified with `CP`.

## Dual-only control of \((J,M)\)

* `DualControl` — dual-only motion conserves `J+M` and cannot raise `J`. It reaches a shield `J=0`
  precisely when the dual wall is nonpositive.
* `ConeLabels` — four regimes of normalised mismatch on the admissible cone. Saturated
  attraction is the unique dual-only rigid point. A negative wall carries repulsion and
  balance; below the ceiling a positive wall stays in unsaturated attraction.
* `MassCorners` — the unsigned mass shares the ceiling of `J`. Equality is eight
  corners, at normalised heights `1`, `1/3`, `-1/3`, and `-1`. Balance reaches at
  most five sixths of that mass. The unsigned mass is not the Dirac mass.
* `ShieldClock` — `γ_eff` returns to `1` at a dual angle strictly before the coaxial shield. It is
  not the mismatch `J`.
* `ShieldCeiling` — the admissible cone forbids a configuration from being simultaneously heavy and
  gravitationally neutral.
* `ControlDomain` — the exact image of the cone is the three-lobed envelope. No electromagnetic
  coupling is claimed.
* `EnvelopeLock` — the envelope is met only when every axis lies on the wall and at least two axes
  are corners, so a dual-only motion meets it at most once.
* `ShieldHold` — both angular accelerations vanish exactly on axiswise alignment. A neutral
  configuration has lag budget at most `π²/2`.
* `HoldPrice` — on the cone the lag budget is at least `4M-3k²`, with equality exactly on the wall.
* `ControlScale` — in units of `k²=(π/2)²`, the exact image of the cone is `5/4` plus the squared
  distance from `J/k²` to the nearest of `{-1,0,1}`.
-/
