import DstDiophantine.Gravity.Regression

/-!
# Gravity

Parallel track, not re-exported from `DstDiophantine.Basic`.
Algebraic `J` is not the Weitzenböck density `T` and not a dimensionful coupling.
No theorem derives `G`, `a0`, `alpha_s`, `lambda`, Maxwell, a Weinberg angle, `W/Z` masses, chiral
`SU(2)`, V--A, or a numerical baryon yield.
Child module docs hold the checked boundary, and `Gravity.Regression` adds no claim.

## Chart dictionary

* `Tetrad` — motor sandwich of the reference frame; a pure translator does not reproduce the
  classical Schwarzschild diagonal gauge.
* `DegenerateSandwich` — a motor preserves the degenerate square; the metric and `T` do not see `λ`
  and are not a function of the finite angle `J`.
* `Identification` — parameter-space `J` against the teleparallel scalar; no pointwise map sends `J`
  to `T` on every tetrad.
* `RadialQuadratic` — the teleparallel quadratic on the diagonal radial coframe.
* `JTDictionary`, `GaugeDictionary` — the auxiliary chart expressions; not a dictionary between `J`
  and the Weitzenböck scalar.
* `ClassicalSchwarzschild` — exterior Schwarzschild as the vacuum gauge; far-field
  `schwarzschildTeleparallelT` concerns the auxiliary expression.
* `LorentzGauge` — a one-parameter boost or rotation on any coordinate plane, a null rotation, and
  the commuting product of a `(t,x)` boost with a `(y,z)` rotation keep the Minkowski metric and
  kill the quadratic; an arbitrary local Lorentz jet need not.
* `OrderedPlanes` — a `(t,x)` boost of rapidity `φ(y)` and an `(x,y)` rotation of angle `θ(t)` do
  not commute.

## The direction of gravity

* `PlaneBracket` — on a coordinate plane `Πᵢⱼ = e₄ ∧ eᵢ ∧ eⱼ` with right-handed normal `n`, the
  bracket with the spatial volume `k` is `-Nₙ` and the bracket with the dual trivector of `n` is
  `N₀`.
* `KillingAxis` — the static Killing field as a pure boost about an inward axis at distance `ℓ`.
* `CurvedTransport` — the Levi-Civita connection of the exterior orthonormal frame annihilates the
  outward radial leg.
* `KillingTransport` — conjugation by the translator of a displacement sends `λ` to `λ + ω x` and
  leaves the Lorentz part fixed.
* `RadialFall` — the same release law on the exterior chart.
* `Perihelion` — constant angular momentum on that coframe; that ellipse is not an exact solution.
* `Mercury` — exterior radial return of Mercury in `(42, 44)` arcseconds per Julian
  century from external elements.
* `SolarDeflection` — azimuthal excess of an exterior null ray that turns at radius `R`.
  For the nominal solar radius the excess lies in `(17/10, 9/5)` arcseconds. No eclipse
  residual is claimed, and this is not `Lensing.interiorDeflection`.
* `OffEquator` — the same radial law with both angular legs.

## Scales that are inputs

* `SI` — external rational stand-ins, not derived from the algebra.
* `NewtonFromLight` — a comparison of `c` with `G`; it does not derive `G`.
* `EventBoundary` — the admissible ceiling read as a finite redshift floor.
* `Godel` — the Gödel coframe.
* `Kerr` — the Kerr coframe on `Σ > 0` and `Δ > 0`.
* `Algebra.SourceSuperposition` — source bivectors add without a ceiling.
* `GravitonQuantum` — one graviton is one pure dual step of angle `2π/N`; these carriers are not a
  mass spectrum, and no derivation of `α_G` or of a laboratory error rate.
* `GravitonLogic` — the ray of `spinUp` is the computational observable; two orders occupy distinct
  atoms and one device error, and no laboratory rate.
* `MachSource` — surrounding matter fixes the expressed point, not the stiffness `m`; no `F=ma`, and
  no laboratory acceleration ceiling.
* `InteriorClock` — DST time is the enclosed compactness, and at the centre it is the vacuum rate;
  no claim that a frequency beat equals a wavelength.
* `MassOrigin` — the time-reversing dual map fixes a configuration only at vanishing unsigned mass.
* `MassCoefficient` — a pure lag off equal rapidity adds to the unsigned mass at every common
  rapidity; the value of `m` is not fixed.
* `CoulombFromDual` — a labelled pairing of the lattice floor with `α`; it does not derive `α`.
* `ElectronShell` — Coulomb rewritten with `γ_s`; the length `ℓ` is not a theorem, and no theorem
  asserts `dst_derives_lambda`.
* `ForceScale` — one integer read as the Planck ratio places the floor at `(16/3)α_G`; it derives
  neither `G` nor `α`.
* `CompactS3` — \(v^2=(GM/R)\,f(r/R)\) on the three-sphere; `a₀` is an input.
* `DualImage` — the same period laid along the dual direction.
* `GalaxyCurve` — a spherical dwarf on those stand-ins.
* `SlerpTorque` — the pull follows a great circle.
* `ChartRotation` — a pole-fixing reflection and a pole-fixing rotation commute with the log chart.
* `RacketFlip` — the separatrix `A sech(kt)`, `B tanh(kt)`, `C sech(kt)` of Euler's equations.
* `RacketThermal` — the uniform average of a signed sum of chart moments is zero, and the average of
  its square is the sum of the squares; no frequency of reversals is drawn from the weight.
* `RelationalPosition` — relative position is the rotor `ρ(a,b)=a⁻¹b`; it is not the intra-particle
  mismatch `Ω`, and no position operator is claimed.
* `ChannelRange` — the same enhancement on two compactification radii; `Λ` is an input, and the
  comparison does not subtract the Coulomb coupling from `G`.
* `CliffordParallel` — the two Hopf families on the three-sphere; `H₀` is an input, no theorem
  asserts `dst_derives_lambda`, and none names which family the universe carries.
* `WeakLinearity` — at a fixed compactification radius the dual acceleration is linear in mass, and
  the mass-scaled relation is strictly subadditive.
* `NuclearLayer` — saturation density, binding energy per nucleon, and the pion-length window; the
  inclusion does not select a scattering scale, `A∼300` is an external heuristic, the counts are not
  node indices, and the splitting is not derived.
* `NuclearLength` — the charged-pion Compton wavelength against laboratory caps; not the definition
  of the sign-reversal scale.
* `SignReversal` — the sign-reversal scale `r₁` is an observational constant for the channel
  theorems; equating `ℓ` to the charged-pion Compton stand-in selects a unique scale in `(1/2, 1)`,
  and `channelMassRatio` still does not take a meson mass.
* `ScatteringScale` — repulsion at `1/2` and attraction on `[1, 2]` are exactly `1/2 < r₁ < 1`,
  so `14/15 < ℓ < 19/10`. The same signs do not select a point. One positive rapidity gives
  `3/5` and `9/10` the same `thresholdRadius / ℓ`. A two-channel zero at a phase that ignores `ℓ`
  does not select `ℓ`. `γ_s` is even in `ℓ`, and the charged-pion selector is not an input.
* `StrongChannel` — `thresholdRadius ℓ φ` is the equal-scale radius where a positive rapidity meets
  `phiStar`. Every `layerRadius ℓ x` whose phase ignores `ℓ` has a ratio that depends only on that
  phase, so it does not select `ℓ`. `phiStar` has no critical phase on `(π/4, π/2)`. `gammaSEqual`
  is critical only at integer multiples of `π`, and those radii stay in the family. At the external
  `14` MeV hypothesis the skin is thinner than `6/100` of the static node. The prefactor `κ`, a
  fusion rate, and the `1/v` law are not derived.
* `LengthRule` — both channels at once; `ℓ_E` stays an external input and is not a nuclear
  `layerRadius`. Nothing here fixes `κ` or computes a binding.
* `BothChannels` — an unlike pair exerts both terms at every separation. Vanishing of
  `pairChannelForce` does not depend on the separation.
* `ElectronExclusion` — two electrons above the Bohr radius repel electrically and attract
  gravitationally; no spin-statistics theorem is claimed.
* `SpinVersusExclusion` — spin reversal keeps the place and reverses the spin vector; no
  spin-statistics theorem is claimed.
* `ChannelBridge` — where both factors are nonzero, the mass-to-charge ratio is
  `(κ/coul)·(γ_E/γ_G)`; nothing here derives a radius at which the two factors vanish together.
  The external electromagnetic length over the sign-reversal window lies in `(203, 414)` and does
  not select `r₁`.
* `BaryonAsymmetry` — both signs of a vacuum rapidity; no numerical baryon yield is derived.
* `ParticleStability` — a balanced massive seed is not emptied by either rapidity budget alone.

## Layers and particle dynamics

* `TorsionalLayer` — the equal-scale spectrum: one node in each `π`-interval, and inward screening
  of the plateau force.
* `DualRotorDynamics` — the Euler–Lagrange system of the written action.
* `WheelerDeWitt` — the written kinetic Hessian has determinant `-1` in six rapidities, `-1` on
  one axis, and `-1/4` in the mixed velocities. The Jacobi integral is the Hamiltonian and takes
  both signs on the solutions. Vanishing curvature of a one-parameter rotor does not impose that
  constraint. No wave functional of a spatial metric is constructed.
* `DualRotorRigidity` — an arbitrary mismatch slope; the quartic well's curvature is not a
  prescribed Compton value.
* `DualRotorFlow` — closed integrals of those jets.
* `DualRotorVacuum` — on one axis, written alignment keeps `J=0` while `M` coasts with `σ²/4`.
* `DualRotorMismatch` — on the written flow `J` is the product `δσ/2`. For positive stiffness
  it is constant only when the lag vanishes, and then it is zero; any other lag tends to `-∞`
  at both time ends. The flow stays in the admissible cone for every time only at a resting
  aligned rapidity in `[0, π/2]`.
* `DualRotorMotor` — the factorised rotor splits the null ideal.
* `NullRotation` — that parabolic rotor is a one-parameter group of Minkowski isometries; no
  position operator is claimed.
* `ExponentialFamily` — one exponential covers the elliptic and null limits; no position operator is
  claimed.
* `RestMass` — stiffness, unsigned mass, and free fall are three different quantities; no `F=ma` is
  claimed.
* `DualCycle` — an admissible dual half-angle is at most `π √3 / 4`, so the dual rotor is never
  `-1`. Negating the dual rapidities reverses the rotor and preserves `J`, and a unit lag rate
  leaves the cone short of the antipodal rapidity `2π`. No acceleration ceiling is read off a
  `4π` wrap.
* `ElectronOrbit` — the first Coulombic node lies in `(π/4,1)`; equal-scale radii are not the Bohr
  radii, and the map `ℓ ↦ ℓ/Z` is not the radius `a₀/Z`.
* `ElectronSquare` — on the square the midplane pair has no outer-well equilibrium.
* `ElectronHelium` — charge `Z>0` with `Z≠1` is not that square equilibrium wherever both factors
  are nonzero.
* `HeliumBody` — two electrons relative to a nucleus are two elements of the three-sphere; the three
  cosines are not the laboratory separations.
* `ElectronForce` — counted with attraction positive, the outer-well force strengthens with phase;
  the denominator is the time-delay factor `γ_s`, not the torsional mismatch.
  No angular momentum is assigned, and no circular energy is formed.
* `HydrogenRepulsion` — the constant factor `1` puts `-ke²/(2n²a₀)` on the gross-structure
  ladder, so the Balmer and Lyman ratios are the rational Rydberg ratios. The equal-scale factor
  `γ_s` is a repulsive correction on the outer well and points outward on `(x₁, π)`. The written
  factor `1/γ_s` strengthens the attraction and is unbounded at the first node. Reading energies
  off the nodes does not recover those ratios. No fine structure is claimed.
* `RelationalPolarization` — the interaction is the stiffness cross term of two charge labels,
  evaluated at the geodesic angle of the relative rotor `ρ = a⁻¹b`. `m` is that stiffness.
  The conjugate momenta are half the mismatch rate and half the common rate. Holding the usual
  rapidity at zero is a constraint. On the equal-scale locus `J` vanishes while `γ_s` changes
  sign, so those shells are not this polarization. The angle derivative is not an
  Euler–Lagrange force. On a diameter the coefficient is `4 - Z`; it vanishes at every angle
  when `Z = 4`, and nowhere in `(0, π/2)` otherwise. No position operator is claimed.
* `ElectronDiscrete` — a dual step `2π/N` spaces the equal-scale phase by `π/N`; a sample is not
  proved to stay a full step from the node, and the second node is not capped.
* `ElectronStanding` — the curvature of `e^{-r/a}` supplies the outward force `ℏ²/(m a r²)`; no
  binding energy is derived.
* `LineWindow` — a rational bracket for `π` carries a rational window up to the real vacuum
  wavelength; it does not place an atomic radius.
* `OrbitClosure` — one revolution restores the orbital point and leaves the dual rotor at `-1`; the
  plane-wave identity `pr=nℏ` does not select a radius.
* `ElectronNumbers` — the first node, the diagonal, the side, the one-electron extremum, and the
  second node stand in that order.
* `ElectronLength` — an outer-well radius caps `ℓ`; the radius `a₀/Z` is not an input.
* `Rutherford` — the electromagnetic scale on the SI stand-ins, and the head-on distance of a `7.69`
  MeV alpha particle on gold.
* `NeutronScatter` — outside the rapidity wall a neutron is pulled inward; a scattering length in
  femtometres is not derived.
* `ElectronCapacity` — diameter, cube, and seat counts; those counts are not indices of the
  equal-scale nodes.
* `ElectronShape` — a seat is a pattern on directions, not a path.
* `ElectronAngular` — the square is the response of the pattern when its direction is turned, the
  degree times one more than the degree; it is not the angular momentum of an electron in
  circulation, it does not place a radius, and no fine-structure splitting is claimed.
* `ElectronBoundary` — tetrahedron, octahedron, cube, and icosahedron have no outer radial root once
  the nuclear charge is large enough.
* `ElectronDodeca` — for every `Z≥8` the dodecahedron has one restoring root before the nearest
  chord meets the first node.
* `ElectronWater` — while the bonding electrons repel, the other bond drives each toward a wider
  angle.
* `ElectronAngle` — four rays of a regular tetrahedron.
* `ElectronTrio` — three coplanar rays.
* `ElectronMetal` — at the centre of a regular octahedron, a cube, or a cuboctahedron the force
  vanishes and every displacement of an electron is pushed further; no cohesive energy is claimed.
* `ElectronCrystal` — a finite set closed under the rotations of a tetrahedron exerts no force at
  the site.
* `MetalFusion` — two protons on one axis of a regular octahedron of ions have one restoring
  separation; no rate and no heat are derived.
* `Blackbody` — mean occupation `1/(eˣ-1)` on a harmonic ladder; the constants `h`, `k_B`, `c`, and
  the mode growth are not roots of `γ_s`.
* `ShellCollision` — a partner on the line of centres meets the electron of larger radius first; no
  collision rate is derived, and no root is retuned.
* `Lensing` — weak deflection by one thin shell.
* `PhotonReturn` — a ray below the photon sphere has no turning point on the classical exterior; no
  boundary condition for a gravitational wave, and no late echo train.

## One Faraday six-space

* `Faraday` — electric coefficients on the boosts and magnetic coefficients on the rotations; the
  outer product is not the first-order sandwich increment.
* `Electroweak` — the six-space against an axis; Maxwell's equations, a Weinberg angle, and \(W/Z\)
  masses are not derived.
* `CircularPolarization` — a circular wave is null at every phase; a helicity drive of `J` is not
  derived.
* `ChiralSpectrum` — a spatial axis splits the six-space into an `so(2,1)` stabilizer and a
  complement; compact `SU(2)` here is the dual rotor, not a symmetry of a fixed projector.
* `ChiralityStabilizer` — the stabilizer of one chirality axis; a chiral `SU(2)` gauge symmetry is
  not derived.
* `ChiralCurrent` — a charged generator exchanges the two projectors and its cross sandwich does not
  vanish.
* `EMControl` — a dual-only increment read as magnetic superposition and as `θ↦θ+eA`.
* `CircularHold` — one cycle of that potential stays in the cone exactly when each transverse axis
  has dual bias and wall slack at least `ρ`.
* `NeutronMagnet` — the charge-silent magnet; the ratio of nucleon moments is not derived.
* `SilentControl` — that magnet joined to dual-only control.
* `BetaDecay` — replacement of one nucleon class; the weights, the absolute gap, and V--A are not
  derived.
* `ParityBridge` — spatial inversion exchanges the two projectors of every axis and acts by
  `(E,B)↦(-E,B)`; the bridge is not identified with `CP`.

## Dual-only control of \((J,M)\)

* `DualControl` — dual-only motion conserves `J+M` and cannot raise `J`.
* `ConeLabels` — four regimes of normalised mismatch on the admissible cone.
* `MassCorners` — the unsigned mass shares the ceiling of `J`; the unsigned mass is not the Dirac
  mass.
* `ShieldClock` — `γ_eff` returns to `1` at a dual angle strictly before the coaxial shield; it is
  not the mismatch `J`.
* `ShieldCeiling` — the admissible cone forbids a configuration from being simultaneously heavy and
  gravitationally neutral.
* `ControlDomain` — the exact image of the cone is the three-lobed envelope; no electromagnetic
  coupling is claimed.
* `EnvelopeLock` — the envelope is met only when every axis lies on the wall and at least two axes
  are corners, so a dual-only motion meets it at most once.
* `ShieldHold` — both angular accelerations vanish exactly on axiswise alignment.
* `HoldPrice` — on the cone the lag budget is at least `4M-3k²`, with equality exactly on the wall.
* `ControlScale` — in units of `k²=(π/2)²`, the exact image of the cone is `5/4` plus the squared
  distance from `J/k²` to the nearest of `{-1,0,1}`.
-/
