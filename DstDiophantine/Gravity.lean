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
A rotation in one spatial plane, of any angle profile \(\theta(x,y)\),
induces the Minkowski metric as well. Its coordinate torsion is
\(T^x{}_{xy}=\partial_x\theta\) and \(T^y{}_{xy}=\partial_y\theta\), and the
teleparallel quadratic vanishes for every in-plane jet. The one-axis
mismatch of that angle is \(J=-\tfrac12\theta^2\), opposite the pure boost.

`Coframe`, `Sandwich`, `Weitzenbock`, `Schwarzschild`, and `SI` are
imported by the modules below. They are not named in the import list of
`Gravity.Regression`. `LineWindow` is imported there.

## Chart dictionary

* `Tetrad` — motor sandwich of the reference frame. A pure translator does not reproduce the
  classical Schwarzschild diagonal gauge.
* `DegenerateSandwich` — a motor preserves the degenerate square. On each reference vector the
  Minkowski leg is the rotor sandwich and the null coefficient is the pairing of `λ`. The metric
  and `T` read that leg. They do not see `λ`, and they are not a function of the finite angle `J`.
* `Identification` — parameter-space `J` against the teleparallel scalar. No pointwise map sends
  `J` to `T` on every tetrad.
* `RadialQuadratic` — the teleparallel quadratic on the diagonal radial coframe.
* `JTDictionary`, `GaugeDictionary` — the auxiliary chart expressions. They are not a dictionary
  between `J` and the Weitzenböck scalar.
* `ClassicalSchwarzschild` — exterior Schwarzschild as the vacuum gauge. Far-field statements about
  `schwarzschildTeleparallelT` concern the auxiliary expression.
* `LorentzGauge` — a one-parameter boost or rotation on any coordinate plane, a null rotation, and
  the commuting product of a `(t,x)` boost with a `(y,z)` rotation keep the Minkowski metric and
  kill the quadratic. An arbitrary local Lorentz jet need not.
* `OrderedPlanes` — a `(t,x)` boost of rapidity `φ(y)` and an `(x,y)` rotation of angle `θ(t)`
  do not commute. Either order induces Minkowski. With the boost on the left,
  `T = -2 (∂_y φ)(∂_t θ) cos θ`. With the rotation on the left,
  `T = -2 (∂_y φ)(∂_t θ) cosh φ`. For a positive product of the derivatives the second stays
  negative, the sign of the attractive vacuum. The first has that sign exactly when `cos θ > 0`.

## The direction of gravity

* `PlaneBracket` — on a coordinate plane `Πᵢⱼ = e₄ ∧ eᵢ ∧ eⱼ` with right-handed normal `n`,
  the bracket with the spatial volume `k` is `-Nₙ`, and the bracket with the dual trivector
  of `n` is `N₀`. Both are pure translations, the bivector of a motor with vanishing torsion.
  The bracket with the dual of an in-plane axis vanishes. For an arbitrary spatial vector `n`
  the ideal plane `Π(n)` brackets with `k` to the translation along `n`, and with the dual of
  `n` to `|n|² N₀`. The symmetric product vanishes in both cases. Displacing the plane by a
  coefficient `δ` of the spatial volume keeps the translation, writes `-δ` as the symmetric
  product, and adds the boost `-δ` along `n` to the time translation.
* `KillingAxis` — the static Killing field as a pure boost about an inward axis at distance `ℓ`.
  The squared Killing norm has d'Alembertian `8J`.
* `CurvedTransport` — the Levi-Civita connection of the exterior orthonormal frame annihilates
  the outward radial leg. The static boost rate changes with proper radius at `-rₛ √A / r³`,
  and the connection contributes nothing. The Killing norm on that leg changes at `κ`, the
  flat rate of a unit radial step. Along the observer the boost is parallel. Along either
  angular leg the connection tilts it out of the time-radial plane at `κ √A / r`; the tangent
  rotation of the sphere does not enter. Static bivectors at two exterior radii are not radial
  parallel transports of one another.
* `KillingTransport` — conjugation by the translator of a displacement sends `λ` to `λ + ω x`
  and leaves the Lorentz part fixed. Along a differentiable curve the translational part changes
  at the rate `ω(ẋ)`. `J` is constant. On the exterior the proper radial derivative of the
  mismatch redshift is the static coefficient `κ = rₛ/(2r²)`, and the inward shift of length
  `ℓ` drops the time translation, leaving the pure boost of that rate. Static bivectors at two
  exterior radii are not flat transports of one another. The Levi-Civita action on the static
  bivector is `CurvedTransport`.
* `RadialFall` — the same release law on the exterior chart. The speed cancels and
  \(d^2r/d\tau^2=-r_s/(2r^2)\).
* `Perihelion` — constant angular momentum on that coframe. The areal acceleration
  is \(-\kappa+L^2/r^3-3\kappa L^2/r^2\). One share of the three is the transverse
  speed in \(\gamma^2\); two shares are the deficit \(A-1\) in the centrifugal
  barrier. For \(0<6M/p<1\) one radial period of the precessing ellipse
  exceeds \(2\pi\) by an amount strictly between \(6\pi M/p\) and that quantity
  over \(1-6M/p\). That ellipse is not an exact solution. A bound orbit
  turning at \(0\le\alpha<\beta\), with third root \(\gamma\) above \(\beta\),
  returns to the larger root at an angle strictly above one radial period of
  the resonant ellipse of rectum \(2/(\alpha+\beta)\). The excess over \(2\pi\)
  is therefore strictly greater than \(6\pi M\) over that rectum, and, because
  \(L^{2}/M\) is strictly longer, strictly greater than \(6\pi M^{2}/L^{2}\).
  When \(3M(\alpha+\beta)\le 1/2\) the excess is strictly less than the
  turning-point quantity divided by \(1-3M(\alpha+\beta)\).
  A tangential tilt \(-\kappa\hat{u}_\varphi\) multiplies angular
  momentum by \(\exp(-\kappa\tau)\). The torsional leg changes only with the radius,
  the radial piece of \(\gamma^2\) cancels, and the transverse piece that remains is
  the perihelion.
* `OffEquator` — the same radial law with both angular legs. The rotation
  `cot θ / r` in the tangent plane of the sphere cancels in
  \(L^2=r^2(\hat{u}_\theta^2+\hat{u}_\varphi^2)\) and in \(r\sin\theta\,\hat{u}_\varphi\),
  wherever \(\sin\theta\neq 0\), and it does not enter the radial rate. The areal
  acceleration, \(E=\sqrt{A}\,\gamma\), and the first integral are the equatorial
  ones in this \(L^2\). An angle advancing at \(L/r^2\) carries the Binet slope,
  and the radial period of the resonant ellipse depends on the motion only
  through this \(L^2\). The return to the larger turning value has the same
  bounds.
  The constants satisfy \((r\sin\theta\,\hat{u}_\varphi)^2\le L^2\sin^2\theta\),
  with equality exactly at \(\hat{u}_\theta=0\). A nonzero azimuthal constant
  keeps \(\sin^2\theta\) at least that ratio, so the trajectory stays off both
  poles. On the edge the polar acceleration is \((\cot\theta/r)\hat{u}_\varphi^2\):
  positive cosine raises \(\theta\) and negative cosine lowers it.
  On the equator the polar rate vanishes and the azimuthal rate is the torsional leg.
  A vanishing azimuthal constant forces \(\hat{u}_\varphi=0\) off the poles
  and keeps \(\varphi\) fixed, so the motion lies on a meridian. Both angular
  accelerations then lose \(\cot\theta/r\). The polar leg changes by the
  equatorial torsional law, the colatitude advances at \(L/r^2\) with
  \(L=r\hat{u}_\theta\), and the radial acceleration is the equatorial one
  in this \(L\). These rates do not divide by \(\sin\theta\).
  A fixed colatitude is either the radial motion of vanishing angular
  momentum, or the equator: there the two constants agree, the band
  collapses to \(\sin^2\theta=1\), and the polar leg remains zero. Off the
  equator that leg does not remain zero on an interval of positive length.
  Where the polar leg does not vanish, \((d\varphi/d\theta)^2\) depends on
  \(\theta\) and the two constants alone: the radius cancels. The
  proper-time rate \((d\theta/d\tau)^2\) still carries the radius.

## Scales that are inputs

* `SI` — external rational stand-ins. They are not derived from the algebra.
* `NewtonFromLight` — a comparison of `c` with `G`. It does not derive `G`.
* `EventBoundary` — the admissible ceiling read as a finite redshift floor. A one-way horizon `A=0`
  does not form on that chart.
* `Godel` — the Gödel coframe. The azimuthal norm changes sign at `log(1+√2)`, with finite
  coframe legs. Every real rapidity of the tilt `√2 tanh r` is attained strictly before that
  radius, where the circles are still spacelike. A pure `(t,φ)` boost writes no cross term.
* `Kerr` — the Kerr coframe on `Σ > 0` and `Δ > 0`. Vanishing spin returns the exterior
  Schwarzschild coframe of gravitational radius `2M`. The `(t,φ)` block has determinant
  `-Δ sin²θ`. A pure `(t,φ)` boost writes no cross term.
* `Algebra.SourceSuperposition` — source bivectors add without a ceiling. The expressed point is
  the nearest admissible configuration, so its `|J|` stays at most \(3\pi^2/8\).
* `GravitonQuantum` — one graviton is one pure dual step of angle `2π/N`. For
  `N ≥ 4` it is admissible and its normalized height is `-16/(3N²)`. While `4n ≤ N`, `n` aligned
  gravitons express `n²` times that height: `n` own shares plus `n(n-1)` ordered-pair shares, and
  every share equals one graviton travelling alone. For `n ≥ 1`, one further graviton makes the
  mutual sum strictly more negative by `2n` shares, while the new own share stays equal to one.
  For `n ≥ 3` the mutual sum is strictly more negative than the own sum. The same angle also
  builds a usual step of height `+ε_N`, whose interference stays above `1`, and an equal-scale
  step of height `0`, whose interference stays positive. The equal-scale phase `π` makes the
  interference negative and is not admissible. These carriers are not a mass spectrum. Once
  `4n ≥ N` the expressed height on that axis locks at `-1/3`, and further mutual growth stays in
  the internal sum. One graviton stays strictly above that lock for `N ≥ 5`. Two aligned gravitons
  remain admissible for `N ≥ 8` and their height is four times one. Gravitons on distinct axes
  share no ordered-pair height. Two on perpendicular axes stay admissible for `N ≥ 4` and express
  twice one; for `N ≥ 8` the aligned pair is lower by exactly the two ordered-pair shares. One on
  each axis expresses three times one. At `N = 4` the three axes meet the pure dual corner and the
  height is `-1`; for `N ≥ 5` the split stays above `-1`, and for `N ≥ 7` above the one-axis lock.
  For `N ≥ 12` three aligned gravitons express nine times one, lower by the six ordered-pair shares.
  The expressed height of a census is the sum of the three axis feet: the square of the count times
  one graviton inside the cone, and the lock `-1/3` on or past the wall. Two locked axes express
  `-2/3`, and three express the floor `-1`. Further gravitons on a locked axis are not expressed.
  For every `n ≥ 1`, at `N = 4n`, `n` gravitons on each axis express that floor. While a total still
  fits on one axis, the aligned census is strictly the lowest. Moving one graviton from a count `n`
  onto a count `m` changes the internal height by `2(m + 1 - n)` shares. Inside the cone the
  expressed height moves with it. Past one wall, gravitons on a second axis still inside the cone
  make the expressed height strictly lower than `-1/3`. With `12n ≤ N`, `n` on each axis express
  `3n²` times one, and the aligned `3n` is lower by `6n²` shares.
  The height does not see an order. On a spinor the perpendicular rotors do not commute for every
  positive angle up to `π`, hence for every lattice step with `N ≥ 3`. A full turn of each axis is
  `-I`, and those two turns commute. Aligned gravitons do commute, and `n` of them act as one rotor
  of angle `2π n/N`. For `2 ≤ n` and `4n ≤ N` their transverse orthogonal probability lies strictly
  below `n²` times one, while the height is exactly `n²` times one. A full count of `N` restores the
  computational weight to `1` and the orthogonal probability to `0`, with the expressed height
  already at `-1/3`. When `4 ∣ N`, the quarter turn `N/4`, the half turn
  `N/2`, the three-quarter turn `3N/4`, and the full turn `N` express that
  same lock. Their orthogonal probabilities are `1/2`, `1`, `1/2`, and `0`.
  From the quarter turn through the half turn each added graviton raises the
  probability, and from the half turn through the full turn each added
  graviton lowers it, while the mutual sum falls throughout. A transverse step replaces the
  computational Born weight `1` by `cos²(π/N)`. The orthogonal probability is `sin²(π/N)`,
  strictly between `(3/4)` and `(3π²/16)` times the floor for `N ≥ 3`, strictly above that floor,
  and strictly below `1/2` for `N ≥ 5`. On every compactification with `N > 10¹⁹` the probability
  lies below `10⁻³⁷`. Three hundred aligned gravitons there express `300²` times one and stay
  above `-10⁻³²`. An axial step leaves that weight at `1`, so its orthogonal probability is `0`,
  and is not `±I`. No derivation of `α_G` or of a laboratory error rate. The charged-pion
  comparison is `NuclearLayer`. The channel-length mass ratio, with no meson mass as an input,
  is `SignReversal.channelMassRatio`.
* `GravitonLogic` — the computational observable is the ray of `spinUp` and its
  negation. An axial graviton leaves that eigenstate inside the original ray and
  outside the negation, and the device error is `0`. A transverse angle in
  `(0, π)`, hence every lattice step with `N ≥ 3`, puts the carrier on a third
  ray: neither ray, meeting each only at zero, and not orthogonal to the
  computational ray. The device may record the negation at `sin²(π/N)`. The
  carrier has not become that ray. The same axial step after the transverse step
  leaves the device error unchanged and moves the ray; before it, the ray is the
  transverse one. The ray depends on the order. The device error does not. One
  graviton about each of two transverse axes, of one angle in `(0, π)`, hence
  `N ≥ 3`, determines a different ray in the two orders and one device error.
  That error is exactly half the error of the same two gravitons aligned, and
  strictly less than twice the error of one. For `N ≥ 8` both censuses lie in
  the cone, the perpendicular height is twice one, and the ratio of the two
  device errors equals the ratio of the two expressed heights. For
  `0 < n ≤ N`, aligned transverse gravitons meet the original ray exactly at
  the full turn and the negation exactly when `2n = N`. Every other count
  occupies a third ray. When `4 ∣ N`, the quarter turn and the three-quarter
  turn share the device error `1/2` on different third rays, the half turn is
  the negation with error `1`, and the full turn returns to the original ray
  with error `0`, while all four express the height `-1/3` and the amplitude
  label `B`. The half turn and the full turn lie on the computational island;
  the quarter turns do not, and the classical expansion along the computational
  ray does not detach onto them. The untouched eigenstate occupies that same
  ray and expresses height `0`. The device errors `0`, `1/2`, and `1`, read as
  heights, are the labels `T`, `U`, and `F`. The device error is not the ray
  the carrier satisfies, and it is not the expressed height. No laboratory
  rate. The height does not see the order.
* `MachSource` — surrounding matter fixes the expressed point, not the stiffness `m`. No `F=ma`,
  and no laboratory acceleration ceiling.
* `InteriorClock` — DST time is the enclosed compactness, and at the centre it is the vacuum
  rate. The potential gradient is the weight, below the surface as well as above. Outside, the
  weak-field clock difference equals the potential difference. The Earth compactness rounds to
  `6.96×10⁻¹⁰`. No claim that a frequency beat equals a wavelength.
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
* `ChartRotation` — a pole-fixing reflection and a pole-fixing rotation commute with the log chart.
  A common left translation preserves `ρ` and adds a first-order cross product
  to the chart velocity.
  Logging the point again returns its chart vector. The logarithm of the rotor from the point to its
  left translate is `(cos 2χ, 0, sin 2χ)`, unequal to that velocity on `(0, π)`.
  Six axis intercepts are torque-free. For `0 < a < b < c` the principal moments are distinct, and
  one partner moved off the ray leaves a positive moment.
* `RacketFlip` — the separatrix `A sech(kt)`, `B tanh(kt)`, `C sech(kt)` of Euler's equations.
  The energy is `½ I₂ B²` and `L² = 2 E I₂`. The intermediate component vanishes only at `t = 0`.
  Only that axis has a positive linear rate, and a residual `ε < 1/6` waits
  longer than the crossing.
* `RacketThermal` — the uniform average of a signed sum of chart moments is zero, and the average
  of its square is the sum of the squares. The canonical weight is the product of three centered
  Gaussians of variances `1/(β Iᵢ)`, the normalized factor `exp(-β E)`. The mean gap is
  `(I₁ + I₃ - 2 I₂)/β`. Both signs of the gap, and the residuals in `(0, 1/6)`, have positive
  weight. No frequency of reversals is drawn from the weight.
* `RelationalPosition` — relative position is the rotor `ρ(a,b)=a⁻¹b`. It is not the intra-particle
  mismatch `Ω`. No position operator is claimed.
* `ChannelRange` — the same enhancement on two compactification radii. `Λ` is an input, and the
  comparison does not subtract the Coulomb coupling from `G`.
* `CliffordParallel` — the two Hopf families on the three-sphere. `H₀` is an input. No theorem
  asserts `dst_derives_lambda`, and none names which family the universe carries.
* `WeakLinearity` — at a fixed compactification radius the dual acceleration is linear in mass, and
  the mass-scaled relation is strictly subadditive.
* `NuclearLayer` — saturation density, binding energy per nucleon, and the pion-length window. The
  charged-pion mass over the proton mass lies strictly between `ε_6` and `ε_5`, equals no lattice
  floor, lies in the channel-length interval `(2/19, 9/28)`, and exceeds the proton Planck floor
  by more than `10³⁶`. That inclusion does not select a scattering scale. A floor at or below that
  Planck floor forces `N > 10¹⁹`. The estimate `A∼300` is an external heuristic. The oscillator
  counts `2`, `8`, `20` and the shifted counts `28`, `50`, `82`, `126` are seat arithmetic, not
  node indices, and the splitting is not derived.
* `NuclearLength` — the charged-pion Compton wavelength against laboratory caps. Not the definition
  of the sign-reversal scale.
* `SignReversal` — the sign-reversal scale `r₁` is an observational constant. The channel length is
  the definition `ℓ=2 x₁ r₁`. The mass ratio read from that length is `λ_p/ℓ`, strictly between
  `2/19` and `9/28` on the scattering window, above `ε_8` and below the lock `1/3`, and above
  `(16/3) α_G` by more than `10³⁶`. A meson mass is not an input. For `N ≤ 4` or `N ≥ 8` the ratio
  equals no lattice height `ε_N`. This ratio is not one graviton.
* `StrongChannel` — the rapidity threshold on `(π/4,π/2)`. The prefactor `κ`, a fusion rate, and
  the `1/v` law are not derived.
* `LengthRule` — both channels at once. Nothing here fixes `κ` or computes a binding.
* `BothChannels` — an unlike pair exerts both terms at every separation. Where the factors have the
  same sign, the separation-increasing force does not vanish.
* `ElectronExclusion` — two electrons above the Bohr radius repel electrically and attract
  gravitationally. The mass term is a fraction of the charge term strictly between `2398/10^46`
  and `2404/10^46`. Inside the first gravitational node, while the phase is still below `1`, the
  outward force exceeds `ke²/r²` only for a fractional depth below `164/100·10⁻⁴³`, and such a
  depth exists. For `0 < r₁ < 1` that depth is smaller than a radius above `52917` by more than
  `3×10⁴⁷`. No spin-statistics theorem is claimed.
* `SpinVersusExclusion` — spin reversal keeps the place and reverses the spin vector.
  One place occurs with opposite rays, and that joint state is the singlet. One ray
  occurs at the identity and at its antipode, and that joint state is not the singlet.
  The two ray arrangements share the three cosines. Above the Bohr radius the masses
  attract and a repeated ray is still not the singlet. No spin-statistics theorem is claimed.
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
  radii. The map `ℓ ↦ ℓ/Z` moves the nodes and is not the radius `a₀/Z`.
* `ElectronSquare` — on the square the midplane pair has no outer-well equilibrium. In the first
  repulsive shell there is exactly one restoring square.
* `ElectronHelium` — charge `Z>0` with `Z≠1` is not that square equilibrium wherever both factors
  are nonzero.
* `HeliumBody` — two electrons relative to a nucleus are two elements of the three-sphere.
  The three cosines classify the pair. They are not the laboratory separations. At an
  atomic separation the curvature of a galactic or cosmic compactification does not
  enter the force.
* `ElectronForce` — counted with attraction positive, the outer-well force strengthens with phase.
  No angular momentum is assigned, and no circular energy is formed.
* `ElectronDiscrete` — a dual step `2π/N` spaces the equal-scale phase by `π/N`. On `[π/4, 1]`,
  one such step from the first node keeps `|4x²/γ_s| < N`. One step before the node the force
  exceeds `π N/(4 s₁)`. The outer-well integral cut off one step short of the node is at most
  a constant plus `(1/s₀) log N`. The continuum pole is the limit that removes the step.
  A sample is not proved to stay a full step from the node, and the second node is not capped.
* `ElectronStanding` — the curvature of `e^{-r/a}` supplies the outward force `ℏ²/(m a r²)`.
  It meets the signed force once in the outer well, and the separation-increasing imbalance
  is positive at larger radius, so the balance is unstable and does not hold the electron.
  The decay `a₀ γ_s(α/2)` meets the signed force at the Bohr phase. The fractional
  shortening lies strictly between `13312/10⁹` and `13314/10⁹`, below the electron-to-proton
  mass ratio, and the first node lies strictly between `a₀/261` and `a₀/255`. The node is
  a divergence. No binding energy is derived.
* `LineWindow` — a rational bracket for `π` carries a rational window up to the real vacuum
  wavelength. It does not place an atomic radius.
* `OrbitClosure` — one revolution restores the orbital point and leaves the dual rotor at `-1`.
  That return contains no momentum. The plane-wave identity `pr=nℏ` does not select a radius.
* `ElectronNumbers` — the first node, the diagonal, the side, the one-electron extremum, and the
  second node stand in that order.
* `ElectronLength` — an outer-well radius caps `ℓ`. The radius `a₀/Z` is not an input.
* `Rutherford` — the electromagnetic scale on the SI stand-ins, and the head-on distance of a
  `7.69` MeV alpha particle on gold.
* `NeutronScatter` — outside the rapidity wall a neutron is pulled inward. A scattering length in
  femtometres is not derived.
* `ElectronCapacity` — diameter, cube, and seat counts. Those counts are not indices of the
  equal-scale nodes.
* `ElectronShape` — a seat is a pattern on directions, not a path.
* `ElectronAngular` — the square is the response of the pattern when its direction is turned,
  the degree times one more than the degree. It is not the angular momentum of an electron in
  circulation, and it does not place a radius. No fine-structure splitting is claimed.
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
* `ShellCollision` — a partner on the line of centres meets the electron of larger radius first.
  An impulse deposits `p²/(2m)` and does not enter `√(κ/m)`. A stiffer root has a higher frequency
  and, for the same impulse, a smaller amplitude. Two positive weights on two distinct frequencies
  have positive variance. On the printed square curvatures the diagonal wavelength
  exceeds the electron wavelength by a factor strictly between `45.07` and `45.08`.
  The equipartition ratio of two roots does not depend on temperature. The
  Larmor ratio `ν³/(e^{aν/T}-1)` of a higher frequency to a lower one is strictly increasing in `T`,
  and so is their weighted mean, which stays strictly between them. The mean of `x³/(eˣ-1)` lies
  strictly between `3` and `4`, above the maximum in `(5/2,3)`, and the shape has positive integral
  on `(1,2)` and on `(4,5)`. No collision rate is derived, and no root is retuned.
* `Lensing` — weak deflection by one thin shell. A repulsive shell has neither critical curve on
  its disk.
* `PhotonReturn` — a ray below the photon sphere has no turning point on the classical exterior. On
  either recorded ceiling the same ray turns inside the freeze. No boundary condition for a
  gravitational wave, and no late echo train.

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
* `BetaDecay` — replacement of one nucleon class. The quark charges are the unique rational
  solution of the two nucleon charges. On the external free-gap window the excess over the
  electron and the ratio to the electron mass stay inside the stated rationals, and the gap
  lies below the Coulomb energy at every reversal inside `1` fm. The chart moment ratio is
  `-2/3`. The weights, the absolute gap, and V--A are not derived.
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
