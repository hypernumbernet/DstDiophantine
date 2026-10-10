import DstDiophantine.Gravity.Identification
import DstDiophantine.Gravity.JTDictionary
import DstDiophantine.Gravity.GaugeDictionary
import DstDiophantine.Gravity.ClassicalSchwarzschild
import DstDiophantine.Gravity.LorentzGauge
import DstDiophantine.Gravity.Tetrad
import DstDiophantine.Gravity.NewtonFromLight
import DstDiophantine.Gravity.EventBoundary
import DstDiophantine.Gravity.CoulombFromDual
import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Gravity.CompactS3
import DstDiophantine.Gravity.TorsionalLayer
import DstDiophantine.Gravity.NuclearLayer
import DstDiophantine.Gravity.DualRotorDynamics
import DstDiophantine.Gravity.DualRotorRigidity
import DstDiophantine.Gravity.DualRotorFlow
import DstDiophantine.Gravity.DualRotorVacuum
import DstDiophantine.Gravity.DualRotorMotor
import DstDiophantine.Gravity.NullRotation
import DstDiophantine.Gravity.RestMass
import DstDiophantine.Gravity.ElectronOrbit
import DstDiophantine.Gravity.ElectronSquare
import DstDiophantine.Gravity.ElectronForce
import DstDiophantine.Gravity.ElectronCapacity
import DstDiophantine.Gravity.ElectronBoundary
import DstDiophantine.Gravity.ElectronWater
import DstDiophantine.Gravity.ElectronNegativity
import DstDiophantine.Gravity.ElectronDodeca
import DstDiophantine.Gravity.Blackbody
import DstDiophantine.Gravity.Faraday
import DstDiophantine.Gravity.Electroweak
import DstDiophantine.Gravity.CircularPolarization
import DstDiophantine.Gravity.DualControl
import DstDiophantine.Gravity.ShieldClock
import DstDiophantine.Gravity.ShieldCeiling
import DstDiophantine.Gravity.ControlDomain
import DstDiophantine.Gravity.EnvelopeLock
import DstDiophantine.Gravity.ChiralSpectrum
import DstDiophantine.Gravity.ChiralityStabilizer
import DstDiophantine.Gravity.EMControl
import DstDiophantine.Gravity.ParticleStability
import DstDiophantine.Gravity.BaryonAsymmetry
import DstDiophantine.Gravity.KillingAxis
import DstDiophantine.Gravity.RadialFall
import DstDiophantine.Gravity.Lensing
import DstDiophantine.Gravity.PhotonReturn

/-!
# Gravity / PGA–TEGR chart layer

Parallel track. Not re-exported from `DstDiophantine.Basic`.
Algebraic `J` is a dimensionless parameter-space scalar. It is not the
Weitzenböck density `T`, and it is not \(c^4/(G\,\ell_P^{-2})\).

No theorem asserts `dst_derives_G`, `dst_derives_a0`, `dst_derives_alpha_s`,
`dst_derives_lambda`, `dst_derives_lambdaN`, `dst_derives_Amax`, Maxwell's
equations, a Weinberg angle, \(W/Z\) masses, a chiral \(\mathrm{SU}(2)\),
a V--A coupling, a helicity-odd drive of \(J\), or a numerical baryon yield.

## Chart dictionary

`Coframe`, `Sandwich`, `Weitzenbock`, `Tetrad`, `Identification`,
`JTDictionary`, `GaugeDictionary`, `ClassicalSchwarzschild`, `LorentzGauge`.

On every static radial-boost chart,
\(T=(4/r^2)(\cosh\sqrt{2J}-1)\). The map inverts on the admissible cone,
where \(r^2 T\) lies in a finite two-sided window. A real radial boost
cannot produce \(T<0\). Exterior Schwarzschild is the vacuum gauge
\(A=1-r_s/r\). The naive identification \(J_{\mathrm{field}}=\tfrac12 T\)
holds on at most one sphere.

A pure boost of the inertial frame in a fixed plane, of any rapidity
profile \(\varphi(t,x)\), induces the Minkowski metric. Its coordinate
torsion is \(T^t{}_{tx}=\partial_t\varphi\) and \(T^x{}_{xt}=\partial_x\varphi\),
and the teleparallel quadratic vanishes for every jet. The same \(J=\tfrac12\varphi^2\)
is positive-\(T\) on the exterior Schwarzschild coframe, so no pointwise map
sends \(J\) to \(T\) for every tetrad. Distinct squared rapidities give the
same metric and distinct \(J\).

## The direction of gravity

`KillingAxis` reads the static Killing field at an event as the Poincaré
bivector \(K=\tfrac{\kappa}{2}B^{+}+\tfrac{\nu}{2}N_0\). It is the pure boost
\(\tfrac{\kappa}{2}B^{+}\) moved by the radial translator of length
\(\ell=\nu/\kappa\); its velocity vanishes only on that axis, and \(\exp(\tau K)\)
carries the observer on the hyperbola at interval \(\ell\) from it. On the
exterior chart \(\nu=\sqrt A\), \(\kappa=r_s/(2r^2)\) with \(r^2\kappa=r_s/2\),
and \(\ell\cdot\partial_r\sqrt A=1\), where \(\partial_r\sqrt A=T^0{}_{rt}\) is the
hover acceleration. The axis lies inward exactly when \(r_s>0\). It reaches the
observer at the horizon, where \(K\) is the pure boost of rate \(1/(2r_s)\), and
recedes to infinity far away, where \(K\) is the time translation. For any
Poincaré bivector the squared Killing norm has d'Alembertian \(8J\): it grows away
from a boost axis and shrinks away from a rotation axis. In the flat flow, the
inertial frame of release is \(\exp(-\tau K)\) as seen by the hoverer. A body
released from rest travels on \(s e_0\); at observer proper time \(\sigma\) its
separation is \(\ell(\operatorname{sech}(\sigma/\ell)-1)\), with initial
acceleration \(-1/\ell\), and it meets the light cone of the axis, where \(N=0\),
at proper time \(\ell\). Along that line the radial rapidity relative to the
local hovering observer obeys \(d\psi/ds=-\cosh\psi/\rho\), with
\(\rho=\sqrt{\ell^2-s^2}\), and at release this derivative is \(-1/\ell\).

`RadialFall` keeps that law on the exterior, with the chart distance
\(\ell(r)\) in place of \(\rho\) and with \(dr/d\tau=\sqrt{A}\sinh\psi\).
Differentiating cancels every power of the speed, so
\(d^2r/d\tau^2=-\kappa=-r_s/(2r^2)\). The energy
\(E=\sqrt{A}\cosh\psi\) is stationary, and on a proper-time interval
\((dr/d\tau)^2=E^2-A\). Release from rest at radius \(R\) gives \(E^2=A(R)\).
The straight line of one fixed jet is not itself that geodesic.

## Scales that are inputs

* `SI`, `NewtonFromLight` — SI stand-ins. The \(c\to G\) comparison does
  not derive \(G\).
* `EventBoundary` — the admissible ceiling read as a finite redshift floor.
  A one-way horizon \(A=0\) does not form on that chart.
* `CoulombFromDual`, `ElectronShell` — Coulombic stand-ins. Neither derives
  \(\alpha\) or \(\lambda\).
* `CompactS3` — \(v^2=(GM/R)\,f(r/R)\). The cotangent potential is radially
  harmonic, with Newtonian germ \(-GM/r+GMr/(3R^2)\). Unique minimum of \(f\)
  on \((0,\pi/2)\) with \(1.35<f_0<1.41\), and \(f<(11/10)f_0\) on \([1,6/5]\).
  The acceleration stays center-directed on \((0,\pi R)\); the negative well
  ends before \(r=2R\). Milky-Way window \(8\,\mathrm{kpc}<R<9\,\mathrm{kpc}\).
* `NuclearLayer` — saturation density, \(\mathrm{BE}/A\), and the
  pion-length window. Under \(\ell=\lambda_\pi\) every equal-scale node
  lies below \(1\,\mathrm{fm}\). The estimate \(A\sim 300\) is an external
  heuristic.
* `BaryonAsymmetry` — a vacuum excess of rapidity \(\delta\) along \(p\) has
  \(J=M=(\delta^2/2)\sum_a p_a^2\) on the boost side and \(J=-M\) on the
  rotation side, so \(J/M=\pm 1\) when both are nonzero. Both scalars are
  even in \(\delta\). On a one-axis balance of rapidity \(\varphi\), a boost
  shift has \(J=\varphi\delta+\delta^2/2\), and the two signs of \(\delta\)
  differ in mass by \(2\varphi\delta\). Both odd pieces vanish for every
  \(\delta\) precisely when \(\varphi=0\). Equal nonzero rapidities give
  \(J=0\), \(M=\varphi^2\), and a relative rotor different from \(1\).
  Spatial inversion sends the pseudoscalar to its negative, negates each
  boost generator, and fixes each rotation generator. On \(\mathbb{C}^2\)
  the dual rotor has determinant \(1\).
* `ParticleStability` — a balanced massive seed is not emptied by either
  rapidity budget alone. On the SI stand-ins, \(1836<m_p/m_e<1837\),
  a hundred nuclear bindings and twenty optical wells each lie below the
  proton rest energy, and hydrogen ionisation is \(\alpha^2/2\in
  (2,3)\times 10^{-5}\) of the electron rest energy, hence between
  \(3\times 10^4\) and \(5\times 10^4\) such ionisations.

## Layers and particle dynamics

* `TorsionalLayer` — equal-scale spectrum: exact derivative, plateaux
  \((-1)^n\cosh(n\pi)\), one node per \(\pi\)-interval in
  \((n\pi+\pi/4,\,n\pi+\pi/2)\), inward screening of the plateau force.
* `DualRotorDynamics` — Euler–Lagrange system of the written action: free
  mismatch \(\ddot\delta=0\), sourced common rapidity \(\ddot\sigma=-2m\delta\).
  The same-sign kinetic model is the oscillator \(\ddot\delta+2m\delta=0\).
  Dual-only \(\ddot\phi=0\) is a constraint, not a free solution, unless
  \(m(\phi-\theta)=0\).
* `DualRotorRigidity` — an arbitrary mismatch slope. Opposite kinetics
  still free \(\delta\); a frozen lag is inertial only at a critical
  point. Same-sign kinetics restore. The quartic \((\lambda/4)(\delta^2-v^2)^2\)
  is minimized at \(\delta=\pm v\), and its radial curvature \(4\lambda v^2\)
  is not a prescribed Compton value.
* `DualRotorFlow` — closed integrals of those jets. The written action is
  an affine lag with cubic common rapidity, and its Jacobi integral
  reduces to initial data. The neighbouring runaway at rate \(\kappa\)
  with \(\kappa^2=2m\) is hyperbolic and unbounded for a nonzero seed.
  The same-sign oscillator is harmonic, of squared amplitude \(A^2+B^2\).
  \(\sqrt{2m}\) meets the Compton frequency \(m\) only at \(m=0\) and
  \(m=2\).
* `DualRotorVacuum` — on one axis \(J=\delta\sigma/2\) and
  \(M=(\sigma^2+\delta^2)/4\). Written alignment keeps \(J=0\) while \(M\)
  coasts with \(\sigma^2/4\), stationary if and only if the common rate
  vanishes, and crosses \(M=0\) once when that rate is nonzero.
  A frozen well \(\delta=v\) carries \(J=v\sigma/2\); at rest it is
  balanced and massive, not free fall.
* `DualRotorMotor` — on one axis the factorised rotor splits the null
  ideal. The usual rapidity scales \(N_0\pm N_1\) by \(e^{\pm\phi}\); the
  dual angle rotates \((N_2,N_3)\). Along the written flow those
  parameters are \((\sigma+\delta)/2\) and \((\sigma-\delta)/2\), so the
  stiffness accelerates both planes and leaves their offset free. The
  relative rotor sees \(\phi\) and \(\theta\) separately. Its derivative
  at the identity retains \(\sigma\), and alignment with \(\sigma\neq 0\)
  still moves the boost plane. Off axis a usual generator and a dual
  generator anticommute, and \(p B^+_a+q B^-_b\) squares to \(p^2-q^2\).
  The sign of that scalar is one rotor: hyperbolic, elliptic, or
  parabolic. The parabolic rotor \(1+t(B^+_0+B^-_1)\) sends \(N_1\) to
  \(N_1+2t(N_0-N_3)\), which leaves the boost plane when \(t\neq 0\).
* `NullRotation` — that same generator lies in the Lorentz span. The
  truncations multiply by adding the parameter, and the opposite parameter
  is the reverse, so the shear preserves the Minkowski product. For
  \(t\neq 0\) the fixed vectors are the span of \(e_0-e_3\) and \(e_2\).
  Because \(e_4\) commutes with the Lorentz span, the null ideal carries
  the same coefficients. A translator \(1+s N_1\) adds \(e_4\).
* `RestMass` — stiffness \(V=(m/2)\sum(\alpha_a-\beta_a)^2\), unsigned
  mass \(M\), and free fall \(\Omega=1\) are three different quantities.
  On one axis \(V=2m(M-\sigma^2/4)\). For \(m\neq 0\), \(V=mJ\) if and
  only if the lag vanishes or the dual angle vanishes. A cross-axis
  shield has \(J=0\), \(M>0\), and \(V>0\). Vanishing stiffness does not
  force resonance. A frozen lag keeps \(V\) constant while \(J\) and \(M\)
  move whenever \(m\delta\neq 0\). Only the same-sign kinetic model
  restores the lag. No \(F=ma\) and no acceleration ceiling are claimed.
* `ElectronOrbit` — first Coulombic node in \((\pi/4,1)\). The zero is
  simple, and the equal-scale Coulomb potential falls logarithmically,
  without a lower bound, as the node is approached. Repulsive layers
  yield no real circular \(v^2\). Equal-scale \(r_2/r_1\) is not the Bohr
  ratio \(4\). Any strictly distance-decreasing equal phase places
  successive nodes inward, so they cannot coincide with the outward Bohr radii.
* `ElectronSquare` — on the square the two electrostatic components reduce
  to \(\gamma_s(\sqrt{2}x)=2\sqrt{2}\,\gamma_s(x)\). That balance is negative
  throughout the outer well. While the proton separation and the electron
  separation both lie in the outer well, the midplane pair has no equilibrium
  at any ratio of those separations. Opposite signs of the two factors
  likewise give no equilibrium. In the first repulsive shell the balance is
  strictly increasing and changes sign between \(3/2\) and \(8/5\), so there
  is exactly one such square.
* `ElectronForce` — counted with attraction positive, the electron–proton
  force \(4x^{2}/\gamma_s(x)\) is positive and strictly increasing on the
  outer well, and negative throughout the first repulsive shell. Inside that
  shell it has exactly one extremum,
  at a phase in \((5/2,\pi)\), so the radius lies in \((1/(2\pi),1/5)\).
  The outward magnitude there is strictly less than \(3\), while at \(x=\pi\)
  it is \(4\pi^{2}/\cosh\pi\), strictly greater than \(3\). On the outer well,
  \(d\ln Y/d\ln x<3\) exactly when \(\gamma_s(x)>2x\cosh x\sin x\). That
  comparison has one root, in \((1/2,3/5)\), so the radius lies in \((5/6,1)\).
  The root is not a zero of the electrostatic force. The energy of a
  circular path, kinetic term of the centripetal identity plus the
  outer-well potential, is strictly least there and is negative.
* `ElectronCapacity` — two electrons at the ends of a diameter have no radial
  balance in the outer well and exactly one in the first repulsive shell, for
  every nuclear charge \(Z\ge 1\). That point is an angular maximum. Eight
  electrons at the vertices of a cube likewise have exactly one radial balance
  in that shell, and the outward force restores the radius. Monopole, dipole,
  and traceless quadrupole modes have dimensions \(1\), \(3\), and \(5\); two
  complementary chiral seats give \(2\), \(8\), and \(18\). The traceless
  octupole has dimension \(7\), and the count through degree \(3\) is \(32\).
  These counts are not indices of the equal-scale nodes. Degree by degree the
  same seats number \(2\), \(6\), \(10\), and \(14\). Where the interference
  factor of a separation is positive, the antipode is an angular minimum.
* `ElectronBoundary` — the cube's far-field coefficient lies strictly between
  \(2\) and \(3\), so for every \(Z\ge 3\) the cube has no radial root in the
  outer well. The tetrahedron, the octahedron, and the icosahedron likewise
  keep every chord longer than the radius, and their coefficients lie strictly
  below \(1\), \(2\), and \(5\), so the same absence holds for every nuclear
  charge at least that large. Two electrons in the outer well, at any
  placement, are not simultaneously force-free once the nuclear charge is at
  least \(1/4\). The nearest chord of a regular dodecahedron is
  shorter than its radius, and the far-field coefficient of the twenty vertices
  lies strictly between \(15/2\) and \(8\). Before that chord meets the first
  node the response stays strictly above \(7\), so every nuclear charge
  \(Z\le 7\) is pushed outward on that whole interval. For every \(Z\ge 8\)
  the force is inward at large separation, and the response equals \(Z\) at
  exactly one phase before the chord meets the node. The radius there lies
  strictly between
  \(7\ell/10\) and \(10\ell/7\), and the outward force restores it. An unlike
  pair is driven toward the first node from both sides; a like pair is driven
  off it, and that repulsion is the wall of this shell.
* `ElectronWater` — the water skeleton places the nucleus at the origin and
  one proton on each of two rays, with one electron on each ray. While the
  electron–electron and proton–proton separations lie in the outer well and
  the cross factor is not a node, the tangential force on the electron and
  the tangential force on its proton do not vanish together at any angle
  strictly between ray coincidence and a straight line. On a straight line,
  with each electron between the nucleus and its proton, the sum of the
  outward forces is strictly negative whenever the nuclear charge is at
  least \(1/4\), both nucleus distances lie in the outer well, and the factor
  on the segment between them is not a node.
* `ElectronNegativity` — at one outer-well phase the pull is the nuclear charge
  times \(4x^{2}/\gamma_s\). A smaller charge outpulls a larger one only at a
  larger phase. On the segment between two positive charges, with separation
  phase strictly below \(x_1/2\), the net pull toward the first charge is
  strictly decreasing in the electron fraction and vanishes once. At the
  midpoint it is \((Z-W)\) times the unit pull. When \(Z>W\) the root lies
  strictly above \(1/2\), the side drawn toward \(Z\) is the longer side, and
  raising \(Z\) moves the root toward \(W\). The cancellation is not restored.
* `Blackbody` — on a harmonic ladder of spacing \(x>0\), in units of
  \(k_B T\), the mean number of quanta is \(1/(e^x-1)\). The mean energy
  above the ground state is less than one such unit, and the occupation is
  less than \(2e^{-x}\) once \(x\ge 1\). For \(n\ge 2\) the shape
  \(x^n/(e^x-1)\) has one positive maximum, in \((n-1,n)\): the frequency
  density peaks in \((5/2,3)\) and the wavelength density in \((9/2,5)\).
  The maximizing wavelength times the temperature is constant. The
  equipartition density \(T\nu^2\) has no maximum. The integral of
  \(x^3/(e^x-1)\) equals \(\pi^4/15\), so an enclosure whose modes grow as
  \(\nu^2\) scales as \(T^4\). The constants \(h\), \(k_B\), \(c\), and that
  mode growth are not roots of \(\gamma_s\).
* `Lensing` — weak deflection by one thin shell. Angles are in units of
  the shell's angular radius, and \(c=(b_m/R)^2\). The tangential ratio
  stays finite at the limb; the radial slope does not. An attractive shell
  has an interior radial critical curve exactly when \(c<2\), and an
  interior tangential curve exactly when \(1<c<2\), in which case the
  tangential curve lies outside the radial one. A repulsive shell has
  neither curve on its disk.
* `PhotonReturn` — a ray with \(b<b_c\) has no turning point on the
  classical exterior, and the Killing time down to \(r_s\) is unbounded.
  For \(r<r_s\) the classical factor is negative. On either recorded
  ceiling the same ray turns inside the freeze. The photon half-orbit
  lies between \(16\) and \(17\) in units of \(GM/c^3\); the shortest
  interior visit exceeds \(20\) on the one-axis saturation and \(280\)
  on the three-axis ceiling.

## One Faraday six-space

`Faraday`, `Electroweak`, `CircularPolarization`, `ChiralSpectrum`,
`ChiralityStabilizer`, `EMControl`.

Faraday coefficients occupy the dual-rotor generators: electric on the
boosts, magnetic on the rotations, \(F=F_{\mathrm{usual}}+F_{\mathrm{dual}}\).
Duality sends \((E,B)\) to \((B,-E)\) and has period 4. The usual–dual
parameter swap has period 2. Laboratory time reversal preserves \(J\).
The quadratic is \(J=\tfrac12(E^2-B^2)\). The first-order sandwich
increment is the commutator; on \(e_0+v\) it is the Lorentz 4-force of
\((E,-B)\). The outer product is not that increment.

A spatial axis splits the six-space into an \(\mathfrak{so}(2,1)\)
stabilizer and a complement that moves the axis. Distinct-axis projectors
do not resolve the identity. Compact \(\mathrm{SU}(2)\) here is the dual
rotor (\(IJ=K\)), not a symmetry of a fixed projector. In the parallel
plane, \(c_B B_a+c_E E_a\) preserves the axis only when \(c_E=0\).

`EMControl` reads a dual-only increment in two ways: magnetic superposition,
and the substitution \(\theta\mapsto\theta+eA\). Neither raises \(J\) against
a nonnegative dual seed. A circular potential drops mean \(J\) by the
helicity-even ponderomotive \((e^2/2)(E_0/\omega)^2\).

## Dual-only control of \((J,M)\)

`DualControl`, `ShieldClock`, `ShieldCeiling`, `ControlDomain`,
`EnvelopeLock`.

Dual-only motion conserves \(J+M\) and cannot raise \(J\). It reaches a
shield \(J=0\) precisely when the dual wall is nonpositive. The mass
ceiling is the parabola
\(M_{\mathrm{norm}}\le\frac56+\frac32 J_{\mathrm{norm}}^2\), sharp on
\(|J|\le\pi^2/8\). The exact image of the cone is the three-lobed envelope
of `ControlDomain`. That envelope is met only when every axis lies on the
wall and at least two axes are corners, so a dual-only motion meets it at
most once. On a boosted axis, \(\gamma_{\mathrm{eff}}\) returns to \(1\)
at a dual angle strictly before the coaxial shield; a cross-axis shield of
the same mass leaves that clock at \(\cosh\alpha\).
-/

namespace DstDiophantine

namespace Gravity

open Invariant PGA Generators Logic Operations

/-- Regression: closed-form dictionary \(T=(4/r^2)(\cosh\sqrt{2J}-1)\). -/
example {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      teleparallelTofJ (J (radialBoostParams rs r)) r :=
  schwarzschild_T_eq_teleparallelTofJ h

/-- Regression: the static Killing bivector is a boost about the inward axis at `ℓ`. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    KillingAxis.staticKilling rs r =
      Sandwich.sandwich (Motor.expTrans (KillingAxis.radialShift (KillingAxis.axisDistance rs r)))
        ((KillingAxis.killingRate rs r / 2) • hyperbolic 0) ∧
      KillingAxis.axisDistance rs r * dSqrtA_dr rs r = 1 :=
  ⟨KillingAxis.staticKilling_eq_sandwich h, KillingAxis.axisDistance_mul_dSqrtA_dr h⟩

/-- Regression: the d'Alembertian of the squared Killing norm is `8J`. -/
example (p : Motor.OmegaParams) (x : Fin 4 → ℝ) (t : ℝ) :
    ∑ μ : Fin 4, w31 μ * (KillingAxis.killingNormSq p (x + t • e4vec μ) +
        KillingAxis.killingNormSq p (x - t • e4vec μ) - 2 * KillingAxis.killingNormSq p x) =
      8 * J p.torsion * t ^ 2 :=
  KillingAxis.killingNormSq_dAlembertian p x t

/-- Regression: a body released from rest accelerates toward the axis at the hover rate. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    deriv (deriv (KillingAxis.releasedDisplacementProper (KillingAxis.axisDistance rs r))) 0 =
      -dSqrtA_dr rs r :=
  KillingAxis.released_initial_acceleration_exterior h

/-- Regression: on the exterior chart that meeting lies on the static horizon. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    KillingAxis.killingNormSq
        (KillingAxis.killingParams (KillingAxis.killingRate rs r) (KillingAxis.killingNorm rs r))
        (KillingAxis.releasedWorldline (KillingAxis.axisDistance rs r)) = 0 :=
  KillingAxis.released_on_staticHorizon h

/-- Regression: an inertial-plane boost keeps the Minkowski metric and kills `T`. -/
example (φ u v : ℝ) (μ ν : Fin 4) :
    inducedMetric (inertialBoostCoframe φ) μ ν =
        (if μ = ν then w31 μ else 0) ∧
      boostCoordTorsion φ u v 0 0 1 = u ∧
      boostTeleparallel u v = 0 :=
  ⟨inducedMetric_inertialBoost φ μ ν, boostCoordTorsion_ttx φ u v,
    boostTeleparallel_eq_zero u v⟩

/-- Regression: the same `J` does not determine `T` off the radial-boost gauge. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    J (DstDiophantine.Amplification.pureBoost (schwarzschildRapidity rs r)) =
        J (radialBoostParams rs r) ∧
      boostTeleparallel 0 0 = 0 ∧
      0 < schwarzschildTeleparallelT rs r :=
  sameJ_inertial_T_zero_schwarzschild_T_pos h

/-- Regression: the same dictionary holds for any static radial-boost gauge. -/
example {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofA A r =
      4 * (Real.cosh (Real.sqrt (2 * J (gaugeBoostParams A))) - 1) :=
  r_sq_T_ofA_eq_four_cosh_sqrt hA hr

/-- Regression: a real radial boost cannot produce \(T<0\). -/
example {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    ¬ teleparallelTofA A r < 0 :=
  teleparallelTofA_not_lt_zero hA hr

/-- Regression: \(T<0\) on the admissible cone requires the elliptic sector. -/
example {Jval r : ℝ} (hr : r ≠ 0)
    (hbound : |Jval| ≤ JMax) (hT : teleparallelTofJ Jval r < 0) :
    Jval < 0 :=
  repulsive_requires_negative_J hr hbound hT

/-- Regression: TEGR density dominates the algebraic density. -/
example {A r θ : ℝ} (hA : 0 < A) (hr : r ≠ 0) (hsin : 0 ≤ Real.sin θ) :
    algebraicDensity A r θ ≤ tegrDensity A r θ :=
  algebraicDensity_le_tegrDensity hA hr hsin

/-- Regression: sandwich \(4J\le r^2 T\) and \(T\le 4J_{\mathrm{field}}\). -/
example {rs r : ℝ} (h : IsExterior rs r) :
    4 * J (radialBoostParams rs r) ≤
      r ^ 2 * schwarzschildTeleparallelT rs r ∧
    schwarzschildTeleparallelT rs r ≤ 4 * J_field rs r :=
  ⟨four_J_le_r_sq_T h, T_le_four_J_field h⟩

/-- Regression: naive \(J_{\mathrm{field}}=\tfrac12 T\) holds on at most one sphere. -/
example {rs r1 r2 : ℝ}
    (h1 : IsExterior rs r1) (h2 : IsExterior rs r2)
    (heq1 : J_field rs r1 = (1 / 2) * schwarzschildTeleparallelT rs r1)
    (heq2 : J_field rs r2 = (1 / 2) * schwarzschildTeleparallelT rs r2) :
    r1 = r2 :=
  naive_half_ratio_at_most_one_sphere h1 h2 heq1 heq2

/-- Regression: admissible ceiling \(r^2 T\le 4(\cosh\varphi_{\max}-1)<27\). -/
example {rs r : ℝ} (h : IsExterior rs r)
    (hφ : schwarzschildRapidity rs r ≤ phiMax) :
    r ^ 2 * schwarzschildTeleparallelT rs r < 27 :=
  lt_of_le_of_lt (r_sq_T_le_ceiling h hφ) four_cosh_phiMax_sub_one_bounds.2

/-- Regression: on the admissible cone \(r^2 T\) lies in a finite two-sided window. -/
example {Jval r : ℝ} (hr : r ≠ 0) (hbound : |Jval| ≤ JMax) :
    4 * (Real.cos phiMax - 1) ≤ r ^ 2 * teleparallelTofJ Jval r ∧
      r ^ 2 * teleparallelTofJ Jval r ≤ 4 * (Real.cosh phiMax - 1) :=
  r_sq_teleparallelTofJ_window hr hbound

/-- Regression: numeric envelope of that window, \(-8<r^2 T<27\). -/
example {Jval r : ℝ} (hr : r ≠ 0) (hbound : |Jval| ≤ JMax) :
    -8 < r ^ 2 * teleparallelTofJ Jval r ∧
      r ^ 2 * teleparallelTofJ Jval r < 27 :=
  r_sq_teleparallelTofJ_bounds hr hbound

/-- Regression: both window ends are attained, so neither bound is improvable. -/
example {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofJ (-JMax) r = 4 * (Real.cos phiMax - 1) ∧
      r ^ 2 * teleparallelTofJ JMax r = 4 * (Real.cosh phiMax - 1) :=
  r_sq_teleparallelTofJ_window_sharp hr

/-- Regression: at a fixed radius the teleparallel density determines \(J\). -/
example {J₁ J₂ r : ℝ} (hr : r ≠ 0) (h₁ : |J₁| ≤ JMax) (h₂ : |J₂| ≤ JMax)
    (heq : teleparallelTofJ J₁ r = teleparallelTofJ J₂ r) : J₁ = J₂ :=
  J_unique_of_teleparallelTofJ_eq hr h₁ h₂ heq

/-- Regression: closed-form inversion of the dictionary on the exterior chart. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    (1 / 2) *
        Real.arcosh (1 + r ^ 2 * schwarzschildTeleparallelT rs r / 4) ^ 2 =
      J (radialBoostParams rs r) :=
  J_radialBoostParams_eq_half_arcosh_sq h

/-- Regression: exterior Schwarzschild is the vacuum specialisation of the gauge. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    HasDerivAt (fun x => x * schwarzschildA rs x) 1 r :=
  hasDerivAt_r_mul_schwarzschildA rs r (lt_trans h.1 h.2).ne'

/-- Regression: Newtonian sandwich and far-field coefficient. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    rs / (2 * r) ≤ schwarzschildRapidity rs r :=
  (schwarzschildRapidity_sandwich h).1

/-- Regression: exact witness \(r=\frac43 r_s\) has \(r^2 T=1\). -/
example {rs : ℝ} (hrs : 0 < rs) :
    referenceRadius rs ^ 2 *
      schwarzschildTeleparallelT rs (referenceRadius rs) = 1 :=
  r_sq_T_reference hrs

/-- Regression: the proper-time factor is strictly positive. -/
example (α β : ℝ) : 0 < gammaEff α β :=
  gammaEff_pos α β

/-- Regression: special relativity is the unexcited dual sector. -/
example (α : ℝ) : gammaEff α 0 = Real.cosh α :=
  gammaEff_sr_is_beta_zero α

/-- Regression: written Euler–Lagrange is a free mismatch and a sourced common channel. -/
example (m φ θ φddot θddot : ℝ) :
    PaperActualEL m φ θ φddot θddot ↔
      φddot - θddot = 0 ∧ φddot + θddot = -2 * m * (φ - θ) :=
  paperActualEL_iff_channels m φ θ φddot θddot

/-- Regression: written energy is conserved on the Euler–Lagrange jet. -/
example {m φ θ φdot θdot φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    paperEnergyDot m φ θ φdot θdot φddot θddot = 0 :=
  paperEnergy_conserved h

/-- Regression: written energy is indefinite. -/
example :
    (∃ m φ θ φdot θdot : ℝ, 0 < paperEnergy m φ θ φdot θdot) ∧
      (∃ m φ θ φdot θdot : ℝ, paperEnergy m φ θ φdot θdot < 0) :=
  paperEnergy_indefinite

/-- Regression: the cubic flow solves the written Euler–Lagrange system. -/
example (σ₀ σd₀ m δ₀ ν t : ℝ) :
    PaperActualEL m (writtenUsual σ₀ σd₀ m δ₀ ν t) (writtenDual σ₀ σd₀ m δ₀ ν t)
      (deriv (deriv (writtenUsual σ₀ σd₀ m δ₀ ν)) t)
      (deriv (deriv (writtenDual σ₀ σd₀ m δ₀ ν)) t) :=
  written_flow_actualEL σ₀ σd₀ m δ₀ ν t

/-- Regression: one-axis stiffness is \(2m(M-\sigma^2/4)\), not \(J\). -/
example (m α β : ℝ) :
    stiffnessPotential m (RelativeRotor.axisParams α β) =
      2 * m * (mass (RelativeRotor.axisParams α β) - (α + β) ^ 2 / 4) :=
  stiffness_axis_massShift m α β

/-- Regression: coasting alignment keeps \(J=0\) and lets the mass run with \(\sigma^2\). -/
example (σ₀ σd₀ m t : ℝ) :
    J (RelativeRotor.axisParams (writtenUsual σ₀ σd₀ m 0 0 t)
        (writtenDual σ₀ σd₀ m 0 0 t)) = 0 ∧
      mass (RelativeRotor.axisParams (writtenUsual σ₀ σd₀ m 0 0 t)
        (writtenDual σ₀ σd₀ m 0 0 t)) =
        (σ₀ + σd₀ * t) ^ 2 / 4 :=
  ⟨written_aligned_J σ₀ σd₀ m t, written_aligned_mass σ₀ σd₀ m t⟩

/-- Regression: the written flow splits null translations into a boost by
\((\sigma+\delta)/2\) and a rotation by \((\sigma-\delta)/2\). -/
example (σ₀ σd₀ m δ₀ ν t : ℝ) :
    writtenUsual σ₀ σd₀ m δ₀ ν t =
        (writtenSigma σ₀ σd₀ m δ₀ ν t + writtenDelta δ₀ ν t) / 2 ∧
      writtenDual σ₀ σd₀ m δ₀ ν t =
        (writtenSigma σ₀ σd₀ m δ₀ ν t - writtenDelta δ₀ ν t) / 2 ∧
      Sandwich.sandwich (Motor.rotorTorsion (RelativeRotor.axisParams
          (writtenUsual σ₀ σd₀ m δ₀ ν t) (writtenDual σ₀ σd₀ m δ₀ ν t)))
        (Generators.null 0 + Generators.null 1) =
          Real.exp (writtenUsual σ₀ σd₀ m δ₀ ν t) •
            (Generators.null 0 + Generators.null 1) ∧
      Sandwich.sandwich (Motor.rotorTorsion (RelativeRotor.axisParams
          (writtenUsual σ₀ σd₀ m δ₀ ν t) (writtenDual σ₀ σd₀ m δ₀ ν t)))
        (Generators.null 2) =
          Real.cos (writtenDual σ₀ σd₀ m δ₀ ν t) • Generators.null 2 +
            Real.sin (writtenDual σ₀ σd₀ m δ₀ ν t) • Generators.null 3 :=
  written_flow_null_split σ₀ σd₀ m δ₀ ν t

/-- Regression: off axis, equal coefficients truncate, and the shear leaves the boost plane. -/
example {t : ℝ} (ht : t ≠ 0) :
    NormedSpace.exp (t • (hyperbolic 0 + cyclic 1)) =
        (1 : PGA) + t • (hyperbolic 0 + cyclic 1) ∧
      Sandwich.sandwich ((1 : PGA) + t • (hyperbolic 0 + cyclic 1)) (null 1) =
        null 1 + (2 * t) • null 0 - (2 * t) • null 3 ∧
      ∀ c₀ c₁ : ℝ,
        Sandwich.sandwich ((1 : PGA) + t • (hyperbolic 0 + cyclic 1)) (null 1) ≠
          c₀ • null 0 + c₁ • null 1 :=
  ⟨exp_offAxis_sum (by decide) t, sandwich_parabolic_null1 t,
    sandwich_parabolic_null1_not_boostPlane ht⟩

/-- Regression: the parabolic truncation is a null rotation, and a translator adds \(e_4\). -/
example (t : ℝ) :
    Sandwich.sandwich ((1 : PGA) + t • parabolicGen) (ι 0 - ι 3) = ι 0 - ι 3 ∧
      Sandwich.sandwich ((1 : PGA) + t • parabolicGen) (ι 2) = ι 2 ∧
        Sandwich.sandwich ((1 : PGA) + t • parabolicGen) (ι 1) =
          ι 1 + (2 * t) • (ι 0 - ι 3) ∧
          Sandwich.sandwich ((1 : PGA) + t • parabolicGen) (ι 0 + ι 3) =
            ι 0 + ι 3 + (4 * t) • ι 1 + (4 * t ^ 2) • (ι 0 - ι 3) ∧
            Sandwich.sandwich (Motor.expTrans ⟨![0, t, 0, 0]⟩) (ι 1) =
              ι 1 + t • ι e4Index ∧
              parabolicGen ∉ nullSpan :=
  ⟨sandwich_parabolic_fixedNull t, sandwich_parabolic_e2 t,
    sandwich_parabolic_e1_shear t, sandwich_parabolic_nullPlus_shear t,
    sandwich_translator_e1 t, parabolicGen_not_mem_nullSpan⟩

/-- Regression: null rotations are a one-parameter group of Minkowski isometries,
and the null ideal transforms by the same coefficients. -/
example (t s : ℝ) (x y : Fin 4 → ℝ) :
    parabolicRotor t * parabolicRotor s = parabolicRotor (t + s) ∧
      CliffordAlgebra.reverse (parabolicRotor t) = parabolicRotor (-t) ∧
        parabolicRotor t * CliffordAlgebra.reverse (parabolicRotor t) = 1 ∧
          Q31 (nullRotation t x) = Q31 x ∧
            KillingAxis.minkowskiProd (nullRotation t x) (nullRotation t y) =
              KillingAxis.minkowskiProd x y ∧
              Sandwich.sandwich (parabolicRotor t) (nullVector x) =
                nullVector (nullRotation t x) ∧
                Sandwich.sandwich (parabolicRotor t) (null 0 - null 3) = null 0 - null 3 ∧
                  Sandwich.sandwich (parabolicRotor t) (null 2) = null 2 :=
  ⟨parabolicRotor_mul t s, reverse_parabolicRotor t, parabolicRotor_mul_reverse t,
    Q31_nullRotation t x, minkowskiProd_nullRotation t x y,
    sandwich_parabolic_nullVector t x, sandwich_parabolic_null_fixedLine t,
    sandwich_parabolic_null2_fixed t⟩

/-- Regression: a nonzero null rotation fixes only the null line and \(e_2\). -/
example {t : ℝ} (ht : t ≠ 0) (x : Fin 4 → ℝ) :
    nullRotation t x = x ↔ ∃ a b : ℝ, x = a • nullLineVec + b • transverseVec :=
  nullRotation_eq_self_iff ht x

/-- Regression: the Jacobi integral of the cubic flow is initial data. -/
example (σ₀ σd₀ m δ₀ ν t : ℝ) :
    paperEnergy m (writtenUsual σ₀ σd₀ m δ₀ ν t) (writtenDual σ₀ σd₀ m δ₀ ν t)
        (deriv (writtenUsual σ₀ σd₀ m δ₀ ν) t)
        (deriv (writtenDual σ₀ σd₀ m δ₀ ν) t) =
      (1 / 2) * ν * σd₀ + (m / 2) * δ₀ ^ 2 :=
  written_flow_energy σ₀ σd₀ m δ₀ ν t

/-- Regression: \(\sqrt{2m}\) meets the Compton frequency only at \(m=0,2\). -/
example {m : ℝ} (hm : 0 ≤ m) :
    Real.sqrt (2 * m) = m ↔ m = 0 ∨ m = 2 :=
  sqrt_two_mul_eq_compton_iff hm

/-- Regression: same-sign oscillator frees the common rapidity. -/
example {m φ θ φddot θddot : ℝ}
    (h : OscillatorEL m φ θ φddot θddot) :
    φddot + θddot = 0 :=
  oscillatorEL_free_common h

/-- Regression: exact derivative of the equal-scale interference factor. -/
example (x : ℝ) :
    HasDerivAt gammaSEqual (-2 * Real.cosh x * Real.sin x) x :=
  hasDerivAt_gammaSEqual x

/-- Regression: critical points are exactly the zeros of `sin`. -/
example (x : ℝ) : deriv gammaSEqual x = 0 ↔ Real.sin x = 0 :=
  deriv_gammaSEqual_eq_zero_iff x

/-- Regression: plateau amplitudes are `(-1)^n cosh(nπ)`. -/
example (n : ℕ) :
    gammaSEqual ((n : ℝ) * Real.pi) = (-1) ^ n * Real.cosh ((n : ℝ) * Real.pi) :=
  gammaSEqual_nat_mul_pi n

/-- Regression: exactly one torsional node per `π`-interval. -/
example (n : ℕ) :
    ∃! x : ℝ,
      x ∈ Set.Ioo ((n : ℝ) * Real.pi) ((n : ℝ) * Real.pi + Real.pi) ∧
        gammaSEqual x = 0 :=
  exists_unique_node_branch n

/-- Regression: sharpened branch localisation of a node. -/
example (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo ((n : ℝ) * Real.pi) ((n : ℝ) * Real.pi + Real.pi))
    (h : gammaSEqual x = 0) :
    x ∈ Set.Ioo ((n : ℝ) * Real.pi + Real.pi / 4)
      ((n : ℝ) * Real.pi + Real.pi / 2) :=
  node_mem_sharp_branch n hx h

/-- Regression: layer radius window from the sharpened branch. -/
example {ℓ x : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (hx : x ∈ Set.Ioo ((n : ℝ) * Real.pi + Real.pi / 4)
      ((n : ℝ) * Real.pi + Real.pi / 2)) :
    ℓ / ((2 * (n : ℝ) + 1) * Real.pi) < layerRadius ℓ x ∧
      layerRadius ℓ x < 2 * ℓ / ((4 * (n : ℝ) + 1) * Real.pi) :=
  layerRadius_window hℓ n hx

/-- Regression: amplitudes grow at least like `11^n`. -/
example (n : ℕ) : (11 : ℝ) ^ n ≤ Real.cosh ((n : ℝ) * Real.pi) :=
  eleven_pow_le_cosh_nat_mul_pi n

/-- Regression: per-layer amplification never reaches `e^π`. -/
example (a : ℝ) : Real.cosh (a + Real.pi) < Real.exp Real.pi * Real.cosh a :=
  cosh_add_pi_lt_exp_pi_mul a

/-- Regression: exact shortfall below the `e^π` ceiling. -/
example (a : ℝ) :
    Real.exp Real.pi * Real.cosh a - Real.cosh (a + Real.pi) =
      Real.sinh Real.pi * Real.exp (-a) :=
  exp_pi_mul_cosh_sub_cosh_add_pi a

/-- Regression: the amplification ratio is strictly increasing. -/
example {a b : ℝ} (hab : a < b) :
    Real.cosh (a + Real.pi) * Real.cosh b <
      Real.cosh (b + Real.pi) * Real.cosh a :=
  cosh_add_pi_ratio_strictMono hab

/-- Regression: plateau amplitudes grow no faster than `e^{nπ}`. -/
example (n : ℕ) :
    Real.cosh ((n : ℝ) * Real.pi) ≤ Real.exp ((n : ℝ) * Real.pi) :=
  cosh_nat_mul_pi_le_exp n

/-- Regression: the mid-layer force factor decreases inward. -/
example (n : ℕ) (hn : 1 ≤ n) :
    plateauForceFactor (n + 1) < plateauForceFactor n :=
  plateauForceFactor_strictAnti n hn

/-- Regression: the equal-scale locus is the balanced locus `J = 0`. -/
example (α : Fin 3 → ℝ) : J (equalScaleParams α) = 0 :=
  J_equalScaleParams α

/-- Regression: that locus is nonetheless massive. -/
example {α : Fin 3 → ℝ} (h : ∃ a, α a ≠ 0) : 0 < mass (equalScaleParams α) :=
  mass_equalScaleParams_pos h

/-- Regression: under `ℓ = λ_π` every node sits below `1` fm. -/
example (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo ((n : ℝ) * Real.pi + Real.pi / 4)
      ((n : ℝ) * Real.pi + Real.pi / 2)) :
    layerRadius (pionComptonFm : ℝ) x < 1 :=
  pionLambda_node_lt_one_fm n hx

/-- Regression: a `1`-fm outermost node forces `ℓ > π/2` fm. -/
example {ℓ x : ℝ} (hℓ : 0 < ℓ)
    (hx : x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2))
    (h1 : 1 ≤ layerRadius ℓ x) : Real.pi / 2 < ℓ :=
  outer_node_one_fm_forces_ell_gt_pi_div_two hℓ hx h1

/-- Regression: constant nucleon density is exactly the `A^{1/3}` radius law. -/
example {r0 s : ℝ} (hr0 : r0 ≠ 0) (hs : s ≠ 0) :
    nucleonNumberDensity r0 s = numberDensityOfRadiusCoeff r0 :=
  nucleonNumberDensity_eq_const hr0 hs

/-- Regression: `r₀ = 1.2` fm is not consistent with `n₀ = 0.16` fm⁻³. -/
example : numberDensityOfRadiusCoeff (6 / 5) ≠ 4 / 25 :=
  numberDensity_radiusCoeff_1_2_ne_saturation

/-- Regression: a diameter has one radial balance in the first repulsive shell. -/
example : ∃! x : ℝ, x ∈ Set.Ioo (2 * resonanceRoot1) (branchNode 1) ∧
    pairBalance 1 x = 0 :=
  exists_unique_diameter_shell (by norm_num)

/-- Regression: for `Z ≥ 3` a cube has no radial root in the outer well. -/
example {Z x : ℝ} (hZ : 3 ≤ Z) (hx : x ∈ Set.Ioo (0 : ℝ) resonanceRoot1) :
    cubeOutward Z x < 0 :=
  cube_no_outer_root hZ hx

/-- Regression: for `Z ≥ 1` a tetrahedron has no radial root in the outer well. -/
example {Z x : ℝ} (hZ : 1 ≤ Z) (hx : x ∈ Set.Ioo (0 : ℝ) resonanceRoot1) :
    tetraOutward Z x < 0 :=
  tetra_no_outer_root hZ hx

/-- Regression: for `Z ≥ 2` an octahedron has no radial root in the outer well. -/
example {Z x : ℝ} (hZ : 2 ≤ Z) (hx : x ∈ Set.Ioo (0 : ℝ) resonanceRoot1) :
    octaOutward Z x < 0 :=
  octa_no_outer_root hZ hx

/-- Regression: for `Z ≥ 5` an icosahedron has no radial root in the outer well. -/
example {Z x : ℝ} (hZ : 5 ≤ Z) (hx : x ∈ Set.Ioo (0 : ℝ) resonanceRoot1) :
    icosaOutward Z x < 0 :=
  icosa_no_outer_root hZ hx

/-- Regression: a dodecahedron of charge `Z ≥ 8` has one restoring root,
at a radius strictly between `7ℓ/10` and `10ℓ/7`. -/
example {Z : ℝ} (hZ : 8 ≤ Z) :
    ∃! x : ℝ, x ∈ Set.Ioo (0 : ℝ) dodecaWall ∧ dodecaResponse x = Z :=
  exists_unique_dodeca_outer_root hZ

example {Z x : ℝ} (hZ : 8 ≤ Z) (hx : x ∈ Set.Ioo (0 : ℝ) dodecaWall)
    (hR : dodecaResponse x = Z) :
    (7 : ℝ) / 10 < 1 / (2 * x) ∧ 1 / (2 * x) < 10 / 7 ∧
      (∀ y ∈ Set.Ioo (0 : ℝ) dodecaWall,
        (y < x → dodecaOutward Z y < 0) ∧ (y = x → dodecaOutward Z y = 0) ∧
          (x < y → 0 < dodecaOutward Z y)) :=
  ⟨(dodeca_outer_root_radius hZ hx hR).1, (dodeca_outer_root_radius hZ hx hR).2,
    fun _ hy => dodeca_outer_root_restoring hZ hx hR hy⟩

/-- Regression: the dodecahedral coefficient lies strictly between `15/2` and `8`. -/
example : (15 / 2 : ℝ) < dodecaCoeff ∧ dodecaCoeff < 8 :=
  ⟨dodecaCoeff_gt_fifteen_halves, dodecaCoeff_lt_eight⟩

/-- Regression: for `Z ≤ 7` a dodecahedron is pushed outward before the chord node. -/
example {Z x : ℝ} (hZ : Z ≤ 7) (hx : x ∈ Set.Ioo (0 : ℝ) dodecaWall) :
    7 < dodecaResponse x ∧ 0 < dodecaOutward Z x :=
  ⟨dodecaResponse_gt_seven hx, dodeca_outward_pos_of_le_seven hZ hx⟩

/-- Regression: for `Z ≥ 8` the dodecahedral far field is inward. -/
example {Z : ℝ} (hZ : 8 ≤ Z) :
    ∃ a ∈ Set.Ioo (0 : ℝ) dodecaWall, ∀ x ∈ Set.Ioo (0 : ℝ) a, dodecaOutward Z x < 0 :=
  dodeca_far_field_inward hZ

section
open MeasureTheory

/-- Regression: wavelength peak in `(9/2,5)`, frequency peak in `(5/2,3)`,
and the Bose integral `\pi^4/15`. -/
example :
    (9 / 2 : ℝ) < planckPeak 5 ∧ planckPeak 5 < 5 ∧
      (5 / 2 : ℝ) < planckPeak 3 ∧ planckPeak 3 < 3 ∧
      ∫ x in Set.Ioi (0 : ℝ), planckShape 3 x = Real.pi ^ 4 / 15 :=
  ⟨wavelengthPeak_bounds.1, wavelengthPeak_bounds.2,
    frequencyPeak_bounds.1, frequencyPeak_bounds.2, boseIntegral⟩

end

/-- Regression: a cube has one radial balance in the first repulsive shell. -/
example : ∃! x : ℝ, x ∈ Set.Ioo (2 * resonanceRoot1) (branchNode 1) ∧
    cubeOutward 1 x = 0 :=
  exists_unique_cube_shell (by norm_num)

/-- Regression: two chiral seats through the quadrupole and the octupole. -/
example : 2 * (Module.finrank ℝ ℝ + Module.finrank ℝ (Fin 3 → ℝ) +
    Module.finrank ℝ Gravity.quadrupole) = 18 ∧
    2 * (Module.finrank ℝ ℝ + Module.finrank ℝ (Fin 3 → ℝ) +
      Module.finrank ℝ Gravity.quadrupole + Module.finrank ℝ Gravity.octupole) = 32 := by
  simpa using shell_seat_counts.2.2

/-- Regression: the seats on one degree number `2`, `6`, `10`, and `14`. -/
example : 2 * Module.finrank ℝ ℝ = 2 ∧
    2 * Module.finrank ℝ (Fin 3 → ℝ) = 6 ∧
    2 * Module.finrank ℝ Gravity.quadrupole = 10 ∧
    2 * Module.finrank ℝ Gravity.octupole = 14 :=
  subshell_seat_counts

/-- Regression: the midplane pair has no outer-well balance at any ratio. -/
example {ℓ R ρ : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hρ : 0 < ρ)
    (hRwell : ℓ / (2 * R) ∈ Set.Ioo (0 : ℝ) resonanceRoot1)
    (hEwell : ℓ / (2 * (2 * ρ)) ∈ Set.Ioo (0 : ℝ) resonanceRoot1) :
    ¬ (covalentAxial ℓ R ρ = 0 ∧ covalentRadial ℓ R ρ = 0) :=
  no_midplane_outer_equilibrium hℓ hR hρ hRwell hEwell

/-- Regression: in the outer well the antipode is an angular minimum. -/
example {k e γ r : ℝ} (hr : 0 < r) (hk : 0 < k) (he : e ≠ 0) (hγ : 0 < γ) :
    0 < likePairEnergySlope k e γ (2 * r) *
      deriv (deriv (pairSeparation r)) Real.pi :=
  antipode_energy_curvature_pos hr hk he hγ

/-- Regression: two electrons in the outer well do not balance for `Z ≥ 1/4`. -/
example {Z : ℝ} {a b : Fin 3 → ℝ} (hZ : (1 / 4 : ℝ) ≤ Z)
    (ha : outerSep (vnorm a)) (hb : outerSep (vnorm b))
    (hd : outerSep (vnorm (vsub a b))) :
    ¬ ((∀ i, twoForce Z a b i = 0) ∧ (∀ i, twoForce Z b a i = 0)) :=
  two_electron_no_outer_balance hZ ha hb hd

/-- Regression: the water skeleton has no outer tangential balance. -/
example {Z r R θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (hr : 0 < r) (hR : 0 < R) (hne : r ≠ R)
    (hee : outerSep (2 * r * Real.sin (θ / 2)))
    (hhh : outerSep (2 * R * Real.sin (θ / 2)))
    (hc : gammaSEqual (pairPhase
      (Real.sqrt (r ^ 2 + R ^ 2 - 2 * r * R * Real.cos θ))) ≠ 0) :
    ¬ (waterBendElectron Z r R (θ / 2) = 0 ∧ waterBendProton Z r R (θ / 2) = 0) :=
  water_no_outer_tangent hθ hr hR hne hee hhh hc

/-- Regression: the outer-well cancellation lies toward the smaller charge. -/
example {Z W φ t : ℝ} (hW : 0 < W) (hZ : W < Z)
    (hφ : φ ∈ Set.Ioo 0 (resonanceRoot1 / 2))
    (ht : t ∈ segmentSlot φ) (h0 : segmentPull Z W φ t = 0) :
    1 / 2 < t ∧
      (1 - φ / resonanceRoot1) - t < t - φ / resonanceRoot1 ∧
      0 < segmentPull Z W φ (1 / 2) := by
  refine ⟨segmentRoot_gt_half hW hZ hφ ht h0,
    larger_charge_longer_reach hW hZ hφ ht h0, ?_⟩
  rw [segmentPull_midpoint]
  have h2 : 2 * φ ∈ Set.Ioo 0 resonanceRoot1 :=
    ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  exact mul_pos (sub_pos.mpr hZ) (pairAttraction_pos_outer h2)

/-- Regression: the segment has one cancellation. -/
example {Z W φ : ℝ} (hZ : 0 < Z) (hW : 0 < W)
    (hφ : φ ∈ Set.Ioo 0 (resonanceRoot1 / 2)) :
    ∃! t : ℝ, t ∈ segmentSlot φ ∧ segmentPull Z W φ t = 0 :=
  exists_unique_segmentPull hZ hW hφ

/-- Regression: a smaller charge outpulls a larger one only at a larger phase. -/
example {Z W x y : ℝ} (hZ : 0 < Z) (hW : Z < W)
    (hx : x ∈ Set.Ioo 0 resonanceRoot1) (hy : y ∈ Set.Ioo 0 resonanceRoot1)
    (hp : W * pairAttraction y < Z * pairAttraction x) :
    y < x :=
  weaker_charge_closer hZ hW hx hy hp

/-- Regression: on the straight water skeleton the outward sum is negative. -/
example {Z r R : ℝ} (hZ : (1 / 4 : ℝ) ≤ Z) (hr : outerSep r) (hR : outerSep R)
    (hrR : r < R) (hgap : gammaSEqual (pairPhase (R - r)) ≠ 0) :
    waterStraightElectron Z r R + waterStraightProton Z r R < 0 :=
  water_straight_sum_neg hZ hr hR hrR hgap

/-- Regression: first Coulombic node lies in \((\pi/4,1)\). -/
example : Real.pi / 4 < resonanceRoot1 ∧ resonanceRoot1 < 1 :=
  firstNode_window

/-- Regression: the first repulsive shell has one force extremum in `(5/2, π)`. -/
example : ∃! x : ℝ, x ∈ Set.Ioo (5 / 2) Real.pi ∧ forceCrit x = 0 :=
  exists_unique_forceQuiet

/-- Regression: that extremum is weaker than the outward value at `π`. -/
example {x : ℝ} (hx : x ∈ Set.Ioo (5 / 2) Real.pi) (h0 : forceCrit x = 0) :
    -3 < pairAttraction x ∧ pairAttraction x < 0 ∧ pairAttraction Real.pi < -3 :=
  ⟨(forceQuiet_magnitude hx h0).1, (forceQuiet_magnitude hx h0).2,
    pairAttraction_pi_lt_neg_three⟩

/-- Regression: attraction strengthens with phase throughout the outer well. -/
example : StrictMonoOn pairAttraction (Set.Ioo (0 : ℝ) resonanceRoot1) :=
  pairAttraction_strictMono_outer

/-- Regression: a circular path in the outer well changes stability once, in `(1/2, 3/5)`. -/
example : ∃! x : ℝ, x ∈ Set.Ioo (1 / 2) (3 / 5) ∧ circStable x = 0 :=
  exists_unique_circStable

/-- Regression: that phase has radius strictly between `5/6` and `1`. -/
example {x : ℝ} (hx : x ∈ Set.Ioo (1 / 2) (3 / 5)) :
    5 / 6 < 1 / (2 * x) ∧ 1 / (2 * x) < 1 :=
  circStable_radius hx

/-- Regression: circular-path energy is negative and least at that phase. -/
example {x y : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) resonanceRoot1)
    (hy : y ∈ Set.Ioo (1 / 2) (3 / 5)) (h0 : circStable y = 0) :
    circEnergy y < 0 ∧ circEnergy y ≤ circEnergy x ∧
      (circEnergy x = circEnergy y ↔ x = y) :=
  circEnergy_least_outer hx hy h0

/-- Regression: repulsive Coulombic layers yield no real circular speed. -/
example {k e m γs r : ℝ} (hk : 0 < k) (he : e ≠ 0) (hm : 0 < m)
    (hγ : γs < 0) (hr : 0 < r) :
    circularSpeedSq k e m γs r < 0 :=
  circularSpeedSq_neg_of_repulsive hk he hm hγ hr

/-- Regression: equal-scale radius ratio cannot equal the Bohr ratio \(4\). -/
example {x₂ : ℝ} (hx₂ : x₂ ∈ Set.Ioo (Real.pi + Real.pi / 4) (Real.pi + Real.pi / 2)) :
    resonanceRoot1 / x₂ ≠ bohrShellRadius 2 / bohrShellRadius 1 :=
  equalScale_ratio_ne_bohr hx₂

/-- Regression: a decreasing equal phase cannot place successive Bohr shells on successive nodes. -/
example {ρ : ℝ → ℝ} {n k : ℕ} (hk : 0 < k) (hanti : StrictAntiOn ρ (Set.Ioi 0))
    (hr : ρ (bohrShellRadius k) = 2 * branchNode n)
    (hs : ρ (bohrShellRadius (k + 1)) = 2 * branchNode (n + 1)) : False :=
  equalScale_successive_nodes_ne_bohr hk hanti hr hs

/-- Regression: \(\ell\mapsto\ell/Z\) contracts every equal-scale radius. -/
example {ℓ Z x : ℝ} (hZ : Z ≠ 0) :
    layerRadius (ℓ / Z) x = layerRadius ℓ x / Z :=
  Z_contracts_layerRadius hZ

/-- Regression: Faraday splits as usual electric plus dual magnetic. -/
example (p : FaradayParams) :
    faraday p = faradayUsual p + faradayDual p :=
  faraday_eq_add p

/-- Regression: duality sends \((E,B)\) to \((B,-E)\). -/
example (p : FaradayParams) :
    Operations.dual (faraday p) = faraday (dualFaradayParams p) :=
  dual_faraday p

/-- Regression: the Faraday quadratic is the torsional scalar. -/
example (p : FaradayParams) :
    J (toTorsion p) = (1 / 2) * (energySq p - magneticSq p) :=
  J_faraday p

/-- Regression: a circular snapshot with helicity \(\pm 1\) is null and massive. -/
example {E0 : ℝ} (hE : E0 ≠ 0) :
    J (toTorsion (circularSnapshot 1 E0)) = 0 ∧
      0 < mass (toTorsion (circularSnapshot 1 E0)) :=
  ⟨(circularSnapshot_J (by norm_num : (1 : ℝ) ^ 2 = 1)),
    circularSnapshot_mass_pos (by norm_num) hE⟩

/-- Regression: Hodge duality flips \(J\); laboratory \(T\) does not. -/
example (p : FaradayParams) :
    J (toTorsion (dualFaradayParams p)) = -J (toTorsion p) ∧
      J (toTorsion (timeReverseFaradayParams p)) = J (toTorsion p) :=
  ⟨J_dualFaraday p, J_timeReverse p⟩

/-- Regression: Hodge, parameter swap, and laboratory \(T\) are pairwise distinct. -/
example :
    dualFaradayParams (pureE 1) ≠ swapFaradayParams (pureE 1) ∧
      dualFaradayParams (pureE 1) ≠ timeReverseFaradayParams (pureE 1) ∧
      swapFaradayParams (pureE 1) ≠ timeReverseFaradayParams (pureE 1) :=
  ⟨dual_ne_swap_of_pureE, dual_ne_timeReverse_of_pureE, swap_ne_timeReverse_of_pureE⟩

/-- Regression: Hodge duality has period 4 on the Faraday bivector. -/
example (p : FaradayParams) :
    Operations.dual (Operations.dual (faraday p)) = -faraday p :=
  dual_dual_faraday p

/-- Regression: the outer product is not the first-order sandwich increment. -/
example :
    sandwichIncrement (cyclic 0) (ι 0) = 0 ∧
      paperWedgeIncrement (cyclic 0) (ι 0) ≠ 0 :=
  paper_wedge_ne_lorentz_increment

/-- Regression: a \(y\)-velocity against \(B_x\) yields a \(z\)-kick; the outer
product vanishes. -/
example :
    sandwichIncrement (cyclic 0) (ι 2) = (2 : ℝ) • ι 3 ∧
      paperWedgeIncrement (cyclic 0) (ι 2) = 0 :=
  sandwich_moving_pureB_ne_wedge

/-- Regression: complementary axis projectors multiply to zero. -/
example : chiralityL * chiralityR = 0 :=
  chiralityL_mul_chiralityR

/-- Regression: duality does not preserve the chirality axis. -/
example : ¬ ∃ c : ℝ, Operations.dual chiralityGen = c • chiralityGen :=
  dual_chiralityGen_not_real_span

/-- Regression: Faraday 3+3 split relative to \(e_1\). -/
example :
    Commute chiralityGen (cyclic 0) ∧
      chiralityGen * hyperbolic 0 = -(hyperbolic 0 * chiralityGen) :=
  ⟨commute_chiralityGen_cyclic0, chiralityGen_anticomm_hyperbolic0⟩

/-- Regression: same-projector sandwich kills the anticommuting summand. -/
example (p : FaradayParams) :
    chiralSandwich (faradayCharged p) = 0 ∧
      chiralSandwich (faraday p) = chiralityR * faradayCartan p :=
  ⟨chiralSandwich_charged p, chiralSandwich_faraday p⟩

/-- Regression: Hodge duality is the mix at \(\omega=\pi/2\). -/
example (p : FaradayParams) :
    mixFaradayParams (Real.pi / 2) p = dualFaradayParams p :=
  mixFaradayParams_pi_div_two p

/-- Regression: orthogonal mix scales \(J\) by \(\cos 2\omega\). -/
example {ω : ℝ} {p : FaradayParams} (h : faradayDot p = 0) :
    J (toTorsion (mixFaradayParams ω p)) =
      Real.cos (2 * ω) * J (toTorsion p) :=
  J_mixFaraday_of_orthogonal h

/-- Regression: pure electric \(J\ge 0\), pure magnetic \(J\le 0\). -/
example (Ex Bx : ℝ) :
    0 ≤ J (toTorsion (pureE Ex)) ∧ J (toTorsion (pureB Bx)) ≤ 0 :=
  ⟨J_pureE_nonneg Ex, J_pureB_nonpos Bx⟩

/-- Regression: a circular wave is null at every phase. -/
example {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (circularWave σ E0 ψ)) = 0 :=
  circularWave_J hσ

/-- Regression: helicity Poynting is constant. -/
example (σ E0 ψ : ℝ) :
    poyntingZ (circularWave σ E0 ψ) = σ * E0 ^ 2 :=
  poyntingZ_circularWave σ E0 ψ

/-- Regression: four-phase mean of a linear circular coefficient vanishes. -/
example (σ E0 : ℝ) :
    quadMean (fun ψ => (circularWave σ E0 ψ).E 0) = 0 :=
  quadMean_circularWave_E σ E0 0

/-- Regression: superposition does not shift mean \(J\). -/
example (p : FaradayParams) {σ E0 : ℝ} (hσ : σ ^ 2 = 1) :
    quadMean (fun ψ => J (toTorsion (p + circularWave σ E0 ψ))) =
      J (toTorsion p) :=
  quadMean_J_add_circularWave p hσ

/-- Regression: mix cannot create \(J\) from a circular wave. -/
example (ω : ℝ) {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (mixFaradayParams ω (circularWave σ E0 ψ))) = 0 :=
  J_mix_circularWave ω hσ

/-- Regression: laboratory \(T\) flips Poynting; duality preserves it. -/
example (p : FaradayParams) :
    poyntingZ (timeReverseFaradayParams p) = -poyntingZ p ∧
      poyntingZ (dualFaradayParams p) = poyntingZ p :=
  ⟨poyntingZ_timeReverse p, poyntingZ_dual p⟩

/-- Regression: rest sandwich of every dual Faraday field vanishes. -/
example (p : FaradayParams) :
    sandwichIncrement (faradayDual p) (ι 0) = 0 :=
  sandwichIncrement_rest_faradayDual p

/-- Regression: Faraday coefficients split as Cartan plus charged. -/
example (p : FaradayParams) :
    cartanParams p + chargedParams p = p :=
  cartanParams_add_chargedParams p

/-- Regression: the coefficient Cartan summand embeds as `faradayCartan`. -/
example (p : FaradayParams) :
    faraday (cartanParams p) = faradayCartan p :=
  faraday_cartanParams p

/-- Regression: both axis sandwiches kill the charged Faraday summand. -/
example (p : FaradayParams) :
    chiralSandwich (faradayCharged p) = 0 ∧
      chiralSandwichL (faradayCharged p) = 0 :=
  ⟨chiralSandwich_charged p, chiralSandwichL_charged p⟩

/-- Regression: Cartan and charged pieces of a circular wave are null. -/
example {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    J (toTorsion (cartanParams (circularWave σ E0 ψ))) = 0 ∧
      J (toTorsion (chargedParams (circularWave σ E0 ψ))) = 0 :=
  ⟨circularWave_cartan_J hσ, circularWave_charged_J hσ⟩

/-- Regression: Poynting of a circular wave splits without a Cartan–charged
cross term. -/
example (σ E0 ψ : ℝ) :
    poyntingZ (cartanParams (circularWave σ E0 ψ)) +
        poyntingZ (chargedParams (circularWave σ E0 ψ)) =
      poyntingZ (circularWave σ E0 ψ) :=
  poyntingZ_circularWave_cartan_add_charged σ E0 ψ

/-- Regression: the circular snapshot is annihilated by the right sandwich. -/
example (σ E0 : ℝ) :
    chiralSandwich (faraday (circularWave σ E0 0)) = 0 :=
  chiralSandwich_circularWave_zero σ E0

/-- Regression: Faraday sandwich on \(e_0+v\) is the written 4-kick. -/
example (p : FaradayParams) (v : Fin 3 → ℝ) :
    sandwichIncrement (faraday p) (minkowskiVec v) = lorentzKick p v :=
  sandwichIncrement_faraday_minkowski p v

/-- Regression: the spatial kick is the Lorentz 3-force of \((E,-B)\). -/
example (p : FaradayParams) (v : Fin 3 → ℝ) :
    sandwichForce p v = lorentzForce 1 (timeReverseFaradayParams p) v :=
  sandwichForce_eq_lorentzForce_timeReverse p v

/-- Regression: rest sandwich is the electric 3-vector. -/
example (p : FaradayParams) :
    sandwichIncrement (faraday p) (ι 0) =
      p.E 0 • ι 1 + p.E 1 • ι 2 + p.E 2 • ι 3 :=
  sandwichIncrement_rest_faraday p

/-- Regression: four-phase mean of the circular rest kick vanishes. -/
example (σ E0 : ℝ) (a : Fin 3) :
    quadMean (fun ψ =>
      sandwichForce (circularWave σ E0 ψ) restVelocity a) = 0 :=
  quadMean_sandwichForce_circularWave_rest σ E0 a

/-- Regression: a beam-direction velocity yields a transverse kick. -/
example (σ E0 ψ vz : ℝ) :
    sandwichForce (circularWave σ E0 ψ) (zVelocity vz) 2 = 0 :=
  sandwichForce_circularWave_zVelocity_transverse σ E0 ψ vz

/-- Regression: circular \(v^2=(GM/R)\,f(r/R)\) on the \(S^3\) chart. -/
example (G M R r : ℝ) (hR : R ≠ 0) (hs : Real.sin (r / R) ≠ 0) :
    s3CircularSpeedSq G M R r = (G * M / R) * rotationShape (r / R) :=
  s3CircularSpeedSq_eq_shape G M R r hR hs

/-- Regression: unique minimum of the rotation-curve shape on \((0,\pi/2)\). -/
example {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    f0 ≤ rotationShape x ∧ (rotationShape x = f0 ↔ x = plateauRoot) :=
  rotationShape_min hx

/-- Regression: \(1.35<f_0<1.41\). -/
example : (135 / 100 : ℝ) < f0 ∧ f0 < (141 / 100 : ℝ) :=
  f0_bounds

/-- Regression: the attractive patch ends strictly before \(r=2R\). -/
example : plateauRoot < Real.pi / 2 ∧ Real.pi / 2 < (2 : ℝ) :=
  attractive_patch_before_two

/-- Regression: \(\eta\) is strictly increasing on \((0,\pi)\). -/
example : StrictMonoOn enhancement (Set.Ioo (0 : ℝ) Real.pi) :=
  strictMonoOn_enhancement

/-- Regression: enhancement at the potential zero is \(\pi^2/4\). -/
example : enhancement (Real.pi / 2) = Real.pi ^ 2 / 4 :=
  enhancement_pi_div_two

/-- Regression: SI Milky-Way compactification radius, \(8\,\mathrm{kpc}<R<9\,\mathrm{kpc}\). -/
example : (8 : ℝ) < milkyWayROverKpc ∧ milkyWayROverKpc < (9 : ℝ) :=
  milkyWayROverKpc_bounds

/-- Regression: geometric plateau inside the optical disk. -/
example : (9 : ℝ) < milkyWayPlateauOverKpc ∧ milkyWayPlateauOverKpc < (11 : ℝ) :=
  milkyWayPlateauOverKpc_bounds

/-- Regression: reversal after the plateau, still well inside \(15\,\mathrm{kpc}\). -/
example :
    (12 : ℝ) < milkyWayReversalOverKpc ∧ milkyWayReversalOverKpc < (15 : ℝ) ∧
      milkyWayPlateauOverKpc < milkyWayReversalOverKpc :=
  ⟨milkyWayReversalOverKpc_bounds.1, milkyWayReversalOverKpc_bounds.2,
    milkyWayPlateau_lt_reversal⟩

/-- Regression: Gauss flux on \(S^3\). -/
example (G M R r : ℝ) (hR : R ≠ 0) (hs : Real.sin (r / R) ≠ 0) :
    s3Accel G M R r * (4 * Real.pi * R ^ 2 * Real.sin (r / R) ^ 2) =
      -4 * Real.pi * G * M :=
  s3Accel_gauss G M R r hR hs

/-- Regression: Tully–Fisher algebra given \(R^2=GM/a_0\). -/
example {G M R a0 : ℝ} (hR : R ≠ 0) (hscale : R ^ 2 = G * M / a0)
    (ha0 : a0 ≠ 0) :
    (vFlatSq G M R) ^ 2 = G * M * a0 * f0 ^ 2 :=
  tullyFisher_of_scaling hR hscale ha0

/-- Regression: cotangent flux equals the enclosed mass. -/
example {G M R r : ℝ} (hR : R ≠ 0) (hs : Real.sin (r / R) ≠ 0) :
    R ^ 2 * Real.sin (r / R) ^ 2 * deriv (cotPotential G M R) r = G * M :=
  geodesicFlux_cotPotential hR hs

/-- Regression: the cotangent potential is radially harmonic off the origin. -/
example {G M R r : ℝ} (hR : R ≠ 0) (hs : Real.sin (r / R) ≠ 0) :
    radialLaplace R (cotPotential G M R) r = 0 :=
  radialLaplace_cotPotential hR hs

/-- Regression: the chart acceleration stays center-directed on \((0,\pi R)\). -/
example {G M R r : ℝ} (hG : 0 < G) (hM : 0 < M) (hR : 0 < R)
    (hr : r ∈ Set.Ioo (0 : ℝ) (Real.pi * R)) :
    s3Accel G M R r < 0 :=
  s3Accel_lt_zero_of_mem_Ioo hG hM hR hr

/-- Regression: the negative well is exactly the open hemisphere. -/
example {G M R r : ℝ} (hG : 0 < G) (hM : 0 < M) (hR : 0 < R)
    (hr : 0 < r) (hπ : r < Real.pi * R) :
    cotPotential G M R r < 0 ↔ r < Real.pi * R / 2 :=
  cotPotential_neg_iff_lt_equator hG hM hR hr hπ

/-- Regression: enhancement and the azimuthal Jacobian both tend to \(1\) at the origin. -/
example :
    Filter.Tendsto enhancement (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
      Filter.Tendsto compactJacobian (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  ⟨tendsto_enhancement_zero, tendsto_compactJacobian_zero⟩

/-- Regression: Newtonian germ on \(0<r\le R\). -/
example {G M R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) :
    |cotPotential G M R r + G * M / r - G * M * r / (3 * R ^ 2)|
      ≤ |G * M| * r ^ 3 / (6 * R ^ 4) :=
  abs_cotPotential_newton hR hr hrR

/-- Regression: on \([1,6/5]\), \(f<(11/10)f_0\). -/
example {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) (6 / 5)) :
    rotationShape x < (11 / 10) * f0 :=
  rotationShape_lt_eleven_tenths_f0 hx

/-- Regression: a constant enclosed mass reproduces the point-mass speed. -/
example {G R M0 r : ℝ} {M : ℝ → ℝ} (hR : R ≠ 0) (hs : Real.sin (r / R) ≠ 0)
    (hM : M r = M0) :
    enclosedCircularSpeedSq G R M r = s3CircularSpeedSq G M0 R r :=
  enclosedCircularSpeedSq_const_eq_point hR hs hM

/-- Regression: dual wall formula. -/
example (α : ℝ) :
    JAxis α (dualWall α) = (Real.pi / 2) * (α - Real.pi / 4) :=
  JAxis_wall α

/-- Regression: dual-only shielding iff the wall is nonpositive. -/
example (p : Operations.TorsionParams) :
    J (dualWallParams p) ≤ 0 ↔
      ∑ a : Fin 3, p.alpha a ≤ 3 * Real.pi / 4 :=
  J_dualWall_nonpos_iff p

/-- Regression: uniform \(\pi/6\) admits equal-scale shielding. -/
example : J (equalScaleOf (uniformTorsion (Real.pi / 6) 0)) = 0 ∧
    Admissible.IsAdmissibleContinuous
      (equalScaleOf (uniformTorsion (Real.pi / 6) 0)) ∧
    0 < mass (equalScaleOf (uniformTorsion (Real.pi / 6) 0)) :=
  ⟨uniform_pi_div_six_shields, uniform_pi_div_six_equalScale_admissible,
    uniform_pi_div_six_massive⟩

/-- Regression: equal-scale shielding is the existing balanced locus. -/
example (p : Operations.TorsionParams) :
    equalScaleOf p = equalScaleParams p.alpha :=
  rfl

/-- Regression: uniform \(\pi/3\) cannot be dual-only shielded. -/
example {q : Operations.TorsionParams}
    (hα : ∀ a, q.alpha a = Real.pi / 3)
    (hq : Admissible.IsAdmissibleContinuous q) :
    0 < J q :=
  uniform_pi_div_three_no_dual_shield hα hq

/-- Regression: dual-only motion conserves \(J+M\). -/
example {p q : Operations.TorsionParams} (hα : q.alpha = p.alpha) :
    J q + mass q = J p + mass p :=
  dual_only_conserves_J_add_mass hα

/-- Regression: a dual-only shield doubles the pure-usual unsigned mass. -/
example {p q : Operations.TorsionParams}
    (hα : q.alpha = p.alpha) (hJ : J q = 0) :
    mass q = 2 * mass (zeroDual p) :=
  mass_eq_two_zeroDual_of_dual_only_J_eq_zero hα hJ

/-- Regression: mixed unwind shields a uniform \(\pi/3\) seed. -/
example :
    J (equalScaleUnwind (uniformTorsion (Real.pi / 3) 0)) = 0 ∧
      Admissible.IsAdmissibleContinuous
        (equalScaleUnwind (uniformTorsion (Real.pi / 3) 0)) ∧
      0 < mass (equalScaleUnwind (uniformTorsion (Real.pi / 3) 0)) :=
  uniform_pi_div_three_mixed_shield

/-- Regression: equal-scale is strictly stronger than dual-only shielding. -/
example :
    ∃ p : Operations.TorsionParams,
      Admissible.IsAdmissibleContinuous p ∧
        (∃ q : Operations.TorsionParams,
          q.alpha = p.alpha ∧ Admissible.IsAdmissibleContinuous q ∧
            J q = 0) ∧
          ¬ Admissible.IsAdmissibleContinuous (equalScaleOf p) :=
  equalScale_strictly_stronger_than_dual_only_shield

/-- Regression: two silent axes give two distinct dual-only shields. -/
example :
    ∃ q₁ q₂ : Operations.TorsionParams,
      q₁.alpha = (axisUsual (Real.pi / 3)).alpha ∧
        q₂.alpha = (axisUsual (Real.pi / 3)).alpha ∧
          Admissible.IsAdmissibleContinuous q₁ ∧
            Admissible.IsAdmissibleContinuous q₂ ∧
              J q₁ = 0 ∧ J q₂ = 0 ∧ q₁ ≠ q₂ :=
  exists_two_dual_only_shields_axisUsual (by positivity)
    pi_div_three_le_pi_div_two

/-- Regression: dual-only cannot evacuate a positive usual seed. -/
example {p q : Operations.TorsionParams}
    (hα : q.alpha = p.alpha)
    (hU : ∑ a : Fin 3, p.alpha a ^ 2 ≠ 0)
    (hM : mass q = 0) : False :=
  dual_only_not_vacuum_of_usual_pos hα hU hM

/-- Regression: a balanced massive seed is not emptied by either channel alone. -/
example {p q : Operations.TorsionParams}
    (hJ : J p = 0) (hM : 0 < mass p) (hq : mass q = 0) :
    q.alpha ≠ p.alpha ∧ q.beta ≠ p.beta :=
  vacuum_moves_both_budgets hJ hM hq

/-- Regression: neutrality is equality of the two rapidity budgets, and is
neither the vacuum nor agreement of the two rotors. -/
example (p : Operations.TorsionParams) :
    (IsGravNeutral p ↔
      ∑ a : Fin 3, p.alpha a ^ 2 = ∑ a : Fin 3, p.beta a ^ 2) ∧
    (∃ q : Operations.TorsionParams, IsGravNeutral q ∧ 0 < mass q ∧
      RelativeRotor.relativeRotor q ≠ 1) :=
  ⟨isGravNeutral_iff_budgets_agree p, exists_isGravNeutral_massive_torsioned⟩

/-- Regression: a configuration at the cone's mass ceiling is not neutral. -/
example {p : Operations.TorsionParams}
    (h : Admissible.IsAdmissibleContinuous p)
    (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    ¬ IsGravNeutral p :=
  not_isGravNeutral_of_mass_eq_max h hM

/-- Regression: sharp mass–mismatch trade-off on the admissible cone. -/
example (p : Operations.TorsionParams)
    (h : Admissible.IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p ≤ 5 * Real.pi ^ 4 / 16 + 4 * J p ^ 2 :=
  pi_sq_mass_le_shield_ceiling_add_J_sq p h

/-- Regression: normalized trade-off curve. -/
example (p : Operations.TorsionParams)
    (h : Admissible.IsAdmissibleContinuous p) :
    massNormalized p ≤ 5 / 6 + (3 / 2) * JNormalized p ^ 2 :=
  massNormalized_le_shield_curve p h

/-- Regression: a shield weighs at most five sixths of the cone ceiling,
and that weight is attained. -/
example : ∃ p : Operations.TorsionParams,
    Admissible.IsAdmissibleContinuous p ∧ J p = 0 ∧
      mass p = 5 * Real.pi ^ 2 / 16 :=
  exists_admissible_shield_of_mass_eq_ceiling

/-- Regression: the trade-off is an equality along the whole wall family. -/
example (γ : ℝ) :
    Real.pi ^ 2 * mass (ceilingWitness γ)
      = 5 * Real.pi ^ 4 / 16 + 4 * J (ceilingWitness γ) ^ 2 :=
  ceilingWitness_attains γ

/-- Regression: the isotropic shield is capped below the ceiling. -/
example {p : Operations.TorsionParams}
    (h : Admissible.IsAdmissibleContinuous p) (heq : p.beta = p.alpha) :
    mass p ≤ 3 * Real.pi ^ 2 / 16 :=
  mass_le_equalScale_ceiling h heq

/-- Regression: at the cone's mass ceiling every axis is purely usual or
purely dual, and no shield exists. -/
example {p : Operations.TorsionParams}
    (h : Admissible.IsAdmissibleContinuous p)
    (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    (∀ a : Fin 3, (p.alpha a = Real.pi / 2 ∧ p.beta a = 0) ∨
        (p.alpha a = 0 ∧ p.beta a = Real.pi / 2)) ∧
      Real.pi ^ 2 / 8 ≤ |J p| :=
  ⟨fun a => axis_rigidity_of_mass_eq_max h hM a,
    pi_sq_div_eight_le_abs_J_of_mass_eq_max h hM⟩

/-- Regression: full repulsion carries no mass penalty. -/
example : ∃ p : Operations.TorsionParams,
    Admissible.IsAdmissibleContinuous p ∧
      mass p = 3 * Real.pi ^ 2 / 8 ∧ J p = -(3 * Real.pi ^ 2 / 8) :=
  exists_admissible_max_mass_full_repulsion

/-- Regression: a dual-only shieldable seed carries at most the ceiling
budget. -/
example {p q : Operations.TorsionParams} (hα : q.alpha = p.alpha)
    (hq : Admissible.IsAdmissibleContinuous q) (hJ : J q = 0) :
    ∑ a : Fin 3, p.alpha a ^ 2 ≤ 5 * Real.pi ^ 2 / 16 :=
  sum_alpha_sq_le_shield_ceiling_of_dual_only_shield hα hq hJ

/-- Regression: attractive-lobe pairing on the whole cone. -/
example (p : Operations.TorsionParams)
    (h : Admissible.IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p ≤
      5 * Real.pi ^ 4 / 16 + (2 * J p - Real.pi ^ 2 / 2) ^ 2 :=
  pi_sq_mass_le_attractive_lobe p h

/-- Regression: repulsive-lobe pairing on the whole cone. -/
example (p : Operations.TorsionParams)
    (h : Admissible.IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p ≤
      5 * Real.pi ^ 4 / 16 + (2 * J p + Real.pi ^ 2 / 2) ^ 2 :=
  pi_sq_mass_le_repulsive_lobe p h

/-- Regression: the piecewise envelope is the mass ceiling at each \(J\). -/
example (p : Operations.TorsionParams)
    (h : Admissible.IsAdmissibleContinuous p) :
    mass p ≤ controlCeiling (J p) :=
  mass_le_control_ceiling p h

/-- Regression: at \(|J|=\pi^2/4\) the envelope falls back to the shield
mass, and that value is attained. -/
example : ∃ p : Operations.TorsionParams,
    Admissible.IsAdmissibleContinuous p ∧
      J p = Real.pi ^ 2 / 4 ∧ mass p = 5 * Real.pi ^ 2 / 16 :=
  exists_admissible_J_quarter_mass_eq_shield

/-- Regression: every pair under the envelope is realised. -/
example {Jval Mval : ℝ}
    (hJmax : |Jval| ≤ 3 * Real.pi ^ 2 / 8)
    (hMlo : |Jval| ≤ Mval) (hMhi : Mval ≤ controlCeiling Jval) :
    ∃ p : Operations.TorsionParams, Admissible.IsAdmissibleContinuous p ∧
      J p = Jval ∧ mass p = Mval :=
  exists_admissible_of_JM hJmax hMlo hMhi

/-- Regression: the envelope is met exactly on the locked wall. -/
example {p : Operations.TorsionParams}
    (h : Admissible.IsAdmissibleContinuous p) :
    mass p = controlCeiling (J p) ↔ OnWall p ∧ TwoCorners p :=
  onEnvelope_iff h

/-- Regression: a dual-only slice meets the envelope at most once. -/
example {p q : Operations.TorsionParams}
    (hp : Admissible.IsAdmissibleContinuous p)
    (hq : Admissible.IsAdmissibleContinuous q)
    (hα : q.alpha = p.alpha)
    (hpE : mass p = controlCeiling (J p))
    (hqE : mass q = controlCeiling (J q)) : p = q :=
  eq_of_onEnvelope_of_alpha_eq hp hq hα hpE hqE

/-- Regression: the heaviest shield splits the free axis in half. -/
example {p : Operations.TorsionParams}
    (h : Admissible.IsAdmissibleContinuous p)
    (hJ : J p = 0) (hM : mass p = 5 * Real.pi ^ 2 / 16) :
    ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsPureUsual p a ∧ IsPureDual p b ∧
      p.alpha c = Real.pi / 4 ∧ p.beta c = Real.pi / 4 :=
  exists_heaviest_shield_roles h hJ hM

/-- Regression: both-channel power is the indefinite pairing. -/
example {m φ θ φdot θdot φddot θddot v u : ℝ}
    (h : PaperBothSourcedEL m φ θ φddot θddot v u) :
    paperEnergyDot m φ θ φdot θdot φddot θddot = v * φdot - u * θdot :=
  paperEnergyDot_both_sourced h

/-- Regression: dual-only constraint force is unique. -/
example {m φ θ φddot θddot v u : ℝ}
    (h : PaperBothSourcedEL m φ θ φddot θddot v u) (hφ : φddot = 0) :
    v = m * (φ - θ) :=
  paperBothSourcedEL_constraint_force h hφ

/-- Regression: vanishing dual force recovers the unsourced written jet. -/
example (m φ θ φddot θddot : ℝ) :
    PaperSourcedEL m φ θ φddot θddot 0 ↔ PaperActualEL m φ θ φddot θddot :=
  paperSourcedEL_zero_iff m φ θ φddot θddot

/-- Regression: written dual force freely accelerates the mismatch. -/
example (m φ θ φddot θddot u : ℝ) (h : PaperSourcedEL m φ θ φddot θddot u) :
    φddot - θddot = -u :=
  paperSourcedEL_mismatch h

/-- Regression: working oscillator plus dual force shifts the mismatch. -/
example {m φ θ u : ℝ} (hm : m ≠ 0)
    (h : OscillatorSourcedEL m φ θ 0 0 u) :
    φ - θ = -u / (2 * m) :=
  oscillatorSourcedEL_eq_mismatch hm h

/-- Regression: leftover mismatch is not dual-only on the written sourced jet. -/
example {m φ θ φddot θddot u : ℝ} (hm : m ≠ 0) (hδ : φ ≠ θ) :
    ¬ (PaperSourcedEL m φ θ φddot θddot u ∧ φddot = 0) :=
  paperSourcedEL_not_dual_only_of_mismatch hm hδ

/-- Regression: helicity-odd classical quadratics are multiples of \(P_z\). -/
example {cE2 cB2 cEB cPx cPy cPz : ℝ}
    (h : ∀ σ E0 ψ : ℝ, σ ^ 2 = 1 →
      classicalQuadratic cE2 cB2 cEB cPx cPy cPz (circularWave (-σ) E0 ψ) =
        -classicalQuadratic cE2 cB2 cEB cPx cPy cPz (circularWave σ E0 ψ))
    {σ E0 ψ : ℝ} (hσ : σ ^ 2 = 1) :
    classicalQuadratic cE2 cB2 cEB cPx cPy cPz (circularWave σ E0 ψ) =
      cPz * poyntingZ (circularWave σ E0 ψ) :=
  classicalQuadratic_eq_smul_poyntingZ_of_helicity_odd h hσ

/-- Regression: the time axis cannot furnish a chirality projector. -/
example :
    ((1 : PGA) + PGA.ι 0) * half * (((1 : PGA) + PGA.ι 0) * half) ≠
      ((1 : PGA) + PGA.ι 0) * half :=
  timeAxis_not_chirality_projector

/-- Regression: three right projectors are not a resolution of the identity. -/
example : chiralityRAxis 0 + chiralityRAxis 1 + chiralityRAxis 2 ≠ 1 :=
  chiralityRAxis_sum_ne_one

/-- Regression: distinct-axis chirality projectors do not commute. -/
example : chiralityRAxis 0 * chiralityRAxis 1 ≠
    chiralityRAxis 1 * chiralityRAxis 0 :=
  chiralityRAxis_not_commute (by decide : (0 : Fin 3) ≠ 1)

/-- Regression: Cartan brackets of axis \(e_1\) close as \(\mathfrak{so}(2,1)\). -/
example :
    commutator (cartanGen 0 0) (cartanGen 0 1) = (2 : ℝ) • cartanGen 0 2 ∧
      commutator (cartanGen 0 0) (cartanGen 0 2) = -((2 : ℝ) • cartanGen 0 1) ∧
        commutator (cartanGen 0 1) (cartanGen 0 2) = -((2 : ℝ) • cartanGen 0 0) :=
  ⟨commutator_cartan_K_P1 0, commutator_cartan_K_P2 0, commutator_cartan_P1_P2 0⟩

/-- Regression: the charged triple is not Lie-closed. -/
example (a : Fin 3) :
    ¬ (spatialGen a * commutator (chargedGen a 0) (chargedGen a 1) =
        -(commutator (chargedGen a 0) (chargedGen a 1) * spatialGen a)) :=
  charged_triple_not_lie_closed a

/-- Regression: duality exchanges Cartan with charged. -/
example (a : Fin 3) :
    dual (cartanGen a 0) = chargedGen a 0 ∧
      dual (cartanGen a 1) = -chargedGen a 1 :=
  ⟨(dual_cartanGen a).1, (dual_cartanGen a).2.1⟩

/-- Regression: a perpendicular dual rotation exchanges the projectors at angle \(\pi\). -/
example (a : Fin 3) :
    NormedSpace.exp ((Real.pi / 2) • cyclic (a + 1)) * chiralityRAxis a *
        CliffordAlgebra.reverse
          (NormedSpace.exp ((Real.pi / 2) • cyclic (a + 1))) =
      chiralityLAxis a :=
  dualRotation_exchanges_projectors a

/-- Regression: the parallel electric mix preserves the axis only at a trivial angle. -/
example (a : Fin 3) (cB cE : ℝ) :
    Commute (spatialGen a) (cB • cyclic a + cE • hyperbolic a) ↔ cE = 0 :=
  commute_neutral_axis_iff a cB cE

/-- Regression: \(\theta\mapsto\theta+eA\) is magnetic Faraday superposition. -/
example (p : Operations.TorsionParams) (e : ℝ) (A : Fin 3 → ℝ) :
    coupleA p e A = superpose p (magneticFaraday (fun a => e * A a)) :=
  coupleA_eq_superpose_magnetic p e A

/-- Regression: nonnegative magnetic increments cannot raise \(J\). -/
example {p : Operations.TorsionParams} {B : Fin 3 → ℝ}
    (hβ : ∀ a, 0 ≤ p.beta a) (hB : ∀ a, 0 ≤ B a) :
    J (superpose p (magneticFaraday B)) ≤ J p :=
  J_superpose_magnetic_le hβ hB

/-- Regression: circular Faraday superposition does not shift mean \(J\). -/
example (p : Operations.TorsionParams) {σ E0 : ℝ} (hσ : σ ^ 2 = 1) :
    quadMean (fun ψ => J (superpose p (circularWave σ E0 ψ))) = J p :=
  quadMean_J_superpose_circular p hσ

/-- Regression: circular \(A\) drops mean \(J\) by a helicity-even
ponderomotive. -/
example (p : Operations.TorsionParams) (e E0 ω σ : ℝ) (hσ : σ ^ 2 = 1) :
    quadMean (fun ψ => J (coupleA p e (circularPotential σ E0 ω ψ))) =
      J p - (e ^ 2 / 2) * (E0 / ω) ^ 2 ∧
    quadMean (fun ψ => J (coupleA p e (circularPotential σ E0 ω ψ))) =
      quadMean (fun ψ =>
        J (coupleA p e (circularPotential (-σ) E0 ω ψ))) :=
  ⟨quadMean_J_coupleA_circular p e E0 ω hσ,
    quadMean_J_coupleA_circular_helicity_even p e E0 ω σ hσ⟩

/-- Regression: a constant shift of \(A\) changes \(J\). -/
example :
    ∃ p : Operations.TorsionParams, ∃ e : ℝ, ∃ A c : Fin 3 → ℝ,
      J (coupleA p e A) ≠ J (coupleA p e (fun a => A a + c a)) :=
  exists_constant_potential_changes_J

/-- Regression: zero-mean circular \(A\) on a vanishing dual seed leaves
the cone. -/
example {p : Operations.TorsionParams} {e E0 ω : ℝ} (hβ : p.beta 0 = 0)
    (he : 0 < e) (hE : 0 < E0) (hω : 0 < ω) :
    ¬ Admissible.IsAdmissibleContinuous
        (coupleA p e (circularPotential 1 E0 ω (3 * Real.pi / 2))) :=
  not_admissible_coupleA_circular_from_zeroDual hβ he hE hω

/-- Regression: dual-only realisation of \(\theta=\theta_0+eA\) on the
written action requires \(u=e\ddot A+m\delta\). -/
example (m φ θ0 e A Addot : ℝ) :
    PaperBothSourcedEL m φ (θ0 + e * A) 0 (e * Addot)
      (m * (φ - (θ0 + e * A)))
      (e * Addot + m * (φ - (θ0 + e * A))) :=
  paperBothSourcedEL_coupleA_jet m φ θ0 e A Addot

/-- Regression: dual-rotor cyclic generators satisfy \(IJ=K\). -/
example : cyclic 0 * cyclic 1 = cyclic 2 :=
  dual_rotor_quaternion.1

/-- Regression: Cartan signature is mixed; hyperbolic generators are not compact. -/
example (a : Fin 3) :
    cartanGen a 0 * cartanGen a 0 = -1 ∧ hyperbolic a * hyperbolic a ≠ -1 :=
  ⟨(cartan_mixed_signature a).1, hyperbolic_noncompact a⟩

/-- Regression: dual excitation strictly lowers \(\gamma_{\mathrm{eff}}\)
on a boosted axis. -/
example {α β₁ β₂ : ℝ} (hα : 0 < α) (hlo : 0 ≤ β₁) (hlt : β₁ < β₂)
    (hhi : β₂ ≤ Real.pi / 2) :
    gammaEff α β₂ < gammaEff α β₁ :=
  gammaEff_lt_gammaEff_of_lt_beta hα hlo hlt hhi

/-- Regression: \(\gamma_{\mathrm{eff}}=1\) iff the dual angle is \(\beta_\ast\). -/
example {α β : ℝ} (hα : 0 < α) (hβ0 : 0 ≤ β) (hβ : β ≤ Real.pi / 2) :
    gammaEff α β = 1 ↔ β = clockAngle α :=
  gammaEff_eq_one_iff_clockAngle hα hβ0 hβ

/-- Regression: an admissible coaxial shield has already passed that
return. -/
example {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 4) :
    gammaEff α α < 1 :=
  gammaEff_coaxial_lt_one hα0 hα

/-- Regression: unique wall-clock threshold in \((\pi/3,\pi/2)\). -/
example :
    wallClockRoot ∈ Set.Ioo (Real.pi / 3) (Real.pi / 2) ∧
      ∀ α, α ∈ Set.Ioo (Real.pi / 3) (Real.pi / 2) →
        wallClockProbe α = 0 → α = wallClockRoot :=
  ⟨wallClockRoot_mem, fun _ h hz => eq_wallClockRoot h hz⟩

/-- Regression: cross-axis shielding preserves the special-relativistic
clock on the boosted axis. -/
example (α : ℝ) :
    J (crossAxisDual α) = 0 ∧
      J (equalScaleOf (axisUsual α)) = 0 ∧
        mass (crossAxisDual α) = mass (equalScaleOf (axisUsual α)) ∧
          gammaEff ((crossAxisDual α).alpha 0) ((crossAxisDual α).beta 0) =
            Real.cosh α ∧
            gammaEff ((crossAxisDual α).alpha 1) ((crossAxisDual α).beta 1) =
              1 :=
  ⟨J_crossAxisDual α, J_equalScaleOf (axisUsual α),
    mass_crossAxisDual_eq_equalScale α, gammaEff_crossAxisDual_boost α,
    gammaEff_crossAxisDual_comp α⟩

/-- Regression: a unit vacuum excess is gravitationally maximal. -/
example {δ : ℝ} {p : Fin 3 → ℝ} (hδ : δ ≠ 0) (hp : ∑ a : Fin 3, p a ^ 2 = 1) :
    J (boostAlong δ p) = δ ^ 2 / 2 ∧
      mass (boostAlong δ p) = δ ^ 2 / 2 ∧
        J (boostAlong δ p) / mass (boostAlong δ p) = 1 ∧
          J (rotationAlong δ p) / mass (rotationAlong δ p) = -1 := by
  have hJ := J_boostAlong_unit (δ := δ) hp
  have hp0 : ∑ a : Fin 3, p a ^ 2 ≠ 0 := by
    rw [hp]
    norm_num
  exact ⟨hJ.1, hJ.2, J_div_mass_boostAlong hδ hp0, J_div_mass_rotationAlong hδ hp0⟩

/-- Regression: the quadratic vacuum law characterises a vanishing background. -/
example (φ : ℝ) :
    (∀ δ : ℝ, J (balancedBoostShift φ δ) = δ ^ 2 / 2) ↔ φ = 0 :=
  balancedBoostShift_J_eq_quadratic_iff φ

/-- Regression: spatial inversion negates the pseudoscalar. -/
example : spatialParity Operations.pseudoscalar = -Operations.pseudoscalar :=
  spatialParity_pseudoscalar

/-- Regression: in the thin-shell window the tangential caustic lies outside the radial one. -/
example {c : ℝ} (h1 : 1 < c) (h2 : c < 2) :
    xiOfS (radialCriticalS c) < xiOfS (tangentialCriticalS c) :=
  radial_caustic_lt_tangential h1 h2

/-- Regression: a subcritical ray has no classical turning point, and the
Killing time down to the horizon is unbounded. -/
example {rs r b T : ℝ} (hrs : 0 < rs) (hr : rs < r) (hb : 0 ≤ b)
    (hlt : b < criticalImpact rs) :
    b ^ 2 * schwarzschildA rs r < r ^ 2 ∧
      ∃ s, rs < s ∧ s < photonSphere rs ∧
        T < killingAntideriv rs (photonSphere rs) - killingAntideriv rs s :=
  ⟨no_exterior_turning hrs hr hb hlt, exists_classical_delay_gt hrs⟩

/-- Regression: the dual-rotor determinant has vanishing argument. -/
example (β : DualRapidity) :
    (dualRotorMat β).det = 1 ∧ ((dualRotorMat β).det).arg = 0 :=
  dualRotor_det_arg β

end Gravity

end DstDiophantine
