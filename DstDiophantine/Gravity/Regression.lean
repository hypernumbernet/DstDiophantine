import DstDiophantine.Gravity.Identification
import DstDiophantine.Gravity.JTDictionary
import DstDiophantine.Gravity.GaugeDictionary
import DstDiophantine.Gravity.ClassicalSchwarzschild
import DstDiophantine.Gravity.LorentzGauge
import DstDiophantine.Gravity.LorentzFamily
import DstDiophantine.Gravity.NullChart
import DstDiophantine.Gravity.CommutingPlanes
import DstDiophantine.Gravity.LorentzCounterexample
import DstDiophantine.Gravity.OrderedPlanes
import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Logic.Quantum.SpinConnection
import DstDiophantine.Gravity.RadialQuadratic
import DstDiophantine.Gravity.Tetrad
import DstDiophantine.Gravity.NewtonFromLight
import DstDiophantine.Gravity.EventBoundary
import DstDiophantine.Gravity.Godel
import DstDiophantine.Gravity.Kerr
import DstDiophantine.Gravity.CoulombFromDual
import DstDiophantine.Gravity.ForceScale
import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Gravity.CompactS3
import DstDiophantine.Gravity.DualImage
import DstDiophantine.Gravity.GalaxyCurve
import DstDiophantine.Gravity.SlerpTorque
import DstDiophantine.Gravity.RelationalPosition
import DstDiophantine.Gravity.ChannelRange
import DstDiophantine.Gravity.CliffordParallel
import DstDiophantine.Gravity.ChartRotation
import DstDiophantine.Gravity.RacketFlip
import DstDiophantine.Gravity.RacketThermal
import DstDiophantine.Gravity.WeakLinearity
import DstDiophantine.Gravity.TorsionalLayer
import DstDiophantine.Gravity.NuclearLayer
import DstDiophantine.Gravity.NuclearLength
import DstDiophantine.Gravity.SignReversal
import DstDiophantine.Gravity.StrongChannel
import DstDiophantine.Gravity.DualRotorDynamics
import DstDiophantine.Gravity.DualRotorRigidity
import DstDiophantine.Gravity.DualRotorFlow
import DstDiophantine.Gravity.DualRotorVacuum
import DstDiophantine.Gravity.DualRotorMotor
import DstDiophantine.Gravity.NullRotation
import DstDiophantine.Gravity.ExponentialFamily
import DstDiophantine.Gravity.RestMass
import DstDiophantine.Gravity.ElectronOrbit
import DstDiophantine.Gravity.ElectronSquare
import DstDiophantine.Gravity.ElectronHelium
import DstDiophantine.Gravity.HeliumBody
import DstDiophantine.Gravity.ElectronForce
import DstDiophantine.Gravity.OrbitClosure
import DstDiophantine.Gravity.ElectronNumbers
import DstDiophantine.Gravity.ElectronLength
import DstDiophantine.Gravity.ElectronStanding
import DstDiophantine.Gravity.Rutherford
import DstDiophantine.Gravity.NeutronScatter
import DstDiophantine.Gravity.ElectronCapacity
import DstDiophantine.Gravity.ElectronShape
import DstDiophantine.Gravity.ElectronAngular
import DstDiophantine.Gravity.ElectronBoundary
import DstDiophantine.Gravity.ElectronWater
import DstDiophantine.Gravity.ElectronAngle
import DstDiophantine.Gravity.ElectronTrio
import DstDiophantine.Gravity.ElectronMetal
import DstDiophantine.Gravity.ElectronCrystal
import DstDiophantine.Gravity.MetalFusion
import DstDiophantine.Gravity.ElectronDodeca
import DstDiophantine.Gravity.Blackbody
import DstDiophantine.Gravity.ShellCollision
import DstDiophantine.Gravity.Faraday
import DstDiophantine.Gravity.Electroweak
import DstDiophantine.Gravity.CircularPolarization
import DstDiophantine.Gravity.DualControl
import DstDiophantine.Gravity.ConeLabels
import DstDiophantine.Gravity.MassCorners
import DstDiophantine.Gravity.ShieldClock
import DstDiophantine.Gravity.ShieldCeiling
import DstDiophantine.Gravity.ControlDomain
import DstDiophantine.Gravity.EnvelopeLock
import DstDiophantine.Gravity.ChiralSpectrum
import DstDiophantine.Gravity.ChiralityStabilizer
import DstDiophantine.Gravity.ChiralCurrent
import DstDiophantine.Gravity.EMControl
import DstDiophantine.Gravity.CircularHold
import DstDiophantine.Gravity.NeutronMagnet
import DstDiophantine.Gravity.SilentControl
import DstDiophantine.Gravity.ShieldHold
import DstDiophantine.Gravity.HoldPrice
import DstDiophantine.Gravity.ControlScale
import DstDiophantine.Gravity.ParticleStability
import DstDiophantine.Gravity.BaryonAsymmetry
import DstDiophantine.Gravity.ParityBridge
import DstDiophantine.Gravity.KillingAxis
import DstDiophantine.Gravity.RadialFall
import DstDiophantine.Gravity.Perihelion
import DstDiophantine.Gravity.Lensing
import DstDiophantine.Gravity.PhotonReturn
import DstDiophantine.Gravity.LengthRule
import DstDiophantine.Gravity.BothChannels
import DstDiophantine.Gravity.ElectronExclusion
import DstDiophantine.Gravity.SpinVersusExclusion
import DstDiophantine.Gravity.ChannelBridge
import DstDiophantine.Algebra.SourceSuperposition
import DstDiophantine.Gravity.MachSource
import DstDiophantine.Gravity.InteriorClock
import DstDiophantine.Gravity.MassOrigin
import DstDiophantine.Gravity.MassCoefficient

/-!
# Gravity regression examples

Smoke tests for the gravity track. Each `example` restates a theorem proved
in a submodule. Nothing here is a new claim. The index of the track is the
module doc of `DstDiophantine.Gravity`.
-/

namespace DstDiophantine

namespace Gravity

open Invariant PGA Generators Logic Operations SourceSuperposition


/-! ## Chart dictionary -/

/-- Regression: auxiliary expression `(4/r²)(cosh√(2J)-1)`, not the teleparallel quadratic. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      teleparallelTofJ (J (radialBoostParams rs r)) r :=
  schwarzschild_T_eq_teleparallelTofJ h


/-! ## The direction of gravity -/

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

/-- Regression: one share of the perihelion term is transverse speed, two are `A − 1`. -/
example {rs r L : ℝ} (hr : r ≠ 0) :
    (schwarzschildA rs r - 1) * L ^ 2 / r ^ 3 =
        2 * (-(KillingAxis.killingRate rs r) * (L / r) ^ 2) ∧
      -(KillingAxis.killingRate rs r) * (L / r) ^ 2 +
          (schwarzschildA rs r - 1) * L ^ 2 / r ^ 3 =
        -3 * KillingAxis.killingRate rs r * L ^ 2 / r ^ 2 :=
  Perihelion.perihelion_three_shares hr

/-- Regression: the perihelion excess lies strictly between `6π M/p` and that over `1 − 6M/p`. -/
example {M L p : ℝ} (hM : M ≠ 0) (hp : p = L ^ 2 / M)
    (hx0 : 0 < 6 * M / p) (hx1 : 6 * M / p < 1) :
    let k := Real.sqrt (1 - 6 * M / p)
    6 * Real.pi * M / p < 2 * Real.pi * (1 / k - 1) ∧
      2 * Real.pi * (1 / k - 1) < (6 * Real.pi * M / p) / (1 - 6 * M / p) :=
  Perihelion.perihelion_excess_latus hM hp hx0 hx1

/-- Regression: the radial piece of `γ²` cancels and the transverse piece remains. -/
example {κ ur uφ : ℝ} :
    κ * ur ^ 2 - κ * Perihelion.gammaSq ur uφ = -κ * (1 + uφ ^ 2) :=
  Perihelion.radial_speed_cancels

/-- Regression: a tangential tilt multiplies angular momentum by a decaying exponential. -/
example {κ L0 τ₁ τ₂ : ℝ} (hL : 0 < L0) (hκ : 0 < κ) (hτ : τ₁ < τ₂) :
    L0 * Real.exp (-κ * τ₂) < L0 * Real.exp (-κ * τ₁) :=
  Perihelion.naiveAngular_strictAnti hL hκ hτ

/-- Regression: on the exterior chart that meeting lies on the static horizon. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    KillingAxis.killingNormSq
        (KillingAxis.killingParams (KillingAxis.killingRate rs r) (KillingAxis.killingNorm rs r))
        (KillingAxis.releasedWorldline (KillingAxis.axisDistance rs r)) = 0 :=
  KillingAxis.released_on_staticHorizon h

/-- Regression: above the surface the DST clock and the potential agree. -/
example {GM c2 r h : ℝ} (hr : r ≠ 0) (hrh : r + h ≠ 0) (hc : c2 ≠ 0) :
    InteriorClock.clockExterior GM c2 r h = InteriorClock.potentialExterior GM c2 r h :=
  InteriorClock.exterior_agreement hr hrh hc

/-- Regression: light climbing against the weight is shifted by `g h / c²`. -/
example {grav c2 h : ℝ} :
    InteriorClock.lightClimb grav c2 h = grav * h / c2 :=
  InteriorClock.lightClimb_eq

/-- Regression: the centre factor is the vacuum value.
Its advance against the surface factor is `centreAdvance`. -/
example {ε : ℝ} :
    InteriorClock.centreFactor / InteriorClock.surfaceFactor ε - 1 =
      InteriorClock.centreAdvance ε :=
  InteriorClock.centreAdvance_eq_ratio

/-- Regression: the shared potential gradient rounds to `1.093×10⁻¹⁶` per metre. -/
example :
    (10925 : ℝ) / 10 ^ 20 < InteriorClock.earthWeight ∧
      InteriorClock.earthWeight < (10935 : ℝ) / 10 ^ 20 :=
  InteriorClock.earth_potential_gradient_bins

/-- Regression: compactness and the centre advance both round to `6.96×10⁻¹⁰`. -/
example :
    (6955 : ℝ) / 10 ^ 13 < (InteriorClock.earthCompactnessQ : ℝ) ∧
      (InteriorClock.earthCompactnessQ : ℝ) < (6965 : ℝ) / 10 ^ 13 ∧
      (6955 : ℝ) / 10 ^ 13 <
        InteriorClock.centreAdvance (InteriorClock.earthCompactnessQ : ℝ) ∧
        InteriorClock.centreAdvance (InteriorClock.earthCompactnessQ : ℝ) <
          (6965 : ℝ) / 10 ^ 13 :=
  ⟨InteriorClock.earth_centre_bins.1, InteriorClock.earth_centre_bins.2.1,
    InteriorClock.earth_centre_bins.2.2.1, InteriorClock.earth_centre_bins.2.2.2.1⟩


/-! ## Chart dictionary -/

/-- Regression: an inertial-plane boost keeps the Minkowski metric and kills `T`. -/
example (φ u v : ℝ) (μ ν : Fin 4) :
    inducedMetric (inertialBoostCoframe φ) μ ν =
        (if μ = ν then w31 μ else 0) ∧
      boostCoordTorsion φ u v 0 0 1 = u ∧
      boostTeleparallel u v = 0 :=
  ⟨inducedMetric_inertialBoost φ μ ν, boostCoordTorsion_ttx φ u v,
    boostTeleparallel_eq_zero u v⟩

/-- Regression: an inertial rotation in one spatial plane keeps Minkowski and kills `T`.
The mismatch of that angle is the negative of the pure boost. -/
example (θ p q : ℝ) (μ ν : Fin 4) :
    inducedMetric (inertialRotationCoframe θ) μ ν =
        (if μ = ν then w31 μ else 0) ∧
      rotationCoordTorsion θ p q 1 1 2 = p ∧
      rotationCoordTorsion θ p q 2 1 2 = q ∧
      rotationTeleparallel p q = 0 ∧
      J (inertialRotationParams θ) = -J (DstDiophantine.Amplification.pureBoost θ) :=
  ⟨inducedMetric_inertialRotation θ μ ν, rotationCoordTorsion_xxy θ p q,
    rotationCoordTorsion_yxy θ p q, rotationTeleparallel_eq_zero p q,
    J_inertialRotation_eq_neg_pureBoost θ⟩

/-- Regression: a constant boost coframe row is the sandwich of that boost. -/
example (φ : ℝ) :
    Sandwich.sandwich (Motor.rotorTorsion (Amplification.pureBoost φ)) (ι 0) =
      axisBoostCoframe 0 φ 0 0 • ι 0 + axisBoostCoframe 0 φ 0 1 • ι 1 +
        axisBoostCoframe 0 φ 0 2 • ι 2 + axisBoostCoframe 0 φ 0 3 • ι 3 :=
  sandwich_pureBoost_coframe_ι0 φ

/-- Regression: a constant `(x,y)` rotation coframe row is the cyclic-2 sandwich. -/
example (θ : ℝ) :
    Sandwich.sandwich (Motor.rotorTorsion (Sandwich.pureRotation2 θ)) (ι 1) =
      axisRotCoframe 2 θ 1 1 • ι 1 + axisRotCoframe 2 θ 1 2 • ι 2 :=
  sandwich_rotation2_coframe_ι1 θ

/-- Regression: every coordinate-plane boost keeps Minkowski and kills `T`. -/
example (i : Fin 3) (φ : ℝ) (d : Fin 4 → ℝ) (μ ν : Fin 4) :
    inducedMetric (axisBoostCoframe i φ) μ ν = (if μ = ν then w31 μ else 0) ∧
      PlaneTorsion.genTeleparallel (axisBoostGen i) d = 0 ∧
      J (axisBoostParams i φ) = (1 / 2) * φ ^ 2 :=
  ⟨inducedMetric_axisBoost i φ μ ν, axisBoostTeleparallel_eq_zero i d, J_axisBoost i φ⟩

/-- Regression: every coordinate-plane rotation keeps Minkowski and kills `T`. -/
example (i : Fin 3) (θ : ℝ) (d : Fin 4 → ℝ) (μ ν : Fin 4) :
    inducedMetric (axisRotCoframe i θ) μ ν = (if μ = ν then w31 μ else 0) ∧
      PlaneTorsion.genTeleparallel (axisRotGen i) d = 0 ∧
      J (axisRotParams i θ) = -J (axisBoostParams i θ) :=
  ⟨inducedMetric_axisRot i θ μ ν, axisRotTeleparallel_eq_zero i d, J_axisRot_eq_neg_boost i θ⟩

/-- Regression: a one-parameter connection has vanishing curvature coefficient. -/
example (c : PGA) : (0 : PGA) + (c * c - c * c) = 0 :=
  oneParam_curvature c

/-- Regression: a common left rotor leaves the relative rotor unchanged. -/
example (S : PGA) (hS : S * CliffordAlgebra.reverse S = 1) (α β : ℝ) :
    CliffordAlgebra.reverse (S * RelativeRotor.rotorUsual (RelativeRotor.axisParams α β)) *
        (S * RelativeRotor.rotorDual (RelativeRotor.axisParams α β)) =
      RelativeRotor.relativeRotor (RelativeRotor.axisParams α β) :=
  RelativeRotor.common_left_preserves_relativeRotor S hS _

/-- Regression: a null rotation keeps Minkowski, kills `T`, and has `J = 0`. -/
example (t : ℝ) (d : Fin 4 → ℝ) (μ ν : Fin 4) :
    inducedMetric (nullCoframe t) μ ν = (if μ = ν then w31 μ else 0) ∧
      J (nullMismatch t) = 0 ∧
      PlaneTorsion.genTeleparallel nullCoGen d = 0 :=
  ⟨inducedMetric_nullCoframe t μ ν, J_nullMismatch t, nullTeleparallel_eq_zero d⟩

/-- Regression: a commuting boost and rotation keep Minkowski and kill `T`. -/
example (φ θ : ℝ) (dφ dθ : Fin 4 → ℝ) (μ ν : Fin 4) :
    inducedMetric (productCoframe φ θ) μ ν = (if μ = ν then w31 μ else 0) ∧
      productTeleparallel dφ dθ = 0 :=
  ⟨inducedMetric_product φ θ μ ν, productTeleparallel_eq_zero dφ dθ⟩

/-- Regression: order of a noncommuting boost and rotation remains in `T`. -/
example (φ θ u v : ℝ) (huv : u * v ≠ 0) (μ ν : Fin 4) :
    inducedMetric (boostLeftCoframe φ θ) μ ν = (if μ = ν then w31 μ else 0) ∧
      inducedMetric (rotLeftCoframe φ θ) μ ν = (if μ = ν then w31 μ else 0) ∧
      (boostLeftTeleparallel φ θ u v = rotLeftTeleparallel φ θ u v ↔
        φ = 0 ∧ Real.cos θ = 1) :=
  ⟨inducedMetric_boostLeft φ θ μ ν, inducedMetric_rotLeft φ θ μ ν,
    ordered_agree_iff φ θ u v huv⟩

/-- Regression: a positive jet keeps the vacuum sign for one order only. -/
example (φ θ u v : ℝ) (h : 0 < u * v) :
    rotLeftTeleparallel φ θ u v < 0 ∧
      (boostLeftTeleparallel φ θ u v < 0 ↔ 0 < Real.cos θ) ∧
      boostLeftTeleparallel 0 Real.pi u v = 2 * u * v ∧
      rotLeftTeleparallel 0 Real.pi u v = -2 * u * v ∧
      boostLeftTeleparallel 0 (Real.pi / 2) u v = 0 ∧
      rotLeftTeleparallel 0 (Real.pi / 2) u v = -2 * u * v := by
  obtain ⟨hπb, hπr⟩ := ordered_opposite_at_pi u v
  obtain ⟨hhb, hhr⟩ := ordered_split_at_half_pi u v
  exact ⟨rotLeft_has_vacuum_sign φ θ u v h, boostLeft_has_vacuum_sign_iff φ θ u v h,
    hπb, hπr, hhb, hhr⟩

/-- Regression: a translator keeps the inertial leg, and a motor `RT` keeps the rotor's leg. -/
example (p : Motor.TransParams) (q : Motor.OmegaParams) (μ : Fin 4) :
    sandwich (Motor.expTrans p) (frameVec μ) =
        frameVec μ + (w31 μ * p.lambda μ) • ι e4Index ∧
      sandwich (Motor.motor q) (frameVec μ) =
        sandwich (Motor.rotorTorsion q.torsion) (frameVec μ) +
          (w31 μ * q.trans.lambda μ) • ι e4Index :=
  ⟨translator_minkowski_leg p μ, motor_minkowski_leg q μ⟩

/-- Regression: the pure-gauge boost derivative sends solutions to solutions. -/
example (θ : ℝ) {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (h : DiracMomentum m p Ψ) :
    blockDiag2 (embedR (halfDerivR θ * halfInvR θ))
        (embedR (halfInvDerivR θ * halfR θ)) = spinGen 0 1 ∧
      DiracMomentum m (lorentzAct (usualRotorMat (EuclideanSpace.single 0 θ)) p)
        (rotorDirac (usualRotorMat (EuclideanSpace.single 0 θ)) Ψ) :=
  ⟨boost_logDeriv θ, constant_boost_sends_solution θ h⟩

/-- Regression: a Lorentz matrix keeps the Minkowski metric, and a mixed jet has `T = -2`. -/
example (Λ : Coframe)
    (h : ∀ μ ν, ∑ a : Fin 4, w31 a * Λ a μ * Λ a ν = if μ = ν then w31 μ else 0)
    (μ ν : Fin 4) :
    inducedMetric Λ μ ν = (if μ = ν then w31 μ else 0) ∧ mixedTeleparallel = -2 :=
  ⟨inducedMetric_of_lorentz Λ h μ ν, mixedTeleparallel_eq⟩

/-- Regression: the same `J` does not determine `T`. The inertial jet has `T=0`;
the exterior quadratic is `-2/r²`. -/
example {rs r θ : ℝ} (h : IsExterior rs r) (hs : Real.sin θ ≠ 0) :
    J (DstDiophantine.Amplification.pureBoost (schwarzschildRapidity rs r)) =
        J (radialBoostParams rs r) ∧
      boostTeleparallel 0 0 = 0 ∧
      radialTeleparallel (schwarzschildA rs r) (rs / r ^ 2) r θ = -2 / r ^ 2 ∧
      0 < J (radialBoostParams rs r) := by
  refine ⟨?_, boostTeleparallel_eq_zero 0 0, radialTeleparallel_schwarzschild h hs, ?_⟩
  · rw [Amplification.J_pureBoost, J_radialBoostParams]
  · exact (schwarzschild_J_pos_T_frozen h hs).1

/-- Regression: the auxiliary chart expression is positive, and is not the quadratic. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    J (DstDiophantine.Amplification.pureBoost (schwarzschildRapidity rs r)) =
        J (radialBoostParams rs r) ∧
      boostTeleparallel 0 0 = 0 ∧
      0 < schwarzschildTeleparallelT rs r :=
  sameJ_inertial_T_zero_schwarzschild_T_pos h

/-- Regression: the auxiliary expression on any positive time-leg, not the quadratic. -/
example {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofA A r =
      4 * (Real.cosh (Real.sqrt (2 * J (gaugeBoostParams A))) - 1) :=
  r_sq_T_ofA_eq_four_cosh_sqrt hA hr

/-- Regression: the auxiliary expression is nonnegative. The quadratic is not. -/
example {A r : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    ¬ teleparallelTofA A r < 0 :=
  teleparallelTofA_not_lt_zero hA hr

/-- Regression: \(T<0\) on the admissible cone requires the elliptic sector. -/
example {Jval r : ℝ} (hr : r ≠ 0)
    (hbound : |Jval| ≤ JMax) (hT : teleparallelTofJ Jval r < 0) :
    Jval < 0 :=
  repulsive_requires_negative_J hr hbound hT

/-- Regression: the auxiliary expression dominates the algebraic density. -/
example {A r θ : ℝ} (hA : 0 < A) (hr : r ≠ 0) (hsin : 0 ≤ Real.sin θ) :
    algebraicDensity A r θ ≤ tegrDensity A r θ :=
  algebraicDensity_le_tegrDensity hA hr hsin

/-- Regression: sandwich for the auxiliary expression,
\(4J\le r^2 T_{\mathrm{aux}}\) and \(T_{\mathrm{aux}}\le 4J_{\mathrm{field}}\). -/
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


/-! ## Scales that are inputs -/

/-- Regression: repeated pure boosts express a fixed mismatch. -/
example {n : ℕ} (hn : 1 ≤ n) (a0 : Fin 3) :
    J (expressedSuperposition (List.replicate n (axisBoost a0 (Real.pi / 2)))) =
      Real.pi ^ 2 / 8 :=
  J_express_repeat_pure_boost hn a0

/-- Regression: the internal quadratic of those boosts has no ceiling. -/
example {n : ℕ} (hn : 2 ≤ n) (a0 : Fin 3) :
    3 * Real.pi ^ 2 / 8 <
      J (sumParams (List.replicate n (axisBoost a0 (Real.pi / 2)))) :=
  J_internal_repeat_gt_ceiling hn a0

/-- Regression: two quarter-boosts do not add their values of \(J\). -/
example (a0 : Fin 3) :
    let p := axisBoost a0 (Real.pi / 4)
    let s := sumParams [p, p]
    J s ≠ J p + J p :=
  (J_two_quarter_boosts a0).2.2.2.2.2.2

/-- Regression: on the wall the lag passes through and the quadratics overflow. -/
example {n : ℕ} (hn : 6 ≤ n) (a0 : Fin 3) :
    J (expressedSuperposition (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)) =
        Real.pi ^ 2 / 16 ∧
      mass (expressedSuperposition (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)) =
        5 * Real.pi ^ 2 / 64 ∧
      J (sumParams (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)) =
        ((n : ℝ) + 1) * Real.pi ^ 2 / 16 ∧
      3 * Real.pi ^ 2 / 8 <
        J (sumParams (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)) ∧
      J (expressedSuperposition (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)) +
          mass (expressedSuperposition (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)) <
        J (sumParams (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)) +
          mass (sumParams (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)) :=
  ⟨J_express_quarter_balancePile a0, mass_express_quarter_balancePile a0,
    J_quarter_balancePile n a0, J_quarter_balancePile_gt_ceiling hn a0,
    balancePile_JM_overflow (by positivity) (by linarith [Real.pi_pos])
      (by positivity) (le_trans (by decide : (1 : ℕ) ≤ 6) hn)⟩

/-- Regression: inside the triangle a balanced source raises \(J\). -/
example (a0 : Fin 3) :
    let b := axisBoost a0 (Real.pi / 8)
    let s := sumParams [b, axisBalance a0 (Real.pi / 8)]
    Admissible.IsAdmissibleContinuous s ∧ express s = s ∧ J b < J s :=
  let h := eighth_balance_inside a0
  ⟨h.1, h.2.1, h.2.2.2.2⟩

/-- Regression: an empty source list assigns no angular acceleration, at every stiffness. -/
example (m φddot θddot : ℝ) :
    PaperActualEL m 0 0 φddot θddot ↔ φddot = 0 ∧ θddot = 0 :=
  empty_sources_no_acceleration m φddot θddot

/-- Regression: two quarter-boosts add their common accelerations to \(-m\pi\). -/
example (m : ℝ) (a0 : Fin 3) :
    commonAccel m
        ((expressedSuperposition (List.replicate 2 (axisBoost a0 (Real.pi / 4)))).alpha a0)
        ((expressedSuperposition (List.replicate 2 (axisBoost a0 (Real.pi / 4)))).beta a0) =
      -m * Real.pi :=
  two_quarter_boosts_accel m a0

/-- Regression: balanced sources do not change the common acceleration. -/
example (m : ℝ) {n : ℕ} (a0 : Fin 3) :
    commonAccel m
        ((expressedSuperposition (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)).alpha a0)
        ((expressedSuperposition (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)).beta a0) =
      -m * Real.pi / 2 ∧
      commonAccel m
          ((sumParams (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)).alpha a0)
          ((sumParams (balancePile a0 (Real.pi / 4) (Real.pi / 4) n)).beta a0) =
        -m * Real.pi / 2 :=
  quarter_balancePile_accel m a0

/-- Regression: past the wall the internal lag pushes harder than the expressed state. -/
example {n : ℕ} {m φ : ℝ} {a0 : Fin 3}
    (hm : 0 < m) (hφ : 0 ≤ φ) (hs : Real.pi / 2 < (n : ℝ) * φ) :
    commonAccel m
        ((sumParams (List.replicate n (axisBoost a0 φ))).alpha a0)
        ((sumParams (List.replicate n (axisBoost a0 φ))).beta a0) <
      commonAccel m
        ((expressedSuperposition (List.replicate n (axisBoost a0 φ))).alpha a0)
        ((expressedSuperposition (List.replicate n (axisBoost a0 φ))).beta a0) :=
  (pure_boost_force_overflows hm hφ hs).2.1

/-- Regression: a further quarter-boost does not add another copy of the acceleration. -/
example {m : ℝ} (hm : m ≠ 0) {n : ℕ} (hn : 3 ≤ n) (a0 : Fin 3) :
    commonAccel m
        ((expressedSuperposition (List.replicate n (axisBoost a0 (Real.pi / 4)))).alpha a0)
        ((expressedSuperposition (List.replicate n (axisBoost a0 (Real.pi / 4)))).beta a0) ≠
      (n : ℝ) *
        commonAccel m
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 (Real.pi / 4)))).alpha a0)
          ((expressedSuperposition (List.replicate 1 (axisBoost a0 (Real.pi / 4)))).beta a0) :=
  quarter_boosts_past_wall hm hn a0

/-- Regression: a carried quarter-boost accelerates, and is not the empty reading. -/
example {m : ℝ} (hm : m ≠ 0) (a0 : Fin 3) :
    commonAccel m ((axisBoost a0 (Real.pi / 4)).alpha a0)
        ((axisBoost a0 (Real.pi / 4)).beta a0) = -m * Real.pi / 2 ∧
      commonAccel m ((axisBoost a0 (Real.pi / 4)).alpha a0)
          ((axisBoost a0 (Real.pi / 4)).beta a0) ≠
        commonAccel m
          ((expressedSuperposition ([] : List TorsionParams)).alpha a0)
          ((expressedSuperposition ([] : List TorsionParams)).beta a0) :=
  ⟨carried_quarter_boost_accel m a0, carried_quarter_boost_not_empty hm a0⟩


/-! ## Chart dictionary -/

/-- Regression: admissible ceiling of the auxiliary expression. -/
example {rs r : ℝ} (h : IsExterior rs r)
    (hφ : schwarzschildRapidity rs r ≤ phiMax) :
    r ^ 2 * schwarzschildTeleparallelT rs r < 27 :=
  lt_of_le_of_lt (r_sq_T_le_ceiling h hφ) four_cosh_phiMax_sub_one_bounds.2

/-- Regression: two-sided window of the auxiliary expression on the cone. -/
example {Jval r : ℝ} (hr : r ≠ 0) (hbound : |Jval| ≤ JMax) :
    4 * (Real.cos phiMax - 1) ≤ r ^ 2 * teleparallelTofJ Jval r ∧
      r ^ 2 * teleparallelTofJ Jval r ≤ 4 * (Real.cosh phiMax - 1) :=
  r_sq_teleparallelTofJ_window hr hbound

/-- Regression: numeric envelope of the auxiliary expression, not of the quadratic. -/
example {Jval r : ℝ} (hr : r ≠ 0) (hbound : |Jval| ≤ JMax) :
    -8 < r ^ 2 * teleparallelTofJ Jval r ∧
      r ^ 2 * teleparallelTofJ Jval r < 27 :=
  r_sq_teleparallelTofJ_bounds hr hbound

/-- Regression: both window ends are attained, so neither bound is improvable. -/
example {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofJ (-JMax) r = 4 * (Real.cos phiMax - 1) ∧
      r ^ 2 * teleparallelTofJ JMax r = 4 * (Real.cosh phiMax - 1) :=
  r_sq_teleparallelTofJ_window_sharp hr

/-- Regression: at a fixed radius the auxiliary expression determines \(J\). -/
example {J₁ J₂ r : ℝ} (hr : r ≠ 0) (h₁ : |J₁| ≤ JMax) (h₂ : |J₂| ≤ JMax)
    (heq : teleparallelTofJ J₁ r = teleparallelTofJ J₂ r) : J₁ = J₂ :=
  J_unique_of_teleparallelTofJ_eq hr h₁ h₂ heq

/-- Regression: closed-form inversion of the auxiliary expression. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    (1 / 2) *
        Real.arcosh (1 + r ^ 2 * schwarzschildTeleparallelT rs r / 4) ^ 2 =
      J (radialBoostParams rs r) :=
  J_radialBoostParams_eq_half_arcosh_sq h

/-- Regression: the Gödel coframe induces the chart metric. -/
example (r : ℝ) :
    inducedMetric (godelCoframe r) 2 2 = godelGφφ r :=
  induced_godel_φφ r

/-- Regression: the three-axis ceiling meets the Gödel tilt before the null circle. -/
example :
    ∃ r, 0 < r ∧ r < godelCriticalRadius ∧ godelRapidity r = phiMax ∧
      0 < godelGφφ r :=
  exists_phiMax_godel_before_loop

/-- Regression: past the null circle the tilt is not a real rapidity. -/
example {ψ r : ℝ} (hr : godelCriticalRadius < r) :
    godelTilt r ≠ Real.tanh ψ :=
  godelTilt_ne_tanh_of_gt_critical hr

/-- Regression: a pure `(t,φ)` boost writes no cross term. -/
example (ψ β : ℝ) :
    inducedMetric (cylBoostCoframe ψ β) 0 2 = 0 :=
  induced_cylBoost_tφ ψ β

/-- Regression: the Kerr `(t,φ)` block has determinant `-Δ sin²θ`. -/
example {M a r θ : ℝ} (hSig : kerrSigma a r θ ≠ 0) :
    -(1 - 2 * M * r / kerrSigma a r θ) * kerrGφφ M a r θ - kerrGtφ M a r θ ^ 2 =
      -kerrDelta M a r * Real.sin θ ^ 2 :=
  kerr_timePhi_det M a r θ hSig

/-- Regression: vanishing spin returns the exterior Schwarzschild coframe. -/
example {M r θ : ℝ} (h : IsExterior (2 * M) r) :
    kerrCoframe M 0 r θ = schwarzschildCoframe (2 * M) r θ :=
  kerrCoframe_zero_spin h

/-- Regression: a pure `(t,φ)` boost writes no Kerr cross term. -/
example (ψ β : ℝ) :
    inducedMetric (kerrAzimuthBoostCoframe ψ β) 0 3 = 0 :=
  induced_kerrAzimuthBoost_tφ ψ β

/-- Regression: exterior Schwarzschild is the vacuum specialisation of the gauge. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    HasDerivAt (fun x => x * schwarzschildA rs x) 1 r :=
  hasDerivAt_r_mul_schwarzschildA rs r (lt_trans h.1 h.2).ne'

/-- Regression: Newtonian sandwich and far-field coefficient. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    rs / (2 * r) ≤ schwarzschildRapidity rs r :=
  (schwarzschildRapidity_sandwich h).1

/-- Regression: exact witness of the auxiliary expression at \(r=\frac43 r_s\). -/
example {rs : ℝ} (hrs : 0 < rs) :
    referenceRadius rs ^ 2 *
      schwarzschildTeleparallelT rs (referenceRadius rs) = 1 :=
  r_sq_T_reference hrs


/-! ## Scales that are inputs -/

/-- Regression: the proper-time factor is strictly positive. -/
example (α β : ℝ) : 0 < gammaEff α β :=
  gammaEff_pos α β

/-- Regression: special relativity is the unexcited dual sector. -/
example (α : ℝ) : gammaEff α 0 = Real.cosh α :=
  gammaEff_sr_is_beta_zero α


/-! ## Layers and particle dynamics -/

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

/-- Regression: a null rotation keeps the null line and slides \(e_1\) along it.
The transverse reading is unchanged and the displacement is lightlike. -/
example {t : ℝ} (ht : t ≠ 0) :
    nullRotation t nullLineVec = nullLineVec ∧
      nullRotation t screenVec = screenVec + (2 * t) • nullLineVec ∧
      (nullRotation t screenVec) 1 = 1 ∧
      (nullRotation t screenVec) 2 = 0 ∧
      Q31 (nullRotation t screenVec - screenVec) = 0 ∧
      nullRotation t screenVec ≠ screenVec :=
  light_kept_on_null_line ht

/-- Regression: off the ray the transverse coordinate moves, while \(x_0+x_3\) does not. -/
example {t : ℝ} {x : Fin 4 → ℝ} (ht : t ≠ 0) (hs : x 0 + x 3 ≠ 0) :
    (nullRotation t x) 0 + (nullRotation t x) 3 = x 0 + x 3 ∧
      (nullRotation t x) 1 ≠ x 1 :=
  ⟨null_sum_invariant t x, transverse_moves_off_ray ht hs⟩

/-- Regression: one off-axis exponential is elliptic at `π/ε` and null at `ε = 0`. -/
example {ε t : ℝ} (hε : ε ≠ 0) :
    NormedSpace.exp (t • contractedGen ε) =
        Real.cos (ε * t) • (1 : PGA) +
          (t * Real.sinc (ε * t)) • contractedGen ε ∧
      NormedSpace.exp ((Real.pi / ε) • contractedGen ε) = -1 ∧
        (NormedSpace.exp (t • contractedGen ε) = -1 ↔ Real.cos (ε * t) = -1) ∧
          (Generators.commutator (contractedGen ε) (minkowskiVector nullLineVec) = 0 ↔
            ε = 0) ∧
            Real.sinc Real.pi = 0 ∧
              compactJacobian Real.pi = 0 :=
  ⟨exp_contractedGen_formula ε t, exp_contractedGen_antipode hε,
    exp_contractedGen_eq_neg_one_iff hε, commutator_contracted_nullLine_eq_zero_iff ε,
    sinc_pi, compactJacobian_antipode⟩

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


/-! ## Scales that are inputs -/

/-- Regression: acceleration per unit lag is minus the lag-second ratio. -/
example {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) (hδ : φ - θ ≠ 0) :
    (φddot + θddot) / (φ - θ) =
      -(lagPotentialSecond m ((φ + θ) / 2) (φ - θ) /
          lagMassSecond ((φ + θ) / 2) (φ - θ)) :=
  common_accel_eq_lagSecond_ratio h hδ

/-- Regression: off equal rapidity the stiffness quotient is \(2m\). -/
example {m : ℝ} {p : Operations.TorsionParams} (h : lagSq p ≠ 0) :
    stiffnessPotential m p / transverseMass p = 2 * m :=
  stiffness_quotient h


/-! ## Layers and particle dynamics -/

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


/-! ## Scales that are inputs -/

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

/-- Regression: the charged-pion Compton wavelength lies strictly inside the sign caps. -/
example : (56 / 75 : ℚ) < pionComptonFm ∧ pionComptonFm < 19 / 10 :=
  pion_inside_sign_caps

/-- Regression: under `ℓ = λ_π` the core scale lies in the inversion layer. -/
example {x : ℝ} (hx : x ∈ Set.Ioo (Real.pi + Real.pi / 4) (Real.pi + Real.pi / 2)) :
    layerRadius (pionComptonFm : ℝ) x < (SI.nnCoreScaleFm : ℝ) ∧
      (SI.nnCoreScaleFm : ℝ) < layerRadius (pionComptonFm : ℝ) resonanceRoot1 :=
  pion_core_scale_in_inversion_layer hx

/-- Regression: charge-radius lower edges lie outside the rapidity wall. -/
example :
    2 * (pionComptonFm : ℝ) / Real.pi < (SI.he4ChargeRadiusFmLower : ℝ) ∧
      2 * (pionComptonFm : ℝ) / Real.pi < (SI.lead208ChargeRadiusFmLower : ℝ) :=
  ⟨chargeRadii_outside_wall.2.1, chargeRadii_outside_wall.2.2.2.2.2⟩


/-! ## Layers and particle dynamics -/

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

/-- Regression: a larger charge places the dodecahedral root at a smaller radius. -/
example {Z W x y : ℝ} (hZ : (8 : ℝ) ≤ Z) (hW : Z < W)
    (hx : x ∈ Set.Ioo (0 : ℝ) dodecaWall) (hy : y ∈ Set.Ioo (0 : ℝ) dodecaWall)
    (hRx : dodecaResponse x = Z) (hRy : dodecaResponse y = W) :
    1 / (2 * y) < 1 / (2 * x) :=
  dodeca_root_radius_lt_of_lt_charge hZ hW hx hy hRx hRy

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

/-- Regression: an impulse does not retune a root, and the thermal mean of the
frequency shape lies strictly between `3` and `4`, above the peak. -/
example {m κ1 κ2 p : ℝ} (hm : 0 < m) (hp : p ≠ 0) (hκ1 : 0 < κ1) (hκ : κ1 < κ2) :
    longitudinalOmega κ1 m < longitudinalOmega κ2 m ∧
      impulseAmplitude m κ2 p < impulseAmplitude m κ1 p ∧
      radialEnergy m κ1 0 (p / m) = p ^ 2 / (2 * m) ∧
      (3 : ℝ) < shapeMean ∧ shapeMean < 4 ∧ planckPeak 3 < shapeMean :=
  ⟨longitudinalOmega_strictMono hm hκ1 hκ, impulseAmplitude_strictAnti hm hp hκ1 hκ,
    impulse_energy hm.ne', shapeMean_bounds.1, shapeMean_bounds.2, peak_lt_shapeMean⟩

end

/-- Regression: a cube has one radial balance in the first repulsive shell. -/
example : ∃! x : ℝ, x ∈ Set.Ioo (2 * resonanceRoot1) (branchNode 1) ∧
    cubeOutward 1 x = 0 :=
  exists_unique_cube_shell (by norm_num)

/-- Regression: a tetrahedron has one radial balance in the first repulsive shell. -/
example : ∃! x : ℝ, x ∈ Set.Ioo (resonanceRoot1 / tetraScale) (branchNode 1) ∧
    tetraOutward 1 x = 0 :=
  exists_unique_tetra_shell (by norm_num)

/-- Regression: an octahedron has one radial balance in the first repulsive shell. -/
example : ∃! x : ℝ, x ∈ Set.Ioo (2 * resonanceRoot1) (branchNode 1) ∧
    octaOutward 1 x = 0 :=
  exists_unique_octa_shell (by norm_num)

/-- Regression: a proton pair in an octahedral cage of radius `2` has one restoring seat. -/
example {Z : ℝ} (hZ : 1 ≤ Z) :
    ∃ s, 1 / (2 * resonanceRoot1) < s ∧ s < 2 ∧
      octaPairOutward Z 2 (s / 2) = 0 ∧
      (∀ s', 1 / (2 * resonanceRoot1) < s' → s' < 2 →
        octaPairOutward Z 2 (s' / 2) = 0 → s' = s) ∧
      ∀ t, 1 / (4 * resonanceRoot1) < t → t ≤ 1 →
        (t < s / 2 → 0 < octaPairOutward Z 2 t) ∧
        (s / 2 < t → octaPairOutward Z 2 t < 0) :=
  octa_pair_seat hZ

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

/-- Regression: angular-momentum squares `0`, `2`, `6`, and `12`, and the
running total `2 n²`. -/
example (a : Fin 3 → ℝ) (v : Fin 3 → ℝ) {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ quadrupole) {c : Fin 10 → ℝ} (hc : c ∈ octupole) :
    -(dipoleValue (jDip 0 1 (jDip 0 1 a)) v +
        dipoleValue (jDip 0 2 (jDip 0 2 a)) v +
        dipoleValue (jDip 1 2 (jDip 1 2 a)) v) =
      (1 * 2) * dipoleValue a v ∧
    -(quadPoly (jQuadXY (jQuadXY (quadCoeff M))) v +
        quadPoly (jQuadXZ (jQuadXZ (quadCoeff M))) v +
        quadPoly (jQuadYZ (jQuadYZ (quadCoeff M))) v) =
      (2 * 3) * quadValue M v ∧
    -(octuValue (jOctuXY (jOctuXY c)) v +
        octuValue (jOctuXZ (jOctuXZ c)) v +
        octuValue (jOctuYZ (jOctuYZ c)) v) =
      (3 * 4) * octuValue c v ∧
    2 * (Module.finrank ℝ ℝ + Module.finrank ℝ (Fin 3 → ℝ) +
      Module.finrank ℝ quadrupole + Module.finrank ℝ octupole) =
      2 * 4 ^ 2 :=
  ⟨angSq_dipole a v, angSq_quadrupole hM v, angSq_octupole hc v,
    shell_capacity_two_n_sq.2.2.2⟩

/-- Regression: a dipole changes sign across a plane. -/
example {a : Fin 3 → ℝ} (ha : dipoleValue a a ≠ 0) :=
  seatPattern_dipole ha

/-- Regression: a nonzero quadrupole is even and has a nodal direction. -/
example {M} (hM : M ∈ quadrupole) (h0 : M ≠ 0) :=
  seatPattern_quadrupole hM h0

/-- Regression: a nonzero octupole changes sign when the direction is reversed. -/
example {c} (hc : c ∈ octupole) (h0 : c ≠ 0) :=
  seatPattern_octupole hc h0

/-- Regression: the shell square restores its diagonal. -/
example {ℓ R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hx : ℓ / (2 * R) ∈ Set.Ioo (3 / 2 : ℝ) (8 / 5))
    (hy : ℓ / (2 * S) ∈ Set.Ioo (3 / 2 : ℝ) (8 / 5))
    (h0 : squareBalance (ℓ / (2 * R)) = 0) :
    (covalentAxial ℓ S (S / 2) < 0 ↔ R < S) ∧
      (0 < covalentAxial ℓ S (S / 2) ↔ S < R) :=
  square_diagonal_restores hR hS hx hy h0

/-- Regression: the first-node coefficient of \(\varepsilon\) lies in the slope bracket. -/
example :
    (Real.pi / (2 * Real.sqrt 2)) * Real.cosh (Real.pi / 4) <
      resonanceRoot1 * (2 * Real.cosh resonanceRoot1 * Real.sin resonanceRoot1) ∧
    resonanceRoot1 * (2 * Real.cosh resonanceRoot1 * Real.sin resonanceRoot1) <
      2 * Real.cosh 1 * Real.sin 1 :=
  firstNode_eps_coeff_bounds

/-- Regression: the midplane pair has no outer-well balance at any ratio. -/
example {ℓ R ρ : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hρ : 0 < ρ)
    (hRwell : ℓ / (2 * R) ∈ Set.Ioo (0 : ℝ) resonanceRoot1)
    (hEwell : ℓ / (2 * (2 * ρ)) ∈ Set.Ioo (0 : ℝ) resonanceRoot1) :
    ¬ (covalentAxial ℓ R ρ = 0 ∧ covalentRadial ℓ R ρ = 0) :=
  no_midplane_outer_equilibrium hℓ hR hρ hRwell hEwell

/-- Regression: both midplane forces vanish exactly when the three weights agree. -/
example {ℓ R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hγR : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγee : gammaSEqual (ℓ / (2 * (2 * ρ))) ≠ 0)
    (hγep : gammaSEqual (ℓ / (2 * Real.sqrt ((R / 2) ^ 2 + ρ ^ 2))) ≠ 0) :
    covalentAxial ℓ R ρ = 0 ∧ covalentRadial ℓ R ρ = 0 ↔
      gammaSEqual (ℓ / (2 * R)) * R ^ 3 =
          gammaSEqual (ℓ / (2 * Real.sqrt ((R / 2) ^ 2 + ρ ^ 2))) *
            (Real.sqrt ((R / 2) ^ 2 + ρ ^ 2)) ^ 3 ∧
        gammaSEqual (ℓ / (2 * Real.sqrt ((R / 2) ^ 2 + ρ ^ 2))) *
            (Real.sqrt ((R / 2) ^ 2 + ρ ^ 2)) ^ 3 =
          gammaSEqual (ℓ / (2 * (2 * ρ))) * (2 * ρ) ^ 3 :=
  covalent_forces_iff_weights hR hρ hγR hγee hγep

/-- Regression: no midplane equilibrium while the electron–proton separation is outer. -/
example {ℓ R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hEp : ℓ / (2 * Real.sqrt ((R / 2) ^ 2 + ρ ^ 2)) ∈ Set.Ioo (0 : ℝ) resonanceRoot1) :
    ¬ (covalentAxial ℓ R ρ = 0 ∧ covalentRadial ℓ R ρ = 0) :=
  no_midplane_ep_outer hR hρ hEp

/-- Regression: at a square root the side force is the diagonal force over √2. -/
example {ℓ R : ℝ} (hR : 0 < R)
    (hγ : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγs : gammaSEqual (Real.sqrt 2 * (ℓ / (2 * R))) ≠ 0)
    (hbal : squareBalance (ℓ / (2 * R)) = 0) :
    |1 / (gammaSEqual (Real.sqrt 2 * (ℓ / (2 * R))) * (R / Real.sqrt 2) ^ 2)| =
      |1 / (gammaSEqual (ℓ / (2 * R)) * R ^ 2)| / Real.sqrt 2 :=
  square_side_eq_diag_div_sqrtTwo hR hγ hγs hbal

/-- Regression: charge two is not a square equilibrium. -/
example {ℓ R : ℝ} (hR : 0 < R)
    (hγ : gammaSEqual (ℓ / (2 * R)) ≠ 0)
    (hγs : gammaSEqual (Real.sqrt 2 * (ℓ / (2 * R))) ≠ 0) :
    ¬ (heliumAxial 2 ℓ R (R / 2) = 0 ∧ heliumRadial 2 ℓ R (R / 2) = 0) :=
  helium_square_not_balance (by norm_num) (by norm_num) hR hγ hγs

/-- Regression: charge two has no outer-well midplane balance. -/
example {ℓ R ρ : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hρ : 0 < ρ)
    (hRwell : ℓ / (2 * R) ∈ Set.Ioo (0 : ℝ) resonanceRoot1)
    (hEwell : ℓ / (2 * (2 * ρ)) ∈ Set.Ioo (0 : ℝ) resonanceRoot1) :
    ¬ (heliumAxial 2 ℓ R ρ = 0 ∧ heliumRadial 2 ℓ R ρ = 0) :=
  helium_no_outer_equilibrium hℓ hR hρ hRwell hEwell

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

/-- Regression: the two bonds have no common outer tangential zero. -/
example {Z r R θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (hr : 0 < r) (hR : 0 < R) (hne : r ≠ R)
    (hee : outerSep (2 * r * Real.sin (θ / 2)))
    (hhh : outerSep (2 * R * Real.sin (θ / 2)))
    (hc : gammaSEqual (pairPhase
      (Real.sqrt (r ^ 2 + R ^ 2 - 2 * r * R * Real.cos θ))) ≠ 0) :
    ¬ (waterBendElectron Z r R (θ / 2) = 0 ∧ waterBendProton Z r R (θ / 2) = 0) :=
  water_no_outer_tangent hθ hr hR hne hee hhh hc

/-- Regression: the nearer bonding electron is driven toward a wider angle. -/
example {Z r R a : ℝ}
    (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hr : 0 < r) (hrR : r < R)
    (hee : outerSep (2 * r * Real.sin a)) :
    0 < waterBendElectron Z r R a :=
  waterBendElectron_opening ha hr hrR hee

/-- Regression: an electron on the same ray adds no tangent. -/
example (r a q s : ℝ) :
    waterExtraTangent r a q (vsmul s (waterU a)) = 0 :=
  waterExtraTangent_same_ray r a q s

/-- Regression: an electron between the bonds, while it repels, pushes wider. -/
example {r a μ : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hμ : 0 < μ)
    (hsep : outerSep (vnorm (vsub (vsmul r (waterU a)) (bondAxis μ)))) :
    0 < waterExtraTangent r a (-1) (bondAxis μ) :=
  waterExtraTangent_bisector_pos ha hμ hsep

/-- Regression: on the straight line a far electron drives the bond off the line. -/
example {Z r R lam : ℝ} (hr : outerSep r) (hR : outerSep R) (hlam : 0 < lam) :
    waterBendElectron Z r R (Real.pi / 2) +
      waterExtraTangent r (Real.pi / 2) (-1) (bondAxis (-lam)) < 0 :=
  water_straight_far_neg hr hR hlam

/-- Regression: nonnegative extra tangents leave the bond opening. -/
example {Z r R a : ℝ}
    (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hr : 0 < r) (hrR : r < R)
    (hee : outerSep (2 * r * Real.sin a)) :
    0 < waterBendElectron Z r R a +
      waterTangentSum r a (fun _ : Fin 0 => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := by
  refine waterMolecule_opening ha hr hrR hee ?_
  intro i
  exact Fin.elim0 i

/-- Regression: three shared pairs meet between the four-pair angle and a straight angle. -/
example :
    Real.pi / 2 < Real.arccos tetCos ∧
      Real.arccos tetCos < Real.arccos triCos ∧
      Real.arccos triCos < Real.pi :=
  shared_angle_order

/-- Regression: three coplanar shared pairs exert no tangential force. -/
example {Z r R : ℝ} {i : Fin 3}
    (hr : outerSep r) (hR : r < R) (hgap : outerSep (R - r)) :
    vdot (triPerp i) (electronForce Z i r R) = 0 ∧
      vdot triZ (electronForce Z i r R) = 0 ∧
      vdot (triPerp i) (protonForce Z i r R) = 0 ∧
      vdot triZ (protonForce Z i r R) = 0 :=
  tri_tangent_zero hr hR hgap

/-- Regression: an axial electron no farther than the bonds folds each ray the same way. -/
example {Z r R s : ℝ} {i : Fin 3}
    (hr : 0 < r) (hR : 0 < R) (hs : 0 ≤ s)
    (hwell : outerSep s) (hsr : s ≤ r) (hrR : r < R) :
    -r * (electronForce Z i r R 2 +
        pairForce (-1) (-1) (vsmul r (triU i)) (triAxis s) 2) -
      R * (protonForce Z i r R 2 +
        pairForce 1 (-1) (vsmul R (triU i)) (triAxis s) 2) =
      triBend r R s ∧ 0 < triBend r R s :=
  ⟨triRay_bend_eq hr hR hs, triBend_pos hwell hsr hrR⟩

/-- Regression: on the straight water molecule the outward sum is negative. -/
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

/-- Regression: the centripetal formula is not a radius law. Where it is written,
a repulsive layer gives a negative square. -/
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


/-! ## One Faraday six-space -/

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


/-! ## Scales that are inputs -/

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

/-- Regression: the \(S^3\) shape diverges at the antipode. -/
example : Filter.Tendsto rotationShape (nhdsWithin Real.pi (Set.Iio Real.pi)) Filter.atTop :=
  tendsto_rotationShape_pi

/-- Regression: Milky-Way antipode \(25<\pi R<29\,\mathrm{kpc}\). -/
example : (25 : ℝ) < Real.pi * milkyWayROverKpc ∧ Real.pi * milkyWayROverKpc < 29 :=
  milkyWayAntipode_bounds

/-- Regression: dual image lattice sum. -/
example {x : ℝ} (hx : x ≠ 0) :
    HasSum (fun n : ℤ => x ^ 2 / (x ^ 2 + ((n : ℝ) * Real.pi) ^ 2)) (dualEnhancement x) :=
  hasSum_dualImage hx

/-- Regression: windings of the dual phase sum to the lattice acceleration. -/
example {G M R r : ℝ} (hr : r ≠ 0) (hR : R ≠ 0) :
    HasSum (fun n : ℤ => G * M / (r ^ 2 + ((n : ℝ) * Real.pi * R) ^ 2))
      (dualAccel G M R r) :=
  hasSum_dualAccel hr hR

/-- Regression: \(\max(1,x)<x\coth x<\min(1+x,1+x^2/3)\). -/
example {x : ℝ} (hx : 0 < x) :
    1 < dualEnhancement x ∧ x < dualEnhancement x ∧ dualEnhancement x < 1 + x ∧
      dualEnhancement x < 1 + x ^ 2 / 3 :=
  ⟨one_lt_dualEnhancement hx, self_lt_dualEnhancement hx, dualEnhancement_lt_one_add hx,
    dualEnhancement_lt_one_add_sq_div_three hx⟩

/-- Regression: acceleration sandwich of the lattice. -/
example {G M R r : ℝ} (hGM : 0 < G * M) (hR : 0 < R) (hr : 0 < r) :
    G * M / r ^ 2 < dualAccel G M R r ∧ G * M / (r * R) < dualAccel G M R r ∧
      dualAccel G M R r < G * M / r ^ 2 + G * M / (r * R) ∧
      dualAccel G M R r < G * M / r ^ 2 + G * M / (3 * R ^ 2) :=
  dualAccel_bounds hGM hR hr

/-- Regression: the pushed great-circle tangent has moment `chordMoment`. -/
example (χ ψ α : ℝ) (hs : Real.sin χ ≠ 0) :
    SlerpTorque.pushedMoment χ ψ α = SlerpTorque.chordMoment χ ψ α :=
  SlerpTorque.pushedMoment_eq χ ψ α hs

/-- Regression: equal chart distances give a positive moment on \((0,\pi)\). -/
example {χ α : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) (hα : 0 < α) (hαu : α < Real.pi) :
    0 < SlerpTorque.chordMoment χ χ α :=
  SlerpTorque.chordMoment_equal_pos hχ hχu hα hαu

/-- Regression: reflection through a chart plane commutes with the log chart. -/
example {χ : ℝ} {n : SlerpTorque.V3} (hn : SlerpTorque.dot3 n n = 1)
    (hχ : 0 < χ) (hχu : χ < Real.pi) :
    SlerpTorque.logChart (SlerpTorque.lift χ (ChartRotation.reflectZ n)) =
      ChartRotation.reflectZ (SlerpTorque.logChart (SlerpTorque.lift χ n)) :=
  ChartRotation.logChart_reflectZ hn hχ hχu

/-- Regression: a common left translation preserves the relative rotor. -/
example (t : ℝ) (a b : RelationalPosition.S3) :
    RelationalPosition.relative (CliffordParallel.hopfI t * a)
        (CliffordParallel.hopfI t * b) =
      RelationalPosition.relative a b :=
  ChartRotation.common_left_preserves_relative t a b

/-- Regression: a second logarithm does not return the chart velocity. -/
example {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    (fun i => χ * ChartRotation.axisJ i) ≠ ChartRotation.leftVelocity χ ∧
      ChartRotation.leftVelocity χ ≠ ChartRotation.secondLogVelocity χ ∧
      ChartRotation.secondLogVelocity (Real.pi / 2) 0 = -1 ∧
      ChartRotation.leftVelocity (Real.pi / 2) 2 = Real.pi / 2 :=
  ⟨ChartRotation.iterated_log_ne_leftVelocity hχ hχu,
    ChartRotation.leftVelocity_ne_secondLog hχ hχu,
    ChartRotation.secondLogVelocity_equator_value.1,
    ChartRotation.leftVelocity_equator_value.2⟩

/-- Regression: six axis intercepts are torque-free, and `a < b < c` makes them triaxial. -/
example {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    ChartRotation.axisPairTorque a b = 0 ∧
      ChartRotation.secondZ a b c < ChartRotation.secondY a b c ∧
      ChartRotation.secondY a b c < ChartRotation.secondX a b c :=
  ⟨(ChartRotation.axisInterceptTorque_zero a b c).1,
    (ChartRotation.principal_ordered ha hab hbc).1,
    (ChartRotation.principal_ordered ha hab hbc).2⟩

/-- Regression: moving one partner off the ray turns a vanishing moment positive. -/
example {χ α : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) (hα : 0 < α) (hαu : α < Real.pi) :
    SlerpTorque.chordMoment χ χ 0 = 0 ∧ 0 < ChartRotation.defectTorque χ α :=
  ChartRotation.displacement_seeds_torque hχ hχu hα hαu

/-- Regression: the separatrix keeps `L² = 2EI₂` and crosses zero only at the origin of time. -/
example {I1 I2 I3 B t : ℝ} (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) :
    RacketFlip.racketLsq I1 I2 I3 B t = 2 * RacketFlip.racketEnergy I1 I2 I3 B t * I2 ∧
      (RacketFlip.omega2 I1 I2 I3 B t = 0 ↔ t = 0) :=
  ⟨RacketFlip.racket_critical h1 h12 h23 hB t, RacketFlip.omega2_eq_zero_iff h1 h12 h23 hB t⟩

/-- Regression: only the intermediate axis has a positive squared rate. -/
example {I1 I2 I3 Ω : ℝ} (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hΩ : Ω ≠ 0) :
    0 < RacketFlip.rateMid I1 I2 I3 Ω ∧ RacketFlip.rateSmall I1 I2 I3 Ω < 0 ∧
      RacketFlip.rateLarge I1 I2 I3 Ω < 0 :=
  ⟨RacketFlip.rateMid_pos h1 h12 h23 hΩ, RacketFlip.rateSmall_neg h1 h12 h23 hΩ,
    RacketFlip.rateLarge_neg h1 h12 h23 hΩ⟩

/-- Regression: a residual below one sixth waits longer than the crossing. -/
example {k ε : ℝ} (hk : 0 < k) (hε : 0 < ε) (hεu : ε < 1 / 6) :
    RacketFlip.crossingTime k < RacketFlip.waitingTime k ε :=
  RacketFlip.waiting_gt_crossing hk hε hεu

/-- Regression: a mirror ensemble has mean torque zero and mean square the sum of squares. -/
example (m : Fin 2 → ℝ) :
    RacketThermal.mirrorAverage (fun σ => RacketThermal.mirrorTorque m σ) = 0 ∧
      RacketThermal.mirrorAverage (fun σ => RacketThermal.mirrorTorque m σ ^ 2) =
        ∑ i, m i ^ 2 :=
  ⟨RacketThermal.mirrorAverage_zero m, RacketThermal.mirrorAverage_sq m⟩

/-- Regression: the canonical mean of the separatrix gap is `(I₁ + I₃ - 2 I₂)/β`. -/
example {β I1 I2 I3 : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (h2 : 0 < I2) (h3 : 0 < I3) :
    ∫ p : ℝ × ℝ × ℝ, RacketThermal.separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2
        ∂RacketThermal.rotorMeasure β I1 I2 I3 =
      (I1 + I3 - 2 * I2) / β :=
  RacketThermal.meanGap hβ h1 h2 h3

/-- Regression: residuals that wait longer than the crossing have positive canonical weight. -/
example {β I1 I2 I3 B : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3)
    (hB : 0 < B) :
    0 < RacketThermal.rotorMeasure β I1 I2 I3 (RacketThermal.residualSet I1 I2 I3 B) :=
  RacketThermal.residual_weight_pos hβ h1 h12 h23 hB

/-- Regression: the nucleus frame keeps the electron–electron rotor. -/
example (n a b : RelationalPosition.S3) :
    HeliumBody.ee (HeliumBody.toFrame n a b) = RelationalPosition.relative a b :=
  HeliumBody.ee_toFrame n a b

/-- Regression: exchange swaps the two nuclear cosines and keeps the third. -/
example (p : HeliumBody.Frame) :
    HeliumBody.cosA (HeliumBody.exchange p) = HeliumBody.cosB p ∧
      HeliumBody.cosEE (HeliumBody.exchange p) = HeliumBody.cosEE p :=
  ⟨(HeliumBody.cos_exchange p).1, (HeliumBody.cos_exchange p).2.2⟩

/-- Regression: the singlet sector changes sign under the joint exchange. -/
example (F : HeliumBody.Frame → ℂ) (hF : HeliumBody.Symmetric F) (c : ℂ) (p : HeliumBody.Frame) :
    F (HeliumBody.exchange p) • DstDiophantine.Logic.pairSwap (c • DstDiophantine.Logic.singlet) =
      -(F p • (c • DstDiophantine.Logic.singlet)) :=
  HeliumBody.singlet_sector_exchange F hF c p

/-- Regression: \(\rho(a,b)=1\) if and only if the two elements coincide. -/
example (a b : RelationalPosition.S3) :
    RelationalPosition.relative a b = 1 ↔ a = b :=
  RelationalPosition.relative_eq_one_iff a b

/-- Regression: a left rotation leaves the relative position fixed. -/
example (g a b : RelationalPosition.S3) :
    RelationalPosition.relative (g * a) (g * b) = RelationalPosition.relative a b :=
  RelationalPosition.relative_left g a b

/-- Regression: a right rotation preserves the geodesic angle. -/
example (a b h : RelationalPosition.S3) :
    RelationalPosition.separation (a * h) (b * h) = RelationalPosition.separation a b :=
  RelationalPosition.separation_right a b h

/-- Regression: body, source, and pole, rotated together, keep the chart readings. -/
example (g : RelationalPosition.S3) {χ ψ α : ℝ}
    (hχ : 0 < χ) (hχu : χ < Real.pi) (hψ : 0 < ψ) (hψu : ψ < Real.pi) :
    RelationalPosition.chartAt g (g * RelationalPosition.bodyElem χ) =
        SlerpTorque.bodyPoint χ ∧
      RelationalPosition.chartAt g (g * RelationalPosition.sourceElem ψ α) =
        SlerpTorque.sourcePoint ψ α :=
  RelationalPosition.charts_joint_left g hχ hχu hψ hψu

/-- Regression: one pair has positive moment about the identity pole. After the
right translation that puts the source at the pole and the body on the first
axis, the moment is zero and the angle is unchanged. -/
example :
    0 < SlerpTorque.chordMoment RelationalPosition.sampleχ RelationalPosition.sampleχ
        RelationalPosition.sampleχ ∧
      RelationalPosition.chartAt
          (RelationalPosition.sampleSource * RelationalPosition.axisTurn)
          (RelationalPosition.sampleBody * RelationalPosition.axisTurn) =
        SlerpTorque.bodyPoint (-RelationalPosition.sampleχ) ∧
      SlerpTorque.pushedMoment (-RelationalPosition.sampleχ) 0 0 = 0 ∧
      SlerpTorque.chordMoment RelationalPosition.sampleχ RelationalPosition.sampleχ
          RelationalPosition.sampleχ ≠
        SlerpTorque.pushedMoment (-RelationalPosition.sampleχ) 0 0 ∧
      RelationalPosition.separation
          (RelationalPosition.sampleSource * RelationalPosition.axisTurn)
          (RelationalPosition.sampleBody * RelationalPosition.axisTurn) =
        RelationalPosition.separation RelationalPosition.sampleSource
          RelationalPosition.sampleBody := by
  obtain ⟨_, _, _, hpos, hbody, _, hzero, hdiff, hsep⟩ :=
    RelationalPosition.pole_shift_changes_moment
  exact ⟨hpos, hbody, hzero, hdiff, hsep⟩

/-- Regression: a left Clifford step is the same rotor at every base point. -/
example (q : RelationalPosition.S3) (t s : ℝ) :
    (CliffordParallel.leftParallel q t)⁻¹ * CliffordParallel.leftParallel q (t + s) =
      CliffordParallel.hopfI s :=
  CliffordParallel.leftParallel_step q t s

/-- Regression: conjugation swaps the two parallel families and reverses the step. -/
example (q : RelationalPosition.S3) (t : ℝ) :
    (CliffordParallel.leftParallel q t)⁻¹ = CliffordParallel.rightParallel q⁻¹ (-t) :=
  CliffordParallel.mirror_parallel q t

/-- Regression: a rotation carries each parallel family onto itself. -/
example (a b q : RelationalPosition.S3) (t : ℝ) :
    a * CliffordParallel.leftParallel q t * b =
      (a * q * b) * (b⁻¹ * CliffordParallel.hopfI t * b) ∧
      a * CliffordParallel.rightParallel q t * b =
        (a * CliffordParallel.hopfI t * a⁻¹) * (a * q * b) :=
  ⟨CliffordParallel.rotation_carries_left a b q t,
    CliffordParallel.rotation_carries_right a b q t⟩

/-- Regression: through `J` the two families end a quarter turn at opposite points. -/
example :
    (CliffordParallel.leftParallel CliffordParallel.sJ (Real.pi / 2)).val =
      -CliffordParallel.qK ∧
      (CliffordParallel.rightParallel CliffordParallel.sJ (Real.pi / 2)).val =
        CliffordParallel.qK ∧
      CliffordParallel.leftParallel CliffordParallel.sJ (Real.pi / 2) ≠
        CliffordParallel.rightParallel CliffordParallel.sJ (Real.pi / 2) :=
  CliffordParallel.family_sense

/-- Regression: on `(0, π/2)` the two screws are strict and opposite. -/
example {φ : ℝ} (h0 : 0 < φ) (hπ : φ < Real.pi / 2) :
    (CliffordParallel.twistedJ φ).imK = -Real.sin (2 * φ) ∧
      (CliffordParallel.twistedJ (-φ)).imK = Real.sin (2 * φ) ∧
      (CliffordParallel.twistedJ φ).imK < 0 ∧
      0 < (CliffordParallel.twistedJ (-φ)).imK :=
  CliffordParallel.screw_sign h0 hπ

/-- Regression: the moment is odd in the oriented angle, the reflected pair
cancels, and the equal-distance moment is negative on `(-π, 0)`. -/
example {χ ψ α : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi)
    (hα : -Real.pi < α) (hα0 : α < 0) :
    SlerpTorque.chordMoment χ ψ (-α) = -SlerpTorque.chordMoment χ ψ α ∧
      SlerpTorque.chordMoment χ ψ α + SlerpTorque.chordMoment χ ψ (-α) = 0 ∧
      SlerpTorque.chordMoment χ χ α < 0 :=
  ⟨SlerpTorque.chordMoment_neg_angle χ ψ α, SlerpTorque.chordMoment_cancels χ ψ α,
    SlerpTorque.chordMoment_equal_neg hχ hχu hα hα0⟩

/-- Regression: on \([0,\pi/2]\) the mirror frames differ by twice the geodesic angle. -/
example {φ : ℝ} (h0 : 0 ≤ φ) (hπ : φ ≤ Real.pi / 2) :
    Real.arccos ((star CliffordParallel.qJ * CliffordParallel.twistedJ φ).re) = 2 * φ :=
  CliffordParallel.twist_angle h0 hπ

/-- Regression: at the patch edge the gravitational mismatch is \(2\), and the
ratio of the two channels' mismatches is \(\Lambda/R\). -/
example {R s Λ : ℝ} (hR : R ≠ 0) (hs : s ≠ 0) (hΛ : Λ ≠ 0) :
    CliffordParallel.mirrorTwist R R = 2 ∧
      CliffordParallel.mirrorTwist s R / CliffordParallel.mirrorTwist s Λ = Λ / R :=
  ⟨CliffordParallel.mirrorTwist_edge hR, CliffordParallel.mirrorTwist_ratio hs hR hΛ⟩

/-- Regression: Hubble window for the frame mismatch. \(H_0\) is an external input. -/
example {R H : ℝ} (hRlo : (8 : ℝ) ≤ R) (hRhi : R ≤ 9)
    (hHlo : (67 : ℝ) ≤ H) (hHhi : H ≤ 74) :
    (450138 : ℝ) < ((SI.speedOfLight : ℝ) / H) / R ∧
      ((SI.speedOfLight : ℝ) / H) / R < 559315 ∧
      (357 : ℝ) / 10 ^ 8 < 2 * R / ((SI.speedOfLight : ℝ) / H) ∧
      2 * R / ((SI.speedOfLight : ℝ) / H) < (445 : ℝ) / 10 ^ 8 :=
  CliffordParallel.hubble_frame_window hRlo hRhi hHlo hHhi

/-- Regression: the patch radius over the Hubble length, and the resulting
ceilings on the cosmic Jacobian and the two fractional excesses. -/
example {r R H : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlo : (8 : ℝ) ≤ R) (hRhi : R ≤ 9)
    (hHlo : (67 : ℝ) ≤ H) (hHhi : H ≤ 74) :
    (1787 : ℝ) / 10 ^ 9 < R / ((SI.speedOfLight : ℝ) / H) ∧
      R / ((SI.speedOfLight : ℝ) / H) < 2222 / 10 ^ 9 ∧
      0 < 1 - compactJacobian (r / ((SI.speedOfLight : ℝ) / H)) ∧
      1 - compactJacobian (r / ((SI.speedOfLight : ℝ) / H)) < 1646 / 10 ^ 15 ∧
      dualEnhancement (r / ((SI.speedOfLight : ℝ) / H)) - 1 < 1646 / 10 ^ 15 ∧
      (18836 : ℝ) * 10 ^ 7 <
        (dualEnhancement 1 - 1) /
          (dualEnhancement (R / ((SI.speedOfLight : ℝ) / H)) - 1) :=
  hubble_patch_reading hr hrR hRlo hRhi hHlo hHhi

/-- Regression: the equidistant chart writes the pole and the antipode at one
origin. Angle \(\pi\) occurs only there, and every rotation fixes the rotor \(-1\).
Distinct directions at distance \(\pi\) are that one element. -/
example (a b : RelationalPosition.S3) (r : RelationalPosition.Rotation) :
    RelationalPosition.chartAt a a = RelationalPosition.chartAt a (RelationalPosition.antipode a) ∧
      (RelationalPosition.separation a b = Real.pi ↔ b = RelationalPosition.antipode a) ∧
      RelationalPosition.relative (r.act a) (r.act (RelationalPosition.antipode a)) =
        RelationalPosition.negOne ∧
      RelationalPosition.elem Real.pi RelationalPosition.axis0 RelationalPosition.axis0_unit =
        RelationalPosition.elem Real.pi (RelationalPosition.axisAngle (Real.pi / 2))
          (RelationalPosition.axisAngle_unit (Real.pi / 2)) := by
  obtain ⟨hchart, _, _, _, _, hfix⟩ := RelationalPosition.flattened_chart_loses_antipode a r
  obtain ⟨h0, h1, _⟩ := RelationalPosition.boundary_one_element
  exact ⟨hchart, RelationalPosition.separation_eq_pi_iff a b, hfix, h0.trans h1.symm⟩

/-- Regression: spherical rotation curve \((GM(r)/R)\coth(r/R)\). -/
example {G R r : ℝ} {M : ℝ → ℝ} (hr : r ≠ 0) (hR : R ≠ 0) :
    dualRotationSq R (fun s => G * M s / s) r = dualCircularSpeedSq G R M r :=
  dualRotationSq_spherical hr hR

/-- Regression: a Keplerian baryonic tail flattens at \(GM/R\). -/
example {R GM : ℝ} {vbarSq : ℝ → ℝ} (hR : 0 < R)
    (h : Filter.Tendsto (fun r => r * vbarSq r) Filter.atTop (nhds GM)) :
    Filter.Tendsto (dualRotationSq R vbarSq) Filter.atTop (nhds (GM / R)) :=
  tendsto_dualRotationSq_atTop hR h

/-- Regression: past \(3R\) outside the mass, within \(1/200\) of the asymptote. -/
example {G R M0 r : ℝ} {M : ℝ → ℝ} (hGM : 0 < G * M0) (hR : 0 < R) (hr : 3 * R ≤ r)
    (hM : M r = M0) :
    dualCircularSpeedSq G R M r < (1 + 1 / 200) * (G * M0 / R) :=
  dualCircularSpeedSq_near_flat hGM hR hr hM

/-- Regression: exact baryonic Tully–Fisher given \(R^2=GM/a_0\). -/
example {G M R a0 : ℝ} (hR : 0 < R) (ha0 : 0 < a0) (hscale : R ^ 2 = G * M / a0) :
    (G * M / R) ^ 2 = G * M * a0 :=
  dual_tullyFisher hR ha0 hscale

/-- Regression: enhancement at \(GM/r^2=a_0\). -/
example : (131 / 100 : ℝ) < dualEnhancement 1 ∧ dualEnhancement 1 < 132 / 100 :=
  dualEnhancement_one_bounds

/-- Regression: on \(R^2=GM/a_0\) the lattice is \(\sqrt{a_0g_N}\coth\sqrt{a_0/g_N}\). -/
example {G M R a0 r : ℝ} (hGM : 0 < G * M) (hR : 0 < R) (ha0 : 0 < a0) (hr : 0 < r)
    (hscale : R ^ 2 = G * M / a0) :
    dualAccel G M R r = dualRAR a0 (G * M / r ^ 2) :=
  dualAccel_eq_dualRAR hGM hR ha0 hr hscale

/-- Regression: acceleration-relation sandwich. -/
example {a0 gN : ℝ} (ha0 : 0 < a0) (hgN : 0 < gN) :
    gN < dualRAR a0 gN ∧ Real.sqrt (a0 * gN) < dualRAR a0 gN ∧
      dualRAR a0 gN < gN + Real.sqrt (a0 * gN) ∧ dualRAR a0 gN < gN + a0 / 3 :=
  dualRAR_bounds ha0 hgN

/-- Regression: fixed radius is additive in mass. -/
example (G R r M₁ M₂ : ℝ) :
    dualAccel G (M₁ + M₂) R r = dualAccel G M₁ R r + dualAccel G M₂ R r :=
  dualAccel_add G R r M₁ M₂

/-- Regression: mass-scaled relation is strictly subhomogeneous. -/
example {a0 gN k : ℝ} (ha0 : 0 < a0) (hgN : 0 < gN) (hk : 1 < k) :
    dualRAR a0 (k * gN) < k * dualRAR a0 gN :=
  dualRAR_strict_subhomogeneous ha0 hgN hk

/-- Regression: three-sphere enhancement above the shared germ. -/
example {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) :
    1 + x ^ 2 / 3 < enhancement x :=
  enhancement_gt_curvatureGerm hx hxπ

/-- Regression: solar compactification radius, in astronomical units. -/
example :
    (7020 : ℝ) * astronomicalUnit < solarCompactR ∧
      solarCompactR < (7040 : ℝ) * astronomicalUnit :=
  solarCompactR_bounds

/-- Regression: solar dual excess at one astronomical unit. -/
example :
    dualEnhancement ((astronomicalUnit : ℝ) / solarCompactR) - 1 < 1 / 10 ^ 8 :=
  solar_dualExcess_at_au

/-- Regression: Milky-Way rapidity fraction at its compactification radius. -/
example :
    schwarzschildRapidity milkyWayRs milkyWayCompactR /
        (milkyWayRs / (2 * milkyWayCompactR)) - 1 < 1 / 10 ^ 6 :=
  milkyWay_fractionalRapidity_at_compactification

/-- Regression: \(g=a_0\coth 1\) at \(g_N=a_0\). -/
example {a0 : ℝ} (ha0 : 0 < a0) :
    dualRAR a0 a0 = a0 * (Real.cosh 1 / Real.sinh 1) :=
  dualRAR_self ha0

/-- Regression: enclosed-patch curve \(v^2=v_{\mathrm{bar}}^2\,x\coth x\),
\(x^2=a_0r/v_{\mathrm{bar}}^2\). -/
example {a0 r : ℝ} {vbarSq : ℝ → ℝ} (ha0 : 0 < a0) (hr : 0 < r) (hv : 0 < vbarSq r) :
    dualLocalRotationSq a0 vbarSq r =
      vbarSq r * dualEnhancement (Real.sqrt (a0 * r / vbarSq r)) :=
  dualLocalRotationSq_eq ha0 hr hv

/-- Regression: enclosed-patch curve sandwich. -/
example {a0 r : ℝ} {vbarSq : ℝ → ℝ} (ha0 : 0 < a0) (hr : 0 < r) (hv : 0 < vbarSq r) :
    vbarSq r < dualLocalRotationSq a0 vbarSq r ∧
      Real.sqrt (a0 * (r * vbarSq r)) < dualLocalRotationSq a0 vbarSq r ∧
      dualLocalRotationSq a0 vbarSq r < vbarSq r + Real.sqrt (a0 * (r * vbarSq r)) :=
  dualLocalRotationSq_bounds ha0 hr hv

/-- Regression: a Keplerian tail flattens at \(\sqrt{GMa_0}\) on the enclosed patch. -/
example {a0 GM : ℝ} {vbarSq : ℝ → ℝ} (ha0 : 0 < a0) (hGM : 0 < GM)
    (h : Filter.Tendsto (fun r => r * vbarSq r) Filter.atTop (nhds GM)) :
    Filter.Tendsto (dualLocalRotationSq a0 vbarSq) Filter.atTop (nhds (Real.sqrt (a0 * GM))) :=
  tendsto_dualLocalRotationSq_atTop ha0 hGM h

/-- Regression: Milky-Way \(175<v_\infty<176\,\mathrm{km/s}\). -/
example :
    ((175 * 10 ^ 3 : ℚ)) ^ 4 < milkyWayFlatSpeedFourth ∧
      milkyWayFlatSpeedFourth < ((176 * 10 ^ 3 : ℚ)) ^ 4 :=
  milkyWayFlatSpeedFourth_bounds

/-- Regression: dwarf \(50.2<v_\infty<50.3\,\mathrm{km/s}\). -/
example :
    ((502 * 10 ^ 2 : ℚ)) ^ 4 < dwarfFlatSpeedFourth ∧
      dwarfFlatSpeedFourth < ((503 * 10 ^ 2 : ℚ)) ^ 4 :=
  dwarfFlatSpeedFourth_bounds

/-- Regression: low-surface-brightness \(83.1<v_\infty<83.2\,\mathrm{km/s}\). -/
example :
    ((831 * 10 ^ 2 : ℚ)) ^ 4 < lsbFlatSpeedFourth ∧
      lsbFlatSpeedFourth < ((832 * 10 ^ 2 : ℚ)) ^ 4 :=
  lsbFlatSpeedFourth_bounds

/-- Regression: dwarf ball of radius \(0.8\,\mathrm{kpc}\), and the flat stretch past it. -/
example :
    ((552 * 10 ^ 2) ^ 4 : ℝ) < dwarfPointSpeedSq (4 / 5) ^ 2 ∧
      dwarfPointSpeedSq (4 / 5) ^ 2 < ((553 * 10 ^ 2) ^ 4 : ℝ) ∧
      ((50380 : ℕ) ^ 4 : ℝ) < dwarfPointSpeedSq 2 ^ 2 ∧
      dwarfPointSpeedSq 2 ^ 2 < ((50390 : ℕ) ^ 4 : ℝ) ∧
      ((502 * 10 ^ 2) ^ 4 : ℝ) < dwarfPointSpeedSq 4 ^ 2 ∧
      dwarfPointSpeedSq 4 ^ 2 < ((503 * 10 ^ 2) ^ 4 : ℝ) :=
  ⟨dwarfSurfaceSpeed_bounds.1, dwarfSurfaceSpeed_bounds.2,
    dwarfTwoKpcSpeed_bounds.1, dwarfTwoKpcSpeed_bounds.2,
    dwarfFourKpcSpeed_bounds.1, dwarfFourKpcSpeed_bounds.2⟩


/-! ## Dual-only control of \(J,M\) -/

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

/-- Regression: saturated attraction is the unique dual-only rigid point. -/
example {p : Operations.TorsionParams} (hp : Admissible.IsAdmissibleContinuous p) :
    (∀ q : Operations.TorsionParams,
        Admissible.IsAdmissibleContinuous q → q.alpha = p.alpha → q = p) ↔
      Logic.ofParams p hp = .F :=
  dualOnly_rigid_iff_F hp

/-- Regression: the attractive ceiling has no dual-only repulsive continuation. -/
example {p : Operations.TorsionParams} (hp : Admissible.IsAdmissibleContinuous p)
    (hF : Logic.ofParams p hp = .F) :
    ¬ ∃ q : Operations.TorsionParams, ∃ hq : Admissible.IsAdmissibleContinuous q,
      q.alpha = p.alpha ∧ Logic.ofParams q hq = .B :=
  no_dualOnly_repulsion_of_F hp hF

/-- Regression: uniform \(\pi/6\) reaches repulsion, balance, and unsaturated attraction. -/
example :
    (∃ q : Operations.TorsionParams, ∃ hq : Admissible.IsAdmissibleContinuous q,
        q.alpha = (uniformTorsion (Real.pi / 6) 0).alpha ∧ Logic.ofParams q hq = .B) ∧
      (∃ q : Operations.TorsionParams, ∃ hq : Admissible.IsAdmissibleContinuous q,
        q.alpha = (uniformTorsion (Real.pi / 6) 0).alpha ∧ Logic.ofParams q hq = .T) ∧
      Logic.ofParams (uniformTorsion (Real.pi / 6) 0) uniform_pi_div_six_admissible = .U :=
  ⟨uniform_pi_div_six_three_labels.1, uniform_pi_div_six_three_labels.2.1,
    uniform_pi_div_six_three_labels.2.2.1⟩

/-- Regression: the mass ceiling has one of four normalised heights. -/
example {p : Operations.TorsionParams}
    (h : Admissible.IsAdmissibleContinuous p)
    (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    JNormalized p = 1 ∨ JNormalized p = 1 / 3 ∨
      JNormalized p = -(1 / 3) ∨ JNormalized p = -1 :=
  JNormalized_mass_ceiling_four h hM

/-- Regression: saturated attraction carries the whole mass ceiling. -/
example {p : Operations.TorsionParams}
    (h : Admissible.IsAdmissibleContinuous p)
    (hF : Logic.ofParams p h = .F) :
    mass p = 3 * Real.pi ^ 2 / 8 ∧ massNormalized p = 1 ∧ JNormalized p = 1 :=
  saturated_attraction_has_mass_ceiling h hF

/-- Regression: balance stays at or below five sixths of the mass ceiling. -/
example {p : Operations.TorsionParams}
    (h : Admissible.IsAdmissibleContinuous p)
    (hT : Logic.ofParams p h = .T) :
    massNormalized p ≤ 5 / 6 :=
  massNormalized_le_five_sixths_of_balance h hT

/-- Regression: the heaviest shield attains five sixths and is balanced. -/
example :
    massNormalized maximalShield = 5 / 6 ∧
      Logic.ofParams maximalShield isAdmissibleContinuous_maximalShield = .T :=
  ⟨massNormalized_maximalShield, ofParams_maximalShield⟩

/-- Regression: uniform \(\pi/3\) stays in unsaturated attraction. -/
example {q : Operations.TorsionParams}
    (hα : ∀ a, q.alpha a = Real.pi / 3)
    (hq : Admissible.IsAdmissibleContinuous q) :
    Logic.ofParams q hq = .U :=
  uniform_pi_div_three_dualOnly_U hα hq

/-- Regression: dual-only cannot evacuate a positive usual seed. -/
example {p q : Operations.TorsionParams}
    (hα : q.alpha = p.alpha)
    (hU : ∑ a : Fin 3, p.alpha a ^ 2 ≠ 0)
    (hM : mass q = 0) : False :=
  dual_only_not_vacuum_of_usual_pos hα hU hM


/-! ## Scales that are inputs -/

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


/-! ## Dual-only control of \(J,M\) -/

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


/-! ## One Faraday six-space -/

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

/-- Regression: a charged generator exchanges the projectors, and the cross
sandwich does not vanish. -/
example (a i : Fin 3) :
    chargedGen a i * chiralityRAxis a = chiralityLAxis a * chargedGen a i ∧
      chiralityLAxis a * chargedGen a i * chiralityRAxis a ≠ 0 :=
  ⟨chargedGen_mul_chiralityRAxis a i, crossSandwich_charged_ne_zero a i⟩

/-- Regression: a Cartan generator preserves the right projector. -/
example (a i : Fin 3) :
    cartanGen a i * chiralityRAxis a = chiralityRAxis a * cartanGen a i ∧
      chiralityLAxis a * cartanGen a i * chiralityRAxis a = 0 :=
  ⟨cartanGen_mul_chiralityRAxis a i, crossSandwich_cartan a i⟩

/-- Regression: the mismatch adds across the chiral split. -/
example (a : Fin 3) (p : FaradayParams) :
    J (toTorsion p) =
      J (toTorsion (evenParams a p)) + J (toTorsion (oddParams a p)) :=
  J_even_add_odd a p


/-! ## Scales that are inputs -/

/-- Regression: corresponding nodes stand in the ratio of the lengths. -/
example {ℓ₁ ℓ₂ x : ℝ} (hℓ : ℓ₂ ≠ 0) (hx : x ≠ 0) :
    layerRadius ℓ₁ x / layerRadius ℓ₂ x = ℓ₁ / ℓ₂ :=
  layerRadius_ratio hℓ hx

/-- Regression: the first charge-channel node lies between 203 and 414 nuclear reversals. -/
example {r₁ : ℝ} (hr0 : 1 / 2 < r₁) (hr1 : r₁ < 1) :
    (203 : ℝ) < layerRadius ((ellRepFm : ℚ) : ℝ) resonanceRoot1 / r₁ ∧
      layerRadius ((ellRepFm : ℚ) : ℝ) resonanceRoot1 / r₁ < 414 :=
  first_node_ratio hr0 hr1


/-! ## One Faraday six-space -/

/-- Regression: the parallel electric mix preserves the axis only at a trivial angle. -/
example (a : Fin 3) (cB cE : ℝ) :
    Commute (spatialGen a) (cB • cyclic a + cE • hyperbolic a) ↔ cE = 0 :=
  commute_neutral_axis_iff a cB cE

/-- Regression: on \(J=0\) the magnetic square equals the unsigned mass. -/
example {p : FaradayParams} (hJ : J (toTorsion p) = 0) :
    mass (toTorsion p) = magneticSq p ∧
      (1 / 2) * magneticSq p = mass (toTorsion p) / 2 :=
  ⟨mass_eq_magneticSq_of_balanced hJ, (balanced_shares hJ).1⟩

/-- Regression: a silent charge does not move the dual angles. -/
example (p : Operations.TorsionParams) (A : Fin 3 → ℝ) :
    coupleA p 0 A = p :=
  coupleA_zero_label p A

/-- Regression: a silent label drops no ponderomotive mean. -/
example (p : Operations.TorsionParams) (A : ℝ → Fin 3 → ℝ) :
    quadMean (fun ψ => J (coupleA p 0 (A ψ))) = J p :=
  quadMean_J_coupleA_zero_label p A

/-- Regression: the heaviest shield admits no further nonnegative magnetic increment. -/
example {B : Fin 3 → ℝ} (hB : ∀ a, 0 ≤ B a) (hne : ∑ a : Fin 3, B a ^ 2 ≠ 0) :
    ¬ Admissible.IsAdmissibleContinuous (superpose maximalShield (magneticFaraday B)) :=
  maximalShield_magnetic_rigid hB hne

/-- Regression: one-axis dual phase \(2\pi\) sends the dual rotor to \(-1\). -/
example (a : Fin 3) (p : Operations.TorsionParams)
    (h : ∀ b, p.beta b = if b = a then 2 * Real.pi else 0) :
    RelativeRotor.rotorDual p = -1 :=
  rotorDual_single_axis_two_pi a p h

/-- Regression: the dual Faraday summand does not kick a body at rest. -/
example (p : FaradayParams) :
    sandwichIncrement (faradayDual p) (ι 0) = 0 :=
  magnet_rest_kick p

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

/-- Regression: a full circular cycle drops mean \(J\) by at most \(\pi^2/32\),
and the bound is attained. -/
example {σ : ℝ} (hσ : σ ^ 2 = 1) :
    ((1 : ℝ) ^ 2 / 2) * ((Real.pi / 4) / 1) ^ 2 = Real.pi ^ 2 / 32 ∧
      (∀ ψ : ℝ, Admissible.IsAdmissibleContinuous
        (coupleA transversePureDual 1 (circularPotential σ (Real.pi / 4) 1 ψ))) :=
  ⟨ponderomotive_transverse_extremal, cycle_admissible_transverse_extremal hσ⟩

/-- Regression: at rapidity \(\pi/6\) the isotropic cycle holds a constant
potential \(m\pi^2/72\). -/
example {m ψ σ : ℝ} (hσ : σ ^ 2 = 1) :
    stiffnessPotential m
        (coupleA (isotropicSeed (Real.pi / 6)) 1
          (circularPotential σ (Real.pi / 6) 1 ψ)) =
      m * (Real.pi ^ 2 / 72) :=
  stiffness_isotropic_sixth hσ

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


/-! ## Dual-only control of \(J,M\) -/

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

/-- Regression: the heaviest shield saturates the neutral lag budget, and a
pure usual seed relaxes under coaxial alignment while a silent axis doubles it. -/
example (α : ℝ) (hα : α ≠ 0) :
    lagSq maximalShield = Real.pi ^ 2 / 2 ∧
      lagSq (equalScaleOf (axisUsual α)) = 0 ∧
        lagSq (crossAxisDual α) = 2 * lagSq (axisUsual α) ∧
          lagSq (axisUsual α) < lagSq (crossAxisDual α) :=
  ⟨lagSq_maximalShield, lagSq_equalScale_axisUsual α, lagSq_cross_eq_two_axisUsual α,
    lagSq_cross_gt_axisUsual hα⟩

/-- Regression: a neutral wall of given mass attains the holding price, and a
matched hold does no work when the two rotors share a velocity. -/
example {M : ℝ} (hlo : 3 * Real.pi ^ 2 / 16 ≤ M) (hhi : M ≤ 5 * Real.pi ^ 2 / 16) :=
  balancedWallOfMass_spec hlo hhi

example {m c : ℝ} {φ θ : Fin 3 → ℝ} :
    holdPower (fun a => m * (φ a - θ a)) (fun a => m * (φ a - θ a))
      (fun _ => c) (fun _ => c) = 0 :=
  holdPower_matched_of_equal_velocity (fun _ => rfl)

/-- Regression: one scale \(k^2\) prices both the envelope and the hold,
and the three centers share that price. -/
example (p : Operations.TorsionParams)
    (h : Admissible.IsAdmissibleContinuous p) :
    mass p / coneScale ≤ 5 / 4 + lobeExcess (J p / coneScale) ∧
      (mass p = controlCeiling (J p) →
        lagSq p / coneScale = 2 + 4 * lobeExcess (J p / coneScale)) :=
  ⟨scaledMass_le_lobe h, fun hE => lagSq_div_coneScale_of_onEnvelope h hE⟩

example :
    J maximalShield / coneScale = 0 ∧
      J (twoUsualWitness (Real.pi / 4)) / coneScale = 1 ∧
        J (twoDualWitness (Real.pi / 4)) / coneScale = -1 ∧
          mass maximalShield = 5 * coneScale / 4 ∧
            lagSq maximalShield = 2 * coneScale ∧
              stiffnessPotential 1 maximalShield = coneScale ∧
                stiffnessPotential 1 (twoUsualWitness (Real.pi / 4)) = coneScale := by
  have hs := center_shield_mass_lag
  have hu := center_usual_mass_lag
  have hd := center_dual_mass_lag
  refine ⟨hs.1, hu.1, hd.1, ?_, ?_, hs.2.2.2, hu.2.2.2⟩
  · rw [mass_maximalShield, shield_mass_eq_scaled]
  · rw [lagSq_maximalShield, neutral_lag_cap_eq_scaled]


/-! ## Scales that are inputs -/

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


/-! ## Layers and particle dynamics -/

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

/-- Regression: on the outer well an ion's outflow is positive, so the ions
alone hold no electron there. -/
example {x : ℝ} (hx : x ∈ Set.Ioo 0 resonanceRoot1) : 0 < ionOutflow x :=
  ionOutflow_pos_outer hx


/-! ## Scales that are inputs -/

/-- Regression: a rising nonnegative rapidity meets the nuclear threshold
before the static node. -/
example {c : ℝ} {φ : ℝ → ℝ}
    (hc : Real.pi / 4 < c) (hc1 : c < resonanceRoot1)
    (h0 : 0 ≤ φ c) (hlt : φ c < phiStar c)
    (hcont : ContinuousOn φ (Set.Icc c resonanceRoot1))
    (hmono : StrictMonoOn φ (Set.Icc c resonanceRoot1)) :
    ∃ t, t ∈ Set.Ioo c resonanceRoot1 ∧ φ t = phiStar t :=
  inward_rapidity_meets_threshold hc hc1 h0 hlt hcont hmono

/-- Regression: above the nuclear threshold the charged net force is more
repulsive than the Coulomb term alone. -/
example {x δ ρ γE : ℝ}
    (hx : Real.pi / 4 < x) (hx2 : x < Real.pi / 2)
    (hδ : phiStar x / 2 < δ) (hρ : 0 < ρ) (hγE : 0 < γE) :
    ρ / γE < chargedShift (gammaRapidity x δ) ρ γE :=
  above_threshold_reinforces_coulomb hx hx2 hδ hρ hγE

/-- Regression: a kinetic energy at most `10⁻¹⁰` of the rest energy widens
the inversion radius by less than five parts in a million. -/
example {φ y x : ℝ}
    (hφ : 0 < φ) (hy : Real.cosh φ = 1 + y)
    (hyb : y ≤ 1 / (10 : ℝ) ^ 10)
    (hx : x ∈ Set.Ioo (Real.pi / 4) resonanceRoot1)
    (hφx : phiStar x = φ) :
    (resonanceRoot1 - x) / x < 5 / (10 : ℝ) ^ 6 :=
  fractional_widening_of_small_energy hφ hy hyb hx hφx

/-- Regression: an unlike pair does not balance where both factors are positive. -/
example {κ coul γG γE r : ℝ}
    (hκ : 0 < κ) (hc : coul < 0) (hr : r ≠ 0) (hG : 0 < γG) (hE : 0 < γE) :
    pairChannelForce κ coul γG γE r < 0 :=
  (unlike_same_sign_no_zero hκ hc hr hG hE).2.2

/-- Regression: at a hydrogenic separation the mass term is between
\(4.40\times 10^{-40}\) and \(4.42\times 10^{-40}\) of the charge term. -/
example {ℓE ℓG a : ℝ}
    (hE0 : 0 < ℓE) (hE : ℓE < 387) (hG0 : 0 < ℓG) (hG : ℓG < 71 / 50)
    (ha : 52917 < a) :
    (440 : ℝ) / 10 ^ 42 <
        (electronProtonGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) / gammaSEqual (ℓG / (2 * a)) ∧
      (electronProtonGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) / gammaSEqual (ℓG / (2 * a)) <
        442 / 10 ^ 42 :=
  bohr_mass_fraction hE0 hE hG0 hG ha

/-- Regression: two electrons above the Bohr radius repel electrically.
The gravitational term is between `2.398×10⁻⁴³` and `2.404×10⁻⁴³` of that
repulsion. -/
example {ℓE ℓG a : ℝ}
    (hE0 : 0 < ℓE) (hE : ℓE < 387) (hG0 : 0 < ℓG) (hG : ℓG < 19 / 10)
    (ha : 52917 < a) :
    (2398 : ℝ) / 10 ^ 46 <
        (electronElectronGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) / gammaSEqual (ℓG / (2 * a)) ∧
      (electronElectronGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) / gammaSEqual (ℓG / (2 * a)) <
        2404 / 10 ^ 46 :=
  shell_electron_grav_fraction hE0 hE hG0 hG ha

/-- Regression: at that separation the electric term increases the separation,
the gravitational term decreases it, and the sum increases it. -/
example {ℓE ℓG a coul r : ℝ}
    (hE0 : 0 < ℓE) (hE : ℓE < 387) (hG0 : 0 < ℓG) (hG : ℓG < 19 / 10)
    (ha : 52917 < a) (hc : 0 < coul) (hr : r ≠ 0) :
    0 < coul / (gammaSEqual (ℓE / (2 * a)) * r ^ 2) ∧
      -(electronElectronGravToCoulomb : ℝ) * coul /
          (gammaSEqual (ℓG / (2 * a)) * r ^ 2) < 0 ∧
        0 < pairChannelForce
          ((electronElectronGravToCoulomb : ℝ) * coul) coul
          (gammaSEqual (ℓG / (2 * a))) (gammaSEqual (ℓE / (2 * a))) r :=
  shell_electron_net_repels hE0 hE hG0 hG ha hc hr

/-- Regression: one place holds opposite rays, and the identity with its antipode holds one ray. -/
example :
    SpinVersusExclusion.samePlace
        (SpinVersusExclusion.atPlace 1 SpinVersusExclusion.axisUp)
        (SpinVersusExclusion.spinReverse
          (SpinVersusExclusion.atPlace 1 SpinVersusExclusion.axisUp)) ∧
      ¬ SpinVersusExclusion.sameRay
        (SpinVersusExclusion.atPlace 1 SpinVersusExclusion.axisUp)
        (SpinVersusExclusion.spinReverse
          (SpinVersusExclusion.atPlace 1 SpinVersusExclusion.axisUp)) ∧
      SpinVersusExclusion.sameRay
        (SpinVersusExclusion.atPlace 1 SpinVersusExclusion.axisUp)
        (SpinVersusExclusion.atPlace RelationalPosition.negOne SpinVersusExclusion.axisUp) ∧
      ¬ SpinVersusExclusion.samePlace
        (SpinVersusExclusion.atPlace 1 SpinVersusExclusion.axisUp)
        (SpinVersusExclusion.atPlace RelationalPosition.negOne SpinVersusExclusion.axisUp) := by
  have hsing := SpinVersusExclusion.singlet_at_one_place
  have hrep := SpinVersusExclusion.repeated_ray_at_antipodes (0 : ℂ)
  exact ⟨hsing.1, hsing.2.1, hrep.1, hrep.2.1⟩

/-- Regression: above the Bohr radius a repeated ray is still not the singlet. -/
example {ℓE ℓG a coul r : ℝ}
    (hE0 : 0 < ℓE) (hE : ℓE < 387) (hG0 : 0 < ℓG) (hG : ℓG < 19 / 10)
    (ha : 52917 < a) (hc : 0 < coul) (hr : r ≠ 0) (c : ℂ) :
    DstDiophantine.Logic.pairTensor SpinVersusExclusion.axisUp SpinVersusExclusion.axisUp ≠
        c • DstDiophantine.Logic.singlet ∧
      -(electronElectronGravToCoulomb : ℝ) * coul /
          (gammaSEqual (ℓG / (2 * a)) * r ^ 2) < 0 ∧
        0 < pairChannelForce
          ((electronElectronGravToCoulomb : ℝ) * coul) coul
          (gammaSEqual (ℓG / (2 * a))) (gammaSEqual (ℓE / (2 * a))) r :=
  SpinVersusExclusion.repeated_ray_where_masses_attract hE0 hE hG0 hG ha hc hr c

/-- Regression: inside the first node the outward excess over `ke²/r²` is a
fractional depth below `1.64×10⁻⁴³`, and that depth is attained. -/
example :
    ∃ ε : ℝ, 0 < ε ∧ ε < (164 : ℝ) / 100 / 10 ^ 43 ∧
      ε < 1 - resonanceRoot1 ∧
        (electronElectronGravToCoulomb : ℝ) > -gammaSEqual (phaseAtDepth ε) :=
  exists_grav_excess_depth

/-- Regression: a node below `1` fm and a depth below `1.64×10⁻⁴³` is smaller
than a radius above `52917` by more than `3×10⁴⁷`. -/
example {r₁ a ε : ℝ}
    (hr0 : 0 < r₁) (hr1 : r₁ < 1) (ha : 52917 < a)
    (hε : 0 < ε) (hε1 : ε < (164 : ℝ) / 100 / 10 ^ 43) :
    a / (ε * r₁) > 3 * 10 ^ 47 := by
  have h := grav_depth_below_bohr hr0 hr1 ha hε.le hε1
  exact h.resolve_right (ne_of_gt hε)


/-! ## One Faraday six-space -/

/-- Regression: inversion exchanges the projectors and leaves \(J\) even. -/
example (a : Fin 3) (p : FaradayParams) :
    spatialParity (chiralityRAxis a) = chiralityLAxis a ∧
      spatialParity (chiralityLAxis a) = chiralityRAxis a ∧
        J (toTorsion (parityFaradayParams p)) = J (toTorsion p) ∧
          faradayDot (parityFaradayParams p) = -faradayDot p ∧
            faradayDot (swapFaradayParams p) = faradayDot p ∧
              poyntingZ (parityFaradayParams (timeReverseFaradayParams p)) =
                poyntingZ p := by
  refine ⟨spatialParity_chiralityRAxis a, spatialParity_chiralityLAxis a,
    J_parityFaraday p, faradayDot_parity p, faradayDot_swap p, ?_⟩
  rw [parity_timeReverse_eq_neg, poyntingZ_neg]

/-- Regression: a pure vacuum excess carries no \(E\cdot B\). -/
example (δ : ℝ) (dir : Fin 3 → ℝ) :
    faradayDot ({ E := fun a => δ * dir a, B := fun _ => 0 } : FaradayParams) = 0 ∧
      faradayDot ({ E := fun _ => 0, B := fun a => δ * dir a } : FaradayParams) = 0 :=
  ⟨faradayDot_boostAlong δ dir, faradayDot_rotationAlong δ dir⟩


/-! ## Layers and particle dynamics -/

/-- Regression: one revolution restores the orbital point and leaves the rotor at `-1`. -/
example (a b : ℝ) :
    Motor.rotorTorsion (Amplification.pureRotation1 (2 * Real.pi)) = -1 ∧
      Sandwich.sandwich
        (Motor.rotorTorsion (Amplification.pureRotation1 (2 * Real.pi)))
        (a • ι 1 + b • ι 3) = a • ι 1 + b • ι 3 :=
  ⟨dualRotor_one_revolution, orbitPoint_one_revolution a b⟩

/-- Regression: the plane-wave factor on that revolution equals `1` exactly at `pr = nℏ`.
This equivalence does not place a radius. -/
example {p r ℏ : ℝ} (hℏ : ℏ ≠ 0) :
    Complex.exp (Complex.I * ((p * r * (2 * Real.pi) / ℏ : ℝ) : ℂ)) = 1 ↔
      ∃ n : ℤ, p * r = (n : ℝ) * ℏ :=
  planeWave_revolution_iff hℏ


/-! ## Charge two -/

/-- Regression: on the diameter the net force is inward throughout the outer well. -/
example {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) resonanceRoot1) :
    0 < -diameterOutward 2 x :=
  diameter_inward hx

/-- Regression: the standing-wave shortening at the Bohr radius lies below the
electron-to-proton mass ratio, and the first node lies between `a₀/261` and `a₀/255`. -/
example :
    (13312 / 10 ^ 9 : ℝ) < 1 - gammaSEqual bohrPhase ∧
      1 - gammaSEqual bohrPhase < 13314 / 10 ^ 9 ∧
        1 - gammaSEqual bohrPhase <
          (SI.electronMassApprox : ℝ) / (SI.protonMassApprox : ℝ) ∧
      (1 / 261 : ℝ) < (SI.fineStructureApprox : ℝ) / (2 * resonanceRoot1) ∧
        (SI.fineStructureApprox : ℝ) / (2 * resonanceRoot1) < 1 / 255 := by
  have hfrac := hydrogen_fraction_window
  exact ⟨hfrac.1, hfrac.2.1, hydrogen_shortening_lt_mass_ratio,
    firstNode_over_bohr_window.1, firstNode_over_bohr_window.2⟩

/-! ## Scales that are inputs -/

/-- Regression: the dual-rotor determinant has vanishing argument. -/
example (β : DualRapidity) :
    (dualRotorMat β).det = 1 ∧ ((dualRotorMat β).det).arg = 0 :=
  dualRotor_det_arg β

end Gravity

end DstDiophantine
