import DstDiophantine.Gravity.Identification
import DstDiophantine.Gravity.JTDictionary
import DstDiophantine.Gravity.GaugeDictionary
import DstDiophantine.Gravity.ClassicalSchwarzschild
import DstDiophantine.Gravity.Tetrad
import DstDiophantine.Gravity.NewtonFromLight
import DstDiophantine.Gravity.EventBoundary
import DstDiophantine.Gravity.CoulombFromDual
import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Gravity.CompactS3
import DstDiophantine.Gravity.TorsionalLayer
import DstDiophantine.Gravity.NuclearLayer
import DstDiophantine.Gravity.DualRotorDynamics
import DstDiophantine.Gravity.ElectronOrbit
import DstDiophantine.Gravity.Faraday
import DstDiophantine.Gravity.Electroweak

/-!
# Gravity / PGA–TEGR chart layer

Re-exports the chart-level TEGR scaffolding (coframe, sandwich scales,
Schwarzschild tetrad, Weitzenböck torsion, motor-induced frame vectors,
and the `J` / `J_field` / `T` dictionary with naive-identification rejections,
the closed radial-boost form in `JTDictionary` together with its strict
monotonicity, closed-form inversion, and finite two-sided window on the
admissible cone, the gauge-level generalisation in `GaugeDictionary`, and the
classical specialisation `A=1-rₛ/r` in `ClassicalSchwarzschild`),
plus the exploratory SI / \(c\to G\) hypothesis layer (`SI`, `NewtonFromLight`),
the labelled quasi-horizon cutoff (`EventBoundary`), the electromagnetic
exploratory layer (`CoulombFromDual`, `ElectronShell`), the galactic
S³ cotangent exploratory layer (`CompactS3`; no `dst_derives_a0` / `dst_derives_G`),
the closed-form layer spectrum of `TorsionalLayer` (exact derivative, plateau
extrema `(-1)^n cosh(nπ)`, one node per `π`-interval, sharpened branch
`(nπ+π/4, nπ+π/2)`, exponential inward screening), and the nuclear-layer
exploratory diagnostics (`NuclearLayer`; no `dst_derives_alpha_s` /
`dst_derives_lambdaN` / `dst_derives_Amax`),
the closed form of `gammaEff`, the Euler–Lagrange identities of
`DualRotorDynamics`, the Coulombic circular-orbit identities of
`ElectronOrbit` (first-root window \(\pi/4<x_1<1\), repulsive layers yield
no real circular \(v^2\), equal-scale \(r_2/r_1\) cannot equal the Bohr
ratio \(4\); no `dst_derives_lambda`), the Faraday 6-space audit of
`Faraday` (Section 10/12 split, dual map \((E,B)\mapsto(B,-E)\), Faraday
quadratic \(J=\tfrac12(E^2-B^2)\), null circular snapshots with \(J=0\) and
\(M>0\), Hodge period 4 versus the period-2 parameter swap and laboratory
\(T\), sandwich commutator versus the paper wedge on rest and on a
\(y\)-velocity; Maxwell is not derived), and the electroweak skeleton of
`Electroweak` (dual map is not a Weyl projector; Faraday \(3+3\) split
relative to \(e_1\); same-projector sandwich kills the anticommuting
summand; mix \(J\mapsto J\cos 2\omega+(E\cdot B)\sin 2\omega\) with duality
at \(\omega=\pi/2\); pure \(E\) has \(J\ge 0\), pure \(B\) has \(J\le 0\);
no Weinberg angle, no \(W/Z\) masses).
-/

namespace DstDiophantine

namespace Gravity

open Invariant PGA Generators Logic

/-- Regression: closed-form dictionary \(T=(4/r^2)(\cosh\sqrt{2J}-1)\). -/
example {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      teleparallelTofJ (J (radialBoostParams rs r)) r :=
  schwarzschild_T_eq_teleparallelTofJ h

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

/-- Regression: the written particle action makes the mismatch free. -/
example {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) :
    φddot - θddot = 0 :=
  paperActualEL_free_mismatch h

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

/-- Regression: first Coulombic node lies in \((\pi/4,1)\). -/
example : Real.pi / 4 < resonanceRoot1 ∧ resonanceRoot1 < 1 :=
  firstNode_window

/-- Regression: repulsive Coulombic layers yield no real circular speed. -/
example {k e m γs r : ℝ} (hk : 0 < k) (he : e ≠ 0) (hm : 0 < m)
    (hγ : γs < 0) (hr : 0 < r) :
    circularSpeedSq k e m γs r < 0 :=
  circularSpeedSq_neg_of_repulsive hk he hm hγ hr

/-- Regression: equal-scale radius ratio cannot equal the Bohr ratio \(4\). -/
example {x₂ : ℝ} (hx₂ : x₂ ∈ Set.Ioo (Real.pi + Real.pi / 4) (Real.pi + Real.pi / 2)) :
    resonanceRoot1 / x₂ ≠ bohrShellRadius 2 / bohrShellRadius 1 :=
  equalScale_ratio_ne_bohr hx₂

/-- Regression: \(\ell\mapsto\ell/Z\) contracts every equal-scale radius. -/
example {ℓ Z x : ℝ} (hZ : Z ≠ 0) :
    layerRadius (ℓ / Z) x = layerRadius ℓ x / Z :=
  Z_contracts_layerRadius hZ

/-- Regression: Faraday is the Section 12 usual-plus-dual split. -/
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

/-- Regression: the paper wedge is not the first-order sandwich increment. -/
example :
    sandwichIncrement (cyclic 0) (ι 0) = 0 ∧
      paperWedgeIncrement (cyclic 0) (ι 0) ≠ 0 :=
  paper_wedge_ne_lorentz_increment

/-- Regression: a \(y\)-velocity against \(B_x\) yields a \(z\)-kick; the wedge
vanishes. -/
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

end Gravity

end DstDiophantine
