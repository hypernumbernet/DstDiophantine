import DstDiophantine.Gravity.Faraday
import DstDiophantine.Logic.Quantum.MinimalIdeal
import DstDiophantine.Logic.Quantum.CompositeProjector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# Faraday 6-space versus axis chirality (electroweak skeleton)

## Paper boundary (do **not** claim)

Maxwell's equations, a Weinberg angle, \(W/Z\) masses, and a Lorentz-invariant
Weyl V--A gauge theory are **not** derived. The dual map \(X\mapsto Xi\) is
not a chirality projector. Axis-dependent sandwich selection is not identified
with the Standard Model, nor with photon helicity.

## What is proved

* The Cl(3,1) pseudoscalar squares to \(-1\), so \((1\pm i)/2\) is not
  idempotent. Complementary projectors \(P_{L,R}=(1\pm e_1)/2\) from
  \(e_1^2=+1\) are idempotent, sum to \(1\), and multiply to \(0\). Duality
  sends \(e_1\) to a trivector, not to a real multiple of \(e_1\).
* Relative to the chirality axis \(e_1\), the Faraday generators split
  \(3+3\): \(\Gamma_0,\,i\Gamma_1,\,i\Gamma_2\) commute with \(e_1\);
  \(i\Gamma_0,\,\Gamma_1,\,\Gamma_2\) anticommute. Same-projector sandwich
  \(P_R X P_R\) kills the anticommuting summand and retains the commuting one.
  The coefficient split \(p=\mathrm{Cartan}+\mathrm{Charged}\) realises that
  decomposition on \(E,B\); the \(z\)-Poynting cross of Cartan against Charged
  vanishes. The left sandwich \(P_L X P_L\) likewise kills the anticommuting
  summand, so \(P_{L,R}\) do not select a helicity sign.
* A one-parameter mix rotating \((E,B)\) in every axis acts on the
  Faraday quadratic by \(J\mapsto J\cos 2\omega+(E\cdot B)\sin 2\omega\).
  Hodge duality is the special angle \(\omega=\pi/2\). Same-axis \(E_a,B_a\)
  commute, so the mix is simultaneously diagonalisable on each axis.
* Pure electric configurations have \(J\ge 0\); pure magnetic ones have
  \(J\le 0\). That is the Killing-form signature of usual versus dual
  sectors, written in Faraday coefficients.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations RelativeRotor Invariant
open Logic
open scoped Real

/-! ### Dual map is not a Weyl projector -/

theorem chiralityL_mul_chiralityR :
    chiralityL * chiralityR = 0 := by
  unfold chiralityL chiralityR
  have hdiff :
      ((1 : PGA) - chiralityGen) * ((1 : PGA) + chiralityGen) =
        (1 : PGA) - chiralityGen * chiralityGen := by
    noncomm_ring
  rw [mul_half_mul_half, hdiff, chiralityGen_sq, sub_self, zero_mul]

theorem chiralityR_mul_chiralityL :
    chiralityR * chiralityL = 0 := by
  unfold chiralityL chiralityR
  have hdiff :
      ((1 : PGA) + chiralityGen) * ((1 : PGA) - chiralityGen) =
        (1 : PGA) - chiralityGen * chiralityGen := by
    noncomm_ring
  rw [mul_half_mul_half, hdiff, chiralityGen_sq, sub_self, zero_mul]

/-- Duality sends the chirality axis to the trivector \(-e_0 e_2 e_3\). -/
theorem dual_chiralityGen :
    dual chiralityGen = -((ι 0 * ι 2) * ι 3) := by
  unfold dual chiralityGen pseudoscalar
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc ι 1 * (ι 0 * ι 1 * ι 2 * ι 3)
      = (ι 1 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
    _ = (-(ι 0 * ι 1)) * ι 1 * ι 2 * ι 3 := by rw [h10]
    _ = -(ι 0 * (ι 1 * ι 1) * ι 2 * ι 3) := by simp [mul_assoc]
    _ = -(ι 0 * ι 2 * ι 3) := by simp [e1_sq]
    _ = -((ι 0 * ι 2) * ι 3) := by simp [mul_assoc]

/-- Duality does not preserve the chirality axis as a real line. -/
theorem dual_chiralityGen_not_real_span :
    ¬ ∃ c : ℝ, dual chiralityGen = c • chiralityGen := by
  rintro ⟨c, hc⟩
  have hps : pseudoscalar = algebraMap ℝ PGA c := by
    have hmul : chiralityGen * dual chiralityGen = chiralityGen * (c • chiralityGen) :=
      congrArg (fun z : PGA => chiralityGen * z) hc
    have hL : chiralityGen * dual chiralityGen = pseudoscalar := by
      unfold dual
      calc chiralityGen * (chiralityGen * pseudoscalar)
          = (chiralityGen * chiralityGen) * pseudoscalar := by rw [← mul_assoc]
        _ = (1 : PGA) * pseudoscalar := by rw [chiralityGen_sq]
        _ = pseudoscalar := by simp
    have hR : chiralityGen * (c • chiralityGen) = c • (1 : PGA) := by
      rw [mul_smul_comm, chiralityGen_sq]
    have : pseudoscalar = c • (1 : PGA) := by
      rw [← hL, hmul, hR]
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have hsq : algebraMap ℝ PGA (c ^ 2) = algebraMap ℝ PGA (-1) := by
    have h : algebraMap ℝ PGA (c * c) = (-1 : PGA) := by
      have : algebraMap ℝ PGA c * algebraMap ℝ PGA c = (-1 : PGA) := by
        rw [← hps, pseudoscalar_sq]
      rwa [← map_mul] at this
    rw [pow_two]
    simpa [map_neg, map_one] using h
  have hc2 : c ^ 2 = -1 :=
    FaithfulSMul.algebraMap_injective (R := ℝ) (A := PGA) hsq
  nlinarith [sq_nonneg c]

/-! ### Axis \(e_1\): commuting versus anticommuting Faraday generators -/

theorem commute_chiralityGen_hyperbolic2 :
    Commute chiralityGen (hyperbolic 2) := by
  change chiralityGen * hyperbolic 2 = hyperbolic 2 * chiralityGen
  unfold chiralityGen hyperbolic
  have h10 : PGA.ι 1 * PGA.ι 0 = -(PGA.ι 0 * PGA.ι 1) :=
    e_mul_anticomm (by decide)
  have h31 : PGA.ι 3 * PGA.ι 1 = -(PGA.ι 1 * PGA.ι 3) :=
    e_mul_anticomm (by decide)
  calc PGA.ι 1 * (PGA.ι 0 * PGA.ι 3)
      = (PGA.ι 1 * PGA.ι 0) * PGA.ι 3 := by simp [mul_assoc]
    _ = (-(PGA.ι 0 * PGA.ι 1)) * PGA.ι 3 := by rw [h10]
    _ = -(PGA.ι 0 * PGA.ι 1 * PGA.ι 3) := by simp [mul_assoc]
    _ = PGA.ι 0 * (-(PGA.ι 1 * PGA.ι 3)) := by simp [mul_neg, mul_assoc]
    _ = PGA.ι 0 * (PGA.ι 3 * PGA.ι 1) := by rw [← h31]
    _ = (PGA.ι 0 * PGA.ι 3) * PGA.ι 1 := by simp [mul_assoc]

theorem commute_chiralityGen_cyclic0 :
    Commute chiralityGen (cyclic 0) := by
  change chiralityGen * cyclic 0 = cyclic 0 * chiralityGen
  unfold chiralityGen cyclic
  have h13 : PGA.ι 1 * PGA.ι 3 = -(PGA.ι 3 * PGA.ι 1) :=
    e_mul_anticomm (by decide)
  have h21 : PGA.ι 2 * PGA.ι 1 = -(PGA.ι 1 * PGA.ι 2) :=
    e_mul_anticomm (by decide)
  calc PGA.ι 1 * (PGA.ι 3 * PGA.ι 2)
      = (PGA.ι 1 * PGA.ι 3) * PGA.ι 2 := by simp [mul_assoc]
    _ = (-(PGA.ι 3 * PGA.ι 1)) * PGA.ι 2 := by rw [h13]
    _ = -(PGA.ι 3 * PGA.ι 1 * PGA.ι 2) := by simp [mul_assoc]
    _ = PGA.ι 3 * (-(PGA.ι 1 * PGA.ι 2)) := by simp [mul_neg, mul_assoc]
    _ = PGA.ι 3 * (PGA.ι 2 * PGA.ι 1) := by rw [← h21]
    _ = (PGA.ι 3 * PGA.ι 2) * PGA.ι 1 := by simp [mul_assoc]

theorem chiralityGen_anticomm_cyclic1 :
    chiralityGen * cyclic 1 = -(cyclic 1 * chiralityGen) := by
  unfold chiralityGen cyclic
  have h31 : PGA.ι 3 * PGA.ι 1 = -(PGA.ι 1 * PGA.ι 3) :=
    e_mul_anticomm (by decide)
  have hL : PGA.ι 1 * (PGA.ι 1 * PGA.ι 3) = PGA.ι 3 := by
    rw [← mul_assoc, e1_sq, one_mul]
  have hR : (PGA.ι 1 * PGA.ι 3) * PGA.ι 1 = -(PGA.ι 3) := by
    calc PGA.ι 1 * PGA.ι 3 * PGA.ι 1
        = PGA.ι 1 * (PGA.ι 3 * PGA.ι 1) := by simp [mul_assoc]
      _ = PGA.ι 1 * (-(PGA.ι 1 * PGA.ι 3)) := by rw [h31]
      _ = -(PGA.ι 1 * PGA.ι 1 * PGA.ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(PGA.ι 3) := by simp [e1_sq]
  rw [hL, hR, neg_neg]

theorem chiralityGen_anticomm_cyclic2 :
    chiralityGen * cyclic 2 = -(cyclic 2 * chiralityGen) := by
  unfold chiralityGen cyclic
  have h12 : PGA.ι 1 * PGA.ι 2 = -(PGA.ι 2 * PGA.ι 1) :=
    e_mul_anticomm (by decide)
  have hL : PGA.ι 1 * (PGA.ι 2 * PGA.ι 1) = -(PGA.ι 2) := by
    calc PGA.ι 1 * (PGA.ι 2 * PGA.ι 1)
        = (PGA.ι 1 * PGA.ι 2) * PGA.ι 1 := by simp [mul_assoc]
      _ = (-(PGA.ι 2 * PGA.ι 1)) * PGA.ι 1 := by rw [h12]
      _ = -(PGA.ι 2 * (PGA.ι 1 * PGA.ι 1)) := by simp [mul_assoc]
      _ = -(PGA.ι 2) := by simp [e1_sq]
  have hR : (PGA.ι 2 * PGA.ι 1) * PGA.ι 1 = PGA.ι 2 := by
    simp [mul_assoc, e1_sq]
  rw [hL, hR]

private theorem iota_ne_zero_of_sq_one {μ : Fin 5}
    (hsq : ι μ * ι μ = (1 : PGA)) : ι μ ≠ 0 := by
  intro h
  have : (1 : PGA) = 0 := by rw [← hsq, h, mul_zero]
  have hR : (1 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hR

private theorem e2_sq_one : ι 2 * ι 2 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (2 : Fin 5)

private theorem e3_sq_one : ι 3 * ι 3 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (3 : Fin 5)

theorem not_commute_chiralityGen_cyclic1 :
    cyclic 1 * chiralityGen ≠ chiralityGen * cyclic 1 := by
  rw [chiralityGen_anticomm_cyclic1]
  intro h
  have h2 : cyclic 1 * chiralityGen + cyclic 1 * chiralityGen = 0 :=
    eq_neg_iff_add_eq_zero.mp h
  have hsmul : (2 : ℝ) • (cyclic 1 * chiralityGen) = 0 := by
    simpa [two_smul] using h2
  have hprod : cyclic 1 * chiralityGen = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have hι : ι 3 = 0 := by
    have hR : (ι 1 * ι 3) * ι 1 = -(ι 3) := by
      unfold cyclic chiralityGen at hprod
      have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
      calc ι 1 * ι 3 * ι 1
          = ι 1 * (ι 3 * ι 1) := by simp [mul_assoc]
        _ = ι 1 * (-(ι 1 * ι 3)) := by rw [h31]
        _ = -(ι 1 * ι 1 * ι 3) := by simp [mul_neg, mul_assoc]
        _ = -(ι 3) := by simp [e1_sq]
    have : -(ι 3) = 0 := by
      unfold cyclic chiralityGen at hprod
      exact hR.symm.trans hprod
    exact neg_eq_zero.mp this
  exact iota_ne_zero_of_sq_one e3_sq_one hι

theorem not_commute_chiralityGen_cyclic2 :
    cyclic 2 * chiralityGen ≠ chiralityGen * cyclic 2 := by
  rw [chiralityGen_anticomm_cyclic2]
  intro h
  have h2 : cyclic 2 * chiralityGen + cyclic 2 * chiralityGen = 0 :=
    eq_neg_iff_add_eq_zero.mp h
  have hsmul : (2 : ℝ) • (cyclic 2 * chiralityGen) = 0 := by
    simpa [two_smul] using h2
  have hprod : cyclic 2 * chiralityGen = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have hι : ι 2 = 0 := by
    have : (ι 2 * ι 1) * ι 1 = ι 2 := by simp [mul_assoc, e1_sq]
    unfold cyclic chiralityGen at hprod
    exact this.symm.trans hprod
  exact iota_ne_zero_of_sq_one e2_sq_one hι

/-- Commuting Faraday triple relative to \(e_1\): \(B_x,\,E_y,\,E_z\). -/
theorem faraday_commuting_triple :
    Commute chiralityGen (cyclic 0) ∧
      Commute chiralityGen (hyperbolic 1) ∧
        Commute chiralityGen (hyperbolic 2) :=
  ⟨commute_chiralityGen_cyclic0, commute_chiralityGen_hyperbolic1,
    commute_chiralityGen_hyperbolic2⟩

/-- Anticommuting Faraday triple relative to \(e_1\): \(E_x,\,B_y,\,B_z\). -/
theorem faraday_anticommuting_triple :
    chiralityGen * hyperbolic 0 = -(hyperbolic 0 * chiralityGen) ∧
      chiralityGen * cyclic 1 = -(cyclic 1 * chiralityGen) ∧
        chiralityGen * cyclic 2 = -(cyclic 2 * chiralityGen) :=
  ⟨chiralityGen_anticomm_hyperbolic0, chiralityGen_anticomm_cyclic1,
    chiralityGen_anticomm_cyclic2⟩

/-! ### Same-projector sandwich selection -/

/-- \(P_R X P_R\). Linear in \(X\). -/
noncomputable def chiralSandwich (x : PGA) : PGA :=
  chiralityR * x * chiralityR

theorem chiralSandwich_add (x y : PGA) :
    chiralSandwich (x + y) = chiralSandwich x + chiralSandwich y := by
  unfold chiralSandwich
  noncomm_ring

theorem chiralSandwich_smul (c : ℝ) (x : PGA) :
    chiralSandwich (c • x) = c • chiralSandwich x := by
  unfold chiralSandwich
  rw [mul_smul_comm, smul_mul_assoc]

private theorem chiralSandwich_expand (x : PGA) :
    chiralSandwich x =
      ((1 : PGA) + chiralityGen) * x * ((1 : PGA) + chiralityGen) *
        (half * half) := by
  unfold chiralSandwich chiralityR
  have hhalfx : half * x = x * half := half_comm x
  calc ((1 : PGA) + chiralityGen) * half * x *
        (((1 : PGA) + chiralityGen) * half)
      = ((1 : PGA) + chiralityGen) * (half * x) *
          ((1 : PGA) + chiralityGen) * half := by simp [mul_assoc]
    _ = ((1 : PGA) + chiralityGen) * (x * half) *
          ((1 : PGA) + chiralityGen) * half := by rw [hhalfx]
    _ = ((1 : PGA) + chiralityGen) * x *
          (half * ((1 : PGA) + chiralityGen)) * half := by simp [mul_assoc]
    _ = ((1 : PGA) + chiralityGen) * x *
          (((1 : PGA) + chiralityGen) * half) * half := by rw [half_comm]
    _ = ((1 : PGA) + chiralityGen) * x * ((1 : PGA) + chiralityGen) *
          (half * half) := by simp [mul_assoc]

private theorem one_add_mul_anticomm {g x : PGA} (hg : g * g = 1)
    (hanti : g * x = -(x * g)) :
    ((1 : PGA) + g) * x * ((1 : PGA) + g) = 0 := by
  have hgxg : g * x * g = -x := by
    calc g * x * g
        = (-(x * g)) * g := by rw [hanti, neg_mul]
      _ = -(x * (g * g)) := by simp [mul_assoc]
      _ = -(x * 1) := by rw [hg]
      _ = -x := by simp
  have hsum : x * g + g * x = 0 := by
    rw [hanti, add_neg_cancel]
  calc ((1 : PGA) + g) * x * ((1 : PGA) + g)
      = x + x * g + g * x + g * x * g := by noncomm_ring
    _ = x + (x * g + g * x) + (-x) := by rw [hgxg]; ac_rfl
    _ = x + 0 + (-x) := by rw [hsum]
    _ = 0 := by abel

private theorem one_add_mul_comm {g x : PGA} (hg : g * g = 1)
    (hc : g * x = x * g) :
    ((1 : PGA) + g) * x * ((1 : PGA) + g) =
      algebraMap ℝ PGA 2 * (((1 : PGA) + g) * x) := by
  have hgxg : g * x * g = x := by
    calc g * x * g
        = (x * g) * g := by rw [hc]
      _ = x * (g * g) := by simp [mul_assoc]
      _ = x * 1 := by rw [hg]
      _ = x := by simp
  have htwo : x + x = algebraMap ℝ PGA 2 * x := add_self_eq_map_two_mul x
  have htwog : g * x + g * x = algebraMap ℝ PGA 2 * (g * x) :=
    add_self_eq_map_two_mul (g * x)
  have hxg : x * g = g * x := hc.symm
  calc ((1 : PGA) + g) * x * ((1 : PGA) + g)
      = x + x * g + g * x + g * x * g := by noncomm_ring
    _ = x + g * x + g * x + x := by rw [hxg, hgxg]
    _ = (x + x) + (g * x + g * x) := by abel
    _ = algebraMap ℝ PGA 2 * x + algebraMap ℝ PGA 2 * (g * x) := by
          rw [htwo, htwog]
    _ = algebraMap ℝ PGA 2 * (x + g * x) := by rw [mul_add]
    _ = algebraMap ℝ PGA 2 * (((1 : PGA) + g) * x) := by
          simp [add_mul, one_mul]

/-- Anticommuting generators are killed by \(P_R(-)P_R\). -/
theorem chiralSandwich_eq_zero_of_anticomm {x : PGA}
    (hanti : chiralityGen * x = -(x * chiralityGen)) :
    chiralSandwich x = 0 := by
  rw [chiralSandwich_expand, one_add_mul_anticomm chiralityGen_sq hanti,
    zero_mul]

/-- Commuting generators survive as \(P_R X\). -/
theorem chiralSandwich_eq_of_commute {x : PGA}
    (hc : Commute chiralityGen x) :
    chiralSandwich x = chiralityR * x := by
  have hx : chiralityGen * x = x * chiralityGen := hc
  have hexp := one_add_mul_comm chiralityGen_sq hx
  have hhalf : half * half = algebraMap ℝ PGA (1 / 4) := half_mul_half
  have h2q : algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4) = half :=
    two_mul_quarter
  rw [chiralSandwich_expand, hexp, hhalf]
  unfold chiralityR
  have hcommA :
      ((1 : PGA) + chiralityGen) * x * algebraMap ℝ PGA (1 / 4) =
        algebraMap ℝ PGA (1 / 4) * (((1 : PGA) + chiralityGen) * x) :=
    (Algebra.commutes (1 / 4 : ℝ) (((1 : PGA) + chiralityGen) * x)).symm
  calc algebraMap ℝ PGA 2 * (((1 : PGA) + chiralityGen) * x) *
        algebraMap ℝ PGA (1 / 4)
      = algebraMap ℝ PGA 2 * ((((1 : PGA) + chiralityGen) * x) *
          algebraMap ℝ PGA (1 / 4)) := by simp [mul_assoc]
    _ = algebraMap ℝ PGA 2 * (algebraMap ℝ PGA (1 / 4) *
          (((1 : PGA) + chiralityGen) * x)) := by rw [hcommA]
    _ = (algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4)) *
          (((1 : PGA) + chiralityGen) * x) := by simp [mul_assoc]
    _ = half * (((1 : PGA) + chiralityGen) * x) := by rw [h2q]
    _ = ((1 : PGA) + chiralityGen) * half * x := by
          rw [← mul_assoc, half_comm ((1 : PGA) + chiralityGen)]

theorem chiralSandwich_hyperbolic0 :
    chiralSandwich (hyperbolic 0) = 0 :=
  chiralSandwich_eq_zero_of_anticomm chiralityGen_anticomm_hyperbolic0

theorem chiralSandwich_cyclic1 :
    chiralSandwich (cyclic 1) = 0 :=
  chiralSandwich_eq_zero_of_anticomm chiralityGen_anticomm_cyclic1

theorem chiralSandwich_cyclic2 :
    chiralSandwich (cyclic 2) = 0 :=
  chiralSandwich_eq_zero_of_anticomm chiralityGen_anticomm_cyclic2

theorem chiralSandwich_cyclic0 :
    chiralSandwich (cyclic 0) = chiralityR * cyclic 0 :=
  chiralSandwich_eq_of_commute commute_chiralityGen_cyclic0

theorem chiralSandwich_hyperbolic1 :
    chiralSandwich (hyperbolic 1) = chiralityR * hyperbolic 1 :=
  chiralSandwich_eq_of_commute commute_chiralityGen_hyperbolic1

theorem chiralSandwich_hyperbolic2 :
    chiralSandwich (hyperbolic 2) = chiralityR * hyperbolic 2 :=
  chiralSandwich_eq_of_commute commute_chiralityGen_hyperbolic2

/-- Dual-parallel plus usual-perpendicular Faraday summand (axis \(e_1\)). -/
noncomputable def faradayCartan (p : FaradayParams) : PGA :=
  (p.B 0 / 2) • cyclic 0 + (p.E 1 / 2) • hyperbolic 1 +
    (p.E 2 / 2) • hyperbolic 2

/-- Usual-parallel plus dual-perpendicular Faraday summand (axis \(e_1\)). -/
noncomputable def faradayCharged (p : FaradayParams) : PGA :=
  (p.E 0 / 2) • hyperbolic 0 + (p.B 1 / 2) • cyclic 1 +
    (p.B 2 / 2) • cyclic 2

/-- Coefficient Cartan summand: commuting triple \((B_x,E_y,E_z)\). -/
def cartanParams (p : FaradayParams) : FaradayParams where
  E := fun
    | 0 => 0
    | 1 => p.E 1
    | 2 => p.E 2
  B := fun
    | 0 => p.B 0
    | _ => 0

/-- Coefficient charged summand: anticommuting triple \((E_x,B_y,B_z)\). -/
def chargedParams (p : FaradayParams) : FaradayParams where
  E := fun
    | 0 => p.E 0
    | _ => 0
  B := fun
    | 0 => 0
    | 1 => p.B 1
    | 2 => p.B 2

theorem cartanParams_add_chargedParams (p : FaradayParams) :
    cartanParams p + chargedParams p = p := by
  ext a <;> fin_cases a <;> simp [cartanParams, chargedParams]

theorem faraday_cartanParams (p : FaradayParams) :
    faraday (cartanParams p) = faradayCartan p := by
  rw [faraday_eq_add]
  unfold faradayUsual faradayDual faradayCartan toTorsion cartanParams
    omegaUsual omegaDual
  simp only [Fin.sum_univ_three]
  simp [zero_div, zero_smul]
  abel

theorem faraday_chargedParams (p : FaradayParams) :
    faraday (chargedParams p) = faradayCharged p := by
  rw [faraday_eq_add]
  unfold faradayUsual faradayDual faradayCharged toTorsion chargedParams
    omegaUsual omegaDual
  simp only [Fin.sum_univ_three]
  simp [zero_div, zero_smul]
  abel

/-- The \(z\)-Poynting cross of a Cartan field against a charged field vanishes. -/
theorem cross_z_cartan_charged (p q : FaradayParams) :
    cross (cartanParams p).E (chargedParams q).B 2 = 0 ∧
      cross (chargedParams q).E (cartanParams p).B 2 = 0 := by
  constructor <;> simp [cross, cartanParams, chargedParams]

theorem faraday_eq_cartan_add_charged (p : FaradayParams) :
    faraday p = faradayCartan p + faradayCharged p := by
  rw [faraday_eq_add]
  unfold faradayUsual faradayDual faradayCartan faradayCharged toTorsion
    omegaUsual omegaDual
  simp only [Fin.sum_univ_three]
  abel

theorem chiralSandwich_charged (p : FaradayParams) :
    chiralSandwich (faradayCharged p) = 0 := by
  unfold faradayCharged
  rw [chiralSandwich_add, chiralSandwich_add, chiralSandwich_smul,
    chiralSandwich_smul, chiralSandwich_smul, chiralSandwich_hyperbolic0,
    chiralSandwich_cyclic1, chiralSandwich_cyclic2]
  simp

theorem chiralSandwich_cartan (p : FaradayParams) :
    chiralSandwich (faradayCartan p) =
      chiralityR * faradayCartan p := by
  unfold faradayCartan
  rw [chiralSandwich_add, chiralSandwich_add, chiralSandwich_smul,
    chiralSandwich_smul, chiralSandwich_smul, chiralSandwich_cyclic0,
    chiralSandwich_hyperbolic1, chiralSandwich_hyperbolic2]
  simp [mul_add, add_assoc]

/-- The same-projector sandwich retains only the commuting Faraday summand. -/
theorem chiralSandwich_faraday (p : FaradayParams) :
    chiralSandwich (faraday p) = chiralityR * faradayCartan p := by
  rw [faraday_eq_cartan_add_charged, chiralSandwich_add,
    chiralSandwich_cartan, chiralSandwich_charged, add_zero]

/-! ### Left sandwich \(P_L X P_L\) also kills the charged summand -/

/-- \(P_L X P_L\). Linear in \(X\). -/
noncomputable def chiralSandwichL (x : PGA) : PGA :=
  chiralityL * x * chiralityL

theorem chiralSandwichL_add (x y : PGA) :
    chiralSandwichL (x + y) = chiralSandwichL x + chiralSandwichL y := by
  unfold chiralSandwichL
  noncomm_ring

theorem chiralSandwichL_smul (c : ℝ) (x : PGA) :
    chiralSandwichL (c • x) = c • chiralSandwichL x := by
  unfold chiralSandwichL
  rw [mul_smul_comm, smul_mul_assoc]

private theorem chiralSandwichL_expand (x : PGA) :
    chiralSandwichL x =
      ((1 : PGA) - chiralityGen) * x * ((1 : PGA) - chiralityGen) *
        (half * half) := by
  unfold chiralSandwichL chiralityL
  have hhalfx : half * x = x * half := half_comm x
  calc ((1 : PGA) - chiralityGen) * half * x *
        (((1 : PGA) - chiralityGen) * half)
      = ((1 : PGA) - chiralityGen) * (half * x) *
          ((1 : PGA) - chiralityGen) * half := by simp [mul_assoc]
    _ = ((1 : PGA) - chiralityGen) * (x * half) *
          ((1 : PGA) - chiralityGen) * half := by rw [hhalfx]
    _ = ((1 : PGA) - chiralityGen) * x *
          (half * ((1 : PGA) - chiralityGen)) * half := by simp [mul_assoc]
    _ = ((1 : PGA) - chiralityGen) * x *
          (((1 : PGA) - chiralityGen) * half) * half := by rw [half_comm]
    _ = ((1 : PGA) - chiralityGen) * x * ((1 : PGA) - chiralityGen) *
          (half * half) := by simp [mul_assoc]

private theorem one_sub_mul_anticomm {g x : PGA} (hg : g * g = 1)
    (hanti : g * x = -(x * g)) :
    ((1 : PGA) - g) * x * ((1 : PGA) - g) = 0 := by
  have hneg : (-g) * (-g) = (1 : PGA) := by
    simp [neg_mul, mul_neg, hg]
  have hanti' : (-g) * x = -(x * (-g)) := by
    calc (-g) * x = -(g * x) := by simp [neg_mul]
      _ = -(-(x * g)) := by rw [hanti]
      _ = x * g := by simp
      _ = -(x * (-g)) := by simp [mul_neg]
  have h := one_add_mul_anticomm hneg hanti'
  simpa [sub_eq_add_neg] using h

theorem chiralSandwichL_eq_zero_of_anticomm {x : PGA}
    (hanti : chiralityGen * x = -(x * chiralityGen)) :
    chiralSandwichL x = 0 := by
  rw [chiralSandwichL_expand, one_sub_mul_anticomm chiralityGen_sq hanti,
    zero_mul]

theorem chiralSandwichL_hyperbolic0 :
    chiralSandwichL (hyperbolic 0) = 0 :=
  chiralSandwichL_eq_zero_of_anticomm chiralityGen_anticomm_hyperbolic0

theorem chiralSandwichL_cyclic1 :
    chiralSandwichL (cyclic 1) = 0 :=
  chiralSandwichL_eq_zero_of_anticomm chiralityGen_anticomm_cyclic1

theorem chiralSandwichL_cyclic2 :
    chiralSandwichL (cyclic 2) = 0 :=
  chiralSandwichL_eq_zero_of_anticomm chiralityGen_anticomm_cyclic2

/-- The left sandwich likewise kills the anticommuting Faraday summand. -/
theorem chiralSandwichL_charged (p : FaradayParams) :
    chiralSandwichL (faradayCharged p) = 0 := by
  unfold faradayCharged
  rw [chiralSandwichL_add, chiralSandwichL_add, chiralSandwichL_smul,
    chiralSandwichL_smul, chiralSandwichL_smul, chiralSandwichL_hyperbolic0,
    chiralSandwichL_cyclic1, chiralSandwichL_cyclic2]
  simp

theorem chiralSandwichL_faraday (p : FaradayParams) :
    chiralSandwichL (faraday p) = chiralSandwichL (faradayCartan p) := by
  rw [faraday_eq_cartan_add_charged, chiralSandwichL_add,
    chiralSandwichL_charged, add_zero]

/-! ### Same-axis mix and the Faraday quadratic -/

/-- Plane rotation of Faraday coefficients; Hodge duality is \(\omega=\pi/2\). -/
noncomputable def mixFaradayParams (ω : ℝ) (p : FaradayParams) : FaradayParams where
  E := fun a => Real.cos ω * p.E a + Real.sin ω * p.B a
  B := fun a => -Real.sin ω * p.E a + Real.cos ω * p.B a

theorem mixFaradayParams_pi_div_two (p : FaradayParams) :
    mixFaradayParams (Real.pi / 2) p = dualFaradayParams p := by
  ext a <;> simp [mixFaradayParams, dualFaradayParams, Real.cos_pi_div_two,
    Real.sin_pi_div_two]

theorem energySq_mix (ω : ℝ) (p : FaradayParams) :
    energySq (mixFaradayParams ω p) =
      Real.cos ω ^ 2 * energySq p + Real.sin ω ^ 2 * magneticSq p +
        2 * Real.cos ω * Real.sin ω * faradayDot p := by
  unfold energySq mixFaradayParams magneticSq faradayDot
  simp only [Fin.sum_univ_three]
  ring

theorem magneticSq_mix (ω : ℝ) (p : FaradayParams) :
    magneticSq (mixFaradayParams ω p) =
      Real.sin ω ^ 2 * energySq p + Real.cos ω ^ 2 * magneticSq p -
        2 * Real.cos ω * Real.sin ω * faradayDot p := by
  unfold energySq mixFaradayParams magneticSq faradayDot
  simp only [Fin.sum_univ_three]
  ring

theorem J_mixFaraday (ω : ℝ) (p : FaradayParams) :
    J (toTorsion (mixFaradayParams ω p)) =
      Real.cos (2 * ω) * J (toTorsion p) +
        Real.sin (2 * ω) * faradayDot p := by
  rw [J_faraday, J_faraday, energySq_mix, magneticSq_mix]
  have hc : Real.cos ω ^ 2 - Real.sin ω ^ 2 = Real.cos (2 * ω) := by
    have h2 : Real.cos (2 * ω) = 2 * Real.cos ω ^ 2 - 1 := Real.cos_two_mul ω
    have hsin : Real.sin ω ^ 2 = 1 - Real.cos ω ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq ω]
    rw [hsin, h2]
    ring
  have hs : Real.sin (2 * ω) = 2 * Real.sin ω * Real.cos ω :=
    Real.sin_two_mul ω
  rw [← hc, hs]
  ring

theorem J_mixFaraday_of_orthogonal {ω : ℝ} {p : FaradayParams}
    (h : faradayDot p = 0) :
    J (toTorsion (mixFaradayParams ω p)) =
      Real.cos (2 * ω) * J (toTorsion p) := by
  rw [J_mixFaraday, h, mul_zero, add_zero]

/-- Same-axis electric and magnetic generators commute, so a mix factorises. -/
theorem commute_same_axis_faraday (a : Fin 3) :
    Commute (hyperbolic a) (cyclic a) :=
  commute_hyperbolic_cyclic_same a

/-! ### Sector signature in Faraday coefficients -/

theorem J_pureE (Ex : ℝ) :
    J (toTorsion (pureE Ex)) = (1 / 2) * Ex ^ 2 := by
  rw [J_faraday]
  simp [energySq, magneticSq, pureE, Fin.sum_univ_three]

theorem J_pureB (Bx : ℝ) :
    J (toTorsion (pureB Bx)) = -((1 / 2) * Bx ^ 2) := by
  rw [J_faraday]
  simp [energySq, magneticSq, pureB, Fin.sum_univ_three]

theorem J_pureE_nonneg (Ex : ℝ) :
    0 ≤ J (toTorsion (pureE Ex)) := by
  rw [J_pureE]
  exact mul_nonneg (by norm_num) (sq_nonneg Ex)

theorem J_pureB_nonpos (Bx : ℝ) :
    J (toTorsion (pureB Bx)) ≤ 0 := by
  rw [J_pureB]
  nlinarith [sq_nonneg Bx]

theorem J_pureE_eq_zero_iff (Ex : ℝ) :
    J (toTorsion (pureE Ex)) = 0 ↔ Ex = 0 := by
  rw [J_pureE]
  constructor
  · intro h
    have : Ex ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp this
  · intro h
    simp [h]

theorem J_pureB_eq_zero_iff (Bx : ℝ) :
    J (toTorsion (pureB Bx)) = 0 ↔ Bx = 0 := by
  rw [J_pureB]
  constructor
  · intro h
    have : Bx ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp this
  · intro h
    simp [h]

end Gravity

end DstDiophantine
