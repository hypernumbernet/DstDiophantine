import DstDiophantine.Logic.Quantum.MinimalIdeal
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-!
# Composite spinor projectors

The paper's `P = P_spin P_R` with `P_spin = (1+e₀e₁)/2` and `P_R = (1+e₁)/2`
is not idempotent: those factors do not commute. A commuting square-`+1`
pair is `e₁` with the off-axis boost `e₀e₂`. Left-ideal irreducibility
remains deferred.
-/

namespace DstDiophantine

namespace Logic

open PGA Operations Generators

theorem hyperbolic0_mul_chiralityGen :
    hyperbolic 0 * chiralityGen = PGA.ι 0 := by
  unfold hyperbolic chiralityGen
  simp [mul_assoc, e1_sq]

theorem chiralityGen_mul_hyperbolic0 :
    chiralityGen * hyperbolic 0 = -(PGA.ι 0) := by
  unfold hyperbolic chiralityGen
  have h10 : PGA.ι 1 * PGA.ι 0 = -(PGA.ι 0 * PGA.ι 1) :=
    e_mul_anticomm (by decide)
  calc PGA.ι 1 * (PGA.ι 0 * PGA.ι 1)
      = (PGA.ι 1 * PGA.ι 0) * PGA.ι 1 := by simp [mul_assoc]
    _ = (-(PGA.ι 0 * PGA.ι 1)) * PGA.ι 1 := by rw [h10]
    _ = -(PGA.ι 0 * (PGA.ι 1 * PGA.ι 1)) := by simp [mul_assoc]
    _ = -(PGA.ι 0) := by simp [e1_sq]

theorem chiralityGen_anticomm_hyperbolic0 :
    chiralityGen * hyperbolic 0 = -(hyperbolic 0 * chiralityGen) := by
  rw [chiralityGen_mul_hyperbolic0, hyperbolic0_mul_chiralityGen]

theorem not_commute_hyperbolic0_chiralityGen :
    hyperbolic 0 * chiralityGen ≠ chiralityGen * hyperbolic 0 := by
  rw [hyperbolic0_mul_chiralityGen, chiralityGen_mul_hyperbolic0]
  intro h
  have h2 : PGA.ι 0 + PGA.ι 0 = 0 := by
    simpa [sub_eq_add_neg] using (eq_neg_iff_add_eq_zero.mp h)
  have : (2 : ℝ) • PGA.ι 0 = 0 := by simpa [two_smul] using h2
  have h0 : PGA.ι 0 = 0 :=
    (smul_eq_zero.mp this).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have : algebraMap ℝ PGA (-1 : ℝ) = 0 := by
    rw [← e0_sq, h0, mul_zero]
  have hR : (-1 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hR

/-- If involutions `u,v` anticommute, then `((1+u)(1+v))² = 2(1+u)(1+v)`. -/
private theorem anticommute_expand_sq {u v : PGA}
    (_hu : u * u = 1) (hv : v * v = 1)
    (hanti : v * u = -(u * v)) :
    ((1 : PGA) + u) * ((1 : PGA) + v) * (((1 : PGA) + u) * ((1 : PGA) + v)) =
      algebraMap ℝ PGA 2 * (((1 : PGA) + u) * ((1 : PGA) + v)) := by
  have hmid :
      ((1 : PGA) + v) * ((1 : PGA) + u) * ((1 : PGA) + v) =
        algebraMap ℝ PGA 2 * ((1 : PGA) + v) := by
    have hexp :
        ((1 : PGA) + v) * ((1 : PGA) + u) * ((1 : PGA) + v) =
          (1 : PGA) + v + u + u * v + v + v * v + v * u + v * u * v := by
      noncomm_ring
    have hvuv : v * u * v = -u := by
      calc v * u * v
          = -(u * v) * v := by rw [hanti, neg_mul]
        _ = -(u * (v * v)) := by simp [mul_assoc]
        _ = -(u * 1) := by rw [hv]
        _ = -u := by simp
    rw [hexp, hv, hvuv, hanti]
    have : (1 : PGA) + v + u + u * v + v + 1 + -(u * v) + -u =
        algebraMap ℝ PGA 2 * ((1 : PGA) + v) := by
      have h2 : (1 + 1 : PGA) = algebraMap ℝ PGA 2 := one_add_one_eq_map_two
      calc (1 : PGA) + v + u + u * v + v + 1 + -(u * v) + -u
          = (1 + 1) + (v + v) + (u + -u) + (u * v + -(u * v)) := by abel
        _ = algebraMap ℝ PGA 2 + algebraMap ℝ PGA 2 * v + 0 + 0 := by
              rw [h2, add_self_eq_map_two_mul, add_neg_cancel, add_neg_cancel]
        _ = algebraMap ℝ PGA 2 * ((1 : PGA) + v) := by noncomm_ring
    exact this
  calc ((1 : PGA) + u) * ((1 : PGA) + v) * (((1 : PGA) + u) * ((1 : PGA) + v))
      = ((1 : PGA) + u) * (((1 : PGA) + v) * ((1 : PGA) + u) * ((1 : PGA) + v)) := by
          noncomm_ring
    _ = ((1 : PGA) + u) * (algebraMap ℝ PGA 2 * ((1 : PGA) + v)) := by rw [hmid]
    _ = algebraMap ℝ PGA 2 * (((1 : PGA) + u) * ((1 : PGA) + v)) := by
          rw [← mul_assoc, ← map_two_comm, mul_assoc]

theorem paperComposite_num_sq :
    (((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen)) *
      (((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen)) =
      algebraMap ℝ PGA 2 *
        (((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen)) :=
  anticommute_expand_sq (hyperbolic_sq 0) chiralityGen_sq
    chiralityGen_anticomm_hyperbolic0

theorem paperComposite_eq_factor :
    ((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen) =
      ((1 : PGA) + PGA.ι 0) * ((1 : PGA) + chiralityGen) := by
  have h : ((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen) =
      (1 : PGA) + chiralityGen + hyperbolic 0 + hyperbolic 0 * chiralityGen := by
    simp [mul_add, add_mul, one_mul, mul_one]
    abel
  have h' : ((1 : PGA) + PGA.ι 0) * ((1 : PGA) + chiralityGen) =
      (1 : PGA) + chiralityGen + PGA.ι 0 + PGA.ι 0 * chiralityGen := by
    simp [mul_add, add_mul, one_mul, mul_one]
    abel
  have hι : PGA.ι 0 * chiralityGen = hyperbolic 0 := by
    unfold hyperbolic chiralityGen; rfl
  rw [h, h', hyperbolic0_mul_chiralityGen, hι]
  abel

theorem paperComposite_num_ne_zero :
    ((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen) ≠ 0 := by
  intro hA
  rw [paperComposite_eq_factor] at hA
  have hsq : ((1 : PGA) - PGA.ι 0) * ((1 : PGA) + PGA.ι 0) =
      algebraMap ℝ PGA 2 := by
    calc ((1 : PGA) - PGA.ι 0) * ((1 : PGA) + PGA.ι 0)
        = 1 - PGA.ι 0 * PGA.ι 0 := by noncomm_ring
      _ = 1 - algebraMap ℝ PGA (-1) := by rw [e0_sq]
      _ = algebraMap ℝ PGA 1 + algebraMap ℝ PGA 1 := by
            simp [Algebra.algebraMap_eq_smul_one, map_neg]
      _ = algebraMap ℝ PGA 2 := one_add_one_eq_map_two
  have hfactor :
      ((1 : PGA) - PGA.ι 0) *
        (((1 : PGA) + PGA.ι 0) * ((1 : PGA) + chiralityGen)) =
        algebraMap ℝ PGA 2 * ((1 : PGA) + chiralityGen) := by
    rw [← mul_assoc, hsq]
  rw [hA] at hfactor
  simp only [mul_zero] at hfactor
  have hv : (1 : PGA) + chiralityGen = 0 := by
    have : (2 : ℝ) • ((1 : PGA) + chiralityGen) = 0 := by
      simpa [two_smul, Algebra.smul_def] using hfactor.symm
    exact (smul_eq_zero.mp this).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have he1 : chiralityGen = -1 := eq_neg_of_add_eq_zero_right hv
  have hanti : chiralityGen * PGA.ι 0 + PGA.ι 0 * chiralityGen = 0 :=
    e_anticomm (by decide : (1 : Fin 5) ≠ 0)
  rw [he1] at hanti
  have h0sum : PGA.ι 0 + PGA.ι 0 = 0 := by
    have : (-1 : PGA) * PGA.ι 0 + PGA.ι 0 * (-1) = 0 := hanti
    have hneg : -(PGA.ι 0) + -(PGA.ι 0) = 0 := by simpa using this
    have : -(PGA.ι 0 + PGA.ι 0) = 0 := by simpa [neg_add] using hneg
    exact neg_eq_zero.mp this
  have h0 : PGA.ι 0 = 0 := by
    have : (2 : ℝ) • PGA.ι 0 = 0 := by simpa [two_smul] using h0sum
    exact (smul_eq_zero.mp this).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have : algebraMap ℝ PGA (-1 : ℝ) = 0 := by
    rw [← e0_sq, h0, mul_zero]
  have hR : (-1 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hR

private theorem algebraMap_comm (r : ℝ) (x : PGA) :
    algebraMap ℝ PGA r * x = x * algebraMap ℝ PGA r :=
  Algebra.commutes r x

theorem paperComposite_not_idempotent :
    (spinorIdem * chiralityR) * (spinorIdem * chiralityR) ≠
      spinorIdem * chiralityR := by
  intro h
  set A := ((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen)
  have hP : spinorIdem * chiralityR = A * (half * half) := by
    simp [spinorIdem, chiralityR, A, mul_half_mul_half]
  rw [hP] at h
  have hP2 :
      (A * (half * half)) * (A * (half * half)) =
        (A * A) * ((half * half) * (half * half)) := by
    have hc : half * half * A = A * (half * half) := by
      rw [half_mul_half]
      exact Algebra.commutes (1 / 4 : ℝ) A
    calc A * (half * half) * (A * (half * half))
        = A * (half * half * A) * (half * half) := by noncomm_ring
      _ = A * (A * (half * half)) * (half * half) := by rw [hc]
      _ = A * A * (half * half * (half * half)) := by noncomm_ring
  rw [hP2, paperComposite_num_sq] at h
  have h4 : half * half = algebraMap ℝ PGA (1 / 4) := half_mul_half
  rw [h4] at h
  have h16 : algebraMap ℝ PGA (1 / 4) * algebraMap ℝ PGA (1 / 4) =
      algebraMap ℝ PGA (1 / 16) := by
    rw [← map_mul]; norm_num
  rw [h16] at h
  have hscale : algebraMap ℝ PGA (1 / 8) * A = algebraMap ℝ PGA (1 / 4) * A := by
    have h2 : algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 16) =
        algebraMap ℝ PGA (1 / 8) := by
      rw [← map_mul]; norm_num
    have hLHS : algebraMap ℝ PGA 2 * A * algebraMap ℝ PGA (1 / 16) =
        algebraMap ℝ PGA (1 / 8) * A := by
      calc algebraMap ℝ PGA 2 * A * algebraMap ℝ PGA (1 / 16)
          = algebraMap ℝ PGA 2 * (A * algebraMap ℝ PGA (1 / 16)) := by rw [mul_assoc]
        _ = algebraMap ℝ PGA 2 * (algebraMap ℝ PGA (1 / 16) * A) := by
              rw [algebraMap_comm (1 / 16 : ℝ) A]
        _ = (algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 16)) * A := by rw [← mul_assoc]
        _ = algebraMap ℝ PGA (1 / 8) * A := by rw [h2]
    have hRHS : A * algebraMap ℝ PGA (1 / 4) = algebraMap ℝ PGA (1 / 4) * A :=
      (algebraMap_comm _ _).symm
    exact (hLHS.symm.trans h).trans hRHS
  have : algebraMap ℝ PGA ((1 / 8 : ℝ) - (1 / 4)) * A = 0 := by
    rw [map_sub, sub_mul, hscale, sub_self]
  have hcoef : (1 / 8 : ℝ) - 1 / 4 ≠ 0 := by norm_num
  have hA0 : A = 0 := by
    have hsmul : ((1 / 8 : ℝ) - 1 / 4) • A = 0 := by
      simpa [Algebra.smul_def] using this
    exact (smul_eq_zero.mp hsmul).resolve_left hcoef
  exact paperComposite_num_ne_zero (by simpa [A] using hA0)

theorem not_commute_spinorIdem_chiralityR :
    spinorIdem * chiralityR ≠ chiralityR * spinorIdem := by
  intro h
  have hL : spinorIdem * chiralityR =
      ((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen) * (half * half) := by
    simp [spinorIdem, chiralityR, mul_half_mul_half]
  have hR : chiralityR * spinorIdem =
      ((1 : PGA) + chiralityGen) * ((1 : PGA) + hyperbolic 0) * (half * half) := by
    simp [spinorIdem, chiralityR, mul_half_mul_half]
  rw [hL, hR] at h
  have hdiff :
      (((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen) -
        ((1 : PGA) + chiralityGen) * ((1 : PGA) + hyperbolic 0)) *
        (half * half) = 0 := by
    simpa [sub_mul] using sub_eq_zero.mpr h
  have hsub :
      ((1 : PGA) + hyperbolic 0) * ((1 : PGA) + chiralityGen) -
        ((1 : PGA) + chiralityGen) * ((1 : PGA) + hyperbolic 0) =
          hyperbolic 0 * chiralityGen - chiralityGen * hyperbolic 0 := by
    noncomm_ring
  rw [hsub, hyperbolic0_mul_chiralityGen, chiralityGen_mul_hyperbolic0,
    half_mul_half] at hdiff
  have htwo : PGA.ι 0 - (-PGA.ι 0) = algebraMap ℝ PGA 2 * PGA.ι 0 := by
    simpa [sub_neg_eq_add] using add_self_eq_map_two_mul (PGA.ι 0)
  rw [htwo] at hdiff
  have : algebraMap ℝ PGA (1 / 2) * PGA.ι 0 = 0 := by
    have h2 : algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4) =
        algebraMap ℝ PGA (1 / 2) := by
      rw [← map_mul]; norm_num
    calc algebraMap ℝ PGA (1 / 2) * PGA.ι 0
        = algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4) * PGA.ι 0 := by rw [h2]
      _ = algebraMap ℝ PGA 2 * (algebraMap ℝ PGA (1 / 4) * PGA.ι 0) := by
            rw [mul_assoc]
      _ = algebraMap ℝ PGA 2 * (PGA.ι 0 * algebraMap ℝ PGA (1 / 4)) := by
            rw [algebraMap_comm (1 / 4 : ℝ) (PGA.ι 0)]
      _ = algebraMap ℝ PGA 2 * PGA.ι 0 * algebraMap ℝ PGA (1 / 4) := by
            rw [mul_assoc]
      _ = 0 := hdiff
  have hsmul : (1 / 2 : ℝ) • PGA.ι 0 = 0 := by simpa [Algebra.smul_def] using this
  have h0 : PGA.ι 0 = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have : algebraMap ℝ PGA (-1 : ℝ) = 0 := by
    rw [← e0_sq, h0, mul_zero]
  have hz : (-1 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hz

theorem commute_chiralityGen_hyperbolic1 :
    Commute chiralityGen (hyperbolic 1) := by
  change chiralityGen * hyperbolic 1 = hyperbolic 1 * chiralityGen
  unfold chiralityGen hyperbolic
  have h10 : PGA.ι 1 * PGA.ι 0 = -(PGA.ι 0 * PGA.ι 1) :=
    e_mul_anticomm (by decide)
  have h21 : PGA.ι 2 * PGA.ι 1 = -(PGA.ι 1 * PGA.ι 2) :=
    e_mul_anticomm (by decide)
  calc PGA.ι 1 * (PGA.ι 0 * PGA.ι 2)
      = (PGA.ι 1 * PGA.ι 0) * PGA.ι 2 := by simp [mul_assoc]
    _ = (-(PGA.ι 0 * PGA.ι 1)) * PGA.ι 2 := by rw [h10]
    _ = -(PGA.ι 0 * PGA.ι 1 * PGA.ι 2) := by simp [mul_assoc]
    _ = PGA.ι 0 * (-(PGA.ι 1 * PGA.ι 2)) := by simp [mul_neg, mul_assoc]
    _ = PGA.ι 0 * (PGA.ι 2 * PGA.ι 1) := by rw [← h21]
    _ = (PGA.ι 0 * PGA.ι 2) * PGA.ι 1 := by simp [mul_assoc]

noncomputable def spinorIdemAxis1 : PGA :=
  ((1 : PGA) + hyperbolic 1) * half

theorem spinorIdemAxis1_sq : spinorIdemAxis1 * spinorIdemAxis1 = spinorIdemAxis1 :=
  idempotent_of_sq_one (hyperbolic_sq 1)

theorem commute_chiralityR_spinorIdemAxis1 :
    Commute chiralityR spinorIdemAxis1 := by
  change chiralityR * spinorIdemAxis1 = spinorIdemAxis1 * chiralityR
  unfold chiralityR spinorIdemAxis1
  have hc : chiralityGen * hyperbolic 1 = hyperbolic 1 * chiralityGen :=
    commute_chiralityGen_hyperbolic1
  have hfactors :
      ((1 : PGA) + chiralityGen) * ((1 : PGA) + hyperbolic 1) =
        ((1 : PGA) + hyperbolic 1) * ((1 : PGA) + chiralityGen) := by
    simp [mul_add, add_mul, one_mul, mul_one, hc]
    abel
  rw [mul_half_mul_half, mul_half_mul_half, hfactors]

theorem chiralityR_mul_spinorIdemAxis1_sq :
    (chiralityR * spinorIdemAxis1) * (chiralityR * spinorIdemAxis1) =
      chiralityR * spinorIdemAxis1 := by
  have hc : chiralityR * spinorIdemAxis1 = spinorIdemAxis1 * chiralityR :=
    commute_chiralityR_spinorIdemAxis1
  calc chiralityR * spinorIdemAxis1 * (chiralityR * spinorIdemAxis1)
      = chiralityR * (spinorIdemAxis1 * chiralityR) * spinorIdemAxis1 := by
          simp [mul_assoc]
    _ = chiralityR * (chiralityR * spinorIdemAxis1) * spinorIdemAxis1 := by
          rw [hc]
    _ = (chiralityR * chiralityR) * (spinorIdemAxis1 * spinorIdemAxis1) := by
          simp [mul_assoc]
    _ = chiralityR * spinorIdemAxis1 := by
          rw [chiralityR_sq, spinorIdemAxis1_sq]

end Logic

end DstDiophantine
