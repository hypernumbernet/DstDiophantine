import DstDiophantine.Gravity.ChiralSpectrum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Chirality-even and chirality-odd Faraday summands

## Paper boundary (do **not** claim)

A Weinberg angle, \(W/Z\) masses, and a V--A coupling are **not** derived.
The chirality-odd summand exchanges the two projectors. It does not remain
inside one of them, and the chirality-even summand is the Cartan
\(\mathfrak{so}(2,1)\), not a left-handed current.

## What is proved

* Left multiplication by a charged generator exchanges the projectors of its
  axis. The cross sandwich \(P_L X P_R\) retains that generator and does not
  vanish. The same-side sandwich vanishes.
* Left multiplication by a Cartan generator preserves each projector. The
  cross sandwich vanishes.
* Relative to any one axis the Faraday coefficients split into that even
  piece and that odd piece, and the mismatch adds: the cross term in \(J\)
  is zero.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Operations Invariant Logic

/-! ### Charged generators exchange the projectors -/

theorem chargedGen_mul_spatialGen (a i : Fin 3) :
    chargedGen a i * spatialGen a = -(spatialGen a * chargedGen a i) := by
  have h := chargedGen_anticomm_axis a i
  calc chargedGen a i * spatialGen a
      = -(-(chargedGen a i * spatialGen a)) := by simp
    _ = -(spatialGen a * chargedGen a i) := by rw [← h]

theorem chargedGen_mul_chiralityRAxis (a i : Fin 3) :
    chargedGen a i * chiralityRAxis a = chiralityLAxis a * chargedGen a i := by
  unfold chiralityRAxis chiralityLAxis
  have hL : chargedGen a i * (((1 : PGA) + spatialGen a) * half) =
      (chargedGen a i - spatialGen a * chargedGen a i) * half := by
    calc chargedGen a i * (((1 : PGA) + spatialGen a) * half)
        = (chargedGen a i * ((1 : PGA) + spatialGen a)) * half := by rw [mul_assoc]
      _ = (chargedGen a i * 1 + chargedGen a i * spatialGen a) * half := by rw [mul_add]
      _ = (chargedGen a i + chargedGen a i * spatialGen a) * half := by rw [mul_one]
      _ = (chargedGen a i + -(spatialGen a * chargedGen a i)) * half := by
            rw [chargedGen_mul_spatialGen]
      _ = (chargedGen a i - spatialGen a * chargedGen a i) * half := by rw [sub_eq_add_neg]
  have hR : ((1 : PGA) - spatialGen a) * half * chargedGen a i =
      (chargedGen a i - spatialGen a * chargedGen a i) * half := by
    calc ((1 : PGA) - spatialGen a) * half * chargedGen a i
        = ((1 : PGA) - spatialGen a) * (half * chargedGen a i) := by rw [mul_assoc]
      _ = ((1 : PGA) - spatialGen a) * (chargedGen a i * half) := by rw [half_comm]
      _ = ((1 : PGA) - spatialGen a) * chargedGen a i * half := by rw [← mul_assoc]
      _ = (1 * chargedGen a i - spatialGen a * chargedGen a i) * half := by rw [sub_mul]
      _ = (chargedGen a i - spatialGen a * chargedGen a i) * half := by rw [one_mul]
  exact hL.trans hR.symm

theorem chargedGen_mul_chiralityLAxis (a i : Fin 3) :
    chargedGen a i * chiralityLAxis a = chiralityRAxis a * chargedGen a i := by
  unfold chiralityRAxis chiralityLAxis
  have hL : chargedGen a i * (((1 : PGA) - spatialGen a) * half) =
      (chargedGen a i + spatialGen a * chargedGen a i) * half := by
    calc chargedGen a i * (((1 : PGA) - spatialGen a) * half)
        = (chargedGen a i * ((1 : PGA) - spatialGen a)) * half := by rw [mul_assoc]
      _ = (chargedGen a i * 1 - chargedGen a i * spatialGen a) * half := by rw [mul_sub]
      _ = (chargedGen a i - chargedGen a i * spatialGen a) * half := by rw [mul_one]
      _ = (chargedGen a i - -(spatialGen a * chargedGen a i)) * half := by
            rw [chargedGen_mul_spatialGen]
      _ = (chargedGen a i + spatialGen a * chargedGen a i) * half := by
            rw [sub_neg_eq_add]
  have hR : ((1 : PGA) + spatialGen a) * half * chargedGen a i =
      (chargedGen a i + spatialGen a * chargedGen a i) * half := by
    calc ((1 : PGA) + spatialGen a) * half * chargedGen a i
        = ((1 : PGA) + spatialGen a) * (half * chargedGen a i) := by rw [mul_assoc]
      _ = ((1 : PGA) + spatialGen a) * (chargedGen a i * half) := by rw [half_comm]
      _ = ((1 : PGA) + spatialGen a) * chargedGen a i * half := by rw [← mul_assoc]
      _ = (1 * chargedGen a i + spatialGen a * chargedGen a i) * half := by rw [add_mul]
      _ = (chargedGen a i + spatialGen a * chargedGen a i) * half := by rw [one_mul]
  exact hL.trans hR.symm

/-- The cross sandwich retains the charged generator. -/
theorem crossSandwich_charged (a i : Fin 3) :
    chiralityLAxis a * chargedGen a i * chiralityRAxis a =
      chiralityLAxis a * chargedGen a i := by
  calc chiralityLAxis a * chargedGen a i * chiralityRAxis a
      = chiralityLAxis a * (chargedGen a i * chiralityRAxis a) := by simp [mul_assoc]
    _ = chiralityLAxis a * (chiralityLAxis a * chargedGen a i) := by
          rw [chargedGen_mul_chiralityRAxis]
    _ = (chiralityLAxis a * chiralityLAxis a) * chargedGen a i := by simp [mul_assoc]
    _ = chiralityLAxis a * chargedGen a i := by rw [chiralityLAxis_sq]

/-- The same-side sandwich kills the charged generator. -/
theorem sameSandwich_charged (a i : Fin 3) :
    chiralityRAxis a * chargedGen a i * chiralityRAxis a = 0 := by
  calc chiralityRAxis a * chargedGen a i * chiralityRAxis a
      = chargedGen a i * chiralityLAxis a * chiralityRAxis a := by
          rw [← chargedGen_mul_chiralityLAxis]
    _ = chargedGen a i * (chiralityLAxis a * chiralityRAxis a) := by rw [mul_assoc]
    _ = chargedGen a i * 0 := by rw [chiralityLAxis_mul_chiralityRAxis]
    _ = 0 := mul_zero _

/-! ### The cross sandwich does not vanish -/

private theorem spatialGen_anticomm_time (a : Fin 3) :
    spatialGen a * ι 0 = -(ι 0 * spatialGen a) := by
  fin_cases a
  · simpa [spatialGen] using e_mul_anticomm (by decide : (1 : Fin 5) ≠ 0)
  · simpa [spatialGen] using e_mul_anticomm (by decide : (2 : Fin 5) ≠ 0)
  · simpa [spatialGen] using e_mul_anticomm (by decide : (3 : Fin 5) ≠ 0)

private theorem spatialGen_ne_one (a : Fin 3) : spatialGen a ≠ 1 := by
  intro h
  have hanti := spatialGen_anticomm_time a
  rw [h, one_mul, mul_one] at hanti
  have hsum : ι 0 + ι 0 = 0 := by
    nth_rw 1 [hanti]
    exact neg_add_cancel (ι 0)
  have htwo : algebraMap ℝ PGA 2 * ι 0 = 0 := by
    rw [← add_self_eq_map_two_mul, hsum]
  have hι : ι 0 = 0 := by
    have hsmul : (2 : ℝ) • ι 0 = 0 := by
      simpa [Algebra.smul_def] using htwo
    exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
  have hmap : algebraMap ℝ PGA (-1 : ℝ) = 0 := by
    rw [← e0_sq, hι, mul_zero]
  have hℝ : (-1 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp hmap
  norm_num at hℝ

private theorem half_mul_two : half * algebraMap ℝ PGA 2 = 1 := by
  rw [half_comm, two_mul_half]

private theorem chiralityLAxis_mul_ne_zero_of_sq {a : Fin 3} {g : PGA}
    (hsq : g * g = 1 ∨ g * g = -1) (hg : chiralityLAxis a * g = 0) : False := by
  have hclear : ((1 : PGA) - spatialGen a) * g = 0 := by
    have h0 : ((1 : PGA) - spatialGen a) * (g * half) = 0 := by
      simpa [chiralityLAxis, mul_assoc, half_comm] using hg
    have hmul := congrArg (fun z : PGA => z * algebraMap ℝ PGA 2) h0
    simpa [mul_assoc, half_mul_two] using hmul
  have hge : g = spatialGen a * g := by
    have : g - spatialGen a * g = 0 := by
      simpa [sub_mul, one_mul] using hclear
    exact sub_eq_zero.mp this
  have hs : g * g = spatialGen a * (g * g) := by
    calc g * g
        = (spatialGen a * g) * g := by rw [← hge]
      _ = spatialGen a * (g * g) := by rw [mul_assoc]
  have he : spatialGen a = 1 := by
    rcases hsq with h1 | h1
    · have : (1 : PGA) = spatialGen a * 1 := by simpa [h1] using hs
      simpa using this.symm
    · have hneg : spatialGen a * (-1 : PGA) = -spatialGen a := by simp
      have : (-1 : PGA) = -spatialGen a := by simpa [h1, hneg] using hs
      exact neg_inj.mp this.symm
  exact spatialGen_ne_one a he

theorem crossSandwich_charged_ne_zero (a i : Fin 3) :
    chiralityLAxis a * chargedGen a i * chiralityRAxis a ≠ 0 := by
  rw [crossSandwich_charged]
  intro hz
  have hsq : chargedGen a i * chargedGen a i = 1 ∨
      chargedGen a i * chargedGen a i = -1 := by
    fin_cases i
    · exact Or.inl (chargedGen_sq a).1
    · exact Or.inr (chargedGen_sq a).2.1
    · exact Or.inr (chargedGen_sq a).2.2
  exact chiralityLAxis_mul_ne_zero_of_sq hsq hz

/-! ### Cartan generators preserve the projectors -/

theorem cartanGen_mul_chiralityRAxis (a i : Fin 3) :
    cartanGen a i * chiralityRAxis a = chiralityRAxis a * cartanGen a i := by
  have hc : cartanGen a i * spatialGen a = spatialGen a * cartanGen a i :=
    (cartanGen_commute_axis a i).eq.symm
  unfold chiralityRAxis
  have hL : cartanGen a i * (((1 : PGA) + spatialGen a) * half) =
      (cartanGen a i + spatialGen a * cartanGen a i) * half := by
    calc cartanGen a i * (((1 : PGA) + spatialGen a) * half)
        = (cartanGen a i * ((1 : PGA) + spatialGen a)) * half := by rw [mul_assoc]
      _ = (cartanGen a i * 1 + cartanGen a i * spatialGen a) * half := by rw [mul_add]
      _ = (cartanGen a i + cartanGen a i * spatialGen a) * half := by rw [mul_one]
      _ = (cartanGen a i + spatialGen a * cartanGen a i) * half := by rw [hc]
  have hR : ((1 : PGA) + spatialGen a) * half * cartanGen a i =
      (cartanGen a i + spatialGen a * cartanGen a i) * half := by
    calc ((1 : PGA) + spatialGen a) * half * cartanGen a i
        = ((1 : PGA) + spatialGen a) * (half * cartanGen a i) := by rw [mul_assoc]
      _ = ((1 : PGA) + spatialGen a) * (cartanGen a i * half) := by rw [half_comm]
      _ = ((1 : PGA) + spatialGen a) * cartanGen a i * half := by rw [← mul_assoc]
      _ = (1 * cartanGen a i + spatialGen a * cartanGen a i) * half := by rw [add_mul]
      _ = (cartanGen a i + spatialGen a * cartanGen a i) * half := by rw [one_mul]
  exact hL.trans hR.symm

theorem crossSandwich_cartan (a i : Fin 3) :
    chiralityLAxis a * cartanGen a i * chiralityRAxis a = 0 := by
  calc chiralityLAxis a * cartanGen a i * chiralityRAxis a
      = chiralityLAxis a * (chiralityRAxis a * cartanGen a i) := by
          rw [← cartanGen_mul_chiralityRAxis, mul_assoc]
    _ = (chiralityLAxis a * chiralityRAxis a) * cartanGen a i := by rw [← mul_assoc]
    _ = 0 := by rw [chiralityLAxis_mul_chiralityRAxis, zero_mul]

/-! ### The mismatch adds across the split -/

/-- Chirality-even Faraday coefficients of axis `a`: \((B_a,E_{a+1},E_{a+2})\). -/
def evenParams (a : Fin 3) (p : FaradayParams) : FaradayParams where
  E := fun b => if b = a then 0 else p.E b
  B := fun b => if b = a then p.B b else 0

/-- Chirality-odd Faraday coefficients of axis `a`: \((E_a,B_{a+1},B_{a+2})\). -/
def oddParams (a : Fin 3) (p : FaradayParams) : FaradayParams where
  E := fun b => if b = a then p.E b else 0
  B := fun b => if b = a then 0 else p.B b

theorem evenParams_add_oddParams (a : Fin 3) (p : FaradayParams) :
    evenParams a p + oddParams a p = p := by
  ext b
  · simp only [add_E, evenParams, oddParams]
    split_ifs <;> simp
  · simp only [add_B, evenParams, oddParams]
    split_ifs <;> simp

theorem evenParams_zero (p : FaradayParams) : evenParams 0 p = cartanParams p := by
  ext b <;> fin_cases b <;> simp [evenParams, cartanParams]

theorem oddParams_zero (p : FaradayParams) : oddParams 0 p = chargedParams p := by
  ext b <;> fin_cases b <;> simp [oddParams, chargedParams]

theorem faradayCross_even_odd (a : Fin 3) (p : FaradayParams) :
    faradayCross (evenParams a p) (oddParams a p) = 0 := by
  unfold faradayCross evenParams oddParams
  fin_cases a <;> simp [Fin.sum_univ_three]

/-- The mismatch of a Faraday field is the sum of its even and odd mismatches. -/
theorem J_even_add_odd (a : Fin 3) (p : FaradayParams) :
    J (toTorsion p) =
      J (toTorsion (evenParams a p)) + J (toTorsion (oddParams a p)) := by
  have hsum : evenParams a p + oddParams a p = p := evenParams_add_oddParams a p
  calc J (toTorsion p)
      = J (toTorsion (evenParams a p + oddParams a p)) := by rw [hsum]
    _ = J (toTorsion (evenParams a p)) + J (toTorsion (oddParams a p)) +
          faradayCross (evenParams a p) (oddParams a p) := J_add _ _
    _ = J (toTorsion (evenParams a p)) + J (toTorsion (oddParams a p)) := by
          rw [faradayCross_even_odd, add_zero]

end Gravity

end DstDiophantine
