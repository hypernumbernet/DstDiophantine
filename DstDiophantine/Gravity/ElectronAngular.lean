import DstDiophantine.Gravity.ElectronShape
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Angular momentum of a directional seat

## Paper boundary (do **not** claim)

The degree of a pattern is not an index of an equal-scale node, and it is not
a Bohr radius. Nothing here is a fine-structure splitting, a spin-orbit term,
or a value of `ℓ`. The length `ℓ` stays an external scale.

## What is proved

The square of the angular momentum is the response of a directional pattern
when the direction is turned: minus the sum of the squares of the three
infinitesimal rotations of that pattern. On a constant pattern that square is
`0`. On a dipole it is `2` times the pattern. On a traceless quadrupole it is
`6` times the pattern. On a traceless octupole it is `12` times the pattern.
These are the products of the degree with one more than the degree. The
circular path in the outer well is the travel of the electron and leaves this
square as the degree fixes it.

A monopole, a dipole, a traceless quadrupole, and a traceless octupole have
dimensions `1`, `3`, `5`, and `7`, one more than twice the degree. The running
total of both rays through degree `n - 1` is `2 n²` for `n = 1, 2, 3, 4`.
-/

namespace DstDiophantine

namespace Gravity

open Matrix

/-! ### Monopole: every partial vanishes, so the square is zero -/

theorem mono_shift (s : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    monoValue s (fun k => v k + if k = i then t else 0) = monoValue s v := by
  simp [monoValue]

/-- Each infinitesimal rotation of a constant pattern is the zero function, so
the sum of their squares is zero. -/
theorem angSq_monopole (s : ℝ) (v : Fin 3 → ℝ) :
    -((v 0 * (0 : ℝ) - v 1 * 0) + (v 0 * 0 - v 2 * 0) + (v 1 * 0 - v 2 * 0)) =
      (0 * 1) * monoValue s v := by
  simp [monoValue]

/-! ### Dipole -/

/-- Infinitesimal rotation in the coordinate plane `(i, j)`, on a linear form. -/
def jDip (i j : Fin 3) (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => if k = i then a j else if k = j then -a i else 0

theorem jDip_01_eval (a v : Fin 3 → ℝ) :
    dipoleValue (jDip 0 1 a) v = v 0 * a 1 - v 1 * a 0 := by
  rw [dipoleValue_expand]
  simp [jDip]
  ring

theorem jDip_02_eval (a v : Fin 3 → ℝ) :
    dipoleValue (jDip 0 2 a) v = v 0 * a 2 - v 2 * a 0 := by
  rw [dipoleValue_expand]
  simp [jDip]
  ring

theorem jDip_12_eval (a v : Fin 3 → ℝ) :
    dipoleValue (jDip 1 2 a) v = v 1 * a 2 - v 2 * a 1 := by
  rw [dipoleValue_expand]
  simp [jDip]
  ring

private theorem jDip_sq_01 (a : Fin 3 → ℝ) :
    jDip 0 1 (jDip 0 1 a) = fun k => if k = 0 then -a 0 else if k = 1 then -a 1 else 0 := by
  ext k
  fin_cases k <;> simp [jDip]

private theorem jDip_sq_02 (a : Fin 3 → ℝ) :
    jDip 0 2 (jDip 0 2 a) = fun k => if k = 0 then -a 0 else if k = 2 then -a 2 else 0 := by
  ext k
  fin_cases k <;> simp [jDip]

private theorem jDip_sq_12 (a : Fin 3 → ℝ) :
    jDip 1 2 (jDip 1 2 a) = fun k => if k = 1 then -a 1 else if k = 2 then -a 2 else 0 := by
  ext k
  fin_cases k <;> simp [jDip]

theorem angSq_dipole (a v : Fin 3 → ℝ) :
    -(dipoleValue (jDip 0 1 (jDip 0 1 a)) v + dipoleValue (jDip 0 2 (jDip 0 2 a)) v +
        dipoleValue (jDip 1 2 (jDip 1 2 a)) v) =
      (1 * 2) * dipoleValue a v := by
  have h01 : dipoleValue (fun k => if k = 0 then -a 0 else if k = 1 then -a 1 else 0) v =
      -(a 0 * v 0) + -(a 1 * v 1) := by
    rw [dipoleValue_expand]
    simp
  have h02 : dipoleValue (fun k => if k = 0 then -a 0 else if k = 2 then -a 2 else 0) v =
      -(a 0 * v 0) + -(a 2 * v 2) := by
    rw [dipoleValue_expand]
    simp
  have h12 : dipoleValue (fun k => if k = 1 then -a 1 else if k = 2 then -a 2 else 0) v =
      -(a 1 * v 1) + -(a 2 * v 2) := by
    rw [dipoleValue_expand]
    simp
  rw [jDip_sq_01, jDip_sq_02, jDip_sq_12, h01, h02, h12, dipoleValue_expand]
  ring

/-! ### Quadrupole

A homogeneous quadratic is stored as `x²`, `y²`, `z²`, `xy`, `xz`, `yz`.
For a symmetric matrix the cross coefficients are twice the off-diagonal entries.
-/

def quadPoly (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  c 0 * v 0 ^ 2 + c 1 * v 1 ^ 2 + c 2 * v 2 ^ 2 +
    c 3 * v 0 * v 1 + c 4 * v 0 * v 2 + c 5 * v 1 * v 2

def jQuadXY (c : Fin 6 → ℝ) : Fin 6 → ℝ
  | 0 => c 3
  | 1 => -c 3
  | 2 => 0
  | 3 => -2 * c 0 + 2 * c 1
  | 4 => c 5
  | 5 => -c 4

def jQuadXZ (c : Fin 6 → ℝ) : Fin 6 → ℝ
  | 0 => c 4
  | 1 => 0
  | 2 => -c 4
  | 3 => c 5
  | 4 => -2 * c 0 + 2 * c 2
  | 5 => -c 3

def jQuadYZ (c : Fin 6 → ℝ) : Fin 6 → ℝ
  | 0 => 0
  | 1 => c 5
  | 2 => -c 5
  | 3 => c 4
  | 4 => -c 3
  | 5 => -2 * c 1 + 2 * c 2

def dQuadX (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  2 * c 0 * v 0 + c 3 * v 1 + c 4 * v 2

def dQuadY (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  2 * c 1 * v 1 + c 3 * v 0 + c 5 * v 2

def dQuadZ (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  2 * c 2 * v 2 + c 4 * v 0 + c 5 * v 1

theorem quad_shift_x (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) (t : ℝ) :
    quadPoly c (fun i => if i = 0 then v 0 + t else v i) =
      quadPoly c v + t * dQuadX c v + t ^ 2 * c 0 := by
  unfold quadPoly dQuadX
  simp
  ring

theorem quad_shift_y (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) (t : ℝ) :
    quadPoly c (fun i => if i = 1 then v 1 + t else v i) =
      quadPoly c v + t * dQuadY c v + t ^ 2 * c 1 := by
  unfold quadPoly dQuadY
  simp
  ring

theorem quad_shift_z (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) (t : ℝ) :
    quadPoly c (fun i => if i = 2 then v 2 + t else v i) =
      quadPoly c v + t * dQuadZ c v + t ^ 2 * c 2 := by
  unfold quadPoly dQuadZ
  simp
  ring

theorem jQuadXY_eval (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) :
    quadPoly (jQuadXY c) v = v 0 * dQuadY c v - v 1 * dQuadX c v := by
  unfold quadPoly jQuadXY dQuadY dQuadX
  ring

theorem jQuadXZ_eval (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) :
    quadPoly (jQuadXZ c) v = v 0 * dQuadZ c v - v 2 * dQuadX c v := by
  unfold quadPoly jQuadXZ dQuadZ dQuadX
  ring

theorem jQuadYZ_eval (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) :
    quadPoly (jQuadYZ c) v = v 1 * dQuadZ c v - v 2 * dQuadY c v := by
  unfold quadPoly jQuadYZ dQuadZ dQuadY
  ring

/-- Sum of the three squared rotations on a homogeneous quadratic.
On the diagonal coefficients the trace term remains; the cross coefficients
are pure. -/
def quadGenSq (c : Fin 6 → ℝ) : Fin 6 → ℝ
  | 0 => -6 * c 0 + 2 * (c 0 + c 1 + c 2)
  | 1 => -6 * c 1 + 2 * (c 0 + c 1 + c 2)
  | 2 => -6 * c 2 + 2 * (c 0 + c 1 + c 2)
  | 3 => -6 * c 3
  | 4 => -6 * c 4
  | 5 => -6 * c 5

theorem genSq_quad (c : Fin 6 → ℝ) :
    (fun i => jQuadXY (jQuadXY c) i + jQuadXZ (jQuadXZ c) i + jQuadYZ (jQuadYZ c) i) =
      quadGenSq c := by
  ext i
  fin_cases i <;> simp [jQuadXY, jQuadXZ, jQuadYZ, quadGenSq] <;> ring

theorem angSq_quadPoly (c : Fin 6 → ℝ) (v : Fin 3 → ℝ) :
    -(quadPoly (jQuadXY (jQuadXY c)) v + quadPoly (jQuadXZ (jQuadXZ c)) v +
        quadPoly (jQuadYZ (jQuadYZ c)) v) =
      (2 * 3) * quadPoly c v - 2 * (c 0 + c 1 + c 2) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  have hlin : quadPoly (fun i =>
      jQuadXY (jQuadXY c) i + jQuadXZ (jQuadXZ c) i + jQuadYZ (jQuadYZ c) i) v =
      quadPoly (jQuadXY (jQuadXY c)) v + quadPoly (jQuadXZ (jQuadXZ c)) v +
        quadPoly (jQuadYZ (jQuadYZ c)) v := by
    unfold quadPoly
    ring
  rw [← hlin, genSq_quad]
  unfold quadPoly quadGenSq
  ring

def quadCoeff (M : Matrix (Fin 3) (Fin 3) ℝ) : Fin 6 → ℝ
  | 0 => M 0 0
  | 1 => M 1 1
  | 2 => M 2 2
  | 3 => M 0 1 + M 1 0
  | 4 => M 0 2 + M 2 0
  | 5 => M 1 2 + M 2 1

theorem quadCoeff_eval (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    quadValue M v = quadPoly (quadCoeff M) v := by
  rw [quadValue_expand]
  simp [quadPoly, quadCoeff]

theorem angSq_quadrupole {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ quadrupole)
    (v : Fin 3 → ℝ) :
    -(quadPoly (jQuadXY (jQuadXY (quadCoeff M))) v +
        quadPoly (jQuadXZ (jQuadXZ (quadCoeff M))) v +
        quadPoly (jQuadYZ (jQuadYZ (quadCoeff M))) v) =
      (2 * 3) * quadValue M v := by
  have htr : quadCoeff M 0 + quadCoeff M 1 + quadCoeff M 2 = 0 := by
    simpa [quadCoeff, Matrix.trace, Fin.sum_univ_three] using hM.2
  have hpoly := angSq_quadPoly (quadCoeff M) v
  rw [quadCoeff_eval M v]
  simpa [htr] using hpoly

/-! ### Octupole -/

def dOctuX (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  3 * c 0 * v 0 ^ 2 + 2 * c 3 * v 0 * v 1 + 2 * c 4 * v 0 * v 2 +
    c 5 * v 1 ^ 2 + c 7 * v 2 ^ 2 + c 9 * v 1 * v 2

def dOctuY (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  3 * c 1 * v 1 ^ 2 + c 3 * v 0 ^ 2 + 2 * c 5 * v 0 * v 1 + 2 * c 6 * v 1 * v 2 +
    c 8 * v 2 ^ 2 + c 9 * v 0 * v 2

def dOctuZ (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  3 * c 2 * v 2 ^ 2 + c 4 * v 0 ^ 2 + c 6 * v 1 ^ 2 + 2 * c 7 * v 0 * v 2 +
    2 * c 8 * v 1 * v 2 + c 9 * v 0 * v 1

theorem octu_shift_x (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) (t : ℝ) :
    octuValue c (fun i => if i = 0 then v 0 + t else v i) =
      octuValue c v + t * dOctuX c v +
        t ^ 2 * (3 * c 0 * v 0 + c 3 * v 1 + c 4 * v 2) + t ^ 3 * c 0 := by
  unfold octuValue dOctuX
  simp
  ring

theorem octu_shift_y (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) (t : ℝ) :
    octuValue c (fun i => if i = 1 then v 1 + t else v i) =
      octuValue c v + t * dOctuY c v +
        t ^ 2 * (3 * c 1 * v 1 + c 5 * v 0 + c 6 * v 2) + t ^ 3 * c 1 := by
  unfold octuValue dOctuY
  simp
  ring

theorem octu_shift_z (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) (t : ℝ) :
    octuValue c (fun i => if i = 2 then v 2 + t else v i) =
      octuValue c v + t * dOctuZ c v +
        t ^ 2 * (3 * c 2 * v 2 + c 7 * v 0 + c 8 * v 1) + t ^ 3 * c 2 := by
  unfold octuValue dOctuZ
  simp
  ring

/-- `x ∂_y - y ∂_x` on the ten cubic monomials. -/
def jOctuXY (c : Fin 10 → ℝ) : Fin 10 → ℝ
  | 0 => c 3
  | 1 => -c 5
  | 2 => 0
  | 3 => -3 * c 0 + 2 * c 5
  | 4 => c 9
  | 5 => 3 * c 1 - 2 * c 3
  | 6 => -c 9
  | 7 => c 8
  | 8 => -c 7
  | 9 => -2 * c 4 + 2 * c 6

/-- `x ∂_z - z ∂_x`. -/
def jOctuXZ (c : Fin 10 → ℝ) : Fin 10 → ℝ
  | 0 => c 4
  | 1 => 0
  | 2 => -c 7
  | 3 => c 9
  | 4 => -3 * c 0 + 2 * c 7
  | 5 => c 6
  | 6 => -c 5
  | 7 => 3 * c 2 - 2 * c 4
  | 8 => -c 9
  | 9 => -2 * c 3 + 2 * c 8

/-- `y ∂_z - z ∂_y`. -/
def jOctuYZ (c : Fin 10 → ℝ) : Fin 10 → ℝ
  | 0 => 0
  | 1 => c 6
  | 2 => -c 8
  | 3 => c 4
  | 4 => -c 3
  | 5 => c 9
  | 6 => -3 * c 1 + 2 * c 8
  | 7 => -c 9
  | 8 => 3 * c 2 - 2 * c 6
  | 9 => -2 * c 5 + 2 * c 7

theorem jOctuXY_eval (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) :
    octuValue (jOctuXY c) v = v 0 * dOctuY c v - v 1 * dOctuX c v := by
  unfold octuValue jOctuXY dOctuY dOctuX
  ring

theorem jOctuXZ_eval (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) :
    octuValue (jOctuXZ c) v = v 0 * dOctuZ c v - v 2 * dOctuX c v := by
  unfold octuValue jOctuXZ dOctuZ dOctuX
  ring

theorem jOctuYZ_eval (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) :
    octuValue (jOctuYZ c) v = v 1 * dOctuZ c v - v 2 * dOctuY c v := by
  unfold octuValue jOctuYZ dOctuZ dOctuY
  ring

def octuRad (c : Fin 10 → ℝ) : Fin 10 → ℝ
  | 0 => 3 * c 0 + c 5 + c 7
  | 1 => 3 * c 1 + c 3 + c 8
  | 2 => 3 * c 2 + c 4 + c 6
  | 3 => 3 * c 1 + c 3 + c 8
  | 4 => 3 * c 2 + c 4 + c 6
  | 5 => 3 * c 0 + c 5 + c 7
  | 6 => 3 * c 2 + c 4 + c 6
  | 7 => 3 * c 0 + c 5 + c 7
  | 8 => 3 * c 1 + c 3 + c 8
  | 9 => 0

theorem genSq_octu (c : Fin 10 → ℝ) :
    (fun i => jOctuXY (jOctuXY c) i + jOctuXZ (jOctuXZ c) i + jOctuYZ (jOctuYZ c) i) =
      fun i => -12 * c i + 2 * octuRad c i := by
  ext i
  fin_cases i <;> simp [jOctuXY, jOctuXZ, jOctuYZ, octuRad] <;> ring

theorem octuRad_mem {c : Fin 10 → ℝ} (hc : c ∈ octupole) : octuRad c = 0 := by
  have h0 : octuTrace c 0 = 0 := congr_fun hc 0
  have h1 : octuTrace c 1 = 0 := congr_fun hc 1
  have h2 : octuTrace c 2 = 0 := congr_fun hc 2
  ext i
  fin_cases i <;> simp [octuRad, octuTrace] at h0 h1 h2 ⊢ <;> linarith

theorem angSq_octupole {c : Fin 10 → ℝ} (hc : c ∈ octupole) (v : Fin 3 → ℝ) :
    -(octuValue (jOctuXY (jOctuXY c)) v + octuValue (jOctuXZ (jOctuXZ c)) v +
        octuValue (jOctuYZ (jOctuYZ c)) v) =
      (3 * 4) * octuValue c v := by
  have h := congr_fun (genSq_octu c)
  have hlin :
      octuValue (fun i =>
        jOctuXY (jOctuXY c) i + jOctuXZ (jOctuXZ c) i + jOctuYZ (jOctuYZ c) i) v =
      octuValue (jOctuXY (jOctuXY c)) v + octuValue (jOctuXZ (jOctuXZ c)) v +
        octuValue (jOctuYZ (jOctuYZ c)) v := by
    unfold octuValue
    ring
  rw [← hlin]
  have hrad : octuRad c = 0 := octuRad_mem hc
  simp only [h, hrad, Pi.zero_apply, mul_zero, add_zero]
  unfold octuValue
  ring

/-! ### Capacities -/

theorem mode_rank_degree :
    Module.finrank ℝ ℝ = 2 * 0 + 1 ∧
      Module.finrank ℝ (Fin 3 → ℝ) = 2 * 1 + 1 ∧
      Module.finrank ℝ quadrupole = 2 * 2 + 1 ∧
      Module.finrank ℝ octupole = 2 * 3 + 1 := by
  have h3 : Module.finrank ℝ (Fin 3 → ℝ) = 3 :=
    (Module.finrank_fin_fun ℝ : Module.finrank ℝ (Fin 3 → ℝ) = 3)
  simp [h3, quadrupole_rank, octupole_rank]

theorem shell_capacity_two_n_sq :
    2 * Module.finrank ℝ ℝ = 2 * 1 ^ 2 ∧
      2 * (Module.finrank ℝ ℝ + Module.finrank ℝ (Fin 3 → ℝ)) = 2 * 2 ^ 2 ∧
      2 * (Module.finrank ℝ ℝ + Module.finrank ℝ (Fin 3 → ℝ) +
        Module.finrank ℝ quadrupole) = 2 * 3 ^ 2 ∧
      2 * (Module.finrank ℝ ℝ + Module.finrank ℝ (Fin 3 → ℝ) +
        Module.finrank ℝ quadrupole + Module.finrank ℝ octupole) = 2 * 4 ^ 2 := by
  have h3 : Module.finrank ℝ (Fin 3 → ℝ) = 3 :=
    (Module.finrank_fin_fun ℝ : Module.finrank ℝ (Fin 3 → ℝ) = 3)
  simp [h3, quadrupole_rank, octupole_rank]

end Gravity

end DstDiophantine
