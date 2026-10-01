import DstDiophantine.Gravity.DualRotorMotor
import DstDiophantine.Gravity.KillingAxis

/-!
# The parabolic rotor is a null rotation

Off a common axis, `B⁺₀ + B⁻₁` squares to zero and lies in the Lorentz span,
complementary to the null ideal. Its exponential therefore truncates. The
truncations multiply by adding the parameter, the opposite parameter is the
reverse, and the sandwich preserves the Minkowski product. For a nonzero
parameter the fixed vectors are the span of `e₀ - e₃` and `e₂`. The same
coefficients act on the null ideal, because `e₄` commutes with the Lorentz
span: `N(x)` is sent to `N(Λₜ x)`. A translator `1 + s N₁` sends `e₁` to
`e₁ + s e₄`.
-/

namespace DstDiophantine

namespace Gravity

open CliffordAlgebra (reverse)
open PGA Generators Motor Operations Sandwich BivectorBasis LorentzLie

/-- Lightlike Lorentz generator `B⁺₀ + B⁻₁`. -/
noncomputable def parabolicGen : PGA :=
  hyperbolic 0 + cyclic 1

/-- Truncated null rotation `1 + t(B⁺₀ + B⁻₁)`. -/
noncomputable def parabolicRotor (t : ℝ) : PGA :=
  (1 : PGA) + t • parabolicGen

/-- Coordinates of the fixed null line `e₀ - e₃`. -/
def nullLineVec : Fin 4 → ℝ := ![1, 0, 0, -1]

/-- Coordinates of the fixed transverse axis `e₂`. -/
def transverseVec : Fin 4 → ℝ := ![0, 0, 1, 0]

/-- Translational bivector with Minkowski coefficients `x`. -/
noncomputable def nullVector (x : Fin 4 → ℝ) : PGA :=
  ι e4Index * minkowskiVector x

/-- Half-angle parameters whose torsion bivector is `parabolicGen`. -/
def parabolicParams : Operations.TorsionParams where
  alpha := fun a => if a = 0 then 2 else 0
  beta := fun a => if a = 1 then 2 else 0

theorem parabolicGen_sq : parabolicGen * parabolicGen = 0 := by
  simpa [parabolicGen] using
    offAxis_scaled_sq (by decide : (0 : Fin 3) ≠ 1) (1 : ℝ) (1 : ℝ)

theorem omegaTorsion_parabolicParams : omegaTorsion parabolicParams = parabolicGen := by
  rw [omegaTorsion, Fin.sum_univ_three, parabolicGen]
  simp [parabolicParams, one_smul, zero_smul, add_zero, zero_add]

theorem parabolicGen_mem_lorentzSpan : parabolicGen ∈ lorentzSpan :=
  Submodule.add_mem _ (hyperbolic_mem_lorentzSpan 0) (cyclic_mem_lorentzSpan 1)

theorem parabolicGen_ne_zero : parabolicGen ≠ 0 := by
  intro h
  let f : Fin 3 → ℝ := fun a => if a = 0 then 1 else 0
  let g : Fin 3 → ℝ := fun a => if a = 1 then 1 else 0
  have hsum :
      (∑ a : Fin 3, f a • hyperbolic a) + (∑ a : Fin 3, g a • cyclic a) = 0 := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simpa [f, g, parabolicGen] using h
  have hg := (sum_elim_hyperbolic_cyclic_eq_zero hsum).2 1
  simp [g] at hg

theorem parabolicGen_not_mem_nullSpan : parabolicGen ∉ nullSpan := by
  intro h
  have hbot : parabolicGen ∈ (⊥ : Submodule ℝ PGA) :=
    (Submodule.disjoint_def.mp disjoint_lorentz_null) parabolicGen
      parabolicGen_mem_lorentzSpan h
  rw [Submodule.mem_bot] at hbot
  exact parabolicGen_ne_zero hbot

/-- Null rotation of a Minkowski coordinate vector. -/
def nullRotation (t : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![x 0 + 2 * t * x 1 + 2 * t ^ 2 * (x 0 + x 3),
    x 1 + 2 * t * (x 0 + x 3),
    x 2,
    x 3 - 2 * t * x 1 - 2 * t ^ 2 * (x 0 + x 3)]

@[simp] private theorem fin4_apply_zero (x : Fin 4 → ℝ) : Matrix.vecHead x = x 0 := rfl

@[simp] private theorem fin4_apply_one (x : Fin 4 → ℝ) :
    Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl

@[simp] private theorem fin4_apply_two (x : Fin 4 → ℝ) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail x)) = x 2 := rfl

@[simp] private theorem fin4_apply_three (x : Fin 4 → ℝ) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail x))) = x 3 := rfl

theorem nullRotation_eq_series (t : ℝ) (x : Fin 4 → ℝ) :
    nullRotation t x =
      x + t • KillingAxis.lorentzAct parabolicParams x +
        (t ^ 2 / 2) • KillingAxis.lorentzAct parabolicParams
          (KillingAxis.lorentzAct parabolicParams x) := by
  funext i
  fin_cases i
  · suffices x 0 + 2 * t * x 1 + 2 * t ^ 2 * (x 0 + x 3) =
        x 0 + t * (2 * x 1) + t ^ 2 / 2 * (2 * (2 * x 0 + 2 * x 3)) by
      simpa [nullRotation, Pi.add_apply, Pi.smul_apply, KillingAxis.lorentzAct,
        parabolicParams] using this
    ring
  · suffices x 1 + 2 * t * (x 0 + x 3) =
        x 1 + t * (2 * x 0 + 2 * x 3) by
      simpa [nullRotation, Pi.add_apply, Pi.smul_apply, KillingAxis.lorentzAct,
        parabolicParams] using this
    ring
  · simp [nullRotation, Pi.add_apply, KillingAxis.lorentzAct, parabolicParams]
  · suffices x 3 - 2 * t * x 1 - 2 * t ^ 2 * (x 0 + x 3) =
        x 3 + -(t * (2 * x 1)) + -(t ^ 2 / 2 * (2 * (2 * x 0 + 2 * x 3))) by
      simpa [nullRotation, Pi.add_apply, Pi.smul_apply, KillingAxis.lorentzAct,
        parabolicParams] using this
    ring

private theorem minkowskiVector_smul (c : ℝ) (x : Fin 4 → ℝ) :
    minkowskiVector (c • x) = c • minkowskiVector x := by
  simp [minkowskiVector_eq_sum, Finset.smul_sum, smul_smul]

private theorem commutator_commutator_of_sq_zero {K v : PGA} (hK : K * K = 0) :
    Generators.commutator K (Generators.commutator K v) =
      -((2 : ℝ) • (K * v * K)) := by
  rw [Generators.commutator, Generators.commutator]
  have h1 : K * (K * v - v * K) = K * (K * v) - K * (v * K) := mul_sub _ _ _
  have h2 : (K * v - v * K) * K = (K * v) * K - (v * K) * K := sub_mul _ _ _
  rw [h1, h2]
  rw [show K * (K * v) = K * K * v from (mul_assoc K K v).symm]
  rw [show K * (v * K) = K * v * K from (mul_assoc K v K).symm]
  rw [show (v * K) * K = v * (K * K) from mul_assoc v K K]
  rw [hK, zero_mul, mul_zero]
  module

private theorem reverse_parabolicGen : reverse parabolicGen = -parabolicGen := by
  rw [parabolicGen, map_add, hyperbolic_reverse, cyclic_reverse, neg_add]

private theorem sandwich_one_add_nilpotent {K v : PGA} (hK : K * K = 0)
    (hrev : reverse K = -K) (t : ℝ) :
    sandwich ((1 : PGA) + t • K) v =
      v + t • Generators.commutator K v +
        (t ^ 2 / 2) • Generators.commutator K (Generators.commutator K v) := by
  have hrevM : reverse ((1 : PGA) + t • K) = (1 : PGA) + (-t) • K := by
    rw [map_add, reverse.map_one, map_smul, hrev, smul_neg, neg_smul]
  rw [sandwich, hrevM]
  have hquad : (t • K) * v * ((-t) • K) = (-(t ^ 2)) • (K * v * K) := by
    calc
      (t • K) * v * ((-t) • K) = (t • (K * v)) * ((-t) • K) := by
        rw [smul_mul_assoc]
      _ = t • ((K * v) * ((-t) • K)) := by
        rw [smul_mul_assoc]
      _ = t • ((-t) • ((K * v) * K)) := by
        rw [mul_smul_comm]
      _ = (t * -t) • (K * v * K) := by
        rw [smul_smul]
      _ = (-(t ^ 2)) • (K * v * K) := by
        congr 1
        ring
  have hexpand :
      ((1 : PGA) + t • K) * v * ((1 : PGA) + (-t) • K) =
        v + (-t) • (v * K) + t • (K * v) + (t • K) * v * ((-t) • K) := by
    have hstep1 : ((1 : PGA) + t • K) * v = v + (t • K) * v := by
      rw [add_mul, one_mul]
    rw [hstep1, mul_add, mul_one, add_mul]
    rw [smul_mul_assoc, mul_smul_comm]
    abel
  rw [hexpand, hquad]
  have hcomm : (-t) • (v * K) + t • (K * v) = t • Generators.commutator K v := by
    rw [Generators.commutator, smul_sub, sub_eq_add_neg, ← neg_smul, add_comm]
  have hKvK : (t ^ 2) • (K * v * K) =
      -((t ^ 2 / 2) • Generators.commutator K (Generators.commutator K v)) := by
    have htwo : (2 : ℝ) • (K * v * K) =
        -Generators.commutator K (Generators.commutator K v) := by
      rw [commutator_commutator_of_sq_zero hK, neg_neg]
    calc
      (t ^ 2) • (K * v * K) = (t ^ 2 / 2) • ((2 : ℝ) • (K * v * K)) := by
        rw [smul_smul]
        congr 1
        ring
      _ = (t ^ 2 / 2) •
          (-Generators.commutator K (Generators.commutator K v)) := by
        rw [htwo]
      _ = -((t ^ 2 / 2) • Generators.commutator K (Generators.commutator K v)) := by
        rw [smul_neg]
  have hrest : (-(t ^ 2)) • (K * v * K) =
      (t ^ 2 / 2) • Generators.commutator K (Generators.commutator K v) := by
    rw [neg_smul, hKvK, neg_neg]
  calc
    v + (-t) • (v * K) + t • (K * v) + (-(t ^ 2)) • (K * v * K)
        = v + ((-t) • (v * K) + t • (K * v)) + (-(t ^ 2)) • (K * v * K) := by
          abel
    _ = v + t • Generators.commutator K v +
          (t ^ 2 / 2) • Generators.commutator K (Generators.commutator K v) := by
          rw [hcomm, hrest]

/-- The parabolic rotor acts on Minkowski vectors by the null rotation. -/
theorem sandwich_parabolic_minkowski (t : ℝ) (x : Fin 4 → ℝ) :
    sandwich ((1 : PGA) + t • parabolicGen) (minkowskiVector x) =
      minkowskiVector (nullRotation t x) := by
  rw [sandwich_one_add_nilpotent parabolicGen_sq reverse_parabolicGen]
  have h1 : Generators.commutator parabolicGen (minkowskiVector x) =
      minkowskiVector (KillingAxis.lorentzAct parabolicParams x) := by
    rw [← omegaTorsion_parabolicParams]
    exact KillingAxis.commutator_omegaTorsion_minkowskiVector parabolicParams x
  have h2 : Generators.commutator parabolicGen
        (minkowskiVector (KillingAxis.lorentzAct parabolicParams x)) =
      minkowskiVector (KillingAxis.lorentzAct parabolicParams
        (KillingAxis.lorentzAct parabolicParams x)) := by
    rw [← omegaTorsion_parabolicParams]
    exact KillingAxis.commutator_omegaTorsion_minkowskiVector parabolicParams _
  rw [h1, h2, nullRotation_eq_series, KillingAxis.minkowskiVector_add,
    KillingAxis.minkowskiVector_add, minkowskiVector_smul, minkowskiVector_smul]

theorem sandwich_parabolic_e1 (t : ℝ) :
    sandwich ((1 : PGA) + t • parabolicGen) (ι 1) =
      (2 * t) • ι 0 + ι 1 - (2 * t) • ι 3 := by
  have h := sandwich_parabolic_minkowski t ![0, 1, 0, 0]
  have hv : minkowskiVector ![0, 1, 0, 0] = ι 1 := by
    simpa using KillingAxis.minkowskiVector_vec 0 1 0 0
  have hrot : nullRotation t ![0, 1, 0, 0] = ![2 * t, 1, 0, -(2 * t)] := by
    funext i
    fin_cases i <;> simp [nullRotation]
  rw [hv] at h
  rw [h, hrot]
  have himg := KillingAxis.minkowskiVector_vec (2 * t) 1 0 (-(2 * t))
  rw [himg]
  module

/-- The shear of `e₁`, written along the fixed null line. -/
theorem sandwich_parabolic_e1_shear (t : ℝ) :
    sandwich ((1 : PGA) + t • parabolicGen) (ι 1) =
      ι 1 + (2 * t) • (ι 0 - ι 3) := by
  rw [sandwich_parabolic_e1]
  module

theorem sandwich_parabolic_e2 (t : ℝ) :
    sandwich ((1 : PGA) + t • parabolicGen) (ι 2) = ι 2 := by
  have h := sandwich_parabolic_minkowski t ![0, 0, 1, 0]
  have hv : minkowskiVector ![0, 0, 1, 0] = ι 2 := by
    simpa using KillingAxis.minkowskiVector_vec 0 0 1 0
  have hrot : nullRotation t ![0, 0, 1, 0] = ![0, 0, 1, 0] := by
    funext i
    fin_cases i <;> simp [nullRotation]
  rw [hv] at h
  rw [h, hrot, hv]

theorem sandwich_parabolic_fixedNull (t : ℝ) :
    sandwich ((1 : PGA) + t • parabolicGen) (ι 0 - ι 3) = ι 0 - ι 3 := by
  have h := sandwich_parabolic_minkowski t ![1, 0, 0, -1]
  have hv : minkowskiVector ![1, 0, 0, -1] = ι 0 - ι 3 := by
    have hvec := KillingAxis.minkowskiVector_vec (1 : ℝ) 0 0 (-1)
    rw [hvec]
    module
  have hrot : nullRotation t ![1, 0, 0, -1] = ![1, 0, 0, -1] := by
    funext i
    fin_cases i <;> simp [nullRotation]
  rw [hv] at h
  rw [h, hrot, hv]

theorem sandwich_parabolic_nullPlus (t : ℝ) :
    sandwich ((1 : PGA) + t • parabolicGen) (ι 0 + ι 3) =
      (1 + 4 * t ^ 2) • ι 0 + (4 * t) • ι 1 + (1 - 4 * t ^ 2) • ι 3 := by
  have h := sandwich_parabolic_minkowski t ![1, 0, 0, 1]
  have hv : minkowskiVector ![1, 0, 0, 1] = ι 0 + ι 3 := by
    have hvec := KillingAxis.minkowskiVector_vec (1 : ℝ) 0 0 1
    rw [hvec]
    module
  have hrot : nullRotation t ![1, 0, 0, 1] =
      ![1 + 4 * t ^ 2, 4 * t, 0, 1 - 4 * t ^ 2] := by
    funext i
    fin_cases i <;> simp [nullRotation] <;> ring
  rw [hv] at h
  rw [h, hrot]
  have himg := KillingAxis.minkowskiVector_vec (1 + 4 * t ^ 2) (4 * t) 0 (1 - 4 * t ^ 2)
  rw [himg]
  module

/-- The shear of the complementary null vector `e₀ + e₃`. -/
theorem sandwich_parabolic_nullPlus_shear (t : ℝ) :
    sandwich ((1 : PGA) + t • parabolicGen) (ι 0 + ι 3) =
      ι 0 + ι 3 + (4 * t) • ι 1 + (4 * t ^ 2) • (ι 0 - ι 3) := by
  rw [sandwich_parabolic_nullPlus]
  module

/-- A translator along `e₁` adds `e₄`. -/
theorem sandwich_translator_e1 (s : ℝ) :
    sandwich (expTrans ⟨![0, s, 0, 0]⟩) (ι 1) = ι 1 + s • ι e4Index := by
  have hcast : (Fin.castAdd 1 (1 : Fin 4) : Fin 5) = 1 := rfl
  have h := KillingAxis.sandwich_expTrans_ι ⟨![0, s, 0, 0]⟩ 1
  simp only [hcast, w31] at h
  have hvec : ![0, s, 0, 0] (1 : Fin 4) = s := by simp
  rw [hvec] at h
  simpa using h

/-! ### The truncations form a one-parameter group of isometries -/

theorem parabolicRotor_mul (t s : ℝ) :
    parabolicRotor t * parabolicRotor s = parabolicRotor (t + s) := by
  unfold parabolicRotor
  have hsq : (t • parabolicGen) * (s • parabolicGen) = 0 := by
    rw [smul_mul_smul_comm, parabolicGen_sq, smul_zero]
  calc
    ((1 : PGA) + t • parabolicGen) * ((1 : PGA) + s • parabolicGen)
        = (1 : PGA) * ((1 : PGA) + s • parabolicGen) +
            (t • parabolicGen) * ((1 : PGA) + s • parabolicGen) := by
          rw [add_mul]
    _ = ((1 : PGA) + s • parabolicGen) +
          ((t • parabolicGen) * (1 : PGA) + (t • parabolicGen) * (s • parabolicGen)) := by
          rw [one_mul, mul_add]
    _ = (1 : PGA) + s • parabolicGen + t • parabolicGen +
          (t • parabolicGen) * (s • parabolicGen) := by
          rw [mul_one]
          abel
    _ = (1 : PGA) + (t + s) • parabolicGen := by
          rw [hsq, add_zero]
          module

theorem reverse_parabolicRotor (t : ℝ) :
    reverse (parabolicRotor t) = parabolicRotor (-t) := by
  rw [parabolicRotor, parabolicRotor, map_add, reverse.map_one, map_smul, reverse_parabolicGen,
    smul_neg, neg_smul]

theorem parabolicRotor_mul_reverse (t : ℝ) :
    parabolicRotor t * reverse (parabolicRotor t) = 1 := by
  rw [reverse_parabolicRotor, parabolicRotor_mul, add_neg_cancel]
  simp [parabolicRotor]

/-- The third adjoint of the nilpotent generator vanishes. -/
theorem adjoint_parabolic_cube (v : PGA) :
    Generators.commutator parabolicGen
        (Generators.commutator parabolicGen (Generators.commutator parabolicGen v)) = 0 := by
  have hdouble :
      Generators.commutator parabolicGen (Generators.commutator parabolicGen v) =
        (-2 : ℝ) • (parabolicGen * v * parabolicGen) := by
    rw [commutator_commutator_of_sq_zero parabolicGen_sq, neg_smul]
  rw [hdouble, Generators.commutator_smul_right, Generators.commutator]
  have hleft : parabolicGen * (parabolicGen * v * parabolicGen) = 0 := by
    rw [show parabolicGen * (parabolicGen * v * parabolicGen) =
        (parabolicGen * parabolicGen) * v * parabolicGen by simp [mul_assoc],
      parabolicGen_sq, zero_mul, zero_mul]
  have hright : (parabolicGen * v * parabolicGen) * parabolicGen = 0 := by
    rw [show (parabolicGen * v * parabolicGen) * parabolicGen =
        parabolicGen * v * (parabolicGen * parabolicGen) by simp [mul_assoc],
      parabolicGen_sq, mul_zero]
  simp [hleft, hright]

theorem nullRotation_add (t : ℝ) (x y : Fin 4 → ℝ) :
    nullRotation t (x + y) = nullRotation t x + nullRotation t y := by
  funext i
  fin_cases i <;> simp [nullRotation, Pi.add_apply] <;> ring

theorem nullRotation_smul (t c : ℝ) (x : Fin 4 → ℝ) :
    nullRotation t (c • x) = c • nullRotation t x := by
  funext i
  fin_cases i <;> simp [nullRotation, Pi.smul_apply] <;> ring

/-- The null rotation preserves Minkowski squares. -/
theorem Q31_nullRotation (t : ℝ) (x : Fin 4 → ℝ) : Q31 (nullRotation t x) = Q31 x := by
  have hsq := sandwich_minkowskiVector_sq (parabolicRotor_mul_reverse t) x
  rw [parabolicRotor, sandwich_parabolic_minkowski t x, minkowskiVector_sq] at hsq
  exact FaithfulSMul.algebraMap_injective (R := ℝ) (A := PGA) hsq

private theorem minkowskiProd_polar (x y : Fin 4 → ℝ) :
    KillingAxis.minkowskiProd x y = (1 / 2) * (Q31 (x + y) - Q31 x - Q31 y) := by
  simp only [KillingAxis.minkowskiProd, Q31_eq_minkowskiDot, minkowskiDot, Pi.add_apply]
  ring

/-- The null rotation preserves the Minkowski product. -/
theorem minkowskiProd_nullRotation (t : ℝ) (x y : Fin 4 → ℝ) :
    KillingAxis.minkowskiProd (nullRotation t x) (nullRotation t y) =
      KillingAxis.minkowskiProd x y := by
  rw [minkowskiProd_polar, minkowskiProd_polar, ← nullRotation_add, Q31_nullRotation,
    Q31_nullRotation, Q31_nullRotation]

theorem Q31_nullLineVec : Q31 nullLineVec = 0 := by
  simp [Q31_eq_minkowskiDot, minkowskiDot, nullLineVec]

theorem Q31_transverseVec : Q31 transverseVec = 1 := by
  simp [Q31_eq_minkowskiDot, minkowskiDot, transverseVec]

theorem minkowskiProd_nullLine_transverse :
    KillingAxis.minkowskiProd nullLineVec transverseVec = 0 := by
  simp [KillingAxis.minkowskiProd, nullLineVec, transverseVec]

/-- A lightlike vector remains lightlike. -/
theorem nullRotation_lightlike {t : ℝ} {x : Fin 4 → ℝ} (hx : Q31 x = 0) :
    Q31 (nullRotation t x) = 0 := by
  rw [Q31_nullRotation, hx]

/-- For `t ≠ 0` the fixed vectors are the span of the null line and `e₂`. -/
theorem nullRotation_eq_self_iff {t : ℝ} (ht : t ≠ 0) (x : Fin 4 → ℝ) :
    nullRotation t x = x ↔ ∃ a b : ℝ, x = a • nullLineVec + b • transverseVec := by
  constructor
  · intro h
    have h1 : x 1 + 2 * t * (x 0 + x 3) = x 1 := by
      simpa [nullRotation] using congr_fun h 1
    have h0 : x 0 + 2 * t * x 1 + 2 * t ^ 2 * (x 0 + x 3) = x 0 := by
      simpa [nullRotation] using congr_fun h 0
    have hsum : x 0 + x 3 = 0 := by
      have hdiff : 2 * t * (x 0 + x 3) = 0 := by linarith
      exact (mul_eq_zero.mp hdiff).resolve_left (mul_ne_zero two_ne_zero ht)
    have hx1 : x 1 = 0 := by
      have : 2 * t * x 1 = 0 := by
        rw [hsum] at h0
        linarith
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero ht)
    refine ⟨x 0, x 2, ?_⟩
    funext i
    fin_cases i <;> simp [nullLineVec, transverseVec, hx1, Pi.add_apply]
    · linarith
  · rintro ⟨a, b, rfl⟩
    funext i
    fin_cases i <;> simp [nullRotation, nullLineVec, transverseVec, Pi.add_apply]

/-! ### The null ideal carries the same coefficients -/

theorem nullVector_eq_sum (x : Fin 4 → ℝ) :
    nullVector x = ∑ μ : Fin 4, x μ • null μ := by
  rw [nullVector, minkowskiVector_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [mul_smul_comm]
  rfl

theorem nullVector_basis (μ : Fin 4) : nullVector (e4vec μ) = null μ := by
  rw [nullVector_eq_sum, e4vec, Fintype.sum_eq_single μ]
  · simp [Pi.single]
  · intro ν hν
    simp [Pi.single, hν]

theorem commute_e4_parabolicRotor (t : ℝ) : Commute (ι e4Index) (parabolicRotor t) := by
  have h1 : Commute (ι e4Index) (1 : PGA) := Commute.one_right _
  have hK : Commute (ι e4Index) parabolicGen :=
    KillingAxis.commute_e4_of_mem_lorentzSpan parabolicGen_mem_lorentzSpan
  simpa [parabolicRotor] using h1.add_right (hK.smul_right t)

/-- `e₄` commutes through the rotor, so translations transform as vectors. -/
theorem sandwich_parabolic_nullVector (t : ℝ) (x : Fin 4 → ℝ) :
    sandwich (parabolicRotor t) (nullVector x) = nullVector (nullRotation t x) := by
  have hcomm : parabolicRotor t * ι e4Index = ι e4Index * parabolicRotor t :=
    (commute_e4_parabolicRotor t).eq.symm
  calc
    sandwich (parabolicRotor t) (nullVector x)
        = parabolicRotor t * (ι e4Index * minkowskiVector x) *
            reverse (parabolicRotor t) := by
          rw [sandwich, nullVector]
    _ = (parabolicRotor t * ι e4Index) * minkowskiVector x *
          reverse (parabolicRotor t) := by
          simp [mul_assoc]
    _ = (ι e4Index * parabolicRotor t) * minkowskiVector x *
          reverse (parabolicRotor t) := by
          rw [hcomm]
    _ = ι e4Index * (parabolicRotor t * minkowskiVector x *
          reverse (parabolicRotor t)) := by
          simp [mul_assoc]
    _ = ι e4Index * sandwich (parabolicRotor t) (minkowskiVector x) := by
          rw [sandwich]
    _ = ι e4Index * minkowskiVector (nullRotation t x) := by
          rw [parabolicRotor, sandwich_parabolic_minkowski]
    _ = nullVector (nullRotation t x) := by
          rw [nullVector]

theorem nullVector_sub (x y : Fin 4 → ℝ) :
    nullVector (x - y) = nullVector x - nullVector y := by
  rw [nullVector_eq_sum, nullVector_eq_sum, nullVector_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Pi.sub_apply, sub_smul]

private theorem nullLineVec_eq : nullLineVec = e4vec 0 - e4vec 3 := by
  ext i
  fin_cases i <;> simp [nullLineVec, e4vec, Pi.single, Pi.sub_apply]

theorem sandwich_parabolic_null2_fixed (t : ℝ) :
    sandwich (parabolicRotor t) (null 2) = null 2 := by
  rw [← nullVector_basis, sandwich_parabolic_nullVector]
  have hrot : nullRotation t (e4vec 2) = e4vec 2 := by
    ext i
    fin_cases i <;> simp [nullRotation, e4vec, Pi.single]
  rw [hrot, nullVector_basis]

theorem sandwich_parabolic_null_fixedLine (t : ℝ) :
    sandwich (parabolicRotor t) (null 0 - null 3) = null 0 - null 3 := by
  have hvec : null 0 - null 3 = nullVector nullLineVec := by
    rw [nullLineVec_eq, nullVector_sub, nullVector_basis, nullVector_basis]
  have hrot : nullRotation t nullLineVec = nullLineVec := by
    ext i
    fin_cases i <;> simp [nullRotation, nullLineVec]
  rw [hvec, sandwich_parabolic_nullVector, hrot]

end Gravity

end DstDiophantine
