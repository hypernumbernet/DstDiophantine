import DstDiophantine.Gravity.Tetrad
import DstDiophantine.Algebra.Amplification
import Mathlib.Tactic.FieldSimp

/-!
# Sandwich in the degenerate metric of `G(3,1,1)`

A motor fixes the null line up to the translational shear and acts on the
Minkowski complement, so the sandwich is an isometry of the degenerate metric.
The null coefficient is not a function of the finite angle \(J\), and \(J\) is
not identified with the teleparallel scalar.
-/

namespace DstDiophantine.Gravity.DegenerateSandwich

open PGA Generators Operations Motor Amplification Invariant LorentzLie MotorGroup
open Sandwich (sandwich sandwich_add sandwich_smul sandwich_comp sandwich_sq)
open CliffordAlgebra (reverse)
open KillingAxis (sandwich_expTrans sandwich_expTrans_ι
  commutator_omegaTorsion_minkowskiVector omegaTrans_eq_half_e4)

/-! ### The five-dimensional vector space -/

/-- Grade-one element `ι(v)` of `G(3,1,1)`. -/
noncomputable def vec5 (v : Vec5) : PGA :=
  CliffordAlgebra.ι Q311 v

theorem vec5_e5vec (i : Fin 5) : vec5 (e5vec i) = ι i := rfl

/-- Minkowski complement of the null line. -/
noncomputable def minkowskiSpan : Submodule ℝ PGA :=
  Submodule.span ℝ (Set.range fun μ : Fin 4 => ι (Fin.castAdd 1 μ))

/-- The null line `ℝ e₄`. -/
noncomputable def nullLine : Submodule ℝ PGA :=
  Submodule.span ℝ {ι e4Index}

theorem vec5_injective : Function.Injective vec5 := by
  have : Invertible (2 : ℝ) := ⟨2⁻¹, by norm_num, by norm_num⟩
  intro v w h
  apply (ExteriorAlgebra.ι_inj ℝ v w).mp
  have hE := congrArg (CliffordAlgebra.equivExterior (Q := Q311)) h
  simpa [vec5, CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_ι] using hE

theorem minkowskiVector_mem (x : Vec4) : minkowskiVector x ∈ minkowskiSpan := by
  rw [minkowskiVector_eq_sum]
  exact Submodule.sum_smul_mem _ _ fun μ _ =>
    Submodule.subset_span ⟨μ, rfl⟩

theorem frameVec_mem (μ : Fin 4) : frameVec μ ∈ minkowskiSpan := by
  rw [frameVec, ← vec5_e5vec, ← extend4_e4vec]
  exact minkowskiVector_mem (e4vec μ)

theorem e4_mem_nullLine : ι e4Index ∈ nullLine :=
  Submodule.subset_span rfl

theorem exists_minkowskiVector_of_mem {x : PGA} (hx : x ∈ minkowskiSpan) :
    ∃ y : Vec4, x = minkowskiVector y := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  exact ⟨c, by rw [minkowskiVector_eq_sum, hc]⟩

theorem mem_nullLine_iff {x : PGA} : x ∈ nullLine ↔ ∃ c : ℝ, x = c • ι e4Index := by
  rw [nullLine, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

theorem eq_zero_of_minkowski_eq_null {y : Vec4} {c : ℝ}
    (h : minkowskiVector y = c • ι e4Index) : y = 0 ∧ c = 0 := by
  have hι : vec5 (extend4 y) = vec5 (c • e5vec 4) := by
    simp only [vec5, minkowskiVector, map_smul] at h ⊢
    rw [h]
    rfl
  have hv := vec5_injective hι
  refine ⟨?_, ?_⟩
  · ext μ
    have := congr_fun hv (Fin.castAdd 1 μ)
    fin_cases μ <;> simpa [extend4, e5vec, Pi.single] using this
  · have h4 := congr_fun hv 4
    simp [extend4, e5vec, Pi.single_eq_same] at h4
    exact h4.symm

theorem minkowskiSpan_inf_nullLine : minkowskiSpan ⊓ nullLine = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hm, hn⟩ := hx
  obtain ⟨y, hy⟩ := exists_minkowskiVector_of_mem hm
  obtain ⟨c, hc⟩ := mem_nullLine_iff.mp hn
  obtain ⟨_, hc0⟩ := eq_zero_of_minkowski_eq_null (hy.symm.trans hc)
  rw [hc, hc0, zero_smul]
  exact Submodule.zero_mem _

theorem split_unique {a a' : PGA} {c c' : ℝ}
    (ha : a ∈ minkowskiSpan) (ha' : a' ∈ minkowskiSpan)
    (h : a + c • ι e4Index = a' + c' • ι e4Index) : a = a' ∧ c = c' := by
  have hsub : a - a' = (c' - c) • ι e4Index := by
    calc
      a - a' = a + c • ι e4Index - c • ι e4Index - a' := by abel
      _ = a' + c' • ι e4Index - c • ι e4Index - a' := by rw [h]
      _ = (c' - c) • ι e4Index := by module
  have hbot : a - a' ∈ minkowskiSpan ⊓ nullLine :=
    ⟨sub_mem ha ha', by
      rw [hsub]
      exact Submodule.smul_mem _ (c' - c) e4_mem_nullLine⟩
  rw [minkowskiSpan_inf_nullLine, Submodule.mem_bot] at hbot
  have haa : a = a' := sub_eq_zero.mp hbot
  have hc : (c' - c) • ι e4Index = 0 := by rw [← hsub, hbot]
  rcases smul_eq_zero.mp hc with hzero | hzero
  · exact ⟨haa, by linarith⟩
  · exact absurd hzero ι_e4_ne_zero

theorem vec5_split (v : Vec5) :
    vec5 v = minkowskiVector (restrict4 v) + v 4 • ι e4Index := by
  have h := extend4_restrict4_add_last v
  have h1 : vec5 v = vec5 (extend4 (restrict4 v)) + v 4 • vec5 (e5vec 4) := by
    conv_lhs => rw [← h]
    simp only [vec5, map_add, map_smul]
  rw [h1, minkowskiVector, vec5_e5vec]
  simp [vec5, e4Index]

/-! ### Rotors preserve the splitting -/

theorem commutator_omegaTorsion_mem_minkowskiSpan (t : TorsionParams) {x : PGA}
    (hx : x ∈ minkowskiSpan) : commutator (omegaTorsion t) x ∈ minkowskiSpan := by
  refine Submodule.span_induction (p := fun y _ => commutator (omegaTorsion t) y ∈ minkowskiSpan)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨μ, rfl⟩
    have h := commutator_omegaTorsion_minkowskiVector t (e4vec μ)
    have he : minkowskiVector (e4vec μ) = ι (Fin.castAdd 1 μ) := by
      rw [minkowskiVector_eq_sum, Fin.sum_univ_four]
      fin_cases μ <;> simp [e4vec]
    rw [he] at h
    rw [h]
    exact minkowskiVector_mem _
  · rw [Generators.commutator]
    simp
  · intro _ _ _ _ hy hz
    rw [commutator_add_right]
    exact add_mem hy hz
  · intro r y _ hy
    rw [commutator_smul_right]
    exact Submodule.smul_mem _ r hy

theorem sandwich_rotor_mem_minkowskiSpan (t : TorsionParams) {x : PGA}
    (hx : x ∈ minkowskiSpan) : sandwich (rotorTorsion t) x ∈ minkowskiSpan :=
  sandwich_exp_mem (omegaTorsion_reverse t)
    (fun _ hy => commutator_omegaTorsion_mem_minkowskiSpan t hy) hx

theorem rotor_frame_mem_minkowskiSpan (t : TorsionParams) (μ : Fin 4) :
    sandwich (rotorTorsion t) (frameVec μ) ∈ minkowskiSpan :=
  sandwich_rotor_mem_minkowskiSpan t (frameVec_mem μ)

theorem sandwich_rotor_vec5 (t : TorsionParams) (v : Vec5) :
    ∃ w : Vec5, sandwich (rotorTorsion t) (vec5 v) = vec5 w ∧ w 4 = v 4 ∧
      Q311 w = Q311 v := by
  have hR : sandwich (rotorTorsion t) (vec5 v) =
      sandwich (rotorTorsion t) (minkowskiVector (restrict4 v)) + v 4 • ι e4Index := by
    rw [vec5_split, sandwich_add, sandwich_smul, rotor_fixes_null]
  have hm := sandwich_rotor_mem_minkowskiSpan t (minkowskiVector_mem (restrict4 v))
  obtain ⟨y, hy⟩ := exists_minkowskiVector_of_mem hm
  let w : Vec5 := extend4 y + v 4 • e5vec 4
  have hs : sandwich (rotorTorsion t) (vec5 v) = vec5 w := by
    rw [hR, hy]
    rw [show w = extend4 y + v 4 • e5vec 4 from rfl, vec5, map_add, map_smul, minkowskiVector]
    rfl
  refine ⟨w, hs, ?_, ?_⟩
  · change (extend4 y + v 4 • e5vec 4) 4 = v 4
    simp [extend4, e5vec, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
  · have hscalar : vec5 v * vec5 v = algebraMap ℝ PGA (Q311 v) := by
      simp [vec5, CliffordAlgebra.ι_sq_scalar]
    have hscalarw : vec5 w * vec5 w = algebraMap ℝ PGA (Q311 w) := by
      simp [vec5, CliffordAlgebra.ι_sq_scalar]
    have hunit : sandwich (rotorTorsion t) (algebraMap ℝ PGA (Q311 v)) =
        algebraMap ℝ PGA (Q311 v) := by
      simp only [sandwich]
      rw [← Algebra.commutes (Q311 v) (rotorTorsion t), mul_assoc, rotor_unitary, mul_one]
    have hprod := sandwich_sq (rotor_unitary t) (vec5 v)
    rw [hscalar, hunit, hs, hscalarw] at hprod
    exact FaithfulSMul.algebraMap_injective (R := ℝ) (A := PGA) hprod

/-! ### Translators shear along the null line -/

/-- Minkowski pairing `η(λ, x)`, the coefficient of the null shear. -/
def minkowskiPair (lam x : Vec4) : ℝ :=
  -lam 0 * x 0 + lam 1 * x 1 + lam 2 * x 2 + lam 3 * x 3

theorem minkowskiPair_eq_sum (lam x : Vec4) :
    minkowskiPair lam x = ∑ μ : Fin 4, w31 μ * lam μ * x μ := by
  simp [minkowskiPair, Fin.sum_univ_four, w31]

theorem sandwich_expTrans_minkowskiVector (p : TransParams) (x : Vec4) :
    sandwich (expTrans p) (minkowskiVector x) =
      minkowskiVector x + minkowskiPair p.lambda x • ι e4Index := by
  rw [minkowskiVector_eq_sum, Fin.sum_univ_four]
  simp only [sandwich_add, sandwich_smul, sandwich_expTrans_ι, minkowskiPair, w31]
  module

theorem sandwich_expTrans_e4 (p : TransParams) :
    sandwich (expTrans p) (ι e4Index) = ι e4Index := by
  rw [sandwich_expTrans, omegaTrans_eq_half_e4, commutator_smul_left]
  have h0 : commutator (ι e4Index * minkowskiVector p.lambda) (ι e4Index) = 0 := by
    rw [Generators.commutator]
    have h1 : ι e4Index * minkowskiVector p.lambda * ι e4Index = 0 := by
      simpa [mul_assoc] using e4_mul_mul_e4 (minkowskiVector p.lambda)
    have h2 : ι e4Index * (ι e4Index * minkowskiVector p.lambda) = 0 := by
      rw [← mul_assoc, e4_sq_zero, zero_mul]
    rw [h1, h2, sub_zero]
  rw [h0, smul_zero, add_zero]

theorem Q311_add_null (v : Vec5) (c : ℝ) : Q311 (v + c • e5vec 4) = Q311 v := by
  simp only [Q311, QuadraticMap.weightedSumSquares_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, e5vec]
  refine Finset.sum_congr rfl fun i _ => ?_
  fin_cases i <;> simp [w311, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem sandwich_expTrans_vec5 (p : TransParams) (v : Vec5) :
    sandwich (expTrans p) (vec5 v) =
      vec5 (v + minkowskiPair p.lambda (restrict4 v) • e5vec 4) := by
  rw [vec5_split, sandwich_add, sandwich_smul, sandwich_expTrans_e4,
    sandwich_expTrans_minkowskiVector]
  have hright : vec5 (v + minkowskiPair p.lambda (restrict4 v) • e5vec 4) =
      minkowskiVector (restrict4 v) +
        (v 4 + minkowskiPair p.lambda (restrict4 v)) • ι e4Index := by
    have hsplit := vec5_split (v + minkowskiPair p.lambda (restrict4 v) • e5vec 4)
    have hrest : restrict4 (v + minkowskiPair p.lambda (restrict4 v) • e5vec 4) =
        restrict4 v := by
      ext μ
      fin_cases μ <;> simp [restrict4, Pi.add_apply, Pi.smul_apply, e5vec, Pi.single]
    have hlast : (v + minkowskiPair p.lambda (restrict4 v) • e5vec 4) 4 =
        v 4 + minkowskiPair p.lambda (restrict4 v) := by
      simp [Pi.add_apply, Pi.smul_apply, e5vec, Pi.single_eq_same]
    rw [hsplit, hrest, hlast]
  rw [hright]
  module

theorem translator_preserves_Q311 (p : TransParams) (v : Vec5) :
    Q311 (v + minkowskiPair p.lambda (restrict4 v) • e5vec 4) = Q311 v :=
  Q311_add_null v _

/-! ### Motors are degenerate isometries, and the field splits -/

theorem motor_degenerate_isometry (p : OmegaParams) (v : Vec5) :
    ∃ w : Vec5,
      sandwich (motor p) (vec5 v) = vec5 w ∧
        w 4 = v 4 + minkowskiPair p.trans.lambda (restrict4 v) ∧
        Q311 w = Q311 v := by
  let vT : Vec5 := v + minkowskiPair p.trans.lambda (restrict4 v) • e5vec 4
  have hT : sandwich (expTrans p.trans) (vec5 v) = vec5 vT :=
    sandwich_expTrans_vec5 p.trans v
  obtain ⟨w, hw, h4, hQ⟩ := sandwich_rotor_vec5 p.torsion vT
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [motor, sandwich_comp, hT, hw]
  · rw [h4]
    simp [vT, Pi.add_apply, Pi.smul_apply, e5vec, Pi.single_eq_same]
  · rw [hQ, translator_preserves_Q311]

theorem motor_frame_split (p : OmegaParams) (μ : Fin 4) :
    sandwich (motor p) (frameVec μ) =
      sandwich (rotorTorsion p.torsion) (frameVec μ) +
        (w31 μ * p.trans.lambda μ) • ι e4Index ∧
      sandwich (rotorTorsion p.torsion) (frameVec μ) ∈ minkowskiSpan :=
  ⟨motor_minkowski_leg p μ, rotor_frame_mem_minkowskiSpan p.torsion μ⟩

theorem motor_difference_null {p q : OmegaParams} (h : p.torsion = q.torsion) (μ : Fin 4) :
    sandwich (motor p) (frameVec μ) - sandwich (motor q) (frameVec μ) =
      (w31 μ * (p.trans.lambda μ - q.trans.lambda μ)) • ι e4Index := by
  rw [motor_minkowski_leg, motor_minkowski_leg, h]
  module

theorem nullShear_eq_of_trans {p q : OmegaParams} (h : p.trans = q.trans) (μ : Fin 4) :
    sandwich (motor p) (frameVec μ) - sandwich (rotorTorsion p.torsion) (frameVec μ) =
      sandwich (motor q) (frameVec μ) -
        sandwich (rotorTorsion q.torsion) (frameVec μ) := by
  rw [motor_minkowski_leg, motor_minkowski_leg, h]
  abel

theorem minkowskiLeg_eq_of_torsion {p q : OmegaParams} (h : p.torsion = q.torsion)
    (μ : Fin 4) :
    sandwich (motor p) (frameVec μ) - (w31 μ * p.trans.lambda μ) • ι e4Index =
      sandwich (motor q) (frameVec μ) - (w31 μ * q.trans.lambda μ) • ι e4Index := by
  rw [motor_minkowski_leg, motor_minkowski_leg, h]
  abel

theorem pureTranslation_minkowski_leg (p : TransParams) (μ : Fin 4) :
    sandwich (motor ⟨⟨fun _ => 0, fun _ => 0⟩, p⟩) (frameVec μ) =
      frameVec μ + (w31 μ * p.lambda μ) • ι e4Index := by
  rw [motor_of_pure_translation, translator_minkowski_leg]

/-- The finite angle is not the null coefficient. -/
theorem pureBoost_nullShear_zero_of_J (φ : ℝ) (hφ : φ ≠ 0) (μ : Fin 4) :
    sandwich (motor ⟨pureBoost φ, ⟨fun _ => 0⟩⟩) (frameVec μ) -
        sandwich (rotorTorsion (pureBoost φ)) (frameVec μ) = 0 ∧
      J (pureBoost φ) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [motor_minkowski_leg]
    simp
  · rw [J_pureBoost]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hφ)

end DstDiophantine.Gravity.DegenerateSandwich
