import DstDiophantine.Gravity.ElectronCapacity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shapes of the seats

## Paper boundary (do **not** claim)

A seat is a pattern on directions. It is not a path, and it is not an
`s`/`p`/`d`/`f` label. The zero of a pattern is not a node of `γ_s` and not a
zero of the signed force. Nothing here is a force minimum, a Bohr radius, or a
value of `ℓ`.

## What is proved

* The monopole takes the same value in every direction.
* A dipole with nonzero axis is positive along that axis and negative along
  the opposite direction. Its zero set is the orthogonal plane: the kernel of
  the linear form has dimension `2`.
* A nonzero traceless quadrupole is unchanged when the direction is reversed.
  It is positive in some direction, negative in another, and zero along some
  nonzero direction.
* A nonzero traceless octupole changes sign when the direction is reversed, so
  some direction and its opposite carry opposite values.
-/

namespace DstDiophantine

namespace Gravity

open Matrix Set

/-! ### Directions -/

private def dirDot (v w : Fin 3 → ℝ) : ℝ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

private def applyMat (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2

private def e3 (i : Fin 3) : Fin 3 → ℝ :=
  fun j => if j = i then (1 : ℝ) else 0

private lemma dirDot_self_nonneg (a : Fin 3 → ℝ) : 0 ≤ dirDot a a := by
  unfold dirDot
  nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2)]

private lemma symm_apply {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.transpose = M)
    (i j : Fin 3) : M i j = M j i := by
  simpa [Matrix.transpose_apply] using congr_fun (congr_fun hM j) i

private lemma quadrupole_spec {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ quadrupole) :
    M.transpose = M ∧ M.trace = 0 := hM

/-! ### Monopole -/

def monoValue (s : ℝ) (_u : Fin 3 → ℝ) : ℝ := s

theorem seatPattern_monopole (s : ℝ) (u w : Fin 3 → ℝ) :
    monoValue s u = monoValue s w := rfl

/-! ### Dipole -/

def dipoleValue (a u : Fin 3 → ℝ) : ℝ := dirDot a u

def dipoleForm (a : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun u := dirDot a u
  map_add' u w := by
    unfold dirDot
    simp [Pi.add_apply]
    ring
  map_smul' r u := by
    unfold dirDot
    simp [Pi.smul_apply, smul_eq_mul]
    ring

theorem dipoleValue_neg (a u : Fin 3 → ℝ) :
    dipoleValue a (-u) = -dipoleValue a u := by
  unfold dipoleValue dirDot
  simp [Pi.neg_apply]
  ring

private lemma dipoleValue_self_pos {a : Fin 3 → ℝ} (ha : dipoleValue a a ≠ 0) :
    0 < dipoleValue a a := by
  have hnn := dirDot_self_nonneg a
  unfold dipoleValue at ha hnn ⊢
  exact lt_of_le_of_ne hnn ha.symm

private lemma dirDot_smul_self (a : Fin 3 → ℝ) (c : ℝ) :
    dirDot a (c • a) = c * dirDot a a := by
  unfold dirDot
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma dipoleForm_surjective {a : Fin 3 → ℝ} (ha : dipoleValue a a ≠ 0) :
    Function.Surjective (dipoleForm a) := by
  intro t
  refine ⟨(t / dipoleValue a a) • a, ?_⟩
  have hs : dirDot a a ≠ 0 := by simpa [dipoleValue] using ha
  change dirDot a ((t / dipoleValue a a) • a) = t
  rw [dirDot_smul_self]
  simp only [dipoleValue]
  field_simp [hs]

theorem seatPattern_dipole {a : Fin 3 → ℝ} (ha : dipoleValue a a ≠ 0) :
    0 < dipoleValue a a ∧
      dipoleValue a (-a) < 0 ∧
      Module.finrank ℝ (LinearMap.ker (dipoleForm a)) = 2 := by
  have hpos := dipoleValue_self_pos ha
  refine ⟨hpos, ?_, ?_⟩
  · rw [dipoleValue_neg]
    linarith
  · have hsum := (dipoleForm a).finrank_range_add_finrank_ker
    have hdom : Module.finrank ℝ (Fin 3 → ℝ) = 3 :=
      (Module.finrank_fin_fun ℝ : Module.finrank ℝ (Fin 3 → ℝ) = 3)
    have hrange : LinearMap.range (dipoleForm a) = ⊤ :=
      LinearMap.range_eq_top.mpr (dipoleForm_surjective ha)
    rw [hrange, finrank_top, Module.finrank_self, hdom] at hsum
    omega

/-! ### Quadrupole -/

def quadValue (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) : ℝ :=
  dirDot v (applyMat M v)

private def quadPolar (M : Matrix (Fin 3) (Fin 3) ℝ) (v w : Fin 3 → ℝ) : ℝ :=
  dirDot v (applyMat M w)

private lemma quadValue_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (v : Fin 3 → ℝ) :
    quadValue M (c • v) = c ^ 2 * quadValue M v := by
  unfold quadValue dirDot applyMat
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma quadPolar_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ)
    (v w : Fin 3 → ℝ) :
    quadPolar M (s • v) (t • w) = s * t * quadPolar M v w := by
  unfold quadPolar dirDot applyMat
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma quadPolar_symm {M : Matrix (Fin 3) (Fin 3) ℝ} {v w : Fin 3 → ℝ}
    (hM : M.transpose = M) : quadPolar M v w = quadPolar M w v := by
  unfold quadPolar dirDot applyMat
  have h01 := symm_apply hM 0 1
  have h02 := symm_apply hM 0 2
  have h12 := symm_apply hM 1 2
  rw [h01, h02, h12]
  ring

private lemma quadValue_add {M : Matrix (Fin 3) (Fin 3) ℝ} {v w : Fin 3 → ℝ}
    (hM : M.transpose = M) :
    quadValue M (v + w) =
      quadValue M v + quadValue M w + 2 * quadPolar M v w := by
  unfold quadValue quadPolar dirDot applyMat
  have h01 := symm_apply hM 0 1
  have h02 := symm_apply hM 0 2
  have h12 := symm_apply hM 1 2
  simp only [Pi.add_apply]
  rw [h01, h02, h12]
  ring

private lemma quadValue_combo {M : Matrix (Fin 3) (Fin 3) ℝ} {v w : Fin 3 → ℝ}
    (hM : M.transpose = M) (s t : ℝ) :
    quadValue M (s • v + t • w) =
      s ^ 2 * quadValue M v + t ^ 2 * quadValue M w +
        2 * s * t * quadPolar M v w := by
  calc
    quadValue M (s • v + t • w)
        = quadValue M (s • v) + quadValue M (t • w) +
            2 * quadPolar M (s • v) (t • w) :=
          quadValue_add hM
    _ = s ^ 2 * quadValue M v + t ^ 2 * quadValue M w +
          2 * (s * t * quadPolar M v w) := by
          rw [quadValue_smul, quadValue_smul, quadPolar_smul]
    _ = s ^ 2 * quadValue M v + t ^ 2 * quadValue M w +
          2 * s * t * quadPolar M v w := by ring

theorem quadValue_even (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    quadValue M (-v) = quadValue M v := by
  have h := quadValue_smul M (-1) v
  simpa using h

private lemma quadValue_e3 (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    quadValue M (e3 i) = M i i := by
  fin_cases i <;>
    · unfold quadValue dirDot applyMat e3
      simp

private lemma quad_pair01 {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.transpose = M) :
    quadValue M (e3 0 + e3 1) = M 0 0 + M 1 1 + 2 * M 0 1 ∧
      quadValue M (e3 0 - e3 1) = M 0 0 + M 1 1 - 2 * M 0 1 := by
  have h01 := symm_apply hM 0 1
  constructor
  · unfold quadValue dirDot applyMat e3
    simp [h01, Pi.add_apply]
    ring
  · unfold quadValue dirDot applyMat e3
    simp [h01, Pi.sub_apply]
    ring

private lemma quad_pair02 {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.transpose = M) :
    quadValue M (e3 0 + e3 2) = M 0 0 + M 2 2 + 2 * M 0 2 ∧
      quadValue M (e3 0 - e3 2) = M 0 0 + M 2 2 - 2 * M 0 2 := by
  have h02 := symm_apply hM 0 2
  constructor
  · unfold quadValue dirDot applyMat e3
    simp [h02, Pi.add_apply]
    ring
  · unfold quadValue dirDot applyMat e3
    simp [h02, Pi.sub_apply]
    ring

private lemma quad_pair12 {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.transpose = M) :
    quadValue M (e3 1 + e3 2) = M 1 1 + M 2 2 + 2 * M 1 2 ∧
      quadValue M (e3 1 - e3 2) = M 1 1 + M 2 2 - 2 * M 1 2 := by
  have h12 := symm_apply hM 1 2
  constructor
  · unfold quadValue dirDot applyMat e3
    simp [h12, Pi.add_apply]
    ring
  · unfold quadValue dirDot applyMat e3
    simp [h12, Pi.sub_apply]
    ring

private lemma quadValue_nonneg_eq_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ quadrupole) (hnn : ∀ v, 0 ≤ quadValue M v) : M = 0 := by
  have hspec := quadrupole_spec hM
  have hsym := hspec.1
  have h00 : M 0 0 = 0 := by
    have hle : 0 ≤ M 0 0 := by simpa [quadValue_e3] using hnn (e3 0)
    have h11 : 0 ≤ M 1 1 := by simpa [quadValue_e3] using hnn (e3 1)
    have h22 : 0 ≤ M 2 2 := by simpa [quadValue_e3] using hnn (e3 2)
    have htr : M 0 0 + M 1 1 + M 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using hspec.2
    linarith
  have h11 : M 1 1 = 0 := by
    have hle : 0 ≤ M 0 0 := by simpa [quadValue_e3] using hnn (e3 0)
    have h11 : 0 ≤ M 1 1 := by simpa [quadValue_e3] using hnn (e3 1)
    have h22 : 0 ≤ M 2 2 := by simpa [quadValue_e3] using hnn (e3 2)
    have htr : M 0 0 + M 1 1 + M 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using hspec.2
    linarith
  have h22 : M 2 2 = 0 := by
    have hle : 0 ≤ M 0 0 := by simpa [quadValue_e3] using hnn (e3 0)
    have h11 : 0 ≤ M 1 1 := by simpa [quadValue_e3] using hnn (e3 1)
    have h22 : 0 ≤ M 2 2 := by simpa [quadValue_e3] using hnn (e3 2)
    have htr : M 0 0 + M 1 1 + M 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using hspec.2
    linarith
  have hpair01 := quad_pair01 hsym
  have h01 : M 0 1 = 0 := by
    have hp : 0 ≤ M 0 0 + M 1 1 + 2 * M 0 1 := by
      simpa [hpair01.1] using hnn (e3 0 + e3 1)
    have hm : 0 ≤ M 0 0 + M 1 1 - 2 * M 0 1 := by
      simpa [hpair01.2] using hnn (e3 0 - e3 1)
    linarith
  have hpair02 := quad_pair02 hsym
  have h02 : M 0 2 = 0 := by
    have hp : 0 ≤ M 0 0 + M 2 2 + 2 * M 0 2 := by
      simpa [hpair02.1] using hnn (e3 0 + e3 2)
    have hm : 0 ≤ M 0 0 + M 2 2 - 2 * M 0 2 := by
      simpa [hpair02.2] using hnn (e3 0 - e3 2)
    linarith
  have hpair12 := quad_pair12 hsym
  have h12 : M 1 2 = 0 := by
    have hp : 0 ≤ M 1 1 + M 2 2 + 2 * M 1 2 := by
      simpa [hpair12.1] using hnn (e3 1 + e3 2)
    have hm : 0 ≤ M 1 1 + M 2 2 - 2 * M 1 2 := by
      simpa [hpair12.2] using hnn (e3 1 - e3 2)
    linarith
  have h10 : M 1 0 = 0 := (symm_apply hsym 1 0).trans h01
  have h20 : M 2 0 = 0 := (symm_apply hsym 2 0).trans h02
  have h21 : M 2 1 = 0 := (symm_apply hsym 2 1).trans h12
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h01, h02, h12, h10, h20, h21]

private lemma quadValue_neg_matrix (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    quadValue (-M) v = -quadValue M v := by
  unfold quadValue dirDot applyMat
  simp
  ring

private lemma quadValue_nonpos_eq_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ quadrupole) (hnp : ∀ v, quadValue M v ≤ 0) : M = 0 := by
  have hnn : ∀ v, 0 ≤ quadValue (-M) v := by
    intro v
    have hneg := quadValue_neg_matrix M v
    linarith [hnp v]
  have hz : -M = 0 := quadValue_nonneg_eq_zero (Submodule.neg_mem quadrupole hM) hnn
  exact neg_eq_zero.mp hz

private lemma continuous_quadPoly (α β γ : ℝ) :
    Continuous (fun t : ℝ =>
      (1 - t) ^ 2 * α + t ^ 2 * β + 2 * (1 - t) * t * γ) := by
  have hsub : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
  have hA : Continuous (fun t : ℝ => (1 - t) ^ 2 * α) :=
    (hsub.pow 2).mul continuous_const
  have hB : Continuous (fun t : ℝ => t ^ 2 * β) :=
    (continuous_id.pow 2).mul continuous_const
  have hC : Continuous (fun t : ℝ => 2 * (1 - t) * t * γ) :=
    (((continuous_const.mul hsub).mul continuous_id).mul continuous_const)
  exact (hA.add hB).add hC

private lemma quadValue_pos_exists {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ quadrupole) (h0 : M ≠ 0) : ∃ v, 0 < quadValue M v := by
  by_contra h
  push Not at h
  exact h0 (quadValue_nonpos_eq_zero hM h)

private lemma quadValue_neg_exists {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ quadrupole) (h0 : M ≠ 0) : ∃ w, quadValue M w < 0 := by
  by_contra h
  push Not at h
  exact h0 (quadValue_nonneg_eq_zero hM h)

private lemma quadValue_has_node {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ quadrupole) (h0 : M ≠ 0) :
    ∃ u, u ≠ 0 ∧ quadValue M u = 0 := by
  obtain ⟨v, hv⟩ := quadValue_pos_exists hM h0
  obtain ⟨w, hw⟩ := quadValue_neg_exists hM h0
  have hsym := (quadrupole_spec hM).1
  let p : ℝ → ℝ := fun t =>
    (1 - t) ^ 2 * quadValue M v + t ^ 2 * quadValue M w +
      2 * (1 - t) * t * quadPolar M v w
  have hp (t : ℝ) : quadValue M ((1 - t) • v + t • w) = p t := by
    simpa [p] using quadValue_combo hsym (1 - t) t
  have hcont : Continuous p := continuous_quadPoly (quadValue M v) (quadValue M w)
    (quadPolar M v w)
  have hp0 : 0 < p 0 := by
    have : p 0 = quadValue M v := by simp [p]
    linarith
  have hp1 : p 1 < 0 := by
    have : p 1 = quadValue M w := by simp [p]
    linarith
  have hmem : (0 : ℝ) ∈ Icc (p 1) (p 0) := ⟨hp1.le, hp0.le⟩
  obtain ⟨t, ht, hpt⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn hmem
  let u := (1 - t) • v + t • w
  have hu0 : quadValue M u = 0 := by
    simpa [u, hp] using hpt
  have ht0 : t ≠ 0 := by
    intro ht0
    have : p 0 = 0 := by simpa [ht0] using hpt
    linarith
  have ht1 : t ≠ 1 := by
    intro ht1
    have : p 1 = 0 := by simpa [ht1] using hpt
    linarith
  have hune : u ≠ 0 := by
    intro hu
    have htw : t • w = -((1 - t) • v) := eq_neg_of_add_eq_zero_right hu
    have hwscale : w = (-((1 - t) * t⁻¹)) • v := by
      calc
        w = t⁻¹ • (t • w) := by rw [← mul_smul, inv_mul_cancel₀ ht0, one_smul]
        _ = t⁻¹ • (-((1 - t) • v)) := by rw [htw]
        _ = -(t⁻¹ • ((1 - t) • v)) := by rw [smul_neg]
        _ = -((t⁻¹ * (1 - t)) • v) := by rw [mul_smul]
        _ = (-(t⁻¹ * (1 - t))) • v := by rw [neg_smul]
        _ = (-((1 - t) * t⁻¹)) • v := by
              congr 1
              ring
    have hqw : quadValue M w =
        ((1 - t) * t⁻¹) ^ 2 * quadValue M v := by
      rw [hwscale, quadValue_smul]
      ring
    have hfac : 0 < ((1 - t) * t⁻¹) ^ 2 := by
      apply sq_pos_of_ne_zero
      exact mul_ne_zero (sub_ne_zero.mpr ht1.symm) (inv_ne_zero ht0)
    have : 0 < quadValue M w := by
      rw [hqw]
      exact mul_pos hfac hv
    linarith
  exact ⟨u, hune, hu0⟩

theorem seatPattern_quadrupole {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ quadrupole) (h0 : M ≠ 0) :
    (∀ v, quadValue M (-v) = quadValue M v) ∧
      (∃ v, 0 < quadValue M v) ∧
      (∃ w, quadValue M w < 0) ∧
      (∃ u, u ≠ 0 ∧ quadValue M u = 0) :=
  ⟨fun v => quadValue_even M v, quadValue_pos_exists hM h0, quadValue_neg_exists hM h0,
    quadValue_has_node hM h0⟩

/-! ### Octupole

Coefficients, matching `octuTrace`: `0,1,2` are `x³,y³,z³`; `3,4` are `x²y,x²z`;
`5` is `xy²`; `6` is `y²z`; `7` is `xz²`; `8` is `yz²`; `9` is `xyz`.
`octuTrace` is then half the Laplacian. -/

def octuValue (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  c 0 * v 0 ^ 3 + c 1 * v 1 ^ 3 + c 2 * v 2 ^ 3 +
    c 3 * v 0 ^ 2 * v 1 + c 4 * v 0 ^ 2 * v 2 +
    c 5 * v 0 * v 1 ^ 2 + c 6 * v 1 ^ 2 * v 2 +
    c 7 * v 0 * v 2 ^ 2 + c 8 * v 1 * v 2 ^ 2 +
    c 9 * v 0 * v 1 * v 2

theorem octuValue_neg (c : Fin 10 → ℝ) (v : Fin 3 → ℝ) :
    octuValue c (-v) = -octuValue c v := by
  unfold octuValue
  simp only [Pi.neg_apply]
  ring

private lemma octu_e0 (c : Fin 10 → ℝ) : octuValue c (e3 0) = c 0 := by
  unfold octuValue e3
  simp

private lemma octu_e1 (c : Fin 10 → ℝ) : octuValue c (e3 1) = c 1 := by
  unfold octuValue e3
  simp

private lemma octu_e2 (c : Fin 10 → ℝ) : octuValue c (e3 2) = c 2 := by
  unfold octuValue e3
  simp

private lemma octu_sum01 (c : Fin 10 → ℝ) :
    octuValue c (e3 0 + e3 1) = c 0 + c 1 + c 3 + c 5 := by
  unfold octuValue e3
  simp [Pi.add_apply]

private lemma octu_diff01 (c : Fin 10 → ℝ) :
    octuValue c (e3 0 - e3 1) = c 0 - c 1 - c 3 + c 5 := by
  unfold octuValue e3
  simp [Pi.sub_apply]
  ring

private lemma octu_sum02 (c : Fin 10 → ℝ) :
    octuValue c (e3 0 + e3 2) = c 0 + c 2 + c 4 + c 7 := by
  unfold octuValue e3
  simp [Pi.add_apply]

private lemma octu_diff02 (c : Fin 10 → ℝ) :
    octuValue c (e3 0 - e3 2) = c 0 - c 2 - c 4 + c 7 := by
  unfold octuValue e3
  simp [Pi.sub_apply]
  ring

private lemma octu_sum12 (c : Fin 10 → ℝ) :
    octuValue c (e3 1 + e3 2) = c 1 + c 2 + c 6 + c 8 := by
  unfold octuValue e3
  simp [Pi.add_apply]

private lemma octu_diff12 (c : Fin 10 → ℝ) :
    octuValue c (e3 1 - e3 2) = c 1 - c 2 - c 6 + c 8 := by
  unfold octuValue e3
  simp [Pi.sub_apply]
  ring

private lemma octu_sum012 (c : Fin 10 → ℝ) :
    octuValue c (e3 0 + e3 1 + e3 2) =
      c 0 + c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7 + c 8 + c 9 := by
  unfold octuValue e3
  simp [Pi.add_apply]

private lemma octuValue_forall_eq_zero {c : Fin 10 → ℝ}
    (h : ∀ v, octuValue c v = 0) : c = 0 := by
  have h0 : c 0 = 0 := by simpa [octu_e0] using h (e3 0)
  have h1 : c 1 = 0 := by simpa [octu_e1] using h (e3 1)
  have h2 : c 2 = 0 := by simpa [octu_e2] using h (e3 2)
  have hA01 := h (e3 0 + e3 1)
  have hB01 := h (e3 0 - e3 1)
  have h3 : c 3 = 0 := by
    have hA := octu_sum01 c
    have hB := octu_diff01 c
    linarith
  have h5 : c 5 = 0 := by
    have hA := octu_sum01 c
    have hB := octu_diff01 c
    linarith
  have hA02 := h (e3 0 + e3 2)
  have hB02 := h (e3 0 - e3 2)
  have h4 : c 4 = 0 := by
    have hA := octu_sum02 c
    have hB := octu_diff02 c
    linarith
  have h7 : c 7 = 0 := by
    have hA := octu_sum02 c
    have hB := octu_diff02 c
    linarith
  have hA12 := h (e3 1 + e3 2)
  have hB12 := h (e3 1 - e3 2)
  have h6 : c 6 = 0 := by
    have hA := octu_sum12 c
    have hB := octu_diff12 c
    linarith
  have h8 : c 8 = 0 := by
    have hA := octu_sum12 c
    have hB := octu_diff12 c
    linarith
  have h9 : c 9 = 0 := by
    have hS := h (e3 0 + e3 1 + e3 2)
    have hP := octu_sum012 c
    linarith
  ext i
  fin_cases i <;> assumption

private lemma octuValue_exists_ne {c : Fin 10 → ℝ} (h0 : c ≠ 0) :
    ∃ v, octuValue c v ≠ 0 := by
  by_contra h
  push Not at h
  exact h0 (octuValue_forall_eq_zero h)

theorem seatPattern_octupole {c : Fin 10 → ℝ} (_hc : c ∈ octupole) (h0 : c ≠ 0) :
    (∀ v, octuValue c (-v) = -octuValue c v) ∧
      ∃ v, 0 < octuValue c v ∧ octuValue c (-v) < 0 := by
  refine ⟨fun v => octuValue_neg c v, ?_⟩
  obtain ⟨v, hv⟩ := octuValue_exists_ne h0
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · refine ⟨-v, ?_, ?_⟩
    · have hneg := octuValue_neg c v
      linarith
    · simpa [neg_neg] using hlt
  · refine ⟨v, hgt, ?_⟩
    rw [octuValue_neg]
    linarith

end Gravity

end DstDiophantine
