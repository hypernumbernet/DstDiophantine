import DstDiophantine.Gravity.ConeLabels
import DstDiophantine.Gravity.ShieldCeiling

/-!
# Mass ceiling of the admissible cone

The unsigned mass shares the ceiling of the mismatch. Equality holds
exactly on the corner configurations: every axis is a pure boost or a
pure rotation. If `n` axes are pure boosts, the normalised mismatch is
the discrete height `(2n-3)/3`, hence one of `1`, `1/3`, `-1/3`, `-1`.
Saturated attraction is the unique corner of height `1` and carries the
whole mass ceiling. Unsaturated attraction meets that ceiling only at
height `1/3`, on the three corners with a single pure rotation.
Repulsion meets it at `-1/3` and at the pure rotation `-1`. Balance does
not meet it: a balanced configuration has normalised mass at most `5/6`,
and that bound is attained. Sector swap preserves the mass and sends `n`
to `3-n`.

The unsigned mass is the Euclidean size of the rapidities. It is not the
value of the Dirac mass.
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-- One axis at the pure-boost corner. -/
def IsUsualCorner (p : TorsionParams) (a : Fin 3) : Prop :=
  p.alpha a = Real.pi / 2 ∧ p.beta a = 0

/-- One axis at the pure-rotation corner. -/
def IsDualCorner (p : TorsionParams) (a : Fin 3) : Prop :=
  p.alpha a = 0 ∧ p.beta a = Real.pi / 2

/-- Corner configuration whose pure-boost axes are the `true` entries of `usual`. -/
noncomputable def massCorner (usual : Fin 3 → Bool) : TorsionParams where
  alpha := fun a => if usual a then Real.pi / 2 else 0
  beta := fun a => if usual a then 0 else Real.pi / 2

/-- Number of pure-boost axes. -/
def usualCount (usual : Fin 3 → Bool) : ℕ :=
  (if usual 0 then 1 else 0) + (if usual 1 then 1 else 0) + (if usual 2 then 1 else 0)

theorem isAdmissibleContinuous_massCorner (usual : Fin 3 → Bool) :
    IsAdmissibleContinuous (massCorner usual) := by
  intro a
  cases ha : usual a
  · refine ⟨?_, ?_, ?_⟩
    · simp [massCorner, ha]
    · simp [massCorner, ha]
      positivity
    · simp [massCorner, ha]
  · refine ⟨?_, ?_, ?_⟩
    · simp [massCorner, ha]
      positivity
    · simp [massCorner, ha]
    · simp [massCorner, ha]

private theorem axis_sq_sum_massCorner (usual : Fin 3 → Bool) (a : Fin 3) :
    (massCorner usual).alpha a ^ 2 + (massCorner usual).beta a ^ 2 = (Real.pi / 2) ^ 2 := by
  cases ha : usual a
  · simp [massCorner, ha]
  · simp [massCorner, ha]

theorem mass_massCorner (usual : Fin 3 → Bool) :
    mass (massCorner usual) = 3 * Real.pi ^ 2 / 8 := by
  rw [mass_coef]
  simp only [Fin.sum_univ_three]
  have h0 := axis_sq_sum_massCorner usual 0
  have h1 := axis_sq_sum_massCorner usual 1
  have h2 := axis_sq_sum_massCorner usual 2
  calc
    (1 / 2) * ((massCorner usual).alpha 0 ^ 2 + (massCorner usual).beta 0 ^ 2 +
        ((massCorner usual).alpha 1 ^ 2 + (massCorner usual).beta 1 ^ 2) +
        ((massCorner usual).alpha 2 ^ 2 + (massCorner usual).beta 2 ^ 2))
      = (1 / 2) * (3 * (Real.pi / 2) ^ 2) := by rw [h0, h1, h2]; ring
    _ = 3 * Real.pi ^ 2 / 8 := by ring

private theorem axis_signed_massCorner (usual : Fin 3 → Bool) (a : Fin 3) :
    (massCorner usual).alpha a ^ 2 - (massCorner usual).beta a ^ 2 =
      if usual a then (Real.pi / 2) ^ 2 else -((Real.pi / 2) ^ 2) := by
  cases ha : usual a
  · simp [massCorner, ha]
  · simp [massCorner, ha]

private theorem usualCount_eq_bits (usual : Fin 3 → Bool) :
    usualCount usual =
      (if usual 0 then 1 else 0) + (if usual 1 then 1 else 0) + (if usual 2 then 1 else 0) :=
  rfl

theorem usualCount_le_three (usual : Fin 3 → Bool) : usualCount usual ≤ 3 := by
  rw [usualCount_eq_bits]
  cases usual 0 <;> cases usual 1 <;> cases usual 2 <;> decide

theorem JNormalized_massCorner (usual : Fin 3 → Bool) :
    JNormalized (massCorner usual) = ((usualCount usual : ℝ) * 2 - 3) / 3 := by
  rw [JNormalized_coef]
  simp only [Fin.sum_univ_three]
  have h0 := axis_signed_massCorner usual 0
  have h1 := axis_signed_massCorner usual 1
  have h2 := axis_signed_massCorner usual 2
  rw [usualCount_eq_bits]
  cases b0 : usual 0 <;> cases b1 : usual 1 <;> cases b2 : usual 2
  all_goals
    simp [h0, h1, h2, b0, b1, b2]
    field_simp
    ring

theorem massNormalized_eq_one_iff (p : TorsionParams) :
    massNormalized p = 1 ↔ mass p = 3 * Real.pi ^ 2 / 8 := by
  unfold massNormalized
  have hc : (8 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := by positivity
  have hceil : (8 / (3 * Real.pi ^ 2)) * (3 * Real.pi ^ 2 / 8) = 1 := by
    field_simp
  constructor
  · intro heq
    apply mul_left_cancel₀ hc
    rw [heq, hceil]
  · intro heq
    rw [heq, hceil]

theorem massNormalized_massCorner (usual : Fin 3 → Bool) :
    massNormalized (massCorner usual) = 1 := by
  rw [massNormalized_eq_one_iff, mass_massCorner]

theorem height_of_usualCount {n : ℕ} (hn : n ≤ 3) :
    ((n : ℝ) * 2 - 3) / 3 = 1 ∨ ((n : ℝ) * 2 - 3) / 3 = 1 / 3 ∨
      ((n : ℝ) * 2 - 3) / 3 = -(1 / 3) ∨ ((n : ℝ) * 2 - 3) / 3 = -1 := by
  obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  · right; right; right; norm_num
  · right; right; left; norm_num
  · right; left; norm_num
  · left; norm_num

/-- At the mass ceiling every axis is a corner, so the configuration is one
of the eight corner points. -/
theorem mass_ceiling_axis_corner {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hM : mass p = 3 * Real.pi ^ 2 / 8) (a : Fin 3) :
    IsUsualCorner p a ∨ IsDualCorner p a :=
  axis_rigidity_of_mass_eq_max hp hM a

private theorem eq_massCorner_of_bools {p : TorsionParams} {usual : Fin 3 → Bool}
    (h : ∀ a, if usual a = true then IsUsualCorner p a else IsDualCorner p a) :
    p = massCorner usual := by
  refine torsionParams_ext ?_ ?_
  · funext a
    cases ha : usual a
    · have hc : IsDualCorner p a := by
        have := h a
        simp [ha] at this
        exact this
      simp [massCorner, ha, hc.1]
    · have hc : IsUsualCorner p a := by
        have := h a
        simp [ha] at this
        exact this
      simp [massCorner, ha, hc.1]
  · funext a
    cases ha : usual a
    · have hc : IsDualCorner p a := by
        have := h a
        simp [ha] at this
        exact this
      simp [massCorner, ha, hc.2]
    · have hc : IsUsualCorner p a := by
        have := h a
        simp [ha] at this
        exact this
      simp [massCorner, ha, hc.2]

theorem exists_massCorner_of_mass_eq_max {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    ∃ usual : Fin 3 → Bool, p = massCorner usual := by
  have c0 := mass_ceiling_axis_corner hp hM 0
  have c1 := mass_ceiling_axis_corner hp hM 1
  have c2 := mass_ceiling_axis_corner hp hM 2
  rcases c0 with c0 | c0 <;> rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
  · refine ⟨fun _ => true, eq_massCorner_of_bools ?_⟩
    intro a
    fin_cases a
    · simp [c0]
    · simp [c1]
    · simp [c2]
  · refine ⟨fun b => decide (b ≠ 2), eq_massCorner_of_bools ?_⟩
    intro a
    fin_cases a
    · have hb : ((0 : Fin 3) ≠ 2) = true := by decide
      simpa [hb] using c0
    · have hb : ((1 : Fin 3) ≠ 2) = true := by decide
      simpa [hb] using c1
    · have hb : ((2 : Fin 3) ≠ 2) = false := by decide
      simpa [hb] using c2
  · refine ⟨fun b => decide (b ≠ 1), eq_massCorner_of_bools ?_⟩
    intro a
    fin_cases a
    · have hb : ((0 : Fin 3) ≠ 1) = true := by decide
      simpa [hb] using c0
    · have hb : ((1 : Fin 3) ≠ 1) = false := by decide
      simpa [hb] using c1
    · have hb : ((2 : Fin 3) ≠ 1) = true := by decide
      simpa [hb] using c2
  · refine ⟨fun b => decide (b = 0), eq_massCorner_of_bools ?_⟩
    intro a
    fin_cases a
    · have hb : ((0 : Fin 3) = 0) = true := by decide
      simpa [hb] using c0
    · have hb : ((1 : Fin 3) = 0) = false := by decide
      simpa [hb] using c1
    · have hb : ((2 : Fin 3) = 0) = false := by decide
      simpa [hb] using c2
  · refine ⟨fun b => decide (b ≠ 0), eq_massCorner_of_bools ?_⟩
    intro a
    fin_cases a
    · have hb : ((0 : Fin 3) ≠ 0) = false := by decide
      simpa [hb] using c0
    · have hb : ((1 : Fin 3) ≠ 0) = true := by decide
      simpa [hb] using c1
    · have hb : ((2 : Fin 3) ≠ 0) = true := by decide
      simpa [hb] using c2
  · refine ⟨fun b => decide (b = 1), eq_massCorner_of_bools ?_⟩
    intro a
    fin_cases a
    · have hb : ((0 : Fin 3) = 1) = false := by decide
      simpa [hb] using c0
    · have hb : ((1 : Fin 3) = 1) = true := by decide
      simpa [hb] using c1
    · have hb : ((2 : Fin 3) = 1) = false := by decide
      simpa [hb] using c2
  · refine ⟨fun b => decide (b = 2), eq_massCorner_of_bools ?_⟩
    intro a
    fin_cases a
    · have hb : ((0 : Fin 3) = 2) = false := by decide
      simpa [hb] using c0
    · have hb : ((1 : Fin 3) = 2) = false := by decide
      simpa [hb] using c1
    · have hb : ((2 : Fin 3) = 2) = true := by decide
      simpa [hb] using c2
  · refine ⟨fun _ => false, eq_massCorner_of_bools ?_⟩
    intro a
    fin_cases a
    · simp [c0]
    · simp [c1]
    · simp [c2]

theorem JNormalized_mass_ceiling_height {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    ∃ n : ℕ, n ≤ 3 ∧ JNormalized p = ((n : ℝ) * 2 - 3) / 3 := by
  obtain ⟨usual, rfl⟩ := exists_massCorner_of_mass_eq_max hp hM
  exact ⟨usualCount usual, usualCount_le_three usual, JNormalized_massCorner usual⟩

theorem JNormalized_mass_ceiling_four {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    JNormalized p = 1 ∨ JNormalized p = 1 / 3 ∨
      JNormalized p = -(1 / 3) ∨ JNormalized p = -1 := by
  obtain ⟨n, hn, hJ⟩ := JNormalized_mass_ceiling_height hp hM
  rw [hJ]
  exact height_of_usualCount hn

theorem mass_ceiling_not_balance {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    Logic.ofParams p hp ≠ .T := by
  intro hT
  have hJ0 : JNormalized p = 0 := (Logic.ofParams_eq_T_iff hp).mp hT
  have hfour := JNormalized_mass_ceiling_four hp hM
  rcases hfour with h | h | h | h <;> linarith

theorem mass_ceiling_eq_F_iff {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (_hM : mass p = 3 * Real.pi ^ 2 / 8) :
    Logic.ofParams p hp = .F ↔ JNormalized p = 1 := by
  rw [Logic.ofParams_eq_F_iff]

theorem mass_ceiling_eq_U_iff {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    Logic.ofParams p hp = .U ↔ JNormalized p = 1 / 3 := by
  have hfour := JNormalized_mass_ceiling_four hp hM
  rw [Logic.ofParams_eq_U_iff]
  constructor
  · intro ⟨hpos, hlt⟩
    rcases hfour with h | h | h | h
    · linarith
    · exact h
    · linarith
    · linarith
  · intro h
    exact ⟨by linarith, by linarith⟩

theorem mass_ceiling_eq_B_iff {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    Logic.ofParams p hp = .B ↔ JNormalized p = -(1 / 3) ∨ JNormalized p = -1 := by
  have hfour := JNormalized_mass_ceiling_four hp hM
  rw [Logic.ofParams_eq_B_iff]
  constructor
  · intro ⟨hle, hlt⟩
    rcases hfour with h | h | h | h
    · linarith
    · linarith
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    rcases h with h | h
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩

theorem massNormalized_le_five_sixths_of_balance {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hT : Logic.ofParams p hp = .T) :
    massNormalized p ≤ 5 / 6 := by
  have hJ : J p = 0 :=
    (JNormalized_eq_zero_iff p).mp ((Logic.ofParams_eq_T_iff hp).mp hT)
  have hM := mass_le_shield_ceiling hp hJ
  unfold massNormalized
  calc
    (8 / (3 * Real.pi ^ 2)) * mass p
        ≤ (8 / (3 * Real.pi ^ 2)) * (5 * Real.pi ^ 2 / 16) := by gcongr
    _ = 5 / 6 := by
      field_simp
      norm_num

theorem massNormalized_maximalShield : massNormalized maximalShield = 5 / 6 := by
  unfold massNormalized
  rw [mass_maximalShield]
  field_simp
  norm_num

theorem ofParams_maximalShield :
    Logic.ofParams maximalShield isAdmissibleContinuous_maximalShield = .T := by
  rw [Logic.ofParams_eq_T_iff, JNormalized_eq_zero_iff, J_maximalShield]

theorem dagger_massCorner (usual : Fin 3 → Bool) :
    daggerParams (massCorner usual) = massCorner (fun a => !usual a) := by
  refine torsionParams_ext ?_ ?_
  · funext a
    cases ha : usual a <;> simp [daggerParams, massCorner, ha]
  · funext a
    cases ha : usual a <;> simp [daggerParams, massCorner, ha]

theorem usualCount_compl (usual : Fin 3 → Bool) :
    usualCount (fun a => !usual a) + usualCount usual = 3 := by
  rw [usualCount_eq_bits, usualCount_eq_bits]
  cases usual 0 <;> cases usual 1 <;> cases usual 2 <;> decide

theorem usualCount_dagger (usual : Fin 3 → Bool) :
    usualCount (fun a => !usual a) = 3 - usualCount usual := by
  have h := usualCount_compl usual
  omega

/-- Sector swap preserves the mass ceiling and sends height `(2n-3)/3` to
its negative, exchanging `n` pure boosts with `3-n`. -/
theorem dagger_mass_ceiling {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    IsAdmissibleContinuous (daggerParams p) ∧
      mass (daggerParams p) = 3 * Real.pi ^ 2 / 8 ∧
      JNormalized (daggerParams p) = -JNormalized p := by
  refine ⟨Logic.isAdmissibleContinuous_dagger hp, ?_, JNormalized_dagger p⟩
  rw [mass_dagger, hM]

theorem saturated_attraction_has_mass_ceiling {p : TorsionParams}
    (hp : IsAdmissibleContinuous p) (hF : Logic.ofParams p hp = .F) :
    mass p = 3 * Real.pi ^ 2 / 8 ∧ massNormalized p = 1 ∧ JNormalized p = 1 := by
  have hpure : IsPureHyperbolic p := (Logic.ofParams_F_iff_pureHyperbolic hp).mp hF
  have hJ : JNormalized p = 1 := (Logic.ofParams_eq_F_iff hp).mp hF
  have hM : mass p = 3 * Real.pi ^ 2 / 8 := by
    rw [mass_coef]
    simp only [Fin.sum_univ_three]
    have h0 := hpure 0
    have h1 := hpure 1
    have h2 := hpure 2
    simp [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
    ring
  refine ⟨hM, ?_, hJ⟩
  rw [massNormalized_eq_one_iff, hM]

end Gravity

end DstDiophantine
