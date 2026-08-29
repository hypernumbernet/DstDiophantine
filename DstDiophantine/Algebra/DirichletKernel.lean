import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Normalised Dirichlet kernel on the dual-sector torus

The synchronisation factor
\[
D_N(\theta)=\frac{\sin(N\theta/2)}{N\sin(\theta/2)}
\]
has a removable singularity on the lattice \(\theta=2\pi k\). Filling those
points by the L'Hôpital value \(\cos(N\theta/2)/\cos(\theta/2)\) yields a
function bounded by \(1\) for every positive integer \(N\) (primality is
not required). Mass spectra and \(\prod_p p\) regularisation are not treated
here.
-/

namespace DstDiophantine

namespace DirichletKernel

open Real

/-- Normalised Dirichlet kernel with removable singularities filled. -/
noncomputable def dirichletKernel (N : ℕ) (θ : ℝ) : ℝ :=
  if sin (θ / 2) = 0 then
    cos (N * θ / 2) / cos (θ / 2)
  else
    sin (N * θ / 2) / (N * sin (θ / 2))

private theorem abs_sin_nat_mul_le (n : ℕ) (x : ℝ) :
    |sin (n * x)| ≤ n * |sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htrig : sin ((n + 1 : ℝ) * x) = sin (n * x) * cos x + cos (n * x) * sin x := by
      rw [add_mul, one_mul, sin_add]
    have : |sin ((n + 1 : ℝ) * x)| ≤ |sin (n * x)| + |sin x| := by
      rw [htrig]
      calc |sin (n * x) * cos x + cos (n * x) * sin x|
          ≤ |sin (n * x) * cos x| + |cos (n * x) * sin x| := abs_add_le _ _
        _ = |sin (n * x)| * |cos x| + |cos (n * x)| * |sin x| := by
              simp [abs_mul]
        _ ≤ |sin (n * x)| * 1 + 1 * |sin x| := by
              gcongr
              · exact abs_cos_le_one x
              · exact abs_cos_le_one (n * x)
        _ = |sin (n * x)| + |sin x| := by simp
    have : |sin ((n + 1) * x)| ≤ (n + 1) * |sin x| :=
      this.trans (by
        have := add_le_add ih (le_refl |sin x|)
        simpa [Nat.cast_succ, add_mul, one_mul] using this)
    simpa [Nat.cast_succ] using this

theorem dirichletKernel_of_sin_ne_zero {N : ℕ} {θ : ℝ}
    (h : sin (θ / 2) ≠ 0) :
    dirichletKernel N θ = sin (N * θ / 2) / (N * sin (θ / 2)) := by
  simp [dirichletKernel, h]

theorem dirichletKernel_of_sin_eq_zero {N : ℕ} {θ : ℝ}
    (h : sin (θ / 2) = 0) :
    dirichletKernel N θ = cos (N * θ / 2) / cos (θ / 2) := by
  simp [dirichletKernel, h]

theorem cos_half_ne_zero_of_sin_half_eq_zero {θ : ℝ}
    (h : sin (θ / 2) = 0) : cos (θ / 2) ≠ 0 := by
  have : sin (θ / 2) ^ 2 + cos (θ / 2) ^ 2 = 1 := sin_sq_add_cos_sq (θ / 2)
  intro hc
  rw [h, hc] at this
  norm_num at this

/-- At every lattice point \(\theta = 2\pi k\) one has \(D_N = \pm 1\). -/
theorem dirichletKernel_two_pi {N k : ℕ} :
    dirichletKernel N (2 * π * k) = (-1 : ℝ) ^ (k * (N + 1)) := by
  have hsin : sin ((2 * π * k) / 2) = 0 := by
    have : (2 * π * k) / 2 = k * π := by ring
    rw [this, sin_nat_mul_pi]
  rw [dirichletKernel_of_sin_eq_zero hsin]
  have hhalf : (2 * π * k) / 2 = k * π := by ring
  have hcos : cos ((2 * π * k) / 2) = (-1 : ℝ) ^ k := by
    rw [hhalf, cos_nat_mul_pi]
  have hNθ : N * (2 * π * k) / 2 = ((N * k : ℕ) : ℝ) * π := by
    push_cast
    ring
  have hcosN : cos (N * (2 * π * k) / 2) = (-1 : ℝ) ^ (N * k) := by
    rw [hNθ, cos_nat_mul_pi]
  rw [hcosN, hcos, div_eq_mul_inv]
  have hinv : ((-1 : ℝ) ^ k)⁻¹ = (-1 : ℝ) ^ k := by
    refine inv_eq_of_mul_eq_one_right ?_
    simp [← pow_add, ← two_mul, pow_mul]
  rw [hinv, ← pow_add]
  congr 1
  ring

theorem abs_dirichletKernel_lattice {N k : ℕ} :
    |dirichletKernel N (2 * π * k)| = 1 := by
  rw [dirichletKernel_two_pi, abs_neg_one_pow]

/-- \(|D_N(\theta)|\le 1\) for every positive integer \(N\). -/
theorem abs_dirichletKernel_le_one {N : ℕ} (hN : N ≠ 0) (θ : ℝ) :
    |dirichletKernel N θ| ≤ 1 := by
  by_cases hsin : sin (θ / 2) = 0
  · rw [dirichletKernel_of_sin_eq_zero hsin, abs_div]
    have habs : |cos (θ / 2)| = 1 := by
      have hsq : cos (θ / 2) ^ 2 = 1 := by
        have := sin_sq_add_cos_sq (θ / 2)
        simpa [hsin] using this
      have hx : |cos (θ / 2)| ^ 2 = 1 := by
        simpa [sq, abs_mul_abs_self] using hsq
      have hnn : 0 ≤ |cos (θ / 2)| := abs_nonneg _
      nlinarith [sq_nonneg (|cos (θ / 2)| - 1)]
    rw [habs, div_one]
    exact abs_cos_le_one (N * θ / 2)
  · rw [dirichletKernel_of_sin_ne_zero hsin, abs_div, abs_mul]
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hNnn : 0 ≤ (N : ℝ) := hNpos.le
    have hbound := abs_sin_nat_mul_le N (θ / 2)
    have : |sin (N * (θ / 2))| ≤ N * |sin (θ / 2)| := hbound
    have hden : 0 < (N : ℝ) * |sin (θ / 2)| :=
      mul_pos hNpos (abs_pos.mpr hsin)
    rw [abs_of_nonneg hNnn, div_le_one hden]
    simpa [mul_div_assoc] using this

end DirichletKernel

end DstDiophantine
