import DstDiophantine.Gravity.SI
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.nativeDecide false

/-!
# Exploratory hypothesis: discrete height → fine-structure coupling

## Paper boundary (do **not** claim)

DST does **not** derive the fine-structure constant \(\alpha\) from the dual
rotor algebra. Electromagnetic \(k,e,\alpha\) enter Sec.~electronshells as
external replacements for \((G,M,m)\). This module explores a **labelled
hypothesis** that pairs the shared lattice floor `SI.epsN` with CODATA \(\alpha\).

## Working hypothesis (not a derivation)

\[
\alpha_{\mathrm{hyp}}(N) = \varepsilon_N = \frac{16}{3N^2}.
\]

Matching CODATA \(\alpha\) yields \(N_*^2 = 16/(3\alpha)\). Numerically
\(729 = 27^2 < N_*^2 < 732 < 28^2\), so \(N_* \approx 27\).

No theorem asserts `dst_derives_alpha`. The gravitational
`impliedNsq` for the electron (\(\sim 10^{45}\)) is a *different* channel
(Planck-mass ratio) and must **not** be identified with this \(N_*\).
Dimensionless \(|J|\le 3\pi^2/8\) must not be conflated with \(\alpha\).
-/

namespace DstDiophantine

namespace Gravity

open SI

/-- Same lattice floor as `G_hyp`; electromagnetic channel only. -/
abbrev alpha_hyp : ℕ → ℚ := epsN

/-- Inverse: \(N_*^2\) implied by \(\alpha_{\mathrm{hyp}}=\alpha_{\mathrm{CODATA}}\). -/
def impliedNsqEM : ℚ :=
  16 / (3 * fineStructureApprox)

/-- Cleared form: `impliedNsqEM = 16 · 10^αScale / (3 · αₘ)`. -/
def impliedNsqEM_num : ℕ := 16 * 10 ^ fineStructureScale

def impliedNsqEM_den : ℕ := 3 * fineStructureMantissa

theorem impliedNsqEM_eq_num_div_den :
    impliedNsqEM = (impliedNsqEM_num : ℚ) / (impliedNsqEM_den : ℚ) := by
  unfold impliedNsqEM impliedNsqEM_num impliedNsqEM_den
  unfold fineStructureApprox fineStructureMantissa fineStructureScale
  field_simp
  ring

private theorem impliedNsqEM_den_pos : (0 : ℚ) < (impliedNsqEM_den : ℚ) := by
  unfold impliedNsqEM_den fineStructureMantissa
  norm_num

private theorem rat_div_gt
    {num den k : ℕ} (hden : (0 : ℚ) < den) (hnat : k * den < num) :
    (k : ℚ) < (num : ℚ) / den := by
  rw [lt_div_iff₀ hden]
  exact_mod_cast hnat

private theorem rat_div_lt
    {num den k : ℕ} (hden : (0 : ℚ) < den) (hnat : num < k * den) :
    (num : ℚ) / den < (k : ℚ) := by
  rw [div_lt_iff₀ hden]
  exact_mod_cast hnat

private theorem impliedNsqEM_nat_bounds :
    impliedNsqEM_den * 729 < impliedNsqEM_num ∧
      impliedNsqEM_num < impliedNsqEM_den * 732 := by
  unfold impliedNsqEM_num impliedNsqEM_den fineStructureMantissa fineStructureScale
  exact ⟨by native_decide, by native_decide⟩

/-- Window: \(27^2 = 729 < N_*^2 < 732\). -/
theorem impliedNsqEM_bounds :
    (729 : ℚ) < impliedNsqEM ∧ impliedNsqEM < (732 : ℚ) := by
  rw [impliedNsqEM_eq_num_div_den]
  have ⟨hlo, hhi⟩ := impliedNsqEM_nat_bounds
  exact ⟨rat_div_gt impliedNsqEM_den_pos hlo,
    rat_div_lt impliedNsqEM_den_pos hhi⟩

/-- Between consecutive squares: \(27^2 < N_*^2 < 28^2\). -/
theorem impliedNsqEM_between_27_28_sq :
    (27 : ℚ) ^ 2 < impliedNsqEM ∧ impliedNsqEM < (28 : ℚ) ^ 2 := by
  have h := impliedNsqEM_bounds
  refine ⟨by convert h.1 using 1; norm_num, lt_trans h.2 (by norm_num)⟩

/-- On the SI stand-ins, \(\alpha_{\mathrm{hyp}}(1)/\alpha =\) `impliedNsqEM`. -/
theorem alpha_hyp_one_div_alpha (hα : fineStructureApprox ≠ 0) :
    alpha_hyp 1 / fineStructureApprox = impliedNsqEM := by
  unfold alpha_hyp epsN impliedNsqEM
  simp only [Nat.cast_one, one_pow]
  field_simp [hα]

/-- With \(N=1\), \(\varepsilon_1=16/3\) overshoots CODATA \(\alpha\) by \(>700\). -/
theorem alpha_hyp_one_overshoots :
    fineStructureApprox * (700 : ℚ) < alpha_hyp 1 := by
  have himp := impliedNsqEM_bounds.1
  have hα : fineStructureApprox ≠ 0 := ne_of_gt fineStructureApprox_pos
  have hratio := alpha_hyp_one_div_alpha hα
  have h700 : (700 : ℚ) < impliedNsqEM :=
    lt_trans (by norm_num : (700 : ℚ) < 729) himp
  calc fineStructureApprox * (700 : ℚ)
      < fineStructureApprox * impliedNsqEM :=
        mul_lt_mul_of_pos_left h700 fineStructureApprox_pos
    _ = alpha_hyp 1 := by
        rw [← hratio]; field_simp [hα]

/-- Algebraic identity: \(\alpha_{\mathrm{hyp}}(27) = 16/2187\). -/
theorem alpha_hyp_27_eq : alpha_hyp 27 = (16 : ℚ) / 2187 := by
  unfold alpha_hyp epsN; norm_num

/-- Relative proximity: \(\alpha_{\mathrm{hyp}}(27)/\alpha = N_*^2/27^2\), and
\(729 < N_*^2 < 732\) yields \(1 <\) ratio \(< 732/729\). -/
theorem alpha_hyp_27_close :
    fineStructureApprox < alpha_hyp 27 ∧
      alpha_hyp 27 < (732 : ℚ) / 729 * fineStructureApprox := by
  have hα : fineStructureApprox ≠ 0 := ne_of_gt fineStructureApprox_pos
  have hratio : alpha_hyp 27 / fineStructureApprox =
      impliedNsqEM / (27 : ℚ) ^ 2 := by
    unfold alpha_hyp epsN impliedNsqEM
    field_simp [hα]
    ring
  have hb := impliedNsqEM_bounds
  have h27sq : (27 : ℚ) ^ 2 = 729 := by norm_num
  constructor
  · -- 1 < ratio  ⟺  α < α_hyp(27)
    have : (1 : ℚ) < alpha_hyp 27 / fineStructureApprox := by
      rw [hratio, h27sq]
      exact (lt_div_iff₀ (by norm_num : (0 : ℚ) < 729)).mpr (by simpa using hb.1)
    simpa using (lt_div_iff₀ fineStructureApprox_pos).mp this
  · have : alpha_hyp 27 / fineStructureApprox < (732 : ℚ) / 729 := by
      rw [hratio, h27sq]
      exact (div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 729)
        (by norm_num : (0 : ℚ) < 729)).mpr (by simpa using hb.2)
    rwa [div_lt_iff₀ fineStructureApprox_pos] at this

end Gravity

end DstDiophantine
