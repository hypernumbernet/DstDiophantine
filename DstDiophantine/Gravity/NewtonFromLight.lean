import DstDiophantine.Gravity.SI
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option linter.style.nativeDecide false

/-!
# Exploratory hypothesis: discrete height → Newton coupling

## Paper boundary (do **not** claim)

DST does **not** derive \(G\) from \(c\) alone. The action inserts \(G\) as an
external coupling; \(c\) alone lacks a mass dimension. This module explores a
**labelled hypothesis** that pairs the already-proved dimensionless lattice
floor \(\varepsilon_N = 16/(3N^2)\) (`Framework.discrete_nonzero_height_lb`)
with the Planck bridge \(G = \ell^2 c^3/\hbar\).

## Working hypothesis (not a derivation)

\[
G_{\mathrm{hyp}}(N,m) = \varepsilon_N\cdot\frac{\hbar c}{m^2}
  = \frac{16}{3N^2}\frac{\hbar c}{m^2}.
\]

If \(N \propto m\) then \(G_{\mathrm{hyp}}\) is species-independent. Taking
\(N = m_P/m\) yields exactly the factor \(16/3\) relative to CODATA \(G\).

No theorem asserts `dst_derives_G`. Numerics use `Gravity.SI` rationals only.
Dimensionless \(|J|\le 3\pi^2/8\) must not be conflated with
\(c^4/(G\,\ell_P^{-2})\) — see `Identification` docstring.
-/

namespace DstDiophantine

namespace Gravity

open SI

/-- Dimensionless discrete height \(\varepsilon_N = 16/(3N^2)\). -/
def epsN (N : ℕ) : ℚ := 16 / (3 * (N : ℚ) ^ 2)

theorem epsN_pos {N : ℕ} (hN : 0 < N) : (0 : ℚ) < epsN N := by
  unfold epsN
  have : (0 : ℚ) < (N : ℚ) := Nat.cast_pos.mpr hN
  positivity

/-- Hypothesised Newton constant from lattice height and reference mass. -/
def G_hyp (N : ℕ) (m : ℚ) : ℚ :=
  epsN N * hbarC / m ^ 2

/-- Inverse: \(N_*^2\) implied by \(G_{\mathrm{hyp}}=G_{\mathrm{CODATA}}\). -/
def impliedNsq (m : ℚ) : ℚ :=
  (16 / 3) * hbarC / (GApprox * m ^ 2)

/-- Planck-mass squared stand-in \(m_P^2 = \hbar c / G\). -/
def planckMassSqApprox : ℚ := hbarC / GApprox

/-- On the SI stand-ins, \(G_{\mathrm{hyp}}(1,m)/G =\) `impliedNsq m`. -/
theorem G_hyp_one_div_G (m : ℚ) (hm : m ≠ 0) (hG : GApprox ≠ 0) :
    G_hyp 1 m / GApprox = impliedNsq m := by
  unfold G_hyp epsN impliedNsq
  simp only [Nat.cast_one, one_pow]
  field_simp [hG, hm]

/-- Ratio \(G_{\mathrm{hyp}}/G\) on the SI stand-ins. -/
theorem G_hyp_div_G (N : ℕ) (m : ℚ) (hm : m ≠ 0) (hG : GApprox ≠ 0) :
    G_hyp N m / GApprox =
      (16 : ℚ) / 3 * (planckMassSqApprox / ((N : ℚ) ^ 2 * m ^ 2)) := by
  unfold G_hyp epsN planckMassSqApprox
  field_simp [hG, hm]

/-- If \(N^2 m^2 = m_P^2\), then \(G_{\mathrm{hyp}}/G = 16/3\) (algebraic identity). -/
theorem G_hyp_div_G_of_planckN {N : ℕ} {m : ℚ}
    (hm : m ≠ 0) (hG : GApprox ≠ 0)
    (hN : (N : ℚ) ^ 2 * m ^ 2 = planckMassSqApprox) :
    G_hyp N m / GApprox = (16 : ℚ) / 3 := by
  have hP : planckMassSqApprox ≠ 0 :=
    div_ne_zero (ne_of_gt hbarC_pos) hG
  rw [G_hyp_div_G N m hm hG, hN]
  field_simp [hP]

/-! ### Cleared-denominator witnesses

For mass \(m = M/10^s\),
`impliedNsq = (16 · ħₘ · c · 10^(2s+GScale−ħScale)) / (3 · Gₘ · M²)`,
with mantissas from `SI`.
-/

/-- Cleared numerator for mass scale \(s\) (`ħScale ≤ 2s + GScale`). -/
def impliedNumOf (massScale : ℕ) : ℕ :=
  16 * hbarMantissa * speedOfLightNat * 10 ^ (2 * massScale + GScale - hbarScale)

def impliedDenOf (massMantissa : ℕ) : ℕ :=
  3 * GMantissa * massMantissa ^ 2

def electronImpliedNum : ℕ := impliedNumOf electronMassScale
def electronImpliedDen : ℕ := impliedDenOf electronMassMantissa
def protonImpliedNum : ℕ := impliedNumOf protonMassScale
def protonImpliedDen : ℕ := impliedDenOf protonMassMantissa

theorem impliedNsq_electron_eq_num_div_den :
    impliedNsq electronMassApprox =
      (electronImpliedNum : ℚ) / (electronImpliedDen : ℚ) := by
  unfold impliedNsq electronMassApprox hbarC hbarApprox speedOfLight GApprox
  unfold electronImpliedNum electronImpliedDen impliedNumOf impliedDenOf
  unfold electronMassMantissa electronMassScale hbarMantissa hbarScale
    speedOfLightNat GMantissa GScale
  field_simp
  ring

theorem impliedNsq_proton_eq_num_div_den :
    impliedNsq protonMassApprox =
      (protonImpliedNum : ℚ) / (protonImpliedDen : ℚ) := by
  unfold impliedNsq protonMassApprox hbarC hbarApprox speedOfLight GApprox
  unfold protonImpliedNum protonImpliedDen impliedNumOf impliedDenOf
  unfold protonMassMantissa protonMassScale hbarMantissa hbarScale
    speedOfLightNat GMantissa GScale
  field_simp
  ring

private theorem rat_div_gt_pow
    {num den k e : ℕ} (hden : (0 : ℚ) < den)
    (hnat : k * 10 ^ e * den < num) :
    (k : ℚ) * 10 ^ e < (num : ℚ) / den := by
  rw [lt_div_iff₀ hden]
  exact_mod_cast hnat

private theorem rat_div_lt_pow
    {num den k e : ℕ} (hden : (0 : ℚ) < den)
    (hnat : num < k * 10 ^ e * den) :
    (num : ℚ) / den < (k : ℚ) * 10 ^ e := by
  rw [div_lt_iff₀ hden]
  exact_mod_cast hnat

private theorem electronImpliedDen_pos :
    (0 : ℚ) < (electronImpliedDen : ℚ) := by
  unfold electronImpliedDen impliedDenOf electronMassMantissa GMantissa
  norm_num

private theorem protonImpliedDen_pos :
    (0 : ℚ) < (protonImpliedDen : ℚ) := by
  unfold protonImpliedDen impliedDenOf protonMassMantissa GMantissa
  norm_num

/-- Electron: \(3\times 10^{45} < N_*^2 < 4\times 10^{45}\). -/
theorem impliedNsq_electron_bounds :
    (3 : ℚ) * 10 ^ 45 < impliedNsq electronMassApprox ∧
      impliedNsq electronMassApprox < (4 : ℚ) * 10 ^ 45 := by
  rw [impliedNsq_electron_eq_num_div_den]
  refine ⟨rat_div_gt_pow electronImpliedDen_pos ?_,
    rat_div_lt_pow electronImpliedDen_pos ?_⟩
  · unfold electronImpliedNum electronImpliedDen impliedNumOf impliedDenOf
    unfold electronMassMantissa electronMassScale hbarMantissa speedOfLightNat
      GMantissa GScale hbarScale
    native_decide
  · unfold electronImpliedNum electronImpliedDen impliedNumOf impliedDenOf
    unfold electronMassMantissa electronMassScale hbarMantissa speedOfLightNat
      GMantissa GScale hbarScale
    native_decide

/-- Electron window: \(55^2\cdot 10^{42} < N_*^2 < 56^2\cdot 10^{42}\). -/
theorem impliedNsq_electron_between_55_56_e22_sq :
    (55 : ℚ) ^ 2 * 10 ^ 42 < impliedNsq electronMassApprox ∧
      impliedNsq electronMassApprox < (56 : ℚ) ^ 2 * 10 ^ 42 := by
  rw [impliedNsq_electron_eq_num_div_den]
  have hden := electronImpliedDen_pos
  have h55 : (55 : ℚ) ^ 2 = 3025 := by norm_num
  have h56 : (56 : ℚ) ^ 2 = 3136 := by norm_num
  constructor
  · rw [h55]
    refine rat_div_gt_pow hden ?_
    unfold electronImpliedNum electronImpliedDen impliedNumOf impliedDenOf
    unfold electronMassMantissa electronMassScale hbarMantissa speedOfLightNat
      GMantissa GScale hbarScale
    native_decide
  · rw [h56]
    refine rat_div_lt_pow hden ?_
    unfold electronImpliedNum electronImpliedDen impliedNumOf impliedDenOf
    unfold electronMassMantissa electronMassScale hbarMantissa speedOfLightNat
      GMantissa GScale hbarScale
    native_decide

/-- Proton: \(9\times 10^{38} < N_*^2 < 10^{39}\). -/
theorem impliedNsq_proton_bounds :
    (9 : ℚ) * 10 ^ 38 < impliedNsq protonMassApprox ∧
      impliedNsq protonMassApprox < (10 : ℚ) ^ 39 := by
  rw [impliedNsq_proton_eq_num_div_den]
  have hden := protonImpliedDen_pos
  refine ⟨rat_div_gt_pow hden ?_, ?_⟩
  · unfold protonImpliedNum protonImpliedDen impliedNumOf impliedDenOf
    unfold protonMassMantissa protonMassScale hbarMantissa speedOfLightNat
      GMantissa GScale hbarScale
    native_decide
  · have : (10 : ℚ) ^ 39 = (1 : ℚ) * 10 ^ 39 := by ring
    rw [this]
    refine rat_div_lt_pow hden ?_
    unfold protonImpliedNum protonImpliedDen impliedNumOf impliedDenOf
    unfold protonMassMantissa protonMassScale hbarMantissa speedOfLightNat
      GMantissa GScale hbarScale
    native_decide

/-! ### Rejection labels -/

/-- With \(N=1\), the electron hypothesis overshoots CODATA \(G\) by \(>10^{44}\). -/
theorem G_hyp_one_electron_overshoots :
    GApprox * (10 : ℚ) ^ 44 < G_hyp 1 electronMassApprox := by
  have himp := impliedNsq_electron_bounds.1
  have hG : GApprox ≠ 0 := ne_of_gt GApprox_pos
  have hm : electronMassApprox ≠ 0 := ne_of_gt electronMassApprox_pos
  have hratio := G_hyp_one_div_G electronMassApprox hm hG
  have h44 : (10 : ℚ) ^ 44 < impliedNsq electronMassApprox :=
    lt_trans (by norm_num) himp
  calc GApprox * (10 : ℚ) ^ 44
      < GApprox * impliedNsq electronMassApprox :=
        mul_lt_mul_of_pos_left h44 GApprox_pos
    _ = G_hyp 1 electronMassApprox := by
        rw [← hratio]; field_simp [hG]

end Gravity

end DstDiophantine
