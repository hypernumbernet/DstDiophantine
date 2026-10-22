import DstDiophantine.Gravity.TorsionalLayer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The length rule and the chaotic proton force, without circularity

## Paper boundary (do **not** claim)

The electromagnetic length `ℓ_E ∈ (386, 387)` fm, the Bohr radius
`a₀ ∈ (52917, 52918)` fm, and the separation window `1`–`2` fm of nucleons in a
nucleus are external inputs. Nothing here fixes `κ` or computes a binding.

## The ordering

1. *Isolated charge* is defined by the electromagnetic reading itself: a charge
   acts as an isolated charge toward a partner when no electromagnetic wall lies
   at or beyond their separation. Every separation larger than `2ℓ/π` is on the
   wall-free outer plateau (`γ_s > 0`), for any length `ℓ`.
2. The hydrogen proton and its electron at `a₀` satisfy it: `a₀ > 2ℓ_E/π`.
3. Two protons at a separation in `(1, 2)` fm do not: read at `ℓ_E`, that window
   already contains at least thirty electromagnetic walls (one in each branch
   `n = 31, …, 60`). The same holds at the alpha–gold head-on distance below
   `ℓ_E/2`: it is inside the first electromagnetic node.
   So a nuclear proton is not an isolated charge whichever length is tried;
   this does not use `λ = 1`.
4. Reading at the common length (`λ = 1`), the two-channel force is one layer
   sequence with prefactor `k e² − κ`: its walls are exactly the gravitational
   walls, and two separations in chambers of opposite sign push the middle
   proton the same way. The sign-cell structure survives the rule it justifies.
-/

namespace DstDiophantine

namespace Gravity

open Real Set

/-- On `[0, x₁)` the equal-scale factor is strictly positive. -/
theorem gammaSEqual_pos_below_root1 {x : ℝ} (h0 : 0 ≤ x) (h1 : x < resonanceRoot1) :
    0 < gammaSEqual x := by
  have hb := resonanceRoot1_sharp_bounds
  have hπ := pi_gt_three
  have hanti := strictAntiOn_gammaSEqual_even 0
  simp only [mul_zero, Nat.cast_zero, zero_mul, zero_add] at hanti
  have hxI : x ∈ Icc (0 : ℝ) π := ⟨h0, by linarith⟩
  have hrI : resonanceRoot1 ∈ Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
  have := hanti hxI hrI h1
  rwa [resonanceRoot1_gammaSEqual_zero] at this

/-- Wall-free outer plateau: for any length `ℓ > 0`, every separation beyond
`2ℓ/π` has `γ_s(ℓ/(2r)) > 0`. -/
theorem gammaSEqual_pos_beyond_two_ell_div_pi {ℓ r : ℝ} (hℓ : 0 < ℓ)
    (hr : 2 * ℓ / π < r) : 0 < gammaSEqual (ℓ / (2 * r)) := by
  have hπ := pi_pos
  have hb := resonanceRoot1_sharp_bounds
  have hr0 : 0 < r := lt_trans (by positivity) hr
  apply gammaSEqual_pos_below_root1 (by positivity)
  have h2ℓ : 2 * ℓ < r * π := (div_lt_iff₀ hπ).mp hr
  have : ℓ / (2 * r) < π / 4 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- Inside `ℓ/2` the phase exceeds `1 > x₁`: the separation is inward of the
first node. -/
theorem phase_gt_root1_of_lt_half {ℓ r : ℝ} (hr0 : 0 < r) (hr : r < ℓ / 2) :
    resonanceRoot1 < ℓ / (2 * r) := by
  have hb := resonanceRoot1_sharp_bounds
  have : 1 < ℓ / (2 * r) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  linarith [hb.2]

/-- Hydrogen: with `ℓ_E < 387` fm and `a₀ > 52917` fm, the Bohr radius lies on
the wall-free outer plateau of the electromagnetic length. -/
theorem hydrogen_isolated_charge {ℓE a₀ : ℝ} (hℓ0 : 0 < ℓE) (hℓ : ℓE < 387)
    (ha : 52917 < a₀) : 2 * ℓE / π < a₀ ∧ 0 < gammaSEqual (ℓE / (2 * a₀)) := by
  have hπ : (3 : ℝ) < π := pi_gt_three
  have h : 2 * ℓE / π < a₀ := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  exact ⟨h, gammaSEqual_pos_beyond_two_ell_div_pi hℓ0 h⟩

/-- Nuclear separations read at the electromagnetic length: for each branch
`31 ≤ n ≤ 60` there is an electromagnetic wall at a separation in `(1, 2)` fm.
The phases of these walls lie in the disjoint intervals `(nπ, nπ + π)`, so the
window carries at least thirty walls. -/
theorem nuclear_window_em_walls {ℓE : ℝ} (hlo : 386 < ℓE) (hhi : ℓE < 387)
    (n : ℕ) (hn1 : 31 ≤ n) (hn2 : n ≤ 60) :
    ∃ r ∈ Ioo (1 : ℝ) 2, gammaSEqual (ℓE / (2 * r)) = 0 ∧
      ℓE / (2 * r) ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π) := by
  obtain ⟨x, ⟨hxI, hx0⟩, -⟩ := exists_unique_node_branch n
  have hp1 := pi_gt_d2
  have hp2 := pi_lt_d2
  have hn1' : (31 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn2' : (n : ℝ) ≤ 60 := by exact_mod_cast hn2
  obtain ⟨hxa, hxb⟩ := hxI
  have hxlo : 97 < x := by nlinarith
  have hxhi : x < 193 := by nlinarith
  have hx : 0 < x := by linarith
  refine ⟨ℓE / (2 * x), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · have : ℓE / (2 * (ℓE / (2 * x))) = x := by field_simp
    rw [this]; exact hx0
  · have : ℓE / (2 * (ℓE / (2 * x))) = x := by field_simp
    rw [this]; exact ⟨hxa, hxb⟩

/-- Every separation of at most `2` fm (in particular the alpha–gold head-on
distance below `30` fm, and every nucleon separation) is inward of the first
electromagnetic node when read at `ℓ_E > 386` fm. -/
theorem below_193_inside_first_em_node {ℓE r : ℝ} (hlo : 386 < ℓE)
    (hr0 : 0 < r) (hr : r < 193) : resonanceRoot1 < ℓE / (2 * r) :=
  phase_gt_root1_of_lt_half hr0 (by linarith)

/-- At the common length (`λ = 1`) the two-channel force is one layer sequence
with prefactor `k e² − κ`. -/
theorem twoChannel_common_length (κ ke2 g r : ℝ) :
    -κ / (g * r ^ 2) + ke2 / (g * r ^ 2) = (ke2 - κ) / (g * r ^ 2) := by
  ring

/-- At the common length the walls are exactly the gravitational walls:
for `k e² ≠ κ` and `r ≠ 0`, the net force vanishes nowhere and its sign on a
chamber is the sign of `(k e² − κ) γ_s`. -/
theorem twoChannel_common_length_sign {κ ke2 g r : ℝ} (hr : r ≠ 0) (hg : g ≠ 0) :
    0 < (ke2 - κ) / (g * r ^ 2) ↔ 0 < (ke2 - κ) * g := by
  have hd : 0 < g ^ 2 * r ^ 2 := by positivity
  have he : (ke2 - κ) / (g * r ^ 2) = ((ke2 - κ) * g) / (g ^ 2 * r ^ 2) := by
    field_simp
  rw [he]
  exact div_pos_iff_of_pos_right hd

/-- The sign-cell step: if the left separation of a middle proton lies in an
inward chamber and the right one in an outward chamber, both partners push it
the same way. -/
theorem middle_proton_same_direction {Fs Ft : ℝ} (hs : Fs < 0) (ht : 0 < Ft) :
    Fs - Ft < 0 := by linarith

/-! ### The slow charged entrance at the common length -/

/-- At the common length the Coulomb factor of a nuclear pair is the static
equal-scale factor at the same phase; on the entrance window `π/4 < x < x₁`
it is strictly positive. The positivity assumed for the slow charged entrance
holds there with no ordering of two lengths. -/
theorem cold_window_coulomb_factor_pos {x : ℝ} (h0 : π / 4 < x)
    (h1 : x < resonanceRoot1) : 0 < gammaSEqual x :=
  gammaSEqual_pos_below_root1 (by linarith [pi_pos]) h1

/-- For a positive Coulomb factor `γ_E` and finite `ρ > 0`, the net coefficient
`-1/γ + ρ/γ_E` is negative whenever `0 < γ < γ_E/ρ`: an interval abutting the
threshold from below on which the nuclear term exceeds the Coulomb term. -/
theorem cold_net_inward {γ γE ρ : ℝ} (hE : 0 < γE) (hρ : 0 < ρ) (hγ : 0 < γ)
    (hlt : γ < γE / ρ) : -1 / γ + ρ / γE < 0 := by
  have h1 : γ * ρ < γE := by rwa [lt_div_iff₀ hρ] at hlt
  have : ρ / γE < 1 / γ := by
    rw [div_lt_div_iff₀ hE hγ]; linarith
  have : -1 / γ = -(1 / γ) := by ring
  linarith

/-- Two like charges held in an octahedral hole about `2 Å = 2·10⁵` fm apart
are beyond `2ℓ_E/π`: the seat is read at the electromagnetic length. -/
theorem octahedral_seat_isolated {ℓE : ℝ} (hℓ0 : 0 < ℓE) (hℓ : ℓE < 387) :
    0 < gammaSEqual (ℓE / (2 * 200000)) := by
  have hπ : (3 : ℝ) < π := pi_gt_three
  apply gammaSEqual_pos_beyond_two_ell_div_pi hℓ0
  rw [div_lt_iff₀ (by linarith)]; nlinarith

/-- Nucleon separations of at least `1` fm, read at `λ_π < 71/50` fm, lie
beyond the wall `2λ_π/π`, on the outer attractive chamber. -/
theorem nucleon_window_outer_chamber {ℓ r : ℝ} (hℓ0 : 0 < ℓ) (hℓ : ℓ < 71 / 50)
    (hr : 1 ≤ r) : 2 * ℓ / π < r ∧ 0 < gammaSEqual (ℓ / (2 * r)) := by
  have hπ : (3 : ℝ) < π := pi_gt_three
  have h : 2 * ℓ / π < r := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  exact ⟨h, gammaSEqual_pos_beyond_two_ell_div_pi hℓ0 h⟩

end Gravity

end DstDiophantine
