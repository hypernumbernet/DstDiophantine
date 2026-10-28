import DstDiophantine.Theorems.Goldbach
import DstDiophantine.Theorems.Polignac

set_option linter.style.native false

/-!
# One phase for the additive prime problems

Goldbach and Polignac are two channels of one prime pair. For primes `p ≤ q`
the rapidity is `δ = log(q/p)`, the relative rotor is the pure boost of angle
`2δ`, and the mismatch is `J = 2δ²`. The sum `n = p + q` and the half-gap
`k = (q - p)/2` obey

`(n/2)² - k² = pq`,

which is `cosh²(δ/2) - sinh²(δ/2) = 1` written on the two channels

`n/2 = √(pq) cosh(δ/2)`, `k = √(pq) sinh(δ/2)`.

Equal primes close the gap channel (`k = 0`, `δ = 0`). Every unequal pair is
at once a Goldbach decomposition of `n` and a Polignac pair of gap `2k`, with
the same rapidity and the same mismatch. The classical conjectures ask
different questions of this one family, and neither is claimed.
-/

namespace DstDiophantine

namespace Theorems

open Real

/-- Half the gap `q - p`, as an integer. Truncates when `q < p`. -/
def halfGap (p q : ℕ) : ℕ :=
  (q - p) / 2

/-- The sum and the signed half-gap of any two naturals lie on one hyperbola. -/
theorem additive_phase_relation (p q : ℕ) :
    ((p + q : ℝ) / 2) ^ 2 - (((q : ℝ) - (p : ℝ)) / 2) ^ 2 = (p : ℝ) * q := by
  ring

/-- The Goldbach and Polignac rapidities are the same number. -/
theorem primePair_rapidity_eq {p q k : ℕ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hk : q = p + 2 * k) :
    goldbachRapidity p q hp hq = polignacRapidity p k hp := by
  unfold goldbachRapidity polignacRapidity
  rw [hk]

/-- The Goldbach and Polignac mismatches are the same scalar. -/
theorem primePair_mismatch_eq {p q k : ℕ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hk : q = p + 2 * k) :
    goldbachMismatch p q hp hq = polignacMismatch p k hp := by
  unfold goldbachMismatch polignacMismatch
  rw [primePair_rapidity_eq hp hq hk]

/-- The normalised heights of the two channels agree. -/
theorem primePair_mismatchHeight_eq {p q k : ℕ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hk : q = p + 2 * k) :
    goldbachMismatchHeight p q hp hq = polignacMismatchHeight p k hp := by
  unfold goldbachMismatchHeight polignacMismatchHeight
  rw [primePair_rapidity_eq hp hq hk]

/-- A Polignac pair is the Goldbach decomposition of its sum. -/
theorem polignac_is_goldbach {p k : ℕ} (h : IsPolignacPair p k) :
    IsGoldbachPair p (p + 2 * k) (2 * (p + k)) := by
  obtain ⟨hp, hq, hk⟩ := h
  have htwo : 2 ≤ p := hp.two_le
  refine ⟨hp, hq, ?_, even_two_mul (p + k), ?_⟩
  · omega
  · omega

/-- An unequal Goldbach pair is the Polignac pair of half-gap `(q - p) / 2`. -/
theorem goldbach_unequal_is_polignac {p q n : ℕ}
    (h : IsGoldbachPair p q n) (hlt : p < q) :
    IsPolignacPair p (halfGap p q) ∧ q = p + 2 * halfGap p q ∧ n = p + q := by
  have hsum : p + q = n := h.2.2.1
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    rcases Nat.Prime.eq_two_or_odd h.2.1 with hq2 | hqodd
    · omega
    · have hneven : n % 2 = 0 := Nat.even_iff.mp h.2.2.2.1
      have hodd : (p + q) % 2 = 1 := by omega
      rw [hsum] at hodd
      omega
  have hq_ne_two : q ≠ 2 := by
    have hp2 : 2 ≤ p := h.1.two_le
    omega
  rcases Nat.Prime.eq_two_or_odd h.1 with hp2 | hpodd
  · exact absurd hp2 hp_ne_two
  rcases Nat.Prime.eq_two_or_odd h.2.1 with hq2 | hqodd
  · exact absurd hq2 hq_ne_two
  have hevenGap : Even (q - p) :=
    even_gap_of_odd_nats hpodd hqodd (le_of_lt hlt)
  have hdvd : 2 ∣ q - p := even_iff_two_dvd.mp hevenGap
  have hmul : 2 * halfGap p q = q - p := by
    unfold halfGap
    exact Nat.mul_div_cancel' hdvd
  have hqeq : q = p + 2 * halfGap p q := by omega
  have hkpos : 0 < halfGap p q := by
    unfold halfGap
    omega
  refine ⟨⟨h.1, ?_, hkpos⟩, hqeq, hsum.symm⟩
  rw [← hqeq]
  exact h.2.1

/-- Equal primes are the vacuum of the same hyperbola: the gap channel is closed. -/
theorem goldbach_vacuum_phase {p : ℕ} (hp : Nat.Prime p) :
    ((2 * p : ℕ) : ℝ) / 2 = (p : ℝ) ∧
      goldbachMismatch p p hp.ne_zero hp.ne_zero = 0 ∧
      (((2 * p : ℕ) : ℝ) / 2) ^ 2 - (0 : ℝ) ^ 2 = (p : ℝ) * p := by
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    ring
  · rw [goldbachMismatch_eq]
    unfold goldbachRapidity
    ring
  · push_cast
    ring

/--
The two additive channels are one relation. For a Polignac pair the sum channel
and the gap channel are the hyperbolic cosine and sine of one rapidity, the
hyperbola `(n/2)² - k² = pq` is `cosh² - sinh² = 1`, and the mismatches agree.
-/
theorem additive_phase_one_relation {p k : ℕ} (h : IsPolignacPair p k) :
    let q : ℕ := p + 2 * k
    let n : ℕ := p + q
    let δ : ℝ := polignacRapidity p k (Nat.Prime.ne_zero h.1)
    (n : ℝ) / 2 = Real.sqrt ((p : ℝ) * q) * Real.cosh (δ / 2) ∧
      (k : ℝ) = Real.sqrt ((p : ℝ) * q) * Real.sinh (δ / 2) ∧
      ((n : ℝ) / 2) ^ 2 - (k : ℝ) ^ 2 = (p : ℝ) * q ∧
      goldbachRapidity p q (Nat.Prime.ne_zero h.1) (Nat.Prime.ne_zero h.2.1) = δ ∧
      goldbachMismatch p q (Nat.Prime.ne_zero h.1) (Nat.Prime.ne_zero h.2.1) =
        polignacMismatch p k (Nat.Prime.ne_zero h.1) ∧
      goldbachMismatchHeight p q (Nat.Prime.ne_zero h.1) (Nat.Prime.ne_zero h.2.1) =
        polignacMismatchHeight p k (Nat.Prime.ne_zero h.1) := by
  intro q n δ
  have hp : 0 < p := Nat.Prime.pos h.1
  have hqpos : 0 < q := Nat.Prime.pos h.2.1
  have hqeq : q = p + 2 * k := rfl
  have hrap :
      goldbachRapidity p q (Nat.Prime.ne_zero h.1) (Nat.Prime.ne_zero h.2.1) = δ :=
    primePair_rapidity_eq (Nat.Prime.ne_zero h.1) (Nat.Prime.ne_zero h.2.1) hqeq
  have hsinh : (k : ℝ) = Real.sqrt ((p : ℝ) * q) * Real.sinh (δ / 2) := by
    simpa [q, δ] using polignac_equation_of_state h
  have hcosh : (n : ℝ) / 2 =
      Real.sqrt ((p : ℝ) * q) * Real.cosh (δ / 2) := by
    have h := goldbach_equation_of_state hp hqpos
    calc
      (n : ℝ) / 2 = ((p + q : ℕ) : ℝ) / 2 := by dsimp [n]
      _ = (p + q : ℝ) / 2 := by push_cast ; rfl
      _ = (2 * Real.sqrt ((p : ℝ) * q) *
            Real.cosh (goldbachRapidity p q (Nat.pos_iff_ne_zero.mp hp)
              (Nat.pos_iff_ne_zero.mp hqpos) / 2)) / 2 := by
            rw [h]
      _ = Real.sqrt ((p : ℝ) * q) * Real.cosh (δ / 2) := by
            rw [show goldbachRapidity p q (Nat.pos_iff_ne_zero.mp hp)
                (Nat.pos_iff_ne_zero.mp hqpos) = δ from hrap]
            ring
  have hnn : 0 ≤ (p : ℝ) * q := by positivity
  have hhyp : Real.cosh (δ / 2) ^ 2 - Real.sinh (δ / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (δ / 2)
  have hrel : ((n : ℝ) / 2) ^ 2 - (k : ℝ) ^ 2 = (p : ℝ) * q := by
    rw [hcosh, hsinh]
    calc
      (Real.sqrt ((p : ℝ) * q) * Real.cosh (δ / 2)) ^ 2 -
          (Real.sqrt ((p : ℝ) * q) * Real.sinh (δ / 2)) ^ 2
        = (Real.sqrt ((p : ℝ) * q)) ^ 2 *
            (Real.cosh (δ / 2) ^ 2 - Real.sinh (δ / 2) ^ 2) := by ring
      _ = (p : ℝ) * q := by
            rw [Real.sq_sqrt hnn, hhyp, mul_one]
  refine ⟨hcosh, hsinh, hrel, hrap, ?_, ?_⟩
  · simpa [q, δ] using
      primePair_mismatch_eq (Nat.Prime.ne_zero h.1) (Nat.Prime.ne_zero h.2.1) hqeq
  · simpa [q, δ] using
      primePair_mismatchHeight_eq (Nat.Prime.ne_zero h.1) (Nat.Prime.ne_zero h.2.1) hqeq

/-- An unequal Goldbach pair carries the same mismatch as its Polignac reading,
and the sum and the half-gap lie on the hyperbola. -/
theorem goldbach_unequal_same_phase {p q n : ℕ}
    (h : IsGoldbachPair p q n) (hlt : p < q) :
    IsPolignacPair p (halfGap p q) ∧
      goldbachRapidity p q h.1.ne_zero h.2.1.ne_zero =
        polignacRapidity p (halfGap p q) h.1.ne_zero ∧
      goldbachMismatch p q h.1.ne_zero h.2.1.ne_zero =
        polignacMismatch p (halfGap p q) h.1.ne_zero ∧
      ((n : ℝ) / 2) ^ 2 - ((halfGap p q : ℕ) : ℝ) ^ 2 = (p : ℝ) * q := by
  obtain ⟨hpol, hqeq, hn⟩ := goldbach_unequal_is_polignac h hlt
  have hrel0 := additive_phase_relation p q
  have hkcast : ((halfGap p q : ℕ) : ℝ) = ((q : ℝ) - (p : ℝ)) / 2 := by
    have hle : p ≤ q := le_of_lt hlt
    have hsub : q - p = 2 * halfGap p q := by omega
    calc
      ((halfGap p q : ℕ) : ℝ) = ((2 * halfGap p q : ℕ) : ℝ) / 2 := by
        push_cast
        ring
      _ = ((q - p : ℕ) : ℝ) / 2 := by rw [← hsub]
      _ = ((q : ℝ) - (p : ℝ)) / 2 := by rw [Nat.cast_sub hle]
  have hncast : (n : ℝ) = (p + q : ℝ) := by
    rw [hn]
    push_cast
    rfl
  refine ⟨hpol, ?_, ?_, ?_⟩
  · exact primePair_rapidity_eq h.1.ne_zero h.2.1.ne_zero hqeq
  · exact primePair_mismatch_eq h.1.ne_zero h.2.1.ne_zero hqeq
  · rw [hncast, hkcast]
    exact hrel0

end Theorems

end DstDiophantine
