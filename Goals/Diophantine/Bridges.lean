import DstDiophantine.Theorems.Abc
import DstDiophantine.Theorems.Collatz
import DstDiophantine.Theorems.Goldbach
import DstDiophantine.Theorems.Polignac
import DstDiophantine.Theorems.Riemann

/-!
# Live Diophantine bridges

A bridge is a target only when the main library still treats it as the live
path. Diagnostic, demoted, legacy, and disproved bridges are not targets;
see `Goals/README.md`.
-/

namespace Goals.Diophantine

open DstDiophantine.Theorems

/-- **Claim (EN):** The quantised log-gap of a high-quality abc triple is an
    admissible modular witness and is conformally gauge-admissible.

    **Claim (JA):** 品質の高い abc 三つ組の量子化された対数差は、許容的な
    モジュラー証拠であり、かつ共形ゲージでも許容的である。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open. The continuous bridge is false
    (`AbcAdmissibleBridge_false`). `abc_conjecture_of_modular_bridge` recovers
    the classical conjecture from this one.
-/
theorem abcModularBridge : AbcModularBridge := by sorry

/-- **Claim (EN):** A positive integer that never reaches 1 produces a Collatz
    cycle of normalised height at most 1.

    **Claim (JA):** 1 に到達しない正の整数は、正規化高さが 1 以下のコラッツ
    サイクルを生む。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open. Equivalent to the classical conjecture
    (`collatzAdmissibleBridge_iff`).
-/
theorem collatzAdmissibleBridge : CollatzAdmissibleBridge := by sorry

/-- **Claim (EN):** An even integer `n ≥ 4` with no Goldbach pair would make
    the pure boost of `n` admissible.

    **Claim (JA):** ゴールドバッハ対を持たない偶数 `n ≥ 4` は、`n` の純ブーストを
    許容的にする。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open. Equivalent to the classical conjecture
    (`goldbachAdmissibleBridge_iff`). For `n ≥ 4` that boost already leaves
    the cone, so the encoding is vacuous on the nose.
-/
theorem goldbachAdmissibleBridge : GoldbachAdmissibleBridge := by sorry

/-- **Claim (EN):** If pairs of gap `2k` are bounded, some admissible pure
    boost has chain height greater than 1.

    **Claim (JA):** 差 `2k` の対が有界なら、鎖の高さが 1 を超える許容的な
    純ブーストがある。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open. Equivalent to Polignac's conjecture
    (`polignacAdmissibleBridge_iff`). Twin primes are the case `k = 1`.
-/
theorem polignacAdmissibleBridge : PolignacAdmissibleBridge := by sorry

/-- **Claim (EN):** An off-critical real part produces an admissible continuous
    mismatch of strictly positive normalised height.

    **Claim (JA):** 臨界線から外れた実部は、正規化高さが正の許容的な連続
    ミスマッチを生む。

    **Paper:** `papers/dst-diophantine.tex`, Chapter 8.

    **Status:** open. This is the critical-line statement of this development,
    not mathlib's `riemannZeta`. `riemann_hypothesis_of_bridge` adds the
    zero-ensemble exclusion.
-/
theorem riemannAdmissibleBridge : RiemannAdmissibleBridge := by sorry

end Goals.Diophantine
