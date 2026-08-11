# DstDiophantine

Discrete biquaternionic double spacetime (DST) の Lean 4 形式化プロジェクト。

論文 [`References/dst-diophantine.tex`](References/dst-diophantine.tex) と
[`References/dst-pga.tex`](References/dst-pga.tex) の主張を段階的に機械検証します。
全体ロードマップは [`PLAN.md`](PLAN.md) を参照してください。

## ビルド

```bash
lake update
lake build
```

Lean 4.34.0-rc1 と mathlib `v4.34.0-rc1` を使用します。

## フェーズ1 API（概要）

`DstDiophantine.Algebra` に `G(3,1,1)` のコア代数を実装しています。

- `Q311` / `PGA` — 5次元クリフォード代数
- `Generators` — 双曲・循環・ヌル10生成子（`N_μ N_ν = 0` 証明済み）
- `Operations` — reverse / dual / dagger
- `Motor` — `Ω` 分解、本物の `rotorTorsion = exp(Ω_torsion)`、`motor_unitary` 証明済み
- `Invariant` — `J` / `J⁽⁵⁾` / `JNormalized`（許容配置上の有界性 `|J| ≤ 3π²/8`、正規化版 `|JNormalized| ≤ 1` 証明済み）

## フェーズ2 インフラ（Discrete API）

- `Discrete.lean` — 離散ラピディティ `(ℤ/Nℤ)⁶` と主枝条件 `IsPrincipalBranch`
- `UnitGroup.lean` — 離散ローター像 `DiscreteUnit`（有限集合）
- `PGA/Normed.lean` — Banach 代数構造（`NormedSpace.exp` 用）
- `Amplification.lean` — スケーリング増幅 `J_scale`、`J_pow_amplify`（純双曲模型）
- `Continuum.lean` — 連続許容領域と離散近似 `exists_discrete_approx`
- `Invariant.lean` — `J5_unbounded` / `J5_bound_spatial`（並進拘束付き有界性）

## フェーズ3 整数埋め込み（Embedding API）

- `IntegerRotor.lean` — `R(n) = exp(log|n| · iI)`、乗法・冪乗
- `NullTranslator.lean` — `T(a)`、加法忠実性
- `PowerMap.lean` — 整数不一致モデルでの `p²` 増幅
- `RotorClass.lean` — 離散トーラス代表・量子化 API
- `Height.lean` — `integerHeight`、`descentCandidate`
- `Equation.lean` — `diophantineMotor`、加法式の忠実埋め込み

## フェーズ4 統一枠組み（Framework API）

- `Representation.lean` — 冪和方程式 `powerSumMotor`（`=1 ↔ eval=0`）
- `Lattice.lean` — 許容格子 `AdmissibleClass`、零高さの整数判定
- `Descent.lean` — dagger 高さ保存（論文ギャップ）と `DescentSchema`
- `Search.lean` — `findZeroHeight`、有限探索の終了・決定可能性

## フェーズ5 個別定理（Theorems API）

- `Fermat.lean` — FLT の DST 増幅核（`fermat_amplification_contradiction`、離散高さ下限、条件付き `fermat_last_theorem_of_bridge`）。古典 FLT の無条件主張は論文ギャップのため置かない。Beal は未着手。
