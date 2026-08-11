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

## 論文ギャップ（有界性）

論文 Ch.3 の生の \(|J|\le 1\) は式 \(J=\frac12\sum(\alpha_a^2-\beta_a^2)\) と矛盾する（Appendix extremal で \(J=3\pi^2/8\)）。Lean では許容配置 `IsAdmissible` 上で \(\|J\|\le 3\pi^2/8\) と正規化 \(J_{\rm norm}=\frac{8}{3\pi^2}J\) の \(\|J_{\rm norm}\|\le 1\) を証明。`IsPrincipalBranch` のみでは非有界（`torsion_bound_naive_false`）。詳細は [`PLAN.md`](PLAN.md) を参照。

## 既知の `sorry`

現時点でフェーズ1–2 コア API に `sorry` はなし。
