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
- `Motor` — `Ω` 分解、ヌル指数の一次打ち切り
- `Invariant` — `J` / `J⁽⁵⁾`（`|J| ≤ 1` はフェーズ2）
