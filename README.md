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

公開 API は `DstDiophantine.Basic`、層境界の回帰例は
`DstDiophantine.FoundationRegression` です。

## 三層アーキテクチャ（要約）

1. **加法忠実化** — 冪和型方程式 ↔ `powerSumMotor = 1`（証明済み）
2. **共通 no-go** — `k` 倍増幅 vs 許容有界性 / 粗格子下限（証明済み）
3. **問題別 bridge** — 整数解 ⇒ 増幅証明書（未証明；無条件古典主張はしない）

**重要:** 旧 `CoarseAmplificationWitness`（実スケール）は粗条件下で**構造的に空**
（`CoarseAmplificationWitness.empty_of_coarse`）。現行の乗法側基盤は
`Algebra.ModularAmplification`（`ZMod` 倍写 + 巻数誤差）です。

## PGA 論文との証明状態（要約）

| 主張 | 状態 |
|------|------|
| G(3,1,1)、10 生成子、`N_μ N_ν=0`、定義積 `M:=RT` 単位性 | 証明済み |
| `e₄` と `i` の可換、`dual` on hyperbolic/cyclic | 証明済み |
| null bivector の dual 閉性 | **棄却**（`dual_null` は grade 4） |
| `so(3,1)⊕so(3,1)` ラベル | **棄却**（正しくは `so(3,1)⋉ℝ^{3,1}` 候補） |
| `J⁽⁵⁾` パラメータ定義 / 非有界性 | 証明済み；ad-invariant は未主張 |
| 3-blade bracket / dual-as-normal | 未形式化・仮説 |
| Schwarzschild 対角テトラッド・誘導計量 | チャート証明済み（`Gravity.Schwarzschild`） |
| Weitzenböck `T` と発散形 | チャート証明済み（`Gravity.Weitzenbock`） |
| 動径ブースト尺度 ↔ redshift | 証明済み（`Gravity.Sandwich`） |
| 一般 `J⁵ ↔ T` / TEGR↔EH | 予想 / 据え置き |

## フェーズ 8（PGA–TEGR / Gravity）

`DstDiophantine.Gravity` にチャート固定の TEGR 骨格があります（`Basic` には強制 import しません）。

- `Coframe` / `Sandwich` — 誘導計量、動径ブースト尺度
- `Schwarzschild` — 外域対角テトラッドと Schwarzschild 計量
- `Weitzenbock` — ねじれ成分と `T = r⁻² DivClosed`
- `Identification` — 静的対角切片での `J`/`J⁵` と `T` の同定パッケージ

## フェーズ1 API（概要）

`DstDiophantine.Algebra` に `G(3,1,1)` のコア代数を実装しています。

- `Q311` / `PGA` — 5次元クリフォード代数
- `Generators` — 双曲・循環・ヌル10生成子（`N_μ N_ν = 0`、commutator API）
- `Operations` — reverse / dual / dagger（`e4_commute_pseudoscalar`, `dual_null`）
- `Motor` — `Ω` 分解、定義積 `motor := R*T`、`motor_unitary`
- `Invariant` — `J` / `J⁽⁵⁾` / `JNormalized`（許容配置上の有界性）

## フェーズ2–4

- Discrete / Continuum / UnitGroup / Amplification（実スケール）
- Embedding（`integerRotor`, `nullTranslator`, `quantizeInt` スケルトン）
- Framework（`Representation`, `Lattice`, `Amplification` no-go, `Descent`, `Search`）

## フェーズ5 個別定理（Theorems API）

いずれも条件付き（`*_of_bridge`）。古典予想の無条件主張は置かない。

- `Fermat.lean` — 加法同値・釣り合い障害・連続/旧粗離散（legacy）bridge
- `Beal.lean` / `Abc.lean` — `Framework.Amplification` 直利用
- `Collatz.lean` / `Goldbach.lean` / `Polignac.lean` / `Riemann.lean`
- 有限証明書: Collatz≤20, Goldbach≤100, abc≤100, RH≤20,
  Polignac 双子≤20 / gap4·6≤30

## フェーズ6–7（共有増幅 + modular 再設計）

- 旧 `FermatCoarseDiscreteBridge` は構造的空ペイロードの diagnostic / legacy
- `Algebra/ModularAmplification.lean` — 巻数恒等式・誤差項・非空 witness 例
- `FoundationRegression.lean` — 空性・modular inhabited・層境界を回帰
