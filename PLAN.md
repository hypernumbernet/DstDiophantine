# PGA-DST ディオファントス証明基盤 — 研究計画

最終更新: 2026-08-13（Fermat modular bridge + 1D CGA 探針）

## 1. 三層アーキテクチャ

PGA-DST による証明手法を、次の三層に分離する。未証明の bridge を一般定理と混同しない。

```mermaid
flowchart LR
  Equation[整数方程式] --> Additive[加法null忠実化]
  Additive --> Bridge[問題別bridge証明書]
  Bridge --> NoGo[増幅と有界性の共通禁止定理]
  NoGo --> Result[条件付きまたは無条件の数論結果]
```

| 層 | 役割 | 状態 | 主な場所 |
|----|------|------|----------|
| **加法忠実化** | 冪和型方程式 ↔ `powerSumMotor = 1` | 証明済み | `Framework/Representation`, `Embedding/NullTranslator` |
| **共通 no-go** | `k` 倍増幅 vs 許容有界性 / 粗格子下限 | 証明済み（高さ版） | `Framework/Amplification`, `Algebra/Amplification` |
| **問題別 bridge** | 整数解 ⇒ 増幅証明書 | **未証明**（旧 coarse は構造的空；modular は型付け済） | 各 `Theorems/*.lean` の `*Bridge` |
| **modular 増幅** | `ZMod` 倍写と巻数誤差 | **基盤＋巻数/実スケールギャップ証明済** | `Algebra/ModularAmplification` |
| **1D CGA 探針** | 乗法 dilation / 斉次 null 点 | **診断層（Basic 非依存）** | `Algebra/CGA`, `Embedding/ConformalInteger` |

### 確立済み（機械検証済み・sorry なし）

- PGA / Cl(3,1) / ヌル強消滅 / 定義積モーター `M:=RT` の単位性
- `e₄` と pseudoscalar の可換、`dual_null`（grade 4；null bivector 閉性は**棄却**）
- 許容配置上の `|JNormalized| ≤ 1`（naive 全配置有界性は**反例付きで棄却**）
- 純ブーストの `k²` 増幅と連続種高さ上界
- 離散非零高さ下限 `ε_N = 16/(3N²)` と粗トーラス高さ no-go
- **旧 `CoarseAmplificationWitness` の構造的空性**（方程式非依存；`empty_of_coarse`）
- 加法 null 忠実性（Fermat / Beal / abc / Goldbach / Polignac の骨格）
- modular 巻数恒等式と `ModularAmplificationWitness` の具体例（`N=16,k=5`）
- **実スケール許容 ⇒ `windingTotal = 0`**（modular witness は連続 no-go に直接渡せない）
- `quantizeMismatch` / `quantizeInt` 補題とフロア誤差
- **`FermatModularBridge` の型付け**と条件付き FLT（解依存 payload；bridge 本体は未証明）
- 1D CGA `Cl(2,1)`: `X(x)² = 0`、dilation 重み、`integerHeight` 非有界診断
- 有限計算証明書（Collatz ≤20、Goldbach ≤100、abc ≤100、RH 有理格子 ≤20、
  Polignac 双子 ≤20 / gap4·6 ≤30）

### 未証明（明示的 bridge・無条件主張しない）

| Bridge | 問題 | 核との接続 | 備考 |
|--------|------|------------|------|
| `FermatModularBridge` | FLT（本命・modular） | 解依存 `quantizeMismatch` + 巻数 witness + 共形ギャップ | **型付け済・未証明**；`ConformalGaugeAdmissible` が残ギャップ |
| `FermatAdmissibleBridge` | FLT（連続・診断用） | 釣り合い型で偽になり得る | 診断専用 |
| `FermatCoarseDiscreteBridge` | FLT（旧粗離散） | ペイロードが構造的空 | legacy / 診断用（単純流用は空のまま） |
| `BealAdmissibleBridge` | Beal | 連続増幅 no-go | 旧 coarse の単純流用は空；modular は解依存 payload が要る |
| `AbcAdmissibleBridge` | abc | 品質天井 | 同上 |
| `CollatzAdmissibleBridge` | Collatz | 軌道・高さ | 別系列 |
| `GoldbachAdmissibleBridge` | Goldbach | 分解候補 | 別系列 |
| `PolignacAdmissibleBridge` | Polignac / 双子 | 強い回避 | 別系列 |
| `RiemannAdmissibleBridge` | RH | 臨界アンサンブル | 長期 |

### 反例で棄却済み（再設計しない）

- 主枝のみでの `|J| ≤ 1`（`torsion_bound_naive_false`）
- dagger による `J` 厳密減少（`dagger_preserves_height`）
- 現行連続 FLT 閾値「任意解 ⇒ 種 > 1/p²」（`fermat_balanced_seed_lt_threshold`）
- 許容錐への単純折り返し（`p²` 増幅破壊）
- `J5` 単独での bridge 閉鎖（解では `λ = 0`）
- **実スケール粗離散 witness**（`CoarseAmplificationWitness.empty_of_coarse`）
- **duality による null bivector sector 閉性**（`dual_null` は grade 4）
- 論文表現 `so(3,1)⊕so(3,1)`（6 生成子に対して次元不一致）

---

## 2. 問題類型と再利用パターン

| 類型 | 代表 | 加法 | 乗法 / 高さ | 次の数学課題 |
|------|------|------|-------------|--------------|
| **冪和増幅型** | FLT, Beal | null motor | modular 巻数誤差の下限 | 解 ⇒ modular witness |
| **品質型** | abc | null motor | `H = c₁(q−1)²` | 高品質 ⇒ modular / 許容配置 |
| **軌道型** | Collatz | — | ログ高さ単調 | 軌道 ⇔ 許容流 |
| **加法分解型** | Goldbach, Polignac | null motor | 候補最小 J / 過剰項 | 論理混同の解消 |
| **解析型** | RH | — | 臨界バランス | ζ 接続（長期） |

**最優先軸:** modular amplification の巻数誤差に数論的下限を与え、冪和型 bridge を再設計する。無条件 FLT はその先の応用。旧 coarse 実スケール witness は診断用に残すが、本命候補としては扱わない（同じ設計の単純流用は空の命題になる）。

---

## 3. 研究優先度

### 高実現性（基盤整備）— 完了

1. 増幅証明書 / no-go の Framework 化
2. pureBoost 代数 API の集約
3. bridge 責務の docstring / 型境界の統一
4. 公開 API（`Basic.lean`）と回帰例（`FoundationRegression.lean`）
5. **旧 coarse witness の空性証明と modular 基盤**

### 中実現性（現行の主対象）

1. **残ギャップ:** `ConformalGaugeAdmissible` を PGA 実スケール錐と同一視せず、CGA ゲージで再定義できるか
2. **modular 巻数誤差の数論的下限** — `JNormalized_scale = JNormalized_amplified + error(winding)` の右辺を制御
3. `FermatModularBridge` 本体の部分証明（解 ⇒ `quantizeMismatch` が巻数付き witness）
4. 成功パターンを Beal / abc へ個別再設計（解依存 payload）
5. 有限証明書の拡大

### 探索的（並列トラック）

- **1D CGA 探針**（`Algebra/CGA`, `CGA.lean`）: `Cl(2,1)` null 点・dilation。時空 CGA は未着手
- **PGA–TEGR チャート形式化**（`Gravity/`）: Schwarzschild 対角テトラッド、Weitzenböck `T`、
  動径ブースト尺度、チャート上 `J`/`T` 同定。一般 `J⁵↔T` は予想、TEGR↔EH 変分同値は据え置き
- Lie 括弧による `iso(3,1)` 同型の完備化
- 3-blade bracket / dual-as-normal の一般定理
- `exp(Ω⁽⁵⁾)` と定義積 `RT` の関係
- coprimality の局所・付値層

### 棄却 / 保留

- 現行連続 FLT bridge をそのまま証明する
- 旧 `CoarseAmplificationWitness` を本命の量子化写像として扱うこと（構造的に空；Beal/abc でも単純流用すれば同様）
- dagger 厳密降下・単純折り返し・`J5` 単独解決
- 一般多様体上の TEGR↔Einstein–Hilbert 変分同値の完全形式化（文献引用のまま据え置き）

---

## 4. 成功判定（本サイクル）

- [x] `CoarseAmplificationWitness.empty_of_coarse` を機械検証
- [x] `ModularAmplificationWitness` が具体例で inhabited
- [x] 巻数恒等式と `J` 誤差恒等式を定式化
- [x] duality / motor / Lie ラベルの Lean・論文境界を修正
- [x] 無条件 FLT や他予想の達成を主張しない
- [x] `lake build` と Docker LaTeX（検証ステップで確認）

### フェーズ 7（modular + CGA 探針）

- [x] `admissible_scale_implies_windingTotal_eq_zero` と対偶
- [x] `quantizeMismatch` / フロア誤差補題
- [x] `FermatModularBridge` と `fermat_last_theorem_of_modular_bridge`（条件付き）
- [x] 1D CGA: `point_sq` / dilation 重み / `integerHeight` 非有界
- [ ] `FermatModularBridge` 本体（無条件 FLT 相当 — 主張しない）
- [ ] 共形ゲージ ≠ PGA 実スケール の再定義

### Gravity トラック（PGA–TEGR）

- [x] Schwarzschild 対角テトラッド ⇒ 誘導計量が Schwarzschild 計量
- [x] チャート上 Weitzenböck ねじれ成分と `T = r⁻² DivClosed`
- [x] 動径ブースト尺度 `e^{±φ}` と Schwarzschild redshift の一致
- [x] 静的対角切片での `J` / `J⁵` と `T` のチャート同定パッケージ
- [ ] 一般 motor 場の `J⁵ = ½ T + div`（予想）
- [ ] TEGR↔EH 変分同値（据え置き・文献）

---

## 5. モジュール地図（現行）

```
Algebra/
  QuadraticForm, PGA, Cl31, Generators, Operations, Motor, Invariant
  Discrete, Continuum, UnitGroup
  Amplification          ← pureBoost / 実スケール
  ModularAmplification   ← ZMod 倍写・巻数・非空 witness・共形ギャップラベル
  CGA/                   ← 1D Cl(2,1) 探針（Basic 非依存）
Gravity/                 ← PGA–TEGR チャート層（数論経路とは独立）
  Coframe, Sandwich, Schwarzschild, Weitzenbock, Identification
Framework/
  Representation, Lattice, Amplification, Descent, Search
Embedding/               ← R(n), T(a), Height, quantizeInt / quantizeMismatch
  ConformalInteger       ← CGA null 点埋め込み（診断）
Theorems/
  Fermat                 ← FermatModularBridge + legacy / 連続診断
  Beal, Abc, Collatz, Goldbach, Polignac, Riemann
Basic.lean / FoundationRegression.lean
Gravity.lean / CGA.lean  ← 並列入口（Basic には強制 import しない）
```

---

## 6. 実装進捗ログ（要約）

### フェーズ 0–5 — 完了

環境、PGA コア、離散有界性、整数埋め込み、統一枠組み、条件付き 7 予想。

### フェーズ 6 — 基盤再構成（完了） + 旧量子化の診断的棄却

- 釣り合い型で連続 bridge が破綻し得ることを機械検証
- 問題非依存核を `Framework/Amplification` へ抽出
- **旧粗離散 witness が方程式非依存に空**であることを直接証明

### フェーズ 7 — modular 再設計（進行中）+ 1D CGA 探針

```
解 a^p+b^p=c^p ──► null translator = 1          （加法・証明済）
                ┄┄► quantizeMismatch 種
                         │
                         ▼
                ModularAmplificationWitness（解依存・未証明）
                         │ has_winding ⇒ ¬ 実スケール許容（証明済）
                         ▼
                ConformalGaugeAdmissible（残ギャップ / CGA 探針）
                         ▼
                   条件付き FLT（fermat_last_theorem_of_modular_bridge）
```

### フェーズ 8 — PGA–TEGR チャート層（進行中）

- `dst-pga.tex` §6 を独立節「PGA–TEGR Correspondence」へ再構成
- Lean `Gravity/`: コフレーム・Schwarzschild・Weitzenböck・`J`/`T` 同定
- 数論主軸（modular bridge）と並列；TEGR↔EH は据え置き

---

## 7. 次アクション

1. **（主）** `ConformalGaugeAdmissible` を CGA ゲージで再定義し、巻数付き modular witness と両立させられるかを検証
2. modular 巻数誤差の数論的下限と、解 ⇒ `quantizeMismatch` witness の部分構成
3. 成功パターンを Beal（`m = min`）/ abc（品質）へ個別再設計（旧粗離散の単純流用は空になる点に注意）
4. 軌道型・加法分解型は別系列として bridge 診断を継続
5. **（並列）** Gravity: 一般 `J⁵↔T` 予想の部分証明、3-blade / dual-as-normal
6. 長期: mathlib PGA contrib；時空 CGA / TEGR↔EH は文献枠または後続

**最終目標（長期）:** 7 予想を「離散双対時空代数の内部で許容増幅証明書が存在しない」という単一原理から導く完全機械検証。現状は **共通 no-go + modular 基盤 + Fermat modular bridge の型付け + 1D CGA 診断** まで固めた段階であり、無条件古典定理はまだ未達成である。
