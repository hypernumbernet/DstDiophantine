# PGA-DST ディオファントス証明基盤 — 研究計画

最終更新: 2026-08-15（D4L: 振幅・四状態・幾何干渉 + 双対 Hilbert 兄弟層）

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
- 連続像はちょうど `[-1,1]`。`|JNormalized|=1` iff 全軸が純双曲または全軸が純楕円
- 離散鋭い上界 `|JNormalized| ≤ (4⌊N/4⌋/N)²`。`4∣N` で ±1 達成、`¬4∣N` なら厳密。許容離散値は `[-1,1]` に稠密
- 純ブーストの `k²` 増幅と連続種高さ上界
- 離散非零高さ下限 `ε_N = 16/(3N²)` と粗トーラス高さ no-go
- **旧 `CoarseAmplificationWitness` の構造的空性**（方程式非依存；`empty_of_coarse`）
- 加法 null 忠実性（Fermat / Beal / abc / Goldbach / Polignac の骨格）
- modular 巻数恒等式と `ModularAmplificationWitness` の具体例（`N=16,k=5`）
- **実スケール許容 ⇒ `windingTotal = 0`**（modular witness は連続 no-go に直接渡せない）
- `quantizeMismatch` / `quantizeInt` 補題とフロア誤差
- **`FermatModularBridge` の型付け**と条件付き FLT（解依存 payload；bridge 本体は未証明）
- **`BealModularBridge` の型付け**と分数冪 gap（`bealFracLogGap` / 解のとき `log(1+B^y/A^x)`；bridge 本体は未証明）
- 1D CGA `Cl(2,1)`: `X(x)² = 0`、dilation 重み、`integerHeight` 非有界診断
- 有限計算証明書（Collatz ≤20、Goldbach ≤100、abc ≤100、RH 有理格子 ≤20、
  Polignac 双子 ≤20 / gap4·6 ≤30）

### 未証明（明示的 bridge・無条件主張しない）

| Bridge | 問題 | 核との接続 | 備考 |
|--------|------|------------|------|
| `FermatModularBridge` | FLT（本命・modular） | 解依存 `quantizeMismatch` + 巻数 witness + 共形ギャップ | **型付け済・未証明**；`ConformalGaugeAdmissible` が残ギャップ |
| `FermatAdmissibleBridge` | FLT（連続・診断用） | 釣り合い型で偽になり得る | 診断専用 |
| `FermatCoarseDiscreteBridge` | FLT（旧粗離散） | ペイロードが構造的空 | legacy / 診断用（単純流用は空のまま） |
| `BealCGARealization` | Beal（bookkeeping） | 互素解 ⇒ A–C 根比が整数 CGA dilation | **≡ `|A|=1` ∧ `|C|^z` が m 乗**；独立幾何原理ではない |
| `bealExpGcd` 還元 | Beal（本命分割） | `d=gcd(x,y,z)` | **3∣d / 4∣d は無条件**（`BealSlice`）；一般 d≥3 は **FLT 公理**（`FermatLast` / フェーズ 7i）；d=2 は参数表示＋**4 整除 2 本以上を無条件閉鎖**（`BealPythagorean`）＋ equal-odd は Gaussian で二因子残件へ；残件は d=1 と `BealPythagoreanResidual` / `BealEqualOddTwoFactorResidual` |
| `BealCGADiscreteClosed` | Beal（bookkeeping） | 互素解 ⇒ k 倍種が m 冪格子上 | **≡ `|A|=1`**（`beal_kFold_powerLattice_iff_natAbs_eq_one`） |
| `BealUnitBaseNoGo` / `bealUnitBaseNoGo_pos` | Beal（残件） | `|A|=1` の互素解は存在しない | **正の基底は Mihăilescu axiom で証明済** |
| `BealWindingBridge` | Beal（窓レジーム・診断） | 解 ⇒ 巻数 witness | **窓場合は証明済**；釣り合い型は構造的空（`windingTotal_eq_zero_of_rapidity_lt`） |
| `BealCGALatticeGauge` / `BealCGADilationNoGo` | Beal（等指数切片・診断） | 整数ヌル格子上の巻数禁止 | 等指数で格子成立；混合は外れ；NoGo 本体未 |
| `BealCGAGauge` / `BealCGANoGo` | Beal（診断） | 恒真 null ゲージ ⇒ 巻数禁止 | **ill-posed**（窓構成と衝突し得る）；関係補題のみ |
| `BealModularBridge` | Beal（診断・旧 modular） | witness + `ConformalGaugeAdmissible` | **payload 矛盾**（`beal_modular_payload_incompatible`） |
| `BealAdmissibleBridge` | Beal（連続・診断） | 連続増幅 no-go | 釣り合い型で種が `1/m²` 未満 |
| `AbcAdmissibleBridge` | abc（連続・診断） | 品質天井 | **偽**（`AbcAdmissibleBridge_false`） |
| `AbcModularBridge` | abc（本命・modular） | 解依存 `quantizeAbcMismatch` + 巻数 witness + 共形ギャップ | **型付け済・未証明**；部分巻数構成あり |
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

**最優先軸:** 無条件 Beal 危機路線（フェーズ 7i）。Realization / DiscreteClosed は bookkeeping。指数 gcd の三分法、無条件スライス、**FLT 公理による `d≥3`**、Gaussian UFD による斜辺冪と equal-odd / 偶二一致の進捗まで固めた。残件は **`BealMixedExpResidual`**、**`BealPythagoreanResidual`**、**`BealEqualOddTwoFactorResidual`**、**`BealTwoEqualEvenResidual`**。無条件古典 Beal は主張しない。CGA Realization は幾何原理としては使わない。

---

## 3. 研究優先度

### 高実現性（基盤整備）— 完了

1. 増幅証明書 / no-go の Framework 化
2. pureBoost 代数 API の集約
3. bridge 責務の docstring / 型境界の統一
4. 公開 API（`Basic.lean`）と回帰例（`FoundationRegression.lean`）
5. **旧 coarse witness の空性証明と modular 基盤**

### 中実現性（現行の主対象）— Beal 危機路線（フェーズ 7h）

1. ~~`BealCGARealization` を幾何原理として証明~~ — bookkeeping 化完了（循環を回避）
2. ~~`3∣d` / `4∣d` / 等指数 3,4~~ — mathlib FLT で無条件閉鎖（`BealSlice`）
3. ~~`d = 2` 原始ピタゴラス参数表示~~ — `coprime_classification` 接続済
4. ~~`d = 2` で 4 整除が 2 本以上~~ — `BealPythagorean`（`not_fermat_42` + DiffFourth）で無条件閉鎖
5. **残件 `bealExpGcd = 1`:** 二指数一致（3 位置）と全相異を切り出し；本体は `BealMixedExpResidual`
6. **残件 `BealPythagoreanResidual`:** 還元指数のうち 2 つ以上が奇数（型固定；ℤ[i] 斜辺は準備のみ）
7. ~~一般 `d ≥ 3`~~ — mathlib `FermatLastTheorem` 仮説で条件付き（本体は未証明）
8. （後続）`FermatModularBridge` / `AbcModularBridge`；有限証明書の拡大

### 探索的（並列トラック）

- **1D CGA 探針**（`Algebra/CGA`, `CGA.lean`）: `Cl(2,1)` null 点・dilation。時空 CGA は未着手
- **D4L / 二重時空四値論理**（`Logic/`, `Logic.lean`）:
  許容配置を振幅とし、`JNormalized` の四状態、\(\min/\max/-\)、Killing 重なり・異軸干渉、
  高さ/情報順序、\(V_\lambda\) の大規模臨界点を機械検証。書かれた \(U\) では小スケール収縮が偽。
  D4L 自体は Hilbert / Born / オーソモジュラーではない（分離定理）。双対セクターの兄弟
  \(\mathbb{C}^2\) と部分空間格子は `Logic/Quantum/`（フェーズ Q0–Q5）。Basic 非依存
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

### フェーズ 7b（ABC modular — 進行中）

- [x] 連続 `AbcAdmissibleBridge` を診断用に落とし `AbcAdmissibleBridge_false` を証明
- [x] `quantizeAbcMismatch` / `abcLogGap` / radical 乗法性
- [x] `AbcModularBridge` と `abc_conjecture_of_modular_bridge`（条件付き）
- [x] pure-boost 巻数判定と主値区間での `abc_has_winding_of_logGap_ge`
- [ ] `AbcModularBridge` 本体（無条件 ABC 相当 — 主張しない）
- [ ] 許容性・増幅後許容と共形ギャップの解消

### フェーズ 7c（Beal modular — 完了）

- [x] `bealFracLogGap` と解のとき `m·δ = log(1+B^y/A^x)`、等指数退化
- [x] `quantizeBealMismatch` / 旧 `BealModularBridge`（診断・payload 矛盾を機械検証）
- [x] 主値区間での `beal_has_winding_of_fracGap_ge`、釣り合い型連続診断
- [x] 共通巻数ヘルパを `Algebra.ModularAmplification` へ抽出
- [x] bridge 分割: `BealWindingBridge` + `BealCGALatticeGauge` / `BealCGADilationNoGo`
- [x] `modularWitness_four_le`（`k < 4` なら空）と `bealAmpExp = max(m,4)`
- [x] 広い主値窓 `N = k`, `2π/k ≤ δ < 4π/k`（`m = 3` 含む）⇒ modular witness
- [x] `principalRapidity` トーラス折り畳みと主値窓への拡張
- [x] CGA 点対ペアリング / スケール不変 dilation mismatch / 2π 非周期性
- [x] 三点 `α^m+β^m=γ^m` と `BealCGALatticeGauge`（等指数で成立・混合で反例；恒真 Triple Prop は置かない）
- [x] 窓に入る解 ⇒ 巻数 witness（`beal_winding_of_solution_window`）
- [x] 旧 `BealCGANoGo` を診断化（ill-posed；窓との関係補題）

### フェーズ 7d（Beal CGA 冪格子降下 — 完了）

- [x] 対ごと互素（`beal_pairwise_coprime`）
- [x] `IsCGAPowerLatticePoint` と整数格子包含・`2^{4/3}` 診断
- [x] k 倍 dilation の m 乗等式・整除裁定・`|A|=1` 降下（無条件補題）
- [x] `δ < 2π/k` で巻数 0 / 釣り合い型 modular witness 空性
- [x] `BealWindingBridge` を窓レジーム診断へ降格
- [x] `BealCGADiscreteClosed` + `BealUnitBaseNoGo` 型付けと条件付き古典 Beal
- [x] 有限断片 `not_one_add_pow_three_eq_pow_three`

### フェーズ 7e（Beal CGA 整数 dilation 実現 — 完了→bookkeeping）

- [x] 互素解で k 倍冪格子 ⇔ `|A|=1`（`BealCGADiscreteClosed` を bookkeeping 化）
- [x] Mihăilescu axiom + 正の `bealUnitBaseNoGo_pos`
- [x] `IsCGAIntegerDilation` / 格子保存 / 二点一意スケール / `|A|∣|C|` 同値
- [x] `IsDSTBealDiscreteConfig` + 互素 ⇒ `|A|=1`；正なら Mihăilescu で矛盾
- [x] `BealCGARealization` 型付け；等指数 `mismatchRotor` ↔ CGA log-scale
- [x] 条件付き正古典 Beal（`beal_conjecture_pos_of_realization`）
- [x] Realization を独立幾何原理として扱わない（フェーズ 7f で確定）

### フェーズ 7f（Realization bookkeeping + 指数 gcd 還元 — 完了）

- [x] `beal_integerDilation_iff_pow_eq` / 互素解での同値 / 等指数⇔`|A|=1`
- [x] 診断 `3²+4²=5²`（比 `5/3` は整数 dilation でない）
- [x] `bealExpGcd`・冪還元・`bealGcd_pow_eq_one`
- [x] mathlib `FermatLastTheorem` 仮説版（残置）と、フェーズ 7i の FLT **公理**版で `d≥3` 閉鎖
- [x] `FermatLastTheorem_of_modular_bridge`；等指数・ピタゴラス冪還元

### フェーズ 7g（無条件 FLT スライス + ピタゴラス参数表示 — 完了）

- [x] `bealExpGcd` 三分法・`d=2` で還元指数の gcd=1
- [x] 互素 `d=2` ⇒ `PythagoreanTriple.coprime_classification`
- [x] `BealSlice`: `3∣d` / `4∣d` / 等指数 3,4 を無条件閉鎖
- [x] `d=2` ∧ `4∣x` ∧ `4∣y` を `not_fermat_42` で無条件閉鎖
- [x] `BealMixedExpResidual` と二指数一致 `x=y` の切り出し（型のみ）

### フェーズ 7h（ピタゴラス UFD 降下 — 完了）

- [x] `BealPythagorean`: `a⁴ + b² ≠ c⁴`（DiffFourth 降下）と偶脚 UFD
- [x] `d=2` ∧ (`4∣x`∧`4∣z` / `4∣y`∧`4∣z`) を無条件閉鎖；系として 4 整除 2 本以上
- [x] `BealPythagoreanResidual`（還元指数のうち 2 つ以上が奇数）と iff
- [x] ℤ[i] 斜辺冪の準備ラベル（完全降下は据え置き）
- [x] `d=1`: 二指数一致を `y=z` / `x=z` に拡張し、全相異を切り出し
- [x] 成功判定: 無条件 Beal ではなく「`d=2` の 4 整除 2 本以上を閉鎖 + 残件型の固定」

### フェーズ 7i（FLT 公理と Gaussian UFD 降下 — 完了）

- [x] `FermatLast.lean`: `axiom fermatLastTheorem`（Wiles の Lean 証明ではない旨明記）
- [x] `not_beal_sol_of_expGcd_ge_three`（仮説なし・公理依存）で `d≥3` を閉鎖
- [x] `beal_conjecture_pos_of_residuals`: 正の基底で古典 Beal を残件 2 つへ還元（sorry なし）
- [x] `BealGaussian`: 互素・反対偶奇 ⇒ `m+ni` が単数倍の冪；`IsGaussianHypotenusePower` 定理化
- [x] equal-odd（偶脚＝斜辺の同じ奇数還元指数）を `BealEqualOddTwoFactorResidual` へ還元
- [x] `d=1` 偶二一致: mod 4 + 平方和形への進捗（`BealTwoEqualEvenResidual`）
- [x] 成功判定: 無条件古典 Beal を主張しない；還元と Gaussian 進捗が sorry なし
- [ ] 残件本体: `BealMixedExpResidual` / `BealPythagoreanResidual` /
  `BealEqualOddTwoFactorResidual` / `BealTwoEqualEvenResidual`
- [ ] 無条件古典 Beal（主張しない）

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
Algebra.lean             ← DST 代数コアのバレル（Theorems / Gravity 非依存）
Algebra/
  Admissible             ← IsPrincipalBranch / IsAdmissibleContinuous（パラメータ辞書）
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
  Beal (exp-gcd 還元 + Realization bookkeeping + 混合指数切り出し),
  BealSlice (無条件 FLT n=3,4 スライス + 双二次),
  BealPythagorean (d=2 UFD / DiffFourth / 4 整除 2 本以上),
  BealGaussian (ℤ[i] UFD / equal-odd / 偶二一致進捗), FermatLast (FLT 公理), Mihailescu,
  Abc (AbcModularBridge + continuous false), Collatz, Goldbach, Polignac, Riemann
Basic.lean / FoundationRegression.lean
Gravity.lean / CGA.lean / Logic.lean  ← 並列入口（Basic には強制 import しない）
Logic/                   ← D4L（振幅、JNormalized の四状態、幾何演算）
Logic/Quantum/           ← 兄弟: 分離、双対扇、四元数、C2、部分空間格子、辞書
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

## 7. DST / 離散論文へ返す欠点（2026-08-14）

Lean 代数コアの整理で機械検証した（または棄却した）論文側の問題。本体 `.tex` は https://github.com/hypernumbernet/dual-spacetime-doc。ローカル `References/` のコピーは 2026-08-14 に本表へ合わせて改訂した。GitHub 本体へは未反映。フォルダに無い `dst-riemann-hypothesis.tex` / `dst-langlands-program.tex` / `dst-particle-stability.tex` / `dst-iut.tex` は未着手。

### 優先（`|J|≤1` を無条件に使っている）

| 論文 | 内容 | Lean |
|------|------|------|
| `dst-riemann-hypothesis.tex` | 要旨・§2 が `|J|≤1`。主枝だけでは偽。許容錐と `JNormalized` に置換 | `torsion_bound_naive_false` |
| `dst-langlands-program.tex` | 「Torsion Boundedness `|J|≤1`」を任意アンサンブルのマスター定理にし、Langlands 全体を従わせている。許容なしでは成り立たない。無条件主張は落とす | 同上 |

### 優先（生の J の有界の中身が食い違う）

| 論文 | 内容 | Lean |
|------|------|------|
| `double-spacetime-theory.tex` App.B | `Ω=∑(α/2)iΓ+(β/2)Γ` と `B(iΓ,iΓ)=8` なら `B(Ω,Ω)=2∑(α²-β²)`。付録の `8∑` は誤り | `paper_appendix_killing_coeff_false` |
| 同 App.B | `[iΓ_a,Γ_b]=0` は同軸のみ。異軸は反例 | `commutator_hyperbolic_cyclic_same` / `…_ne_zero` |
| 同 | `so(3,1)⊕so(3,1)` は次元 12。生成子は 6。Poincaré 候補が妥当 | `Generators` docstring |
| 同 §「J remains bounded」 | 許容＋`|J|≤3π²/8`（または `|JNormalized|≤1`）に限定 | `torsion_bound_raw_continuous_pi_sq` |
| `dst-quantum-gravity.tex` | `|J| ≤ J_max ~ N^{-2}` と `|J| ≤ c⁴/G ℓ_P^{-2}` が並立し、許容錐の `3π²/8` とも矛盾。離散 `ε_N=16/(3N²)` は非零高さの**下限**であり上界ではない | `discrete_nonzero_height_lb` |

### Jnorm 入りだが残件がある

| 論文 | 残件 | Lean |
|------|------|------|
| `discrete-dual-spacetime.tex` | 許容は離散化の帰結ではなく追加仮説。「整数環の有限単数群」は `DiscreteRotorImage`。「`A≲300`」は導出なし。双曲 rapidity のトーラス量子化は釣り合い型で巻数 0 | `torsion_bound_naive_false` / `discreteRotorImage_finite` / `beal_balanced_gap_no_modularWitness` |
| `dst-pga.tex` | `J⁵` 非有界の備考は既にある。残るのは `1/16 B` と生成子展開の係数、`motor=exp(Ω)` vs 定義積 `RT` | `J5_unbounded` / `Motor` |
| 局所 / GitHub `dst-diophantine.tex` | 第3章・付録は 2026-08-14 に等号 iff・離散鋭い上界・Killing `2∑` 注記へ同期した。GitHub 本体へ未反映 | `abs_JNormalized_eq_one_iff` / `torsion_bound_discrete_sharp` |

### J の定義が別物（範囲を流用しない）

| 論文 | 内容 |
|------|------|
| `dst-particle-stability.tex` | `J(ℓ,w,δφ)=½ m ℓ (δφ)²` は Killing の J ではない。`|JNormalized|≤1` を流用できない |
| `dst-iut.tex` | 数値上界は無いが `so(3,1)⊕so(3,1)` と `J=1/16 B` を引用。主論文の Killing 修正に追随 |
| `dst-dynamic-equation.tex` / `dst-de-broglie-wave.tex` | 位相・振動子として J を使う。`|J|≤1` は書いていない。辞書が固まったら引用を揃える程度 |

### 既出の非 J 範囲項目（維持）

| 項目 | 内容 | Lean |
|------|------|------|
| null dual 閉性 | grade で棄却 | `dual_null` |
| `motor = exp(Ω_biv)` | 非可換時は偽。定義積 `R·T` のみ | `Motor` |
| TEGR↔EH | 未証明の `J=½T+div` + 文献引用。変分なし | Gravity チャート切片のみ |
| 連続体否定 vs `∫J d⁴x` | 論理的緊張 | 形式化対象外 |
| `BealCGADiscreteClosed` | 幾何原理ではない（bookkeeping） | `beal_kFold_powerLattice_iff_natAbs_eq_one` |
| 文献プレースホルダ | `arXiv:xxxx.xxxxx` | — |

### 今サイクルで強化した Lean 境界（J 範囲）

- 軸ごと上界の等号 iff、生の天井 `|J|≤3π²/8`、負の極端、`|JNormalized|=1` の大域等号、像 `[-1,1]`
- 離散 `|JNormalized| ≤ (4⌊N/4⌋/N)²`、`4∣N` で ±1、`¬4∣N` で厳密、許容離散値の稠密
- `Algebra.lean` / `Basic.lean` export と `FoundationRegression` の回帰 example

Beal 危機路線の優先度は維持。上記は並列の代数整理。7予想の無条件証明・dagger 降下・粗離散 witness・TEGR↔EH 変分は、J 範囲の辞書が固まってから別チケット。

---

## 8. 次アクション

1. **（主・Beal）** `d=1` 混合指数（`BealMixedExpResidual`）と `d=2` 一般ピタゴラス冪降下
2. （条件付き）一般 `d≥3`（3 でも 4 でも割れない）は FLT 本体トラック
3. （後続）Fermat / abc modular への移植；軌道型・加法分解型は別系列
4. **（並列）** Gravity: 一般 `J⁵↔T` 予想の部分証明
5. 長期: mathlib PGA contrib；時空 CGA / TEGR↔EH は文献枠または後続
6. **（論文フィードバック）** ローカル `References/` は本表へ合わせて改訂済。GitHub `dual-spacetime-doc` 本体と、フォルダに無い RH / Langlands / particle-stability / IUT は未反映
7. **（並列・D4L Hilbert）** `Logic/Quantum/` と `dst-d4l-hilbert.tex`。D4L との同一視はしない。Dirac \(\mathbb{C}^4\) は後続

**最終目標（長期）:** 7 予想を「離散双対時空代数の内部で許容増幅証明書が存在しない」という単一原理から導く完全機械検証。現状は **共通 no-go + modular 基盤 + Beal 窓巻数 + 冪格子/Realization bookkeeping + Mihăilescu 正 UnitBase + 指数 gcd 還元 + 無条件スライス + FLT 公理による d≥3 + Gaussian UFD 進捗** まで固めた段階であり、無条件古典 Beal は残件（混合指数 / ピタゴラス奇数還元 / equal-odd 二因子 / 偶二一致）が閉じるまで未達成である。FLT 公理は mathlib 未形式化の古典定理の明示的仮定であり、Wiles の Lean 証明ではない。
