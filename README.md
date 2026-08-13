# DstDiophantine

Double Spacetime Theory（DST）を、Lean で機械検証するプロジェクトです。

狙いを一言で言うと、「ディオファントス方程式の主張を、幾何代数の言葉に写して証明する」ことです。
論文 [`dst-diophantine.tex`](References/dst-diophantine.tex) と[`dst-pga.tex`](References/dst-pga.tex) の内容（このリポジトリ範囲外）を、段階的に Lean に落としながら、問題が見つかれば論文にフィードバックします。
論文本体は別のリポジトリ( https://github.com/hypernumbernet/dual-spacetime-doc )で管理されており、精査後に改善点が反映されます。
研究の優先順位や未証明箇所の整理は [`PLAN.md`](PLAN.md) にあります。

## ハイライト

このリポジトリでいま強調できる点は次のとおりです。

- **コアは `sorry` なし。** Lean 4 + mathlib 上で、代数・増幅・層境界の中核が機械検証されています。
- **DST / 離散 companion の代数境界を固定。** `DstDiophantine.Algebra` バレル、許容錐上の `|JNormalized|≤1`、双対のノルム保存、付録 Killing 係数誤り・異軸非可換の機械検証、有限ロータ像（整数環の単数群ではない）まで揃えています。
- **証明の骨格が三層に分かれている。** 「方程式を代数に写す層」と「増幅が許されないという共通禁止」は証明済みです。足りないのは、各予想ごとの「解から増幅証明書への橋渡し」（bridge）です。
- **行き止まりも証明した。** 旧い粗離散の増幅証明書は、方程式の種類に関係なく構造的に空だと示しました。いまの本命は、非空な例がある modular（剰余・巻数）増幅です。
- **Beal 危機路線をフェーズ 7f に進めた。** `BealCGARealization` / `BealCGADiscreteClosed` は bookkeeping。指数 gcd 還元で `d≥3` は mathlib `FermatLastTheorem` 仮説へ落とす（axiom ではない）。残件は `d=1`（混合）と `d=2`（ピタゴラス冪）。正の `|A|=1` は Mihăilescu axiom で閉じた。
- **増幅次数を `k = max(m, 4)` にした。** `ModularAmplificationWitness` は `k < 4` で空（`modularWitness_four_le`）。`m = 3` は `k = 4` に持ち上げる。
- **広い主値窓の巻数と釣り合い型の空性を証明した。** 窓内は `beal_winding_of_solution_window`、釣り合い型 `log 2 / m < 2π/k` は任意格子で巻数 0。
- **CGA 整数 dilation 群。** `IsCGAIntegerDilation`、格子保存、二点一意スケール、DST 結合配置の易しい方向、等指数 `mismatchRotor` ↔ CGA log-scale まで機械検証。
- **Fermat / abc modular bridge も型付け済み。** 無条件 FLT / Beal / abc は主張しません。
- **古典予想の無条件証明はまだ主張しない。** 「bridge が正しければ従う」形と部分構成（広い主値窓・折り畳み・Realization 条件付き）までです。
- **数論と独立に、重力側（PGA–TEGR）もチャート固定で動かしている。** Schwarzschild 計量まわりまで Lean に載っています。

## 行ったこと

### 全体の考え方（三層）

証明を次の三層に分けています。未証明の bridge を、すでに証明した一般定理と混ぜないための設計です。

1. **加法忠実化（証明済み）**  
   冪和型の整数方程式を、ヌル並進モーターが単位元になる条件へ一対一で写します。
2. **共通 no-go（証明済み）**  
   「許容される配置では高さが有界」なのに、「増幅すると高さが必ず跳ねる」という衝突を、問題に依存しない形で証明します。
3. **問題別 bridge（未証明）**  
   「整数解がある ⇒ 上の増幅証明書が作れる」という橋です。ここが閉じれば、条件付き／将来の無条件結果につながります。いまは仮説として残しています。

旧い実スケールの粗離散証明書 `CoarseAmplificationWitness` は、粗さの仮定のもとで**中身が必ず空**になります（`empty_of_coarse`）。
そのため現行の乗法側は `Algebra.ModularAmplification`（`ZMod` 上の倍写と巻数の誤差）に移しています。

### PGA 代数コア

幾何代数の土台を `DstDiophantine.Algebra` に実装し、次を証明しました。

- 5 次元クリフォード代数 `G(3,1,1)` と、双曲・循環・ヌルの 10 生成子
- ヌル生成子の強消滅 `N_μ N_ν = 0`（加法の写像に使う重要な代数関係）
- ロータと並進の定義積モーター `M := RT` がユニタリであること（`motor_unitary`）
- `e₄` と擬スカラーの可換性、双曲／循環方向での dual
- 許容配置に限れば正規化不変量 `|JNormalized| ≤ 1`  
  （「すべての配置で有界」という素朴版は反例で棄却済み）

関連モジュールの目安: `QuadraticForm` / `PGA` / `Generators` / `Operations` / `Motor` / `Invariant`。

### 加法忠実化

「整数の足し算の関係」を、代数側の `powerSumMotor = 1` と同値にします。

- 冪和型の方程式 ↔ null translator / `powerSumMotor = 1`（`Framework.Representation`、`Embedding.NullTranslator`）
- Fermat / Beal / abc / Goldbach / Polignac について、この加法骨格を共通化

ここまでが「方程式を PGA の言葉に写す」層です。増幅との衝突は次の層で扱います。

### 共通 no-go と modular 基盤

増幅と有界性の衝突を、問題ごとに書き直さなくてよい共通定理として証明しました。

- 純ブーストで高さが `k²` 倍に増えることと、許容配置での高さ上界の両立不可能性（連続版）
- 離散側の非零高さ下限 `ε_N = 16/(3N²)` と、粗トーラス上の no-go
- **旧粗離散証明書の構造的空性**（方程式に依存しない。同じ設計を Beal / abc に流用しても空のまま）
- **modular 増幅:** 巻数の恒等式、正規化高さの誤差恒等式、具体例 `N = 16`, `k = 5` で witness が非空であること
- **巻数ギャップ:** 実スケールが連続許容なら総巻数は 0（よって巻数付き modular witness は連続 no-go に直接渡せない）
- **`FermatModularBridge`:** 解依存 payload + `ConformalGaugeAdmissible`（暫定的に PGA 実スケール錐と同一視）→ 条件付き FLT
- `FoundationRegression` で、空性・modular の inhabited・巻数 0・modular bridge・三層の境界を回帰テストとして固定

つまり「共通の禁止定理」と「空ではない新しい証明書の型」までは揃っています。残るのは、各予想の解からその証明書へ渡る bridge です。

### 棄却の機械検証（通らなかった道）

うまくいかない方針も、Lean で反例または構造的失敗として残しています。再発明を避けるための成果です。

- 主枝だけ見て `|J| ≤ 1` とする素朴有界性（反例あり）
- dagger による高さの厳密減少（減少しない）
- 「任意の Fermat 解 ⇒ 種が `1/p²` より大きい」という現行連続閾値（釣り合い型で破綻し得る）
- dual で null bivector の扇が閉じるという主張（`dual_null` は grade 4 になる）
- 論文のラベル `so(3,1)⊕so(3,1)`（次元が合わない；`so(3,1)⋉ℝ^{3,1}` 候補）

### 条件付き Theorems API

`DstDiophantine.Theorems` に、主要な予想ごとの入口があります。
いずれも **`*_of_bridge`（bridge を仮定すれば古典主張が従う）** という形です。bridge 自体は未証明なので、無条件の FLT などを主張してはいません。

| ファイル | いま入っているもの |
|----------|-------------------|
| `Fermat.lean` | 加法同値、`FermatModularBridge`、釣り合い型の障害、連続／旧粗離散（legacy・診断用） |
| `Beal.lean` | 分数冪 gap、冪格子⇔`|A|=1`、Realization / DST 配置、Mihăilescu 正 UnitBase、窓巻数、旧格子 / modular（診断） |
| `Mihailescu.lean` | Catalan / Mihăilescu axiom と正の unit-base 断片 |
| `Abc.lean` | 品質–高さ、連続 bridge 棄却、`AbcModularBridge`（条件付き古典 ABC） |
| `Collatz.lean` | 軌道の高さ単調、421 サイクル、有限範囲の到達 |
| `Goldbach.lean` / `Polignac.lean` | 加法分解の motor 同値、候補の健全性、有限範囲の存在 |
| `Riemann.lean` | 臨界高さ・オフライン矛盾の骨格、有限格子上のバランス |

### 有限証明書（計算で閉じた範囲）

無限の予想そのものではなく、「この範囲では成り立つ」ことを Lean で証明した計算証明書です。

- Collatz: 初期値 ≤ 20 で 1 に到達
- Goldbach: 偶数 ≤ 100 で素数和分解
- abc: `c ≤ 100` での radical 関連の有限主張
- Riemann（有理格子モデル）: ≤ 20
- Polignac: 双子素数ギャップ ≤ 20、ギャップ 4・6 は ≤ 30

### PGA–TEGR（チャート固定の重力トラック）

数論の主軸とは独立に、`DstDiophantine.Gravity` で TEGR 寄りの骨格をチャート固定で形式化しています（`Basic` には強制 import しません）。

- 外域の対角テトラッドから、誘導計量が Schwarzschild 計量になること
- Weitzenböck のねじれ成分と、発散形 `T = r⁻² DivClosed`
- 動径ブーストの尺度と redshift の一致
- 静的対角切片での `J` / `J⁵` と `T` の同定パッケージ

一般のモーター場での `J⁵ ↔ T` や、TEGR と Einstein–Hilbert の変分同値まではまだです（見通しを参照）。

## これからの見通し

いまの焦点は **無条件 Beal** です。共通 no-go・modular 基盤・窓巻数・bookkeeping 降下・
Mihăilescu 正 UnitBase・指数 gcd 還元（`d≥3` → FLT 仮説）までは揃っています。
残りは `bealExpGcd ∈ {1,2}` と FLT 本体です。

- **主軸（Beal）**  
  指数 gcd 還元。`d≥3` は mathlib `FermatLastTheorem`（`FermatModularBridge` から従う）
  で条件付き閉鎖。残件は混合指数（`d=1`）とピタゴラス冪（`d=2`）。
  Realization / DiscreteClosed は bookkeeping（幾何原理として証明しない）。
- **1D CGA**  
  ペアリング・整数格子・冪格子・整数 dilation 群・三点冪和は接続済み。時空 CGA は後続です。
- **後続の冪和 / 品質型**  
  Fermat / abc modular への移植、巻数誤差の数論的下限。
- **有限証明書の拡大**  
  Collatz / Goldbach / abc などの検証上限を上げる。
- **別系列**  
  軌道型・加法分解型は別ルート。Riemann は長期。Gravity は並列。
- **長期目標**  
  7 予想を単一原理から導く完全機械検証。無条件古典 Beal はまだ未達成です。

## ビルド

```bash
lake update
lake build
```

Lean 4.34.0-rc1 と mathlib `v4.34.0-rc1` を使います。

公開の入口は `DstDiophantine.Basic`、三層の境界や空性・modular の inhabited を固定する回帰例は
`DstDiophantine.FoundationRegression` です。重力側だけ見る場合は `DstDiophantine.Gravity`、
1D CGA 探針だけ見る場合は `DstDiophantine.CGA` を使います（いずれも `Basic` には強制しません）。
