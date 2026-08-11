**Leanによる形式化の全体的な展望**

DSTディオファントス論文（`dst-diophantine.tex`）の主張をLean 4 + mathlib4で完全に機械検証するためのロードマップを、依存関係と難易度を踏まえて段階的にまとめます。全体は「代数的基盤 → 離散構造と有界性 → 整数埋め込み → 統一的降下枠組み → 個別定理」という順序が自然です。PGA埋め込みとヌルトランスレータが加法構造の核心であるため、ここを早期に固める必要があります。

### 1. フェーズ0：前提環境とmathlib活用
- Lean 4 + 最新mathlib4をベースとする。
- 既に使えるもの：クリフォード代数の一般論（部分的）、リー代数、有限環 \(\mathbb{Z}/N\mathbb{Z}\)、群論・環論の基本、Baker–Campbell–Hausdorff公式の形式的展開の一部、有限集合上の全探索の枠組み。
- 不足・要拡張：射影幾何代数（PGA）\(G(3,1,1)\) の本格的実装、双四元数としての \(\mathrm{Cl}(3,1)\) の具体的基底と演算、ヌルベクトルの取り扱い、モーター／ローターの指数写像と逆元、キリング形式の具体計算、連続群の離散化近似と主枝対数の厳密な扱い。
- 目標：PGAと双四元数を独立したライブラリ（またはmathlibへのコントリビューション候補）として整備する。

### 2. フェーズ1：コア代数構造の形式化（最優先）
- 双四元数代数 \(\mathbb{H}\otimes_{\mathbb{R}}\mathbb{H}\cong\mathrm{Cl}(3,1)\) の定義と演算。
- ヌルベクトル \(e_4\)（\(e_4^2=0\)）の付加による \(G(3,1,1)\) への埋め込み。
- 10次元バイベクトル空間の分類：
  - 双曲生成子（\(iI,iJ,iK\)）
  - 循環生成子（\(I,J,K\)）
  - ヌル生成子 \(N_\mu=e_4\wedge e_\mu\)
- ローター・モーターの定義、逆元（reverse）、指数写像、双対写像 \(X\mapsto Xi\)、dagger演算。
- 拡張されたねじれ不整合 \(J^{(5)}\) とキリング形式に基づく \(J\) の定義。
- **成果物**：PGAと双四元数の基本API。以降のすべてがこれに依存。

### 3. フェーズ2：離散化とねじれ有界性定理
- ラピディティの離散化：\(\omega_a=2\pi n_a/N\)、\(\phi_a=2\pi m_a/N\) による有限トーラス \((\mathbb{Z}/N\mathbb{Z})^6\)。
- 離散双四元数環の有限単位群の存在と性質。
- **中心定理**：\(|J|\le 1\) の厳密証明。
  - キリング形式の符号非対称性
  - 双対写像によるカイラリティ
  - Spin群の被覆トポロジーと主枝の制限
  - 有限トーラスのコンパクト性
  - ヌル生成子の強い消滅性（\(N_\mu N_\nu=0\)）による並進寄与の制御
- 連続極限 \(N\to\infty\) でのTeleparallel Equivalent of GRの回復（ここは補助的に扱う）。
- **成果物**：有界性定理を公理ではなく完全に証明した状態。これ以降のディオファントス証明の「矛盾の源」になる。

### 4. フェーズ3：整数の代数的埋め込み
- 乗法構造：正整数 \(n\) への標準ローター \(R(n)=\exp(\log|n|\cdot iI)\)（主枝対数）。
- 加法構造：ヌルトランスレータ \(T(a)=\frac12 a^\mu N_\mu\)。
- ローターの冪乗とBCH展開による \(J\) の増幅公式（誤差項の厳密評価を含む）。
- 有限単位群による同値類と高さ関数 \(J\) の降下性。
- **成果物**：任意の多項式ディオファントス方程式を「ローター＋ヌルトランスレータの代数恒等式」に翻訳する一般写像。

### 5. フェーズ4：統一ディオファントス枠組みと降下アルゴリズム
- 一般表現：\(f(x_1,\dots,x_k)=0\) を  
  \(R(f)\cdot\exp(\sum c_i T(x_i))=1\)  
  に変換し、対応する \(J\) が0になる格子点の存在問題に帰着。
- 統一的代数的降下：dagger → 単位群判定 → 双対ローター再構成による \(J\) の厳密減少。
- 有限性により「解の存在 ⇔ \(J=0\) の格子点が存在する」ことを決定可能アルゴリズムとして形式化。
- **成果物**：個別定理をこの枠組みのインスタンスとして書くための共通基盤。

### 6. フェーズ5：個別定理の形式化（難易度順推奨）
1. **Fermatの最終定理・Beal予想**（比較的容易）  
   冪乗による \(J\) の \(p^2\) 増幅と有界性の矛盾。ヌルトランスレータによる加法関係の扱いが中心。
2. **Collatz予想**  
   有限トーラス上の軌道の周期性と \(J\) の蓄積。計算的検証と相性が良い。
3. **Goldbach・Polignac（双子素数含む）**  
   偶数ギャップのヌルトランスレータ表現と最小 \(J\) 分解の存在。
4. **abc予想**  
   コプライム三重項のねじれ高さによる品質の有界性。連続極限での古典的主張の回復も。
5. **リーマン予想**（最難）  
   ゼータ関数の非自明零点が「ねじれ不整合が消えるローター・アンサンブル」に対応し、離散ねじれ層のスケール不変性から \(\mathrm{Re}=1/2\) が強制される、という埋め込みの形式化。mathlibの複素解析・ゼータ関数の現状を大幅に拡張する必要がある。

### 7. 全体の見通しとリスク・戦略
- **戦略的分割**：
  - 小さな \(N\) に対する計算的証明書（全探索）をLeanの `decide` や外部計算との連携で先行させる。
- **主な技術的ハードル**：
  - 主枝対数とBCHの誤差評価の厳密化
  - 連続パラメータの離散化における「物理的に許容される配置」の定義
  - リーマン予想部分の解析的内容の代数化
- **最終目標**：7つの予想すべてを「離散双対時空代数の内部で \(|J|\le 1\) を破る格子点が存在しない」という単一の原理から導く、完全に機械検証された状態にする。

この順序で進めれば、途中成果（PGAライブラリ、有界性定理、FLTの形式化など）を段階的に公開・検証しながら全体を積み上げることができます。必要に応じて特定フェーズの詳細設計や最初のLeanスケルトンの作成に進みましょう。

---

## 実装進捗（2026-08-11）

### フェーズ0 — 完了

- `lake build` 成功（Lean 4.34.0-rc1 + mathlib `v4.34.0-rc1`）
- `DstDiophantine/Algebra/` モジュール骨格を配置し `DstDiophantine.lean` から import
- README をビルド手順 + フェーズ概要に更新

### フェーズ1 — コア API 固め（完了）

モジュール構成:

| ファイル | 内容 |
|----------|------|
| `QuadraticForm.lean` | `Q31` / `Q311`、`extend4`、`minkowskiDot` |
| `PGA.lean` | `G(3,1,1)`、`e₄²=0`、`{e₄,e_μ}=0` |
| `Cl31.lean` | `Cl(3,1)` 部分代数、`toPGA` 埋め込み |
| `Generators.lean` | 10 生成子（双曲・循環・ヌル） |
| `Operations.lean` | reverse / dual / dagger API |
| `Motor.lean` | `Ω` 分解、`expTrans`、モーター因数分解 |
| `Invariant.lean` | `J` / `J⁽⁵⁾`、Killing 正規化 |

**証明済み（sorry なし）**

- 二次形式の直交性、`Q311_extend4`
- `e₄² = 0`、`ι e₄` と `ι e_μ` の反可換性
- `Cl(3,1) → G(3,1,1)` 埋め込み (`toPGA_ι`)
- ヌル強消滅 `N_μ N_ν = 0`、`N_μ² = 0`
- `Ω_trans² = 0`、`expTrans = 1 + Ω_trans`
- `J` の係数公式 `J_coef`（Killing 正規化 `×8` 込み）

**フェーズ2 以降に委譲（当時）— 多くはその後完了**

- ~~双曲・循環生成子の平方・reverse-odd 性~~ → 主要分は証明済み
- ~~モーター単位性~~ → 証明済み
- ~~有界性 `|J| ≤ 1`~~ → `JNormalized` 版で証明済み（許容配置上）

### フェーズ2 — インフラ優先（A）完了（2026-08-11）

モジュール追加・更新:

| ファイル | 内容 |
|----------|------|
| `Discrete.lean` | `(ℤ/Nℤ)⁶`、`toTorsionParams`、`IsPrincipalBranch` / `IsAdmissible` |
| `PGA/Normed.lean` | `NormedAlgebra`（左乗法行列ノルム）、`NormedSpace.exp` 用 |
| `UnitGroup.lean` | 離散ローター像 `DiscreteUnit`、有限性 |
| `Motor.lean` | `rotorTorsion = exp(Ω_torsion)`、`rotor_unitary` / `motor_unitary` |
| `Invariant.lean` | `JNormalized`、`torsion_bound`（許容配置上の有界性） |

**証明済み（sorry なし）**

- 離散トーラス `DiscreteTorsion N` の `Fintype` / `Finite`
- `PGA/Normed.lean` — `Module.Finite`、`CharZero`、`NormedAlgebra ℚ`
- `reverse_exp_of_reverse_neg` → `rotor_unitary` / `motor_unitary` 依存鎖が完全に閉じた
- `torsion_bound` の型が主枝条件 `IsAdmissible` 付きに修正され、離散版は連続版へ帰着

### フェーズ2 — 本体（有界性の誠実な形式化）完了

**論文ギャップ（実装しない／無理に閉じない）**

論文 Ch.3 の \(|J|\le 1\) 主張は、同論文の式 \(J=\frac12\sum(\alpha_a^2-\beta_a^2)\) と矛盾する。

- `IsPrincipalBranch`（\(|\alpha_a+\beta_a|\le\pi/2\) のみ）だけでは \(J\) は非有界（反例: \(\alpha=M,\beta=-M+\pi/4\)）
- Appendix の extremal \(\alpha_a=\pi/2,\beta_a=0\) では \(J=3\pi^2/8\approx 3.70\neq 1\)
- BCH 二次打ち切りから \(|\sum(\alpha^2-\beta^2)|\le 2\) への導出は論文内で閉じない
- 全離散トーラス上の \(|J|\le 1\)（許容条件なし）も上記式では偽
- \(J^{(5)}\) の並進項 \(\frac12\eta(\lambda,\lambda)\) は拘束なしでは非有界
- [`discrete-dual-spacetime.tex`](References/discrete-dual-spacetime.tex) は連続極限で局所非有界と述べ、[`dst-diophantine.tex`](References/dst-diophantine.tex) は連続主枝で \(|J|\le 1\) と主張（論文間矛盾）

**Lean で証明した主張**

| 定理 | 内容 |
|------|------|
| `torsion_bound_raw` | 許容離散配置 `IsAdmissible` 上で \(\|J\|\le 3\pi^2/8\) |
| `JNormalized` | \(J_{\rm norm}=\frac{8}{3\pi^2}J\) — Appendix extremal と整合 |
| `torsion_bound` | `IsAdmissible` 上で \(\|J_{\rm norm}\|\le 1\) |
| `torsion_bound_continuous` | `IsAdmissibleContinuous`（非負＋反同期）上で同界 |
| `torsion_bound_naive_false` | `IsPrincipalBranch` のみでは有界性は成り立たない（反例） |

**未着手（フェーズ2時点）**

- Spin 被覆・BCH 一般論・Dirichlet 核による論文 Ch.3 の「完全」導出
- TEGR = Einstein–Hilbert の同値（連続極限の作用そのもの）
- ~~統一降下アルゴリズムの完全終了証明（フェーズ4）~~ → フェーズ4で離散許容問題として完了

### フェーズ2 — 仕上げ（2026-08-11 完了）

| ファイル | 内容 |
|----------|------|
| `Amplification.lean` | `scaleTorsion`、`J_scale`、`pureBoost`、`J_pow_amplify`、`rotorTorsion_pureBoost_pow` |
| `Invariant.lean`（追記） | `J5_unbounded`、`IsSpatialTrans` / `IsBoundedTrans`、`J5_bound_spatial` |
| `Continuum.lean` | `AdmissibleContinuous`、`exists_discrete_approx`（連続許容領域の稠密性） |

**証明済み（sorry なし）**

- スケーリング二次性 `J(c·p) = c² J(p)`
- 純双曲1軸モデルでの厳密 `p²` 増幅
- `J⁵` 並進無拘束非有界（反例）＋有界空間並進での `J⁵` 有界
- 離散格子による連続許容配置の任意精度近似

### フェーズ3 — 整数埋め込み（2026-08-11 完了）

| ファイル | 内容 |
|----------|------|
| `Embedding/IntegerRotor.lean` | `integerRotor`、`integerRotor_mul` / `_pow`、 `rotorTorsion` 接続 |
| `Embedding/NullTranslator.lean` | `nullTranslator`、`nullTranslator_add`、忠実性 `nullTranslator_faithful` |
| `Embedding/PowerMap.lean` | `J_pow_amplify_int`、`logMismatch` |
| `Embedding/RotorClass.lean` | `RotorClass`、`quantizeInt` |
| `Embedding/Height.lean` | `torsionHeight`、`integerHeight`、`descentCandidate` |
| `Embedding/Equation.lean` | `diophantineMotor`、`additive_faithful`、`diophantine_zero_iff` |

**証明済み（sorry なし）**

- 整数ローターの乗法性・冪乗 `R(n·m)=R(n)R(m)`、`R(n^p)=R(n)^p`
- ヌル加法 `T(a+b)=T(a)T(b)` と `T(a)=1 ↔ a=0`
- 純不一致モデルでの `J` 増幅 `J(Ω^p)=p² J(Ω)`
- 加法式ディオファントス式の忠実埋め込み

### フェーズ4 — 統一ディオファントス枠組み（2026-08-11 完了）

| ファイル | 内容 |
|----------|------|
| `Framework/Representation.lean` | 冪和方程式 `PowerSumEquation`、`powerSumMotor`、FLT 形 |
| `Framework/Lattice.lean` | `AdmissibleClass`、`latticeMismatch`、`IsZeroHeight` |
| `Framework/Descent.lean` | `dagger_preserves_height`（論文ギャップ）、`DescentSchema` |
| `Framework/Search.lean` | `findZeroHeight`、決定可能性、`phase4_layers` |

**証明済み（sorry なし）**

- 冪和モータ忠実性 `powerSumMotor e = 1 ↔ eval = 0`（Fermat / 加法特例含む）
- 零高さ ⇔ 整数格子条件 `latticeMismatch = 0`（決定可能）
- 許容条件 ⇔ `4(n.val+m.val) ≤ N`
- dagger は高さを保存する（論文の「厳密減少」は不成立）
- `DiscreteUnit` フィルタは現状自明（`unitFilter_trivial`）
- `DescentSchema.reaches_terminal` と格子探索インスタンス
- `findZeroHeight` の健全性・常に成功（原点が許容零）

**論文ギャップ（無理に閉じない）**

- Ch.10 の dagger による `J` 厳密減少は偽（符号反転のみ）
- 「単位群が候補を絞る」は現行 `DiscreteUnit = range discreteRotor` では追加制約にならない
- 任意多項式 AST の埋め込みは冪和型に制限（FLT / Beal / abc / Goldbach の骨格をカバー）
- 整数方程式の解 ⇔ ある許容格子で `J=0` は量子化誤差のため同値として主張しない（三層 API）

**フェーズ5 へ委譲**

- 7つの個別予想（増幅矛盾・整数サイズ降下の本格インスタンス）
