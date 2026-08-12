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
3. ~~**Goldbach・Polignac（双子素数含む）**~~ → 完了（条件付き bridge）  
   偶数ギャップのヌルトランスレータ表現と最小 `J` 分解・強い回避過剰。
4. ~~**abc予想**~~ → 完了（条件付き bridge）  
   コプライム三重項のねじれ高さによる品質の有界性。連続極限での古典的主張の回復も。
5. ~~**リーマン予想**（最難）~~ → 完了（条件付き bridge）  
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

### フェーズ5 — Fermat 最終定理・Beal 予想（2026-08-11 完了）

| ファイル | 内容 |
|----------|------|
| `Theorems/Fermat.lean` | 加法モータ同値、mismatch↔pureBoost、p² 増幅 vs 許容有界性、離散高さ下限、条件付き古典 FLT |
| `Theorems/Beal.lean` | Beal 形冪和、`m=min(x,y,z)` 増幅 vs 許容有界性、条件付き共通素因数、等指数→FLT 回収 |
| `Framework/Representation.lean` | `bealEquation` / `bealMotor_one_iff` / `bealEquation_eq_fermat` |

**証明済み（sorry なし）— Fermat**

- `fermat_solution_iff_motor` / `fermat_pos_lt`（正整数解 ⇒ `a < c`）
- `mismatchRotor_eq_rotorTorsion`（`logMismatch` との係数 2 を明示）
- `amplification_implies_seed_le` / `fermat_amplification_contradiction`
- `discrete_nonzero_height_lb`（`|JNormalized| ≥ 16/(3N²)`）と離散増幅矛盾
- `fermat_last_theorem_of_bridge`（`FermatAdmissibleBridge` 仮定付き）

**証明済み（sorry なし）— Beal**

- `beal_solution_iff_motor` / `bealEquation_eq_fermat`
- `bealMinExp` / `bealGcd` と `beal_amplification_contradiction`（`m²` 増幅）
- `beal_discrete_amplification_contradiction`（Fermat 離散核の再利用）
- `beal_conjecture_of_bridge`（`BealAdmissibleBridge` 仮定付きで `gcd > 1`）
- `beal_eq_exp_not_coprime_of_bridge`（等指数の原始解排除）

**論文ギャップ（無理に閉じない）**

- 古典 FLT / Beal の無条件主張はしない（連続整数ローター ⇔ 許容増幅配置の橋は未証明）
- Beal の分数冪不一致・三項 BCH・素数ローターによる共通因子消去は形式化しない（下限 `m²` 単軸模型）
- 細かい離散トーラスでは最小高さ `O(1/N²)` が `1/p²`・`1/m²` を下回りうる
- ~~Collatz~~ → 下記完了；~~Goldbach / Polignac~~ → 下記完了；~~abc~~ → 下記完了；~~RH~~ → 下記完了
- **完全化探索** → 下記「フェーズ6 — Fermat 完全化アイデア」（**最終目標: 無条件 FLT**）

### フェーズ5 — Collatz 予想（2026-08-11 完了）

| ファイル | 内容 |
|----------|------|
| `Theorems/Collatz.lean` | Collatz ステップ・高さ符号化、閉路高さ超過、有限型周期性、≤20 証明書、条件付き古典回収 |

**証明済み（sorry なし）— Collatz**

- `collatzStep` / `collatzIter` / `ReachesOne` と吸引閉路 `4→2→1`
- `collatzHeight`（`integerHeight`）と偶数収縮・奇数デルタ `log(3n+1)=log n+log(3+1/n)`
- `collatzHeight_le_one_implies_le_three` / `collatz_cycle_avoids_one_exceeds_bound`
- `eventually_periodic_of_fintype`（有限型上の最終周期性）
- `reachesOne_of_le_twenty`（燃料付き有限探索証明書）
- `collatz_conjecture_of_bridge`（`CollatzAdmissibleBridge` 仮定付き）

**論文ギャップ（無理に閉じない）**

- 古典 Collatz の無条件主張はしない（古典軌道 ⇔ 高さ有界ローター流の橋は未証明）
- 奇数段の `Γ₁` 剪断は純双曲モデル `log(3+1/n)` で代替
- 吸引閉路 `4→2→1` 自体は連続埋め込みで `|JNormalized|≤1` に収まらない点を含む
- ~~Goldbach / Polignac~~ → 下記完了；~~abc~~ → 下記完了；~~RH~~ → 下記完了

### フェーズ5 — Goldbach・Polignac（双子素数含む）（2026-08-12 完了）

| ファイル | 内容 |
|----------|------|
| `Theorems/Goldbach.lean` | Goldbach 対・モータ同値・目標高さ・候補最小 J・≤100 証明書・条件付き古典回収 |
| `Theorems/Polignac.lean` | 偶ギャップ・強い回避過剰・鎖高さ・双子系・小証明書・条件付き古典回収 |
| `Framework/Representation.lean` | `goldbachEquation` / `gapEquation` |

**証明済み（sorry なし）— Goldbach**

- `IsGoldbachPair` / `goldbach_sum_iff_motor` / `goldbach_solution_iff_motor`
- `goldbachTargetHeight_gt_one_of_four_le`（`n≥4` で整数ロータ高さ `>1`；分解の有無と独立）
- `exists_min_goldbachMismatch`（有限候補上の最小ミスマッチ高さ）
- `goldbach_of_le_hundred`（偶数 `4…100` の有限探索証明書）
- `goldbach_conjecture_of_bridge`（`GoldbachAdmissibleBridge` 仮定付き）

**証明済み（sorry なし）— Polignac / 双子素数**

- `IsPolignacPair` / `IsTwinPrimePair` / `polignac_gap_iff_motor`
- `even_gap_of_odd_prime_pair`（奇素数差は偶数）
- `strong_avoidance_term_ge` / `gapChainHeight_gt_one_of_sq`（強い回避 `g≥2k+2` のみ）
- `exists_twin_of_le_twenty` および gap `4`,`6` の小証明書
- `polignac_conjecture_of_bridge` / `twin_prime_conjecture_of_bridge`

**論文ギャップ（無理に閉じない）**

- 古典 Goldbach / Polignac / 双子素数の無条件主張はしない
- Goldbach の「対が無い ⇒ 既約 ⇒ `J_norm(2n)>1`」は加法分解と乗法ロータ高さを混同（高さ超過自体は常に成り立つ）
- Polignac の弱い回避 `g_n≠2k` から過剰項が正とは限らない；Lean は強い回避のみを証明
- ~~abc~~ → 下記完了；~~RH~~ → 下記完了

### フェーズ5 — abc 予想（2026-08-12 完了）

| ファイル | 内容 |
|----------|------|
| `Theorems/Abc.lean` | 原始三重項・radical・品質・純双曲高さ・天井・≤100 証明書・条件付き古典回収 |
| `Framework/Representation.lean` | `abcEquation` / `abcMotor_one_iff` |

**証明済み（sorry なし）— abc**

- `IsAbcTriple` / `abcRadical` / `abcQuality` / `abc_sum_iff_motor`
- `abcHeight_eq_quality`（純双曲モデルで `H = c₁ (q−1)²`）
- `abc_quality_bound_of_admissible` / `abc_amplification_contradiction`
- `discrete_abc_bound` / `discrete_abc_height_lb`（`ε_N` 再利用）
- `abc_radical_pow_of_le_hundred`（`c ≤ 100` で `c ≤ rad(abc)²`）
- `abc_conjecture_of_bridge`（`AbcAdmissibleBridge` 仮定付き）

**論文ギャップ（無理に閉じない）**

- 古典 abc の無条件主張はしない（高品質三重項 ⇔ 許容純双曲配置の橋は未証明）
- 双対セクター `R_dual(p)` / `lem:radical-dual` と品質–高さの `O(1)` 誤差は形式化しない
- ~~RH~~ → 下記完了

### フェーズ5 — リーマン予想（2026-08-12 完了）

| ファイル | 内容 |
|----------|------|
| `Theorems/Riemann.lean` | 臨界ミスマッチ・dagger 対称・層スケール・有理格子証明書・条件付き古典回収 |

**証明済み（sorry なし）— RH**

- `primeRotor` / `finitePrimeEnsemble`（有限アンサンブル；Euler 積はしない）
- `criticalMismatchParams` / `critical_J_eq` / `critical_zero_iff`（`θ≠0` で `J=0 ↔ σ=1/2`）
- `critical_dagger`（`σ ↔ 1−σ`）と `criticalHeight_dagger`
- `layerScale` / `critical_zero_layer_invariant`
- `critical_balance_of_le_twenty` / `critical_balance_ok_of_le_twenty`
- `riemann_hypothesis_of_bridge`（`RiemannAdmissibleBridge` 仮定付き）
- `critical_line_of_zero_ensemble`（代数的臨界線定理）

**論文ギャップ（無理に閉じない）**

- 古典 RH の無条件主張はしない（非自明零点 ⇔ 許容零点アンサンブルの橋は未証明）
- Euler 積のロータ置換・解析接続・`ζ(ρ)=0 ⇔ J(ρ)=0`・PNT 誤差は形式化しない
- mathlib `riemannZeta` は未使用

---

### フェーズ6 — Fermat 完全化アイデア（探索ログ・2026-08-12）

**最終目標（断言）:** Lean 上で **無条件の古典 Fermat 最終定理**  
（`∀ a b c p, 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 → ¬(a^p + b^p = c^p)`）  
を、未証明の bridge 仮定なしに機械検証すること。条件付き定理 `fermat_last_theorem_of_bridge` は途中成果にすぎない。

本節はその目標に向けた探索ログである。現行 a–c 純ブースト模型のまま bridge を `True` と宣言したり、`sorry` で穴を埋めたりして「無条件 FLT 達成」と偽ることはしない。模型／閾値／量子化を再設計し、本当に無条件証明へ到達する。

#### 目的と非目標

| する | しない |
|------|--------|
| **無条件 FLT を最終到達点として追求する** | 条件付き定理で満足して打ち切る |
| bridge / 模型の弱点を診断し、無条件化に必要な再設計を行う | `sorry` や偽の bridge 証明で無条件 FLT を装う |
| PGA（加法 null / 乗法 rotor / `M=RT`）を活用した攻撃案を評価 | 論文ギャップを隠蔽したまま古典 FLT を宣言する |
| 証明可能な補題から積み上げ、最終的に bridge を消去する | Beal 全般の三項 BCH を一気に形式化（Fermat 専用なら検討可） |

#### PGA-DST 再読の要点（引用）

[References/dst-pga.tex](References/dst-pga.tex) は FLT 証明論文ではなく、加法と乗法を同一代数に載せる幾何インフラ:

- **強消滅** `N_μ N_ν = 0`（`eq:null-strong-vanishing`）→ null 指数の 1 次切断 `exp(Ω_trans)=1+Ω_trans`（`eq:exp-truncation`）
- **分解** `Ω_biv^{(5)} = Ω_torsion + Ω_trans`（`eq:Omega-decomp`）、モーター `M = R T`
- **拡張不変量** `J^{(5)} = J + (1/2) η_μν λ^μ λ^ν`（`eq:J5-invariant`）。有界定理はねじれ部のみ（論文 Rem. / Lean `J5_unbounded`）
- **ユニタリ** null 側 `T \widetilde{T} = 1`（`eq:null-unitarity`）

[References/dst-diophantine.tex](References/dst-diophantine.tex) §5 / Lean `Theorems/Fermat.lean`:

- 加法: `powerSumMotor = 1 ↔ a^p+b^p=c^p`（証明済）
- 乗法核: 許容純ブーストで `J ↦ p² J` vs `|J_norm|≤1`（`thm:torsion-bound` / `fermat_amplification_contradiction`）
- 古典回収: `def:fermat-bridge` = `FermatAdmissibleBridge`（未証明）

二セクター図:

```
解 a^p+b^p=c^p ──► null translator = 1          （加法・証明済）
                ┄┄► 許容な増幅 pureBoost        （乗法・bridge のみ）
                         │
                         ▼
                   |J_norm|≤1 と矛盾し得るには
                   種 |J_norm| > 1/p² が必要
```

#### 現行 bridge の数値・漸近診断（アイデア A）

`JNormalized(pureBoost θ) = (4/(3π²)) θ²`。釣り合い型（`a=b` ⇒ `c/a = 2^{1/p}` ⇒ `θ = (ln 2)/p`）では:

| p | θ ≈ (ln 2)/p | 種 `J_norm` | 閾値 `1/p²` | 種/閾値 | 増幅後 `J_norm` |
|---|-------------|------------|------------|---------|----------------|
| 3 | 0.231 | 7.21e-3 | 0.111 | **0.065** | **0.065 < 1** |
| 5 | 0.139 | 2.60e-3 | 0.040 | **0.065** | **0.065 < 1** |
| 任意 | (ln 2)/p | ∝ 1/p² | 1/p² | `(4/(3π²))(ln 2)² ≈ 0.065` | 同左 |

- `mismatchRotor` の係数 2（`θ ↦ 2Δlog`）でも種/閾値 ≈ **0.260** でなお不足、増幅後 ≈ 0.260 < 1。
- 種 > `1/p²` に必要な θ は ≈ `2.721/p`。釣り合い θ ≈ `0.693/p` はその約 1/4。
- 釣り合い増幅ラピディティは `p·θ = ln 2 ≈ 0.693 ≤ π/2` なので **増幅配置は許容に入り得る**。すなわち bridge の連言 1（許容）は成り立ち得て、連言 2（種大）が失敗する。

**判定:** 自然な a–c 純ブースト模型では、現行 `FermatAdmissibleBridge` の「任意の非零解 ⇒ 種 > 1/p²」は **釣り合い型で偽になり得る**。したがって無条件 FLT への本命は、この bridge をそのまま証明することではなく、**釣り合い型でも矛盾が出る模型／閾値／量子化への再設計**である（目標はあくまで無条件 FLT）。

#### アイデア B–E の結果

| ID | 内容 | 判定 | 理由・残課題 |
|----|------|------|-------------|
| A | 種高さ診断 | **棄却方向（現行 bridge 第2連言）** | 上表。docstring で弱点を明示する価値あり |
| B | 係数2整合 / 三項ロータ `R(a)^p R(b)^p R(c)^{-p}` | **部分有望 / 三項は棄却寄り** | 係数2でも釣り合いでは不足。三項積は `R(a^p b^p/c^p)` で **乗法積**を測り加法 Fermat と不一致；大 `|a|` で許容錐を即脱出。PGA の `M=RT` は「解 ⇒ T=1」までで、平面括弧（§4）から R 側許容を強制する道は現状見えない |
| C | 離散 `N = O(p)` 粗トーラス | **有望（弱い bridge 草案）** | `16/(3N²) > 1/p²` ⇔ `N < (4/√3)p ≈ 2.3p`（例: p=3 なら N≤6、p=5 なら N≤11）。残課題は「整数解 ⇒ その N 上の非零許容ミスマッチ」という量子化写像 |
| D | `J5` / 空間並進有界 | **棄却（単独では bridge を閉じない）** | 解では `eval=0` ⇒ `λ=0` ⇒ `J5=J`。`J5_bound_spatial` はねじれ有界に帰着 |
| E | 許容錐への単純折り返し | **棄却** | `fold(pθ) ≠ p·fold(θ)` で `p²` 増幅が壊れ、核と非整合 |

#### 次に Lean で実装すべき候補（優先順・無条件 FLT 向け）

1. ~~**`FermatAdmissibleBridge` docstring 改訂**（最小）~~ → 完了
   釣り合い型での破綻可能性と、「最終目標は無条件 FLT；現行 bridge は仮の足場」を明記する。
2. ~~**種高さの証明可能補題**~~ → 完了
   例: `JNormalized(pureBoost θ) = (4/(3π²))θ²` の明示、釣り合い型での `種 < 1/p²` を定理化し、現行模型では足りないことを機械検証する（再設計の正当性の証拠）。
3. **`N = O(p)` 離散戦略の定義スケルトン → 量子化写像の証明**（スケルトン・閾値完了、量子化写像は未完）
   粗いトーラス上で増幅矛盾が効く形に持ち込み、最終的に bridge 仮定なしの古典 FLT へ接続する。ここが無条件化の主戦場。

#### フェーズ6 — Lean 実装進捗（2026-08-12）

| ファイル | 追加内容 |
|----------|----------|
| `Algebra/Amplification.lean` | `JNormalized_pureBoost`（純ブースト正規化高さの閉形式） |
| `Theorems/Fermat.lean` | 釣り合い型の厳密障害、粗トーラス閾値、離散 bridge スケルトン |

**証明済み（sorry なし）**

- `fermat_balanced_seed_constant_lt_one`: 小数近似を使わず \(\frac{4}{3\pi^2}(\log 2)^2<1\)
- `fermat_balanced_seed_height_eq` / `fermat_balanced_seed_lt_threshold`: \(\theta=\log 2/p\) では種高さが厳密に \(1/p^2\) 未満
- `isAdmissibleContinuous_pureBoost_iff` / `fermat_balanced_amplification_admissible`: 純ブーストの許容条件を整理し、釣り合い種の \(p\) 倍が連続許容錐内にあることを証明
- `fermat_coarse_height_gap`: \(3N^2<16p^2\) なら \(1/p^2<16/(3N^2)\)
- `fermat_coarse_condition_of_le_two_mul`: 単純な線形条件 \(N\le 2p\) が上記粗さ条件を満たす
- `fermat_coarse_discrete_contradiction`: 粗トーラス上の非零格子点と \(p\) 倍後の許容性が両立しないことを再利用可能な核として分離
- `FermatCoarseDiscreteBridge` / `fermat_last_theorem_of_coarse_discrete_bridge`: 必要な量子化像を明示した弱い bridge と、上記矛盾核から古典 FLT を回収する定理

**現在の未解決点**

- `FermatCoarseDiscreteBridge` 自体は未証明。整数解から \(N=O(p)\) 上の「非零・許容・増幅後も許容」な格子点を構成する量子化写像が必要
- したがって無条件 FLT はまだ未達成。次は `quantizeInt` の単純な差ではなく、加法 null 条件と両立する Fermat 専用量子化の設計・不変量証明

#### 探索時点の結論

- **目標は無条件 FLT。** 現状の条件付き定理は到達点ではない。
- DST 増幅核は健全。足りないのは「整数解 → 種が十分大きい許容純ブースト」という **量子化＋閾値** の接続であり、現行 bridge はそのままでは偽になり得る。
- PGA は加法忠実性を既に支えているが、`J5` や平面括弧だけでは乗法側は閉じない。
- 最有望な次路線は **(C) 粗い離散トーラス + 明示的量子化写像の証明** と、それに合う **模型／閾値の再設計**。成功条件は bridge の消去と無条件 FLT 定理の追加である。
