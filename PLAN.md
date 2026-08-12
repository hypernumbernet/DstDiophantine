# PGA-DST ディオファントス証明基盤 — 研究計画

最終更新: 2026-08-12

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
| **共通 no-go** | `k` 倍増幅 vs 許容有界性 / 粗格子下限 | 証明済み | `Framework/Amplification`, `Algebra/Amplification` |
| **問題別 bridge** | 整数解 ⇒ 増幅証明書（種・格子点） | **未証明** | 各 `Theorems/*.lean` の `*Bridge` |

### 確立済み（機械検証済み・sorry なし）

- PGA / Cl(3,1) / ヌル強消滅 / モーター分解のコア API
- 許容配置上の `|JNormalized| ≤ 1`（naive 全配置有界性は**反例付きで棄却**）
- 純ブーストの `k²` 増幅と連続種高さ上界
- 離散非零高さ下限 `ε_N = 16/(3N²)` と粗トーラス no-go
- 加法 null 忠実性（Fermat / Beal / abc / Goldbach / Polignac の骨格）
- 有限計算証明書（Collatz ≤20、Goldbach ≤100、abc ≤100、RH 有理格子 ≤20）

### 未証明（明示的 bridge・無条件主張しない）

| Bridge | 問題 | 核との接続 |
|--------|------|------------|
| `FermatAdmissibleBridge` | FLT（連続・診断用） | 釣り合い型で偽になり得る（証明済） |
| `FermatCoarseDiscreteBridge` | FLT（粗離散・本命） | `CoarseAmplificationWitness` → 共有 no-go |
| `BealAdmissibleBridge` | Beal | 連続増幅 no-go |
| `AbcAdmissibleBridge` | abc | 品質天井 |
| `CollatzAdmissibleBridge` | Collatz | 軌道・高さ |
| `GoldbachAdmissibleBridge` | Goldbach | 分解候補 |
| `PolignacAdmissibleBridge` | Polignac / 双子 | 強い回避 |
| `RiemannAdmissibleBridge` | RH | 臨界アンサンブル |

### 反例で棄却済み（再設計しない）

- 主枝のみでの `|J| ≤ 1`（`torsion_bound_naive_false`）
- dagger による `J` 厳密減少（`dagger_preserves_height`）
- 現行連続 FLT 閾値「任意解 ⇒ 種 > 1/p²」（`fermat_balanced_seed_lt_threshold`）
- 許容錐への単純折り返し（`p²` 増幅破壊）
- `J5` 単独での bridge 閉鎖（解では `λ = 0`）

---

## 2. 問題類型と再利用パターン

7 予想を単一 bridge 型に押し込まない。類型ごとに証明テンプレートを分ける。

| 類型 | 代表 | 加法 | 乗法 / 高さ | 次の数学課題 |
|------|------|------|-------------|--------------|
| **冪和増幅型** | FLT, Beal | null motor | `k²` 増幅 vs 天井 | 粗量子化証明書 |
| **品質型** | abc | null motor | `H = c₁(q−1)²` | 高品質 ⇒ 許容配置 |
| **軌道型** | Collatz | — | ログ高さ単調 | 軌道 ⇔ 許容流 |
| **加法分解型** | Goldbach, Polignac | null motor | 候補最小 J / 過剰項 | 論理混同の解消 |
| **解析型** | RH | — | 臨界バランス | ζ 接続（長期） |

**最優先軸:** 複数問題に再利用できる PGA-DST 増幅証明基盤（冪和・品質型の共通 no-go と公開 API）。無条件 FLT はその基盤上の最初の本命応用であり、到達点ではないが研究の主戦場の一つ。

---

## 3. 研究優先度

### 高実現性（基盤整備 — 本計画の主対象）

1. **増幅証明書 / no-go の Framework 化** → `Framework/Amplification.lean`
2. **pureBoost 代数 API の集約** → `Algebra/Amplification.lean`
3. **bridge 責務の docstring / 型境界の統一**（仮定 vs 証明済み核）
4. **公開 API（`Basic.lean`）と回帰例**

### 中実現性（次の数学）

1. **Fermat 粗量子化写像** — 整数解 ⇒ `N = O(p)` 上の `CoarseAmplificationWitness`
2. Beal / abc への量子化契約の移植（単純コピー不可；釣り合い型・O(1) 誤差に注意）
3. 有限証明書の拡大（回帰と計算的可触性）

### 探索的

- coprimality の局所・付値層
- null / rotor を結ぶ新不変量（平面括弧・`M = RT` の残存道）
- 非自明な `DiscreteUnit` フィルタ

### 棄却 / 保留

- 現行連続 FLT bridge をそのまま証明する
- dagger 厳密降下・単純折り返し・`J5` 単独解決

---

## 4. 成功判定（本基盤強化）

- [x] FLT / Beal / abc が Fermat 定理ファイルを共通増幅ライブラリ代わりに import しない
- [x] 一般 no-go と問題別 bridge の境界が型として明確（`CoarseAmplificationWitness` 等）
- [x] `PLAN.md` が証明済み・条件付き・反証済み・探索中を区別する
- [x] 無条件 FLT や他予想の達成を主張しない（次課題 = 量子化証明書）
- [x] `lake build` と公開 API 回帰例が成功する

---

## 5. モジュール地図（現行）

```
Algebra/
  QuadraticForm, PGA, Cl31, Generators, Operations, Motor, Invariant
  Discrete, Continuum, UnitGroup
  Amplification          ← pureBoost / スケール / JNormalized_pureBoost / 許容 iff
Framework/
  Representation         ← 冪和モータ忠実性
  Lattice                ← AdmissibleClass / latticeMismatch
  Amplification          ← 連続・離散・粗格子 no-go + CoarseAmplificationWitness
  Descent, Search
Embedding/               ← R(n), T(a), Height, quantizeInt スケルトン
Theorems/
  Fermat                 ← 加法・釣り合い障害・bridge のみ（薄いラッパー）
  Beal, Abc              ← Framework.Amplification を直接利用
  Collatz, Goldbach, Polignac, Riemann
Basic.lean               ← 公開 export（フェーズ6 API 含む）
```

---

## 6. 実装進捗ログ（要約）

詳細なフェーズ 0–5 の歴史的記録は git 履歴と各ファイル docstring を正とする。ここでは現状スナップショットのみ記す。

### フェーズ 0–4 — 完了

環境、PGA コア、離散有界性（正規化版）、整数埋め込み、統一枠組み（三層 API）。論文の naive 有界性・dagger 降下は反例 / 保存定理で正直に記録。

### フェーズ 5 — 完了（すべて条件付き）

7 予想について、加法同値・増幅核または有限証明書・`*_of_bridge` を形式化。古典無条件主張はしない。

### フェーズ 6 — Fermat 完全化（探索中） + 基盤再構成（本更新）

- 釣り合い型で連続 bridge が破綻し得ることを機械検証
- 粗トーラス閾値と `fermat_coarse_discrete_contradiction` を証明
- **本更新:** 問題非依存核を `Framework/Amplification` へ抽出し、Beal/abc の Fermat 依存を切断
- **未解決:** `FermatCoarseDiscreteBridge` の量子化写像（整数解 ⇒ `CoarseAmplificationWitness`）

二セクター図:

```
解 a^p+b^p=c^p ──► null translator = 1          （加法・証明済）
                ┄┄► CoarseAmplificationWitness （乗法・bridge のみ）
                         │
                         ▼
                   共有 no-go（証明済）で矛盾
```

---

## 7. 次アクション

1. Fermat 専用量子化: 加法 null 条件と両立する写像で `FermatCoarseDiscreteBridge` を閉じる
2. 成功した証明書パターンを Beal（`m = min`）/ abc（品質）へ個別再設計
3. 軌道型・加法分解型は増幅系と別系列として bridge 診断を継続
4. 長期: mathlib PGA contrib、References 論文ギャップの文書化

**最終目標（長期）:** 7 予想を「離散双対時空代数の内部で許容増幅証明書が存在しない」という単一原理から導く完全機械検証。現状はそのための **共通 no-go 基盤** を固めた段階であり、無条件古典定理はまだ未達成である。
