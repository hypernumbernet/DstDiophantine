# 四値論理 D4L — 真と偽だけでは足りないとき

二重時空理論（DST）の論理は、二重時空四値論理（D4L）一つです。命題の担体は許容ねじれ配置、測定は正規化高さ  $J_{\mathrm{norm}} $、崩壊が四つのラベルです。この文書は入門から数理と Lean 検証までを一つの流れで書きます。

機械検証で差が出るのは、**古典二値（およびその二つの制限）がホストできない充足・帰結・格子の問題を、D4L がホストする**ことです。Lean は同じ問題文に対し、二値側の空性（または空虚さ、単元への潰れ）と D4L 側の実現を対で固定しています。

**検証の現状。** 振幅、四状態、結合子の非爆発、二つの順序、Killing 重なり、異軸干渉は証明済みです。構文・指定値・帰結と、二値が担えない四つの例（否定固定点、非爆発、 $J_{\mathrm{norm}}<1 $、相補性）も機械検証しました。入口は `DstDiophantine/Logic.lean` です（`Basic.lean` には入れません）。代表論文は `papers/dst-4-valued-logic.tex`（日本語 `papers/japanese/dst-4-valued-logic-ja.tex`）です。

---

## 1. 位置づけ

普通、論理は「真か偽か」の二値で考えることが多いです。四値論理は、そこに中間と矛盾を加えます。

| 論理 | 状態 |
|------|------|
| 二値 | 真（True）と偽（False）だけ |
| 四値 | 真・偽に加え、未決定と「真でも偽でもある」 |

D4L の四状態は、抽象的なラベルの寄せ集めではありません。DST ですでに証明済みの不変量  $J_{\mathrm{norm}}\in[-1,1] $ を、符号と飽和で四つに分けたものです。

D4L には二つの層があります。演算は同一視しません。

- **振幅層。** 許容配置が命題、 $J_{\mathrm{norm}} $ が観測量、スカラー結合子は  $\min/\max/- $。Killing 重なりとねじれ双ベクトルの交換子もここに属します。
- **双対 Hilbert 層。** 双対セクターの運動学として  $\mathbb{C}^2 $ とその部分空間格子（Birkhoff–von Neumann）があります。

いま機械検証できている核は、四状態そのものと、二値が担えない四つの例です。

---

## 2. 四つの状態と  $J_{\mathrm{norm}} $

| 状態 | 意味 |  $J_{\mathrm{norm}} $ |
|------|------|------------------------|
| **T** (True) | 完全同期 |  $=0 $ |
| **U** (Undetermined) | 未決定・boost 優勢 |  $0<J_{\mathrm{norm}}<1 $ |
| **F** (False) | 最大正トーション（全軸純双曲） |  $=+1 $ |
| **B** (Both) | 真でも偽でもある・rotation 優勢 |  $-1\le J_{\mathrm{norm}}<0 $ |

普通の二値論理では「真であり偽である」は爆発（何でも導ける）を起こします。D4L は **B** を認め、結合子  $j\wedge\neg j=-|j| $ が決して **F** にならないことで爆発を止めます。ただし **B** のラベル全体が一つの点なのではありません。最深の  $B $ は端点  $J_{\mathrm{norm}}=-1 $ です。内部の  $B $ は範囲です。

DST において、通常時空ローター  $R_{\mathrm{usual}} $ と双対時空ローター  $R_{\mathrm{dual}} $ の相対関係は

$$
\Omega = R_{\mathrm{usual}}^{\dagger} R_{\mathrm{dual}}, \qquad
\Omega_{\mathrm{biv}} = \log \Omega
$$

です。パラメータ展開  $\Omega=\sum(\alpha_a/2)B^{+}_a+(\beta_a/2)B^{-}_a $ のもと、プロジェクトが使う生のトーションは

$$
J = \frac12\sum_{a=1}^{3}\bigl(\alpha_a^2-\beta_a^2\bigr)
$$

です。許容錐（各軸  $\alpha_a\ge 0 $、 $\beta_a\ge 0 $、 $\alpha_a+\beta_a\le\pi/2 $）の上で  $|J|\le 3\pi^2/8 $ です。古い草稿の  $\frac1{16}B(\Omega_{\mathrm{biv}},\Omega_{\mathrm{biv}}) $ は、同じ展開では  $J $ と定数倍だけずれます（Lean: `paper_appendix_killing_coeff_false`）。

真理値の座標は、天井を  $1 $ に直した正規化

$$
J_{\mathrm{norm}} := \frac{8}{3\pi^2}\,J \in [-1,1]
$$

です。許容錐上の有界  $|J_{\mathrm{norm}}|\le 1 $、像がちょうど  $[-1,1] $、等号  $|J_{\mathrm{norm}}|=1 $ が全軸純双曲または全軸純楕円であること、はすでに証明済みです。 $\lvert F\rangle $ は純双曲、最深の  $\lvert B\rangle $ は純楕円です。混合極端——ある軸がブースト、別の軸が回転——は  $|J_{\mathrm{norm}}|=1 $ に届きません。

### 結合子と否定

符号付き高さの上で

$$
\neg j = -j, \qquad j\wedge k=\min(j,k), \qquad j\vee k=\max(j,k)
$$

です。De Morgan と分配則は実数の  $\min/\max $ のものです。非爆発は

$$
j\wedge\neg j=\min(j,-j)=-|j|\le 0
$$

なので、 $p\wedge\neg p $ は  $T $（ $j=0 $）または  $B $ であり、決して  $F $ になりません（`classify_conj_neg_ne_F`）。

代数的な否定は、通常–双対スワップ  $\alpha\leftrightarrow\beta $（`daggerParams`）が誘導する  $J_{\mathrm{norm}}\mapsto -J_{\mathrm{norm}} $ です。新しい論理演算ではなく、PGA の対合です。しかし四つの**名前**の上では関数になりません（`neg_not_a_function_of_TruthValue`）。

|  $J_{\mathrm{norm}} $ | 状態 |  $-J_{\mathrm{norm}} $ | 像の状態 |
|----------------------|------|------------------------|----------|
|  $0 $ |  $T $ |  $0 $ |  $T $ |
|  $1 $ |  $F $ |  $-1 $ | 最深  $B $ |
|  $-1 $ | 最深  $B $ |  $1 $ |  $F $ |
|  $(-1,0) $ |  $B $ |  $(0,1) $ |  $U $ |
|  $(0,1) $ |  $U $ |  $(-1,0) $ |  $B $ |

同じラベル  $B $ でも、最深点は  $F $ へ、内部は  $U $ へ行きます。四ラベルの上の関数として否定を書くことはできません。

---

## 3. なぜ二値では担えないのか

「四値論理でしか解けない」は、Lean が二値より強い証明器だという意味ではありません。計算量の話でもありません。二値代数がホストできない充足・帰結・格子の問題を、D4L がホストし、その差を Lean が**空性と実現の対**として固定している、という意味です。

これらは意味論の変更であり、ペアノ算術の新しい定理ではありません。無条件の FLT / Beal / abc も、ゲーデル定理の反証も主張しません。

### 指定値と帰結

論理式は原子、 $\neg $、 $\wedge $、 $\vee $ から生成し、`negJ` / `conjJ` / `disjJ` で評価します。含意結合子は置いていません。 $\min $ の剰余の頂は  $+1=\lvert F\rangle $ になってしまうので、含意を足すなら指定値の設計からやり直す必要があります。

付値は各原子に  $[-1,1] $ の高さを与えます。指定述語は二つです。

| 述語 | 定義 | 読み |
|------|------|------|
| `HoldsT` |  $j=0 $ | 同期している（ラベル  $T $） |
| `HoldsNotF` |  $j<1 $ | 反駁されていない（ $F $ 以外のすべてのラベル） |

帰結も二つです。 $\Gamma\models_T\psi $（`EntailsT`）は、 $\Gamma $ を同期するすべての付値が  $\psi $ を同期すること。 $\Gamma\models_{\lnot F}\psi $（`EntailsNotF`）は同じ条項を非反駁で書いたものです。どちらも古典的帰結ではありません。

### 二値制限は一つではない

D4L の名前  $T,F $ は古典の真／偽ではないので、区間の二値制限は一意ではありません。

| フラグメント | 集合 | 否定 | 古典か |
|--------------|------|------|--------|
| **壁** `IsWallTwo` | `{-1, +1}` = {最深  $B $,  $F $} | 入れ替わる。固定点なし | 古典の忠実な核 |
| **名前** `IsNamedTwo` | `{0, 1} = {T, F}` |  $\neg T=T $。 $\neg F= $ 最深  $B $ で閉じていない | ラベルは揃うがブールではない |
| **`Bool`** | `{true, false}` | 入れ替わる。固定点なし | 古典そのもの |
| **全 D4L** |  $[-1,1] $ の四ラベル | ラベルの関数ではない | パラコンシステント |

名前フラグメントは否定の固定点をすでに含み、しかも  $\neg $ で閉じていません（`negJ_zero`、`namedTwo_not_closed_under_neg`）。壁フラグメントでは  $j\neq\neg j $ かつ  $\neg $ で閉じます（`wallTwo_neg`、`wallTwo_not_negFixed`）。古典と比較するときは壁を使い、名前で「 $T $ と  $F $ だけ」と比較すると、すでに古典ではありません。

Lean のやり方は単純です。同じ問題文に対し、フラグメント上で  $\nexists $（または空虚、単元への潰れ）を証明し、D4L 上で  $\exists $（または三ラベルの inhabited）を証明します。次の四例がその対です。

---

## 4. 例1：否定の固定点

**問題。**  $P=\neg P $、すなわち高さで  $j=\neg j $。

古典二値では、否定に固定点がありません。 $P\leftrightarrow\neg P $ にモデルがありません。壁フラグメントでも同じです。 $j\in\{-1,+1\} $ なら  $j\neq -j $ なので、壁に制限した付値は条件を満たせません。

D4L では  $j=-j $ は  $j=0 $ と同値です。一意の解はラベル  $T $（完全な通常–双対バランス）です。定数  $0 $ の付値でも、振幅でも実現されます。

| 側 | 内容 | Lean |
|----|------|------|
| 壁では空 | 壁付値で  $P=\neg P $ は充足不能 | `not_exists_wall_negFixed`、`wallTwo_not_negFixed` |
| D4L では一意 |  $j=\neg j\iff j=0 $。振幅でも実現 | `isNegFixed_iff_zero`、`exists_negFixed_valuation`、`exists_amplitude_negFixed` |

場所は `Logic/Example/FixedPoint.lean` です。これはゲーデル文ではありません。自己言及的な**等式**  $P=\neg P $ が、否定に固定点のない代数ではホストできず、D4L では同期点に一意に座る、という事実です。

---

## 5. 例2：爆発しない矛盾

**問題。**  $\{P,\neg P\} $ から無関係な  $Q $ が従うか。

古典二値には *ex falso quodlibet*（爆発原理）があります。 $\{P,\neg P\} $ は任意の  $Q $ を含意します。ただし Lean の `Bool` の上では、 $P=\mathtt{true} $ かつ  $\neg P=\mathtt{true} $ がすでに不可能なので、含意は空虚です（`bool_efq`）。壁でも  $j $ と  $\neg j $ がともに  $+1 $ にはなれません（`wall_not_both_pos`）。二値側の爆発は、前提が同時に指定値を取れないことの言い換えです。

D4L では前提が同時に指定値を取れます。 $P $ を原子  $0 $、 $Q $ を原子  $1 $ とすると

$$
\{P,\neg P\}\not\models_T Q, \qquad
\{P,\neg P\}\not\models_{\lnot F} Q.
$$

証人は二つです。

- T-帰結の反例： $P\mapsto 0 $（よって  $\neg P\mapsto 0 $）、 $Q\mapsto 1 $。矛盾対はともに同期し、無関係原子は  $F $。
- 非反駁帰結の反例： $P\mapsto -1/2 $（内部の  $B $、 $\neg P $ は  $U $）、 $Q\mapsto 1 $。矛盾対はともに非反駁で、無関係原子は  $F $。

連言  $j\wedge\neg j $ 自体も常に非反駁です（`conj_neg_holdsNotF`）。矛盾した観測の対は、無関係な原子を正の壁へ強制しません。

| 側 | 内容 | Lean |
|----|------|------|
| `Bool` は空虚 |  $P $ と  $\neg P $ は同時に true になれない | `bool_not_both`、`bool_efq` |
| 壁も同時指定できない | 両方  $+1 $ は不可 | `wall_not_both_pos` |
| D4L は爆発しない | 二つの証人。連言は常に非反駁 | `contradict_not_entailsT_atom`、`contradict_not_entailsNotF_atom`、`conj_neg_holdsNotF` |

場所は `Logic/Example/Explosion.lean` です。

---

## 6. 例3：制約  $J_{\mathrm{norm}}<1 $

**問題。** 一意の全ブースト世界（ $j=1 $、ラベル  $F $）に坐ることを禁じられた文は、何を残すか。指定述語ではこれが `HoldsNotF` そのものです。

名前フラグメント  $\{0,1\} $ の上では、 $j<1 $ は  $j=0 $ に潰れます。残りは  $\{T\} $ だけです（`namedTwo_notF_only_T`）。名前で「真と偽」を切ったつもりでも、非反駁は同期と一致してしまいます。

D4L では同じ制約が三つのラベルで実現されます。

$$
\mathrm{HoldsNotF}\quad\text{は}\quad \{T,U,B\}\ \text{を inhabited にする。}
$$

`U` はラベルとして inhabited です。

| 側 | 内容 | Lean |
|----|------|------|
| 名前では単元 | `HoldsNotF` が `HoldsT` に潰れる | `namedTwo_holdsNotF_iff_holdsT`、`namedTwo_notF_only_T` |
| D4L では三ラベル |  $T,U,B $ がいずれも非反駁。振幅でも実現 | `exists_three_notF_labels`、`exists_amplitude_notF` |

場所は `Logic/Example/NotFalse.lean` です。論文の自己言及の読みの Lean 形ですが、ゲーデル定理の否定ではありません。

### 自己言及の読み（注意）

 $G $ を「 $G $ はこの体系で証明可能ではない」という文とします。D4L では、証明可能性を同期  $J_{\mathrm{norm}}\to 0 $、すなわち  $T $ への駆動として読むことができます。一意の全ブースト世界に坐ることを禁じられた文に対する誠実な制約は、いまの `HoldsNotF` そのものです。

$$
J_{\mathrm{norm}}(G)<1.
$$

この制約は  $G $ をラベルとして  $T $、 $U $、または  $B $ に残します。さらに同期を要求するなら  $T $ です。連言は爆発しません（例2）。

これは意味論の変更です。ゲーデルの定理が古典算術において失敗することの証明ではありません。負トーションセクター上の完全性の話も、許容ローターの読みであって、一次ペアノ算術の内部でのヒルベルト計画の完了ではありません。固定された内容は例1–4の Lean 定理であり、この読みは新しい不完全性定理ではありません。

---

## 7. 例4：相補性

**問題。** 相補的な光線にブール値を割り当てられるか。四つの D4L ラベルを  $\mathbb{C}^2 $ の直交射影（PVM）と同一視できるか。

双対 Hilbert 層では、命題は  $\mathbb{C}^2 $ の部分空間です。交わりが meet、和が join、直交補空間が否定です。この格子はオーソモジュラーですが、分配的ではありません。したがってブール代数ではありません。互いに直交する原子（一次元部分空間）は高々二つです。次元 2 は四つの互いに直交する光線を供給できません。

振幅層のスカラー結合子  $\min/\max $ は分配的です。分配的な代数は、非分配な部分空間格子を表示できません。四ラベルを四本の直交光線に送る写像も存在しません。

| 側 | 内容 | Lean |
|----|------|------|
| 格子はブールでない |  $\mathbb{C}^2 $ の部分空間格子は非分配 | `not_distributive`、`orthomodular` |
| 直交原子は二つまで | 三本の互いに直交する直線はない | `no_three_pairwise_orthogonal_lines` |
| 四ラベルは PVM でない |  $T,U,F,B $ を四本の直交光線へは送れない | `four_labels_not_orthogonal_pvm` |
| 層の演算は同一視できない | 分配的 `min`/`max` はその格子に同型でない | `scalar_lattice_not_iso_qprop` |

これらは双対層の既存定理です。例専用の別名モジュールは置いていません。場所は `Logic/Quantum/QuantumLogic.lean` と `Logic/Quantum/Dictionary.lean` です。

---

## 8. 振幅・順序・幾何

命題の一次対象は、区間上のスカラーではなく許容ねじれ配置です。測定  $\langle p\rangle=J_{\mathrm{norm}}(p) $ のあとで四つのラベルが現れます。新しい Clifford 代数は足していません。

| 層 | 担体 | Lean |
|----|------|------|
| 振幅 | 許容配置  $p $、 $\Omega(p) $、 $R(p)=\exp\Omega(p) $ | `Amplitude` |
| 四状態 |  $J_{\mathrm{norm}}\in[-1,1] $ → `{T,U,F,B}` | `TruthValue`、`Connective` |
| 構文・指定値・帰結 | 論理式、`HoldsT` / `HoldsNotF`、二つのフラグメント | `Formula`、`Valuation`、`Consequence` |
| 順序 | 高さ  $j\preceq_\tau k\iff j\le k $、情報  $j\preceq_\iota k\iff |j|\le|k| $ | `Order` |
| 幾何 | Killing 重なり、交換子、PGA 合成 | `Geometric` |
| 双対 Hilbert |  $\mathbb{C}^2 $、四元数表、部分空間格子 | `Logic/Quantum/` |

- **重なり**  $\langle p\mid q\rangle=\texttt{killingForm}\,p\,q $。対称。自己対は  $16J $（`overlap_self`）。Hilbert 内積ではありません。Killing 形式は不定で、自己重なりは負になり得るので Born 確率でもありません（`killingForm_indefinite`、`overlap_self_not_born_probability`）。
- **干渉**  $[\Omega(p),\Omega(q)] $。異軸では一般に 0 でない（`interfere_axis0_axis1_ne_zero`）。同軸では消える（`interfere_axis0_self`）。
- **合成**  $R(p)R(q) $ は PGA に留める。BCH で `TorsionParams` へは戻さない。
- **評価** `sandwich` を Gravity 非依存で再掲。退化計量の保存は主張しない。

情報順序では `T`（ $j=0 $）が唯一の底、頂は壁  $\pm 1 $、すなわち `F` と最深 `B` です。内部の `B` は最深 `B` より情報的に真に小さいです（`info_interiorB_lt_deepB`）。ラベル対応が違うので Belnap FOUR 同型は主張しません。

実数上の  $\min/\max $ は分配的です。非分配性は同じ論理の双対 Hilbert 層、 $\mathbb{C}^2 $ の部分空間格子にあります。

---

## 9. 示すこと・示さないこと

**示すのは次です。**

- 許容ねじれ配置を命題の担体とし、 $J_{\mathrm{norm}} $ を観測量とすること
-  $[-1,1] $ を四つの名前付き状態へ分割し、許容錐上で両壁が達成されること
- 否定を幾何的にすること（通常–双対スワップ）
-  $p\wedge\neg p $ を  $\lvert F\rangle $ の外に保つこと
- 二つの指定述語（`HoldsT`、`HoldsNotF`）と二つの二値フラグメント（名前と壁）の区別
-  $P=\neg P $ を  $\lvert T\rangle $ に一意に置くこと、 $\{P,\neg P\} $ が爆発しないこと、 $J_{\mathrm{norm}}<1 $ が三ラベルで実現されること
-  $\mathbb{C}^2 $ の部分空間格子のオーソモジュラー性と非分配性、四ラベルが PVM でないこと
- Killing 対が不定であること、自己重なりが Born 確率でないこと

**示さないのは次です。**

- 量子論理への連続的接近（解釈以上の主張）
- ゲーデル文が古典算術で偽であること、ヒルベルト計画の完了
- 無条件の FLT / Beal / abc
- 振幅層の演算と双対 Hilbert 層の演算の同一視、および  $J $ からの Born 則
-  $R(p)R(q) $ が常にねじれローターへ戻ること
- 生の  $J $ を  $[-1,1] $ の値と同一視すること
- Belnap FOUR 同型
- Dirac スピノル  $\mathbb{C}^4 $、位置・運動量演算子、測定問題の解決

含意結合子とディオファントスのレジーム分類（例5）は後続です。

---

## 10. Lean 辞書

対象は `DstDiophantine/Logic/` です。数論三層（加法忠実化 / no-go / bridge）には依存させず、`lake build DstDiophantine.Logic` で回帰します。幾何代数との接続は新しい代数を足すことではありません。すでに証明済みの PGA 双ベクトル `omegaTorsion` の Killing 二次形式が、正規化を経て四状態になる、という読みです。

### 区間  $[-1,1] $ は  $J_{\mathrm{norm}} $

| 量 | 定義 | 許容錐上の範囲 | Lean |
|----|------|----------------|------|
| 生の  $J $ |  $\tfrac12\sum(\alpha^2-\beta^2) $ |  $\lvert J\rvert\le 3\pi^2/8 $ | `J`、`torsion_bound_raw_continuous_pi_sq` |
|  $J_{\mathrm{norm}} $ |  $\frac{8}{3\pi^2}J $ |  $\lvert J_{\mathrm{norm}}\rvert\le 1 $、像はちょうど  $[-1,1] $ | `JNormalized`、`torsion_bound_continuous`、`exists_admissible_JNormalized` |
|  $\frac1{16}B(\Omega,\Omega) $ | 生成子展開では  $\tfrac18\sum(\alpha^2-\beta^2) $ |  $J $ の  $1/4 $ | `one_sixteenth_omegaKilling_eq`、`paper_appendix_killing_coeff_false` |

四状態の分類は `classifyOfMem` / `ofParams` です。許容配置では常に定義でき、四状態はすべて inhabited です（`exists_ofParams`）。

### モジュール

| 内容 | 場所 |
|------|------|
| 振幅 | `Logic/Amplitude.lean` |
| 四状態 | `Logic/TruthValue.lean` |
| 結合子 | `Logic/Connective.lean` |
| 通常–双対スワップ | `Logic/Interpretation.lean` |
| 二つの順序 | `Logic/Order.lean` |
| Killing・干渉 | `Logic/Geometric.lean` |
| 構文 | `Logic/Formula.lean` |
| 指定値・フラグメント | `Logic/Valuation.lean` |
| 帰結 | `Logic/Consequence.lean` |
| 例1 否定固定点 | `Logic/Example/FixedPoint.lean` |
| 例2 非爆発 | `Logic/Example/Explosion.lean` |
| 例3  $J_{\mathrm{norm}}<1 $ | `Logic/Example/NotFalse.lean` |
| 例4 相補性 | `Logic/Quantum/QuantumLogic.lean`、`Dictionary.lean` |
| 層の分離 | `Logic/Quantum/Separation.lean` |

回帰 example は `DstDiophantine/Logic.lean` にあります。

---

## 11. まとめ

D4L は、許容配置を命題とする一つの論理です。機械検証できている核は次です。

- 真理値の担い手は  $J_{\mathrm{norm}} $（生の  $J $ ではない）
- 合接・選言・符号反転は実数上の  $\min/\max/- $ で、爆発しない
- 壁フラグメントは古典の核、名前フラグメントはブールではない
- 二値が担えない四つの問題——否定固定点、非爆発、 $J_{\mathrm{norm}}<1 $、相補性——を、空性と実現の対として固定した
- Killing 重なりは対称、異軸のねじれ双ベクトルは一般に非可換

いま四値が二値より多く担っているのは、§4–§7 の四つの問題です。

---

*この文書は Dual Spacetime Theory（二重時空理論）と D4L の議論に基づき、`DstDiophantine.Logic` の機械検証で改訂しています。*
