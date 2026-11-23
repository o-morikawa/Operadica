# Operadica 設計文書

最終更新: 2026-11-23(v0.23.0)

## 1. 目的

operad の標準的な理論を、Mathematica 上で実際に計算しながら理解し、使えるようにする。
最初の非自明な到達点を May の recognition theorem に置く。

「証明する」のではなく、**定理の主張と証明の部品をすべて実行可能にする**ことを目標にする。
一般の弱同値の主張そのものは Mathematica の外(人間の証明、必要なら Lean)に残る。

第二の方向として、operad に基づいて、格子 cochain の上でゲージ理論を構成的に作る指針を探る。

- 格子作用を、cochain の演算(δ、∪、∪ᵢ)と、E∞ operad が与えるその間のホモトピーの組み合わせとして書く。
- 可換なゲージ場は Villain 形式(実数の接続と整数の flux の組)で扱い、作用を Deligne–Beilinson 積から組み立てる。
- ゲージ変分と離散的な不変性(Pontryagin 平方、Chern–Simons 型)を記号的に検査し、補正項がどこから来るかを operad の側から説明する。
- 作用を K(A, n) の cocycle として読み、圏の側の量(associator、braiding、spin)と照合する。

これは Wilson 流の格子ゲージ理論の代わりではない。非可換ゲージ場の力学は cochain に乗らない。
届くのは、可換な場、高次形式対称性の背景場、アノマリー、θ 項などの位相的な部分である。

現状は途中経過で、既知の構成の再現までである。どこまで構成的に作れるかを探っている。

## 2. 設計思想

### 2.1 cochain を第一級の対象にする

格子 cochain と、Steenrod の高次 cup 積(立方格子では Chen–Tata の公式)を、
応用として後から載せるのではなく、最初の「代数」の例として入れる。
発展的な格子ゲージ理論の定式化(高次形式対称性、アノマリー、Pontryagin 平方)で
実際に使う演算が、そのまま operad の具体例になるようにする。

### 2.2 四つの層と利用上の分離

層ごとに文脈(context)を分け、単独でロードできるようにする。依存は一方向。

| 層 | 文脈 | 依存 | 内容 |
|---|---|---|---|
| operad | ``Operadica`Trees` `` | なし | 木、接ぎ木、列挙 |
| operad | ``Operadica`Operads` `` | Trees | operad オブジェクト、公理と同変性の検証器、代数 |
| operad | ``Operadica`Rewriting` `` | Trees | 書き換えによる商、正規形、合流性 |
| operad | ``Operadica`LittleCubes` `` | なし | little n-cubes operad(Eₙ)、配置の空間の脈体と Betti 数 |
| operad | ``Operadica`Loops` `` | LittleCubes | little cubes の n 重ループ空間への作用、近似写像 CₙX → ΩⁿΣⁿX、配置の道の braid |
| operad | ``Operadica`Graded` `` | Trees | 線形結合、Koszul 符号つきの次数付き operad、微分、鎖複体の整係数ホモロジー |
| operad | ``Operadica`AInfinity` `` | Trees, Graded, Rewriting | A∞ operad、associahedron |
| operad | ``Operadica`Presented` `` | Graded | 生成元と関係式による対称 operad:Com、Lie、Ass、Poisson、Gerstenhaber、Pₙ |
| operad | ``Operadica`BarrattEccles` `` | Graded | Barratt–Eccles operad(E∞)、Eₙ の段、区間と立方体への作用、無順序の配置と braid 群のホモロジー |
| operad | ``Operadica`BarConstruction` `` | Graded | delooping:アーベル群の反復 bar 構成、Eilenberg–MacLane 空間 K(A, n) |
| カテゴリ | ``Operadica`EnCategories` `` | なし | 点付き Eₙ モノイダル圏:五角形、六角形、spin |
| 格子ゲージ理論 | ``Operadica`Lattice` `` | なし | cochain、δ、∪、∪ᵢ、局所的な多重線形演算 |
| 格子ゲージ理論 | ``Operadica`Gauge` `` | Lattice | 多重線形展開、ゲージ変分、作用 |
| 格子ゲージ理論 | ``Operadica`Simplicial` `` | Lattice | 同じ cochain の式を単体の上で評価する:Steenrod の ∪ᵢ |
| 格子ゲージ理論 | ``Operadica`Villain` `` | Lattice | modified Villain 形式の U(1) ゲージ場、differential cochain、Deligne–Beilinson 積、BF・Chern–Simons の作用、θ 項、奇数 level の障害 |
| 橋 | ``Operadica`EInfinity` `` | Graded, BarrattEccles, Lattice | 格子 cochain への E∞ operad の作用:∪ᵢ とその間のホモトピー |
| 橋 | ``Operadica`Bridge` `` | Trees, Operads, LittleCubes, Loops, Graded, Presented, BarrattEccles, BarConstruction, Lattice, Simplicial, Villain, EnCategories | 層をつなぐ主張 |

- 格子ゲージ理論の計算をしたい人は ``Operadica`Gauge` `` だけをロードすればよく、operad を知る必要はない。
- カテゴリ層と格子層は operad 層に依存しない。三者が同じものであることは橋で初めて述べる。
- ``Needs["Operadica`"]`` は全部をロードする。

### 2.3 物理学者にとって読めること

- 値は格子の添字記法で出る。`f[x, {mu, nu}]` は点 `x`、`(mu, nu)` 面のプラケット上の値。
- cochain の式(`Cup[a, Coboundary[b]]` など)は cell 上で評価するまで記号のまま残る。
  論文の式と見比べられ、`a -> a + Coboundary[lam]` のような置換がそのまま効く。
- 位相は 1 を法とする有理数で持つ(`x` は `exp(2πi x)`)。五角形・六角形の検査は厳密。
- 符号規約は文献の式に合わせ、どの式に合わせたかをコードとテストに書く。

## 3. 表現

### 3.1 木と operad

木は `OpLeaf` か、不活性な頭部 `h` を持つ式 `h[t1, ..., tk]`。
Mathematica の式がそのまま平面根付き木であり、部分合成 ∘ᵢ は i 番目の葉への挿入である。

operad は次のキーを持つ Association。すべての operad がこの一つのインターフェースを持ち、
同じ検証器(`OperadAxiomCheck`、`OperadEquivarianceCheck`)を通る。

| キー | 意味 |
|---|---|
| `"Elements"` | arity n ↦ その arity の元のリスト |
| `"Compose"` | `{x, i, y}` ↦ x ∘ᵢ y |
| `"Unit"` | 恒等演算 |
| `"Equal"` | 等しさの判定(省略時は `SameQ`) |
| `"Action"` | `{x, s}` ↦ x·s。対称群の右作用(対称 operad のとき) |

対称群の規約(`reference/operad_reference.py` で確認):
置換 s はリスト `{s(1), ..., s(n)}`。作用は右作用で `(x·s)·t = x·(st)`、`(st)(j) = s(t(j))`。
関数に対しては `(f·s)(x₁..xₙ) = f(x_{s⁻¹(1)}, ..)`。
同変性は `(a·s) ∘ᵢ (b·t) = (a ∘_{s(i)} b)·(s ∘ᵢ t)`、`s ∘ᵢ t = PermutationCompose[s, i, t]`。

### 3.2 little cubes

配置は立方体のリスト、立方体は区間 `{a, b}` のリスト。合成はアフィン写像による挿入、
対称群はラベルの付け替え `(c·s)_j = c_{s(j)}`。
公理は端点の多項式恒等式なので、端点を記号にした一般の配置で検証する(全配置に対する証明)。

**ループ空間への作用**(``Operadica`Loops` ``、`reference/loops_reference.py` で確認)。
recognition theorem の出発点は「n 重ループ空間は little n-cubes の代数である」ことで、これを実行できる形にする。
ΩⁿY の点は、単位 n-立方体から Y への写像で境界を基点に送るもの(ここでは点 t に適用できて、境界で `LoopBase` を返すもの)。
k 個の立方体の配置 c は

`θ(c; g₁, …, g_k)(t) = gᵢ(cᵢ⁻¹(t))`(t が i 番目の立方体の内部にあるとき。それ以外は基点)

で作用する(`LoopAction[c][g1, …, gk]`)。`GenericLoop[name]` は内部の点 t で `name[t]` を返す一般のループ。

- 代数の公理(単位、合成 `θ(c∘ᵢd; …) = θ(c; …, θ(d; …), …)`、同変性)は点ごとの等式である。両辺は端点の作る格子の上で
  区分的にアフィンなので、格子の各 cell の n+1 個の点で比べれば、その配置については格子の外のすべての点での証明になる
  (`LoopSamplePoints`、`LoopEqualQ`)。配置は有理数の端点を持つ具体的なものを使う(検証の強さは「与えた配置について」)。
- n = 1 では `{[0, 1/2], [1/2, 1]}` がループの合成。3 つのループの 2 通りの合成は、3 つの区間の異なる配置
  (したがって異なる写像)で、配置を直線でつなぐ道が operad の中にある:結合則はホモトピーを除いて成り立つ。
- n ≥ 2 では、2 つの立方体が互いのまわりを回る道 `SwapPath[n][s]` があり、s = 1 で 2 つが入れ替わる:
  積はホモトピーを除いて可換(Eckmann–Hilton)。s = 2 まで行くと元に戻り、これが二重 braiding にあたる
  (n = 2 では C₂(2) ≃ S¹ の生成元、n ≥ 3 では可縮)。
- **配置の道の braid**(`reference/braiding_reference.py` で確認):n ≥ 2 の配置の道を最初の 2 方向で読む。
  立方体を中心の (x, y) の辞書式順序で左から並べる(`ConfigurationOrder`)。隣り合う 2 つが 2 つの標本点の間で
  入れ替わったとき、相対位置 r(右の中心 − 左の中心)が反時計回りに回っていれば生成元 σᵢ(左から来た立方体が下を通る)、
  時計回りなら σᵢ⁻¹ とする(前後の r の外積 `r₀ × r₁` の符号)。`PathBraid[path, {s0, s1}, steps]` は braid を
  整数のリストで返す(i が σᵢ、−i がその逆)。`ExchangeCount` は指数和で、立方体 2 個なら反時計回りの半回転の数。
  - 標本の間で相対位置が半回転したり、隣り合わない立方体が入れ替わったり、2 つの中心が平面で重なったりすると
    `$Failed` を返す(steps を増やす)。`SwapPath[2]` の半分は `{1}`、全部は `{1, 1}`、逆向きは `{−1}`。1 歩では読めない。
  - operad の合成で作った道、つまり `SwapPath[2]` の 2 つの正方形に正方形の列を入れた道は、block の braid になる。
    1 個と 2 個で `{1, 2}`、2 個と 1 個で `{2, 1}`、2 個と 2 個で `{2, 1, 3, 2}`。
  - 参照実装では、乱歩で作った道について、指数和が独立に数えた半回転の数(3 個のときは巻き数の和の 2 倍)に一致すること、
    標本を細かくしても braid が変わらないこと(Burau 表現で比較)を確かめている。
- **3 次元では braid は不変量でない**:`SwapHomotopy[u][s]` は、little 3-cubes 2 個の配置の空間の中で、
  反時計回りの半回転(u = 0)を時計回りの半回転(u = 1)に、端点を動かさずにつなぐ。半回転の面を第 1 方向の
  まわりに回すだけである。途中(u = 1/2)では 2 つの中心が平面への射影で重なり、braid は読めない。
- **近似写像**:単位 `η(x)(t) = [t, x]`(`SuspensionUnit`)から `α(c; x₁, …, x_k) = θ(c; η(x₁), …, η(x_k))` が
  May の写像 CₙX → ΩⁿΣⁿX である(`ApproximationMap`)。α は代数の射で、合成した配置の像は、像への作用に等しい。
  ホモロジーでの帰結(自由 Pₙ-代数との一致)は 6 節の近似定理の小節。

### 3.3 次数付き operad と A∞

線形結合は `LBasis[x]` のスカラー倍の和で表す。自由な次数付き operad では、木の単項式を
頂点のラベルの**前順**(式として書いたときに頭部が現れる順)でのテンソル積とみなす。
部分合成は Koszul 符号を持つ:

- `s ∘ᵢ t = (−1)^(|t|·D) (接ぎ木)`。D は s の頂点のうち葉 i より後にあるものの次数の和。
- 公理は、逐次 `(a∘ᵢb)∘_(i+j−1)c = a∘ᵢ(b∘ⱼc)`、並列 `(a∘ᵢb)∘_(k+m−1)c = (−1)^(|b||c|)(a∘ₖc)∘ᵢb`。
- 次数 −1 の導分 d は生成元での値で決まる。

A∞ operad は生成元 `OpM[n]`(arity n、次数 n−2)と

`d mₙ = Σ_{p+q=n+1} Σ_{i=1}^{p} (−1)^(i+q(p−i)) m_p ∘ᵢ m_q`

で与える(Loday–Vallette の符号)。`d² = 0` が Stasheff の関係式である。
arity n の部分は associahedron Kₙ の胞体鎖複体で、ホモロジーは次数 0 に 1 次元だけ残る
(A∞ は As の分解)。`DGOperadCheck`、`StasheffRelationsQ`、`AssociahedronBetti`。

有限な鎖複体のホモロジーは、有理数係数の Betti 数(`ChainBetti`)と、整数係数の群(`ChainHomology`)の
両方を計算できる。後者は微分の行列の Smith 標準形(`SmithInvariants`)から求め、群を巡回群の直和として返す
(0 は Z、t は Z_t。`{0, 2}` は Z + Z₂、`{}` は 0)。ねじれ(torsion)が見えるのは整数係数だけである。
`IntegerKernel` は整数行列の核の、整数の上での基底を返す(cycle の基底。`NullSpace` は有理数の上の基底しか返さない)。
`ModularBetti[groups, p]` は、整数係数のホモロジー群から Z_p 係数の Betti 数を普遍係数定理で求める
(Z は 1 回、p で割れる位数の巡回群はその次数と次の次数で 1 回ずつ数える)。

### 3.4 生成元と関係式による対称 operad

二項の生成元と二次の関係式で与えた対称 operad を、線形代数で計算する(``Operadica`Presented` ``)。

- ラベル付きの木:葉は入力の番号。`OpLie[OpLie[1, 2], 3]` は `[[x₁, x₂], x₃]`。
- 生成元は対称性 `g[x, y] = ±g'[y, x]` と次数を持つ。木は 3.3 と同じく頂点の前順でのテンソル積で、
  規則は三つ(`reference/presented_reference.py` で確認):
  - 入れ替え `g[a, b] = (g の符号)·(−1)^(|a||b|) g'[b, a]`
  - 接ぎ木 `t ∘ₖ x = (−1)^(|x|·D) (葉 k に x)`。D は t の頂点のうち葉 k より後にあるものの次数の和
  - 作用 `t·s` は葉のラベル j を s⁻¹(j) に付け替える(3.1 の規約)
- **shuffle 木**(各頂点で、左の子の最小の葉 < 右の子の最小の葉)が自由対称 operad の基底になる。
- arity n のイデアルは「関係式の 3 つの入力に shuffle 木を入れ、それをさらに shuffle 木に入れたもの」で
  張られる。行簡約で、商の次元(`OperadDimension`)、正規形の基底(`OperadBasis`)、
  正規形への簡約(`OperadReduce`)、恒等式の判定(`OperadZeroQ`)が得られる。
- 標準例と正規形:

  | operad | 関数 | 正規形 |
  |---|---|---|
  | Com | `PresentedCommutativeOperad[]` | 左に寄せた積 |
  | Lie | `LieOperad[]` | 左ノルムの括弧 `[[[1, a], b], …]`((n−1)! 個) |
  | Ass | `PresentedAssociativeOperad[]` | 語(n! 個)。`OpAssWord` で語に直す |
  | Pₙ | `PoissonOperad[n]` | 左ノルムの括弧の積(n! 個) |

- `PoissonOperad[n]` は可換な積 `OpCom`(次数 0)と括弧 `OpLie`(次数 n−1、入れ替えの符号 (−1)ⁿ)を持つ。
  n = 1 が Poisson operad、n = 2 が Gerstenhaber operad で、n ≥ 2 では Pₙ = H_*(Eₙ)。
  関係式は n によらず同じ形に書ける:

  - 結合則 `(12)3 = 1(23)`
  - Jacobi `[[1,2],3] + [[2,3],1] + [[3,1],2] = 0`
  - Leibniz `[12, 3] = 1[2,3] + [1,3]2`

  n による違いは Koszul 符号だけから出る。たとえば `[1,[2,3]]` の正規形は、Lie と P₃ で
  `[[1,2],3] − [[1,3],2]`、Gerstenhaber で `−[[1,2],3] − [[1,3],2]`。
  符号を落として同じ関係式を課すと別の operad になる(次元が 1, 2, 6, 20。正しくは 1, 2, 6, 24)。
- arity k の成分の次数ごとの次元は `(1+t)(1+2t)…(1+(k−1)t)` の係数(t の次数は n−1)で、
  ℝⁿ の k 点の配置空間の Betti 数である。`OperadDimensionsByDegree`。
- 商が operad であること(単位、逐次、並列。並列は符号 `(−1)^(|b||c|)` つき)は、3.3 の
  `DGOperadCheck` がそのまま検査する。
- 射は生成元の行き先で与える(`OperadMorphismQ`)。交換子 `xy − yx` が Lie → Ass を与えること、
  反交換子(Jordan 積)は可換だが結合的でないこと、など。
- Koszul 双対の対の母関数の関係 `f_P(−f_Q(−x)) = x` は `KoszulSeriesQ`(Com と Lie、Ass と Ass)。
- **指標**:`OperadCharacter[op, k]` は、対称群 S_k の op(k) への作用の指標を、巡回型(k の分割)ごと、次数ごとに返す。
  Com(k) は自明表現、Ass(k) は正則表現、Lie(3) は (2, 0, −1)。Poisson operad は正則表現で、次数ごとに分けると分かれる。
- **自由代数**:次数付きベクトル空間 V の上の自由 P-代数の arity k の部分は `P(k) ⊗_(S_k) V^(⊗k)` で、その次元は

  `(1/k!) Σ_σ tr(σ | P(k)) · tr(σ | V^(⊗k))`

  長さ l の巡回置換の V^(⊗l) の上の跡は、V の基底 e にわたる `(−1)^(|e|(l−1)) t^(l|e|)` の和(Koszul 符号)。
  `FreeAlgebraDimensions[op, degrees, kmax]`。Com で対称・外積冪、Ass でテンソル冪、Lie で自由次数付き Lie 代数
  (偶の生成元 2 個で 2, 1, 2, 3、奇の生成元 2 個で 2, 3, 2, 3)。`reference/approximation_reference.py` で確認。

### 3.5 Barratt–Eccles operad(E∞)と Eₙ の段

E∞ operad の、計算できる具体的なモデル(``Operadica`BarrattEccles` ``)。`reference/einfinity_reference.py` で確認。

- arity r、次数 d の元は語の列 `{w0, …, wd}`。語は 1..r の置換を並びとして書いたもので、隣り合う語は異なる。
  次数 0 は語の operad(3.1 の `WordOperad`、結合 operad)そのものである。
- 微分は `d{w0..wd} = Σᵢ (−1)ⁱ {w0, …, wi を除く, …, wd}`。対称群は文字の付け替え `(w·s)ₖ = s⁻¹(wₖ)`。
- 合成は、二つの列の shuffle(格子路)にわたる和で、路の各点では語の代入。符号は shuffle の符号。
  `DGOperadCheck` が単位・逐次・並列(Koszul 符号つき)・d² = 0・Leibniz 則を検査する。
- E(r) のホモロジーは次数 0 に 1 次元だけ(Com の分解)。r = 2, 3 の低い次数で確認している。
- **Eₙ の段**(Berger):文字の対の相対順序が列に沿って変わる回数が、どの対でも n 未満である元が F_nE をなす。
  F₁E は結合 operad、F_nE は Eₙ operad。`BarrattEcclesLevel`、`BarrattEcclesFiltration`、`BarrattEcclesBetti`。
  F_nE(k) の Betti 数は Pₙ(k) の次数ごとの次元に一致する:F₂E(3) で 1, 3, 2、F₃E(3) で 1, 0, 3, 0, 2。
  参照実装では F₂E(4) の 1, 6, 11, 6 と F₄E(3) も確認した。
- arity 2 の元 `eᵢ = {{1,2},{2,1},{1,2},…}`(`HigherCupElement[i]`)は F_(i+1) にある。
- table reduction(Berger–Fresse)は surjection の複体への鎖写像で、`eᵢ ↦ (1,2,1,2,…)`。
  `TableReduction`、`SurjectionDifferential`。
- **区間への作用**:区間の鎖複体 N(v₀, v₁, e)に対し、次数 m の元 s の作用 `s·e ∈ N^(⊗r)` を table reduction で与える。
  語を行に切り(行の最後の文字は後でもう一度現れる)、最後の行の位置 k を選ぶ。k より前の文字は v₀、
  後の文字は v₁、k の文字と各行の最後の文字は e を受け取る。符号は(行末の文字の列, k の文字)の置換の符号。
  `IntervalCoaction`。
- **立方体への作用**:n 次元立方体は区間の n 個のテンソル積。`0 = i₀ ≤ … ≤ iₙ = d` にわたって、
  `{w_(i_(m−1)), …, w_(i_m)}` を m 番目の辺に作用させて掛け合わせる(Koszul 符号つき)。`CubeCoaction`。
  項は `{係数, {row₁, …, row_r}}` で、rowⱼ は方向ごとに 2(j 番目の因子がその方向に伸びる)、
  1(上端にいる)、0(下端にいる)を持つ。

**無順序の配置**(`reference/braidgroup_reference.py` で確認)。対称群 S_k の F_nE(k) への作用は自由なので、
余不変(軌道)の複体は、k 個の無順序の little n-cubes の空間 C_n(k)/S_k のホモロジーを計算する。
これは「1 点の上の自由 Eₙ-代数」の arity k の部分である。軌道の代表は最初の語が恒等置換である元で取る
(`BarrattEcclesOrbits`、`BarrattEcclesOrbitHomology`)。

- k = 2 では n−1 次元の実射影空間のホモロジー(n = 2 で S¹、n = 3 で Z, Z₂, 0、n = 4 で Z, Z₂, 0, Z)。
- n = 2 では C₂(k)/S_k は braid 群 Br_k の分類空間で、ホモロジーは braid 群のホモロジーである。
- operad 全体(n = ∞)では対称群のホモロジー。次数を打ち切って低い次数を計算する。H₁(S_k) = Z₂。
- **Fuks–Vainshtein の複体**:n = 2 にはずっと小さい複体がある。cell は k の composition `(n₁, …, n_s)`
  (点が s 本の縦線の上に n₁, …, n_s 個ずつ載っている配置)で次数は k − s、余境界は隣り合う 2 本の線を合わせる:

  `δ(n₁, …, n_s) = Σⱼ (−1)^(j−1) [nⱼ + nⱼ₊₁ ; nⱼ] (…, nⱼ + nⱼ₊₁, …)`

  係数は q = −1 での Gauss 二項係数で、a, b がともに奇数なら 0、それ以外は `Binomial[⌊(a+b)/2⌋, ⌊a/2⌋]`。
  `BraidGroupCohomology[k]`、`BraidGroupHomology[k]`(双対の複体)。cell は 2^(k−1) 個しかない。
- 結果(k ≤ 8):H₀ = H₁ = Z、それより上はねじれだけ。Br₄ で Z, Z, Z₂, 0。Br₆ で Z, Z, Z₂, Z₂, Z₃, 0。
  Br₈ で Z, Z, Z₂, Z₂, Z₆, Z₃, Z₂, 0。F₂E(k) の軌道の複体による計算(k = 3。参照実装で k = 4)と一致する。

### 3.6 反復 bar 構成と Eilenberg–MacLane 空間

delooping の、計算できる具体的なモデル(``Operadica`BarConstruction` ``)。`reference/bar_reference.py` で確認。

有限アーベル群 A = Z_N1 × … × Z_Nr の群環 Z[A] の n 重 bar 構成 Bⁿ は鎖複体で、そのホモロジーは
Eilenberg–MacLane 空間 K(A, n) = BⁿA(ホモトピー群が次数 n の A だけである空間)の整数係数ホモロジーである。

- 生成元:レベル 0 は A の 0 でない元(整数のリスト、次数 0)。レベル n は、レベル n−1 の生成元を文字とする
  語 `BarWord[x1, …, xm]`(m ≥ 1)で、`[x1|…|xm]` と書く。次数は `Σ(deg xᵢ + 1)`。
  `[a‖b]` は `[[a]|[b]]`(B² の次数 4 の元)、`[a|||b]` は `[[[a]]|[[b]]]`(B³ の次数 6 の元)。
- 積:レベル 0 は群の和(0 になる項は落とす。正規化した複体)。レベル n は shuffle 積で、
  文字の次数を deg + 1 として Koszul 符号をつける。結合的で、次数付き可換。`BarProduct`。
- 微分:`d[x1|…|xm] = −Σᵢ (−1)^(e_(i−1)) […|d xᵢ|…] + Σᵢ (−1)^(eᵢ) […|xᵢ·x_(i+1)|…]`、`eᵢ = Σ_(j≤i)(deg xⱼ + 1)`。
  レベル 1 では両端の項 `[x2|…|xm] + (−1)^m [x1|…|x_(m−1)]` が加わる。
  レベル 1 は群ホモロジーの複体で、`d[a|b] = [b] − [a+b] + [a]`。`BarDifferential`。
- d は積の導分である。可換な dg 代数の bar 構成はまた可換な dg 代数になるので、bar 構成を繰り返せる。
  群が可換であることはここで使う(非可換な群は 1 回しか deloop できない)。
- 懸垂 `x ↦ [x]`(`BarSuspension`)はレベルと次数を 1 上げ、`d[x] = −[dx]`。
- `BarHomology[orders, n, k]` は H_k(K(A, n)) を巡回群の直和として返す(`{4}` は Z₄、`{2, 4, 4}` は Z₂ + Z₄ + Z₄)。

  | | H_n | H_(n+1) | H_(n+2) |
  |---|---|---|---|
  | K(Z_N, 1) | Z_N | 0 | Z_N |
  | K(Z_N, 2) | Z_N | 0 | Z_(N·gcd(2,N)) |
  | K(Z_N, n)、n ≥ 3 | Z_N | 0 | Z_gcd(2,N) |

  N = 2, 3, 4 と n ≤ 4 で確認している(参照実装では n ≤ 3 で N ≤ 6)。Z₂ × Z₂ では H₄(K(A, 2)) = Z₂ + Z₄ + Z₄。

**単体的集合としての K(A, n)**:k-単体は、頂点 0, …, k の単体の上の A 値 n-cocycle、つまり
単体の上の平坦な n-form ゲージ場である(`EMSimplex[k, values]`。values は n 次元の面の上の値)。
面写像は場の制限、退化写像は辺をつぶす写像による引き戻しで、三角形分割された空間の上の
平坦な n-form ゲージ場は、K(A, n) への単体写像と同じものである。

- `EilenbergMacLaneHomotopy`:Moore 複体から計算したホモトピー群の位数。次数 n で |A|、ほかは 1。
- `EilenbergMacLaneHomology`:退化していない単体の鎖複体のホモロジー。bar 構成のホモロジーと一致する。
  K(Z₂, 2) は次元 4 と 5 に退化していない単体を 41 個と 768 個持ち、H₄ = Z₄。
- `EilenbergMacLaneCycles`:cycle の、整数の上での基底。
- **ループ空間の側**(有理係数):球面の楔 X = ∨S^(dᵢ)(dᵢ ≥ 1)に対し、ΩΣⁿX の有理ホモトピーは次数 dᵢ+n−1 の
  生成元の上の自由次数付き Lie 代数(Hilton–Milnor)で、ΩⁿΣⁿX の有理ホモロジーは、それを n−1 だけ下げたものの上の
  自由次数付き可換代数である(Milnor–Moore)。`FreeLieDimensions`(PBW から)、`LoopSuspensionDimensions`。
  Ω²S⁴ は次数 2 の多項式類と次数 5 の外積類、Ω³S⁴ は次数 1 の外積類と次数 4 の多項式類。
- **ループ空間の側**(Z₂ 係数、n = 2):次数 d ≥ 1 の球面 S^d に対し、Ω²S^(d+2) の Z₂ 係数ホモロジーは
  x, Qx, QQx, … の上の多項式代数である(Kudo–Araki)。x は重み 1・次数 d、作用素 Q は重みを 2 倍にし、次数 m を 2m+1 にする。
  `KudoArakiDimensions[d, kmax]`。Ω²S³ の生成元は次数 1, 3, 7, …。
- K(A, n) の k-単体の上の、1 を法とする値を持つ関数 w が cocycle であること(退化した単体の上で 0、
  (k+1)-単体の面にわたる交代和が 0)を `CharacteristicCocycleQ` が検査する。そのような w は、
  平坦な n-form ゲージ場の、k 次元での位相的作用である。`CharacteristicClassOrder` は、その類の
  H^k(K(A, n); U(1)) での位数を、cycle の基底の上の値から求める。

### 3.7 点付き Eₙ モノイダル圏

単純対象は有限アーベル群の元(整数のリスト)。データは associator `w[a, b, c]` と
braiding `c[a, b]`。通常の圏では E₁ = モノイダル、E₂ = braided、E₃ 以上 = symmetric。

規約は Eilenberg–MacLane のアーベル 3-コサイクル(Joyal–Street の形):

- 五角形 `w(b,c,d) − w(a+b,c,d) + w(a,b+c,d) − w(a,b,c+d) + w(a,b,c) = 0`
- 六角形1 `w(b,c,a) + c(a,b+c) + w(a,b,c) = c(a,c) + w(b,a,c) + c(a,b)`
- 六角形2 `−w(c,a,b) + c(a+b,c) − w(a,b,c) = c(a,c) − w(a,c,b) + c(b,c)`
- ゲージ変換 `w' = w + δf`、`c'(a,b) = c(a,b) + f(b,a) − f(a,b)`
- 不変量:spin `q(a) = c(a,a)`、相互 braiding `b(a,b) = c(a,b) + c(b,a)`
- `MugerCenter` は相互 braiding がすべて自明な対象のリスト(braiding のデータだけから計算する)。
  `ModularQ` は「braided な圏であって(五角形と六角形が成り立ち)、Müger 中心が単位対象だけ」のとき True。
  公理を満たさないデータでも相互 braiding は非退化になりうる(`ZNAnyons[5, 3]` は五角形を満たさない)ので、
  公理の検査を含めている。

braid 群の作用:右に寄せた積 `a₁(a₂(a₃…))` の上で、生成元 σᵢ の位相は
`−w(a,b,x) + c(a,b) + w(b,a,x)`(x は後ろに続く対象の積。最後の 2 つでは `c(a,b)` だけ)。
σᵢ を 2 回かけると相互 braiding になる。点付きの圏では braid 関係式は五角形から従い、
六角形は「積を越える braiding は braiding の合成である」という主張にあたる。`BraidPhase`、`BraidRelationQ`。
`BraidPathPhase[cat, word, braid]` は braid(整数のリスト。−i は σᵢ の逆)の位相で、word の右寄せの積から、
並べ替えた word の右寄せの積への位相である。ゲージ変換では、位相は道の両端だけで決まる量だけ変わる。
したがって pure braid(word が元に戻る braid)の位相は不変で、a と b の 1 回の入れ替えは `f(b, a) − f(a, b)` だけ変わる。

標準例:`ZNAnyons[n, p]`(`w = p·a·carry(b,c)/2`、`c = p·a·b/(2n)`。n が偶数か p が偶数のとき成立)、
`VecZN[n, k]`(H³(Z_n, U(1)) の代表)、`DoubleZN[n]`、`ToricCode[]`、`Semion[]`、`SuperVec[]`。

**U(1) Chern–Simons 理論の線**(`ChernSimonsAnyons[k]`。`reference/encategory_reference.py` で確認):level k では電荷 j の線の spin が `j²/2k` である。

- k が偶数なら Z_k の上の `ZNAnyons[k, 1]` で、modular。
- k が奇数なら `j²/2k` は 2k を法としてしか定まらず、Z_(2k) の上の `ZNAnyons[2k, 2]` になる。Müger 中心は {0, k} で、線 k は spin 1/2 の fermion である。
  modular でないことが、理論が spin 構造に依ることの圏の側の形である。
- **分解**(`ChernSimonsSpinSplitQ`):k が奇数のとき、電荷を `j = 2l + kε`(l は k を法とし、ε = 0, 1)と書くと、spin は `2l²/k + ε/2`、
  相互 braiding は `4ll′/k` になる。つまり `U(1)_k = ZNAnyons[k, 4] ⊠ SuperVec` で、`ZNAnyons[k, 4]` は modular。
  点付きの braided な圏は spin(二次形式)で決まるので、比べているのは spin と相互 braiding である。
- **fermion condensation**(`ChernSimonsFermionCondensationQ`):同じ圏は、level 4k の理論 `ZNAnyons[4k, 1]`(偶数 level。格子の作用がある)の中で、
  fermion である線 2k と相互 braiding が自明な線(電荷が偶数の線)のなす部分でもある。線 2i が level k の線 i にあたる。
  arXiv:2401.09597 が奇数 level を作るのに使う手続きの、圏の側の形である。

圏のデータとしては「bosonic な理論に spin TQFT {1, ψ} を掛けたもの」になっているが、格子の上では直積にはならない:fermion ψ は電荷 k の Wilson line
そのもので、ゲージ場に結びついている。格子の側の障害と、三次元トーラスの上でそれを消す符号は 3.9 節にある。局所的な式(Majorana)はまだない。

### 3.8 cochain

- `Cochain[p, f]`:cell `LCell[x, s]` 上の値が `f[x, s]` の p-cochain。
  `f` が未定義のシンボルなら「一般の cochain」になる。
- `Coboundary[c]`、`Cup[a, b]`(組み込みの `Cup`。`a ⌣ b` と入力できる)、
  `HigherCup[i][a, b]`、和、スカラー倍。
- `CochainValue[c, x, s]` で cell 上の値に展開する。
- `CochainExpand` で多重線形に展開し(δ² = 0 を使う)、`GaugeVariation` でゲージ変分を出し、
  `TotalDerivativeQ` で全微分であることを確かめる。
- **補正項の探索**(`CochainLinearSolve[target, {c1, …, cr}, d]`。`reference/correction_reference.py` で確認):
  `target = x₁c₁ + … + x_r c_r` が cochain の恒等式になる係数を探す。記号的な基点での値を一般の cochain の値の多項式として展開し、
  単項式ごとの係数を比べた線形方程式を解く。解があるか、一意か、解の 1 つを返す。係数は式の中のパラメータ(k、π)に依ってよい。
  - 候補に「原始関数の候補の余境界」と「補正項の候補の変分」を並べると、補正項と全微分を同時に求めることになる。
  - 例:modified Villain の Chern–Simons から ∪₁ の項を除いたラグランジアンのゲージ変分は、
    `δλ∪₁δn`、`δ(λ∪δa)`、`δ(λ∪n)`、`δ(δλ∪₁n)` の結合として一意に `(k/2, k/4π, −k, k/2)` と書ける。
    最初の係数が「補正項は `−(k/2) a∪₁δn`」を意味し、残りが 5 節の全微分である。候補から `δλ∪₁δn` を外すと解がない(補正項なしでは不変にできない)。
  - (A3) そのものも、3 つの ∪₁ の項の一意な結合として出る。符号を取り違えた左辺には解がない。
  - 候補は人が与える。∪ᵢ と E∞ の演算から候補を自動的に並べること、単体の上で解くことはまだない。
- `LocalOperation[f, d][a1, …, ar]`:局所的な多重線形演算。n 次元の cell 上の値は、`f[n]` の項
  `{係数, {row₁, …, row_r}}` についての `係数 × ∏ⱼ aⱼ(x + shiftⱼ; Sⱼ)` の和(row の読み方は 3.5 と同じ)。
  ∪ も ∪ᵢ もこの形で、6 節の E∞ operad の作用はこれで表す。
- **単体の上でも同じ式を評価できる**(``Operadica`Simplicial` ``)。`SimplexValue[c, {v0, …, vn}]` は、
  cochain の式 c を頂点が順序づけられた単体の上で評価する。一般の cochain `Cochain[p, f]` の値は `f[{v0, …, vp}]`。
  `SimplexCochainZeroQ`、`SimplexCochainEqualQ` は恒等式を単体 {0, …, p} の上の 1 回の評価で確かめる
  (頂点に順序のついたすべての単体複体での証明)。規約は 5 節。

### 3.9 Villain 形式の U(1) ゲージ場と Deligne–Beilinson 積

可換なゲージ場を、格子の上の微分コホモロジーとして扱う(``Operadica`Villain` ``、`reference/villain_reference.py` で確認)。
Wilson 流の link 変数ではなく cochain の組を基本の対象にし、作用は cochain の演算で組み立てる。

次数 p の Villain 場は組 `A = (a, n)`(`VillainField[a, n]`):a は実数値の p-cochain(接続)、n は整数値の (p+1)-cochain(flux)。

- 曲率 `F = δa − 2πn`(`VillainCurvature`)
- ゲージ変換 `a → a + δλ`(`VillainGaugeTransform`)
- 大きいゲージ変換 `a → a + 2πm`、`n → n + δm`(m は整数値の p-cochain。`VillainLargeGaugeTransform`)

どちらの変換でも F は変わらない。`δn = 0`(monopole がない)の場を平坦と呼ぶ。作用の中では Lagrange 乗数で課す。

**Deligne–Beilinson 積**(`DeligneProduct`):次数 p の `A = (a, n)` と次数 q の `B = (b, n′)` の積は、次数 p+q+1 の Villain 場

`A ∗ B = ( a∪F_B/2π + (−1)^p n∪b ,  −n∪n′ )`

である。一般の cochain について次が厳密に成り立つ(立方格子と単体の両方。δn、δn′ を含む項は平坦な場で消える):

- 曲率 `F(A∗B) = F_A∪F_B/2π + (−1)^p (δn∪b − a∪δn′)`
- A のゲージ変換 λ:接続が `δ(λ∪F_B/2π) + (−1)^(p−1) λ∪δn′` だけ変わる
- B のゲージ変換 μ:接続が `−δ(n∪μ) + δn∪μ` だけ変わる
- A の大きいゲージ変換 m:接続が `2π(−m∪n′) + (−1)^p δ(m∪b)`、flux が `δ(−m∪n′) + (−1)^p m∪δn′` だけ変わる
- B の大きいゲージ変換 l:接続が `2π(−1)^p n∪l`、flux が `(−1)^p (δ(n∪l) − δn∪l)` だけ変わる

したがって、平坦な場の積はゲージ同値類の上で定まる(積の側でもゲージ変換と大きいゲージ変換になる)。

**作用**:

- BF 理論(相互 Chern–Simons)のラグランジアンは積の接続そのもの:`A ∗ B` の接続は `a∪δb/2π − a∪n′ − n∪b`。
  大きいゲージ変換での変化は 2π × 整数 cochain(と全微分)なので、level は整数でよい。
- Chern–Simons 理論は積の半分に ∪₁ の補正を加えたもの(`VillainChernSimons[k][A, φ]`):

  `(k/2)·(A ∗ A の接続) − (k/2) a∪₁δn + φ∪δn`

  これは arXiv:2303.06160 式 (17) の modified Villain のラグランジアン(``Operadica`Gauge` `` の `ModifiedVillainCS`)と一致する。
  「半分」を取るので大きいゲージ変換での変化は kπ × 整数 cochain になり、そのままでは level k は偶数に限られる(5 節の恒等式。奇数 level は下の小節)。
  ∪₁ の項は、n が平坦でないときにもゲージ不変にするための補正である。

**積の次数付き可換性**(`DeligneSwapGauge`、`DeligneSwapDefect`):連続理論の Deligne–Beilinson 積は次数付き可換で、
`A∗B` と `ε B∗A`(`ε = (−1)^((p+1)(q+1))`)はゲージ変換で移り合う。格子では、`s = (−1)^(p+q)` として、一般の cochain について

- 接続の差 `(A∗B) − ε(B∗A) = δλ + 2πm − s F_A∪₁F_B/2π + (−1)^q (a∪₁δn′ − δn∪₁b)`
- flux の差 `(A∗B) − ε(B∗A) = δm − s (δn∪₁n′ − (−1)^p n∪₁δn′)`
- `λ = ((−1)^p a∪b − (−1)^q F_A∪₁b)/2π − s a∪₁n′`、`m = s n∪₁n′`(`DeligneSwapGauge[A, B]` が `{λ, m}` を返す)

が厳密に成り立つ。λ がゲージ変換、m が大きいゲージ変換である。ホモトピーは ∪₁、つまり ∪ の 2 つの因子を入れ替える
E∞ operad の演算(E₂ の段)で、式は 5 節の (A3) から従う。

- `−s F_A∪₁F_B/2π`(`DeligneSwapDefect`)はゲージ不変な局所項で、ゲージ変換ではない。微分形式の ∧ は厳密に次数付き可換なので、
  連続理論には対応する項がない。cochain の ∪ が可換でないことから出る項で、A か B の曲率が 0 なら消える。
- 例:BF 理論の 2 つの書き方 `a∪δb` と `b∪δa`(p = q = 1、ε = 1)の差は、平坦な flux について `δλ + 2πm − F_A∪₁F_B/2π`。
  作用としては、2π × 整数と、片方の曲率が 0 なら消える項だけ違う。

**θ 項と Witten 効果**(`VillainThetaTerm`、`VillainWittenTerm`):次数 p の場の 2p+2 次元での θ 項は `(θ/8π²) F∪F`
(p = 1 が 4 次元の U(1) ゲージ場)。F だけで書けるので、monopole があっても、ゲージ変換と大きいゲージ変換で厳密に不変である。
一般の cochain について

`(θ/8π²) F∪F = (θ/4π) F(A∗A) + W`、`W = −(−1)^p (θ/4π)(δn∪a − a∪δn)`

が成り立つ(曲率の恒等式で B = A と置いたもの)。`F(A∗A) = δ(A∗A の接続) + 2π n∪n` である。

- monopole がなければ(δn = 0)W = 0 で、`(θ/8π²) F∪F = (θ/2) n∪n + 全微分`。閉じた格子の上の位相電荷は `(1/2) Σ n∪n`。
- 四次元トーラスの上で flux が z(`THooftFluxCochain`)のとき、位相電荷 `(1/8π²) Σ F∪F` は接続 a に依らず
  Pfaffian `z₁₂z₃₄ − z₁₃z₂₄ + z₁₄z₂₃` に等しい。整数なので、トーラスの上で θ の周期は 2π。
- **Witten 効果**:W は接続 a と monopole のカレント δn の結合である。ゲージ変換 `a → a + δλ` で W は
  `−(θ/4π) δ(δn∪λ − (−1)^p λ∪δn)` だけ変わる。大きさ θ/2π の電荷が δn の上にあるときの変化で、
  a の左に置いた δn と右に置いた δn が半分ずつ担う。

**Villain 場は differential cochain である**(`DifferentialCochain`、`VillainDifferentialCochain`):Villain 場は、
Hopkins–Singer の differential cocycle の、微分形式を実 cochain に置き換えたものである。
次数 k の differential cochain は三つ組 `x = (c, h, ω)`:c は整数値の k-cochain、h は実数値の (k−1)-cochain、ω は実数値の k-cochain。

- 余境界 `d(c, h, ω) = (δc, ω − c − δh, δω)`(`DifferentialCoboundary`)。`d² = 0`。
- 積 `x·y = (c₁∪c₂, (−1)^k₁ c₁∪h₂ + h₁∪ω₂, ω₁∪ω₂)`(`DifferentialProduct`)。結合的で、
  Leibniz 則 `d(x·y) = dx·y + (−1)^k₁ x·dy` が成り立つ(どちらも一般の成分について、立方格子と単体で厳密)。

次数 p の Villain 場 `A = (a, n)` は、次数 p+1 の differential cochain `T(A) = (−n, a/2π, F/2π)` である。

| Villain 形式 | differential cochain |
|---|---|
| 曲率の定義 `F = δa − 2πn` | `dT(A)` の中央の成分が 0(`δh = ω − c`) |
| monopole がない(`δn = 0`) | `dT(A) = 0`(cocycle)。一般には `dT(A) = (−δn, 0, −δn)` |
| ゲージ変換 λ、大きいゲージ変換 m | `d(−m, −λ/2π, 0)` を足す |
| Deligne–Beilinson 積 `A∗B` | `T(A)·T(B)`(flux が平坦なら `T(A∗B)` に一致) |

- 整数の場 n は、位相を実数に持ち上げるための補助変数ではなく、differential cocycle の整数部分 c(Chern 類の代表)である。
  modified Villain の拘束 `δn = 0` は cocycle 条件で、n についての和は位相的なセクターの和と 2π 周期性の両方を担う。
- 上に並べた積の恒等式(曲率、ゲージ変換と大きいゲージ変換での変化)は、Leibniz 則 1 本から従う。
  たとえば `(x + dξ)·y = x·y + d(ξ·y) − (−1)^|ξ| ξ·dy`。
- flux が平坦でないとき、`T(A)·T(B)` と `T(A∗B)` は第 3 成分だけが違い、差は `d(T(A)·T(B))` の中央の成分(δn、δn′ を含む項)である。
- 3 つ以上の場の積は結合的なので、括弧の付け方に依らない(flux が平坦なとき。Villain 場としては δn′ などを含む項だけ違う)。
- **可換性のホモトピー**(`DifferentialSwapHomotopy`):一般の成分について

  `x·y − (−1)^(k₁k₂) y·x = dH(x, y) + H(dx, y) + (−1)^k₁ H(x, dy)`

  `H(x, y) = ( s c₁∪₁c₂ , (−1)^k₁ h₁∪h₂ − (−1)^k₂ ω₁∪₁h₂ − (−1)^(k₁+k₂) h₁∪₁c₂ , s ω₁∪₁ω₂ )`、`s = (−1)^(k₁+k₂+1)`

  が成り立つ。Villain 場の上では `H(T(A), T(B)) = (−m, −λ/2π, 欠損/2π)` で、上の λ、m、`F_A∪₁F_B` の項は H の 3 つの成分である。
  ゲージ変換は第 3 成分が 0 の differential cochain の余境界なので、H の第 3 成分 `s ω₁∪₁ω₂` がゲージ変換に入らない部分になる。
  連続理論では ω は微分形式で、∧ が厳密に次数付き可換だから、この成分は現れない。

**量子化との照合**(arXiv:2303.06160、arXiv:2401.09597 に対して。`ChernSimonsZeroModeCount`、`StaggeredMomentumCount`):

- **零モード**:三次元トーラス(辺の長さ L₁, L₂, L₃、V = L₁L₂L₃)の上の二次形式 `Σ a∪δa` は、閉じた 1-cochain
  (ゲージ変換と平坦な接続、V + 2 次元)のほかに零モードを持つ。その数は、`p₁ + p₂ + p₃ = π` を満たす運動量 1 つにつき 2 個で、
  lcm(L₁, L₂, L₃) が偶数なら `2V/lcm`、辺がすべて奇数なら 0 である(行列の階数から数える。参照実装で 10 通りの格子)。
  arXiv:2303.06160 の staggered な対称性の零モードで、framing のない Wilson loop が落ちることの原因である。
  同じ数え方を二次元の空間格子ですると `L₁L₂/lcm(L₁, L₂) = gcd(L₁, L₂)` になり、
  正準量子化(arXiv:2401.09597)で非局所的な拘束が現れる運動量の数と同じ形である。辺がすべて奇数なら、拘束そのものがない。
- **大きいゲージ変換の代数**:5 節の大きいゲージ変換の恒等式の全微分の項 `B(m; a) = −(k/2) m∪a` は

  `B(m + m′; a) − B(m; a + 2πm′) − B(m′; a) = kπ m∪m′`

  を満たす。arXiv:2401.09597 の大きいゲージ変換の演算子の合成則 `U[m]U[m′] = U[m+m′] exp(ikπ Σ m∪m′)` と同じ形である。
  その対称部分は (A3) で `m∪m′ + m′∪m = −δ(m∪₁m′) + δm∪₁m′ − m∪₁δm′` と ∪₁ で書ける。
  k が奇数のときに残る障害がこれで、次の小節で扱う。

**奇数 level:障害と、それを消す符号**(`ChernSimonsLargeGaugeAnomaly`、`SpinStructureSign`、``Operadica`Lattice` `` の `THooftFlux`。`reference/oddlevel_reference.py` で確認)

`Q(x) = x∪x + x∪₁δx` と置く(5 節の Pontryagin 平方 `P(x)` に `2 x∪₁δx` を足したもの。2 を法として P と同じ)。
一般の cochain について、立方格子と単体の両方で次が厳密に成り立つ。

- **inflow**(四次元):Chern–Simons のラグランジアン L の余境界は

  `δL = (k/4π) Q(F) − kπ Q(n) + (ka + δφ)∪δn`

  である。第 1 項は F だけで書けるのでゲージ不変で、monopole がなければ θ = 2πk の θ 項になる。第 3 項は monopole がなければ消える。
  つまり L は θ 項の原始関数に `kπ Q(n)` だけ足りない。k が偶数ならこれは 2π × 整数 cochain で、重み `exp(iS)` には効かない。
  k が奇数なら `π Q(n)` が残る。これは 6 節の fermion の類 `(1/2) P(B)`(B = n mod 2)の 2π 倍である。
- **アノマリー**(三次元):大きいゲージ変換でのラグランジアンの変化(5 節)は `−(k/2) δ(m∪a) − kπ q(m, n)` で、

  `q(m, n) = m∪n + n∪m + m∪₁δn + δm∪m`(整数 cochain。`ChernSimonsLargeGaugeAnomaly[m, n]`)

  閉じた格子の上で `exp(iS)` は `(−1)^(k Σq)` 倍になる。
- **q は Q の降下**(四次元):`Q(n + δm) − Q(n) = δq(m, n) + 2 m∪δn`。境界のアノマリーが、内部の項 `kπ Q(n)` の変化で打ち消される。
- **q は大きいゲージ変換の群の cocycle**:`q(m, n) + q(m′, n + δm) − q(m + m′, n) = −δ(m′∪m)`。
  アノマリーを n だけの関数で打ち消せるかどうかが、意味のある問いになる(Wess–Zumino の整合性条件)。
- 2 を法とし全微分を除くと、q は Gu–Wen の形 `m∪δm + δm∪₁n` になる:
  `q(m, n) = m∪δm + δm∪₁n + δ(m∪m + m∪₁n) + 2 (n∪m + m∪₁δn − δm∪₁n)`。
- **level 4k**:`L_k(a, n, φ) = L_4k(a/2, n/2, 2φ)`。level k の理論は、level 4k の理論(偶数 level)で flux を半整数まで許したものである。
  Z₂ の 1-form 対称性をゲージ化したものと読めて、n mod 2 がその 2-form ゲージ場、上の障害がこの対称性のアノマリーにあたる。
  3.7 節の fermion condensation(level 4k の線 2k が fermion)の、格子の作用の側の形である。

三次元トーラス(周期的な立方格子)の上では、次のことを確かめている。

- **障害は実際に現れる**:`Σ q(m, n)` は奇数になりうる。最小の例は、角で出会う 2 本の link `((0,0,0); 1)` と `((1,0,0); 2)` の上で 1、ほかで 0 の m と、n = 0 で、`Σ q = 1`。
  link 1 本では 0。閉じた m(ゲージ変換と平坦な部分)では、閉じた n について Σq は偶数になる。
- **flux**:閉じた整数 2-cochain n は `THooftFluxCochain[z] + δm` と書ける。z は座標平面の上の n の和で、`THooftFlux[n, dims]` が返す。
- **符号**:2 を法として閉じた整数 2-cochain n の上の、±1 に値を持つ関数 z で

  (i) `z(n + δm) = z(n) (−1)^(Σ q(m, n))`   (ii) `z(n + n′) = z(n) z(n′) (−1)^(Σ n∪₁n′)`

  を満たすものを考える。(i) は「k が奇数のとき `exp(iS)·z(n)` が大きいゲージ変換で不変」という条件、
  (ii) は z が ∪₁ の対の二次の精密化であるという条件である。
  - そのような z は 8 個ある。3 つの単位 flux(`THooftFluxCochain`)の上の値 `(s₁₂, s₁₃, s₂₃)` で決まる(`SpinStructureSign[dims, {s12, s13, s23}][n]`)。
  - 2 つの z の比は `(−1)^(Σ α∪n)`(α は 2 を法として平坦な 1-cochain)。8 個は H¹(T³; Z₂) の torsor をなし、連続理論の spin 構造と同じ数え方になる。
  - `z(δm) = (−1)^(Σ δm∪m)`。上の 2 本の link の m では、どの z でも −1 である。可縮な flux の輪でも、格子の上の形によって符号が付く。
  - (μ, ν) 面を貫くまっすぐな flux の管は、どこに置いても符号 s_μν を持つ。
  - 計算は、`n = (代表の flux) + δm` を 2 を法として解き(行簡約)、(i) で代表まで戻す。代表の上の値は (ii) で決める(3 つの代表どうしの ∪₁ の対は 1)。

**境界条件との対応**(`SpinStructureHolonomy`):flux を座標平面の中に制限すると、z は二次元トーラスの spin 構造の二次形式になる。

- 方向 ρ に沿った link の上だけに値を持つ m と、ρ を含む plaquette の上だけに値を持つ n(双対の曲線が ρ に直交する平面の中にある flux)については、
  `m∪n + n∪m + δm∪m = 0` が恒等的に成り立つ。したがって `q(m, n) = m∪₁δn` で、閉じた n では 0 になる:平面の中の変形で z は変わらない。
- その平面の中の flux の上で、z は双対の曲線の類 `(w_a, w_b)`(2 つの方向に巻く回数の偶奇)だけで決まり、

  `z = s_a^(w_a) s_b^(w_b) (−1)^(w_a w_b)`

  である(s_a、s_b はその平面の 2 種類のまっすぐな管の符号)。平面の中で可縮な曲線では 1 になる。
- `z = (−1)^e` と書くと `e(w + w′) = e(w) + e(w′) + w·w′`(w·w′ は交点数)で、e は交叉形式の二次の精密化である。
  Johnson の定理により、これは二次元トーラスの spin 構造と同じもので、e = 1 はその曲線に沿って fermion が周期的であることを意味する。
  3 つの 0 でない類のすべてで e = 1 になるのは、両方向に周期的な(Arf 不変量が 1 の)spin 構造だけである。
- したがって、方向 ρ の境界条件は、ρ に沿ったまっすぐな flux の管の符号で決まる:`s = −1` が周期的、`s = +1` が反周期的。
  `SpinStructureHolonomy[{s12, s13, s23}]` は `{h₁, h₂, h₃} = {−s₂₃, −s₁₃, −s₁₂}`(1 が周期的、−1 が反周期的)を返す。
  `{1, 1, 1}` は 3 方向とも反周期的、`{−1, −1, −1}` は 3 方向とも周期的である。
- 平面の中で可縮でない曲線の上では `z = −(その曲線に沿った holonomy)`、可縮な曲線の上では `z = +1`。閉じた fermion の世界線の符号の形になっている。

**符号の局所的な式:Grassmann 積分**(`GuWenGrassmannSign`。`reference/grassmann_reference.py` で確認)

上の z は条件 (i)・(ii) で特徴づけた関数で、計算には線形方程式を解いている。同じ関数は、Gu–Wen 型の Grassmann 積分として局所的に書ける。

- plaquette は 2 つの立方体の面である:x にあって μ に垂直な plaquette は、立方体 x − e_μ の「前の面」F_μ で、立方体 x の「後ろの面」B_μ である。
- n が奇数の plaquette ごとに、その 2 つの立方体に 1 つずつ Grassmann 変数を置く。
- 立方体 x は、n が奇数の面の変数を **F1, B2, F3, B1, F2, B3** の順に掛けたものを寄与する。n が 2 を法として閉じていれば個数は偶数で、
  立方体どうしの積の順序は効かない。
- plaquette の 2 つの変数の対は、「この順で後ろの slot の変数、前の slot の変数」の順の積に対して重み 1 で積分する。

`σ(n)` は全立方体の積の積分で、変数を対に並べ替える置換の符号である(`GuWenGrassmannSign[dims][n]`)。確かめていること:

- **変数の順序は決まる**:6 つの面の並べ方 720 通りのうち、(ii) を満たす関数を与えるのは 12 通りで、上の順を巡回的に読んだもの
  (向きと出発点の取り方)だけである。そのすべてで (i) も成り立つ(3×3×3 と 3×4×4)。立方体の上の `n∪₁n′` が結ぶ面の対は、
  F1・B2・F3 の中の対と B1・F2・B3 の中の対、つまり角 (1, 0, 1) と (0, 1, 0) に集まる面どうしである。
- **値**:まっすぐな flux の管の上で、どの方向でも、どの長さでも −1(周期的な境界条件での、閉じたまっすぐな fermion の世界線の符号)。
  link 1 本の境界(plaquette 4 枚の輪)で +1、角で出会う 2 本の link の境界で −1。
- **σ は (i)・(ii) を満たす**。したがって k が奇数のとき、重み `exp(iS)·σ(n)^k` は大きいゲージ変換で不変である。
- **8 個の z は、境界条件つきの Grassmann 積分である**:`h = SpinStructureHolonomy[{s12, s13, s23}]` として

  `z(n) = σ(n) · h₁^(平面 x₁ = 0 を貫く flux) · h₂^(…) · h₃^(…)`

  (`GuWenGrassmannSign[dims, h][n]`)。壁 `x_ρ = 0` を世界線が横切るたびに h_ρ(1 が周期的、−1 が反周期的)が掛かる。
  上の「境界条件との対応」は座標平面の中の flux の二次形式から読み取ったものだったが、ここでは局所的な式そのものから出る。
  平面に収まらない配置(2 本の link の例など)の符号も、この式が与える。

確かめたのは三次元トーラスだけで(参照実装で 3×3×3、3×3×4、4×4×4。まっすぐな管は 7 通りの大きさ)、単体複体(w₂ の代表が現れるはずである)は扱っていない。
ここでの式は立方格子の ∪₁ に合わせて順序を探して決めたもので、文献の式(Gu–Wen と Gaiotto–Kapustin の Grassmann 積分。
奇数 level の格子 Chern–Simons については arXiv:2601.04318 と arXiv:2601.15939 の 13.1 節)と項ごとに照合してはいない。

**背景場と 1-form 対称性のアノマリー**(橋の `ChernSimonsOneFormAnomalyQ` は 6 節。`reference/cech_reference.py` で確認)

- `L_k(a, n, φ) = L_(kN²)(a/N, n/N, Nφ)`:level k の理論は、level kN² の理論で flux を Z/N まで許したものである(N = 2 が上の level 4k)。
- level K の理論に Z_N の 2-form 背景場 B を flux `n + B/N` として入れると、inflow の恒等式の `Kπ Q(n)` は

  `Kπ [ Q(n) + X(n, B)/N + Q(B)/N² ]`、`X(n, B) = n∪B + B∪n + n∪₁δB + B∪₁δn`

  になる。`X = 2 B∪n − δ(n∪₁B) + δn∪₁B + 2 n∪₁δB + B∪₁δn` なので、n が閉じていて δB が N の倍数なら、
  N が K を割るとき、交差項は全微分と 2π × 整数である。
- 残るのは `2π (K/2N²) Q(B)` で、平坦な Z_N 場の上では 6 節の `(p/2N) P(B)`、p = K/N に 1 を法として一致する。
  電荷 K/N の線の類で、その spin は K/2N² である。
- spin が 0 なら対称性はゲージ化でき(結果は level K/N²)、1/2 なら spin 構造が要り(level K/N² が奇数)、
  それ以外ではゲージ化できない。K = kN² では spin は k/2 で、k の偶奇だけで決まる。

**Čech–de Rham の形**(`VillainPatchPrimitive`、`CechDeRhamConnection`、`CechDeRhamTransition`、`CechDeRhamChern`、`CechDeRhamCocycleQ`、
`CechDeRhamChernNumbers`。`reference/cech_reference.py` で確認)

Y. Ikeda の格子 Deligne–Beilinson コホモロジー(arXiv:2601.15939)は Čech–de Rham 型で、patch は格子の単位立方体
(双対格子の点を中心とする立方体)である。三次元トーラスの上の次数 2 の類は 3 つ組

- `A_p`:立方体 p の link の上の実数値 1-cochain
- `Λ_pq`:2 つの立方体の交わりの site の上の実数値 0-cochain
- `N_pqr`:共通点を持つ 3 つの立方体に対する整数

で、`A_q − A_p = dΛ_pq`、`Λ_qr − Λ_pr + Λ_pq = −N_pqr`、N が Čech cocycle、を満たすものである
(同論文の式 (4.14)〜(4.17)、(5.4)、(7.48) の規約。接続の周期は 1)。同論文は、modified Villain 形式の変数との
cocycle の段階での対応を与えておらず、Villain 形式で Λ を省ける理由は明らかでないとしている。

平坦な Villain 場 (a, n) からは、降下でこの 3 つ組が作れる(立方体は最小の角 p で表す。辺の長さは 3 以上):

1. 各立方体の上で `δm_p = n` を解く(`VillainPatchPrimitive`)。立方体は可縮で n は閉じているので整数の解があり、
   link の木の上で 0 になるものを取る。`A_p = a/2π − m_p` と置く。
2. 交わりの上で `m_p − m_q` は閉じているので、`δΛ_pq` と書ける。Λ_pq は、交わりの最小の角からの道に沿った和(整数)である。
3. 3 つの立方体の共通部分の上で `Λ_qr − Λ_pr + Λ_pq` は定数になり、その符号を変えたものが N_pqr である。

確かめていること(参照実装で 3×3×3 と 3×4×5 のトーラス。Wolfram Language のテストは 3×3×3):

- 3 つの条件と、`δA_p = F/2π`(曲率は patch に依らない)。n が閉じていなければ、1 の段階で失敗する。
- **N の類は Chern 類である**:脈体の中で三角形分割した座標トーラスの上の N の和(`CechDeRhamChernNumbers`)は、n の flux(`THooftFlux`)に等しい。
- **Λ と N は n だけの関数である**:modified Villain 形式に遷移関数が現れないのは、大域的な整数の場 n が、遷移関数 Λ と
  三重の重なりの整数 N を、coboundary を除いてすでに決めているからである。ゲージ変換 `a → a + δλ` は A_p を `d(λ/2π)` だけ変え、Λ と N を変えない。
  m_p と Λ は整数なので、閉じた道に沿った holonomy は、どちらの形でも 1 を法として `Σ a/2π` である。

**星積と積分**(`CechDeRhamTriple`、`CechDeRhamFundamentalCycle`、`CechDeRhamStarIntegral`、`CechDeRhamGaugeTransform`、
`CechDeRhamLargeGauge`、`CechDeRhamAnomaly`。
`reference/star_reference.py` で確認)

2 つの 3 つ組 (A, Λ, N)、(A′, Λ′, N′) の星積(同論文 7 節の形:前の因子が前の patch、後の因子が後の patch を取り、patch を 1 つ共有する)は

| 成分 | 式 | 置かれる場所 |
|---|---|---|
| (3, 0) | `A_p ∪ dA′_p` | 立方体 p |
| (2, 1) | `Λ_pq ∪ dA′_q` | p と q の交わりの plaquette |
| (1, 2) | `N_pqr A′_r` | 3 つの交わりの link |
| (0, 3) | `N_pqr Λ′_rs` | 4 つの交わりの site |
| (−1, 4) | `N_pqr N′_rst` | 整数(積分には寄与しない) |

である。cocycle 条件から、Čech の coboundary `δ̌`(順序のついた組の上)と格子の coboundary `d` について
`δ̌ω₃₀ = dω₂₁`、`δ̌ω₂₁ = −dω₁₂`、`δ̌ω₁₂ = dω₀₃`、`δ̌ω₀₃ = −N N′` が出る。したがって積分は、

    ∂σ₃₀ + ∂̌σ₂₁ = 0,   ∂σ₂₁ − ∂̌σ₁₂ = 0,   ∂σ₁₂ + ∂̌σ₀₃ = 0

を満たす鎖 `σ₃₀ + σ₂₁ + σ₁₂ + σ₀₃`(`σ_ij` は「次元 i の cell と、それを含む j+1 個の立方体」の整数係数の和)との対で、
1 を法として定まる。この鎖(`CechDeRhamFundamentalCycle`)は錐で作る:`σ₃₀` は「立方体 x を、それ自身の中で」の和で、
次の段は、前の段の境界に現れる各 cell に、**その cell の基点を最小の角とする立方体を最後の patch として付け加えた**ものである。
積が消える項(N と Λ は交代的)を落とすと、1 つの site あたり 1 + 3 + 6 + 6 項で、係数はすべて ±1 になる:

- `σ₂₁`:x にあって μ に垂直な plaquette を、立方体 `(x − e_μ, x)` の中で、係数 `(−1)^(μ−1)`
- `σ₁₂`:link (x; μ) を、`(x − e_α − e_β, x − e_β, x)` の中で係数 `(−1)^(μ−1)`、`(x − e_α − e_β, x − e_α, x)` の中でその逆符号(α < β は μ 以外の方向)
- `σ₀₃`:site x を、x で終わる link (x − e_μ; μ) の 2 項それぞれの最後に立方体 x を付け加えたものの中で、同じ係数

`σ₂₁` は同論文の式と一致する。`σ₁₂` と `σ₀₃` は項の数(各 6 項)が同論文と一致するが、**符号と patch の並びは同論文の式と照合していない**
(論文の式は PDF の本文を機械的に読んだものしか見ていない)。ここでの符号は上の 3 つの条件で決めてあり、その条件自体を
順序のついた鎖の上で確かめている。

確かめていること(参照実装で 3×3×3、3×3×4、3×4×5。Wolfram Language のテストは 3×3×3):

- **1 を法として定まる**:ゲージ変換 `A_p → A_p + dξ_p`、`Λ_pq → Λ_pq + ξ_q − ξ_p − m_pq`、`N → N + δ̌m`(`CechDeRhamGaugeTransform`)で、
  ξ だけなら 4 つの寄与の間で値が移るが合計は変わらず、整数 m があると合計は整数だけ変わる(どちらの因子を変換しても)。
- **平坦な Villain 場の 3 つ組の上では、項ごとに Villain の式になる**:(a, n) と (b, n′) について 4 つの寄与は、等式として

      Σ (a/2π) ∪ (F_B/2π),   0,   −Σ n ∪ (b/2π),   0

  である。(2, 1) と (0, 3) が消えるのは、Λ が鎖の各 plaquette・site の基点で 0 になるからで、(3, 0) と (1, 2) に m_p が現れないのは、
  m_p が立方体の基点から出る link の上で 0 だからである(どちらも、上の木のゲージと「最後の patch は基点の立方体」という鎖の選び方による)。
  したがって**積分は `(1/2π) Σ VillainConnection[DeligneProduct[A, B]]` に等しい**。v0.13.0 以来の `DeligneProduct` は、
  降下したあとの星積そのものである。A = B なら `(1/2π) Σ VillainChernSimons[2]`、すなわち level 2 の作用で、
  同論文の「level 2k の作用は `∫ k a⋆a`」と合う。
- **偶数 level と奇数 level**:level 2j の重みは `exp(2πi j ∫A⋆A)` で、類の関数である。`∫A⋆A` の半分は 1 を法として定まらない:
  大きなゲージ変換 `(a + 2πm, n + δm)` と (a, n) はゲージ同値な 3 つ組を与えるが、積分は `−Σ q(m, n)` だけ違い、これは奇数になりうる
  (テストでは 17)。上の「奇数 level」の障害と同じものが、Čech–de Rham の側では「積分が 1 を法としてしか定まらない」こととして現れる。
- **アノマリーの Čech の形**(`CechDeRhamAnomaly`):同じゲージ変換 (ξ, m) を `∫A⋆A` の両方の因子に施すと、積分は

      −⟨ m∪N + N∪m + δ̌m∪m , σ₀₃ ⟩,   (m∪N + N∪m + δ̌m∪m)_pqrs = m_pq N_qrs + N_pqr m_rs + (δ̌m)_pqr m_rs

  だけ変わる(∪ は Čech の cup 積。ξ には依らない)。格子の上の `q(m, n) = m∪n + n∪m + δm∪m`(閉じた n では ∪₁ の項は消える)と同じ形である。
- **大きいゲージ変換は 3 つ組のゲージ変換である**(`CechDeRhamLargeGauge`):`(a + 2πm, n + δm)` の 3 つ組は、(a, n) の 3 つ組を

      ξ_p(x) = 立方体 p の木に沿った p から x までの m の和,   m̌_pq = (ξ_q − ξ_p)(交わりの最小の角)

  でゲージ変換したものに、関数として一致する。この m̌ について上の対は `Σ q(m, n)` に等しい(テストでは 17)。
  Villain の側の障害と Čech–de Rham の側の障害は、降下で互いに移る同じ整数である。
- **格子の上では 2 つの因子について対称でない**:`I(A, B) − I(B, A) = −Σ (F_A/2π) ∪₁ (F_B/2π) + Σ n ∪₁ n′`。
  どちらかの曲率が 0 なら 1 を法として対称である。∪ が ∪₁ を除いてしか可換でないことの現れで、`DeligneSwapGauge` の m(`n∪₁n′`)と
  `DeligneSwapDefect`(`F_A∪₁F_B` の項)を積分したものにあたる。

成り立つ範囲:辺の長さが 3 以上の三次元トーラス、平坦な場(`δn = 0`。monopole があると降下の最初の段階で失敗する)。

まだしていないこと:同論文の対称化した積(∪₁ の補正が入る)と奇数 level の扱い(13.1 節)を、上の非対称性および 3.9 節の符号 z と比べること。
Čech–de Rham の類から Villain 場への逆向きの写像。同論文の式は本文から読み取ったもので、`σ₂₁` と cocycle 条件のほかは、符号の規約を 1 つずつ照合してはいない。

補正項の探索は 3.8 節にある。

## 4. 自動検証の4つの強さ

検証結果には、どの強さで通ったかを `"Strength"` に残す。

1. **構成による保証**:自由 operad は接ぎ木なので公理が構造的に成り立つ。
   テストは実装の誤り検出用。
2. **有限全数検査**:有限な operad・代数・圏は、全組合せを調べる。その範囲では証明である。
   `OperadAxiomCheck`、`PentagonQ`、`HexagonQ`、`BarCocycleQ`。
   生成元と関係式による operad では、arity ごとのイデアルの階数の計算がこれにあたる。
   `OperadZeroQ` が True を返せば、その恒等式は関係式から従う(その arity での証明)。
3. **記号的恒等式**:一般の cochain の値、一般の little cubes の端点は独立な変数になる。
   cochain 演算は局所的で並進不変なので、記号的な基点 1 か所での検査が、その次元のすべての
   超立方格子・すべての可換な係数環での証明になる。`CochainEqualQ`、`LittleCubesOperad`。
4. **合流性**:有限表示の operad は、critical pair が現れる arity までの局所合流性の検査で
   正規形が全 arity で確定する。`OpLocallyConfluentQ`。
   位相つきの合流性が五角形方程式である。`MacLaneCoherenceQ`。

検証できないもの:arity や次数についての全称的な主張(帰納法が必要)と、弱同値。

## 5. 符号規約(格子層)

- δ:`(δc)(x; μ₁<…<μₖ) = Σⱼ (−1)^(j−1) [ c(x+μ̂ⱼ; μⱼ を除く) − c(x; μⱼ を除く) ]`
- ∪:`(a∪b)(x; S) = Σ sgn(A,B) a(x; A) b(x+Â; B)`。S を前半 A(p 個)と残り B に分ける。
- ∪ᵢ:Jacobson–Sulejmanpasic, arXiv:2303.06160 の式 (A3)

  `a∪ᵢb − (−1)^(pq+i) b∪ᵢa = (−1)^(p+q+1+i) [ δ(a∪ᵢ₊₁b) − δa∪ᵢ₊₁b − (−1)^p a∪ᵢ₊₁δb ]`

  に従う。同論文の付録 A の成分公式(Chen–Tata, arXiv:2106.05274 に従うもの)を再現する。
- Steenrod の元の規約との差は `(−1)^(i(p+q+1))`(`SteenrodCupSign`)。
- Pontryagin 平方:`P(B) = B∪B − B∪₁δB`。

### 単体の上の cochain

頂点に順序のついた単体 `{v0 < … < vn}` の上では(`reference/simplicial_reference.py` で確認)

- δ:`(δc)(v0…v(p+1)) = Σₖ (−1)ᵏ c(v0 … vₖ を除く … v(p+1))`
- ∪:`(a∪b)(v0…v(p+q)) = a(v0…vp) b(vp…v(p+q))`
- ∪ᵢ(Steenrod):n = p+q−i として、切れ目 `0 ≤ j₀ < j₁ < … < jᵢ ≤ n` にわたる和

  `(a∪ᵢb)(0…n) = Σ ± a(0…j₀, j₁…j₂, …) b(j₀…j₁, j₂…j₃, …)`

  区間 `[0,j₀], [j₀,j₁], …, [jᵢ,n]` を交互に a と b に渡す。符号は、置換
  「a の頂点、続けて b の頂点のうち切れ目でないもの」の符号。`SimplexHigherCupTerms`。

この符号で、立方格子と**同じ形の (A3)** が成り立つ。したがって (A3) から従う恒等式は二つの格子で同じ形になる。
下の Pontryagin 平方の二つの恒等式と `a∪δa − δa∪a` の恒等式は、単体の上でもそのまま成り立つ(`Tests/Simplicial.wlt`)。
二つの格子が違うのは arity 3 からで、Hirsch 公式

`(a∪b)∪₁c = a∪(b∪₁c) + (−1)^(q(r−1)) (a∪₁c)∪b`

は単体の上では厳密に成り立ち、立方格子ではホモトピー H を除いてしか成り立たない(6 節)。
同じ式 `HigherCup[1][Cup[a, b], c] − …` を `SimplexCochainZeroQ` と `CochainZeroQ` に渡すと、True と False が返る。

### Steenrod 平方

p-cochain x に対し `Sq^k x = x ∪_(p−k) x` と置く(`SteenrodSquare[k][x]`。0 ≤ k ≤ p 以外では 0)。
同じ式を立方格子と単体の両方で評価できる(`reference/steenrod_reference.py` で確認)。

- `Sq^p x = x∪x`。`Sq⁰ x` の値は x の値の 2 乗で、2 を法として x そのものである。
- (A3) で a = b = x と置くと、どちらの格子でも

  `δ(Sq^k x) = (−1)^(p−k) (1 + (−1)^k) Sq^(k+1) x + δx ∪_(p−k) x + (−1)^p x ∪_(p−k) δx`

  が成り立つ。δx が偶数(x が Z₂ cocycle の整数への持ち上げ)なら、右辺は偶数で、Sq^k x は 2 を法とする cocycle になる。
- k が偶数のときは右辺の第 1 項が `±2 Sq^(k+1) x` なので、Sq^(k+1) x は Sq^k x の Bockstein を表す
  (コホモロジー類として。Adem 関係式 Sq¹Sq^(2m) = Sq^(2m+1) の cochain での形)。
- 値を 0, 1 に持ち上げた平坦な Z₂ 場 B では、`Sq¹B ≡ δB/2`(mod 2)が cochain の等式として成り立つ。
  1-form 場では `A∪A = δA/2` が厳密に成り立つ。K(Z₂, n)(n ≤ 3)のすべての単体で確かめている(6 節)。

### ∪ᵢ の構成

区間の鎖複体に Δ₀(e) = v₀⊗e + e⊗v₁、Δ₁(e) = −e⊗e を置き、ℤ/2 の標準分解の対角
`ψ(eᵢ) = Σⱼ (−1)^(j(i−j)) eⱼ ⊗ Tʲeᵢ₋ⱼ` によるテンソル積の公式で n 次元立方体へ延ばす。
結果は次の「語」による閉じた公式になる。cell の各方向に 1(a だけが伸びる)、
2(b だけが伸びる)、3(両方が伸びる、ちょうど i 個)を割り当て、
その方向より前にある 3 の個数を t とすると、

- 1 の方向:t が偶数のとき b をその方向に 1 ずらす
- 2 の方向:t が奇数のとき a をその方向に 1 ずらす
- 符号 `(−1)^e`、`e = i(i+1)/2 + #{k<l : wₖ∈{2,3}, wₗ∈{1,3}} + #{k<l : wₖ∈{1,2}, wₗ=3}`

### 検証済みの恒等式(格子ゲージ理論層)

いずれも cochain の厳密な恒等式で、`Tests/Gauge.wlt` に入っている。

- `P(B+δλ) − P(B) = δ[2λ∪B + λ∪δλ − B∪₁δλ] + 2λ∪δB + δB∪₁δλ − δλ∪₁δB`
- `P(B+Nc) − P(B) = 2N c∪B + N²(c∪c − c∪₁δc) − N δ(B∪₁c) + N(δB∪₁c − c∪₁δB)`
- `a∪δa − δa∪a = δ(a∪₁δa) − δa∪₁δa`
- modified Villain Chern–Simons(arXiv:2303.06160 式 (17))の 0-form ゲージ変換
  `a → a+δλ`、`φ → φ−kλ` で、ラグランジアンの変化は
  `δ[(k/4π) λ∪δa − k λ∪n + (k/2) δλ∪₁n]`。∪₁ の項がないと成り立たない。
- 同じ作用の大きいゲージ変換 `a → a+2πm`、`n → n+δm` での変化は
  `−(k/2) δ(m∪a) − kπ (m∪n + n∪m + m∪₁δn + δm∪m)`。

### ∪₁ は ∪ の導分ではない

単体的 cochain では Hirsch 公式 `(a∪b)∪₁c = a∪(b∪₁c) ± (a∪₁c)∪b` が成り立つが、
ここで使う立方格子の ∪₁ では、符号をどう選んでも、左右どちらの形でも成り立たない。
2 次元の 1-cochain では欠損は

`[(a∪b)∪₁c − a∪(b∪₁c) − (a∪₁c)∪b](x; 12) = −a(x; 2) b(x+2̂; 1) (δc)(x; 12)`

で、c が閉じていれば消える。3 次元でも、c が完全な 1-cochain なら、a, b の次数 (1,1)、(1,2)、(2,1) で
符号 (+, +) の Hirsch 公式が成り立つ。c が 2-cochain のとき(次数 (1,1,2))は、完全でも成り立たない。
Gerstenhaber operad の Leibniz 則が cochain の上ではホモトピーを除いてしか成り立たないことの、
具体的な形である。`Tests/Lattice.wlt` の `Lattice-Hirsch-defect`、`Lattice-Hirsch-closed`。
そのホモトピーは 6 節の arity 3 の演算 H で、すべての次数で式が書ける。

## 6. 橋

| 主張 | 関数 |
|---|---|
| (C*, ∪) は結合 operad As の代数 | `CupAlgebraOverAsQ` |
| ∪ᵢ は E∞ operad の arity 2 部分 W の作用。∪ᵢ は E_(i+1) の段にある | `EInfinityArityTwoQ` |
| 格子 cochain は Barratt–Eccles operad(E∞)の代数。arity 2 が ∪ᵢ | `EInfinityOperation`、`EInfinityLeibnizQ`、`EInfinityCompositionQ`、`EInfinityEquivarianceQ`、`EInfinityHigherCupQ` |
| Hirsch 公式は arity 3 のホモトピー H を除いて成り立つ | `HirschHomotopy`、`HirschFormulaQ` |
| C_n(k) の Betti 数 = Pₙ の arity k の成分の次数ごとの次元(H_*(Eₙ) = Pₙ の、次元での確認) | `LittleCubesHomologyQ` |
| 同じことを Barratt–Eccles operad の段 F_n で(組合せ的な Eₙ operad) | `BarrattEcclesHomologyQ` |
| 五角形方程式 ⇔ 結合則の書き換えの、位相つきの合流性(Mac Lane の coherence) | `MacLaneCoherenceQ` |
| 圏のデータ (w, c) は Bⁿ の次数 n+2 の cochain。Eₙ 構造 ⇔ cocycle(n = 1, 2, 3 がモノイダル、braided、symmetric) | `BarCochainValue`、`BarCoboundaryTable`、`BarCocycleQ`、`DeloopingClassificationQ` |
| A 上の Eₙ 構造の個数 = H_(n+2)(K(A, n)) の位数 | `EnStructureCount` |
| 平坦な Z_N ゲージ場の上の格子作用 `(k/N²) A∪δA` は K(Z_N, 1) の 3-cocycle で、四面体の上の値が `VecZN[N, k]` の associator | `FlatFieldCochain`、`DijkgraafWittenWeight`、`DijkgraafWittenAssociatorQ` |
| `(p/2N) P(B)` は K(Z_N, 2) の 4-cocycle で、その類の位数は `ZNAnyons[N, p]` の spin p/2N の分母 | `PontryaginWeight`、`PontryaginSpinQ` |
| 平坦な Z₂ 場の Steenrod 平方:`Sq¹B` は Bockstein `δB/2`(cochain として)。`(1/2) Sq^k B` は K(Z₂, n) の R/Z 値の cocycle | `SteenrodBocksteinQ`、`SteenrodWeight` |
| `(1/2) Sq²` の類は K(Z₂, 2)(`(1/2) B∪B`)と K(Z₂, 3)(`(1/2) C∪₁C`)で位数 2。braided な構造、symmetric な構造としての fermion | `SteenrodFermionQ` |
| 平坦な Z_N 場は平坦な Villain 場。偶数 level k の U(1) Chern–Simons のラグランジアン/2π は K(Z_N, 1) の cocycle で、level −k/2 の Dijkgraaf–Witten の類 | `FlatVillainField`、`ChernSimonsWeight`、`ChernSimonsDijkgraafWittenQ` |
| level K の U(1) Chern–Simons の Z_N 1-form 対称性のアノマリーは、電荷 K/N の線の類 `(p/2N) P(B)`、p = K/N。その spin K/2N² がゲージ化できるかどうかを決める | `ChernSimonsOneFormAnomalyQ` |
| 近似定理 CₙX ≃ ΩⁿΣⁿX(X 連結)の、有理 Poincaré 級数での確認:H̃_*(X) の上の自由 Pₙ-代数 = H_*(ΩⁿΣⁿX; Q) | `ApproximationTheoremQ` |
| 近似定理の Z₂ 係数・n = 2 の場合:braid 群の Z₂ 係数 Betti 数 = Kudo–Araki の多項式代数 x, Qx, QQx, … の次元 | `ApproximationTheoremModTwoQ` |
| braided な圏は、対象を載せた little squares の配置の道に位相を与える。反時計回りの入れ替えが braiding c(a, b) | `PathBraidingPhase` |
| その位相は operad の合成と両立する。1 個が 2 個の列を越える道が六角形 1、2 個の列が 1 個を越える道が六角形 2 | `BlockBraidingQ`、`HexagonFromPathsQ` |
| 3 次元では 2 つの半回転がホモトピックで、位相が一致する条件は symmetric | `SymmetricFromPathsQ` |
| 四次元トーラス上の 't Hooft flux での重み `(p/2N)ΣP(B)` = flux の相互 braiding | `PontryaginFluxPhase`, `FluxBraidingPhase` |

### 格子 cochain は E∞ 代数

Barratt–Eccles operad の元 s(arity r、次数 m)と cochain a₁, …, a_r(次数 p₁, …, p_r)に対し

`θ_s(a₁, …, a_r)(x; S) = Σ_項 c ∏ⱼ aⱼ(x + shiftⱼ; Sⱼ)`

と置く(項は `CubeCoaction[s, |S|]`。次数は Σpⱼ − m)。`EInfinityOperation[s][a1, …, ar]`。
次の三つが成り立ち、cochain は E∞ operad の代数になる:

- (L) `δθ_s(a) = (−1)^m [ Σⱼ (−1)^(p₁+…+p_(j−1)) θ_s(…, δaⱼ, …) − θ_(ds)(a) ]`
- (C) `θ_(s∘ⱼt)(a) = (−1)^(|s||t| + |t|(p₁+…+p_(j−1))) θ_s(a₁, …, θ_t(aⱼ, …), …)`
- (E) `θ_(s·π)(a₁, …, a_r) = ± θ_s(a_(π⁻¹(1)), …, a_(π⁻¹(r)))`。符号は、pᵢ が奇数である i についての π(i) の並びの符号

語 `{1,2}` は ∪、`{1,2,3}` は三重の ∪ で、arity 2 の元は高次 cup 積そのものである:

`θ_(eᵢ)(a, b) = (−1)^(i(p+q) + i(i−1)/2) a ∪ᵢ b`

5 節の (A3) は (L) の arity 2 の場合にあたる。arity 3 以上の元は、∪ᵢ を合成するしかたの間のホモトピーを与える。

**Hirsch 公式**:`Ξ = {{1,2,3},{1,3,2},{3,1,2}}`(`HirschElement[]`、F₂ の元)、`H = θ_Ξ` とすると、
すべての次数 p, q, r ≥ 1 で

`(a∪b)∪₁c − a∪(b∪₁c) − (−1)^(q(r−1)) (a∪₁c)∪b = (−1)^(p+q+r) [ δH(a,b,c) − H(δa,b,c) − (−1)^p H(a,δb,c) − (−1)^(p+q) H(a,b,δc) ]`

`dΞ` の三つの項が左辺の三つの項にあたる。H は plaquette 上では 1 項

`H(a,b,c)(x; 12) = −a(x; 2) b(x+2̂; 1) c(x; 12)`(次数 (1,1,2))

で、3-cell 上では次数 (1,1,3)、(1,2,2)、(2,1,2) のそれぞれに 3 項(Ξ の作用の項は合わせて 9 個)。
c が 1-cochain のときは H = 0。5 節の欠損の式はこの特別な場合である。
Ξ の table reduction は 0 なので、surjection operad が作用する場合(単体的 cochain)には H = 0 で、
Hirsch 公式は厳密に成り立つ。立方格子ではテンソル積を通して作用するので H が残る。

検査はどれも一般の cochain と記号的な基点で行う(その次元のすべての格子での証明)。
(L)・(C)・(E) は 3 次元で arity 2 と 3 の元について、Hirsch 公式は 2、3、4 次元で検査している。

recognition theorem の物理的な中身:p-form 対称性の欠陥は余次元 p+1 で、横方向 ℝ^(p+1) での
融合が E_(p+1) 構造を持つ。可逆なら Ω^(p+1)B^(p+1)A と同値で、背景場は格子上の
(p+1)-cocycle になる。群 A 上の Eₙ 構造は H^(n+2)(K(A, n); U(1)) で分類される。
Z_N では n = 2 が N·gcd(2,N) 個(二次形式)、n = 3 が gcd(2,N) 個で、
`Tests/EnCategories.wlt` がこの個数を数えている。同じ個数を、この節の最後の小節で bar 構成から直接計算する。

C_n(2) ≃ S^(n−1) も同じ区別を与える。n = 1 は 2 成分(積が非可換)、n = 2 は円周
(braiding があり、2 回かけても自明でない)、n = 3 は球面(symmetric)。
`SimplicialBetti[SeparationNerve[n]]` がこれを計算する。
S^(n−1) の次数 0 の類が積、次数 n−1 の類が括弧で、これが Pₙ の生成元である。

k 個の立方体では、対ごとに「どの軸に沿って、どちらが先にあるか」を選ぶ。選び方 c ごとに、
それを満たす配置の集合 V_c は端点の線形不等式で切り出されるので凸で、交わりも凸である。
V_c は C_n(k) を覆うから、その脈体が C_n(k) のホモトピー型を与える(`SeparationNerve[n, k]`。
facet は「各軸に沿った立方体の全順序」の n 個組)。計算では、facet による被覆の脈体に移して
小さくする(`FacetNerve`。facet どうしの交わりは単体か空なので、ホモトピー型は変わらない)。
C_2(3) の Betti 数は 1, 3, 2 で、Gerstenhaber operad の arity 3
(積だけの元 1 個、括弧 1 個の元 3 個、括弧 2 個の元 2 個)に一致する。
この方法で計算できるのは k = 2 と (n, k) = (1, 3)、(1, 4)、(2, 3) まで。

### Eₙ 構造は BⁿA の上の cocycle

点付きの圏のデータは、反復 bar 構成(3.6)の上の、位相に値を持つ cochain になる:

`φ[a|b|c] = w(a, b, c)`、`φ[a‖b] = c(a, b)`(懸垂した生成元 `[x]` の上では x の上の値)

その余境界、つまり次数 n+3 の生成元の微分の上の値は、五角形と六角形の式(3.7 の式の左辺 − 右辺)そのものである:

- B¹:`[a|b|c|d]` の上で五角形
- B²:`[[a|b|c|d]]` の上で −五角形、`[a|b‖c]` の上で六角形 2、`[a‖b|c]` の上で六角形 1
- B³:B² の生成元の懸垂の上で、符号が逆の同じ式。`[a|||b]` の上で `−(c(a,b) + c(b,a))`
- B⁴:次数 7 に新しい生成元がないので、条件は B³ と同じ

したがって、単位対象で消えるように正規化したデータについて

- モノイダル(E₁)⇔ B¹ の 3-cocycle
- braided(E₂)⇔ B² の 4-cocycle
- symmetric(E₃ 以上)⇔ B³ の 5-cocycle

が成り立つ(`BarCocycleQ`、`DeloopingClassificationQ`)。A 上の Eₙ 構造は K(A, n) の (n+2)-cocycle であり、
「n 回 deloop できる圏」である。recognition theorem(群的な Eₙ 代数は n 重ループ空間)の、この設定での中身がこれである。

- **同値は coboundary**:`ψ[a|b] = f(a, b)` と置くと、f によるゲージ変換(3.7)で φ は `(−1)^(n−1) δψ` だけ変わる。
  同値な圏は同じコホモロジー類を与える。
- **個数**:U(1) は可除なので H^(n+2)(K(A, n); U(1)) = Hom(H_(n+2)(K(A, n)), U(1))。構造の個数は H_(n+2) の位数で、
  Z_N では N、N·gcd(2,N)、gcd(2,N)(`EnStructureCount`)。Z₂ × Z₂ では 8、32、4。
- **spin と相互 braiding は cycle の上の値**:`[a‖a]` と `[a‖b] + [b‖a]` は B² の cycle で、cocycle の値は
  spin `c(a,a)` と相互 braiding である。Z_N の生成元の spin の分母は N·gcd(2,N) まで取れて、
  `[1‖1]` の類が H₄(K(Z_N, 2)) を生成する(二次形式による分類)。semion(spin 1/4)は H⁴(K(Z₂, 2); U(1)) = Z₄ の生成元である。
- **symmetric なら boson か fermion**:B³ ではこれらの cycle が境界になる。
  `d[a|||b] = −[[a‖b] + [b‖a]]`、`d[a|||a] = −2[[a‖a]]`。
  5-cocycle の上では相互 braiding が消え、spin の 2 倍が 0 になる。H₅(K(Z_N, 3)) = Z_gcd(2,N) で、N が偶数のときの自明でない 5-cocycle が fermion(`SuperVec[]`)である。
- **物理**:K(A, n) への写像は n-form の A ゲージ場(背景場)で、(n+2)-cocycle の引き戻しは n+2 次元の位相的作用、
  すなわち (n−1)-form 対称性のアノマリーの inflow 作用である。n = 2、A = Z_N では Pontryagin 平方 `(p/2N)·P(B)` で、
  p は 2N を法とする整数(N が奇数なら偶数だけ)、あわせて N·gcd(2,N) 個。`ZNAnyons[N, p]` の p と同じものである。

### 格子の作用は K(A, n) の cocycle

K(Z_N, n) の k-単体は、k-単体の上の平坦な Z_N 値 n-form 場である(3.6)。その値を 0, …, N−1 の整数に持ち上げると
整数 cochain になり(`FlatFieldCochain`)、5 節の単体の上の演算で格子の作用を評価できる。持ち上げた場は閉じていない
(δÃ は N の倍数)。作用の値は 1 を法として K(Z_N, n) の cocycle になり、圏のデータと次のように対応する。

- **n = 1(Dijkgraaf–Witten)**:`(k/N²)(A∪δA)(0123) = (k/N)·a·carry(b, c)`(a, b, c は辺 01, 12, 23 の上の値)。
  これは `VecZN[N, k]` の associator `w(a, b, c)` と、すべての平坦な場の上で値として一致する。
  K(Z_N, 1) の 3-単体は bar 構成の語 `[a|b|c]` と同じものなので、6 節の前の小節の φ そのものである。
  k = 1 の類は H³(K(Z_N, 1); U(1)) = Z_N を生成する。
- **n = 2(Pontryagin 平方)**:`(p/2N) P(B)(01234)`、`P(B) = B∪B − B∪₁δB`。N が偶数なら任意の p、
  N が奇数なら偶数の p で cocycle になる。その類の位数は 2N/gcd(p, 2N) で、`ZNAnyons[N, p]` の生成元の
  spin p/2N の分母に等しい。p = 1(N が偶数)、p = 2(N が奇数)の類が H⁴(K(Z_N, 2); U(1)) = Z_(N·gcd(2,N)) を生成する。
  N = 2 では p = 1 が semion(位数 4)、p = 2 が fermion(位数 2)。
- **∪₁ の項は必要である**:`(1/2N) B∪B` だけでは cocycle にならない(N = 2 で確認)。`(1/N) B∪B` は cocycle で、
  N = 2 では fermion の類である。2N を法とする精密化に ∪₁ が要る。

- **n = 3(Steenrod 平方)**:Z₂ の 3-form 場 C に対し `(1/2) Sq²C = (1/2) C∪₁C` は K(Z₂, 3) の 5-cocycle で、
  その類の位数は 2。H⁵(K(Z₂, 3); U(1)) = Z₂ の生成元で、前の小節の「自明でない 5-cocycle = fermion」の、格子の作用としての形である。
  n = 1 の `A∪δA`(モノイダル)、n = 2 の `P(B)`(braided)に続く、symmetric(E₃ 以上)の場合にあたる。
  - cocycle であることは 5 節の `δ(Sq^k x)` の式から従う:`δ(C∪₁C) = −2 C∪C + δC∪₁C − C∪₁δC` で、δC が偶数なら右辺は偶数。
    K(Z₂, 3) の 6-単体は 2²⁰ 個あるので全数検査はしていない(参照実装で乱数の 2 万個。退化した 5-単体の上で 0 であることは全数)。
  - 類の位数は、5 次元の cycle の基底(退化していない 5-単体は 958 個)の上の値から求める。面 0 と面 5 が一致し、
    ほかの面がすべて退化している 5-単体が 1 個あり、それ 1 個で cycle になっていて、その上の重みが 1/2 である。
  - 物理では、3+1 次元の 2-form Z₂ 対称性(生成する線が fermion の世界線)のアノマリーの inflow 作用 `(1/2)∫Sq²C` にあたる。
- **`(1/2) Sq^k B` の一般の形**:K(Z₂, n) の (n+k)-単体の上の R/Z 値の cocycle である(`SteenrodWeight[n, k]`)。
  n = 2、k = 2 は `(1/2) B∪B` で、p = 2 の重み `(2/4) P(B)` と値として一致する(fermion、位数 2)。
  k = 1 は `δ(B/4)` で、類は自明(n = 1, 2, 3 で確認)。

- **U(1) から Z_N へ**:平坦な Z_N 場(整数への持ち上げ Ã)は、Villain 場 `(2πÃ/N, δÃ/N)` として曲率 0 の U(1) 場である
  (`FlatVillainField`)。この上で 3.9 の Chern–Simons のラグランジアンは `2π × (−k/2N²) δÃ∪Ã` になる(`ChernSimonsWeight`)。
  k が偶数なら K(Z_N, 1) の 3-cocycle で、その類は level −k/2(mod N)の Dijkgraaf–Witten の類、つまり `VecZN[N, −k/2]` の associator である
  (`ChernSimonsDijkgraafWittenQ`。N ≤ 5 で確認)。k が奇数なら cocycle にならない(spin 構造のない格子では level は偶数)。
  微分コホモロジー(Deligne)の作用が、平坦な場の上で群コホモロジー(K(A, n) の cocycle)に落ちることの、最初の例である。

n = 2、3 では、cocycle を cochain として bar 構成の (w, c) と比べること(Eilenberg–MacLane の比較写像)はまだしていない。
比べているのは類の位数である。

### 近似定理

May の近似定理は、連結な X に対して CₙX ≃ ΩⁿΣⁿX を主張する(recognition theorem の証明の中心)。
有理ホモロジーでは、左辺は H̃_*(X) の上の自由 Pₙ-代数(Pₙ = H_*(Eₙ)、F. Cohen)、右辺は 3.6 のループ空間の計算である。
`ApproximationTheoremQ[n, degrees, kmax]` は、球面の楔 X について、両辺の次元が arity(生成元の個数)ごと、
次数ごとに一致することを確かめる。左辺は 3.4 の指標から、右辺は Hilton–Milnor と Milnor–Moore から計算するので、
二つは独立な計算である。

- 球面 1 個:次数 d の類 x の上の自由 Pₙ-代数は、n+d が奇数なら S(x)、偶数なら S(x, [x, x])。
  括弧の次数は n−1 なので `[x, x]` は n+d が偶数のときだけ 0 でなく、次数は 2d+n−1。これは ΩⁿS^(n+d) の有理ホモロジーで、
  `[x, x]` は S^m(m = n+d が偶数)の Whitehead 積 `[ι, ι]`、つまり π_(2m−1)(S^m) ⊗ Q の生成元にあたる。
- n = 1, 2, 3、球面 1 個(d ≤ 4)と楔(次元 (1,1)、(1,2)、(2,3)、(1,1,1)、(1,2,3))で arity 4 まで確認している。
- n を取り違えると一致しない(次数 2 の類の上の自由 Gerstenhaber 代数は `[x, x]` を持つが、Ω³S⁵ にはない)。

写像 α: CₙX → ΩⁿΣⁿX そのものは 3.2 の `ApproximationMap` で、代数の射であることまで確かめている。
ここで確かめているのは次元の一致で、α が弱同値であること(両側 bar 構成を使う証明)は計算の外にある。

**1 点の上の自由 E₂-代数:braid 群**。X = S⁰(1 点と基点)では C₂X は無順序の配置の空間の和 ⊔ₖ C₂(k)/S_k で、
そのホモロジーは braid 群のホモロジーである(3.5)。

- 有理係数:Betti 数は 1, 1(k ≥ 2)。次数 0 の類 x の上の自由 Gerstenhaber 代数の arity k の部分
  `x^k`、`x^(k−2)[x, x]` と一致する(`FreeAlgebraDimensions[PoissonOperad[2], {0}, 4]`)。
- **Z₂ 係数**:`b_j(Br_k; Z₂)` は「k を 2 の冪 k − j 個の和に書く方法の数」に等しい(Fuks)。これは重み 2^i・次数 2^i − 1 の類
  x, Qx, QQx, … の上の多項式代数の次元である。有理係数では `[x, x]` の 2 乗は 0 だが、Z₂ 係数では括弧の代わりに
  Kudo–Araki(Dyer–Lashof)作用素 Q が現れ、Qx が `[x, x]` の位置(重み 2、次数 1)にいる。
- X = S^d(d ≥ 1)では、Z₂ 係数の Thom 同型で左辺は braid 群のホモロジーを次数 dk だけ上げたものになり、
  右辺は Ω²S^(d+2) の Z₂ 係数ホモロジー(3.6 の `KudoArakiDimensions`)である。
  `ApproximationTheoremModTwoQ[d, kmax]` が k ≤ kmax で両者の一致を確かめる(k ≤ 8、d ≤ 3)。
  Thom 同型と Kudo–Araki の定理は使っている事実で、ここで計算しているのは braid 群の側である。
- Z₃ 係数で最初の新しい類は H₄(Br₆) に現れる(Z₃)。

**統計**。同じ対象 k 個の上では、braid 群は H₁(Br_k) = Z を通して作用する:`BraidPathPhase` は spin × braid の指数和になる
(1 つの角度 θ を持つ anyon)。little 3-cubes と対称群では H₁ = Z₂ で、boson と fermion しかない。
前の小節の `SymmetricFromPathsQ` と同じことの、ホモロジーによる形である。

### little squares の道と braiding

E₂ 構造が braiding であることを、3.2 の little squares の道の側から読む。braided な圏は、各正方形に対象を載せた
配置の道に位相を与える。道の braid を `PathBraid` で読み、対象を左から並べた右寄せの積の上で `BraidPathPhase` を取る
(`PathBraidingPhase[cat, objects, path, {s0, s1}, steps]`)。反時計回りの入れ替え(左の a が下を通って右の b と入れ替わる)を
c(a, b) とする。これは平面の向きの選び方で、逆に取ると `c′(a, b) = −c(b, a)` の圏になる。

- 同じ対象 2 つの半回転は spin c(a, a)、1 周は相互 braiding である。semion で 1/4 と 1/2。toric code の e と m では、
  半回転は c(e, m) = 1/2 または c(m, e) = 0(どちらが左かで変わり、ゲージにも依る)、1 周は 1/2(不変量)。
- **operad の合成との両立が六角形である**:`SwapPath[2]` の 2 つの正方形に m₁ 個と m₂ 個の正方形の列を入れた道の位相は

  `−R + c(A, B) + R′`

  に等しい(`BlockBraidingQ[cat, {m1, m2}]`)。A, B は 2 つの列の積、c(A, B) は `SwapPath[2]` そのものに A, B を載せた位相、
  R, R′ は「列ごとにまとめた積」から右寄せの積への再結合の位相(入れ替えの前と後)。
  (m₁, m₂) = (1, 2) の等式は六角形 1 の式、(2, 1) は六角形 2 の式そのもので(差が、六角形の左辺 − 右辺の符号を変えたもの)、
  任意のデータで同値である(`HexagonFromPathsQ` ⇔ `HexagonQ`)。第 2 引数についてだけ加法的な braiding
  `c(a, b) = a²b/3`(Z₃)は (1, 2) だけを満たす。
- 長い列は六角形と五角形から従う。braided な圏で (2, 2)、(1, 3)、(3, 1)、(2, 3) を確かめている。
  `ZNAnyons[5, 3]` は六角形を満たし五角形を満たさないデータで、(1, 2) と (2, 1) は通り、(2, 2) で落ちる。
- **3 次元**:`SwapHomotopy` の両端の braid は `{1}` と `{−1}` で、位相は c(a, b) と −c(b, a)。little 3-cubes の道の
  ホモトピー類だけで位相が決まるには両者が等しいこと、つまり symmetric であることが要る
  (`SymmetricFromPathsQ` ⇔ `SymmetricBraidingQ`)。同じ対象の入れ替えは ±1(boson か fermion)になる。
  E₃ 以上が symmetric であること、3+1 次元に anyon がないことの、道による形である。

ここで計算しているのは、標本点から読んだ braid とその位相である。平面の配置の道のホモトピー類が braid で
分類されること(配置空間が K(π, 1) であること)は古典的な事実として使っていて、計算の外にある。
一般の道について位相が operad の合成と両立すること(coherence)も、確かめているのは上に挙げた列についてだけである。

## 7. 道筋と到達判定

| 段階 | 作るもの | 到達判定 | 状態 |
|---|---|---|---|
| 1 | 木、∘ᵢ、自由 operad、書き換えによる商、End、公理検証器。格子層(δ、∪、∪ᵢ) | As の成分が各 arity で 1 個。(C*, δ, ∪) が dg 結合代数。∪ᵢ が文献の成分公式と (A3) を満たす | 実装済み |
| 1b | 対称群作用と同変性、Com。線形結合と Lie(shuffle 木) | 同変性の検証が通る。Lie の成分次元が (n−1)! | 実装済み |
| 2 | little intervals、A∞ operad(自由 dg operad) | 公理が端点を記号にして通る。d²=0。associahedron の面の総数 1, 3, 11, 45。A∞ が As の分解 | 実装済み |
| 3 | little 2-cubes、Gerstenhaber operad、Pₙ | C_n(2) ≃ S^(n−1)。k 点成分の Poincaré 多項式が ∏(1+jt) | 実装済み(Pₙ の次元は arity 4 まで、参照実装で arity 5 まで。Betti 数との照合は、脈体で k = 2 と (n, k) = (2, 3)、Barratt–Eccles の段で (3, 3) まで、参照実装で (2, 4) と (4, 3) まで) |
| C | 点付き Eₙ モノイダル圏、coherence、braid 群の作用 | 五角形・六角形・分類の個数。coherence が長さ 6 まで | 実装済み(little squares の道の braid とその位相、六角形 = operad の合成との両立まで。parenthesized braids を operad として扱う一般の coherence は未着手) |
| G | 多重線形展開、ゲージ変分、作用、補正項の探索 | 5 節の恒等式が通る。Chern–Simons の ∪₁ の補正項が線形方程式の一意な解として出る | 実装済み(補正項の探索は、与えた候補の線形結合の中から。候補の自動生成は未着手) |
| V | Villain 形式の U(1) 場、Deligne–Beilinson 積、構成的な格子作用 | 積がゲージ同値類の上で定まる。BF と Chern–Simons が積から出る。平坦な Z_N 場の上で Dijkgraaf–Witten になる | 実装済み(対象、ゲージ変換、積、BF、Chern–Simons、Z_N への制限、積の可換性のホモトピー、θ 項と Witten 効果、differential cochain としての定式化、Chern–Simons の零モードの数、奇数 level の障害と三次元トーラスの上でそれを消す符号、その符号と境界条件の対応、Čech–de Rham の形の cocycle、背景場と 1-form 対称性のアノマリー、星積とその積分が level 2 の作用に等しいこと、符号の局所的な式(Grassmann 積分))。単体複体の上の符号は未着手 |
| 4 | E∞ operad(Barratt–Eccles、table reduction で surjection へ)、Eₙ フィルトレーション、cochain への作用 | eᵢ ↦ (1,2,1,2,…) の作用が ∪ᵢ を再現。三つの法則 (L)・(C)・(E)。Hirsch 公式のホモトピー | 実装済み(surjection operad の合成は未実装) |
| 5 | 単体的対象、bar 構成 B(Σⁿ, Cₙ, X) | 反復 bar 構成で作った BⁿA のホモトピー群が次数 n の A だけ。近似定理を有理 Poincaré 級数の一致で確認 | 離散群の場合を実装済み(BⁿA のホモロジーとホモトピー群、Eₙ 構造 = BⁿA の cocycle、格子の作用 = K(A, n) の cocycle)。ΩⁿY への little cubes の作用と近似写像 α は実装済み。近似定理は、球面の楔について有理 Poincaré 級数の一致を arity 4 まで確認済み。n = 2 の Z₂ 係数では球面 1 個について重み 8 まで(braid 群のホモロジーと Kudo–Araki の多項式代数)。両側 bar 構成 B(Σⁿ, Cₙ, X) そのものは未着手 |

次の候補(研究で使う計算機としての方向。cochain の式を入れると、ゲージ変分・補正項・アノマリーの類が出てくること):

- **補正項の探索の続き**:最初の版(与えた候補の中から係数を解く)は 3.8 節にある。次は、次数を指定して ∪ᵢ と E∞ の演算から候補を自動的に並べること、
  整数性(2π × 整数になるか)を条件に入れること、単体の上で解くこと
- 奇数 level の続き:障害が fermion の類 `(1/2) P(B)` であること、三次元トーラスの上でそれを消す 8 個の符号、境界条件との対応は 3.9 節にある。
  符号の局所的な式(Gu–Wen 型の Grassmann 積分)も 3.9 節にある。次は、単体複体(w₂ の代表)、奇数電荷の Wilson line、
  文献の Majorana の重みとの項ごとの照合。アノマリーの Čech の形(脈体の上の `m∪N + N∪m + δ̌m∪m`)も 3.9 節にある。
  次は、降下の像に限らない一般の Čech cocycle N の上で、それを消す符号を作ること
- Ikeda の格子 Deligne–Beilinson コホモロジー(arXiv:2601.15939)との比較の続き:Villain 場から Čech–de Rham の cocycle への写像と、
  星積の積分が level 2 の Chern–Simons の作用に等しいことは 3.9 節にある。次は、同論文の対称化した積と奇数 level の扱いを
  3.9 節の符号 z と比べること、逆向きの写像、framing のある Wilson loop の比較、`σ₁₂`・`σ₀₃` の符号を同論文の式と照合すること
- Z_N の背景場の続き:アノマリーの類と level kN² との関係は 3.9 節と 6 節にある。次は、背景場を入れた作用のゲージ変分(背景場のゲージ変換を含む)、
  ゲージ化した理論の線、`F_A∪₁F_B` のような格子に固有の項の系統的な扱い
- 混合アノマリー(K(A, n) の積の上の cocycle)と 2-group(`δB = β(A)`)
- 非可逆な対称性:fusion 圏の F・R 記号を厳密に扱う層

operad の側の候補:

- arity 4 のホモトピー:Cartan 公式、∪₁ の結合性のずれ、Steenrod 平方の関係式(Sq¹Sq^(2m) = Sq^(2m+1) だけは 5 節の式として入っている)
- Pontryagin 平方や高次 cup 積を含む作用のゲージ変分を、E∞ の演算で系統的に書くこと
- K(A, 2) の 4-cocycle と bar 構成 B² の cocycle (w, c) を cochain として比べること(Eilenberg–MacLane の比較写像)
- surjection operad の、単体的 cochain への作用(arity 3 以上。単体の上では Hirsch のホモトピーが 0 になること)
- 両側 bar 構成 B(Σⁿ, Cₙ, X) そのもの(単体的な対象として)。Dyer–Lashof 作用素を cochain や鎖の上の演算として実装すること(次元の一致は n = 2、Z₂ 係数で確認済み)。奇素数と n ≥ 3 の場合
- Koszul 双対の計算(関係式の直交補空間)と operad の bar 構成
- parenthesized braids の operad(E₂ の基本亜群)を作り、braided な圏がその代数であることを一般の arity で確かめること

## 8. 開発の進め方

- 各段階の到達判定を `Tests/*.wlt` の `VerificationTest` にする。
- `wolframscript -file Scripts/RunTests.wls` で全テストを回す。引数にファイル名(`Gauge` など)を
  渡すと、その層だけを回す。
- 符号や規約が関わる公式は、先に `reference/*.py` の参照実装で確かめてから
  Wolfram Language に移す。
- `Examples/*.nb` は入口のノートブック(`Operadica-Tour.nb` が全体の案内、`ZnAnyons.nb` が最小の例)。
  `wolframscript -file Scripts/RunExamples.wls` は、ノートブックの入力セルをカーネルだけで上から順に評価し、
  メッセージを出したセルを報告する。描画はしないので、図の見た目はノートブックを開いて確かめる。
- 役割分担:目的と方針は著者が決める。`Kernel/` と `Scripts/` のコード、テスト、Python の参照実装、文書は、
  Claude(Anthropic)が著者との対話の中で書く。Wolfram Language でのテストの実行とコミットは、著者の環境で
  Claude Code が行い、全テストが通ってからコミットする。著者は `Examples/` のノートブックで結果を確かめる。

## 9. 検証状況

### Wolfram Language での実行

- v0.2.0:`wolframscript -file Scripts/RunTests.wls` で 134/134 が通過(2026-11-22、利用者の環境)。
  単独の層のロードと、8 層すべてのロードも確認済み。
- v0.3.0:`wolframscript -file Scripts/RunTests.wls` で 156/156 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、10 層すべてのロードも確認済み。`Graded`、`AInfinity`、braid 群の作用を含む。
- v0.4.0:`wolframscript -file Scripts/RunTests.wls` で 188/188 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、11 層すべてのロードも確認済み。`Presented`、k 個の立方体の脈体、Hirsch 公式の欠損を含む。
- v0.5.0:`wolframscript -file Scripts/RunTests.wls` で 222/222 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、13 層すべてのロードも確認済み。`BarrattEccles`、`EInfinity`、`LocalOperation` を含む。
- v0.6.0:`wolframscript -file Scripts/RunTests.wls` で 258/258 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、14 層すべてのロードも確認済み。`BarConstruction`、`SmithInvariants`、`ChainHomology`、橋の delooping の主張を含む。
- v0.7.0:`wolframscript -file Scripts/RunTests.wls` で 281/281 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、15 層すべてのロードも確認済み。`Simplicial`、`IntegerKernel`、`EilenbergMacLaneCycles`、`CharacteristicCocycleQ`、`CharacteristicClassOrder`、橋の格子作用の主張を含む。
- v0.8.0:`wolframscript -file Scripts/RunTests.wls` で 288/288 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、15 層すべてのロードも確認済み。`OperadCharacter`、`FreeAlgebraDimensions`、`FreeLieDimensions`、`LoopSuspensionDimensions`、`ApproximationTheoremQ` を含む。
- v0.8.1:`wolframscript -file Scripts/RunTests.wls` で 289/289 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  `Scripts/RunExamples.wls` で `Examples/` の 2 つのノートブックの入力セルがメッセージなしで評価されることも確認済み。`ModularQ` の修正を含む。
- v0.9.0:`wolframscript -file Scripts/RunTests.wls` で 298/298 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、16 層すべてのロードも確認済み。`Loops`(little cubes のループ空間への作用、近似写像)を含む。
- v0.10.0:`wolframscript -file Scripts/RunTests.wls` で 308/308 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、16 層すべてのロードも確認済み。`PathBraid`、`SwapHomotopy`、`BraidPathPhase`、`PathBraidingPhase`、`BlockBraidingQ`、`HexagonFromPathsQ`、`SymmetricFromPathsQ` を含む。
- v0.11.0:`wolframscript -file Scripts/RunTests.wls` で 315/315 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、16 層すべてのロードも確認済み。`SteenrodSquare` の拡張、`SteenrodWeight`、`SteenrodBocksteinQ`、`SteenrodFermionQ` を含む。
- v0.12.0:`wolframscript -file Scripts/RunTests.wls` で 322/322 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、16 層すべてのロードも確認済み。`ModularBetti`、`BarrattEcclesOrbitHomology`、`BraidGroupHomology`、`BraidGroupCohomology`、`KudoArakiDimensions`、`ApproximationTheoremModTwoQ` を含む。
- v0.13.0:`wolframscript -file Scripts/RunTests.wls` で 327/327 が通過(2026-11-22、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`Villain` の層(`VillainField`、`DeligneProduct`、`VillainChernSimons`)と、橋の `FlatVillainField`、`ChernSimonsWeight`、`ChernSimonsDijkgraafWittenQ` を含む。
- v0.14.0:`wolframscript -file Scripts/RunTests.wls` で 331/331 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`DeligneSwapGauge`、`DeligneSwapDefect`、`VillainThetaTerm`、`VillainWittenTerm` を含む。
- v0.15.0:`wolframscript -file Scripts/RunTests.wls` で 336/336 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`DifferentialCochain`、`DifferentialCoboundary`、`DifferentialProduct`、`DifferentialSwapHomotopy`、`VillainDifferentialCochain`、`ChernSimonsZeroModeCount`、`StaggeredMomentumCount` を含む。
- v0.16.0:`wolframscript -file Scripts/RunTests.wls` で 337/337 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`ChernSimonsAnyons`、`ChernSimonsSpinSplitQ`、`ChernSimonsFermionCondensationQ` を含む。
- v0.17.0:`wolframscript -file Scripts/RunTests.wls` で 339/339 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`CochainLinearSolve` を含む。
- v0.18.0:`wolframscript -file Scripts/RunTests.wls` で 344/344 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`THooftFlux`、`ChernSimonsLargeGaugeAnomaly`、`SpinStructureSign` を含む。
- v0.19.0:`wolframscript -file Scripts/RunTests.wls` で 346/346 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`SpinStructureHolonomy` を含む。
- v0.20.0:`wolframscript -file Scripts/RunTests.wls` で 349/349 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`VillainPatchPrimitive`、`CechDeRhamConnection`、`CechDeRhamTransition`、`CechDeRhamChern`、`CechDeRhamCocycleQ`、`CechDeRhamChernNumbers`、`ChernSimonsOneFormAnomalyQ` を含む。
- v0.21.0:`wolframscript -file Scripts/RunTests.wls` で 352/352 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`CechDeRhamTriple`、`CechDeRhamFundamentalCycle`、`CechDeRhamStarIntegral`、`CechDeRhamGaugeTransform` を含む。
- v0.22.0:`wolframscript -file Scripts/RunTests.wls` で 353/353 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`GuWenGrassmannSign` を含む。
- v0.23.0:`wolframscript -file Scripts/RunTests.wls` で 354/354 が通過(2026-11-23、Wolfram Language 15.0.1、利用者の環境)。
  単独の層のロードと、17 層すべてのロードも確認済み。`CechDeRhamLargeGauge`、`CechDeRhamAnomaly` を含む。

### Python 参照実装(整数・有理数の厳密計算)

- `cubical_reference.py`:δ²=0、Leibniz 則、∪ の結合則、(A3)(d ≤ 4 の全次数)、
  Steenrod の規約、arXiv:2303.06160 付録 A の 1〜3 次元の成分公式、Hirsch 公式の欠損
- `gauge_reference.py`:5 節の恒等式、't Hooft flux で ΣP(B) = 2 Pf(z)、相互 braiding との一致
- `correction_reference.py`:係数の探索(乱数で作った cochain の上の線形方程式として。立方格子と単体)。(A3) が 3 つの ∪₁ の項の一意な結合であること
  (次数 (2, 2) まで)、Chern–Simons のゲージ変分から補正項 `−(k/2) a∪₁δn` と全微分の係数が一意に決まること、補正項の候補がないと解がないこと
- `encategory_reference.py`:標準例が公理を満たすこと、ゲージ不変性、符号を変えた六角形が
  落ちること、Z_N 上の構造の個数、coherence(長さ 6 まで)、
  U(1)_k の線の圏(k ≤ 9 の奇数で、`Z_2k^(2) = Z_k^(4) ⊠ sVec` と、level 4k の fermion の中心化部分であること)
- `operad_reference.py`:対称群の規約と同変性(End、語、little cubes)、
  分離被覆の脈体の Betti 数
- `ainfinity_reference.py`:Koszul 符号つきの公理、d²=0 になる符号則(双線形な 128 通りのうち 4 通り)、
  導分であること、associahedron の面の数・Euler 標数・ホモロジー(n ≤ 7)
- `presented_reference.py`:入れ替えと接ぎ木の整合、自由 operad での同変性、Com・Lie・Ass・Poisson の次元、
  P₂・P₃ の次数ごとの次元(arity 5 まで)、Koszul 符号を落とすと別の operad になること、正規形、
  商での operad の公理(符号つき)、語の operad との一致、射、C_n(k) の Betti 数、Koszul 双対の母関数
- `einfinity_reference.py`:Barratt–Eccles operad の公理(Koszul 符号つき)、F_nE(k) の Betti 数と Pₙ の次元の一致、
  table reduction が鎖写像であること、立方体(n ≤ 3)の上での (L)・(C)・(E)、格子上での三つの法則、
  arity 2 が ∪ᵢ であること(d ≤ 4)、Hirsch 公式(d ≤ 4)
- `bar_reference.py`:反復 bar 構成の d² = 0(レベル 4 まで)、積の結合則・次数付き可換性・導分であること、懸垂、
  K(Z_N, n) のホモロジー(n ≤ 3 で N ≤ 6、n = 4 で N ≤ 4)と Z₂ × Z₂、単体的な K(A, n) のホモトピー群とホモロジー、
  余境界が五角形・六角形・二重 braiding の式であること、cocycle ⇔ Eₙ 構造(102 個の圏)、cycle の上の値が spin と
  相互 braiding であること、構造の個数
- `simplicial_reference.py`:単体の上の δ² = 0、Leibniz 則、結合則、(A3)(次数 3 まで)、Hirsch 公式が厳密に成り立つこと、
  Pontryagin 平方の恒等式、整数核、`(k/N²) A∪δA` が Vec の associator であること(N ≤ 5)、
  `(p/2N) P(B)` が cocycle でその類の位数が spin の分母であること(N ≤ 4)、∪₁ の項が必要であること。実行に 30 秒ほどかかる
- `approximation_reference.py`:Com・Ass・Lie の指標、その自由代数(次数付きの Witt の公式)、Pₙ の指標(arity 4 まで)、
  自由 Pₙ-代数と H_*(ΩⁿΣⁿX; Q) の一致(n ≤ 3、球面 1 個と楔 7 通り、arity 4 まで)
- `loops_reference.py`:little cubes のループ空間への作用の単位・合成・同変性(n ≤ 3、乱数で作った有理数の配置)、
  近似写像が代数の射であること、n ≥ 2 で 2 つの立方体を入れ替える道
- `braiding_reference.py`:配置の道の braid(`SwapPath` の半分が σ、全部が σ²。乱歩 300 本で指数和 = 半回転の数。
  3 個で指数和 = 巻き数の和の 2 倍と、標本の細かさに依らないこと)、列を入れた道が block の braid であること、
  その位相が `−R + c(A, B) + R′` であること(列は (2, 3) まで)、(1, 2) と (2, 1) が六角形 1 と 2 に同値であること(乱数のデータ 400 個)、
  pure braid の位相のゲージ不変性、`SwapHomotopy` が端点を固定したホモトピーであること(33 × 33 の格子点で配置が正しいこと)
- `steenrod_reference.py`:Sq⁰ の値が 2 乗であること、`δ(Sq^k x)` の式(単体で p ≤ 3、立方格子で 4 次元まで)、
  K(Z₂, n)(n ≤ 3)で `Sq¹B ≡ δB/2`(mod 2)、`(1/2) Sq^k B` が cocycle であることと類の位数
  ((n, k) = (1, 1)、(2, 1)、(3, 1) で 1、(2, 2)、(3, 2) で 2)、Z₃ では `(1/2) B∪B` が cocycle でないこと
- `braidgroup_reference.py`:Fuks–Vainshtein の複体の d² = 0(k ≤ 10)、H_*(Br_k; Z)(k ≤ 8)とコホモロジーとの整合(普遍係数定理)、
  Z₂ 係数の Betti 数 = 2 の冪への分割の数、Barratt–Eccles operad の軌道の複体(k = 2 で実射影空間、F₂ で braid 群(k = 3, 4)、
  F₃E(3) と operad 全体で H₁ = Z₂)
- `villain_reference.py`:Deligne–Beilinson 積の曲率とゲージ変換・大きいゲージ変換の恒等式(立方格子と単体、次数 (1,1)、(1,2)、(2,1)、(2,2)。
  2π を 3 通りの整数に置き換えて確認)、modified Villain の Chern–Simons が積の半分と ∪₁ の補正であること、
  平坦な Z_N 場の上で偶数 level の Chern–Simons が level −k/2 の Dijkgraaf–Witten の類になること(N ≤ 5)、奇数 level では cocycle にならないこと、
  積の次数付き可換性(ゲージ変換 λ、m と `F_A∪₁F_B` の項。この項を落とすと成り立たないこと)、
  θ 項の分解と Witten 項のゲージ変分(p = 1 は立方格子と単体、p = 2 は単体)、四次元トーラスの位相電荷が Pfaffian であること、
  differential cochain の d² = 0・Leibniz 則・結合則・可換性のホモトピー(立方格子は 5 次元まで、単体は次数 (3, 3) まで)、
  Villain 場が differential cochain であること、`Σ a∪δa` の零モードの数(三次元トーラス 10 通り)、大きいゲージ変換の合成則
- `oddlevel_reference.py`:奇数 level の恒等式(inflow、アノマリー、降下、cocycle、Gu–Wen の形、level 4k。立方格子と単体)、
  三次元トーラス 4 通りの上で、アノマリーの和が奇数になりうること、flux の読み出し、8 個の符号のそれぞれが条件 (i)・(ii) を満たすこと、
  線形方程式の解の取り方に依らないこと、2 つの符号の比が平坦な 1-cochain で書けること、まっすぐな flux の管の符号、
  類の代表の上の二次の精密化がちょうど 8 個であること、座標平面の中の flux では `m∪n + n∪m + δm∪m = 0` であることと、
  その上で符号が平面の中の類だけで決まること(三次元トーラス 3 通り、8 個の符号、3 つの方向、平面のすべての位置)
- `cech_reference.py`:平坦な Villain 場から作った Čech–de Rham の 3 つ組の条件(立方体の上の原始関数、遷移関数、三重の重なりの整数、
  Čech cocycle 条件。3×3×3 と 3×4×5)、Chern 数が flux に等しいこと、monopole があると原始関数が作れないこと、
  背景場を入れた `Q(n + B/N)` の展開と交差項の恒等式、inflow の恒等式、level kN² との関係(立方格子と単体)、
  平坦な Z_N 場の上で `(K/2N²) Q(B)` が `(p/2N) P(B)` に 1 を法として等しいこと
- `star_reference.py`:星積の積分に使う鎖を錐で作り、3 つの条件を順序のついた鎖の上で確かめること(消える項を落とす前と後。3×3×3 と 3×4×5)、
  閉じた式との一致、ξ による不変性と整数 m による整数の変化(どちらの因子でも)、平坦な Villain 場の 3 つ組の上で 4 つの寄与が
  `Σ(a/τ)∪(F_B/τ)`、0、`−Σ n∪(b/τ)`、0 に等式として等しいこと、大きなゲージ変換での変化が `−Σ q(m, n)` で奇数になりうること、
  2 つの因子の入れ替えでの差が `−Σ(F_A/τ)∪₁(F_B/τ) + Σ n∪₁n′` であること(3×3×3、3×3×4、3×4×5 を 3 通りずつ)、
  同じゲージ変換を両方の因子に施したときの変化が `−⟨m∪N + N∪m + δ̌m∪m, σ₀₃⟩` であること、大きいゲージ変換が 3 つ組のゲージ変換で
  あることと、そのときの対が `Σ q(m, n)` であること(同じ格子)
- `grassmann_reference.py`:Grassmann 積分の符号。6 つの面の並べ方 720 通りのうち (ii) を満たすのが巡回的な 12 通りだけであること
  (3×3×3 と 3×4×4)、`∪₁` が結ぶ面の対、まっすぐな管で −1(7 通りの大きさ)、link の境界で +1、2 本の link で −1、
  (i)・(ii)、8 個の符号が境界条件つきの積分に一致すること(3×3×3、3×3×4、4×4×4)
