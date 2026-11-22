# Operadica 設計文書

最終更新: 2026-11-22(v0.8.0)

## 1. 目的

operad の標準的な理論を、Mathematica 上で実際に計算しながら理解し、使えるようにする。
最初の非自明な到達点を May の recognition theorem に置く。

「証明する」のではなく、**定理の主張と証明の部品をすべて実行可能にする**ことを目標にする。
一般の弱同値の主張そのものは Mathematica の外(人間の証明、必要なら Lean)に残る。

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
| operad | ``Operadica`Graded` `` | Trees | 線形結合、Koszul 符号つきの次数付き operad、微分、鎖複体の整係数ホモロジー |
| operad | ``Operadica`AInfinity` `` | Trees, Graded, Rewriting | A∞ operad、associahedron |
| operad | ``Operadica`Presented` `` | Graded | 生成元と関係式による対称 operad:Com、Lie、Ass、Poisson、Gerstenhaber、Pₙ |
| operad | ``Operadica`BarrattEccles` `` | Graded | Barratt–Eccles operad(E∞)、Eₙ の段、区間と立方体への作用 |
| operad | ``Operadica`BarConstruction` `` | Graded | delooping:アーベル群の反復 bar 構成、Eilenberg–MacLane 空間 K(A, n) |
| カテゴリ | ``Operadica`EnCategories` `` | なし | 点付き Eₙ モノイダル圏:五角形、六角形、spin |
| 格子ゲージ理論 | ``Operadica`Lattice` `` | なし | cochain、δ、∪、∪ᵢ、局所的な多重線形演算 |
| 格子ゲージ理論 | ``Operadica`Gauge` `` | Lattice | 多重線形展開、ゲージ変分、作用 |
| 格子ゲージ理論 | ``Operadica`Simplicial` `` | Lattice | 同じ cochain の式を単体の上で評価する:Steenrod の ∪ᵢ |
| 橋 | ``Operadica`EInfinity` `` | Graded, BarrattEccles, Lattice | 格子 cochain への E∞ operad の作用:∪ᵢ とその間のホモトピー |
| 橋 | ``Operadica`Bridge` `` | Trees, Operads, LittleCubes, Graded, Presented, BarrattEccles, BarConstruction, Lattice, Simplicial, EnCategories | 層をつなぐ主張 |

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

braid 群の作用:右に寄せた積 `a₁(a₂(a₃…))` の上で、生成元 σᵢ の位相は
`−w(a,b,x) + c(a,b) + w(b,a,x)`(x は後ろに続く対象の積。最後の 2 つでは `c(a,b)` だけ)。
σᵢ を 2 回かけると相互 braiding になる。点付きの圏では braid 関係式は五角形から従い、
六角形は「積を越える braiding は braiding の合成である」という主張にあたる。`BraidPhase`、`BraidRelationQ`。

標準例:`ZNAnyons[n, p]`(`w = p·a·carry(b,c)/2`、`c = p·a·b/(2n)`。n が偶数か p が偶数のとき成立)、
`VecZN[n, k]`(H³(Z_n, U(1)) の代表)、`DoubleZN[n]`、`ToricCode[]`、`Semion[]`、`SuperVec[]`。

### 3.8 cochain

- `Cochain[p, f]`:cell `LCell[x, s]` 上の値が `f[x, s]` の p-cochain。
  `f` が未定義のシンボルなら「一般の cochain」になる。
- `Coboundary[c]`、`Cup[a, b]`(組み込みの `Cup`。`a ⌣ b` と入力できる)、
  `HigherCup[i][a, b]`、和、スカラー倍。
- `CochainValue[c, x, s]` で cell 上の値に展開する。
- `CochainExpand` で多重線形に展開し(δ² = 0 を使う)、`GaugeVariation` でゲージ変分を出し、
  `TotalDerivativeQ` で全微分であることを確かめる。
- `LocalOperation[f, d][a1, …, ar]`:局所的な多重線形演算。n 次元の cell 上の値は、`f[n]` の項
  `{係数, {row₁, …, row_r}}` についての `係数 × ∏ⱼ aⱼ(x + shiftⱼ; Sⱼ)` の和(row の読み方は 3.5 と同じ)。
  ∪ も ∪ᵢ もこの形で、6 節の E∞ operad の作用はこれで表す。
- **単体の上でも同じ式を評価できる**(``Operadica`Simplicial` ``)。`SimplexValue[c, {v0, …, vn}]` は、
  cochain の式 c を頂点が順序づけられた単体の上で評価する。一般の cochain `Cochain[p, f]` の値は `f[{v0, …, vp}]`。
  `SimplexCochainZeroQ`、`SimplexCochainEqualQ` は恒等式を単体 {0, …, p} の上の 1 回の評価で確かめる
  (頂点に順序のついたすべての単体複体での証明)。規約は 5 節。

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
| 近似定理 CₙX ≃ ΩⁿΣⁿX(X 連結)の、有理 Poincaré 級数での確認:H̃_*(X) の上の自由 Pₙ-代数 = H_*(ΩⁿΣⁿX; Q) | `ApproximationTheoremQ` |
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

で、3-cell 上では 9 項。5 節の欠損の式はこの特別な場合である。
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

n = 2 では、cocycle を cochain として bar 構成の (w, c) と比べること(Eilenberg–MacLane の比較写像)はまだしていない。
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

確かめているのは次元の一致で、写像 CₙX → ΩⁿΣⁿX そのもの(両側 bar 構成)は作っていない。

## 7. 道筋と到達判定

| 段階 | 作るもの | 到達判定 | 状態 |
|---|---|---|---|
| 1 | 木、∘ᵢ、自由 operad、書き換えによる商、End、公理検証器。格子層(δ、∪、∪ᵢ) | As の成分が各 arity で 1 個。(C*, δ, ∪) が dg 結合代数。∪ᵢ が文献の成分公式と (A3) を満たす | 実装済み |
| 1b | 対称群作用と同変性、Com。線形結合と Lie(shuffle 木) | 同変性の検証が通る。Lie の成分次元が (n−1)! | 実装済み |
| 2 | little intervals、A∞ operad(自由 dg operad) | 公理が端点を記号にして通る。d²=0。associahedron の面の総数 1, 3, 11, 45。A∞ が As の分解 | 実装済み |
| 3 | little 2-cubes、Gerstenhaber operad、Pₙ | C_n(2) ≃ S^(n−1)。k 点成分の Poincaré 多項式が ∏(1+jt) | 実装済み(Pₙ の次元は arity 4 まで、参照実装で arity 5 まで。Betti 数との照合は、脈体で k = 2 と (n, k) = (2, 3)、Barratt–Eccles の段で (3, 3) まで、参照実装で (2, 4) と (4, 3) まで) |
| C | 点付き Eₙ モノイダル圏、coherence、braid 群の作用 | 五角形・六角形・分類の個数。coherence が長さ 6 まで | 実装済み(parenthesized braids の coherence は未着手) |
| G | 多重線形展開、ゲージ変分、作用 | 5 節の恒等式が通る | 実装済み |
| 4 | E∞ operad(Barratt–Eccles、table reduction で surjection へ)、Eₙ フィルトレーション、cochain への作用 | eᵢ ↦ (1,2,1,2,…) の作用が ∪ᵢ を再現。三つの法則 (L)・(C)・(E)。Hirsch 公式のホモトピー | 実装済み(surjection operad の合成は未実装) |
| 5 | 単体的対象、bar 構成 B(Σⁿ, Cₙ, X) | 反復 bar 構成で作った BⁿA のホモトピー群が次数 n の A だけ。近似定理を有理 Poincaré 級数の一致で確認 | 離散群の場合を実装済み(BⁿA のホモロジーとホモトピー群、Eₙ 構造 = BⁿA の cocycle、格子の作用 = K(A, n) の cocycle)。近似定理は、球面の楔について有理 Poincaré 級数の一致を arity 4 まで確認済み。両側 bar 構成 B(Σⁿ, Cₙ, X) そのものは未着手 |

次の候補:

- arity 4 のホモトピー:Cartan 公式、∪₁ の結合性のずれ、Steenrod 平方の関係式
- Pontryagin 平方や高次 cup 積を含む作用のゲージ変分を、E∞ の演算で系統的に書くこと
- K(A, 2) の 4-cocycle と bar 構成 B² の cocycle (w, c) を cochain として比べること(Eilenberg–MacLane の比較写像)
- surjection operad の、単体的 cochain への作用(arity 3 以上。単体の上では Hirsch のホモトピーが 0 になること)
- 両側 bar 構成 B(Σⁿ, Cₙ, X) そのもの(単体的な対象として)。Dyer–Lashof 作用素(mod p の近似定理)
- Koszul 双対の計算(関係式の直交補空間)と operad の bar 構成

## 8. 開発の進め方

- 各段階の到達判定を `Tests/*.wlt` の `VerificationTest` にする。
- `wolframscript -file Scripts/RunTests.wls` で全テストを回す。引数にファイル名(`Gauge` など)を
  渡すと、その層だけを回す。
- 符号や規約が関わる公式は、先に `reference/*.py` の参照実装で確かめてから
  Wolfram Language に移す。

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

### Python 参照実装(整数・有理数の厳密計算)

- `cubical_reference.py`:δ²=0、Leibniz 則、∪ の結合則、(A3)(d ≤ 4 の全次数)、
  Steenrod の規約、arXiv:2303.06160 付録 A の 1〜3 次元の成分公式、Hirsch 公式の欠損
- `gauge_reference.py`:5 節の恒等式、't Hooft flux で ΣP(B) = 2 Pf(z)、相互 braiding との一致
- `encategory_reference.py`:標準例が公理を満たすこと、ゲージ不変性、符号を変えた六角形が
  落ちること、Z_N 上の構造の個数、coherence(長さ 6 まで)
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
