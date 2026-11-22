# Operadica 設計文書

最終更新: 2026-11-22(v0.4.0)

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
| operad | ``Operadica`Graded` `` | Trees | 線形結合、Koszul 符号つきの次数付き operad、微分 |
| operad | ``Operadica`AInfinity` `` | Trees, Graded, Rewriting | A∞ operad、associahedron |
| operad | ``Operadica`Presented` `` | Graded | 生成元と関係式による対称 operad:Com、Lie、Ass、Poisson、Gerstenhaber、Pₙ |
| カテゴリ | ``Operadica`EnCategories` `` | なし | 点付き Eₙ モノイダル圏:五角形、六角形、spin |
| 格子ゲージ理論 | ``Operadica`Lattice` `` | なし | cochain、δ、∪、∪ᵢ |
| 格子ゲージ理論 | ``Operadica`Gauge` `` | Lattice | 多重線形展開、ゲージ変分、作用 |
| 橋 | ``Operadica`Bridge` `` | Trees, Operads, LittleCubes, Presented, Lattice, EnCategories | 層をつなぐ主張 |

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

### 3.5 点付き Eₙ モノイダル圏

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

### 3.6 cochain

- `Cochain[p, f]`:cell `LCell[x, s]` 上の値が `f[x, s]` の p-cochain。
  `f` が未定義のシンボルなら「一般の cochain」になる。
- `Coboundary[c]`、`Cup[a, b]`(組み込みの `Cup`。`a ⌣ b` と入力できる)、
  `HigherCup[i][a, b]`、和、スカラー倍。
- `CochainValue[c, x, s]` で cell 上の値に展開する。
- `CochainExpand` で多重線形に展開し(δ² = 0 を使う)、`GaugeVariation` でゲージ変分を出し、
  `TotalDerivativeQ` で全微分であることを確かめる。

## 4. 自動検証の4つの強さ

検証結果には、どの強さで通ったかを `"Strength"` に残す。

1. **構成による保証**:自由 operad は接ぎ木なので公理が構造的に成り立つ。
   テストは実装の誤り検出用。
2. **有限全数検査**:有限な operad・代数・圏は、全組合せを調べる。その範囲では証明である。
   `OperadAxiomCheck`、`PentagonQ`、`HexagonQ`。
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

## 6. 橋

| 主張 | 関数 |
|---|---|
| (C*, ∪) は結合 operad As の代数 | `CupAlgebraOverAsQ` |
| ∪ᵢ は E∞ operad の arity 2 部分 W の作用。∪ᵢ は E_(i+1) の段にある | `EInfinityArityTwoQ` |
| C_n(k) の Betti 数 = Pₙ の arity k の成分の次数ごとの次元(H_*(Eₙ) = Pₙ の、次元での確認) | `LittleCubesHomologyQ` |
| 五角形方程式 ⇔ 結合則の書き換えの、位相つきの合流性(Mac Lane の coherence) | `MacLaneCoherenceQ` |
| 四次元トーラス上の 't Hooft flux での重み `(p/2N)ΣP(B)` = flux の相互 braiding | `PontryaginFluxPhase`, `FluxBraidingPhase` |

recognition theorem の物理的な中身:p-form 対称性の欠陥は余次元 p+1 で、横方向 ℝ^(p+1) での
融合が E_(p+1) 構造を持つ。可逆なら Ω^(p+1)B^(p+1)A と同値で、背景場は格子上の
(p+1)-cocycle になる。群 A 上の Eₙ 構造は H^(n+2)(K(A, n); U(1)) で分類される。
Z_N では n = 2 が N·gcd(2,N) 個(二次形式)、n = 3 が gcd(2,N) 個で、
`Tests/EnCategories.wlt` がこの個数を数えている。

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

## 7. 道筋と到達判定

| 段階 | 作るもの | 到達判定 | 状態 |
|---|---|---|---|
| 1 | 木、∘ᵢ、自由 operad、書き換えによる商、End、公理検証器。格子層(δ、∪、∪ᵢ) | As の成分が各 arity で 1 個。(C*, δ, ∪) が dg 結合代数。∪ᵢ が文献の成分公式と (A3) を満たす | 実装済み |
| 1b | 対称群作用と同変性、Com。線形結合と Lie(shuffle 木) | 同変性の検証が通る。Lie の成分次元が (n−1)! | 実装済み |
| 2 | little intervals、A∞ operad(自由 dg operad) | 公理が端点を記号にして通る。d²=0。associahedron の面の総数 1, 3, 11, 45。A∞ が As の分解 | 実装済み |
| 3 | little 2-cubes、Gerstenhaber operad、Pₙ | C_n(2) ≃ S^(n−1)。k 点成分の Poincaré 多項式が ∏(1+jt) | 実装済み(Pₙ の次元は arity 4 まで、参照実装で arity 5 まで。C_n(k) の Betti 数との照合は k = 2 と (n, k) = (2, 3) まで) |
| C | 点付き Eₙ モノイダル圏、coherence、braid 群の作用 | 五角形・六角形・分類の個数。coherence が長さ 6 まで | 実装済み(parenthesized braids の coherence は未着手) |
| G | 多重線形展開、ゲージ変分、作用 | 5 節の恒等式が通る | 実装済み |
| 4 | surjection operad、Eₙ フィルトレーション、cochain への作用 | (1,2,1,2,…) の作用が ∪ᵢ を再現 | arity 2 のみ実装済み |
| 5 | 単体的対象、bar 構成 B(Σⁿ, Cₙ, X) | 反復 bar 構成で作った BⁿA のホモトピー群が次数 n の A だけ。近似定理を有理 Poincaré 級数の一致で確認 | 未着手 |

次の候補:

- n ≥ 3 や k ≥ 4 の配置空間の Betti 数(脈体では大きすぎる。より小さい胞体モデルが要る)
- Koszul 双対の計算(関係式の直交補空間)と bar 構成
- 段階 4 の arity 3。5 節の Hirsch 公式の欠損は、arity 3 の演算で書けるはずのものである

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
