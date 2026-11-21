# Operadica 設計文書

最終更新: 2026-11-22(v0.2.0)

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
| operad | ``Operadica`LittleCubes` `` | なし | little n-cubes operad(Eₙ)、arity 2 のホモトピー型 |
| カテゴリ | ``Operadica`EnCategories` `` | なし | 点付き Eₙ モノイダル圏:五角形、六角形、spin |
| 格子ゲージ理論 | ``Operadica`Lattice` `` | なし | cochain、δ、∪、∪ᵢ |
| 格子ゲージ理論 | ``Operadica`Gauge` `` | Lattice | 多重線形展開、ゲージ変分、作用 |
| 橋 | ``Operadica`Bridge` `` | Trees, Operads, Lattice, EnCategories | 層をつなぐ主張 |

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

### 3.3 点付き Eₙ モノイダル圏

単純対象は有限アーベル群の元(整数のリスト)。データは associator `w[a, b, c]` と
braiding `c[a, b]`。通常の圏では E₁ = モノイダル、E₂ = braided、E₃ 以上 = symmetric。

規約は Eilenberg–MacLane のアーベル 3-コサイクル(Joyal–Street の形):

- 五角形 `w(b,c,d) − w(a+b,c,d) + w(a,b+c,d) − w(a,b,c+d) + w(a,b,c) = 0`
- 六角形1 `w(b,c,a) + c(a,b+c) + w(a,b,c) = c(a,c) + w(b,a,c) + c(a,b)`
- 六角形2 `−w(c,a,b) + c(a+b,c) − w(a,b,c) = c(a,c) − w(a,c,b) + c(b,c)`
- ゲージ変換 `w' = w + δf`、`c'(a,b) = c(a,b) + f(b,a) − f(a,b)`
- 不変量:spin `q(a) = c(a,a)`、相互 braiding `b(a,b) = c(a,b) + c(b,a)`

標準例:`ZNAnyons[n, p]`(`w = p·a·carry(b,c)/2`、`c = p·a·b/(2n)`。n が偶数か p が偶数のとき成立)、
`VecZN[n, k]`(H³(Z_n, U(1)) の代表)、`DoubleZN[n]`、`ToricCode[]`、`Semion[]`、`SuperVec[]`。

### 3.4 cochain

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

## 6. 橋

| 主張 | 関数 |
|---|---|
| (C*, ∪) は結合 operad As の代数 | `CupAlgebraOverAsQ` |
| ∪ᵢ は E∞ operad の arity 2 部分 W の作用。∪ᵢ は E_(i+1) の段にある | `EInfinityArityTwoQ` |
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

## 7. 道筋と到達判定

| 段階 | 作るもの | 到達判定 | 状態 |
|---|---|---|---|
| 1 | 木、∘ᵢ、自由 operad、書き換えによる商、End、公理検証器。格子層(δ、∪、∪ᵢ) | As の成分が各 arity で 1 個。(C*, δ, ∪) が dg 結合代数。∪ᵢ が文献の成分公式と (A3) を満たす | 実装済み |
| 1b | 対称群作用と同変性、Com。線形結合と Lie(shuffle 木) | 同変性の検証が通る。Lie の成分次元が (n−1)! | 前半を実装済み、Lie は未着手 |
| 2 | little intervals、A∞ operad(自由 dg operad) | 公理が端点を記号にして通る。d²=0。associahedron の面の総数 1, 3, 11, 45 | little cubes と面の数え上げは実装済み、dg は未着手 |
| 3 | little 2-cubes、Gerstenhaber operad | C_n(2) ≃ S^(n−1)。k 点成分の Poincaré 多項式が ∏(1+jt) | arity 2 は実装済み |
| C | 点付き Eₙ モノイダル圏、coherence | 五角形・六角形・分類の個数。coherence が長さ 6 まで | 実装済み |
| G | 多重線形展開、ゲージ変分、作用 | 5 節の恒等式が通る | 実装済み |
| 4 | surjection operad、Eₙ フィルトレーション、cochain への作用 | (1,2,1,2,…) の作用が ∪ᵢ を再現 | arity 2 のみ実装済み |
| 5 | 単体的対象、bar 構成 B(Σⁿ, Cₙ, X) | 反復 bar 構成で作った BⁿA のホモトピー群が次数 n の A だけ。近似定理を有理 Poincaré 級数の一致で確認 | 未着手 |

## 8. 開発の進め方

- 各段階の到達判定を `Tests/*.wlt` の `VerificationTest` にする。
- `wolframscript -file Scripts/RunTests.wls` で全テストを回す。引数にファイル名(`Gauge` など)を
  渡すと、その層だけを回す。
- 符号や規約が関わる公式は、先に `reference/*.py` の参照実装で確かめてから
  Wolfram Language に移す。

## 9. v0.2.0 時点の検証状況

- Python 参照実装(整数・有理数の厳密計算)で確認済み:
  - `cubical_reference.py`:δ²=0、Leibniz 則、∪ の結合則、(A3)(d ≤ 4 の全次数)、
    Steenrod の規約、arXiv:2303.06160 付録 A の 1〜3 次元の成分公式
  - `gauge_reference.py`:5 節の恒等式、't Hooft flux で ΣP(B) = 2 Pf(z)、相互 braiding との一致
  - `encategory_reference.py`:標準例が公理を満たすこと、ゲージ不変性、符号を変えた六角形が
    落ちること、Z_N 上の構造の個数、coherence(長さ 6 まで)
  - `operad_reference.py`:対称群の規約と同変性(End、語、little cubes)、
    分離被覆の脈体の Betti 数
- Wolfram Language のコードとテストは、この文書を書いた時点では未実行。
