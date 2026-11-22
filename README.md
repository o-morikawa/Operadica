# Operadica

Operads, E_n-monoidal categories and lattice cochains, computed in the Wolfram Language.

A Mathematica expression is a tree, and grafting trees is operadic composition.
Operadica uses that to make the standard theory of operads something you can
run, with two neighbours that physicists meet in practice: pointed braided
categories (anyons, higher-form symmetries) and cochains on the hypercubic
lattice (coboundary, cup product, Steenrod's higher cup products, and the
E-infinity structure they are part of). The aim is a path from the definitions
to May's recognition theorem in which every statement along the way is checked
by computation.

The design and the roadmap are in [docs/DESIGN.ja.md](docs/DESIGN.ja.md) (Japanese).

## Layers

Each layer is its own context and can be loaded alone. Dependencies are loaded
automatically; the lattice and category layers do not need the operad layer.

| Layer | Context | Depends on | What it gives |
|---|---|---|---|
| operad | ``Operadica`Trees` `` | | planar trees, grafting, enumeration |
| operad | ``Operadica`Operads` `` | Trees | operad objects, axiom and equivariance verifiers, algebras |
| operad | ``Operadica`Rewriting` `` | Trees | quotient operads, normal forms, confluence |
| operad | ``Operadica`LittleCubes` `` | | the little n-cubes operads (E_n), nerves and Betti numbers of their spaces |
| operad | ``Operadica`Graded` `` | Trees | linear combinations, graded operads with Koszul signs, differentials |
| operad | ``Operadica`AInfinity` `` | Trees, Graded, Rewriting | the A-infinity operad, associahedra |
| operad | ``Operadica`Presented` `` | Graded | symmetric operads by generators and relations: Com, Lie, Ass, Poisson, Gerstenhaber, P_n |
| operad | ``Operadica`BarrattEccles` `` | Graded | the Barratt-Eccles operad (E-infinity), its E_n stages, its action on cubes |
| category | ``Operadica`EnCategories` `` | | pointed E_n-monoidal categories: pentagon, hexagons, spins |
| lattice gauge theory | ``Operadica`Lattice` `` | | cochains, coboundary, cup and higher cup products, local multilinear operations |
| lattice gauge theory | ``Operadica`Gauge` `` | Lattice | multilinear expansion, gauge variations, actions |
| bridge | ``Operadica`EInfinity` `` | Graded, BarrattEccles, Lattice | the E-infinity operad acts on lattice cochains: higher cup products and the homotopies between them |
| bridge | ``Operadica`Bridge` `` | Trees, Operads, LittleCubes, Presented, BarrattEccles, Lattice, EnCategories | statements connecting the layers |

```wolfram
PacletDirectoryLoad["/path/to/Operadica"];

Needs["Operadica`"]            (* everything *)
Needs["Operadica`Gauge`"]      (* only the lattice gauge theory layer *)
```

Requires Wolfram Language 12.1 or later.

## Which layer do I need?

- **I work with lattice gauge fields and want to check an identity or a gauge
  variation.** Load ``Operadica`Gauge` ``. You never have to touch an operad.
- **I want to check F- and R-symbols of an abelian anyon theory, or see what
  E_1, E_2, E_3 mean concretely.** Load ``Operadica`EnCategories` ``.
- **I want to learn operads by computing.** Load ``Operadica`Operads` ``,
  ``Operadica`Rewriting` ``, ``Operadica`LittleCubes` `` and ``Operadica`AInfinity` ``.
- **I want to know whether an identity follows from the Jacobi and Leibniz
  rules, with the right signs for a bracket of odd degree.** Load
  ``Operadica`Presented` `` and ask `OperadZeroQ`.
- **I use higher cup products and want the identities beyond arity two: what
  replaces the Leibniz rule for the cup-1 product, and where the correction
  terms come from.** Load ``Operadica`EInfinity` ``.
- **I want to see why these are the same subject.** Load ``Operadica`Bridge` ``.

## Lattice gauge theory layer

Cochain expressions stay symbolic until they are evaluated on a cell, and
values use lattice index notation: `f[x, {mu, nu}]` is the component of `f` on
the plaquette at `x` in the `(mu, nu)` plane.

```wolfram
a = Cochain[1, A];  b = Cochain[1, B];

CochainValue[Coboundary[a], {x1, x2}, {1, 2}]
(* A[{x1, x2}, {1}] + A[{1 + x1, x2}, {2}] - A[{x1, 1 + x2}, {1}] - A[{x1, x2}, {2}] *)

CochainValue[Cup[a, b], {x1, x2}, {1, 2}]
(* A[{x1, x2}, {1}] B[{1 + x1, x2}, {2}] - A[{x1, x2}, {2}] B[{x1, 1 + x2}, {1}] *)
```

`Cup` is the built-in symbol, so `a \[Cup] b` works as input.

**Identities are proved, not sampled.** With generic cochains (`Cochain[p, f]`
with `f` an undefined symbol) the values are independent variables. The
operations are local and translation invariant, so a check at one symbolic
base point holds on every hypercubic lattice of that dimension and over every
commutative coefficient ring.

```wolfram
(* Leibniz rule in four dimensions *)
CochainEqualQ[
  Coboundary[Cup[a, b]],
  Cup[Coboundary[a], b] - Cup[a, Coboundary[b]],
  4]
```

**Gauge variations.** Replace a field, expand by multilinearity, and verify a
proposed total derivative:

```wolfram
lam = Cochain[0, L];
var = GaugeVariation[Cup[a, Coboundary[b]], a -> a + Coboundary[lam]]
(* Cup[Coboundary[lam], Coboundary[b]] *)
TotalDerivativeQ[var, Cup[lam, Coboundary[b]], 3]      (* True *)
```

The 0-form gauge invariance of the modified Villain Chern-Simons action of
[arXiv:2303.06160](https://arxiv.org/abs/2303.06160), eq. (17), for every
Villain field `n`:

```wolfram
a = Cochain[1, A];  n = Cochain[2, NN];  phi = Cochain[0, F];  lam = Cochain[0, L];
TotalDerivativeQ[
  ModifiedVillainCS[k][a + Coboundary[lam], n, phi - k lam] - ModifiedVillainCS[k][a, n, phi],
  (k/(4 Pi)) Cup[lam, Coboundary[a]] - k Cup[lam, n] + (k/2) HigherCup[1][Coboundary[lam], n],
  3]                                                    (* True *)
```

The Pontryagin square on a 't Hooft flux background of the four-torus:

```wolfram
z = {{0, 1, 0, 0}, {-1, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, -1, 0}};
flux = THooftFluxCochain[z, {4, 4, 4, 4}];
ZNFlatQ[flux, {4, 4, 4, 4}, 4]                          (* True *)
CochainIntegrate[PontryaginSquare[flux], {4, 4, 4, 4}]  (* 2 = 2 Pf(z) *)
```

Conventions:

- `(dc)(x; m1 < ... < mk) = Sum_j (-1)^(j-1) [ c(x + e_mj; without mj) - c(x; without mj) ]`
- `(a u b)(x; s) = Sum_{A, B} sign(A, B) a(x; A) b(x + e_A; B)` over splittings of `s` into
  a front part `A` of size `p` and the rest `B`.
- `HigherCup[i]` follows eq. (A3) of Jacobson and Sulejmanpasic,
  [arXiv:2303.06160](https://arxiv.org/abs/2303.06160), and reproduces the component
  formulas of its Appendix A, which follow Chen and Tata,
  [arXiv:2106.05274](https://arxiv.org/abs/2106.05274).
- Steenrod's original convention differs by `SteenrodCupSign[p, q, i] = (-1)^(i (p + q + 1))`.
- `PontryaginSquare[b] = Cup[b, b] - HigherCup[1][b, Coboundary[b]]`.

## Category layer

A pointed E_n-monoidal category has the elements of a finite abelian group as
its simple objects. For ordinary categories E_1 means monoidal, E_2 braided,
and E_n for n >= 3 symmetric. The data are an associator `w[a, b, c]` and a
braiding `c[a, b]`; phases are rational numbers modulo 1 (`x` stands for
`exp(2 Pi I x)`), so every check is exact. Group elements are lists.

```wolfram
cat = ZNAnyons[4, 1];                 (* Z_4^(1) *)
{PentagonQ[cat], HexagonQ[cat]}       (* {True, True} *)
EnLevel[cat]                          (* 2: braided, not symmetric *)
SpinTable[cat]                        (* spins 0, 1/8, 1/2, 1/8 *)
ModularQ[cat]                         (* True *)

EnLevel /@ {VecZN[3, 1], Semion[], ToricCode[], SuperVec[]}
(* {1, 2, 2, Infinity} *)

MutualBraiding[ToricCode[], {1, 0}, {0, 1}]   (* 1/2: e and m braid with -1 *)

(* the braid group acts on a product of objects *)
BraidPhase[cat, {{1}, {3}, {2}}, 1]           (* 7/8: exchange the first two *)
BraidRelationQ[cat, 3]                        (* True *)
```

Your own data go into `PointedCategory[{N1, ..., Nr}, w, c]`. Gauge
transformations (`GaugeTransformCategory`) change the data and leave
`PentagonQ`, `HexagonQ`, `SpinTable` and `MutualBraiding` unchanged.

Conventions: abelian 3-cocycles of Eilenberg and MacLane in the form used by
Joyal and Street; the equations are written out at the top of
`Kernel/EnCategories.wl`.

## Operad layer

```wolfram
(* a tree is OpLeaf or h[t1, ..., tk]; partial composition is grafting *)
OpCompose[m[OpLeaf, OpLeaf], 1, m[OpLeaf, OpLeaf]]
(* m[m[OpLeaf, OpLeaf], OpLeaf] *)

(* a basis of the free operad: Catalan numbers *)
Table[Length[OpPlanarTrees[{m -> 2}, n]], {n, 1, 7}]
(* {1, 1, 2, 5, 14, 42, 132} *)

(* every operad has the same interface, so the same verifiers check them all *)
OperadAxiomCheck[WordOperad[], 4]
OperadEquivarianceCheck[WordOperad[], 4]

(* associativity as a rewriting rule; the quotient is the operad As *)
as = QuotientOperad[{m -> 2}, {m[m[a_, b_], c_] :> m[a, m[b, c]]}];
OpLocallyConfluentQ[{m -> 2}, as["Rules"], 5]
Table[Length[as["Elements"][n]], {n, 1, 6}]      (* {1, 1, 1, 1, 1, 1} *)

(* the little 2-cubes operad: the axioms are identities in the endpoints *)
OperadAxiomCheck[LittleCubesOperad[2], 3]["Strength"]
OperadEquivariantQ[LittleCubesOperad[2], 3]

(* C_n(2) is a sphere of dimension n - 1 *)
Table[SimplicialBetti[SeparationNerve[n]], {n, 1, 3}]
(* {{2}, {1, 1}, {1, 0, 1}} *)

(* the A-infinity operad: generators OpM[n] of degree n - 2 *)
AInfinityDifferential[3]
(* -LBasis[OpM[2][OpM[2][OpLeaf, OpLeaf], OpLeaf]] + LBasis[OpM[2][OpLeaf, OpM[2][OpLeaf, OpLeaf]]] *)
StasheffRelationsQ[7]                      (* True: d d = 0 *)
DGOperadCheck[AInfinityOperad[4], 4]       (* axioms with Koszul signs, d d = 0, Leibniz *)

(* its arity-n part is the chain complex of the associahedron K_n *)
AssociahedronFVector[5]                    (* {14, 21, 9, 1} *)
AssociahedronBetti[5]                      (* {1, 0, 0, 0}: A-infinity resolves As *)
AssociahedronGraph[4]                      (* the pentagon *)
```

An operad is an `Association` with the keys `"Elements"`, `"Compose"`,
`"Unit"`, and optionally `"Equal"` and `"Action"`. To check your own, build
such an Association and pass it to `OperadAxiomCheck`.

### Operads by generators and relations

``Operadica`Presented` `` computes symmetric operads with binary generators and
quadratic relations by linear algebra. A labelled tree has the numbers of its
inputs at the leaves: `OpLie[OpLie[1, 2], 3]` is `[[x1, x2], x3]`.

```wolfram
lie = LieOperad[];  pois = PoissonOperad[];  ger = GerstenhaberOperad[];

Table[OperadDimension[lie, n], {n, 1, 5}]         (* {1, 1, 2, 6, 24} = (n - 1)! *)

(* the Jacobi relation as a rewriting rule: normal forms are left-normed brackets *)
OperadReduce[lie, LBasis[OpLie[1, OpLie[2, 3]]]]
(* LBasis[OpLie[OpLie[1, 2], 3]] - LBasis[OpLie[OpLie[1, 3], 2]] *)

(* in the Gerstenhaber operad the bracket has degree 1; the Koszul rule changes the sign *)
OperadReduce[ger, LBasis[OpLie[1, OpLie[2, 3]]]]
(* -LBasis[OpLie[OpLie[1, 2], 3]] - LBasis[OpLie[OpLie[1, 3], 2]] *)

(* does an identity follow from the relations?  {ab, cd} = a{b,c}d + ac{b,d} + b{a,c}d + bc{a,d} *)
OperadZeroQ[pois,
  LBasis[OpLie[OpCom[1, 2], OpCom[3, 4]]] -
    LBasis[OpCom[OpCom[1, OpLie[2, 3]], 4]] - LBasis[OpCom[OpCom[1, 3], OpLie[2, 4]]] -
    LBasis[OpCom[OpCom[2, OpLie[1, 3]], 4]] - LBasis[OpCom[OpCom[2, 3], OpLie[1, 4]]]]   (* True *)

(* P_n = H_*(E_n): dimensions by degree are the Betti numbers of configuration spaces *)
OperadDimensionsByDegree[ger, 4]                  (* <|0 -> 1, 1 -> 6, 2 -> 11, 3 -> 6|> *)
OperadDimensionsByDegree[PoissonOperad[3], 4]     (* <|0 -> 1, 2 -> 6, 4 -> 11, 6 -> 6|> *)

(* the quotient is an operad: axioms with Koszul signs *)
DGOperadQ[ger, 4]                                 (* True *)

(* the commutator of an associative product is a Lie bracket *)
OperadMorphismQ[lie, PresentedAssociativeOperad[],
  {OpLie -> LBasis[OpAss[1, 2]] - LBasis[OpAssOp[1, 2]]}]                                (* True *)
```

`OperadZeroQ` and `OperadReduce` decide by row reduction of the ideal of
relations in the arity of the expression, so a `True` is a proof that the
identity follows from the relations.

Your own operad goes into `PresentedOperad[{g1 -> s1, ...}, {relations}]`,
where `s` is `1` (symmetric), `-1` (antisymmetric) or the name of the opposite
operation, and `{s, d}` gives the generator the degree `d`.

Conventions: a tree is the tensor product of its vertices in preorder, as in
``Operadica`Graded` ``. Swapping the children of a vertex costs the sign of the
generator times `(-1)^(|a| |b|)`; plugging `x` into the input `k` of `t` costs
`(-1)^(|x| D)` with `D` the degree of the vertices of `t` after `k`; the
symmetric group acts by `(t.s)(x1, ..., xn) = t(x_{s^-1(1)}, ...)`. In
`PoissonOperad[n]` the bracket has degree `n - 1` and sign `(-1)^n` under the
swap, and the relations have the same form for every `n`: associativity,
`[[1,2],3] + [[2,3],1] + [[3,1],2] = 0`, and `[12, 3] = 1 [2,3] + [1,3] 2`.

Every check reports its strength in the key `"Strength"`:

| Strength | Meaning |
|---|---|
| by construction | free operads: grafting is associative; the test guards the code |
| exhaustive | all listed elements up to a total arity: a proof in that range |
| symbolic identity | generic elements with symbolic parameters: a proof for all parameters |
| confluence | critical pairs up to an arity: normal forms in all arities |
| supplied or sampled | only the elements you passed in |

### The Barratt-Eccles operad

``Operadica`BarrattEccles` `` is an E-infinity operad small enough to compute
with. An element of arity `r` and degree `d` is a list of `d + 1` words
(permutations of `1..r` written as lists), consecutive words different. In
degree 0 it is the operad of words.

```wolfram
e1 = HigherCupElement[1]                       (* {{1, 2}, {2, 1}} *)
BarrattEcclesDifferential[e1]                  (* LBasis[{{2, 1}}] - LBasis[{{1, 2}}] *)
BarrattEcclesCompose[e1, 1, {{1, 2}}]          (* LBasis[{{1, 2, 3}, {3, 1, 2}}] *)
DGOperadQ[BarrattEcclesOperad[1], 3]           (* True: a differential graded operad *)

(* Berger's filtration: the stage F_n is an E_n operad *)
BarrattEcclesLevel /@ {HigherCupElement[0], e1, HigherCupElement[2]}     (* {1, 2, 3} *)

(* its homology is P_n: three points in the plane, and in three dimensions *)
BarrattEcclesBetti[2, 3]                       (* {1, 3, 2, 0} *)
BarrattEcclesBetti[3, 3]                       (* {1, 0, 3, 0, 2, 0, 0} *)

(* the table reduction of Berger and Fresse, to the surjection operad *)
TableReduction[HigherCupElement[3]]            (* LBasis[{1, 2, 1, 2, 1}] *)
```

## E-infinity structure of lattice cochains

``Operadica`EInfinity` `` lets the Barratt-Eccles operad act on lattice cochains.
`EInfinityOperation[s][a1, ..., ar]` is a cochain expression like `Cup` and
`HigherCup`: it can be evaluated on a cell, differentiated and compared.

```wolfram
a = Cochain[1, A];  b = Cochain[1, B];  c = Cochain[2, W];

(* arity 2 is the higher cup product, up to a sign *)
CochainEqualQ[EInfinityOperation[{{1, 2}}][a, b], Cup[a, b], 3]                    (* True *)
EInfinityHigherCupQ[1, {1, 2}, 3]     (* theta(e_1)(a, b) = (-1)^(p+q) a u_1 b: True *)

(* the cup-1 product is not a derivation of the cup product ... *)
CochainEqualQ[HigherCup[1][Cup[a, b], c],
  Cup[a, HigherCup[1][b, c]] - Cup[HigherCup[1][a, c], b], 3]                       (* False *)

(* ... but it is one up to an explicit homotopy of arity 3 *)
HirschFormulaQ[{1, 1, 2}, 3]                                                        (* True *)
CochainValue[HirschHomotopy[a, b, c], {x1, x2}, {1, 2}]
(* -A[{x1, x2}, {2}] B[{x1, 1 + x2}, {1}] W[{x1, x2}, {1, 2}] *)
```

The three laws that make the cochains an algebra over the operad, for an
element `s` of degree `m` and cochains of degrees `p1, ..., pr`:

- (L) `d theta_s(a) = (-1)^m [ Sum_j (-1)^(p1+..+p(j-1)) theta_s(.., d aj, ..) - theta_(ds)(a) ]`
- (C) `theta_(s o_j t)(a) = (-1)^(|s||t| + |t|(p1+..+p(j-1))) theta_s(a1, .., theta_t(aj, ..), ..)`
- (E) `theta_(s.p)(a1, .., ar) = sign theta_s(a_(p^-1(1)), .., a_(p^-1(r)))`

They are checked on generic cochains by `EInfinityLeibnizQ`,
`EInfinityCompositionQ` and `EInfinityEquivarianceQ`. The Hirsch formula up to
homotopy, with `H = HirschHomotopy`, reads

```
(a u b) u_1 c - a u (b u_1 c) - (-1)^(q(r-1)) (a u_1 c) u b
   = (-1)^(p+q+r) [ dH(a,b,c) - H(da,b,c) - (-1)^p H(a,db,c) - (-1)^(p+q) H(a,b,dc) ]
```

`H` comes from the element `HirschElement[] = {{1,2,3},{1,3,2},{3,1,2}}`, which
lies in the E_2 stage: the Leibniz rule of the Gerstenhaber operad holds on
cochains up to this homotopy. Any other local multilinear formula can be
entered as `LocalOperation[f, d][a1, ..., ar]`.

Conventions: the action on the interval is the table reduction of Berger and
Fresse; cubes are tensor powers of the interval and the operad acts through
its diagonal. The cup-i products obtained in this way are those of the
lattice layer (Chen-Tata, arXiv:2106.05274, in the convention of
arXiv:2303.06160).

## Bridge

```wolfram
CupAlgebraOverAsQ[3]       (* cochains with the cup product are an As-algebra *)
EInfinityArityTwoQ[3]      (* higher cup products = arity-2 part of an E-infinity action *)

(* the pentagon equation is the confluence of associativity with phases *)
MacLaneCoherenceQ[Semion[], 5]

(* a 4d weight on a 't Hooft flux background = mutual braiding of the fluxes *)
PontryaginFluxPhase[4, 1, z, {2, 2, 2, 2}] == FluxBraidingPhase[ZNAnyons[4, 1], z]

(* the homology of the little cubes is P_n: three little squares have Betti
   numbers 1, 3, 2, the Gerstenhaber operad in arity 3 *)
SimplicialBetti[FacetNerve[SeparationNerve[2, 3]]]    (* {1, 3, 2, 0, 0, 0} *)
LittleCubesHomologyQ[2, 3]                            (* True *)
```

`SeparationNerve[n, k]` is the nerve of a cover of the space of `k` little
`n`-cubes by convex sets (for each pair of cubes, an axis along which one lies
before the other), so it has the homotopy type of that space. The nerve grows
quickly: `k = 2` for any `n`, and `(n, k) = (1, 3), (1, 4), (2, 3)` are feasible.
The stages of the Barratt-Eccles operad reach further:
`BarrattEcclesHomologyQ[3, 3]` compares `1, 0, 3, 0, 2` with `PoissonOperad[3]`.

The last two lines are small instances of the recognition principle: an
invertible E_n structure on a group is the same thing as a cocycle on its
n-fold delooping, which on the lattice is a higher-form gauge field.

## Tests

```
wolframscript -file Scripts/RunTests.wls            # everything
wolframscript -file Scripts/RunTests.wls Gauge      # one test file
```

The runner first checks that a single layer loads on its own, then runs
`Tests/*.wlt` and prints the failing test IDs with actual and expected output.

Formulas that involve signs or conventions are fixed first by independent
pure-Python references, which use exact integer and rational arithmetic:

```
python3 reference/cubical_reference.py      # d, cup, higher cup products
python3 reference/gauge_reference.py        # gauge-variation identities
python3 reference/encategory_reference.py   # pentagon, hexagons, coherence
python3 reference/operad_reference.py       # symmetric groups, little cubes
python3 reference/ainfinity_reference.py    # Koszul signs, A-infinity, associahedra
python3 reference/presented_reference.py    # Lie, Poisson, Gerstenhaber; little-cubes homology
python3 reference/einfinity_reference.py    # Barratt-Eccles operad and its action on cochains
```

## Layout

```
PacletInfo.wl
Kernel/Operadica.wl       loads all layers
Kernel/Trees.wl           operad layer
Kernel/Operads.wl
Kernel/Rewriting.wl
Kernel/LittleCubes.wl
Kernel/Graded.wl
Kernel/AInfinity.wl
Kernel/Presented.wl
Kernel/BarrattEccles.wl
Kernel/EnCategories.wl    category layer
Kernel/Lattice.wl         lattice gauge theory layer
Kernel/Gauge.wl
Kernel/EInfinity.wl       bridge
Kernel/Bridge.wl
Tests/*.wlt               one VerificationTest file per layer file
Scripts/RunTests.wls      test runner
reference/*.py            Python references for the conventions
docs/DESIGN.ja.md         design and roadmap
```
