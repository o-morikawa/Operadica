# Operadica

Operads, E_n-monoidal categories and lattice cochains, computed in the Wolfram Language.

A Mathematica expression is a tree, and grafting trees is operadic composition.
Operadica uses that to make the standard theory of operads something you can
run, with two neighbours that physicists meet in practice: pointed braided
categories (anyons, higher-form symmetries) and cochains on the hypercubic
lattice (coboundary, cup product, Steenrod's higher cup products). The aim is
a path from the definitions to May's recognition theorem in which every
statement along the way is checked by computation.

The design and the roadmap are in [docs/DESIGN.ja.md](docs/DESIGN.ja.md) (Japanese).

## Layers

Each layer is its own context and can be loaded alone. Dependencies are loaded
automatically; the lattice and category layers do not need the operad layer.

| Layer | Context | Depends on | What it gives |
|---|---|---|---|
| operad | ``Operadica`Trees` `` | | planar trees, grafting, enumeration |
| operad | ``Operadica`Operads` `` | Trees | operad objects, axiom and equivariance verifiers, algebras |
| operad | ``Operadica`Rewriting` `` | Trees | quotient operads, normal forms, confluence |
| operad | ``Operadica`LittleCubes` `` | | the little n-cubes operads (E_n), arity-two homotopy type |
| category | ``Operadica`EnCategories` `` | | pointed E_n-monoidal categories: pentagon, hexagons, spins |
| lattice gauge theory | ``Operadica`Lattice` `` | | cochains, coboundary, cup and higher cup products |
| lattice gauge theory | ``Operadica`Gauge` `` | Lattice | multilinear expansion, gauge variations, actions |
| bridge | ``Operadica`Bridge` `` | Trees, Operads, Lattice, EnCategories | statements connecting the layers |

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
  ``Operadica`Rewriting` `` and ``Operadica`LittleCubes` ``.
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
```

An operad is an `Association` with the keys `"Elements"`, `"Compose"`,
`"Unit"`, and optionally `"Equal"` and `"Action"`. To check your own, build
such an Association and pass it to `OperadAxiomCheck`.

Every check reports its strength in the key `"Strength"`:

| Strength | Meaning |
|---|---|
| by construction | free operads: grafting is associative; the test guards the code |
| exhaustive | all listed elements up to a total arity: a proof in that range |
| symbolic identity | generic elements with symbolic parameters: a proof for all parameters |
| confluence | critical pairs up to an arity: normal forms in all arities |
| supplied or sampled | only the elements you passed in |

## Bridge

```wolfram
CupAlgebraOverAsQ[3]       (* cochains with the cup product are an As-algebra *)
EInfinityArityTwoQ[3]      (* higher cup products = arity-2 part of an E-infinity action *)

(* the pentagon equation is the confluence of associativity with phases *)
MacLaneCoherenceQ[Semion[], 5]

(* a 4d weight on a 't Hooft flux background = mutual braiding of the fluxes *)
PontryaginFluxPhase[4, 1, z, {2, 2, 2, 2}] == FluxBraidingPhase[ZNAnyons[4, 1], z]
```

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
```

## Layout

```
PacletInfo.wl
Kernel/Operadica.wl       loads all layers
Kernel/Trees.wl           operad layer
Kernel/Operads.wl
Kernel/Rewriting.wl
Kernel/LittleCubes.wl
Kernel/EnCategories.wl    category layer
Kernel/Lattice.wl         lattice gauge theory layer
Kernel/Gauge.wl
Kernel/Bridge.wl          bridge
Tests/*.wlt               one VerificationTest file per layer file
Scripts/RunTests.wls      test runner
reference/*.py            Python references for the conventions
docs/DESIGN.ja.md         design and roadmap
```
