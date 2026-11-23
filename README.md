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

A second direction is lattice gauge theory built constructively on cochains:
actions are written with the operations of an E-infinity operad (cup-i products
and the homotopies between them), checked symbolically, and read as cocycles on
K(A, n).
This part is work in progress; so far it reproduces known constructions
(Pontryagin square, modified Villain Chern-Simons, Dijkgraaf-Witten).

The design and the roadmap are in [docs/DESIGN.ja.md](docs/DESIGN.ja.md) (Japanese).

## Start here

Open [Examples/Operadica-Tour.nb](Examples/Operadica-Tour.nb) in Mathematica and
evaluate it from the top. It loads the package from the folder above it and
walks through the three parts with pictures: operads by computation (trees,
associahedra, rewriting, little squares), categories by running them (the
pentagon with phases, braiding tables), and lattice computations (the terms of
the cup and higher cup products as cell pictures, gauge variations, 't Hooft
flux). [Examples/ZnAnyons.nb](Examples/ZnAnyons.nb) is a minimal example: for
which `n` and `p` the anyons `Z_n^(p)` satisfy the hexagon equations.

## Layers

Each layer is its own context and can be loaded alone. Dependencies are loaded
automatically; the lattice and category layers do not need the operad layer.

| Layer | Context | Depends on | What it gives |
|---|---|---|---|
| operad | ``Operadica`Trees` `` | | planar trees, grafting, enumeration |
| operad | ``Operadica`Operads` `` | Trees | operad objects, axiom and equivariance verifiers, algebras |
| operad | ``Operadica`Rewriting` `` | Trees | quotient operads, normal forms, confluence |
| operad | ``Operadica`LittleCubes` `` | | the little n-cubes operads (E_n), nerves and Betti numbers of their spaces |
| operad | ``Operadica`Loops` `` | LittleCubes | the action of the little n-cubes on n-fold loop spaces, the approximation map, braids of paths of configurations |
| operad | ``Operadica`Graded` `` | Trees | linear combinations, graded operads with Koszul signs, differentials, integral homology of chain complexes |
| operad | ``Operadica`AInfinity` `` | Trees, Graded, Rewriting | the A-infinity operad, associahedra |
| operad | ``Operadica`Presented` `` | Graded | symmetric operads by generators and relations: Com, Lie, Ass, Poisson, Gerstenhaber, P_n |
| operad | ``Operadica`BarrattEccles` `` | Graded | the Barratt-Eccles operad (E-infinity), its E_n stages, its action on cubes, unordered configurations and the homology of braid groups |
| operad | ``Operadica`BarConstruction` `` | Graded | delooping: the iterated bar construction of an abelian group, the Eilenberg-MacLane spaces K(A, n) |
| category | ``Operadica`EnCategories` `` | | pointed E_n-monoidal categories: pentagon, hexagons, spins |
| lattice gauge theory | ``Operadica`Lattice` `` | | cochains, coboundary, cup and higher cup products, local multilinear operations |
| lattice gauge theory | ``Operadica`Gauge` `` | Lattice | multilinear expansion, gauge variations, actions |
| lattice gauge theory | ``Operadica`Simplicial` `` | Lattice | the same cochain expressions on simplices: Steenrod's cup-i products |
| lattice gauge theory | ``Operadica`Villain` `` | Lattice | U(1) gauge fields in the modified Villain form, differential cochains, the Deligne-Beilinson product, BF and Chern-Simons actions, the theta term, the anomaly at odd level |
| bridge | ``Operadica`EInfinity` `` | Graded, BarrattEccles, Lattice | the E-infinity operad acts on lattice cochains: higher cup products and the homotopies between them |
| bridge | ``Operadica`Bridge` `` | Trees, Operads, LittleCubes, Loops, Graded, Presented, BarrattEccles, BarConstruction, Lattice, Simplicial, Villain, EnCategories | statements connecting the layers |

```wolfram
PacletDirectoryLoad["/path/to/Operadica"];

Needs["Operadica`"]            (* everything *)
Needs["Operadica`Gauge`"]      (* only the lattice gauge theory layer *)
```

Requires Wolfram Language 12.1 or later.

## Which layer do I need?

- **I work with lattice gauge fields and want to check an identity or a gauge
  variation.** Load ``Operadica`Gauge` ``. You never have to touch an operad.
- **My lattice is a triangulation, not a hypercubic lattice.** Load
  ``Operadica`Simplicial` `` and evaluate the same expressions with
  `SimplexValue` and `SimplexCochainEqualQ`.
- **I want to build a lattice action for U(1) gauge fields from cochains (BF,
  Chern-Simons) and see how it transforms.** Load ``Operadica`Villain` ``.
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
- **I want the homology of an Eilenberg-MacLane space K(A, n), or the reason
  why Z_N carries N gcd(2, N) braided structures and gcd(2, N) symmetric ones.**
  Load ``Operadica`BarConstruction` ``, and ``Operadica`Bridge` `` for the
  comparison with categories.
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

The cup-1 term of that Lagrangian can be found instead of checked.
`CochainLinearSolve` looks for the coefficients that make a cochain expression
a combination of given candidates. Take the Lagrangian without its cup-1 term;
its gauge variation is a unique combination of the variation of a candidate
correction term and of three coboundaries:

```wolfram
bare[u_, ph_] := ModifiedVillainCS[k][u, n, ph] + (k/2) HigherCup[1][u, Coboundary[n]];

CochainLinearSolve[
  bare[a + Coboundary[lam], phi - k lam] - bare[a, phi],
  {HigherCup[1][Coboundary[lam], Coboundary[n]],       (* the variation of a cup_1 dn *)
   Coboundary[Cup[lam, Coboundary[a]]],
   Coboundary[Cup[lam, n]],
   Coboundary[HigherCup[1][Coboundary[lam], n]]},
  3]
(* <|"Solvable" -> True, "Unique" -> True, "Coefficients" -> {k/2, k/(4 Pi), -k, k/2}|> *)
```

The first coefficient says that the correction term is `-(k/2) a cup_1 dn`.
Without that candidate there is no solution.

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

### Cochains on simplices

``Operadica`Simplicial` `` evaluates the same expressions on an ordered simplex
`{v0, ..., vn}`; a generic cochain `Cochain[p, f]` has the value
`f[{v0, ..., vp}]`. `HigherCup[i]` is then Steenrod's cup-i product, with the
sign for which the identity relating cup-i and cup-(i+1) (arXiv:2303.06160,
(A3)) has the same form on both lattices. Identities that follow from it, such
as the gauge variation of the Pontryagin square, hold on both.

```wolfram
Needs["Operadica`Simplicial`"]

a = Cochain[1, fa]; b = Cochain[1, fb]; c = Cochain[1, fc]; u = Cochain[2, fu];

SimplexValue[Coboundary[a], {0, 1, 2}]       (* fa[{1, 2}] - fa[{0, 2}] + fa[{0, 1}] *)
SimplexValue[HigherCup[1][u, a], {0, 1, 2}]  (* fu[{0, 1, 2}] fa[{0, 1}] + fu[{0, 1, 2}] fa[{1, 2}] *)

(* an identity is proved by one evaluation on the simplex {0, ..., p} *)
SimplexCochainEqualQ[Coboundary[Cup[a, u]], Cup[Coboundary[a], u] - Cup[a, Coboundary[u]]]   (* True *)

(* the Hirsch formula: exact on simplices, a defect on plaquettes *)
hirsch = HigherCup[1][Cup[a, b], c] - Cup[a, HigherCup[1][b, c]] - Cup[HigherCup[1][a, c], b];
{SimplexCochainZeroQ[hirsch], CochainZeroQ[hirsch, 2]}     (* {True, False} *)

(* Steenrod squares, on simplices and on cubes: Sq^k x = x cup_(p-k) x *)
c3 = Cochain[3, fc];
SteenrodSquare[2][c3]                                      (* HigherCup[1][c3, c3] *)
SimplexCochainEqualQ[Coboundary[SteenrodSquare[2][c3]],
  -2 Cup[c3, c3] + HigherCup[1][Coboundary[c3], c3] - HigherCup[1][c3, Coboundary[c3]]]   (* True *)
```

If the coboundary of `x` is even, the right-hand side is even: `Sq^k x` is a
cocycle modulo 2. For even `k` the first term is twice `Sq^(k+1) x`, so that
`Sq^(k+1)` is the Bockstein of `Sq^k`.

### U(1) gauge fields: the Villain form and the Deligne-Beilinson product

``Operadica`Villain` `` treats abelian gauge fields as differential cohomology
on the lattice. A field of degree `p` is a pair `(a, n)`: a real `p`-cochain,
the connection, and an integer `(p+1)`-cochain, the flux, with the curvature
`F = da - 2 Pi n`. Actions are built with the Deligne-Beilinson product
`A * B = (a cup F_B / 2 Pi + (-1)^p n cup b, -n cup n')`.

```wolfram
A = VillainField[Cochain[1, fa], Cochain[2, fn]];
B = VillainField[Cochain[1, fb], Cochain[2, fn2]];
m = Cochain[1, fm];

(* large gauge transformations do not change the curvature *)
CochainEqualQ[VillainCurvature[VillainLargeGaugeTransform[A, m]], VillainCurvature[A], 2]   (* True *)

(* the BF Lagrangian is the connection of A * B *)
VillainConnection[DeligneProduct[A, B]]

(* a large gauge transformation of A changes it by 2 Pi times an integer cochain
   and a total derivative: the level of BF theory is an integer *)
CochainEqualQ[
  VillainConnection[DeligneProduct[VillainLargeGaugeTransform[A, m], B]],
  VillainConnection[DeligneProduct[A, B]] - 2 Pi Cup[m, VillainFlux[B]] - Coboundary[Cup[m, VillainConnection[B]]],
  3]                                                                                        (* True *)

(* Chern-Simons theory is half of A * A with a cup-1 correction: eq. (17) of arXiv:2303.06160 *)
phi = Cochain[0, fp];
CochainEqualQ[VillainChernSimons[k][A, phi], ModifiedVillainCS[k][Cochain[1, fa], Cochain[2, fn], phi], 3]   (* True *)
```

The identities hold for generic cochains, on cubes and on simplices, with the
terms proportional to `dn` written out; for flat fluxes the product is defined
on gauge classes.

The product is graded commutative up to a gauge transformation, and the
homotopy is the cup-1 product. On the lattice one more term appears, the gauge
invariant `F_A cup_1 F_B / 2 Pi`, which has no counterpart for differential
forms and vanishes if one of the two fields has no curvature:

```wolfram
{lam, mm} = DeligneSwapGauge[A, B];

(* the two BF Lagrangians, a db and b da; the last line holds the terms with dn *)
CochainEqualQ[
  VillainConnection[DeligneProduct[A, B]] - VillainConnection[DeligneProduct[B, A]],
  Coboundary[lam] + 2 Pi mm + DeligneSwapDefect[A, B] -
    (HigherCup[1][Cochain[1, fa], Coboundary[Cochain[2, fn2]]] - HigherCup[1][Coboundary[Cochain[2, fn]], Cochain[1, fb]]),
  3]                                                                                        (* True *)
```

The theta term `(theta / 8 Pi^2) F cup F` is `theta / 4 Pi` times the curvature
of `A * A`, plus a coupling of the connection to the monopole current `dn`. That
coupling transforms like an electric charge `theta / 2 Pi` on the monopole (the
Witten effect). On the four-torus the topological charge is the Pfaffian of the
flux, for any connection:

```wolfram
CochainEqualQ[
  VillainThetaTerm[theta][A],
  (theta / (4 Pi)) VillainCurvature[DeligneProduct[A, A]] + VillainWittenTerm[theta][A],
  4]                                                                                        (* True *)

z = {{0, 1, 2, -1}, {-1, 0, 3, 5}, {-2, -3, 0, 7}, {1, -5, -7, 0}};
dims = {2, 2, 2, 2};
T = VillainField[(1/3) RandomCochain[1, dims], THooftFluxCochain[z, dims]];
Expand[CochainIntegrate[VillainThetaTerm[1][T], dims]]                                      (* -6 *)
```

A Villain field is a differential cochain: the differential cocycle of Hopkins
and Singer with the differential form replaced by a cochain. A differential
cochain of degree `k` is a triple `(c, h, w)` of an integer `k`-cochain, a real
`(k-1)`-cochain and a real `k`-cochain, with `d(c, h, w) = (dc, w - c - dh, dw)`,
and the field `(a, n)` is `(-n, a / 2 Pi, F / 2 Pi)`. The definition of the
curvature is the vanishing of the middle component of `d`, `dn = 0` is the
cocycle condition, gauge transformations add coboundaries, and the
Deligne-Beilinson product is the product of differential cochains, which is
associative and satisfies the Leibniz rule:

```wolfram
x = VillainDifferentialCochain[A];
y = VillainDifferentialCochain[B];

(* d(x . y) = dx . y + (-1)^k x . dy, here k = 2 *)
DifferentialCochainEqualQ[
  DifferentialCoboundary[DifferentialProduct[x, y]],
  DifferentialComponents[DifferentialProduct[DifferentialCoboundary[x], y]] +
    DifferentialComponents[DifferentialProduct[x, DifferentialCoboundary[y]]],
  5]                                                                                        (* True *)

(* the homotopy for commutativity has the components (-m, -lam / 2 Pi, defect / 2 Pi) *)
DifferentialCochainEqualQ[
  DifferentialSwapHomotopy[x, y],
  {-mm, -lam / (2 Pi), DeligneSwapDefect[A, B] / (2 Pi)},
  3]                                                                                        (* True *)
```

Towards the quantum theory: besides gauge transformations and flat connections,
the quadratic form `sum of a cup da` on a three-torus has two zero modes for
each momentum with `p1 + p2 + p3 = Pi`, the staggered modes of arXiv:2303.06160.
There are none if all sides are odd:

```wolfram
ChernSimonsZeroModeCount /@ {{2, 2, 2}, {3, 3, 3}, {2, 3, 4}}   (* {8, 0, 4} *)
StaggeredMomentumCount /@ {{2, 2, 2}, {3, 3, 3}, {2, 3, 4}}     (* {4, 0, 2} *)
```

Odd level. In four dimensions the Chern-Simons Lagrangian `L` is a primitive of
the theta term at `theta = 2 Pi k` up to an integer part,

    dL = (k / 4 Pi) Q(F) - k Pi Q(n) + (k a + d phi) cup dn,     Q(x) = x cup x + x cup_1 dx,

and `k Pi Q(n)` is `2 Pi` times an integer cochain only for even `k`. In three
dimensions this is the anomaly of the large gauge transformations: `exp(i S)`
changes by `(-1)^(k times the sum of q(m, n))` with the integer cochain
`q = ChernSimonsLargeGaugeAnomaly[m, n]`, and the sum can be odd. On a
three-torus the anomaly is cancelled by a sign `z(n)` with
`z(n + dm) = z(n) (-1)^(sum of q(m, n))`. Eight such functions are quadratic
refinements of the cup-1 pairing; they play the role of the spin structures:

```wolfram
dims = {3, 3, 3};
two = PeriodicCochain[1, dims, <|{{0, 0, 0}, {1}} -> 1, {{1, 0, 0}, {2}} -> 1|>];
zero = PeriodicCochain[2, dims, <||>];
CochainIntegrate[ChernSimonsLargeGaugeAnomaly[two, zero], dims]     (* 1: odd *)

z = SpinStructureSign[dims, {1, 1, 1}];    (* the signs of the three unit fluxes *)
z[Coboundary[two]]                                                  (* -1 *)
z[THooftFluxCochain[{{0, 1, 0}, {-1, 0, 0}, {0, 0, 0}}, dims]]      (* 1 *)
SpinStructureHolonomy[{1, 1, 1}]           (* {-1, -1, -1}: antiperiodic in all three directions *)
```

On fluxes whose dual curves lie in a coordinate plane, `z` depends only on the
class of the curve in that plane: it is 1 on contractible curves and minus the
holonomy otherwise. This is the quadratic form of a spin structure on the
two-torus, which identifies the eight functions with boundary conditions: the
fermion is periodic in a direction exactly if the straight flux tube along it
has the sign -1.

A local expression for `z` (Majorana fermions) is not there yet.

Background fields of the 1-form symmetry enter as fractional fluxes `n + B / N`.
The level `k` is the level `k N^2` with fluxes in `Z / N`, and the anomaly of
the Z_N 1-form symmetry at level `K` is the class of the line of charge `K / N`,
whose spin `K / (2 N^2)` decides whether the symmetry can be gauged (0), needs a
spin structure (1/2) or neither:

```wolfram
ChernSimonsOneFormAnomalyQ[4, 2]                    (* True *)
TopologicalSpin[ChernSimonsAnyons[4], {2}]          (* 1/2: level 4 = 1 * 2^2, an odd level *)
TopologicalSpin[ChernSimonsAnyons[8], {4}]          (* 0: level 8 = 2 * 2^2 *)
```

A flat Villain field is also a cocycle of Cech-de Rham type for the cover of
the three-torus by the unit cubes, the form of the lattice Deligne-Beilinson
cohomology of Y. Ikeda (arXiv:2601.15939): a local connection `A_p` on each
cube, integer transition functions `Lambda_pq` on intersections and integers
`N_pqr` on triple intersections. They are built from `(a, n)` by descent, and
the Chern numbers of the Cech cocycle `N` are the fluxes of `n`:

```wolfram
(* A = VillainField[a, n] with concrete fields on a periodic lattice, dims = {3, 3, 3} *)
CechDeRhamCocycleQ[A, dims]                         (* {True, True, True} *)
CechDeRhamChernNumbers[A, dims] === THooftFlux[n, dims]      (* True *)
```

The transition functions and `N` depend on the flux `n` alone, which is why the
modified Villain form needs no transition functions.

The star product of two such cocycles is summed over a chain of cells with
their cubes (`CechDeRhamFundamentalCycle`). The sum is defined modulo 1, and on
the cocycles of flat Villain fields its four contributions are, term by term,
those of the Villain form:

```wolfram
CechDeRhamStarIntegral[A, B, dims]
(* {sum of Cup[a, F_B] / (2 Pi)^2, 0, - sum of Cup[n, b] / (2 Pi), 0} *)
Total[CechDeRhamStarIntegral[A, A, dims]]
(* the sum of VillainChernSimons[2][A, phi] / (2 Pi): the action at level 2 *)
```

So `DeligneProduct` is this star product after the descent. The weight at an
even level `2 j` is `Exp[2 Pi I j (the integral)]`; half of the integral is not
defined modulo 1 (a large gauge transformation changes it by minus the sum of
`ChernSimonsLargeGaugeAnomaly`, which can be odd), the obstruction at odd level
again. The pieces of the chain on the links and on the sites are fixed here by
the cycle conditions; their signs have not been compared with the formulas of
that paper.

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

(* a braid is a list of generators, -i for the inverse of sigma_i *)
BraidPathPhase[Semion[], {{1}, {1}}, {1, 1}]  (* 1/2: one semion around another *)
```

The lines of U(1) Chern-Simons theory at level `k` are `ChernSimonsAnyons[k]`.
At odd level the category is not modular: the line `k` is a transparent
fermion, and the theory is a spin theory. As a category it is a bosonic theory
times `SuperVec[]`, and it sits inside the theory at level `4 k`:

```wolfram
MugerCenter[ChernSimonsAnyons[3]]       (* {{0}, {3}} *)
ChernSimonsSpinSplitQ[3]                (* True: ZNAnyons[3, 4] times SuperVec[] *)
ChernSimonsFermionCondensationQ[3]      (* True: the centralizer of the fermion at level 12 *)
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

The symmetric groups act on a presented operad, and the characters give the
free algebra on a graded vector space, arity by arity, with the Koszul signs:

```wolfram
OperadCharacter[LieOperad[], 3]            (* <|{3} -> <|0 -> -1|>, {2, 1} -> <||>, {1, 1, 1} -> <|0 -> 2|>|> *)
OperadCharacter[GerstenhaberOperad[], 3]   (* by cycle type and by the number of brackets *)

(* the free Lie algebra on two even generators: 2, 1, 2, 3 (Witt) *)
FreeAlgebraDimensions[LieOperad[], {2, 2}, 4]
(* the free Gerstenhaber algebra on a class x of degree 2: x^2 and [x, x] in arity 2 *)
FreeAlgebraDimensions[GerstenhaberOperad[], {2}, 2]   (* <|1 -> <|2 -> 1|>, 2 -> <|4 -> 1, 5 -> 1|>|> *)
```

### Loop spaces

``Operadica`Loops` `` makes the starting point of the recognition theorem
executable: an n-fold loop space is an algebra over the little n-cubes. A loop
is anything that can be applied to a point of the unit cube; a configuration of
little cubes acts by running each loop inside its cube.

```wolfram
half = {{{0, 1/2}}, {{1/2, 1}}};                       (* two little intervals *)
prod = LoopAction[half][GenericLoop[g1], GenericLoop[g2]];
{prod[{1/4}], prod[{7/8}], prod[{1/2}]}                (* {g1[{1/2}], g2[{3/4}], LoopBase} *)

(* (g1 g2) g3 and g1 (g2 g3) are two different configurations of three intervals *)
LittleCubesCompose[half, 1, half]                      (* {{{0, 1/4}}, {{1/4, 1/2}}, {{1/2, 1}}} *)
LittleCubesCompose[half, 2, half]                      (* {{{0, 1/2}}, {{1/2, 3/4}}, {{3/4, 1}}} *)

(* in two dimensions the two squares can move around each other: a b ~ b a *)
SwapPath[2][1] === LittleCubesAct[SwapPath[2][0], {2, 1}]            (* True *)

(* May's map C_n X -> Omega^n Sigma^n X *)
ApproximationMap[half, {x, y}][{1/4}]                  (* SuspensionPoint[{1/2}, x] *)

(* a path of configurations in the plane is a braid: half of SwapPath is the
   generator sigma (a counterclockwise exchange), all of it is sigma^2 *)
PathBraid[SwapPath[2], {0, 1}, 8]                      (* {1} *)
PathBraid[SwapPath[2], {0, 2}, 16]                     (* {1, 1} *)
```

`LoopEqualQ` compares two such maps at enough points of every cell of the grid
of endpoints to prove that they agree, for the given configurations; the tests
use it for the axioms of an algebra and for the statement that the
approximation map is a map of algebras.

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

### Delooping: the bar construction and Eilenberg-MacLane spaces

``Operadica`BarConstruction` `` computes with the n-fold bar construction of a
finite abelian group `A` (given by the orders of its cyclic factors). Its
generators are words in words: `BarWord[{1}, {2}]` is `[a|b]` in the first bar
construction, and `BarWord[BarWord[{1}], BarWord[{2}]]` is `[a || b]` in the
second. Its homology is the integral homology of the Eilenberg-MacLane space
`K(A, n)`, given as a list of cyclic summands (`0` for Z, `t` for Z_t).

```wolfram
d = BarDifferential[{3}];
d[BarWord[{1}, {2}]]                       (* [b] - [a+b] + [a], and [0] is dropped:
                                              LBasis[BarWord[{2}]] + LBasis[BarWord[{1}]] *)
d[BarWord[BarWord[{1}], BarWord[{2}]]]     (* LBasis[BarWord[BarWord[{1}, {2}]]] -
                                              LBasis[BarWord[BarWord[{2}, {1}]]] *)

Table[BarHomology[{2}, 2, k], {k, 1, 6}]   (* K(Z_2, 2): {{}, {2}, {}, {4}, {2}, {2}} *)
BarHomology[{4}, 2, 4]                     (* {8}: H_4(K(Z_4, 2)) = Z_8 *)
BarHomology[{2, 2}, 2, 4]                  (* {2, 4, 4} *)
BarHomology[{4}, 3, 5]                     (* {2} *)
```

The space itself is there as a simplicial set. A `k`-simplex of `K(A, n)` is a
flat `n`-form gauge field on a simplex, so a flat `n`-form gauge field on a
triangulated space is a simplicial map to `K(A, n)`.

```wolfram
EilenbergMacLaneSimplices[{2}, 1, 2]       (* the four flat Z_2 gauge fields on a triangle *)
EilenbergMacLaneHomotopy[{2}, 2, 3]        (* {1, 1, 2, 1}: the only homotopy group is pi_2 = Z_2 *)
EilenbergMacLaneHomology[{2}, 2, 4]        (* {4}, from 41 and 768 nondegenerate simplices *)
```

`ChainHomology[bases, d]` in ``Operadica`Graded` `` does the same for any finite
chain complex with integer coefficients, torsion included; `ChainBetti` gives
the rational Betti numbers.

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

### E_n structures are cocycles on the n-fold delooping

The associator and the braiding of a pointed category on `A` are a cochain on
the iterated bar construction: `w(a, b, c)` on `[a|b|c]` and `c(a, b)` on
`[a || b]`. Its coboundary consists of the pentagon and hexagon expressions,
and in the third bar construction of the double braiding as well. So a
monoidal, braided or symmetric structure is a cocycle of degree `n + 2` on
`K(A, n)` for `n = 1, 2, 3`.

```wolfram
BarCocycleQ[Semion[], 2]                       (* True: braided *)
BarCocycleQ[Semion[], 3]                       (* False: not symmetric *)
BarCoboundaryTable[ZNAnyons[3, 1], 2]          (* which pentagons and hexagons fail, generator by generator *)
DeloopingClassificationQ[ToricCode[]]          (* True: cocycle on B^n <=> E_n-monoidal, n = 1, 2, 3 *)

(* the number of structures is the order of H_(n+2)(K(A, n)) *)
Table[EnStructureCount[{4}, n], {n, 1, 4}]     (* {4, 8, 2, 2} *)

(* the spin is the value of the cocycle on the cycle [a || a] *)
BarCochainValue[Semion[], BarWord[BarWord[{1}], BarWord[{1}]]]     (* 1/4 *)
```

In the third bar construction `[a || a]` taken twice is a boundary, which is
why a symmetric structure only has bosons and fermions.

### The approximation theorem

For connected `X`, the little cubes with labels in `X` approximate the
iterated loop space: `C_n X ~ Omega^n Sigma^n X`. Rationally the left side is
the free algebra over `P_n = H_*(E_n)` on the homology of `X`, computed from
the characters above, and for a wedge of spheres the right side is known from
the free graded Lie algebra of Hilton and Milnor. The two computations are
independent, and they agree:

```wolfram
LoopSuspensionDimensions[2, {2}, 2]        (* Omega^2 S^4: <|1 -> <|2 -> 1|>, 2 -> <|4 -> 1, 5 -> 1|>|> *)
ApproximationTheoremQ[2, {2}, 4]           (* True *)
ApproximationTheoremQ[3, {1, 2}, 4]        (* True: Omega^3 Sigma^3 (S^1 v S^2), up to arity 4 *)
```

The bracket `[x, x]` of a class of degree `d` is non-zero exactly when `n + d`
is even: it is the Whitehead square of the sphere of dimension `n + d`.

For a point (`X = S^0`) the left side is the space of unordered little
squares, and its homology is the homology of the braid groups. The complex of
Fuks and Vainshtein computes it from the `2^(k-1)` compositions of `k`:

```wolfram
BraidGroupHomology[6]                      (* {{0}, {0}, {2}, {2}, {3}, {}}: Z, Z, Z_2, Z_2, Z_3, 0 *)
BarrattEcclesOrbitHomology[2, 3]           (* {{0}, {0}, {}, {}}: the same for Br_3, from the E_2 stage *)
ModularBetti[BraidGroupHomology[8], 2]     (* {1, 1, 1, 2, 2, 1, 1, 1} *)
KudoArakiDimensions[1, 4]                  (* Omega^2 S^3 modulo 2: generators in the degrees 1, 3, 7 *)
ApproximationTheoremModTwoQ[1, 8]          (* True *)
```

Rationally only `x^k` and `x^(k-2) [x, x]` survive (the free Gerstenhaber
algebra on a class of degree 0). Modulo 2 the Betti numbers count the ways to
write `k` as a sum of powers of 2: the polynomial algebra on `x, Q x, Q Q x,
...`, with the Kudo-Araki (Dyer-Lashof) operation `Q` where the bracket was.
For a sphere of dimension `d >= 1` this is the homology modulo 2 of
`Omega^2 S^(d+2)`.

`H_1` of the braid group is `Z`: `k` equal objects of a braided category see a
braid only through its exponent sum, with one angle, the spin. For little
3-cubes and for the symmetric groups `H_1` is `Z_2`
(`BarrattEcclesOrbitHomology[Infinity, 4, 1]`): bosons and fermions.

### Braiding from paths of little squares

A braided category gives a phase to a path of configurations of little squares
with an object in every square. `PathBraid` reads the braid of the path from
samples, and the counterclockwise exchange of `a` (left) and `b` (right) has
the phase `c(a, b)`; choosing counterclockwise fixes the orientation of the
plane.

```wolfram
(* the exchange of two semions is their spin; e around m in the toric code *)
PathBraidingPhase[Semion[], {{1}, {1}}, SwapPath[2], {0, 1}, 8]                (* 1/4 *)
PathBraidingPhase[ToricCode[], {{1, 0}, {0, 1}}, SwapPath[2], {0, 2}, 16]      (* 1/2 *)

(* composition of the operad: a row of two squares inside the second square *)
row = {{{0, 1/2}, {0, 1}}, {{1/2, 1}, {0, 1}}};
PathBraid[Function[s, LittleCubesCompose[SwapPath[2][s], 2, row]], {0, 1}, 32] (* {1, 2} *)
HexagonFromPathsQ[ZNAnyons[4, 1]]                                              (* True *)
BlockBraidingQ[ToricCode[], {2, 2}]                                            (* True *)

(* in three dimensions the two half turns are the ends of a homotopy *)
PathBraid[SwapHomotopy[0], {0, 1}, 8]                                          (* {1} *)
PathBraid[SwapHomotopy[1], {0, 1}, 8]                                          (* {-1} *)
SymmetricFromPathsQ /@ {Semion[], SuperVec[]}                                  (* {False, True} *)
```

Moving one square past a pair has the phase of the braiding with the product
of the pair, up to associators: written out, this is the first hexagon
equation, and a pair moving past one square is the second. Longer rows
(`BlockBraidingQ`) follow from the hexagons together with the pentagon. In
three dimensions `SwapHomotopy` joins the counterclockwise exchange to the
clockwise one, so the phase can depend only on the homotopy class of the path
if `c(a, b) = -c(b, a)`: E_3 means symmetric, and two equal objects are
exchanged with a sign, as bosons or fermions.

What is computed is the braid read from samples of a path and its phase. That
braids classify paths of configurations in the plane up to homotopy is a
classical fact used here, not something the computation proves.

### Lattice actions are cocycles on K(Z_N, n)

A simplex of `K(Z_N, n)` is a flat field on a simplex, so a lattice action can
be evaluated on it. Its value modulo 1 is a cocycle on `K(Z_N, n)`, and that
cocycle is the data of a category.

```wolfram
x = EMSimplex[3, {{3}, {1}, {0}, {2}, {1}, {3}}];   (* a flat Z_4 field on a tetrahedron *)
DijkgraafWittenWeight[4, 1][x]                 (* 3/4 = (1/16) (A cup dA)(0123) *)
VecZN[4, 1]["Associator"][{3}, {2}, {3}]       (* 3/4: the same number *)
DijkgraafWittenAssociatorQ[4, 1]               (* True: for every flat field *)

(* the Pontryagin square (p / 2N) P(B) on K(Z_2, 2), and the spins p / 4 *)
Table[CharacteristicClassOrder[{2}, 2, 4, PontryaginWeight[2, p]], {p, 0, 3}]   (* {1, 4, 2, 4} *)
PontryaginSpinQ[2, 1]                          (* True: the semion generates H^4 = Z_4 *)
```

The cup-1 term of the Pontryagin square is needed here: `B cup B / 4` alone
is not a cocycle on `K(Z_2, 2)`.

For n = 3 the action is a Steenrod square. On a flat Z_2 3-form field `C`,
`(1/2) Sq^2 C = (1/2) C cup_1 C` is a cocycle on `K(Z_2, 3)` whose class has
order 2: the generator of `H^5(K(Z_2, 3); U(1)) = Z_2`, the fermion as a
symmetric structure (the anomaly of a 2-form Z_2 symmetry in 3+1 dimensions
whose line is the worldline of a fermion).

```wolfram
SteenrodBocksteinQ[2]                          (* True: Sq^1 B = dB / 2 modulo 2, as cochains *)
CharacteristicClassOrder[{2}, 3, 5, SteenrodWeight[3, 2]]     (* 2 *)
SteenrodFermionQ /@ {2, 3}                     (* {True, True}: (1/2) B cup B and (1/2) C cup_1 C *)
```

So the three lattice actions `A cup dA`, `P(B)` and `Sq^2 C` are the monoidal,
the braided and the symmetric structures: E_1, E_2 and E_3.

A flat Z_N field is a flat U(1) field in the Villain form, `(2 Pi At / N,
d At / N)`. On such fields the U(1) Chern-Simons Lagrangian at an even level
`k` is the Dijkgraaf-Witten cocycle of level `-k / 2`: differential cohomology
restricts to group cohomology.

```wolfram
ChernSimonsWeight[4, 2][x]                     (* 1/4, for the flat Z_4 field x above *)
ChernSimonsDijkgraafWittenQ[4, 2]              (* True: the class of DijkgraafWittenWeight[4, -1] *)
ChernSimonsDijkgraafWittenQ[4, 1]              (* False: at an odd level it is not a cocycle *)
```

This is the recognition principle in its discrete form: an invertible E_n
structure on a group is a cocycle on its n-fold delooping, and a map from a
lattice to that delooping is a flat higher-form gauge field. The 't Hooft flux
line above is the same statement on a torus. (For n = 2 and n = 3 the cocycle on
K(Z_N, n) and the cocycle on the bar construction are compared through the
order of their classes; the comparison at the level of cochains is not
implemented yet.)

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
python3 reference/correction_reference.py   # the search for correction terms as linear algebra
python3 reference/encategory_reference.py   # pentagon, hexagons, coherence
python3 reference/operad_reference.py       # symmetric groups, little cubes
python3 reference/ainfinity_reference.py    # Koszul signs, A-infinity, associahedra
python3 reference/presented_reference.py    # Lie, Poisson, Gerstenhaber; little-cubes homology
python3 reference/einfinity_reference.py    # Barratt-Eccles operad and its action on cochains
python3 reference/bar_reference.py          # bar construction, K(A, n), E_n structures as cocycles
python3 reference/simplicial_reference.py   # cochains on simplices, characteristic classes (30 s)
python3 reference/approximation_reference.py   # characters, free algebras, loop spaces of suspensions
python3 reference/loops_reference.py        # the little cubes act on loop spaces
python3 reference/braiding_reference.py     # braids of paths of little squares, braiding phases
python3 reference/steenrod_reference.py     # Steenrod squares of cochains, the fermion on K(Z_2, 3)
python3 reference/braidgroup_reference.py   # homology of braid groups, unordered configurations
python3 reference/villain_reference.py      # Villain fields, differential cochains, Chern-Simons, the theta term
python3 reference/oddlevel_reference.py     # Chern-Simons at odd level: the anomaly and the signs that cancel it
python3 reference/cech_reference.py         # a flat Villain field as a Cech-de Rham cocycle; background fields
python3 reference/star_reference.py         # the star product and its integral on the Cech-de Rham cocycle
```

## Layout

```
PacletInfo.wl
Kernel/Operadica.wl       loads all layers
Kernel/Trees.wl           operad layer
Kernel/Operads.wl
Kernel/Rewriting.wl
Kernel/LittleCubes.wl
Kernel/Loops.wl
Kernel/Graded.wl
Kernel/AInfinity.wl
Kernel/Presented.wl
Kernel/BarrattEccles.wl
Kernel/BarConstruction.wl
Kernel/EnCategories.wl    category layer
Kernel/Lattice.wl         lattice gauge theory layer
Kernel/Gauge.wl
Kernel/Simplicial.wl
Kernel/Villain.wl
Kernel/EInfinity.wl       bridge
Kernel/Bridge.wl
Tests/*.wlt               one VerificationTest file per layer file
Scripts/RunTests.wls      test runner
Scripts/RunExamples.wls   evaluates the input cells of Examples/*.nb in a plain kernel
Examples/*.nb             notebooks: start with Operadica-Tour.nb
reference/*.py            Python references for the conventions
docs/DESIGN.ja.md         design and roadmap
```

## How this is developed

The aims and the direction are set by the author. The code in `Kernel/` and
`Scripts/`, the tests, the Python reference implementations and the
documentation are written by Claude (Anthropic) in conversation with the
author. Formulas with signs and conventions are checked first in the Python
references, in exact arithmetic. The tests are run in the Wolfram Language on
the author's machine with Claude Code, which also makes the commits; a version
is committed after all tests have passed there. The author checks the results
with the notebooks in `Examples/`.
