# Operadica

Operads and lattice cochains, computed in the Wolfram Language.

A Mathematica expression is a tree, and grafting trees is operadic composition.
Operadica uses that to make the standard theory of operads something you can
run, and it treats cochains on the hypercubic lattice (coboundary, cup product,
Steenrod's higher cup products) as the first example of an algebra rather than
an afterthought. The aim is a path from the definitions to May's recognition
theorem in which every statement along the way is checked by computation.

Status: **stage 1 of 5**. The design and the roadmap are in
[docs/DESIGN.ja.md](docs/DESIGN.ja.md) (Japanese).

## Load

```wolfram
PacletDirectoryLoad["/path/to/Operadica"];
Needs["Operadica`"]
```

Requires Wolfram Language 12.1 or later.

## Trees and operads

```wolfram
(* a tree is OpLeaf or h[t1, ..., tk]; partial composition is grafting *)
OpCompose[m[OpLeaf, OpLeaf], 1, m[OpLeaf, OpLeaf]]
(* m[m[OpLeaf, OpLeaf], OpLeaf] *)

(* a basis of the free operad: Catalan numbers *)
Table[Length[OpPlanarTrees[{m -> 2}, n]], {n, 1, 7}]
(* {1, 1, 2, 5, 14, 42, 132} *)

(* every operad has the same interface, so one verifier checks them all *)
OperadAxiomCheck[WordOperad[], 4]

(* associativity as a rewriting rule; the quotient is the operad As *)
as = QuotientOperad[{m -> 2}, {m[m[a_, b_], c_] :> m[a, m[b, c]]}];
OpLocallyConfluentQ[{m -> 2}, as["Rules"], 5]
Table[Length[as["Elements"][n]], {n, 1, 6}]
(* {1, 1, 1, 1, 1, 1} *)
```

## Lattice cochains

Cochain expressions stay symbolic until they are evaluated on a cell, and the
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

Identities are proved, not sampled. With generic cochains the values are
independent variables, and the operations are local and translation invariant,
so a check at one symbolic base point holds on every lattice of that dimension
and over every coefficient ring:

```wolfram
(* Leibniz rule in four dimensions *)
CochainEqualQ[
  Coboundary[Cup[a, b]],
  Cup[Coboundary[a], b] - Cup[a, Coboundary[b]],
  4]

(* the cup product commutes up to the cup-1 product *)
CochainEqualQ[
  Cup[a, b] + Cup[b, a],
  -(Coboundary[HigherCup[1][a, b]] - HigherCup[1][Coboundary[a], b] + HigherCup[1][a, Coboundary[b]]),
  4]
```

The Pontryagin square and a 't Hooft flux background on the four-torus:

```wolfram
z = {{0, 1, 0, 0}, {-1, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, -1, 0}};
flux = THooftFluxCochain[z, {4, 4, 4, 4}];
CochainZeroQ[Coboundary[flux], {4, 4, 4, 4}]              (* True *)
CochainIntegrate[PontryaginSquare[flux], {4, 4, 4, 4}]    (* 2 = 2 Pf(z) *)
```

### Conventions

- `(dc)(x; m1 < ... < mk) = Sum_j (-1)^(j-1) [ c(x + e_mj; without mj) - c(x; without mj) ]`
- `(a u b)(x; s) = Sum_{A, B} sign(A, B) a(x; A) b(x + e_A; B)` over splittings of `s` into
  a front part `A` of size `p` and the rest `B`.
- `HigherCup[i]` follows eq. (A3) of Jacobson and Sulejmanpasic,
  [arXiv:2303.06160](https://arxiv.org/abs/2303.06160), and reproduces the component
  formulas of its Appendix A, which follow Chen and Tata,
  [arXiv:2106.05274](https://arxiv.org/abs/2106.05274).
- Steenrod's original convention differs by `SteenrodCupSign[p, q, i] = (-1)^(i (p + q + 1))`.
- `PontryaginSquare[b] = Cup[b, b] - HigherCup[1][b, Coboundary[b]]`.

## Tests

```
wolframscript -file Scripts/RunTests.wls
```

The sign conventions of the lattice layer are also fixed by an independent
pure-Python reference, which derives the higher cup products from the
tensor-product structure on cubes and checks the relations above by exact
integer arithmetic:

```
python3 reference/cubical_reference.py
```

## Layout

```
PacletInfo.wl
Kernel/Operadica.wl     public symbols, loads the files below
Kernel/Trees.wl         planar trees, grafting, enumeration
Kernel/Operads.wl       operad objects, axiom verifier, algebras
Kernel/Rewriting.wl     quotient operads, normal forms, confluence
Kernel/Lattice.wl       cochains, coboundary, cup, higher cup
Tests/*.wlt             VerificationTest files
Scripts/RunTests.wls    test runner
reference/              Python reference for the sign conventions
docs/DESIGN.ja.md       design and roadmap
```
