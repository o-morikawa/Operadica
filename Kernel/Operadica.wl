(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica -- operads and lattice cochains, computed                    *)
(*                                                                        *)
(*  Load from a checkout:                                                 *)
(*      PacletDirectoryLoad["/path/to/Operadica"];                        *)
(*      Needs["Operadica`"]                                               *)
(*                                                                        *)
(*  Layers                                                                *)
(*    Trees.wl      planar trees = free nonsymmetric operad               *)
(*    Operads.wl    operad objects, axiom verification, algebras          *)
(*    Rewriting.wl  quotient operads by rewriting, local confluence       *)
(*    Lattice.wl    cochains on the hypercubic lattice: d, cup, cup_i     *)
(* ====================================================================== *)

BeginPackage["Operadica`"];

(* ---------------------------------------------------------------------- *)
(* Trees                                                                  *)
(* ---------------------------------------------------------------------- *)

OpLeaf::usage = "OpLeaf is an input slot of a planar tree. A tree is either OpLeaf or h[t1, ..., tk], where h is an inert head (a generating operation) and t1, ..., tk are trees.";

OpTreeQ::usage = "OpTreeQ[t] gives True if t is a planar tree built from OpLeaf and inert heads.";

OpLeafPositions::usage = "OpLeafPositions[t] gives the positions of the leaves of the tree t, from left to right.";

OpArity::usage = "OpArity[t] gives the number of leaves (inputs) of the tree t.";

OpCompose::usage = "OpCompose[s, i, t] gives the partial composition of trees: t is grafted onto the i-th leaf of s.";

OpComposeAll::usage = "OpComposeAll[s, {t1, ..., tn}] grafts t1, ..., tn onto the n leaves of s simultaneously (full operadic composition).";

OpCorolla::usage = "OpCorolla[h, n] gives the tree h[OpLeaf, ..., OpLeaf] with n leaves.";

OpPlanarTrees::usage = "OpPlanarTrees[{h1 -> k1, h2 -> k2, ...}, n] lists all planar trees with n leaves built from generators hi of arity ki >= 2. This is a basis of the arity-n part of the free nonsymmetric operad.";

OpEvaluate::usage = "OpEvaluate[t, {h1 -> f1, ...}, {x1, ..., xn}] interprets the tree t as an n-ary function, replacing each generator hi by the function fi, and applies it to x1, ..., xn.";

OpTreePlot::usage = "OpTreePlot[t] draws the tree t.";

(* ---------------------------------------------------------------------- *)
(* Operads                                                                *)
(* ---------------------------------------------------------------------- *)

FreeOperad::usage = "FreeOperad[{h1 -> k1, ...}] gives the free nonsymmetric operad on generators hi of arity ki. An operad is an Association with keys \"Name\", \"Elements\" (arity -> list of elements), \"Compose\" (a function of {x, i, y} giving the partial composition of y into input i of x), \"Unit\", and optionally \"Equal\".";

AssociativeOperad::usage = "AssociativeOperad[] gives the nonsymmetric associative operad: one operation in each arity n >= 1, represented by the integer n.";

WordOperad::usage = "WordOperad[] gives the associative operad in its symmetric form: an operation of arity n is a word in x1, ..., xn using each variable once, represented by a permutation of {1, ..., n}. Composition is substitution of words.";

EndOperad::usage = "EndOperad[set] gives the endomorphism operad of a finite set: an operation of arity n is a function set^n -> set, represented by an Association from n-tuples to elements.";

OperadAxiomCheck::usage = "OperadAxiomCheck[op, maxArity] checks the unit axiom and the sequential and parallel associativity axioms of partial composition on all listed elements, for all compositions of total arity at most maxArity. It returns an Association with the keys \"Passed\", \"Checked\", \"Failed\", \"Counterexamples\" and \"Strength\".";

OperadAxiomsQ::usage = "OperadAxiomsQ[op, maxArity] gives True if OperadAxiomCheck finds no violation.";

OpAssociativityRelation::usage = "OpAssociativityRelation[m] gives the pair of trees {m[m[OpLeaf, OpLeaf], OpLeaf], m[OpLeaf, m[OpLeaf, OpLeaf]]}.";

OpAlgebraCheck::usage = "OpAlgebraCheck[relations, rules, argTuples] checks that each relation {lhsTree, rhsTree} holds when the generators are interpreted by rules and both sides are applied to each tuple of arguments of the right length. The option \"Equal\" sets the equality test (default SameQ). It returns an Association with the keys \"Passed\" and \"Counterexamples\".";

(* ---------------------------------------------------------------------- *)
(* Rewriting                                                              *)
(* ---------------------------------------------------------------------- *)

OpNormalForm::usage = "OpNormalForm[t, rules] rewrites the tree t with the given rules, at any subtree, until no rule applies.";

OpRewriteSteps::usage = "OpRewriteSteps[t, rules] lists all trees obtained from t by applying one rule at one subtree.";

OpLocallyConfluentQ::usage = "OpLocallyConfluentQ[gens, rules, maxArity] gives True if, for every tree with at most maxArity leaves, all one-step rewrites have the same normal form. For a terminating system whose critical pairs live in arity at most maxArity this proves confluence in all arities.";

QuotientOperad::usage = "QuotientOperad[gens, rules] gives the operad whose elements are the normal forms of trees under the rewriting rules; composition is grafting followed by normalization.";

(* ---------------------------------------------------------------------- *)
(* Lattice cochains                                                       *)
(* ---------------------------------------------------------------------- *)

LCell::usage = "LCell[x, s] is the cell of the hypercubic lattice with base point x (a list of d coordinates) spanned by the directions s (an increasing list of integers between 1 and d).";

LCells::usage = "LCells[dims, p] lists all p-cells of the periodic lattice with side lengths dims.";

Cochain::usage = "Cochain[p, f] is the p-cochain whose value on the cell LCell[x, s] is f[x, s]. With f an undefined symbol this is a generic cochain, suitable for proving identities.";

Coboundary::usage = "Coboundary[c] is the lattice coboundary (exterior derivative) of the cochain c. It stays unevaluated until it is evaluated on a cell with CochainValue.";

HigherCup::usage = "HigherCup[i][a, b] is the higher cup product of a p-cochain a and a q-cochain b, of degree p + q - i. HigherCup[0] is the cup product Cup[a, b]. The sign convention is that of eq. (A3) of arXiv:2303.06160; see SteenrodCupSign for Steenrod's original convention.";

CochainQ::usage = "CochainQ[c] gives True if c is a cochain expression: built from Cochain, Coboundary, Cup, HigherCup, sums and scalar multiples.";

CochainDegree::usage = "CochainDegree[c] gives the degree of a homogeneous cochain expression.";

CochainValue::usage = "CochainValue[c, x, s] evaluates the cochain expression c on the cell with base point x and directions s. CochainValue[c, LCell[x, s]] does the same. Directions given out of order pick up the sign of the permutation.";

CochainZeroQ::usage = "CochainZeroQ[c, d] gives True if the cochain expression c vanishes identically on the d-dimensional hypercubic lattice, tested at a symbolic base point. CochainZeroQ[c, {L1, ..., Ld}] tests all cells of a periodic lattice. The option Modulus -> n tests vanishing modulo n.";

CochainEqualQ::usage = "CochainEqualQ[a, b, d] gives True if the cochain expressions a and b agree identically on the d-dimensional hypercubic lattice. CochainEqualQ[a, b, {L1, ..., Ld}] compares on all cells of a periodic lattice. The option Modulus -> n compares modulo n.";

PeriodicCochain::usage = "PeriodicCochain[p, dims, data] is the p-cochain on the periodic lattice with side lengths dims whose values are given by the Association data, with keys {x, s}; missing cells have value 0.";

RandomCochain::usage = "RandomCochain[p, dims] is a p-cochain on the periodic lattice with random integer values. RandomCochain[p, dims, {min, max}] sets the range.";

THooftFluxCochain::usage = "THooftFluxCochain[z, dims] is the closed 2-cochain on the periodic lattice with side lengths dims that equals z[[mu, nu]] on the plaquette in the (mu, nu) plane at the sites whose mu and nu coordinates are both maximal, and 0 elsewhere. z is an antisymmetric matrix.";

CochainIntegrate::usage = "CochainIntegrate[c, dims] sums the top-degree cochain c over all top cells of the periodic lattice with side lengths dims.";

PontryaginSquare::usage = "PontryaginSquare[b] gives Cup[b, b] - HigherCup[1][b, Coboundary[b]].";

SteenrodSquare::usage = "SteenrodSquare[k][a] gives HigherCup[p - k][a, a] for a p-cochain a; modulo 2 this represents the Steenrod square Sq^k.";

SteenrodCupSign::usage = "SteenrodCupSign[p, q, i] gives the sign (-1)^(i (p + q + 1)) relating the two conventions for higher cup products: Steenrod's cup-i of a p-cochain and a q-cochain equals SteenrodCupSign[p, q, i] times HigherCup[i].";

Begin["`Private`"];

$kernelDirectory = DirectoryName[$InputFileName];

Scan[
  Function[file, Get[FileNameJoin[{$kernelDirectory, file}]]],
  {"Trees.wl", "Operads.wl", "Rewriting.wl", "Lattice.wl"}
];

End[];

EndPackage[];
