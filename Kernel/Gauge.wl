(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Gauge`                                                       *)
(*                                                                        *)
(*  Lattice gauge theory with cochains: gauge fields are cochains,         *)
(*  actions are built from the coboundary, the cup product and the higher  *)
(*  cup products, and gauge variations are computed and verified           *)
(*  symbolically.                                                          *)
(*                                                                        *)
(*  Typical use:                                                           *)
(*    a = Cochain[1, A];  lam = Cochain[0, L];                             *)
(*    var = GaugeVariation[action, a -> a + Coboundary[lam]];              *)
(*    TotalDerivativeQ[var, primitive, d]                                  *)
(*                                                                        *)
(*  The identities this layer relies on are checked independently in       *)
(*  reference/gauge_reference.py.                                          *)
(*                                                                        *)
(*  Layer: lattice gauge theory.  Depends on: Lattice.                    *)
(* ====================================================================== *)

BeginPackage["Operadica`Gauge`", {"Operadica`Lattice`"}];

CochainExpand::usage = "CochainExpand[expr] expands a cochain expression by multilinearity into a sum of scalar multiples of products of the basic cochains, using that the coboundary squares to zero. The result is a cochain expression equal to expr.";

GaugeVariation::usage = "GaugeVariation[expr, rules] gives the expanded change of the cochain expression expr under the replacement rules, for example a -> a + Coboundary[lam].";

TotalDerivativeQ::usage = "TotalDerivativeQ[expr, primitive, d] gives True if expr equals Coboundary[primitive] identically on the d-dimensional hypercubic lattice. The third argument and the option Modulus are those of CochainEqualQ.";

ZNFlatQ::usage = "ZNFlatQ[c, dims, n] gives True if the coboundary of the cochain c vanishes modulo n on every cell of the periodic lattice with side lengths dims.";

ModifiedVillainCS::usage = "ModifiedVillainCS[k][a, n, phi] gives the Lagrangian of the modified Villain U(1) Chern-Simons theory at level k in three dimensions, eq. (17) of arXiv:2303.06160 without the overall factor i: (k/(4 Pi)) (a u da - 2 Pi (a u n + n u a)) - (k/2) a u_1 dn + phi u dn, for a real 1-cochain a, an integer 2-cochain n and a real 0-cochain phi.";

Begin["`Private`"];

(* ---------------------------------------------------------------------- *)
(* multilinear expansion                                                  *)
(*   terms[expr] is a list of {scalar, monomial}; a monomial contains no   *)
(*   sums and no scalar factors                                            *)
(* ---------------------------------------------------------------------- *)

CochainExpand::notcochain = "`1` is not a cochain expression.";

terms[0] := {};

terms[c_Cochain] := {{1, c}};

terms[u_Plus] := Join @@ Map[terms, List @@ u];

terms[u_Times] :=
  With[{cs = Select[List @@ u, CochainQ], ks = Select[List @@ u, Function[e, ! CochainQ[e]]]},
    If[Length[cs] === 1,
      Map[Function[tm, {(Times @@ ks) tm[[1]], tm[[2]]}], terms[First[cs]]],
      Message[CochainExpand::notcochain, u]; {}
    ]
  ];

(* d d = 0 *)
terms[Coboundary[c_]] :=
  Map[
    Function[tm, {tm[[1]], Coboundary[tm[[2]]]}],
    Select[terms[c], Function[tm, Head[tm[[2]]] =!= Coboundary]]
  ];

terms[Cup[a_, b_]] :=
  Flatten[
    Table[{s[[1]] t[[1]], Cup[s[[2]], t[[2]]]}, {s, terms[a]}, {t, terms[b]}],
    1
  ];

terms[Cup[a_, b_, rest__]] := terms[Cup[Cup[a, b], rest]];

terms[HigherCup[i_][a_, b_]] :=
  Flatten[
    Table[{s[[1]] t[[1]], HigherCup[i][s[[2]], t[[2]]]}, {s, terms[a]}, {t, terms[b]}],
    1
  ];

terms[u_] := (Message[CochainExpand::notcochain, u]; {});


CochainExpand[expr_] :=
  With[{grouped = GroupBy[terms[expr], Last -> First, Function[cs, Expand[Total[cs]]]]},
    Total[KeyValueMap[Function[{mono, coeff}, coeff mono], grouped]]
  ];


(* ---------------------------------------------------------------------- *)
(* gauge variations                                                       *)
(* ---------------------------------------------------------------------- *)

GaugeVariation[expr_, rules_] := CochainExpand[(expr /. rules) - expr];


Options[TotalDerivativeQ] = {Modulus -> 0};

TotalDerivativeQ[expr_, primitive_, where_, opts : OptionsPattern[]] :=
  CochainEqualQ[expr, Coboundary[primitive], where, opts];


ZNFlatQ[c_, dims : {__Integer}, n_Integer?Positive] :=
  CochainZeroQ[Coboundary[c], dims, Modulus -> n];


(* ---------------------------------------------------------------------- *)
(* actions                                                                *)
(* ---------------------------------------------------------------------- *)

ModifiedVillainCS[k_][a_, n_, phi_] :=
  (k / (4 Pi)) (Cup[a, Coboundary[a]] - 2 Pi (Cup[a, n] + Cup[n, a])) -
    (k / 2) HigherCup[1][a, Coboundary[n]] +
    Cup[phi, Coboundary[n]];

End[];

EndPackage[];
