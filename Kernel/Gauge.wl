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

CochainLinearSolve::usage = "CochainLinearSolve[target, {c1, ..., cr}, d] looks for coefficients x1, ..., xr with target = x1 c1 + ... + xr cr as an identity of cochains on the d-dimensional hypercubic lattice. The target and the candidates are cochain expressions of one degree, built from generic cochains Cochain[p, f]; the coefficients may depend on the parameters in them. It gives the Association of \"Solvable\", \"Unique\" and \"Coefficients\" (one solution, or $Failed if there is none), and $Failed if the degrees do not agree. With coboundaries of possible primitives and variations of possible correction terms as candidates, this is the search for a correction term.";

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

terms[LocalOperation[f_, d_][as__]] :=
  Map[
    Function[choice,
      {Times @@ Map[First, choice], LocalOperation[f, d] @@ Map[Last, choice]}
    ],
    Tuples[Map[terms, {as}]]
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

(* ---------------------------------------------------------------------- *)
(* the search for coefficients                                            *)
(* ---------------------------------------------------------------------- *)

(* the expanded values on the cells at a symbolic base point *)
clsValues[u_, p_Integer, d_Integer] :=
  With[{x = Array[\[FormalX], d]},
    Map[Function[s, Expand[CochainValue[u, x, s]]], Subsets[Range[d], {p}]]
  ];

(* rows {coefficients of the candidates..., coefficient of the target}, one
   for each cell and each monomial in the values of the generic cochains *)
clsRows[tvals_List, cvals_List, heads_List] :=
  With[{
      kernels = DeleteDuplicates[
        Cases[{tvals, cvals}, _?(Function[v, MemberQ[heads, Head[v]]]), {0, Infinity}]
      ],
      r = Length[cvals]
    },
    (* the values f[x, s] of the generic cochains, renamed to clsVar[1], clsVar[2], ... *)
    With[{vars = Array[clsVar, Length[kernels]]},
      With[{sub = Thread[kernels -> vars]},
        With[{
            trules = Map[Function[v, Association[CoefficientRules[v /. sub, vars]]], tvals],
            crules = Map[
              Function[vals, Map[Function[v, Association[CoefficientRules[v /. sub, vars]]], vals]],
              cvals
            ]
          },
          Flatten[
            Table[
              Map[
                Function[e,
                  Append[
                    Table[Lookup[crules[[i, j]], Key[e], 0], {i, 1, r}],
                    Lookup[trules[[j]], Key[e], 0]
                  ]
                ],
                Union[Keys[trules[[j]]], Flatten[Table[Keys[crules[[i, j]]], {i, 1, r}], 1]]
              ],
              {j, 1, Length[tvals]}
            ],
            1
          ]
        ]
      ]
    ]
  ];

clsResult[{}, r_Integer] :=
  <|"Solvable" -> True, "Unique" -> False, "Coefficients" -> ConstantArray[0, r]|>;

clsResult[rows_List, r_Integer] :=
  With[{mat = rows[[All, 1 ;; r]], rhs = rows[[All, r + 1]]},
    If[MatrixRank[mat] === MatrixRank[rows],
      <|
        "Solvable" -> True,
        "Unique" -> (MatrixRank[mat] === r),
        "Coefficients" -> Simplify[LinearSolve[mat, rhs]]
      |>,
      <|"Solvable" -> False, "Unique" -> False, "Coefficients" -> $Failed|>
    ]
  ];

CochainLinearSolve[target_, cands : {__}, d_Integer?Positive] :=
  With[{p = CochainDegree[target]},
    If[! IntegerQ[p] || p < 0 || p > d || ! AllTrue[cands, Function[c, CochainDegree[c] === p]],
      $Failed,
      clsResult[
        clsRows[
          clsValues[target, p, d],
          Map[Function[c, clsValues[c, p, d]], cands],
          DeleteDuplicates[Cases[{target, cands}, Cochain[_, f_Symbol] :> f, {0, Infinity}]]
        ],
        Length[cands]
      ]
    ]
  ];

End[];

EndPackage[];
