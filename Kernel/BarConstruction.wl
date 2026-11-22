(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`BarConstruction`                                             *)
(*                                                                        *)
(*  Delooping.  For a finite abelian group A = Z_N1 x ... x Z_Nr the       *)
(*  n-fold bar construction B^n of the group ring Z[A] is a chain complex  *)
(*  whose homology is the homology of the Eilenberg-MacLane space          *)
(*  K(A, n) = B^n A, the space with the single homotopy group pi_n = A.    *)
(*                                                                        *)
(*  The complex (normalized and reduced).                                  *)
(*    generators   level 0: the non-zero elements of A (lists of integers), *)
(*                 in degree 0;                                            *)
(*                 level n: the words BarWord[x1, ..., xm], m >= 1, in     *)
(*                 generators of level n - 1, written [x1 | ... | xm];     *)
(*                 deg [x1|..|xm] = sum (deg xi + 1).                      *)
(*                 [a || b] stands for [[a] | [b]], and so on.             *)
(*    product      level 0: addition in A (a zero result is dropped);      *)
(*                 level n: the shuffle product, with the Koszul sign for  *)
(*                 letters of degree deg x + 1.                            *)
(*    differential d[x1|..|xm] = - sum_i (-1)^(e_(i-1)) [.. | d xi | ..]   *)
(*                               + sum_i (-1)^(e_i) [.. | xi x_(i+1) | ..], *)
(*                 e_i = sum_(j <= i) (deg xj + 1);  at level 1 also the   *)
(*                 end terms [x2|..|xm] + (-1)^m [x1|..|x_(m-1)].          *)
(*                 At level 1 this is the differential of group homology:  *)
(*                 d[a|b] = [b] - [a+b] + [a].                             *)
(*                                                                        *)
(*  The product is associative and graded commutative, d is a derivation,  *)
(*  and this is why the construction can be iterated: the bar construction *)
(*  of a commutative algebra is again a commutative algebra.               *)
(*                                                                        *)
(*  The space.  A k-simplex of K(A, n) is an A-valued n-cocycle on the     *)
(*  k-simplex: a flat n-form gauge field on it.  Faces restrict the field  *)
(*  and degeneracies pull it back.  A flat n-form gauge field on a         *)
(*  triangulated space is the same as a simplicial map to K(A, n).         *)
(*                                                                        *)
(*  Checked in reference/bar_reference.py.                                *)
(*                                                                        *)
(*  Layer: operad.  Depends on: Graded.                                   *)
(* ====================================================================== *)

BeginPackage["Operadica`BarConstruction`", {"Operadica`Graded`"}];

BarWord::usage = "BarWord[x1, ..., xm] is the word [x1 | ... | xm] of the bar construction. In B^1 the letters are non-zero group elements (lists of integers); in B^n they are words of B^(n-1). BarWord[BarWord[a], BarWord[b]] is the element [a || b] of B^2.";

BarLevel::usage = "BarLevel[x] gives n if x is a generator of the n-fold bar construction: 0 for a group element, and one more than the level of its letters for a word.";

BarDegree::usage = "BarDegree[x] gives the degree of a generator of an iterated bar construction: 0 for a group element, and the sum of (degree + 1) over the letters for a word.";

BarGenerators::usage = "BarGenerators[orders, n, k] lists the generators of degree k of the n-fold bar construction B^n of the group ring of Z_N1 x ... x Z_Nr, with orders = {N1, ..., Nr}.";

BarProduct::usage = "BarProduct[orders][x, y] gives the product of two generators of the same level, or of linear combinations of them: the sum in the group at level 0 (a zero result is dropped), and the shuffle product with the Koszul sign for words. The product is associative and graded commutative.";

BarDifferential::usage = "BarDifferential[orders][x] gives the differential of a generator, or of a linear combination of generators, of an iterated bar construction. It has degree -1, squares to zero, and is a derivation of BarProduct.";

BarSuspension::usage = "BarSuspension[x] gives the one-letter word [x] of the next bar construction, for a generator or a linear combination. The suspension raises the level and the degree by one, and d[x] = -[d x].";

BarHomology::usage = "BarHomology[orders, n, k] gives the homology in degree k >= 1 of the n-fold bar construction, that is, the integral homology H_k(K(A, n)) of the Eilenberg-MacLane space, as the list of its cyclic summands: 0 for Z and t for Z_t. {} is the trivial group.";

EMSimplex::usage = "EMSimplex[k, values] is a k-simplex of the Eilenberg-MacLane space K(A, n): a flat n-form gauge field on the simplex with vertices 0, ..., k. values lists its values (group elements) on the n-dimensional faces Subsets[Range[0, k], {n + 1}], in this order.";

EilenbergMacLaneSimplices::usage = "EilenbergMacLaneSimplices[orders, n, k] lists the k-simplices of K(A, n), the A-valued n-cocycles on the k-simplex. The values on the faces through the vertex 0 are free and determine the others; for k < n there is one simplex.";

EilenbergMacLaneFace::usage = "EilenbergMacLaneFace[n][x, i] gives the i-th face of the simplex x of K(A, n): the restriction of the field to the face opposite to the vertex i.";

EilenbergMacLaneDegeneracy::usage = "EilenbergMacLaneDegeneracy[orders, n][x, i] gives the i-th degeneracy of the simplex x of K(A, n): the pullback of the field along the map of simplices that sends the vertices i and i + 1 to i.";

EilenbergMacLaneDegenerateQ::usage = "EilenbergMacLaneDegenerateQ[orders, n][x] gives True if the simplex x of K(A, n) is a degeneracy of a simplex of lower dimension.";

EilenbergMacLaneCocycleQ::usage = "EilenbergMacLaneCocycleQ[orders, n][x] gives True if the values of x are closed: the alternating sum over the faces of every (n+1)-dimensional face vanishes.";

EilenbergMacLaneHomotopy::usage = "EilenbergMacLaneHomotopy[orders, n, kmax] gives the orders of the homotopy groups pi_0, ..., pi_kmax of K(A, n), computed from the Moore complex of the simplicial group: the simplices whose faces 1, ..., k are trivial, with the face 0 as differential. The result is |A| in degree n and 1 elsewhere.";

EilenbergMacLaneHomology::usage = "EilenbergMacLaneHomology[orders, n, k] gives the integral homology H_k of K(A, n), computed from the nondegenerate simplices of the simplicial set, in the format of BarHomology. It agrees with BarHomology[orders, n, k] for k >= 1.";

Begin["`Private`"];

(* ---------------------------------------------------------------------- *)
(* words                                                                  *)
(* ---------------------------------------------------------------------- *)

BarLevel[_List] := 0;
BarLevel[x_BarWord] := 1 + BarLevel[First[x]];

BarDegree[_List] := 0;
BarDegree[x_BarWord] := Total[Map[Function[y, BarDegree[y] + 1], List @@ x]];


(* generators of level n and degree k: a first letter of degree j, then a
   word of degree k - j - 1 *)
gens[orders_List, 0, k_Integer] :=
  If[k === 0, Rest[Tuples[Map[Function[m, Range[0, m - 1]], orders]]], {}];

gens[orders_List, n_Integer?Positive, k_Integer] :=
  gens[orders, n, k] =
    If[k < n,
      {},
      Flatten[
        Table[
          With[{tails = If[k - j - 1 === 0, {BarWord[]}, gens[orders, n, k - j - 1]]},
            Flatten[
              Table[Prepend[tail, letter], {letter, gens[orders, n - 1, j]}, {tail, tails}],
              1
            ]
          ],
          {j, 0, k - 1}
        ],
        1
      ]
    ];

BarGenerators[orders : {__Integer}, n_Integer?NonNegative, k_Integer] := gens[orders, n, k];


(* ---------------------------------------------------------------------- *)
(* the product                                                            *)
(* ---------------------------------------------------------------------- *)

product[orders_List][x_List, y_List] :=
  With[{s = Mod[x + y, orders]},
    If[AllTrue[s, Function[v, v === 0]], 0, LBasis[s]]
  ];

(* shuffles: pos lists the places of the letters of x.  A letter of x that
   moves past the letters of y placed before it picks up the Koszul sign *)
product[orders_List][x_BarWord, y_BarWord] :=
  Module[{p = Length[x], q = Length[y], dx, dy, out = 0, word, sign, xi, yi, placed, pos, t},
    dx = Map[Function[u, BarDegree[u] + 1], List @@ x];
    dy = Map[Function[u, BarDegree[u] + 1], List @@ y];
    Do[
      word = {}; sign = 0; xi = 1; yi = 1; placed = 0;
      Do[
        If[MemberQ[pos, t],
          sign = sign + dx[[xi]] placed;
          word = Append[word, x[[xi]]];
          xi = xi + 1,
          word = Append[word, y[[yi]]];
          placed = placed + dy[[yi]];
          yi = yi + 1
        ],
        {t, 1, p + q}
      ];
      out = out + (-1)^sign LBasis[BarWord @@ word],
      {pos, Subsets[Range[p + q], {p}]}
    ];
    LinearCollect[out]
  ];

BarProduct[orders : {__Integer}][x : (_BarWord | _List), y : (_BarWord | _List)] :=
  product[orders][x, y];

BarProduct[orders : {__Integer}][u_, v_] := BilinearExtend[product[orders]][u, v];


(* ---------------------------------------------------------------------- *)
(* the differential                                                       *)
(* ---------------------------------------------------------------------- *)

diff[orders_List][_List] := 0;

(* the values are remembered: the same letters occur in many words *)
diff[orders_List][x_BarWord] := diff[orders][x] =
  Module[{m = Length[x], level = BarLevel[x], eta = 0, out = 0, i},
    Do[
      (* the differential of the i-th letter *)
      If[level >= 2,
        out = out - (-1)^eta *
          LinearExtend[Function[y, LBasis[ReplacePart[x, i -> y]]]][diff[orders][x[[i]]]]
      ];
      eta = eta + BarDegree[x[[i]]] + 1;
      (* the product of the i-th and the (i+1)-th letter *)
      If[i < m,
        out = out + (-1)^eta *
          LinearExtend[
            Function[y, LBasis[Join[Take[x, i - 1], BarWord[y], Drop[x, i + 1]]]]
          ][product[orders][x[[i]], x[[i + 1]]]]
      ],
      {i, 1, m}
    ];
    (* the augmentation of the first and of the last letter *)
    If[level === 1 && m >= 2,
      out = out + LBasis[Rest[x]] + (-1)^m LBasis[Most[x]]
    ];
    LinearCollect[out]
  ];

BarDifferential[orders : {__Integer}][x_BarWord] := diff[orders][x];

BarDifferential[orders : {__Integer}][_List] := 0;

BarDifferential[orders : {__Integer}][u_] := LinearExtend[diff[orders]][u];


BarSuspension[x_BarWord] := BarWord[x];
BarSuspension[x_List] := BarWord[x];
BarSuspension[u_] := LinearExtend[Function[y, LBasis[BarWord[y]]]][u];


BarHomology[orders : {__Integer}, n_Integer?Positive, k_Integer?Positive] :=
  ChainHomology[
    {gens[orders, n, k - 1], gens[orders, n, k], gens[orders, n, k + 1]},
    diff[orders]
  ][[2]];


(* ---------------------------------------------------------------------- *)
(* the simplicial set K(A, n)                                             *)
(* ---------------------------------------------------------------------- *)

faces[n_Integer, k_Integer] := Subsets[Range[0, k], {n + 1}];

(* the cocycle condition on the face {0} + f gives the value on f from the
   values on the faces through the vertex 0 *)
EilenbergMacLaneSimplices[orders : {__Integer}, n_Integer?Positive, k_Integer?NonNegative] :=
  Module[{fs = faces[n, k], free, els},
    free = Select[fs, Function[f, First[f] === 0]];
    els = Tuples[Map[Function[m, Range[0, m - 1]], orders]];
    Map[
      Function[vals,
        With[{val = AssociationThread[free, vals]},
          EMSimplex[
            k,
            Map[
              Function[f,
                If[First[f] === 0,
                  Lookup[val, Key[f]],
                  Mod[
                    -Total[
                      Table[
                        (-1)^j Lookup[val, Key[Delete[Prepend[f, 0], j + 1]]],
                        {j, 1, n + 1}
                      ]
                    ],
                    orders
                  ]
                ]
              ],
              fs
            ]
          ]
        ]
      ],
      Tuples[els, Length[free]]
    ]
  ];

EilenbergMacLaneFace[n_Integer?Positive][EMSimplex[k_Integer, vals_List], i_Integer] :=
  With[{val = AssociationThread[faces[n, k], vals]},
    EMSimplex[
      k - 1,
      Map[
        Function[f, Lookup[val, Key[Map[Function[v, If[v < i, v, v + 1]], f]]]],
        faces[n, k - 1]
      ]
    ]
  ];

EilenbergMacLaneDegeneracy[orders : {__Integer}, n_Integer?Positive][EMSimplex[k_Integer, vals_List], i_Integer] :=
  With[{val = AssociationThread[faces[n, k], vals], zero = ConstantArray[0, Length[orders]]},
    EMSimplex[
      k + 1,
      Map[
        Function[f,
          With[{g = Map[Function[v, If[v <= i, v, v - 1]], f]},
            If[DuplicateFreeQ[g], Lookup[val, Key[g]], zero]
          ]
        ],
        faces[n, k + 1]
      ]
    ]
  ];

EilenbergMacLaneDegenerateQ[orders : {__Integer}, n_Integer?Positive][x_EMSimplex] :=
  AnyTrue[
    Range[0, First[x] - 1],
    Function[i,
      EilenbergMacLaneDegeneracy[orders, n][EilenbergMacLaneFace[n][x, i], i] === x
    ]
  ];

EilenbergMacLaneCocycleQ[orders : {__Integer}, n_Integer?Positive][EMSimplex[k_Integer, vals_List]] :=
  With[{val = AssociationThread[faces[n, k], vals]},
    AllTrue[
      Subsets[Range[0, k], {n + 2}],
      Function[big,
        AllTrue[
          Mod[
            Total[Table[(-1)^(j - 1) Lookup[val, Key[Delete[big, j]]], {j, 1, n + 2}]],
            orders
          ],
          Function[v, v === 0]
        ]
      ]
    ]
  ];


trivialQ[EMSimplex[_, vals_List]] := AllTrue[Flatten[vals], Function[v, v === 0]];

(* the Moore complex: N_k = the k-simplices with trivial faces 1, ..., k;
   the differential is the face 0 *)
EilenbergMacLaneHomotopy[orders : {__Integer}, n_Integer?Positive, kmax_Integer?NonNegative] :=
  Module[{moore},
    moore = Table[
      Select[
        EilenbergMacLaneSimplices[orders, n, k],
        Function[x,
          AllTrue[Range[1, k], Function[i, trivialQ[EilenbergMacLaneFace[n][x, i]]]]
        ]
      ],
      {k, 0, kmax + 1}
    ];
    Table[
      With[{
          cycles = Select[
            moore[[k + 1]],
            Function[x, k === 0 || trivialQ[EilenbergMacLaneFace[n][x, 0]]]
          ],
          bounds = Union[Map[Function[x, EilenbergMacLaneFace[n][x, 0]], moore[[k + 2]]]]
        },
        Length[cycles] / Length[bounds]
      ],
      {k, 0, kmax}
    ]
  ];


(* normalized chains: the nondegenerate simplices, with the alternating sum
   of the faces; degenerate faces are dropped *)
EilenbergMacLaneHomology[orders : {__Integer}, n_Integer?Positive, k_Integer?Positive] :=
  Module[{nd, member, boundary},
    nd = Table[
      Select[
        EilenbergMacLaneSimplices[orders, n, j],
        Function[x, ! EilenbergMacLaneDegenerateQ[orders, n][x]]
      ],
      {j, k - 1, k + 1}
    ];
    member = Association[Map[Function[x, x -> True], Join[nd[[1]], nd[[2]]]]];
    boundary = Function[x,
      LinearCollect[
        Total[
          Table[
            With[{f = EilenbergMacLaneFace[n][x, i]},
              If[KeyExistsQ[member, f], (-1)^i LBasis[f], 0]
            ],
            {i, 0, First[x]}
          ]
        ]
      ]
    ];
    ChainHomology[nd, boundary][[2]]
  ];

End[];

EndPackage[];
