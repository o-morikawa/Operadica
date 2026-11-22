(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`BarrattEccles`                                               *)
(*                                                                        *)
(*  The Barratt-Eccles operad E, an E-infinity operad that is small        *)
(*  enough to compute with, its filtration by E_n operads, and its action  *)
(*  on the chains of the interval and of cubes.                            *)
(*                                                                        *)
(*  An element of E(r) of degree d is a list {w0, ..., wd} of words: a     *)
(*  word is a permutation of 1..r written as a list, and consecutive       *)
(*  words are different.  In degree 0 this is the operad of words (the     *)
(*  associative operad): {2, 1, 3} is the product x2 x1 x3.                *)
(*                                                                        *)
(*    differential  d{w0..wd} = Sum_i (-1)^i {w0, .., omit wi, .., wd}     *)
(*    action        relabel the letters: (w.s)_k = s^(-1)(w_k)             *)
(*    composition   {u0..ud} o_i {v0..ve} = sum over the lattice paths     *)
(*                  from (0, 0) to (d, e) of sign {u_x o_i v_y along the   *)
(*                  path}; o_i is the substitution of words; the sign is   *)
(*                  that of the shuffle, + for the path that runs first    *)
(*                  through u                                              *)
(*    filtration    (Berger) an element lies in F_n E if the relative      *)
(*                  order of every pair of letters changes fewer than n    *)
(*                  times along it; F_n E is an E_n operad                 *)
(*                                                                        *)
(*  The action on the interval (Berger-Fresse).  N is the chain complex of *)
(*  the interval: v0, v1 in degree 0, e in degree 1.  For s of degree m,   *)
(*  s.e in the r-fold tensor power of N is given by the table reduction:   *)
(*  cut the words into rows (a row ends at a letter that comes back        *)
(*  later).  The terms are indexed by a table and a position k in its last *)
(*  row: the letters before k get v0, the letters after k get v1, the      *)
(*  letter at k and the letters that end the earlier rows get e.  The sign *)
(*  is that of the sequence (row ends, letter at k).                       *)
(*                                                                        *)
(*  The action on the n-cube, the n-fold tensor power of the interval:     *)
(*  sum over 0 = i_0 <= ... <= i_n = d of the product of the actions of    *)
(*  {w_(i_(m-1)), ..., w_(i_m)} on the m-th edge, with the Koszul signs.   *)
(*                                                                        *)
(*  Checked in reference/einfinity_reference.py.                          *)
(*                                                                        *)
(*  Layer: operad.  Depends on: Graded.                                   *)
(* ====================================================================== *)

BeginPackage["Operadica`BarrattEccles`", {"Operadica`Graded`"}];

BarrattEcclesOperad::usage = "BarrattEcclesOperad[maxDegree] gives the Barratt-Eccles operad as a differential graded operad: \"Elements\" lists the elements of an arity up to the given degree, \"Compose\", \"Differential\" and \"Action\" act on single elements and give linear combinations. An element is a list {w0, ..., wd} of words with consecutive words different; its degree is d. DGOperadCheck applies to it.";

BarrattEcclesElements::usage = "BarrattEcclesElements[r, d] lists the elements of degree d of the Barratt-Eccles operad in arity r: the lists of d + 1 permutations of 1..r with consecutive entries different.";

BarrattEcclesDifferential::usage = "BarrattEcclesDifferential[u] gives the differential of an element {w0, ..., wd} of the Barratt-Eccles operad, or of a linear combination of LBasis[element]: the alternating sum over the omission of one word.";

BarrattEcclesCompose::usage = "BarrattEcclesCompose[u, i, v] gives the partial composition u o_i v in the Barratt-Eccles operad of elements or linear combinations: the sum over the shuffles of the two lists of words, composed as words.";

BarrattEcclesAct::usage = "BarrattEcclesAct[u, s] gives the right action of the permutation s on an element or a linear combination: every letter k of every word is replaced by s^(-1)(k).";

BarrattEcclesLevel::usage = "BarrattEcclesLevel[s] gives the smallest n such that the element s lies in the stage F_n of Berger's filtration of the Barratt-Eccles operad: one more than the largest number of times the relative order of a pair of letters changes along s. F_n is an E_n operad.";

BarrattEcclesFiltration::usage = "BarrattEcclesFiltration[n, r] gives the elements of the stage F_n of the Barratt-Eccles operad in arity r, as a list of the lists of elements of degree 0, 1, .... It is a finite complex with the homotopy type of the space of r little n-cubes.";

BarrattEcclesBetti::usage = "BarrattEcclesBetti[n, r] gives the Betti numbers of BarrattEcclesFiltration[n, r]: the homology of the E_n operad F_n in arity r.";

HigherCupElement::usage = "HigherCupElement[i] gives the element {{1, 2}, {2, 1}, {1, 2}, ...} of degree i of the Barratt-Eccles operad in arity 2. It acts on lattice cochains as the higher cup product, up to a sign.";

HirschElement::usage = "HirschElement[] gives the element {{1, 2, 3}, {1, 3, 2}, {3, 1, 2}} of degree 2 of the Barratt-Eccles operad in arity 3. Its differential is the failure of the cup-1 product to be a derivation of the cup product.";

TableReduction::usage = "TableReduction[s] gives the table reduction of the element s of the Barratt-Eccles operad: a linear combination of LBasis[u] with u a surjection, written as the list of its values. It is a chain map to the surjection complex of McClure-Smith and Berger-Fresse.";

TableReductionTables::usage = "TableReductionTables[s] gives the tables of the table reduction of s: each table is a list of rows, and its surjection is the concatenation of the rows.";

SurjectionDifferential::usage = "SurjectionDifferential[u] gives the differential of the surjection u (a list of values with adjacent values different), or of a linear combination of LBasis[surjection], with the signs of Berger and Fresse.";

IntervalCoaction::usage = "IntervalCoaction[s] gives the action of the element s of the Barratt-Eccles operad in arity r on the edge of the interval, as a list of terms {c, pattern}: pattern is a list of r entries, 0, 1 or 2, saying that the corresponding tensor factor is the initial vertex, the final vertex or the edge.";

CubeCoaction::usage = "CubeCoaction[s, n] gives the action of the element s of the Barratt-Eccles operad in arity r on the n-cube, as a list of terms {c, {row_1, ..., row_r}}: row_j has an entry for each direction of the cube, 2 if the j-th tensor factor extends in that direction, 1 if it sits at the upper end and 0 if it sits at the lower end. CubeCoaction[s][n] is the same; CubeCoaction[s] is the form used by LocalOperation.";

Begin["`Private`"];

(* ---------------------------------------------------------------------- *)
(* words                                                                  *)
(* ---------------------------------------------------------------------- *)

(* substitute the word v for the letter i of the word w *)
wordCompose[w_List, i_Integer, v_List] :=
  With[{m = Length[v]},
    Flatten[
      Map[Function[k, Which[k === i, v + (i - 1), k > i, k + m - 1, True, k]], w]
    ]
  ];

(* (w.s)_k = s^(-1)(w_k) *)
wordAct[w_List, s_List] := Ordering[s][[w]];

nonDegenerateQ[s_List] := AllTrue[Partition[s, 2, 1], Function[pr, pr[[1]] =!= pr[[2]]]];

elementQ[s_] := MatchQ[s, {__List}];

toLinear[s_?elementQ] := LBasis[s];
toLinear[u_] := u;


(* ---------------------------------------------------------------------- *)
(* the operad                                                             *)
(* ---------------------------------------------------------------------- *)

BarrattEcclesElements[r_Integer?Positive, d_Integer?NonNegative] := BarrattEcclesElements[r, d] =
  If[d === 0,
    Map[List, Permutations[Range[r]]],
    Flatten[
      Table[
        Append[s, w],
        {s, BarrattEcclesElements[r, d - 1]},
        {w, DeleteCases[Permutations[Range[r]], Last[s]]}
      ],
      1
    ]
  ];

beD[s_List] :=
  If[Length[s] === 1,
    0,
    LinearCollect[
      Total[
        Table[
          With[{t = Delete[s, k]},
            If[nonDegenerateQ[t], (-1)^(k - 1) LBasis[t], 0]
          ],
          {k, 1, Length[s]}
        ]
      ]
    ]
  ];

BarrattEcclesDifferential[s_?elementQ] := beD[s];
BarrattEcclesDifferential[u_] := LinearExtend[beD][u];

(* the lattice paths from (0, 0) to (d, e): {sign of the shuffle, list of points} *)
shufflePaths[d_Integer, e_Integer] := shufflePaths[d, e] =
  Map[
    Function[first,   (* the steps in the first direction *)
      Module[{x = 0, y = 0, inv = 0, pts = {{0, 0}}, step},
        Do[
          If[MemberQ[first, step],
            x = x + 1; inv = inv + y,
            y = y + 1
          ];
          AppendTo[pts, {x, y}],
          {step, 1, d + e}
        ];
        {(-1)^inv, pts}
      ]
    ],
    Subsets[Range[d + e], {d}]
  ];

beCompose[u_List, i_Integer, v_List] :=
  LinearCollect[
    Total[
      Map[
        Function[path,
          With[{t = Map[Function[pt, wordCompose[u[[pt[[1]] + 1]], i, v[[pt[[2]] + 1]]]], path[[2]]]},
            If[nonDegenerateQ[t], path[[1]] LBasis[t], 0]
          ]
        ],
        shufflePaths[Length[u] - 1, Length[v] - 1]
      ]
    ]
  ];

BarrattEcclesCompose[u_?elementQ, i_Integer, v_?elementQ] := beCompose[u, i, v];
BarrattEcclesCompose[u_, i_Integer, v_] :=
  BilinearExtend[Function[{x, y}, beCompose[x, i, y]]][toLinear[u], toLinear[v]];

beAct[s_List, perm_List] := Map[Function[w, wordAct[w, perm]], s];

BarrattEcclesAct[s_?elementQ, perm_List] := beAct[s, perm];
BarrattEcclesAct[u_, perm_List] := LinearExtend[Function[s, LBasis[beAct[s, perm]]]][u];

BarrattEcclesOperad[maxDegree_Integer?NonNegative] :=
  <|
    "Name" -> "BarrattEccles",
    "Linear" -> True,
    "Elements" -> Function[r, Flatten[Table[BarrattEcclesElements[r, d], {d, 0, maxDegree}], 1]],
    "Degree" -> Function[s, Length[s] - 1],
    "Compose" -> beCompose,
    "Unit" -> {{1}},
    "Differential" -> beD,
    "Action" -> Function[{s, perm}, LBasis[beAct[s, perm]]]
  |>;

HigherCupElement[i_Integer?NonNegative] := Table[If[EvenQ[k], {1, 2}, {2, 1}], {k, 0, i}];

HirschElement[] := {{1, 2, 3}, {1, 3, 2}, {3, 1, 2}};


(* ---------------------------------------------------------------------- *)
(* the filtration by E_n operads                                          *)
(* ---------------------------------------------------------------------- *)

BarrattEcclesLevel[s_?elementQ] :=
  With[{r = Length[First[s]], pos = Map[Ordering, s]},   (* pos[[k, v]]: the place of v in the word k *)
    1 + Max[
      0,
      Table[
        Count[
          Differences[Table[Boole[pos[[k, i]] < pos[[k, j]]], {k, 1, Length[s]}]],
          Except[0]
        ],
        {i, 1, r}, {j, i + 1, r}
      ]
    ]
  ];

BarrattEcclesFiltration[n_Integer?Positive, r_Integer?Positive] := BarrattEcclesFiltration[n, r] =
  Module[{perms = Permutations[Range[r]], frontier, out = {}},
    frontier = Map[List, perms];
    While[frontier =!= {},
      AppendTo[out, frontier];
      frontier = Select[
        Flatten[Table[Append[s, w], {s, frontier}, {w, DeleteCases[perms, Last[s]]}], 1],
        Function[t, BarrattEcclesLevel[t] <= n]
      ]
    ];
    out
  ];

BarrattEcclesBetti[n_Integer?Positive, r_Integer?Positive] :=
  ChainBetti[BarrattEcclesFiltration[n, r], beD];


(* ---------------------------------------------------------------------- *)
(* table reduction and surjections                                        *)
(* ---------------------------------------------------------------------- *)

(* the lists of the given number of positive integers with the given total *)
compositionsOf[total_Integer, parts_Integer] :=
  Flatten[Map[Permutations, IntegerPartitions[total, {parts}]], 1];

(* the rows of the table with row lengths a, or None: the row i consists of
   the first a_i letters of the word i that are not finished; the letters of
   a row except the last one are finished, the last row takes all the rest *)
tableRows[s_List, a_List] :=
  Module[{m = Length[s] - 1, removed = {}, rows = {}, ok = True, avail, row, i},
    Do[
      If[ok,
        avail = Select[s[[i + 1]], Function[x, ! MemberQ[removed, x]]];
        If[Length[avail] < a[[i + 1]] || (i === m && Length[avail] =!= a[[i + 1]]),
          ok = False,
          row = Take[avail, a[[i + 1]]];
          AppendTo[rows, row];
          removed = Join[removed, If[i < m, Most[row], row]]
        ]
      ],
      {i, 0, m}
    ];
    If[ok, rows, None]
  ];

TableReductionTables[s_?elementQ] :=
  DeleteCases[
    Map[
      Function[a, tableRows[s, a]],
      compositionsOf[Length[First[s]] + Length[s] - 1, Length[s]]
    ],
    None
  ];

TableReduction[s_?elementQ] :=
  LinearCollect[
    Total[
      Map[
        Function[rows, With[{u = Flatten[rows]}, If[nonDegenerateQ[u], LBasis[u], 0]]],
        TableReductionTables[s]
      ]
    ]
  ];
TableReduction[u_] := LinearExtend[TableReduction][u];

(* the occurrences of a value that are not the last one get alternating signs
   in the order of the sequence; the last occurrence gets the opposite of the
   sign of the previous occurrence of the same value; a value that occurs
   once cannot be removed *)
surjD[u_List] :=
  Module[{n = Length[u], last, signs, count = 0, prev = <||>, i, x},
    last = Association[Map[Function[v, v -> Last[Flatten[Position[u, v, {1}]]]], Union[u]]];
    signs = ConstantArray[None, n];
    Do[
      x = u[[i]];
      If[i =!= Lookup[last, Key[x]],
        signs[[i]] = (-1)^count;
        count = count + 1;
        AssociateTo[prev, x -> signs[[i]]],
        If[KeyExistsQ[prev, x], signs[[i]] = -Lookup[prev, Key[x]]]
      ],
      {i, 1, n}
    ];
    LinearCollect[
      Total[
        Table[
          With[{t = Delete[u, i]},
            If[signs[[i]] =!= None && nonDegenerateQ[t], signs[[i]] LBasis[t], 0]
          ],
          {i, 1, n}
        ]
      ]
    ]
  ];

SurjectionDifferential[u : {__Integer}] := surjD[u];
SurjectionDifferential[u_] := LinearExtend[surjD][u];


(* ---------------------------------------------------------------------- *)
(* the action on the interval and on cubes                                *)
(* ---------------------------------------------------------------------- *)

(* add the coefficients of equal patterns and drop the zero terms *)
collectTerms[list_List] :=
  KeyValueMap[
    Function[{pattern, c}, {c, pattern}],
    DeleteCases[GroupBy[list, Last -> First, Total], 0]
  ];

IntervalCoaction[s_?elementQ] := IntervalCoaction[s] =
  With[{r = Length[First[s]]},
    collectTerms[
      Flatten[
        Map[
          Function[rows,
            With[{ends = Map[Last, Most[rows]], before = Flatten[Most[rows]], last = Last[rows]},
              Table[
                With[{b = Join[before, Take[last, k - 1]], a = Drop[last, k], x = last[[k]]},
                  If[DuplicateFreeQ[b] && DuplicateFreeQ[a] && ! MemberQ[b, x] && ! MemberQ[a, x],
                    {
                      {
                        Signature[Append[ends, x]],
                        Table[
                          Which[
                            j === x || (MemberQ[b, j] && MemberQ[a, j]), 2,
                            MemberQ[b, j], 0,
                            True, 1
                          ],
                          {j, 1, r}
                        ]
                      }
                    },
                    {}
                  ]
                ],
                {k, 1, Length[last]}
              ]
            ]
          ],
          TableReductionTables[s]
        ],
        2
      ]
    ]
  ];

(* the sequences 0 = i_0 <= i_1 <= ... <= i_n = d *)
cutSequences[n_Integer, d_Integer] :=
  Map[
    Function[inner, Join[{0}, inner, {d}]],
    Select[Tuples[Range[0, d], n - 1], OrderedQ]
  ];

(* cols[[m, j]] is what the tensor factor j gets in the direction m.  The
   sign of the rearrangement that collects the factors: one for every pair
   of edges with the earlier direction in the later factor *)
rearrangeSign[cols_List] :=
  With[{edges = Position[cols, 2, {2}]},
    (-1)^Count[
      Subsets[edges, {2}],
      pair_ /; pair[[1, 1]] < pair[[2, 1]] && pair[[1, 2]] > pair[[2, 2]]
    ]
  ];

CubeCoaction[s_?elementQ, n_Integer?NonNegative] := CubeCoaction[s, n] =
  With[{r = Length[First[s]], d = Length[s] - 1},
    If[n === 0,
      If[d === 0, {{1, ConstantArray[{}, r]}}, {}],
      collectTerms[
        Flatten[
          Map[
            Function[cuts,
              With[{
                  factors = Table[
                    IntervalCoaction[Take[s, {cuts[[m]] + 1, cuts[[m + 1]] + 1}]],
                    {m, 1, n}
                  ],
                  (* the piece that acts on the direction m passes the m - 1 edges before it *)
                  sign = (-1)^Total[Table[(cuts[[m + 1]] - cuts[[m]]) (m - 1), {m, 1, n}]]
                },
                Map[
                  Function[choice,
                    With[{cols = Map[Last, choice]},
                      {sign (Times @@ Map[First, choice]) rearrangeSign[cols], Transpose[cols]}
                    ]
                  ],
                  Tuples[factors]
                ]
              ]
            ],
            cutSequences[n, d]
          ],
          1
        ]
      ]
    ]
  ];

CubeCoaction[s_?elementQ][n_Integer?NonNegative] := CubeCoaction[s, n];

End[];

EndPackage[];
