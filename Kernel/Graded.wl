(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Graded`                                                      *)
(*                                                                        *)
(*  Linear combinations, free graded operads with Koszul signs,            *)
(*  differential graded operads, and the homology of chain complexes.      *)
(*                                                                        *)
(*  A linear combination is a sum of scalar multiples of LBasis[x].        *)
(*                                                                        *)
(*  Free graded operad.  A tree monomial is the tensor product of its      *)
(*  vertex labels in PREORDER (the order in which the heads appear when    *)
(*  the tree is written as an expression).  Partial composition carries    *)
(*  the Koszul sign                                                        *)
(*      s o_i t = (-1)^(|t| D) (graft t at leaf i of s),                   *)
(*      D = sum of the degrees of the vertices of s after leaf i.          *)
(*  The axioms then read                                                   *)
(*      sequential  (a o_i b) o_(i+j-1) c = a o_i (b o_j c)                *)
(*      parallel    (a o_i b) o_(k+m-1) c = (-1)^(|b||c|) (a o_k c) o_i b  *)
(*  A derivation d of degree -1 is determined by its values on the         *)
(*  generators:                                                            *)
(*      d(h[c1, .., ck]) = (d h)(c1, .., ck)                               *)
(*          + sum_j (-1)^(|h| + |c1| + .. + |c_(j-1)|) h[c1, .., d cj, .., ck] *)
(*                                                                        *)
(*  Checked in reference/ainfinity_reference.py.                          *)
(*                                                                        *)
(*  Layer: operad.  Depends on: Trees.                                    *)
(* ====================================================================== *)

BeginPackage["Operadica`Graded`", {"Operadica`Trees`"}];

LBasis::usage = "LBasis[x] is the basis vector labelled by x. A linear combination is a sum of scalar multiples of basis vectors.";

LinearTerms::usage = "LinearTerms[expr] gives the list of {coefficient, label} of the linear combination expr.";

LinearCollect::usage = "LinearCollect[expr] brings a linear combination to normal form: one term for each label, with expanded coefficient, and no zero terms.";

LinearZeroQ::usage = "LinearZeroQ[expr] gives True if the linear combination expr is zero.";

LinearExtend::usage = "LinearExtend[f][expr] applies f, a function from labels to linear combinations, to each term of expr and extends linearly.";

BilinearExtend::usage = "BilinearExtend[f][u, v] applies f, a function from pairs of labels to linear combinations, to each pair of terms of u and v and extends bilinearly.";

FreeGradedOperad::usage = "FreeGradedOperad[{h1 -> {k1, d1}, ...}] gives the free graded nonsymmetric operad on generators hi of arity ki >= 2 and degree di. Its \"Compose\" gives a linear combination: the grafted tree with its Koszul sign. \"Degree\" gives the degree of a tree.";

GradedDegree::usage = "GradedDegree[op, expr] gives the degree of a homogeneous linear combination expr of elements of the graded operad op.";

GradedCompose::usage = "GradedCompose[op][u, i, v] gives the partial composition of linear combinations u and v of elements of the graded operad op.";

WithDifferential::usage = "WithDifferential[op, dgen] gives the graded operad op with the differential that is the derivation of degree -1 extending dgen, a function from generators to linear combinations of trees. The differential is stored under the key \"Differential\" and acts on single trees; use LinearExtend to apply it to linear combinations.";

DGOperadCheck::usage = "DGOperadCheck[op, maxArity] checks the axioms of a graded operad with Koszul signs (unit, sequential, parallel) and, if op has a \"Differential\", that it squares to zero and satisfies the Leibniz rule d(a o_i b) = da o_i b + (-1)^|a| a o_i db. It returns an Association with the keys \"Passed\", \"Checked\", \"Failed\", \"Counterexamples\" and \"Strength\".";

DGOperadQ::usage = "DGOperadQ[op, maxArity] gives True if DGOperadCheck finds no violation.";

ChainBetti::usage = "ChainBetti[{basis0, basis1, ...}, d] gives the Betti numbers of the chain complex with the given bases in degrees 0, 1, ... and the differential d of degree -1, a function from basis labels to linear combinations.";

SmithInvariants::usage = "SmithInvariants[m] gives the non-zero diagonal entries d1, d2, ... of the Smith normal form of the integer matrix m, each dividing the next. The cokernel of m is the sum of the cyclic groups Z_di and of a free group.";

ChainHomology::usage = "ChainHomology[{basis0, basis1, ...}, d] gives the integral homology of the chain complex with the given bases in degrees 0, 1, ... and the differential d of degree -1, a function from basis labels to linear combinations with integer coefficients. Each group is given as the list of its cyclic summands: 0 for Z and t for Z_t, so that {0, 0, 2} is Z + Z + Z_2 and {} is the trivial group. In the top degree the chains of the next degree are taken to be absent.";

Begin["`Private`"];

(* ---------------------------------------------------------------------- *)
(* linear combinations                                                    *)
(* ---------------------------------------------------------------------- *)

LinearTerms::notlinear = "`1` is not a linear combination of basis vectors.";

LinearTerms[expr_] := terms[Expand[expr]];

terms[0] := {};
terms[u_Plus] := Join @@ Map[terms, List @@ u];
terms[LBasis[x_]] := {{1, x}};
terms[Times[k__, LBasis[x_]]] := {{Times[k], x}};
terms[u_] := (Message[LinearTerms::notlinear, u]; {});


LinearCollect[expr_] :=
  With[{grouped = GroupBy[LinearTerms[expr], Last -> First, Function[cs, Expand[Total[cs]]]]},
    Total[KeyValueMap[Function[{x, coeff}, coeff LBasis[x]], grouped]]
  ];

LinearZeroQ[expr_] := LinearCollect[expr] === 0;

LinearExtend[f_][expr_] :=
  LinearCollect[
    Total[Map[Function[tm, tm[[1]] f[tm[[2]]]], LinearTerms[expr]]]
  ];

BilinearExtend[f_][u_, v_] :=
  LinearCollect[
    Total[
      Flatten[
        Table[s[[1]] t[[1]] f[s[[2]], t[[2]]], {s, LinearTerms[u]}, {t, LinearTerms[v]}]
      ]
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* free graded operads                                                    *)
(* ---------------------------------------------------------------------- *)

(* positions of the internal vertices of a tree *)
vertexPositions[t_] := Position[t, Except[OpLeaf], {0, Infinity}, Heads -> False];

treeDegree[degs_Association][t_] :=
  Total[Map[Function[pos, Lookup[degs, Key[Head[OpSubtree[t, pos]]]]], vertexPositions[t]]];

(* p comes strictly before q in preorder: an ancestor comes before its
   descendants, and otherwise the first differing index decides *)
beforeQ[p_List, q_List] :=
  Module[{k = 1, n = Min[Length[p], Length[q]]},
    While[k <= n && p[[k]] === q[[k]], k = k + 1];
    If[k > n, Length[p] < Length[q], p[[k]] < q[[k]]]
  ];

gradedGraft[degs_Association][s_, i_Integer, t_] :=
  Module[{lp = OpLeafPositions[s][[i]], after},
    after = Total[
      Map[
        Function[pos, If[beforeQ[lp, pos], Lookup[degs, Key[Head[OpSubtree[s, pos]]]], 0]],
        vertexPositions[s]
      ]
    ];
    (-1)^(treeDegree[degs][t] after) LBasis[OpReplaceSubtree[s, lp, t]]
  ];

FreeGradedOperad[gens_List] :=
  With[{
      arities = Map[Function[g, g[[1]] -> g[[2, 1]]], gens],
      degs = Association[Map[Function[g, g[[1]] -> g[[2, 2]]], gens]]
    },
    <|
      "Name" -> "FreeGraded",
      "Generators" -> gens,
      "Linear" -> True,
      "Elements" -> Function[n, OpPlanarTrees[arities, n]],
      "Degree" -> treeDegree[degs],
      "Compose" -> gradedGraft[degs],
      "Unit" -> OpLeaf
    |>
  ];


GradedDegree::inhom = "`1` is not homogeneous.";

GradedDegree[op_Association, expr_] :=
  With[{ds = Union[Map[Function[tm, op["Degree"][tm[[2]]]], LinearTerms[expr]]]},
    Which[
      ds === {}, 0,
      Length[ds] === 1, First[ds],
      True, Message[GradedDegree::inhom, expr]; $Failed
    ]
  ];

GradedCompose[op_Association][u_, i_Integer, v_] :=
  BilinearExtend[Function[{x, y}, op["Compose"][x, i, y]]][u, v];


(* ---------------------------------------------------------------------- *)
(* derivations                                                            *)
(* ---------------------------------------------------------------------- *)

derive[op_Association, dgen_][OpLeaf] := 0;

derive[op_Association, dgen_][t_] :=
  Module[{h = Head[t], children = List @@ t, deg = op["Degree"], acc, slot, before, out, c, j},
    (* (d h)(c1, .., ck): graft the children from left to right *)
    acc = dgen[h];
    slot = 1;
    Do[
      If[c =!= OpLeaf, acc = GradedCompose[op][acc, slot, LBasis[c]]];
      slot = slot + OpArity[c],
      {c, children}
    ];
    out = acc;
    (* h[c1, .., d cj, .., ck] *)
    before = deg[OpCorolla[h, Length[children]]];
    Do[
      out = out + (-1)^before *
        LinearExtend[Function[tc, LBasis[ReplacePart[t, j -> tc]]]][derive[op, dgen][children[[j]]]];
      before = before + deg[children[[j]]],
      {j, 1, Length[children]}
    ];
    LinearCollect[out]
  ];

WithDifferential[op_Association, dgen_] :=
  Join[op, <|"Differential" -> derive[op, dgen], "GeneratorDifferential" -> dgen|>];


(* ---------------------------------------------------------------------- *)
(* axioms                                                                 *)
(* ---------------------------------------------------------------------- *)

Options[DGOperadCheck] = {"MinArity" -> 1, "MaxCounterexamples" -> 3};

DGOperadCheck[op_Association, maxArity_Integer?Positive, OptionsPattern[]] :=
  Module[{comp, gc, unit, deg, diff, dlin, minA, maxBad, elems, kinds, checked, failed, bad, note,
      a, b, c, i, j, k, l, m, n},
    comp = op["Compose"];
    gc = GradedCompose[op];
    unit = op["Unit"];
    deg = op["Degree"];
    diff = Lookup[op, "Differential", None];
    dlin = If[diff === None, None, LinearExtend[diff]];
    minA = OptionValue["MinArity"];
    maxBad = OptionValue["MaxCounterexamples"];
    elems = Association[Table[n -> op["Elements"][n], {n, minA, maxArity}]];
    kinds = If[diff === None,
      {"Unit", "Sequential", "Parallel"},
      {"Unit", "Sequential", "Parallel", "Square", "Leibniz"}
    ];
    checked = Association[Map[Function[key, key -> 0], kinds]];
    failed = Association[Map[Function[key, key -> 0], kinds]];
    bad = Association[Map[Function[key, key -> {}], kinds]];

    note = Function[{axiom, ok, data},
      checked[axiom] = checked[axiom] + 1;
      If[! TrueQ[ok],
        failed[axiom] = failed[axiom] + 1;
        If[Length[bad[axiom]] < maxBad,
          bad[axiom] = Append[bad[axiom], data]
        ]
      ]
    ];

    (* unit, and d d = 0 *)
    Do[
      Do[
        note["Unit", LinearZeroQ[comp[unit, 1, a] - LBasis[a]], {"left", a}];
        Do[
          note["Unit", LinearZeroQ[comp[a, i, unit] - LBasis[a]], {"right", a, i}],
          {i, 1, n}
        ];
        If[diff =!= None,
          note["Square", LinearZeroQ[dlin[diff[a]]], {a}]
        ],
        {a, elems[n]}
      ],
      {n, minA, maxArity}
    ];

    (* Leibniz rule *)
    If[diff =!= None,
      Do[
        If[l + m - 1 <= maxArity,
          Do[
            note["Leibniz",
              LinearZeroQ[
                dlin[comp[a, i, b]] -
                  gc[diff[a], i, LBasis[b]] -
                  (-1)^deg[a] gc[LBasis[a], i, diff[b]]
              ],
              {a, i, b}
            ],
            {a, elems[l]}, {b, elems[m]}, {i, 1, l}
          ]
        ],
        {l, minA, maxArity}, {m, minA, maxArity}
      ]
    ];

    (* associativity with Koszul signs *)
    Do[
      If[l + m + n - 2 <= maxArity,
        Do[
          Do[
            note["Sequential",
              LinearZeroQ[
                gc[comp[a, i, b], i + j - 1, LBasis[c]] - gc[LBasis[a], i, comp[b, j, c]]
              ],
              {a, i, b, j, c}
            ],
            {i, 1, l}, {j, 1, m}
          ];
          Do[
            note["Parallel",
              LinearZeroQ[
                gc[comp[a, i, b], k + m - 1, LBasis[c]] -
                  (-1)^(deg[b] deg[c]) gc[comp[a, k, c], i, LBasis[b]]
              ],
              {a, i, b, k, c}
            ],
            {i, 1, l}, {k, i + 1, l}
          ],
          {a, elems[l]}, {b, elems[m]}, {c, elems[n]}
        ]
      ],
      {l, minA, maxArity}, {m, minA, maxArity}, {n, minA, maxArity}
    ];

    <|
      "Operad" -> Lookup[op, "Name", "unnamed"],
      "MaxArity" -> maxArity,
      "Passed" -> (Total[Values[failed]] === 0),
      "Checked" -> checked,
      "Failed" -> failed,
      "Counterexamples" -> bad,
      "Strength" -> "exhaustive over the listed basis elements, total arity <= " <> ToString[maxArity]
    |>
  ];

Options[DGOperadQ] = Options[DGOperadCheck];

DGOperadQ[op_Association, maxArity_Integer?Positive, opts : OptionsPattern[]] :=
  TrueQ[DGOperadCheck[op, maxArity, opts]["Passed"]];


(* ---------------------------------------------------------------------- *)
(* homology of a finite chain complex                                     *)
(* ---------------------------------------------------------------------- *)

(* the matrix of d from the span of high to the span of low *)
differentialMatrix[low_List, high_List, d_] :=
  Module[{index = AssociationThread[low, Range[Length[low]]]},
    Normal[
      SparseArray[
        Flatten[
          Table[
            Map[
              Function[tm, {Lookup[index, Key[tm[[2]]]], col} -> tm[[1]]],
              LinearTerms[d[high[[col]]]]
            ],
            {col, 1, Length[high]}
          ],
          1
        ],
        {Length[low], Length[high]}
      ]
    ]
  ];

ChainBetti[bases_List, d_] :=
  Module[{top = Length[bases] - 1, rk},
    (* rk[[k + 1]] is the rank of d from degree k to degree k - 1 *)
    rk = Join[
      {0},
      Table[
        If[bases[[k]] === {} || bases[[k + 1]] === {},
          0,
          MatrixRank[differentialMatrix[bases[[k]], bases[[k + 1]], d]]
        ],
        {k, 1, top}
      ],
      {0}
    ];
    Table[Length[bases[[k + 1]]] - rk[[k + 1]] - rk[[k + 2]], {k, 0, top}]
  ];


(* ---------------------------------------------------------------------- *)
(* integral homology                                                      *)
(*   the Smith normal form by row and column operations.  The corner is   *)
(*   an entry of smallest absolute value; a remainder left in its row or  *)
(*   column, or an entry that it does not divide, gives a smaller corner. *)
(* ---------------------------------------------------------------------- *)

SmithInvariants[m0_?MatrixQ] :=
  Module[{m = m0, nr, nc, out = {}, t = 1, block, pos, p, q, rows, cols, bad, done},
    {nr, nc} = Dimensions[m];
    While[t <= Min[nr, nc] && Max[Abs[m[[t ;; nr, t ;; nc]]]] > 0,
      block = Abs[m[[t ;; nr, t ;; nc]]];
      pos = First[Position[block, Min[DeleteCases[Flatten[block], 0]], {2}, 1]] + (t - 1);
      m[[{t, pos[[1]]}]] = m[[{pos[[1]], t}]];
      m[[All, {t, pos[[2]]}]] = m[[All, {pos[[2]], t}]];
      done = False;
      While[! done,
        p = m[[t, t]];
        (* clear the column below the corner *)
        If[t < nr,
          q = Quotient[m[[t + 1 ;; nr, t]], p];
          m[[t + 1 ;; nr]] = m[[t + 1 ;; nr]] - Outer[Times, q, m[[t]]]
        ];
        rows = Select[Range[t + 1, nr], Function[r, m[[r, t]] =!= 0], 1];
        If[rows =!= {},
          m[[{t, First[rows]}]] = m[[{First[rows], t}]],
          (* clear the row to the right of the corner *)
          If[t < nc,
            q = Quotient[m[[t, t + 1 ;; nc]], p];
            m[[All, t + 1 ;; nc]] = m[[All, t + 1 ;; nc]] - Outer[Times, m[[All, t]], q]
          ];
          cols = Select[Range[t + 1, nc], Function[c, m[[t, c]] =!= 0], 1];
          If[cols =!= {},
            m[[All, {t, First[cols]}]] = m[[All, {First[cols], t}]],
            (* the corner must divide all the remaining entries *)
            bad = Select[
              Range[t + 1, nr],
              Function[r, AnyTrue[m[[r]], Function[v, Mod[v, p] =!= 0]]],
              1
            ];
            If[bad =!= {},
              m[[t]] = m[[t]] + m[[First[bad]]],
              done = True
            ]
          ]
        ]
      ];
      out = Append[out, Abs[m[[t, t]]]];
      t = t + 1
    ];
    out
  ];

ChainHomology[bases_List, d_] :=
  Module[{top = Length[bases] - 1, inv},
    (* inv[[k + 1]] holds the invariants of d from degree k to degree k - 1 *)
    inv = Join[
      {{}},
      Table[
        If[bases[[k]] === {} || bases[[k + 1]] === {},
          {},
          SmithInvariants[differentialMatrix[bases[[k]], bases[[k + 1]], d]]
        ],
        {k, 1, top}
      ],
      {{}}
    ];
    Table[
      Join[
        ConstantArray[0, Length[bases[[k + 1]]] - Length[inv[[k + 1]]] - Length[inv[[k + 2]]]],
        Sort[Select[inv[[k + 2]], Function[x, x > 1]]]
      ],
      {k, 0, top}
    ]
  ];

End[];

EndPackage[];
