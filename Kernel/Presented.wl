(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Presented`                                                   *)
(*                                                                        *)
(*  Symmetric operads given by binary generators and quadratic relations,  *)
(*  computed by linear algebra: Com, Lie, Ass, Poisson, Gerstenhaber and   *)
(*  the operads P_n = H_*(E_n).  Generators may have odd degree; all signs *)
(*  follow the Koszul rule.                                                *)
(*                                                                        *)
(*  Labelled trees.  A tree is a positive integer (an input) or g[t1, t2]  *)
(*  with g a generator: OpLie[OpLie[1, 2], 3] is [[x1, x2], x3].  A tree   *)
(*  stands for the tensor product of its vertices in PREORDER, as in       *)
(*  Operadica`Graded`.  A generator g comes with                           *)
(*      g[x, y] = sign * partner[y, x],                                    *)
(*  and the rules are                                                      *)
(*      swap    g[a, b] = sign (-1)^(|a| |b|) partner[b, a]                *)
(*      graft   t o_k x = (-1)^(|x| D) (x at the leaf k of t),             *)
(*              D = sum of the degrees of the vertices of t after leaf k   *)
(*      action  (t . s): the leaf labelled j gets the label s^(-1)(j),     *)
(*              so that (t . s)(x1, .., xn) = t(x_{s^-1(1)}, ..)           *)
(*                                                                        *)
(*  A tree is a SHUFFLE tree if at every vertex the smallest leaf of the   *)
(*  left child is smaller than the smallest leaf of the right child.  The  *)
(*  shuffle trees on {1..n} are a basis of the free operad in arity n.     *)
(*  The ideal of relations in arity n is spanned by the relations with     *)
(*  shuffle trees plugged into their three inputs, plugged into shuffle    *)
(*  trees.  Row reduction gives the dimension of the quotient, a basis of  *)
(*  normal forms, and a decision procedure for identities.                 *)
(*                                                                        *)
(*  Checked in reference/presented_reference.py.                          *)
(*                                                                        *)
(*  Layer: operad.  Depends on: Graded.                                   *)
(* ====================================================================== *)

BeginPackage["Operadica`Presented`", {"Operadica`Graded`"}];

OpCom::usage = "OpCom[x, y] is the commutative product, the generator of the commutative operad.";

OpLie::usage = "OpLie[x, y] is the bracket, the generator of the Lie operad. In PoissonOperad[n] it has degree n - 1.";

OpAss::usage = "OpAss[x, y] is the associative product x y, a generator of the presented associative operad.";

OpAssOp::usage = "OpAssOp[x, y] is the opposite product y x: OpAss[x, y] = OpAssOp[y, x].";

PresentedOperad::usage = "PresentedOperad[{g1 -> s1, ...}, {r1, ...}] gives the symmetric operad with binary generators gi and quadratic relations ri. Each si is 1 (gi is symmetric), -1 (antisymmetric), or a symbol h (no symmetry; h is the opposite operation, gi[x, y] = h[y, x]); {si, d} gives the generator the degree d. A relation is a linear combination of LBasis[tree] with trees on the inputs 1, 2, 3; its images under the symmetric group are added. Options: \"Name\", and \"Order\", a function from trees to numbers that selects the normal forms (trees with smaller values are eliminated first). The result has the keys \"Generators\", \"Spec\", \"Relations\", and \"Elements\", \"Compose\", \"Unit\", \"Degree\", \"Action\", so that DGOperadCheck applies to it.";

ShuffleTrees::usage = "ShuffleTrees[op, n] lists the shuffle trees with inputs 1, ..., n in the generators of the presented operad op: a basis of the free symmetric operad in arity n. ShuffleTrees[op, labels] uses the given labels, and ShuffleTrees[{g1, ...}, n] the given generators.";

ShuffleTreeQ::usage = "ShuffleTreeQ[t] gives True if, at every vertex of the labelled tree t, the smallest leaf of the left child is smaller than the smallest leaf of the right child.";

ShuffleNormalize::usage = "ShuffleNormalize[op, expr] rewrites a linear combination of labelled trees in terms of shuffle trees, using the symmetry of the generators of op and the Koszul sign rule. No relation of op is used.";

PresentedCompose::usage = "PresentedCompose[op][u, i, v] gives the partial composition u o_i v of linear combinations of labelled trees in the free symmetric operad on the generators of op: v is plugged into the input i of u, the inputs are renumbered, and the Koszul sign is included. Apply OperadReduce to pass to the quotient.";

PresentedAct::usage = "PresentedAct[op][u, s] gives the right action of the permutation s = {s(1), ..., s(n)} on a linear combination u of labelled trees: (u . s)(x1, ..., xn) = u(x_{s^-1(1)}, ..., x_{s^-1(n)}).";

OperadIdealBasis::usage = "OperadIdealBasis[op, n] gives a basis, in reduced row echelon form, of the arity-n part of the ideal generated by the relations of the presented operad op.";

OperadBasis::usage = "OperadBasis[op, n] gives the shuffle trees that are the normal forms of the presented operad op in arity n: a basis of op(n).";

OperadDimension::usage = "OperadDimension[op, n] gives the dimension of the arity-n part of the presented operad op.";

OperadDimensionsByDegree::usage = "OperadDimensionsByDegree[op, n] gives the Association degree -> dimension of the arity-n part of the presented operad op.";

OperadDimensionsByGenerator::usage = "OperadDimensionsByGenerator[op, n, g] gives the list of the dimensions of the parts of op(n) with 0, 1, ..., n - 1 vertices labelled by the generator g. The relations must preserve the number of such vertices.";

OperadReduce::usage = "OperadReduce[op, expr] gives the normal form in the presented operad op of a linear combination of labelled trees with inputs 1, ..., n. Two expressions are equal in op exactly if their normal forms agree.";

OperadZeroQ::usage = "OperadZeroQ[op, expr] gives True if the linear combination expr of labelled trees is zero in the presented operad op, that is, if it is an identity that follows from the relations.";

OperadMorphismImage::usage = "OperadMorphismImage[q, {g1 -> u1, ...}][expr] applies to a linear combination of labelled trees the map that sends each generator gi to ui, a linear combination of trees of the presented operad q with inputs 1 and 2 and of the degree of gi.";

OperadMorphismQ::usage = "OperadMorphismQ[p, q, {g1 -> u1, ...}] gives True if sending the generators gi of the presented operad p to the elements ui of q defines a morphism of operads: the images have the degrees and the symmetry of the generators, and every relation of p becomes zero in q.";

OpAssWord::usage = "OpAssWord[t] gives the word of a tree in OpAss and OpAssOp: the list of its inputs in the order in which they are multiplied.";

PresentedCommutativeOperad::usage = "PresentedCommutativeOperad[] gives the commutative operad, presented by the symmetric generator OpCom and associativity.";

PresentedAssociativeOperad::usage = "PresentedAssociativeOperad[] gives the associative operad as a symmetric operad, presented by the generators OpAss and OpAssOp and associativity. Its normal forms are the left-normed words.";

LieOperad::usage = "LieOperad[] gives the Lie operad, presented by the antisymmetric generator OpLie and the Jacobi relation. Its normal forms are the left-normed brackets [[[1, a], b], ...].";

PoissonOperad::usage = "PoissonOperad[n] gives the operad P_n: a commutative product OpCom of degree 0 and a bracket OpLie of degree n - 1 that satisfies the Jacobi relation and is a derivation of the product. PoissonOperad[] = PoissonOperad[1] is the Poisson operad, PoissonOperad[2] the Gerstenhaber operad; for n >= 2, P_n is the homology of the little n-cubes operad. The normal forms are the products of left-normed brackets.";

GerstenhaberOperad::usage = "GerstenhaberOperad[] gives the Gerstenhaber operad PoissonOperad[2], the homology of the little 2-cubes operad: a commutative product and a bracket of degree 1.";

KoszulSeriesQ::usage = "KoszulSeriesQ[p, q] gives True if the lists p = {dim P(1), dim P(2), ...} and q satisfy f_P(-f_Q(-x)) = x to the order of the shorter list, where f(x) is the sum of dim(n) x^n / n!. This holds if P is a Koszul operad with dimensions p and Q its Koszul dual.";

Begin["`Private`"];

(* ---------------------------------------------------------------------- *)
(* labelled trees                                                         *)
(* ---------------------------------------------------------------------- *)

treeLeaves[t_Integer] := {t};
treeLeaves[_[a_, b_]] := Join[treeLeaves[a], treeLeaves[b]];

treeMin[t_] := Min[treeLeaves[t]];

(* spec is an Association  generator -> {sign, partner, degree} *)

treeDeg[spec_][t_Integer] := 0;
treeDeg[spec_][h_[a_, b_]] := Lookup[spec, Key[h]][[3]] + treeDeg[spec][a] + treeDeg[spec][b];

labelledTreeQ[spec_][t_Integer] := Positive[t];
labelledTreeQ[spec_][h_[a_, b_]] :=
  KeyExistsQ[spec, h] && labelledTreeQ[spec][a] && labelledTreeQ[spec][b];
labelledTreeQ[spec_][_] := False;

wellLabelledQ[spec_][t_] := TrueQ[labelledTreeQ[spec][t]] && DuplicateFreeQ[treeLeaves[t]];

ShuffleTreeQ[t_Integer] := True;
ShuffleTreeQ[_[a_, b_]] := TrueQ[ShuffleTreeQ[a] && ShuffleTreeQ[b] && treeMin[a] < treeMin[b]];
ShuffleTreeQ[_] := False;

(* {sign, shuffle tree} *)
normTree[spec_][t_Integer] := {1, t};
normTree[spec_][h_[a_, b_]] :=
  Module[{na = normTree[spec][a], nb = normTree[spec][b], swap},
    If[treeMin[na[[2]]] < treeMin[nb[[2]]],
      {na[[1]] nb[[1]], h[na[[2]], nb[[2]]]},
      swap = Lookup[spec, Key[h]];
      {
        na[[1]] nb[[1]] swap[[1]] (-1)^(treeDeg[spec][na[[2]]] treeDeg[spec][nb[[2]]]),
        swap[[2]][nb[[2]], na[[2]]]
      }
    ]
  ];

normLinear[spec_][expr_] :=
  LinearCollect[
    Total[
      Map[
        Function[tm, With[{nt = normTree[spec][tm[[2]]]}, tm[[1]] nt[[1]] LBasis[nt[[2]]]]],
        LinearTerms[expr]
      ]
    ]
  ];

(* the degree of the vertices of t after the leaf k in preorder; None if k is not a leaf of t *)
degAfter[spec_][t_Integer, k_] := If[t === k, 0, None];
degAfter[spec_][_[a_, b_], k_] :=
  With[{ra = degAfter[spec][a, k]},
    If[ra === None, degAfter[spec][b, k], ra + treeDeg[spec][b]]
  ];

(* {sign, t with x at the leaf k} *)
graft[spec_][t_, k_Integer, x_] :=
  With[{dx = treeDeg[spec][x]},
    {If[EvenQ[dx], 1, (-1)^degAfter[spec][t, k]], t /. k -> x}
  ];

(* t(x1, .., xm) for a tree t on the leaves 1..m: graft at 1, then at 2, ...
   The leaves of t are first renamed -1, .., -m, so that they cannot be
   confused with the leaves of the xj. *)
plug[spec_][t_, xs_List] :=
  Module[{cur = t /. j_Integer :> -j, sign = 1, gr, k},
    Do[
      gr = graft[spec][cur, -k, xs[[k]]];
      sign = sign gr[[1]];
      cur = gr[[2]],
      {k, 1, Length[xs]}
    ];
    {sign, cur}
  ];


(* ---------------------------------------------------------------------- *)
(* shuffle trees                                                          *)
(* ---------------------------------------------------------------------- *)

(* labels must be sorted.  The splits are listed by the size of the left
   part, and for equal sizes in reverse lexicographic order, so that the
   last split is {1, .., n-1} | {n}. *)
shuffleTrees[gens_List, {x_Integer}] := {x};
shuffleTrees[gens_List, labels_List] := shuffleTrees[gens, labels] =
  With[{first = First[labels], rest = Rest[labels]},
    Flatten[
      Table[
        With[{left = Prepend[extra, first], right = Complement[rest, extra]},
          Table[
            g[ta, tb],
            {g, gens}, {ta, shuffleTrees[gens, left]}, {tb, shuffleTrees[gens, right]}
          ]
        ],
        {size, 0, Length[rest] - 1}, {extra, Reverse[Subsets[rest, {size}]]}
      ]
    ]
  ];

ShuffleTrees[op_Association, n_Integer?Positive] := shuffleTrees[op["Generators"], Range[n]];
ShuffleTrees[op_Association, labels_List] := shuffleTrees[op["Generators"], Sort[labels]];
ShuffleTrees[gens_List, n_Integer?Positive] := shuffleTrees[gens, Range[n]];
ShuffleTrees[gens_List, labels_List] := shuffleTrees[gens, Sort[labels]];

ShuffleNormalize::tree = "`1` is not a tree in the generators `2` with distinct positive integers as inputs.";

ShuffleNormalize[op_Association, expr_] :=
  With[{spec = op["Spec"], tms = LinearTerms[expr]},
    With[{bad = Select[tms, Function[tm, ! wellLabelledQ[spec][tm[[2]]]]]},
      If[bad === {},
        normLinear[spec][expr],
        Message[ShuffleNormalize::tree, bad[[1, 2]], Keys[spec]]; $Failed
      ]
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* presentations                                                          *)
(* ---------------------------------------------------------------------- *)

oneGenerator[Rule[g_Symbol, s : (1 | -1 | _Symbol)]] := oneGenerator[g -> {s, 0}];
oneGenerator[g_Symbol -> {1, d_Integer}] := {g -> {1, g, d}};
oneGenerator[g_Symbol -> {-1, d_Integer}] := {g -> {-1, g, d}};
oneGenerator[g_Symbol -> {h_Symbol, d_Integer}] := {g -> {1, h, d}, h -> {1, g, d}};
oneGenerator[_] := {$Failed};

generatorSpec[gens_List] :=
  With[{entries = Flatten[Map[oneGenerator, gens], 1]},
    If[MemberQ[entries, $Failed],
      $Failed,
      Association[DeleteDuplicatesBy[entries, First]]
    ]
  ];

relationQ[spec_][rel_] :=
  With[{tms = LinearTerms[rel]},
    tms =!= {} &&
      AllTrue[tms, Function[tm, wellLabelledQ[spec][tm[[2]]] && Sort[treeLeaves[tm[[2]]]] === {1, 2, 3}]] &&
      Length[Union[Map[Function[tm, treeDeg[spec][tm[[2]]]], tms]]] === 1
  ];

(* the images of a relation under the six permutations of its inputs *)
relationOrbit[spec_][rel_] :=
  DeleteCases[
    DeleteDuplicates[
      Map[
        Function[perm,
          normLinear[spec][
            Total[
              Map[
                Function[tm,
                  tm[[1]] LBasis[tm[[2]] /. {1 -> perm[[1]], 2 -> perm[[2]], 3 -> perm[[3]]}]
                ],
                LinearTerms[rel]
              ]
            ]
          ]
        ],
        Permutations[{1, 2, 3}]
      ]
    ],
    0
  ];

(* the part of an operad object that determines the quotient; it is the key of the cache *)
coreKeys = {"Generators", "Spec", "Relations", "Order"};
coreOf[op_Association] := KeyTake[op, coreKeys];

PresentedOperad::gens = "`1` is not a list of generators g -> 1, g -> -1, g -> h or g -> {.., degree}.";
PresentedOperad::rel = "`1` is not a homogeneous linear combination of LBasis[tree] with trees in the generators on the inputs 1, 2, 3.";

Options[PresentedOperad] = {"Name" -> "Presented", "Order" -> None};

PresentedOperad[gens_List, relations_List, OptionsPattern[]] :=
  Module[{spec = generatorSpec[gens], bad, core},
    If[spec === $Failed,
      Message[PresentedOperad::gens, gens]; $Failed,
      bad = Select[relations, Function[r, ! TrueQ[Quiet[relationQ[spec][r]]]]];
      If[bad =!= {},
        Message[PresentedOperad::rel, First[bad]]; $Failed,
        core = <|
          "Generators" -> Keys[spec],
          "Spec" -> spec,
          "Relations" -> Flatten[Map[relationOrbit[spec], relations]],
          "Order" -> OptionValue["Order"]
        |>;
        With[{c = core, sp = spec},
          Join[
            <|"Name" -> OptionValue["Name"]|>,
            c,
            <|
              "GivenRelations" -> relations,
              "Linear" -> True,
              "Elements" -> Function[n, OperadBasis[c, n]],
              "Degree" -> treeDeg[sp],
              "Compose" -> Function[{a, i, b}, OperadReduce[c, composeTree[sp][a, i, b]]],
              "Action" -> Function[{a, s}, OperadReduce[c, LBasis[actTree[a, s]]]],
              "Unit" -> 1
            |>
          ]
        ]
      ]
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* the ideal of relations                                                 *)
(* ---------------------------------------------------------------------- *)

(* the partitions of the sorted list s into three non-empty parts, ordered by their smallest elements *)
orderedTriples[s_List] :=
  With[{first = First[s], rest = Rest[s]},
    Select[
      Map[
        Function[assign,
          {Prepend[Pick[rest, assign, 0], first], Pick[rest, assign, 1], Pick[rest, assign, 2]}
        ],
        Tuples[{0, 1, 2}, Length[rest]]
      ],
      Function[parts, parts[[2]] =!= {} && parts[[3]] =!= {} && Min[parts[[2]]] < Min[parts[[3]]]]
    ]
  ];

(* spanning vectors of the ideal in arity n, as lists of {coefficient, shuffle tree} *)
idealRows[core_Association, n_Integer] :=
  Module[{spec = core["Spec"], gens = core["Generators"], rels, labels = Range[n],
      sown, ms, contexts, block, subset, parts, tx, ty, tz, rel, ctx},
    rels = Map[LinearTerms, core["Relations"]];
    If[n < 3 || rels === {},
      {},
      sown = Last[
        Reap[
          Do[
            ms = First[subset];
            contexts = shuffleTrees[gens, Sort[Append[Complement[labels, subset], ms]]];
            Do[
              block = Map[
                Function[tm,
                  With[{pl = plug[spec][tm[[2]], {tx, ty, tz}]}, {tm[[1]] pl[[1]], pl[[2]]}]
                ],
                rel
              ];
              Do[
                Sow[
                  Map[
                    Function[tm,
                      With[{gr = graft[spec][ctx, ms, tm[[2]]]}, {tm[[1]] gr[[1]], gr[[2]]}]
                    ],
                    block
                  ]
                ],
                {ctx, contexts}
              ],
              {parts, orderedTriples[subset]},
              {tx, shuffleTrees[gens, parts[[1]]]},
              {ty, shuffleTrees[gens, parts[[2]]]},
              {tz, shuffleTrees[gens, parts[[3]]]},
              {rel, rels}
            ],
            {subset, Subsets[labels, {3, n}]}
          ]
        ]
      ];
      If[sown === {}, {}, First[sown]]
    ]
  ];

(* the shuffle trees of arity n in the order used for elimination *)
orderedTrees[core_Association, n_Integer] :=
  With[{ts = shuffleTrees[core["Generators"], Range[n]], key = core["Order"]},
    If[key === None,
      ts,
      ts[[Ordering[Table[{key[ts[[j]]], j}, {j, 1, Length[ts]}]]]]
    ]
  ];

(* the vector of a list of {coefficient, tree} *)
termVector[index_Association, len_Integer][tms_List] :=
  Module[{vec = ConstantArray[0, len]},
    Scan[
      Function[tm,
        With[{j = Lookup[index, Key[tm[[2]]]]}, vec[[j]] = vec[[j]] + tm[[1]]]
      ],
      tms
    ];
    vec
  ];

idealData[core_Association, n_Integer] := idealData[core, n] =
  Module[{trees = orderedTrees[core, n], index, rows, reduced},
    index = AssociationThread[trees, Range[Length[trees]]];
    rows = DeleteDuplicates[Map[termVector[index, Length[trees]], idealRows[core, n]]];
    reduced = If[rows === {}, {}, DeleteCases[RowReduce[rows], {0 ..}]];
    <|
      "Trees" -> trees,
      "Index" -> index,
      "Rows" -> reduced,
      "Pivots" -> Map[Function[row, First[FirstPosition[row, 1]]], reduced]
    |>
  ];

OperadIdealBasis[op_Association, n_Integer?Positive] :=
  With[{data = idealData[coreOf[op], n]},
    With[{basis = Map[LBasis, data["Trees"]]},
      Map[Function[row, row . basis], data["Rows"]]
    ]
  ];

OperadBasis[op_Association, n_Integer?Positive] :=
  With[{data = idealData[coreOf[op], n]},
    data["Trees"][[Complement[Range[Length[data["Trees"]]], data["Pivots"]]]]
  ];

OperadDimension[op_Association, n_Integer?Positive] := Length[OperadBasis[op, n]];

OperadDimensionsByDegree[op_Association, n_Integer?Positive] :=
  KeySort[Counts[Map[treeDeg[op["Spec"]], OperadBasis[op, n]]]];

OperadDimensionsByGenerator[op_Association, n_Integer?Positive, g_Symbol] :=
  With[{counts = Map[Function[t, Count[t, Blank[g], {0, Infinity}]], OperadBasis[op, n]]},
    Table[Count[counts, k], {k, 0, n - 1}]
  ];


OperadReduce::leaves = "The trees in `1` do not all have the inputs 1, ..., n, each exactly once.";

OperadReduce[op_Association, expr_] :=
  Module[{normal = ShuffleNormalize[op, expr], tms, n, data, vec},
    Which[
      normal === $Failed,
        $Failed,
      normal === 0,
        0,
      True,
        tms = LinearTerms[normal];
        n = Length[treeLeaves[tms[[1, 2]]]];
        If[! AllTrue[tms, Function[tm, Sort[treeLeaves[tm[[2]]]] === Range[n]]],
          Message[OperadReduce::leaves, expr]; $Failed,
          data = idealData[coreOf[op], n];
          vec = termVector[data["Index"], Length[data["Trees"]]][tms];
          If[data["Pivots"] =!= {},
            vec = Expand[vec - vec[[data["Pivots"]]] . data["Rows"]]
          ];
          LinearCollect[vec . Map[LBasis, data["Trees"]]]
        ]
    ]
  ];

OperadZeroQ[op_Association, expr_] := OperadReduce[op, expr] === 0;


(* ---------------------------------------------------------------------- *)
(* composition and the action of the symmetric groups                     *)
(* ---------------------------------------------------------------------- *)

(* a o_i b for labelled trees a and b, as a linear combination *)
composeTree[spec_][a_, i_Integer, b_] :=
  Module[{k = Length[treeLeaves[b]], a2, b2, gr},
    a2 = a /. j_Integer :> If[j <= i, j, j + k - 1];
    b2 = b /. j_Integer :> j + i - 1;
    gr = graft[spec][a2, i, b2];
    gr[[1]] LBasis[gr[[2]]]
  ];

PresentedCompose[op_Association][u_, i_Integer, v_] :=
  With[{spec = op["Spec"]},
    normLinear[spec][
      BilinearExtend[Function[{x, y}, composeTree[spec][x, i, y]]][u, v]
    ]
  ];

actTree[t_, s_List] := With[{inv = Ordering[s]}, t /. j_Integer :> inv[[j]]];

PresentedAct[op_Association][u_, s_List] :=
  normLinear[op["Spec"]][LinearExtend[Function[t, LBasis[actTree[t, s]]]][u]];


(* ---------------------------------------------------------------------- *)
(* morphisms                                                              *)
(* ---------------------------------------------------------------------- *)

morphTree[qspec_, images_][t_Integer] := LBasis[t];
morphTree[qspec_, images_][h_[a_, b_]] :=
  With[{
      ih = LinearTerms[Lookup[images, Key[h], 0]],
      ia = LinearTerms[morphTree[qspec, images][a]],
      ib = LinearTerms[morphTree[qspec, images][b]]
    },
    LinearCollect[
      Total[
        Flatten[
          Table[
            With[{pl = plug[qspec][th[[2]], {ta[[2]], tb[[2]]}]},
              th[[1]] ta[[1]] tb[[1]] pl[[1]] LBasis[pl[[2]]]
            ],
            {th, ih}, {ta, ia}, {tb, ib}
          ]
        ]
      ]
    ]
  ];

OperadMorphismImage[q_Association, images_][expr_] :=
  LinearExtend[morphTree[q["Spec"], Association[images]]][expr];

OperadMorphismQ[p_Association, q_Association, images_] :=
  Module[{im = Association[images], pspec = p["Spec"], qspec = q["Spec"], gens},
    gens = Keys[pspec];
    (* every generator has an image, a combination of trees of q on the inputs 1, 2 *)
    AllTrue[gens,
      Function[g,
        KeyExistsQ[im, g] &&
          AllTrue[LinearTerms[Lookup[im, Key[g]]],
            Function[tm,
              wellLabelledQ[qspec][tm[[2]]] && Sort[treeLeaves[tm[[2]]]] === {1, 2} &&
                treeDeg[qspec][tm[[2]]] === Lookup[pspec, Key[g]][[3]]
            ]
          ]
      ]
    ] &&
    (* the images have the symmetry of the generators *)
    AllTrue[gens,
      Function[g,
        With[{swap = Lookup[pspec, Key[g]]},
          LinearZeroQ[
            PresentedAct[q][Lookup[im, Key[g]], {2, 1}] -
              swap[[1]] normLinear[qspec][Lookup[im, Key[swap[[2]]]]]
          ]
        ]
      ]
    ] &&
    (* the relations go to zero *)
    AllTrue[p["Relations"],
      Function[r, OperadZeroQ[q, OperadMorphismImage[q, im][r]]]
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* the standard operads                                                   *)
(* ---------------------------------------------------------------------- *)

comAssociativity = LBasis[OpCom[OpCom[1, 2], 3]] - LBasis[OpCom[1, OpCom[2, 3]]];

assAssociativity = LBasis[OpAss[OpAss[1, 2], 3]] - LBasis[OpAss[1, OpAss[2, 3]]];

jacobiRelation =
  LBasis[OpLie[OpLie[1, 2], 3]] + LBasis[OpLie[OpLie[2, 3], 1]] + LBasis[OpLie[OpLie[3, 1], 2]];

(* the bracket with x3 is a derivation of the product *)
leibnizRelation =
  LBasis[OpLie[OpCom[1, 2], 3]] - LBasis[OpCom[1, OpLie[2, 3]]] - LBasis[OpCom[OpLie[1, 3], 2]];

(* write OpAssOp[a, b] as OpAss[b, a]: a planar tree in OpAss alone *)
assPlanar[t_Integer] := t;
assPlanar[OpAss[a_, b_]] := OpAss[assPlanar[a], assPlanar[b]];
assPlanar[OpAssOp[a_, b_]] := OpAss[assPlanar[b], assPlanar[a]];

OpAssWord[t_] := treeLeaves[assPlanar[t]];

(* the number of vertices of a planar tree whose right child is not a leaf *)
notLeftComb[t_Integer] := 0;
notLeftComb[_[a_, b_]] := If[IntegerQ[b], 0, 1] + notLeftComb[a] + notLeftComb[b];

(* the number of pairs (a vertex with head top, a vertex with head bottom below it) *)
countBelow[top_, bottom_][t_Integer] := 0;
countBelow[top_, bottom_][h_[a_, b_]] :=
  If[h === top,
    Count[a, Blank[bottom], {0, Infinity}] + Count[b, Blank[bottom], {0, Infinity}],
    0
  ] + countBelow[top, bottom][a] + countBelow[top, bottom][b];

(* normal forms: left-normed words *)
assOrder = Function[t, -notLeftComb[assPlanar[t]]];

(* normal forms: no product below a bracket *)
poissonOrder = Function[t, -countBelow[OpLie, OpCom][t]];

PresentedCommutativeOperad[] :=
  PresentedOperad[{OpCom -> 1}, {comAssociativity}, "Name" -> "Com"];

PresentedAssociativeOperad[] :=
  PresentedOperad[{OpAss -> OpAssOp}, {assAssociativity}, "Name" -> "Ass", "Order" -> assOrder];

LieOperad[] := PresentedOperad[{OpLie -> -1}, {jacobiRelation}, "Name" -> "Lie"];

PoissonOperad[] := PoissonOperad[1];

PoissonOperad[n_Integer?Positive] :=
  PresentedOperad[
    {OpCom -> 1, OpLie -> {(-1)^n, n - 1}},
    {comAssociativity, jacobiRelation, leibnizRelation},
    "Name" -> Which[n === 1, "Poisson", n === 2, "Gerstenhaber", True, "P" <> ToString[n]],
    "Order" -> poissonOrder
  ];

GerstenhaberOperad[] := PoissonOperad[2];


(* ---------------------------------------------------------------------- *)
(* generating series                                                      *)
(* ---------------------------------------------------------------------- *)

KoszulSeriesQ[p_List, q_List] :=
  Module[{order = Min[Length[p], Length[q]], x, fp, fq, comp, n},
    fq = Total[Table[q[[n]] (-x)^n / n!, {n, 1, order}]];
    fp = Total[Table[p[[n]] (-fq)^n / n!, {n, 1, order}]];
    comp = Expand[fp];
    Table[Coefficient[comp, x, n], {n, 1, order}] === UnitVector[order, 1]
  ];

End[];

EndPackage[];
