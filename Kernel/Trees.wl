(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Trees`                                                       *)
(*                                                                        *)
(*  Planar rooted trees = elements of the free nonsymmetric operad.        *)
(*  A tree is OpLeaf or h[t1, ..., tk] with an inert head h.               *)
(*  Mathematica expressions ARE trees; grafting is ReplacePart.           *)
(*                                                                        *)
(*  Layer: operad.  Depends on: nothing.                                  *)
(* ====================================================================== *)

BeginPackage["Operadica`Trees`"];

OpLeaf::usage = "OpLeaf is an input slot of a planar tree. A tree is either OpLeaf or h[t1, ..., tk], where h is an inert head (a generating operation) and t1, ..., tk are trees.";

OpTreeQ::usage = "OpTreeQ[t] gives True if t is a planar tree built from OpLeaf and inert heads.";

OpLeafPositions::usage = "OpLeafPositions[t] gives the positions of the leaves of the tree t, from left to right.";

OpArity::usage = "OpArity[t] gives the number of leaves (inputs) of the tree t.";

OpSubtree::usage = "OpSubtree[t, pos] gives the subtree of t at the position pos (a list of indices; {} is the root).";

OpReplaceSubtree::usage = "OpReplaceSubtree[t, pos, new] replaces the subtree of t at the position pos by new.";

OpCompose::usage = "OpCompose[s, i, t] gives the partial composition of trees: t is grafted onto the i-th leaf of s.";

OpComposeAll::usage = "OpComposeAll[s, {t1, ..., tn}] grafts t1, ..., tn onto the n leaves of s simultaneously (full operadic composition).";

OpCorolla::usage = "OpCorolla[h, n] gives the tree h[OpLeaf, ..., OpLeaf] with n leaves.";

OpPlanarTrees::usage = "OpPlanarTrees[{h1 -> k1, h2 -> k2, ...}, n] lists all planar trees with n leaves built from generators hi of arity ki >= 2. This is a basis of the arity-n part of the free nonsymmetric operad.";

OpEvaluate::usage = "OpEvaluate[t, {h1 -> f1, ...}, {x1, ..., xn}] interprets the tree t as an n-ary function, replacing each generator hi by the function fi, and applies it to x1, ..., xn.";

OpTreePlot::usage = "OpTreePlot[t] draws the tree t.";

Begin["`Private`"];

OpTreeQ[OpLeaf] = True;
OpTreeQ[_?AtomQ] = False;
OpTreeQ[_[args___]] := AllTrue[{args}, OpTreeQ];


OpLeafPositions[t_] := Position[t, OpLeaf, {0, Infinity}, Heads -> False];

OpArity[t_] := Length[OpLeafPositions[t]];


(* ReplacePart[expr, {} -> new] leaves expr unchanged and Extract[expr, {}]
   gives {}, so the root position {} needs its own rules. *)
OpSubtree[t_, {}] := t;
OpSubtree[t_, pos_List] := Extract[t, pos];

OpReplaceSubtree[t_, {}, new_] := new;
OpReplaceSubtree[t_, pos_List, new_] := ReplacePart[t, pos -> new];


OpCompose::arity = "Cannot graft onto input `1` of a tree with `2` inputs.";

OpCompose[s_, i_Integer, t_] :=
  Module[{pos = OpLeafPositions[s]},
    If[1 <= i <= Length[pos],
      OpReplaceSubtree[s, pos[[i]], t],
      Message[OpCompose::arity, i, Length[pos]]; $Failed
    ]
  ];


OpComposeAll::arity = "The tree has `1` inputs but `2` trees were given.";

OpComposeAll[s_, ts_List] :=
  Module[{pos = OpLeafPositions[s]},
    Which[
      Length[pos] =!= Length[ts],
        Message[OpComposeAll::arity, Length[pos], Length[ts]]; $Failed,
      pos === {},
        s,
      pos === {{}},
        First[ts],
      True,
        ReplacePart[s, MapThread[Rule, {pos, ts}]]
    ]
  ];


OpCorolla[h_, n_Integer?NonNegative] := h @@ ConstantArray[OpLeaf, n];


(* ordered k-tuples of positive integers with sum n *)
compositions[n_Integer, k_Integer] :=
  Flatten[Permutations /@ IntegerPartitions[n, {k}], 1];

OpPlanarTrees::gens = "Generators must be given as {h1 -> k1, ...} with integer arities ki >= 2; got `1`.";

OpPlanarTrees[gens_, n_Integer?Positive] :=
  Module[{g = List @@@ Normal[gens]},
    If[ListQ[g] && AllTrue[g, MatchQ[#, {_, k_Integer /; k >= 2}] &],
      planarTrees[g, n],
      Message[OpPlanarTrees::gens, gens]; $Failed
    ]
  ];

planarTrees[g_List, 1] := {OpLeaf};

planarTrees[g_List, n_Integer] := planarTrees[g, n] =
  Join @@ Table[
    With[{h = gen[[1]], k = gen[[2]]},
      Join @@ Table[
        h @@@ Tuples[planarTrees[g, #] & /@ comp],
        {comp, compositions[n, k]}
      ]
    ],
    {gen, g}
  ];


OpEvaluate::arity = "The tree has `1` inputs but `2` arguments were given.";

(* The generators are replaced inside Hold, the arguments are inserted at the
   leaf positions, and only then is the expression released.  The rules
   therefore never touch the arguments. *)
OpEvaluate[t_, rules_, args_List] :=
  Module[{pos = OpLeafPositions[t], held},
    If[Length[pos] =!= Length[args],
      Message[OpEvaluate::arity, Length[pos], Length[args]]; $Failed,
      held = Hold[t] /. rules;
      ReleaseHold[
        ReplacePart[held, MapThread[Rule, {Prepend[#, 1] & /@ pos, args}]]
      ]
    ]
  ];


OpTreePlot[t_] := TreeForm[t];

End[];

EndPackage[];
