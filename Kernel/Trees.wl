(* ::Package:: *)

(* ====================================================================== *)
(*  Planar rooted trees = elements of the free nonsymmetric operad         *)
(*                                                                        *)
(*  A tree is OpLeaf or h[t1, ..., tk] with an inert head h.               *)
(*  Mathematica expressions ARE trees; grafting is ReplacePart.           *)
(*                                                                        *)
(*  This file is read by Operadica.wl inside Operadica`Private`.          *)
(* ====================================================================== *)

OpTreeQ[OpLeaf] = True;
OpTreeQ[_?AtomQ] = False;
OpTreeQ[_[args___]] := AllTrue[{args}, OpTreeQ];


OpLeafPositions[t_] := Position[t, OpLeaf, {0, Infinity}, Heads -> False];

OpArity[t_] := Length[OpLeafPositions[t]];


(* ReplacePart[expr, {} -> new] leaves expr unchanged, so the root position
   {} needs its own rule. *)
opReplaceAt[t_, {}, new_] := new;
opReplaceAt[t_, pos_List, new_] := ReplacePart[t, pos -> new];

opExtractAt[t_, {}] := t;
opExtractAt[t_, pos_List] := Extract[t, pos];


OpCompose::arity = "Cannot graft onto input `1` of a tree with `2` inputs.";

OpCompose[s_, i_Integer, t_] :=
  Module[{pos = OpLeafPositions[s]},
    If[1 <= i <= Length[pos],
      opReplaceAt[s, pos[[i]], t],
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
opCompositions[n_Integer, k_Integer] :=
  Flatten[Permutations /@ IntegerPartitions[n, {k}], 1];

OpPlanarTrees::gens = "Generators must be given as {h1 -> k1, ...} with integer arities ki >= 2; got `1`.";

OpPlanarTrees[gens_, n_Integer?Positive] :=
  Module[{g = List @@@ Normal[gens]},
    If[ListQ[g] && AllTrue[g, MatchQ[#, {_, k_Integer /; k >= 2}] &],
      opPlanarTrees[g, n],
      Message[OpPlanarTrees::gens, gens]; $Failed
    ]
  ];

opPlanarTrees[g_List, 1] := {OpLeaf};

opPlanarTrees[g_List, n_Integer] := opPlanarTrees[g, n] =
  Join @@ Table[
    With[{h = gen[[1]], k = gen[[2]]},
      Join @@ Table[
        h @@@ Tuples[opPlanarTrees[g, #] & /@ comp],
        {comp, opCompositions[n, k]}
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
