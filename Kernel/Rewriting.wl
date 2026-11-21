(* ::Package:: *)

(* ====================================================================== *)
(*  Quotients of free operads by rewriting                                 *)
(*                                                                        *)
(*  A relation is oriented into a rule, e.g. associativity                *)
(*      m[m[a_, b_], c_] :> m[a, m[b, c]]                                 *)
(*  Mathematica's pattern matcher applies it at any subtree.  If the      *)
(*  system terminates and is locally confluent, every tree has a unique   *)
(*  normal form, and the normal forms are a basis of the quotient.        *)
(*                                                                        *)
(*  This file is read by Operadica.wl inside Operadica`Private`.          *)
(* ====================================================================== *)

OpNormalForm[t_, rules_] := t //. rules;


OpRewriteSteps[t_, rules_] :=
  DeleteDuplicates[
    Join @@ Map[
      Function[pos,
        With[{sub = opExtractAt[t, pos]},
          Map[Function[new, opReplaceAt[t, pos, new]], ReplaceList[sub, rules]]
        ]
      ],
      Position[t, _, {0, Infinity}, Heads -> False]
    ]
  ];


OpLocallyConfluentQ[gens_, rules_, maxArity_Integer?Positive] :=
  AllTrue[
    Join @@ Table[OpPlanarTrees[gens, n], {n, 1, maxArity}],
    Function[t,
      Length[Union[Map[Function[u, OpNormalForm[u, rules]], OpRewriteSteps[t, rules]]]] <= 1
    ]
  ];


QuotientOperad[gens_, rules_] :=
  <|
    "Name" -> "Quotient",
    "Generators" -> gens,
    "Rules" -> rules,
    "Elements" -> Function[n,
      Union[Map[Function[u, OpNormalForm[u, rules]], OpPlanarTrees[gens, n]]]
    ],
    "Compose" -> Function[{x, i, y}, OpNormalForm[OpCompose[x, i, y], rules]],
    "Unit" -> OpLeaf
  |>;
