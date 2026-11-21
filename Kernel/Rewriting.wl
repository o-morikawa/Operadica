(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Rewriting`                                                   *)
(*                                                                        *)
(*  Quotients of free operads by rewriting.                                *)
(*  A relation is oriented into a rule, e.g. associativity                *)
(*      m[m[a_, b_], c_] :> m[a, m[b, c]]                                 *)
(*  Mathematica's pattern matcher applies it at any subtree.  If the      *)
(*  system terminates and is locally confluent, every tree has a unique   *)
(*  normal form, and the normal forms are a basis of the quotient.        *)
(*                                                                        *)
(*  Layer: operad.  Depends on: Trees.                                    *)
(* ====================================================================== *)

BeginPackage["Operadica`Rewriting`", {"Operadica`Trees`"}];

OpNormalForm::usage = "OpNormalForm[t, rules] rewrites the tree t with the given rules, at any subtree, until no rule applies.";

OpRewriteSteps::usage = "OpRewriteSteps[t, rules] lists all trees obtained from t by applying one rule at one subtree.";

OpLocallyConfluentQ::usage = "OpLocallyConfluentQ[gens, rules, maxArity] gives True if, for every tree with at most maxArity leaves, all one-step rewrites have the same normal form. For a terminating system whose critical pairs live in arity at most maxArity this proves confluence in all arities.";

QuotientOperad::usage = "QuotientOperad[gens, rules] gives the operad whose elements are the normal forms of trees under the rewriting rules; composition is grafting followed by normalization.";

Begin["`Private`"];

OpNormalForm[t_, rules_] := t //. rules;


OpRewriteSteps[t_, rules_] :=
  DeleteDuplicates[
    Join @@ Map[
      Function[pos,
        With[{sub = OpSubtree[t, pos]},
          Map[Function[new, OpReplaceSubtree[t, pos, new]], ReplaceList[sub, rules]]
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

End[];

EndPackage[];
