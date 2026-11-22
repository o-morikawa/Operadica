(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Bridge`                                                      *)
(*                                                                        *)
(*  Statements that connect the layers, each one checked by computation.   *)
(*                                                                        *)
(*   operad <-> lattice                                                    *)
(*     CupAlgebraOverAsQ      cochains with the cup product are an algebra *)
(*                            over the associative operad                  *)
(*     EInfinityArityTwoQ     the higher cup products are the action of    *)
(*                            the arity-2 part of an E-infinity operad;    *)
(*                            cup_i lies in the E_(i+1) stage              *)
(*                                                                        *)
(*   operad <-> operad: geometry and algebra                               *)
(*     LittleCubesHomologyQ   the Betti numbers of the space C_n(k) of k   *)
(*                            little n-cubes are the dimensions of the     *)
(*                            operad P_n in arity k (for n = 2 the         *)
(*                            Gerstenhaber operad): H_*(E_n) = P_n         *)
(*     BarrattEcclesHomologyQ the same for the stage F_n of the            *)
(*                            Barratt-Eccles operad, a combinatorial E_n   *)
(*                            operad; it reaches larger n and k            *)
(*                                                                        *)
(*   operad <-> category                                                   *)
(*     MacLaneCoherenceQ      the pentagon equation is the confluence of   *)
(*                            the associativity rewriting with phases:     *)
(*                            reassociation phases do not depend on the    *)
(*                            path                                         *)
(*                                                                        *)
(*   category <-> lattice                                                  *)
(*     FluxBraidingPhase,     the weight of the Pontryagin-square action   *)
(*     PontryaginFluxPhase    on a 't Hooft flux background equals the     *)
(*                            mutual braiding of the fluxes                *)
(*                                                                        *)
(*   delooping <-> category                                                *)
(*     BarCochainValue,       the associator and the braiding of a pointed *)
(*     BarCoboundaryTable,    category on A are a cochain of degree n + 2  *)
(*     BarCocycleQ,           on the n-fold bar construction B^n:          *)
(*     DeloopingClassificationQ   phi[a|b|c] = w(a, b, c),                 *)
(*     EnStructureCount           phi[a || b] = c(a, b).                   *)
(*                            Its coboundary has the values                *)
(*                              B^1  [a|b|c|d]    pentagon                 *)
(*                              B^2  [[a|b|c|d]]  - pentagon               *)
(*                                   [a|b || c]   hexagon 2                *)
(*                                   [a || b|c]   hexagon 1                *)
(*                              B^3  the same with the opposite signs, and *)
(*                                   [a ||| b]    - (c(a,b) + c(b,a))      *)
(*                            so that an E_n-monoidal structure on A is a  *)
(*                            cocycle of degree n + 2 on K(A, n) = B^n A:  *)
(*                            a category that can be delooped n times.     *)
(*                            (pentagon and hexagons: left side minus      *)
(*                            right side, as in Operadica`EnCategories`.)  *)
(*                                                                        *)
(*  The action of an E-infinity operad on lattice cochains is in          *)
(*  Operadica`EInfinity`.                                                 *)
(*                                                                        *)
(*  Layer: bridge.  Depends on: Trees, Operads, LittleCubes, Graded,      *)
(*  Presented, BarrattEccles, BarConstruction, Lattice, EnCategories.     *)
(* ====================================================================== *)

BeginPackage["Operadica`Bridge`", {
  "Operadica`Trees`",
  "Operadica`Operads`",
  "Operadica`LittleCubes`",
  "Operadica`Graded`",
  "Operadica`Presented`",
  "Operadica`BarrattEccles`",
  "Operadica`BarConstruction`",
  "Operadica`Lattice`",
  "Operadica`EnCategories`"
}];

LittleCubesHomologyQ::usage = "LittleCubesHomologyQ[n, k] gives True if the Betti numbers of the space C_n(k) of k little n-cubes, computed from FacetNerve[SeparationNerve[n, k]], are the dimensions by degree of the arity-k part of PoissonOperad[n]. For n >= 2 this is the statement H_*(E_n) = P_n on dimensions; for n = 1 both sides are k! in degree 0. The size of the nerve grows quickly: k = 2 and (n, k) = (1, 3), (1, 4), (2, 3) are feasible.";

OpTensor::usage = "OpTensor is the generator of arity 2 that stands for the tensor product in a parenthesised product, as in OpTensor[OpTensor[OpLeaf, OpLeaf], OpLeaf] for (a b) c.";

ReassociationPhase::usage = "ReassociationPhase[cat, tree, objects] gives the phase, modulo 1, of the canonical sequence of associators that carries the product of the objects parenthesised by tree (a binary tree in OpTensor) to the fully right-nested product.";

ReassociationSteps::usage = "ReassociationSteps[cat, tree, objects] lists {phase, newTree} for every single application of the associator (a b) c -> a (b c) at a subtree. In newTree the leaves are the objects.";

MacLaneCoherenceQ::usage = "MacLaneCoherenceQ[cat, n] gives True if, for the products of n objects of the pointed category cat in every parenthesisation, each single associator step changes the reassociation phase by exactly its own phase, so that the phase of a reassociation does not depend on the path. For n = 4 this is the pentagon equation; for larger n it follows from it (Mac Lane's coherence theorem). The option \"MaxWords\" bounds the number of products tested.";

CupAlgebraOverAsQ::usage = "CupAlgebraOverAsQ[d] gives True if the cup product makes the cochains of the d-dimensional hypercubic lattice an algebra over the associative operad: the associativity relation holds identically for generic cochains of all degrees.";

EInfinityArityTwoQ::usage = "EInfinityArityTwoQ[d] gives True if, on the d-dimensional hypercubic lattice, the higher cup products define a chain map from the arity-2 part W of an E-infinity operad to the binary operations on cochains: with the generator e_i acting as Steenrod's cup-i, the commutator of the coboundary with e_i is the action of the boundary e_(i-1) + (-1)^i T e_(i-1), where T exchanges the two arguments with the Koszul sign.";

FluxBraidingPhase::usage = "FluxBraidingPhase[cat, z] gives b(z12, z34) - b(z13, z24) + b(z14, z23) modulo 1, where b is the mutual braiding of the braided category cat on a cyclic group and z is an antisymmetric 4 x 4 integer matrix of 't Hooft fluxes.";

PontryaginFluxPhase::usage = "PontryaginFluxPhase[n, p, z, dims] gives p / (2 n) times the sum of the Pontryagin square of the 't Hooft flux cochain of z over the four-torus with side lengths dims, modulo 1.";

BarrattEcclesHomologyQ::usage = "BarrattEcclesHomologyQ[n, k] gives True if the Betti numbers of the stage F_n of the Barratt-Eccles operad in arity k are the dimensions by degree of the arity-k part of PoissonOperad[n]: H_*(E_n) = P_n on dimensions, for a combinatorial E_n operad. (n, k) = (2, 3), (3, 3) are fast; (2, 4) and (4, 3) need matrices with several thousand rows.";

BarCochainValue::usage = "BarCochainValue[cat, x] gives the value, modulo 1, of the cochain of the pointed category cat on a generator x of an iterated bar construction, or on a linear combination of generators: the associator w(a, b, c) on [a | b | c], the braiding c(a, b) on [a || b], and the value on x for a suspended generator [x]. The data of cat must be normalized: they vanish when an argument is the unit object.";

BarCoboundaryTable::usage = "BarCoboundaryTable[cat, n] gives the Association from the generators of degree n + 3 of the n-fold bar construction of the group of cat to the value of the cochain of cat on their differentials, modulo 1. For n = 1 these are the pentagon expressions; for n = 2 the pentagon and the two hexagon expressions; for n = 3 the double braidings as well.";

BarCocycleQ::usage = "BarCocycleQ[cat, n] gives True if the cochain of the pointed category cat is a cocycle on the n-fold bar construction: all the values of BarCoboundaryTable[cat, n] vanish. For n >= 2 a category without braiding gives False.";

DeloopingClassificationQ::usage = "DeloopingClassificationQ[cat] gives True if, for n = 1, 2, 3, the data of the pointed category cat are a cocycle on the n-fold bar construction exactly when cat is E_n-monoidal: PentagonQ for n = 1, with HexagonQ for n = 2, and with SymmetricBraidingQ for n = 3. The data of cat must be normalized.";

EnStructureCount::usage = "EnStructureCount[orders, n] gives the order of the homology group H_(n+2)(K(A, n)) of the group A with the given orders, computed with the n-fold bar construction: the number of E_n-monoidal structures on the pointed category with the group A, up to equivalence (monoidal for n = 1, braided for n = 2, symmetric for n >= 3).";

Begin["`Private`"];

(* ---------------------------------------------------------------------- *)
(* operad <-> category: reassociation with phases                         *)
(*   a decorated tree is a binary tree in OpTensor whose leaves are group  *)
(*   elements (lists)                                                      *)
(* ---------------------------------------------------------------------- *)

charge[orders_List][OpTensor[x_, y_]] :=
  Mod[charge[orders][x] + charge[orders][y], orders];

charge[orders_List][g_List] := g;


(* rotate at the root while the left factor is a product, then go right *)
phase[cat_Association][OpTensor[OpTensor[x_, y_], z_]] :=
  With[{ch = charge[cat["Group"]]},
    cat["Associator"][ch[x], ch[y], ch[z]] + phase[cat][OpTensor[x, OpTensor[y, z]]]
  ];

phase[cat_Association][OpTensor[x_, z_]] := phase[cat][z];

phase[cat_Association][_] := 0;


steps[cat_Association][t_] :=
  With[{ch = charge[cat["Group"]], w = cat["Associator"]},
    Map[
      Function[pos,
        Replace[
          OpSubtree[t, pos],
          OpTensor[OpTensor[x_, y_], z_] :>
            {w[ch[x], ch[y], ch[z]], OpReplaceSubtree[t, pos, OpTensor[x, OpTensor[y, z]]]}
        ]
      ],
      Position[t, OpTensor[OpTensor[_, _], _], {0, Infinity}, Heads -> False]
    ]
  ];


ReassociationPhase[cat_Association, tree_, objects_List] :=
  Mod[phase[cat][OpComposeAll[tree, objects]], 1];

ReassociationSteps[cat_Association, tree_, objects_List] :=
  Map[
    Function[st, {Mod[st[[1]], 1], st[[2]]}],
    steps[cat][OpComposeAll[tree, objects]]
  ];


Options[MacLaneCoherenceQ] = {"MaxWords" -> 400};

MacLaneCoherenceQ[cat_Association, n_Integer /; n >= 2, OptionsPattern[]] :=
  Module[{words, trees, max = OptionValue["MaxWords"]},
    words = Tuples[CategoryObjects[cat], n];
    If[Length[words] > max, words = RandomSample[words, max]];
    trees = OpPlanarTrees[{OpTensor -> 2}, n];
    AllTrue[words,
      Function[word,
        AllTrue[trees,
          Function[tree,
            With[{t = OpComposeAll[tree, word]},
              With[{base = phase[cat][t]},
                AllTrue[
                  steps[cat][t],
                  Function[st, Mod[base - st[[1]] - phase[cat][st[[2]]], 1] === 0]
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* operad <-> lattice                                                     *)
(* ---------------------------------------------------------------------- *)

CupAlgebraOverAsQ[d_Integer?Positive] :=
  With[{triples = Select[Tuples[Range[0, d], 3], Function[t, Total[t] <= d]]},
    TrueQ[
      OpAlgebraCheck[
        {OpAssociativityRelation[product]},
        {product -> Cup},
        Map[
          Function[t,
            {Cochain[t[[1]], \[FormalA]], Cochain[t[[2]], \[FormalB]], Cochain[t[[3]], \[FormalC]]}
          ],
          triples
        ],
        "Equal" -> Function[{u, v}, CochainEqualQ[u, v, d]]
      ]["Passed"]
    ]
  ];


(* Steenrod's cup-i in terms of HigherCup *)
steenrod[i_Integer, u_, v_] :=
  SteenrodCupSign[CochainDegree[u], CochainDegree[v], i] HigherCup[i][u, v];

(*  d(a u_i b) = (-1)^i da u_i b + (-1)^(i+p) a u_i db
                 - (-1)^i a u_(i-1) b - (-1)^(pq) b u_(i-1) a   *)
EInfinityArityTwoQ[d_Integer?Positive] :=
  AllTrue[
    Flatten[Table[{p, q, i}, {p, 0, d}, {q, 0, d}, {i, 1, Min[p, q] + 1}], 2],
    Function[t,
      With[{deg1 = t[[1]], deg2 = t[[2]], lev = t[[3]]},
        With[{a = Cochain[deg1, \[FormalA]], b = Cochain[deg2, \[FormalB]]},
          CochainEqualQ[
            Coboundary[steenrod[lev, a, b]],
            (-1)^lev steenrod[lev, Coboundary[a], b] +
              (-1)^(lev + deg1) steenrod[lev, a, Coboundary[b]] -
              (-1)^lev steenrod[lev - 1, a, b] -
              (-1)^(deg1 deg2) steenrod[lev - 1, b, a],
            d
          ]
        ]
      ]
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* operad <-> operad: the homology of the little cubes                    *)
(* ---------------------------------------------------------------------- *)

LittleCubesHomologyQ[n_Integer?Positive, k_Integer /; k >= 2] :=
  Module[{betti, dims, j},
    betti = SimplicialBetti[FacetNerve[SeparationNerve[n, k]]];
    dims = OperadDimensionsByDegree[PoissonOperad[n], k];
    Max[Keys[dims]] <= Length[betti] - 1 &&
      betti === Table[Lookup[dims, Key[j], 0], {j, 0, Length[betti] - 1}]
  ];


BarrattEcclesHomologyQ[n_Integer?Positive, k_Integer?Positive] :=
  Module[{betti, dims, j},
    betti = BarrattEcclesBetti[n, k];
    dims = OperadDimensionsByDegree[PoissonOperad[n], k];
    Max[Keys[dims]] <= Length[betti] - 1 &&
      betti === Table[Lookup[dims, Key[j], 0], {j, 0, Length[betti] - 1}]
  ];


(* ---------------------------------------------------------------------- *)
(* delooping <-> category                                                 *)
(* ---------------------------------------------------------------------- *)

(* a one-letter word [x] with x in B^2 or higher is a suspension *)
barValue[cat_Association][BarWord[x_BarWord]] /; BarLevel[x] >= 2 := barValue[cat][x];

barValue[cat_Association][BarWord[g1_List, g2_List, g3_List]] :=
  cat["Associator"][g1, g2, g3];

barValue[cat_Association][BarWord[BarWord[g1_List, g2_List, g3_List]]] :=
  cat["Associator"][g1, g2, g3];

barValue[cat_Association][BarWord[BarWord[g1_List], BarWord[g2_List]]] :=
  cat["Braiding"][g1, g2];


BarCochainValue[cat_Association, x_BarWord] := Mod[barValue[cat][x], 1];

BarCochainValue[cat_Association, chain_] :=
  Mod[
    Total[Map[Function[tm, tm[[1]] barValue[cat][tm[[2]]]], LinearTerms[chain]]],
    1
  ];

BarCoboundaryTable[cat_Association, n_Integer?Positive] :=
  With[{orders = cat["Group"]},
    Association[
      Map[
        Function[g, g -> BarCochainValue[cat, BarDifferential[orders][g]]],
        BarGenerators[orders, n, n + 3]
      ]
    ]
  ];

BarCocycleQ[cat_Association, n_Integer?Positive] :=
  (n === 1 || Lookup[cat, "Braiding", None] =!= None) &&
    AllTrue[Values[BarCoboundaryTable[cat, n]], Function[v, v === 0]];

DeloopingClassificationQ[cat_Association] :=
  With[{monoidal = PentagonQ[cat]},
    With[{braided = monoidal && HexagonQ[cat]},
      {BarCocycleQ[cat, 1], BarCocycleQ[cat, 2], BarCocycleQ[cat, 3]} ===
        {monoidal, braided, braided && SymmetricBraidingQ[cat]}
    ]
  ];

EnStructureCount[orders : {__Integer}, n_Integer?Positive] :=
  With[{h = BarHomology[orders, n, n + 2]},
    If[MemberQ[h, 0], Infinity, Times @@ h]
  ];


(* ---------------------------------------------------------------------- *)
(* category <-> lattice                                                   *)
(* ---------------------------------------------------------------------- *)

FluxBraidingPhase[cat_Association, z_?MatrixQ] :=
  With[{b = Function[{u, v}, MutualBraiding[cat, Mod[{u}, cat["Group"]], Mod[{v}, cat["Group"]]]]},
    Mod[
      b[z[[1, 2]], z[[3, 4]]] - b[z[[1, 3]], z[[2, 4]]] + b[z[[1, 4]], z[[2, 3]]],
      1
    ]
  ];

PontryaginFluxPhase[n_Integer?Positive, p_Integer, z_?MatrixQ, dims_List] :=
  Mod[
    p / (2 n) CochainIntegrate[PontryaginSquare[THooftFluxCochain[z, dims]], dims],
    1
  ];

End[];

EndPackage[];
