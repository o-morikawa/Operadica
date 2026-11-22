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
(*  Layer: bridge.  Depends on: Trees, Operads, LittleCubes, Presented,   *)
(*  Lattice, EnCategories.                                                *)
(* ====================================================================== *)

BeginPackage["Operadica`Bridge`", {
  "Operadica`Trees`",
  "Operadica`Operads`",
  "Operadica`LittleCubes`",
  "Operadica`Presented`",
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
