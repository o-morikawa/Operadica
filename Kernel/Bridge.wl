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
(*   operad <-> loop spaces                                                *)
(*     ApproximationTheoremQ  the free P_n-algebra on the homology of a    *)
(*                            wedge of spheres X has the Poincare series   *)
(*                            of Omega^n Sigma^n X: the approximation      *)
(*                            theorem C_n X ~ Omega^n Sigma^n X, rationally *)
(*     ApproximationTheoremModTwoQ  modulo 2 and for n = 2: the homology   *)
(*                            of the braid groups (the free E_2-algebra on *)
(*                            a point) is the polynomial algebra on x,     *)
(*                            Q x, Q Q x, ... of Kudo and Araki, the       *)
(*                            homology of the double loop space of a sphere *)
(*                                                                        *)
(*   loop spaces <-> category: paths of little squares and the braiding    *)
(*     PathBraidingPhase,     a braided category gives a phase to a path   *)
(*     BlockBraidingQ,        of configurations of little squares with an  *)
(*     HexagonFromPathsQ,     object in every square: the counterclockwise *)
(*     SymmetricFromPathsQ    exchange of a (left) and b (right) is the    *)
(*                            braiding c(a, b).  The phase is compatible   *)
(*                            with the composition of the operad: moving a *)
(*                            past a row of squares is braiding with the   *)
(*                            product (the two hexagon equations).  In     *)
(*                            three dimensions the two half turns are      *)
(*                            homotopic, and the phases agree exactly when *)
(*                            the braiding is symmetric.                   *)
(*                                                                        *)
(*   lattice <-> delooping <-> category                                    *)
(*     FlatFieldCochain,      a simplex of K(Z_N, n) is a flat n-form      *)
(*     DijkgraafWittenWeight, field on a simplex; its lift to integers is  *)
(*     PontryaginWeight,      a cochain, and a lattice action evaluated on *)
(*     DijkgraafWittenAssociatorQ,  it is a cocycle on K(Z_N, n):          *)
(*     PontryaginSpinQ          (k / N^2) A cup dA on a tetrahedron is the *)
(*                            associator of Vec_(Z_N)^k, and the class of  *)
(*                            (p / 2N) P(B) on a 4-simplex has the order   *)
(*                            of the spin p / 2N of the anyons Z_N^(p).    *)
(*     SteenrodWeight,        (1/2) Sq^k B on a simplex of K(Z_2, n) is a  *)
(*     SteenrodBocksteinQ,    cocycle with values in R/Z.  Sq^1 B is the   *)
(*     SteenrodFermionQ       Bockstein dB / 2 modulo 2 as a cochain, and  *)
(*                            (1/2) Sq^2 has a class of order 2 on         *)
(*                            K(Z_2, 2) and on K(Z_2, 3), where it is      *)
(*                            (1/2) C cup_1 C: the fermion, as a braided   *)
(*                            and as a symmetric structure.                *)
(*     FlatVillainField,      a flat Z_N field is the flat Villain field   *)
(*     ChernSimonsWeight,     (2 Pi At / N, d At / N).  On it the U(1)     *)
(*     ChernSimonsDijkgraafWittenQ  Chern-Simons Lagrangian at an even     *)
(*                            level k, over 2 Pi, is a cocycle on          *)
(*                            K(Z_N, 1) in the class of the Dijkgraaf-     *)
(*                            Witten weight of level - k / 2: the          *)
(*                            associator of Vec_(Z_N).                     *)
(*                                                                        *)
(*  The action of an E-infinity operad on lattice cochains is in          *)
(*  Operadica`EInfinity`.                                                 *)
(*                                                                        *)
(*  Layer: bridge.  Depends on: Trees, Operads, LittleCubes, Loops,       *)
(*  Graded, Presented, BarrattEccles, BarConstruction, Lattice,           *)
(*  Simplicial, Villain, EnCategories.                                    *)
(* ====================================================================== *)

BeginPackage["Operadica`Bridge`", {
  "Operadica`Trees`",
  "Operadica`Operads`",
  "Operadica`LittleCubes`",
  "Operadica`Loops`",
  "Operadica`Graded`",
  "Operadica`Presented`",
  "Operadica`BarrattEccles`",
  "Operadica`BarConstruction`",
  "Operadica`Lattice`",
  "Operadica`Simplicial`",
  "Operadica`Villain`",
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

FlatFieldCochain::usage = "FlatFieldCochain[n][x] gives the integer cochain of degree n on the simplex {0, ..., k} that lifts the flat field x = EMSimplex[k, values], a simplex of K(Z_N, n): its value on a face is the representative in 0, ..., N - 1. FlatFieldCochain[n, j][x] takes the j-th component for a group with several cyclic factors.";

DijkgraafWittenWeight::usage = "DijkgraafWittenWeight[nn, k][x] gives the value modulo 1 of the lattice action (k / nn^2) A cup dA on the tetrahedron, for the flat Z_nn gauge field x, a 3-simplex of K(Z_nn, 1), with A = FlatFieldCochain[1][x].";

PontryaginWeight::usage = "PontryaginWeight[nn, p][x] gives the value modulo 1 of (p / (2 nn)) P(B) on the 4-simplex, for the flat Z_nn 2-form field x, a 4-simplex of K(Z_nn, 2), with B = FlatFieldCochain[2][x] and P the Pontryagin square B cup B - B cup_1 dB.";

DijkgraafWittenAssociatorQ::usage = "DijkgraafWittenAssociatorQ[nn, k] gives True if DijkgraafWittenWeight[nn, k], on every flat field on the tetrahedron with the values a, b, c on the edges 01, 12, 23, equals the associator w(a, b, c) of VecZN[nn, k].";

PontryaginSpinQ::usage = "PontryaginSpinQ[nn, p] gives True if PontryaginWeight[nn, p] is a cocycle on K(Z_nn, 2) and the order of its class in H^4(K(Z_nn, 2); U(1)) is the denominator of the spin p / (2 nn) of the generator of ZNAnyons[nn, p].";

ApproximationTheoremQ::usage = "ApproximationTheoremQ[n, degrees, kmax] gives True if, for X a wedge of spheres of the given dimensions (all >= 1), the free algebra over PoissonOperad[n] = H_*(E_n) on the reduced homology of X and the rational homology of the n-fold loop space of the n-fold suspension of X have the same dimensions in every degree, for the arities (weights) 1, ..., kmax: the approximation theorem C_n X ~ Omega^n Sigma^n X at the level of rational Poincare series.";

PathBraidingPhase::usage = "PathBraidingPhase[cat, {a1, ..., ak}, path, {s0, s1}, steps] gives the phase, modulo 1, that the pointed braided category cat gives to the path s -> path[s] of configurations of k little squares with the object aj in the j-th square: BraidPathPhase for the braid PathBraid[path, {s0, s1}, steps], on the right-nested product of the objects read from left to right at s0. The counterclockwise exchange of a (left) and b (right) has the phase c(a, b); this choice fixes the orientation of the plane. The result is $Failed if PathBraid fails.";

BlockBraidingQ::usage = "BlockBraidingQ[cat, {m1, m2}] gives True if the braiding of cat is compatible with the composition of the little squares operad for the half turn of two rows of m1 and m2 squares, the path SwapPath[2] composed with the two rows: for all objects, the phase of the braid of this path on the right-nested product equals - R + c(A, B) + R', where A and B are the products of the two rows, c(A, B) is the phase of SwapPath[2] itself for the objects A and B, and R, R' are the reassociation phases between the right-nested products and the products of the two rows before and after the exchange. {1, 2} is the first hexagon equation and {2, 1} the second.";

HexagonFromPathsQ::usage = "HexagonFromPathsQ[cat] gives True if BlockBraidingQ[cat, {1, 2}] and BlockBraidingQ[cat, {2, 1}] hold: moving a square around a pair of squares, or a pair around a square, has the phase of the braiding with the product. For arbitrary data this is equivalent to HexagonQ[cat].";

SymmetricFromPathsQ::usage = "SymmetricFromPathsQ[cat] gives True if the category cat gives the same phase to the two ends SwapHomotopy[0] and SwapHomotopy[1] of the homotopy between the counterclockwise and the clockwise exchange of two little 3-cubes, for all pairs of objects: the condition that the phases come from paths of little 3-cubes up to homotopy. It is equivalent to SymmetricBraidingQ[cat].";

SteenrodWeight::usage = "SteenrodWeight[n, k][x] gives the value modulo 1 of (1/2) Sq^k B on the simplex of dimension n + k, for the flat Z_2 field x of degree n, a simplex of K(Z_2, n), with B = FlatFieldCochain[n][x] and Sq^k B = SteenrodSquare[k][B]. It is a cocycle on K(Z_2, n) with values in R/Z: a topological action for a Z_2 gauge field of degree n in n + k dimensions.";

SteenrodBocksteinQ::usage = "SteenrodBocksteinQ[n] gives True if, on every (n+1)-simplex of K(Z_2, n), the cochain SteenrodSquare[1][B] equals half of the coboundary of B modulo 2, for the lift B = FlatFieldCochain[n][x] of the flat field to the values 0 and 1: Sq^1 is the Bockstein, as cochains.";

SteenrodFermionQ::usage = "SteenrodFermionQ[n], for n = 2 or 3, gives True if the weight SteenrodWeight[n, 2], which is (1/2) B cup B for n = 2 and (1/2) C cup_1 C for n = 3, vanishes on the degenerate simplices of K(Z_2, n) and the order of its class in H^(n+2)(K(Z_2, n); U(1)) is the denominator of the spin 1/2 of the fermion SuperVec[]. For n = 3 the class generates H^5(K(Z_2, 3); U(1)) = Z_2, the symmetric structures on Z_2. That the weight is a cocycle follows from the formula for the coboundary of SteenrodSquare.";

ApproximationTheoremModTwoQ::usage = "ApproximationTheoremModTwoQ[d, kmax] gives True if, for k = 1, ..., kmax, the Betti numbers modulo 2 of the braid group on k strands, shifted up by d k, are KudoArakiDimensions[d, kmax] in the weight k. The left side is the homology modulo 2 of the part of C_2 X with k points for X the sphere of dimension d (by the Thom isomorphism, which holds modulo 2 for every vector bundle); the right side is, for d >= 1, the homology modulo 2 of the double loop space of the sphere of dimension d + 2: the approximation theorem C_2 X ~ Omega^2 Sigma^2 X modulo 2, with the Kudo-Araki operation in place of the bracket.";

FlatVillainField::usage = "FlatVillainField[nn, n][x] gives the Villain field of degree n of the flat Z_nn field x, a simplex of K(Z_nn, n): with the integer lift At = FlatFieldCochain[n][x], the connection is (2 Pi / nn) At and the flux Coboundary[At] / nn, an integer cochain. Its curvature vanishes.";

ChernSimonsWeight::usage = "ChernSimonsWeight[nn, k][x] gives the value modulo 1 of the U(1) Chern-Simons Lagrangian VillainChernSimons[k] over 2 Pi on the tetrahedron, for the flat Z_nn gauge field x, a 3-simplex of K(Z_nn, 1), as the Villain field FlatVillainField[nn, 1][x]. It equals -(k / (2 nn^2)) times Cup[Coboundary[At], At].";

ChernSimonsDijkgraafWittenQ::usage = "ChernSimonsDijkgraafWittenQ[nn, k] gives True if k is even, ChernSimonsWeight[nn, k] is a cocycle on K(Z_nn, 1), and its class is that of DijkgraafWittenWeight[nn, -k / 2]: the U(1) Chern-Simons theory at level k, restricted to flat Z_nn fields, is the Dijkgraaf-Witten theory of level -k / 2 modulo nn. For odd k the weight is not a cocycle and the result is False.";

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
(* operad <-> loop spaces: the approximation theorem                      *)
(* ---------------------------------------------------------------------- *)

ApproximationTheoremQ[n_Integer?Positive, degrees : {__Integer}, kmax_Integer?Positive] :=
  FreeAlgebraDimensions[PoissonOperad[n], degrees, kmax] ===
    LoopSuspensionDimensions[n, degrees, kmax];

ApproximationTheoremModTwoQ[d_Integer?NonNegative, kmax_Integer?Positive] :=
  With[{expected = KudoArakiDimensions[d, kmax]},
    AllTrue[
      Range[kmax],
      Function[k,
        With[{betti = ModularBetti[BraidGroupHomology[k], 2]},
          KeySort[
            Association[
              Table[
                If[betti[[j + 1]] > 0, j + d k -> betti[[j + 1]], Nothing],
                {j, 0, k - 1}
              ]
            ]
          ] === Lookup[expected, Key[k]]
        ]
      ]
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* loop spaces <-> category: paths of little squares and the braiding     *)
(* ---------------------------------------------------------------------- *)

PathBraidingPhase[cat_Association, objects_List, path_, {s0_, s1_}, steps_Integer?Positive] :=
  With[{start = ConfigurationOrder[path[s0]], braid = PathBraid[path, {s0, s1}, steps]},
    If[start === $Failed || braid === $Failed,
      $Failed,
      BraidPathPhase[cat, objects[[start]], braid]
    ]
  ];

rowOfSquares[m_Integer] := Table[{{(j - 1) / m, j / m}, {0, 1}}, {j, 1, m}];

combTree[1] := OpLeaf;

combTree[m_Integer /; m >= 2] := OpTensor[OpLeaf, combTree[m - 1]];

(* with 16 m1 m2 steps every exchange happens at a sample of the path *)
blockBraid[m1_Integer, m2_Integer] := blockBraid[m1, m2] =
  PathBraid[
    Function[s, LittleCubesComposeAll[SwapPath[2][s], {rowOfSquares[m1], rowOfSquares[m2]}]],
    {0, 1},
    16 m1 m2
  ];

BlockBraidingQ[cat_Association, {m1_Integer?Positive, m2_Integer?Positive}] :=
  With[{
      braid = blockBraid[m1, m2],
      group = cat["Group"],
      br = Lookup[cat, "Braiding", None],
      before = OpTensor[combTree[m1], combTree[m2]],
      after = OpTensor[combTree[m2], combTree[m1]]
    },
    br =!= None &&
      AllTrue[
        Tuples[CategoryObjects[cat], m1 + m2],
        Function[word,
          With[{first = Take[word, m1], second = Drop[word, m1]},
            BraidWord[word, braid] === Join[second, first] &&
              Mod[
                BraidPathPhase[cat, word, braid]
                  + ReassociationPhase[cat, before, word]
                  - br[Mod[Total[first], group], Mod[Total[second], group]]
                  - ReassociationPhase[cat, after, Join[second, first]],
                1
              ] === 0
          ]
        ]
      ]
  ];

HexagonFromPathsQ[cat_Association] :=
  BlockBraidingQ[cat, {1, 2}] && BlockBraidingQ[cat, {2, 1}];

SymmetricFromPathsQ[cat_Association] :=
  With[{
      b0 = PathBraid[SwapHomotopy[0], {0, 1}, 8],
      b1 = PathBraid[SwapHomotopy[1], {0, 1}, 8]
    },
    Lookup[cat, "Braiding", None] =!= None &&
      AllTrue[
        Tuples[CategoryObjects[cat], 2],
        Function[word, BraidPathPhase[cat, word, b0] === BraidPathPhase[cat, word, b1]]
      ]
  ];


(* ---------------------------------------------------------------------- *)
(* lattice <-> delooping <-> category                                     *)
(* ---------------------------------------------------------------------- *)

FlatFieldCochain[n_Integer?Positive][x_EMSimplex] := FlatFieldCochain[n, 1][x];

FlatFieldCochain[n_Integer?Positive, j_Integer?Positive][EMSimplex[k_Integer, vals_List]] :=
  With[{val = AssociationThread[Subsets[Range[0, k], {n + 1}], Map[Function[g, g[[j]]], vals]]},
    Cochain[n, Function[v, Lookup[val, Key[v], 0]]]
  ];

DijkgraafWittenWeight[nn_Integer?Positive, kk_Integer][x_EMSimplex] :=
  With[{a = FlatFieldCochain[1][x]},
    Mod[(kk / nn^2) * SimplexValue[Cup[a, Coboundary[a]], Range[0, 3]], 1]
  ];

PontryaginWeight[nn_Integer?Positive, p_Integer][x_EMSimplex] :=
  With[{b = FlatFieldCochain[2][x]},
    Mod[(p / (2 nn)) * SimplexValue[PontryaginSquare[b], Range[0, 4]], 1]
  ];

(* the values of a 3-simplex of K(A, 1) are listed for the edges
   01, 02, 03, 12, 13, 23 *)
DijkgraafWittenAssociatorQ[nn_Integer?Positive, kk_Integer] :=
  With[{w = VecZN[nn, kk]["Associator"]},
    AllTrue[
      EilenbergMacLaneSimplices[{nn}, 1, 3],
      Function[x,
        DijkgraafWittenWeight[nn, kk][x] ===
          Mod[w[x[[2, 1]], x[[2, 4]], x[[2, 6]]], 1]
      ]
    ]
  ];

PontryaginSpinQ[nn_Integer?Positive, p_Integer] :=
  CharacteristicCocycleQ[{nn}, 2, 4, PontryaginWeight[nn, p]] &&
    CharacteristicClassOrder[{nn}, 2, 4, PontryaginWeight[nn, p]] ===
      Denominator[TopologicalSpin[ZNAnyons[nn, p], {1}]];

(* U(1) Chern-Simons theory on flat Z_N fields *)
FlatVillainField[nn_Integer?Positive, n_Integer?Positive][x_EMSimplex] :=
  With[{at = FlatFieldCochain[n][x]},
    VillainField[(2 Pi / nn) at, (1 / nn) Coboundary[at]]
  ];

ChernSimonsWeight[nn_Integer?Positive, k_Integer][x_EMSimplex] :=
  Mod[
    Expand[
      (1 / (2 Pi)) *
        SimplexValue[
          VillainChernSimons[k][FlatVillainField[nn, 1][x], Cochain[0, Function[v, 0]]],
          Range[0, 3]
        ]
    ],
    1
  ];

ChernSimonsDijkgraafWittenQ[nn_Integer?Positive, k_Integer] :=
  EvenQ[k] &&
    CharacteristicCocycleQ[{nn}, 1, 3, ChernSimonsWeight[nn, k]] &&
    CharacteristicClassOrder[{nn}, 1, 3,
      Function[x, ChernSimonsWeight[nn, k][x] - DijkgraafWittenWeight[nn, -k / 2][x]]
    ] === 1;

(* Steenrod squares of a flat Z_2 field *)
SteenrodWeight[n_Integer?Positive, k_Integer?NonNegative][x_EMSimplex] :=
  Mod[(1/2) * SimplexValue[SteenrodSquare[k][FlatFieldCochain[n][x]], Range[0, n + k]], 1];

SteenrodBocksteinQ[n_Integer?Positive] :=
  AllTrue[
    EilenbergMacLaneSimplices[{2}, n, n + 1],
    Function[x,
      With[{b = FlatFieldCochain[n][x]},
        Mod[SimplexValue[SteenrodSquare[1][b] - (1/2) Coboundary[b], Range[0, n + 1]], 2] === 0
      ]
    ]
  ];

SteenrodFermionQ[n : (2 | 3)] :=
  With[{w = SteenrodWeight[n, 2]},
    AllTrue[
      EilenbergMacLaneSimplices[{2}, n, n + 2],
      Function[x, ! EilenbergMacLaneDegenerateQ[{2}, n][x] || w[x] === 0]
    ] &&
      CharacteristicClassOrder[{2}, n, n + 2, w] ===
        Denominator[TopologicalSpin[SuperVec[], {1}]]
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
