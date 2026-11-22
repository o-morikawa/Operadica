(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`AInfinity`                                                   *)
(*                                                                        *)
(*  The A-infinity operad and the associahedra.                            *)
(*                                                                        *)
(*  Generators OpM[n], n >= 2, of arity n and degree n - 2, with           *)
(*      d m_n = sum_{p+q=n+1; p,q>=2} sum_{i=1}^{p}                        *)
(*                  (-1)^(i + q (p - i)) m_p o_i m_q .                     *)
(*  This is the sign rule of Loday-Vallette, Algebraic Operads (their      *)
(*  (-1)^(p + q r + 1) with p = i - 1 and r the number of inputs after     *)
(*  the inserted operation).                                               *)
(*                                                                        *)
(*  d d = 0 is the system of Stasheff relations.  The arity-n part is the  *)
(*  cellular chain complex of the associahedron K_n: a tree with v         *)
(*  vertices is a face of dimension n - 1 - v.  Its homology is one-       *)
(*  dimensional, in degree 0: A-infinity resolves the associative operad.  *)
(*                                                                        *)
(*  Checked in reference/ainfinity_reference.py.                          *)
(*                                                                        *)
(*  Layer: operad.  Depends on: Trees, Graded, Rewriting.                 *)
(* ====================================================================== *)

BeginPackage["Operadica`AInfinity`", {
  "Operadica`Trees`",
  "Operadica`Graded`",
  "Operadica`Rewriting`"
}];

OpM::usage = "OpM[n] is the generator of arity n and degree n - 2 of the A-infinity operad. OpM[2] is the product, OpM[3] the homotopy for associativity.";

AInfinityDifferential::usage = "AInfinityDifferential[n] gives the differential of the generator OpM[n] as a linear combination of trees with two vertices.";

AInfinityOperad::usage = "AInfinityOperad[nmax] gives the A-infinity operad as a differential graded operad, with generators OpM[2], ..., OpM[nmax]. It is complete in arities up to nmax.";

StasheffRelationsQ::usage = "StasheffRelationsQ[nmax] gives True if the differential of the A-infinity operad squares to zero on the generators OpM[2], ..., OpM[nmax]. These are the Stasheff relations.";

AssociahedronFaces::usage = "AssociahedronFaces[n] gives the faces of the associahedron K_n as an Association from the dimension to the list of planar trees with n leaves labelling the faces of that dimension.";

AssociahedronFVector::usage = "AssociahedronFVector[n] gives the numbers of faces of the associahedron K_n of dimension 0, 1, ..., n - 2.";

AssociahedronBetti::usage = "AssociahedronBetti[n] gives the Betti numbers of the arity-n part of the A-infinity operad, the cellular chain complex of the associahedron K_n.";

AssociahedronGraph::usage = "AssociahedronGraph[n] gives the graph of the associahedron K_n: the vertices are the binary trees with n leaves and the edges are the single applications of associativity.";

Begin["`Private`"];

AInfinityDifferential[n_Integer /; n >= 2] :=
  Total[
    Flatten[
      Table[
        With[{q = n + 1 - p},
          (-1)^(i + q (p - i)) *
            LBasis[OpCompose[OpCorolla[OpM[p], p], i, OpCorolla[OpM[q], q]]]
        ],
        {p, 2, n - 1}, {i, 1, p}
      ]
    ]
  ];


AInfinityOperad[nmax_Integer /; nmax >= 2] :=
  Join[
    WithDifferential[
      FreeGradedOperad[Table[OpM[k] -> {k, k - 2}, {k, 2, nmax}]],
      Function[h, AInfinityDifferential[First[h]]]
    ],
    <|"Name" -> "A-infinity"|>
  ];


StasheffRelationsQ[nmax_Integer /; nmax >= 2] :=
  With[{op = AInfinityOperad[nmax]},
    AllTrue[
      Range[2, nmax],
      Function[n, LinearZeroQ[LinearExtend[op["Differential"]][AInfinityDifferential[n]]]]
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* associahedra                                                           *)
(* ---------------------------------------------------------------------- *)

AssociahedronFaces[n_Integer /; n >= 2] :=
  With[{op = AInfinityOperad[n]},
    KeySort[GroupBy[op["Elements"][n], op["Degree"]]]
  ];

AssociahedronFVector[n_Integer /; n >= 2] :=
  With[{faces = AssociahedronFaces[n]},
    Table[Length[Lookup[faces, k, {}]], {k, 0, n - 2}]
  ];

AssociahedronBetti[n_Integer /; n >= 2] :=
  With[{op = AInfinityOperad[n]},
    With[{faces = KeySort[GroupBy[op["Elements"][n], op["Degree"]]]},
      ChainBetti[Table[Lookup[faces, k, {}], {k, 0, n - 2}], op["Differential"]]
    ]
  ];

(* associativity, oriented from (a b) c to a (b c) *)
rotation = OpM[2][OpM[2][x_, y_], z_] :> OpM[2][x, OpM[2][y, z]];

AssociahedronGraph[n_Integer /; n >= 2] :=
  With[{vertices = OpPlanarTrees[{OpM[2] -> 2}, n]},
    Graph[
      vertices,
      Flatten[
        Map[
          Function[t, Map[Function[r, UndirectedEdge[t, r]], OpRewriteSteps[t, {rotation}]]],
          vertices
        ]
      ]
    ]
  ];

End[];

EndPackage[];
