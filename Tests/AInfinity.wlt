(* AInfinity: the A-infinity operad and the associahedra.
   Expected values from reference/ainfinity_reference.py. *)

(* the differential of the generators *)

VerificationTest[
  {
    AInfinityDifferential[2],
    AInfinityDifferential[3] ===
      -LBasis[OpM[2][OpM[2][OpLeaf, OpLeaf], OpLeaf]] + LBasis[OpM[2][OpLeaf, OpM[2][OpLeaf, OpLeaf]]],
    AInfinityDifferential[4] ===
      LBasis[OpM[2][OpM[3][OpLeaf, OpLeaf, OpLeaf], OpLeaf]] +
      LBasis[OpM[2][OpLeaf, OpM[3][OpLeaf, OpLeaf, OpLeaf]]] -
      LBasis[OpM[3][OpM[2][OpLeaf, OpLeaf], OpLeaf, OpLeaf]] +
      LBasis[OpM[3][OpLeaf, OpM[2][OpLeaf, OpLeaf], OpLeaf]] -
      LBasis[OpM[3][OpLeaf, OpLeaf, OpM[2][OpLeaf, OpLeaf]]],
    Length[LinearTerms[AInfinityDifferential[5]]]
  },
  {0, True, True, 9},
  TestID -> "AInfinity-differential"
]

(* d m_3 says that m_3 is a homotopy between the two ways to multiply three things *)

VerificationTest[
  With[{op = AInfinityOperad[3]},
    {
      op["Degree"][OpCorolla[OpM[3], 3]],
      op["Differential"][OpCorolla[OpM[3], 3]] === AInfinityDifferential[3],
      op["Differential"][OpCorolla[OpM[2], 2]],
      op["Differential"][OpLeaf]
    }
  ],
  {1, True, 0, 0},
  TestID -> "AInfinity-operad-differential"
]

(* the Stasheff relations: d d = 0 *)

VerificationTest[
  StasheffRelationsQ[7],
  True,
  TestID -> "AInfinity-Stasheff-relations"
]

(* a differential graded operad: axioms with signs, d d = 0, Leibniz rule *)

VerificationTest[
  With[{r = DGOperadCheck[AInfinityOperad[4], 4]},
    {r["Passed"], Sort[Keys[r["Checked"]]], AllTrue[Values[r["Checked"]], # > 0 &]}
  ],
  {True, {"Leibniz", "Parallel", "Sequential", "Square", "Unit"}, True},
  TestID -> "AInfinity-dg-operad"
]

(* with all signs +1 the differential does not square to zero *)

VerificationTest[
  With[{op = FreeGradedOperad[Table[OpM[k] -> {k, k - 2}, {k, 2, 4}]]},
    With[{bad = WithDifferential[op,
        Function[h,
          Total[Flatten[Table[
            LBasis[OpCompose[OpCorolla[OpM[p], p], i, OpCorolla[OpM[First[h] + 1 - p], First[h] + 1 - p]]],
            {p, 2, First[h] - 1}, {i, 1, p}]]]]]},
      With[{r = DGOperadCheck[bad, 4]},
        {r["Passed"], r["Failed"]["Square"] > 0}
      ]
    ]
  ],
  {False, True},
  TestID -> "AInfinity-wrong-signs-detected"
]

(* ---------------------------------------------------------------------- *)
(* associahedra                                                           *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  Table[AssociahedronFVector[n], {n, 2, 6}],
  {{1}, {2, 1}, {5, 5, 1}, {14, 21, 9, 1}, {42, 84, 56, 14, 1}},
  TestID -> "AInfinity-f-vectors"
]

(* K_n is a ball: Euler characteristic 1 *)

VerificationTest[
  Table[Total[MapIndexed[(-1)^(First[#2] - 1) #1 &, AssociahedronFVector[n]]], {n, 2, 7}],
  {1, 1, 1, 1, 1, 1},
  TestID -> "AInfinity-Euler-characteristic"
]

(* the homology of the arity-n part is one-dimensional, in degree 0:
   A-infinity is a resolution of the associative operad *)

VerificationTest[
  Table[AssociahedronBetti[n], {n, 2, 6}],
  {{1}, {1, 0}, {1, 0, 0}, {1, 0, 0, 0}, {1, 0, 0, 0, 0}},
  TestID -> "AInfinity-resolution-of-As"
]

(* the graph of K_n: K_4 is the pentagon *)

VerificationTest[
  Table[{VertexCount[AssociahedronGraph[n]], EdgeCount[AssociahedronGraph[n]]}, {n, 3, 6}],
  {{2, 1}, {5, 5}, {14, 21}, {42, 84}},
  TestID -> "AInfinity-graph-counts"
]

VerificationTest[
  {
    Sort[VertexDegree[AssociahedronGraph[4]]],
    Union[VertexDegree[AssociahedronGraph[5]]],
    ConnectedGraphQ[AssociahedronGraph[5]]
  },
  {{2, 2, 2, 2, 2}, {3}, True},
  TestID -> "AInfinity-graph-pentagon"
]
