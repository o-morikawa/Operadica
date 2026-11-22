(* Graded: linear combinations, free graded operads, differentials.
   The sign conventions are those of reference/ainfinity_reference.py. *)

(* ---------------------------------------------------------------------- *)
(* linear combinations                                                    *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    Sort[LinearTerms[2 LBasis[p] - 3 LBasis[q]]],
    LinearTerms[0],
    Sort[LinearTerms[kk (LBasis[p] + LBasis[q])]]
  },
  {Sort[{{2, p}, {-3, q}}], {}, Sort[{{kk, p}, {kk, q}}]},
  TestID -> "Graded-linear-terms"
]

VerificationTest[
  {
    LinearCollect[LBasis[p] + 2 LBasis[q] - LBasis[p]],
    LinearCollect[(1 + kk) LBasis[p] - kk LBasis[p] - LBasis[p]],
    LinearZeroQ[LBasis[p] - LBasis[p]],
    LinearZeroQ[LBasis[p] - LBasis[q]]
  },
  {2 LBasis[q], 0, True, False},
  TestID -> "Graded-linear-collect"
]

VerificationTest[
  {
    LinearExtend[Function[x, LBasis[f[x]] + LBasis[g[x]]]][2 LBasis[p] - LBasis[q]] ===
      2 LBasis[f[p]] + 2 LBasis[g[p]] - LBasis[f[q]] - LBasis[g[q]],
    BilinearExtend[Function[{x, y}, LBasis[{x, y}]]][LBasis[p] + 2 LBasis[q], 3 LBasis[r]] ===
      3 LBasis[{p, r}] + 6 LBasis[{q, r}],
    LinearExtend[Function[x, 0]][LBasis[p] + LBasis[q]]
  },
  {True, True, 0},
  TestID -> "Graded-linear-extend"
]

(* ---------------------------------------------------------------------- *)
(* free graded operads: Koszul signs                                      *)
(* ---------------------------------------------------------------------- *)

(* gx has degree 0 and gy degree 1; grafting an odd operation to the left of
   an odd vertex costs a sign *)

VerificationTest[
  With[{op = FreeGradedOperad[{gx -> {2, 0}, gy -> {2, 1}}]},
    With[{y = gy[OpLeaf, OpLeaf], x = gx[OpLeaf, OpLeaf]},
      {
        op["Compose"][gy[OpLeaf, y], 1, y] === -LBasis[gy[y, y]],
        op["Compose"][gy[OpLeaf, y], 2, y] === LBasis[gy[OpLeaf, gy[y, OpLeaf]]],
        op["Compose"][gy[OpLeaf, y], 1, x] === LBasis[gy[x, y]],
        op["Compose"][gx[OpLeaf, y], 1, y] === -LBasis[gx[y, y]],
        op["Degree"][gy[x, gy[y, OpLeaf]]]
      }
    ]
  ],
  {True, True, True, True, 3},
  TestID -> "Graded-Koszul-signs"
]

VerificationTest[
  DGOperadQ[FreeGradedOperad[{gx -> {2, 0}, gy -> {2, 1}, gz -> {3, 1}}], 4],
  True,
  TestID -> "Graded-axioms-with-signs"
]

(* without the Koszul sign the parallel axiom fails for odd operations *)

VerificationTest[
  With[{op = FreeGradedOperad[{gy -> {2, 1}}]},
    With[{r = DGOperadCheck[
        Join[op, <|"Compose" -> Function[{s, i, t}, LBasis[OpCompose[s, i, t]]]|>], 4]},
      {r["Passed"], r["Failed"]["Sequential"], r["Failed"]["Parallel"] > 0}
    ]
  ],
  {False, 0, True},
  TestID -> "Graded-missing-signs-detected"
]

VerificationTest[
  With[{op = FreeGradedOperad[{gx -> {2, 0}, gy -> {2, 1}}]},
    {
      GradedCompose[op][LBasis[gy[OpLeaf, OpLeaf]] + 2 LBasis[gx[OpLeaf, OpLeaf]], 1, LBasis[gy[OpLeaf, OpLeaf]]] ===
        LBasis[gy[gy[OpLeaf, OpLeaf], OpLeaf]] + 2 LBasis[gx[gy[OpLeaf, OpLeaf], OpLeaf]],
      GradedDegree[op, LBasis[gy[gy[OpLeaf, OpLeaf], OpLeaf]] - LBasis[gy[OpLeaf, gy[OpLeaf, OpLeaf]]]]
    }
  ],
  {True, 2},
  TestID -> "Graded-compose-linear"
]

(* ---------------------------------------------------------------------- *)
(* homology of a chain complex                                            *)
(* ---------------------------------------------------------------------- *)

(* the boundary of a triangle: three vertices and three edges, a circle *)

VerificationTest[
  ChainBetti[
    {{v1, v2, v3}, {e12, e23, e13}},
    Function[e,
      Replace[e, {
        e12 -> LBasis[v2] - LBasis[v1],
        e23 -> LBasis[v3] - LBasis[v2],
        e13 -> LBasis[v3] - LBasis[v1],
        _ -> 0
      }]
    ]
  ],
  {1, 1},
  TestID -> "Graded-ChainBetti-circle"
]

VerificationTest[
  ChainBetti[
    {{v1, v2, v3}, {e12, e23, e13}, {f123}},
    Function[e,
      Replace[e, {
        e12 -> LBasis[v2] - LBasis[v1],
        e23 -> LBasis[v3] - LBasis[v2],
        e13 -> LBasis[v3] - LBasis[v1],
        f123 -> LBasis[e23] - LBasis[e13] + LBasis[e12],
        _ -> 0
      }]
    ]
  ],
  {1, 0, 0},
  TestID -> "Graded-ChainBetti-disc"
]

(* ---------------------------------------------------------------------- *)
(* integral homology                                                      *)
(* ---------------------------------------------------------------------- *)

(* the invariant factors of an integer matrix; the expected values are those
   of reference/bar_reference.py *)

VerificationTest[
  {
    SmithInvariants[{{2, 4, 4}, {-6, 6, 12}, {10, 4, 16}}],
    SmithInvariants[{{2, 0}, {0, 3}}],
    SmithInvariants[{{4, 0}, {0, 6}}],
    SmithInvariants[{{12, 0, 0}, {0, 6, 0}, {0, 0, 2}}],
    SmithInvariants[{{4, 6}, {6, 10}, {2, 2}}],
    SmithInvariants[{{1, 2, 3, 4}, {2, 4, 6, 8}, {3, 6, 9, 13}}],
    SmithInvariants[{{-3, 1, 7}, {5, -2, 1}, {1, 0, 15}, {2, -1, -6}}],
    SmithInvariants[{{6, 10, 15}}],
    SmithInvariants[{{6}, {10}, {15}}],
    SmithInvariants[{{0, 0, 0}, {0, 0, 0}}]
  },
  {{2, 2, 156}, {1, 6}, {2, 12}, {2, 6, 12}, {2, 2}, {1, 1}, {1, 1, 2}, {1}, {1}, {}},
  TestID -> "Graded-SmithInvariants"
]

(* the same from the built-in Smith decomposition *)

VerificationTest[
  AllTrue[
    {
      {{2, 4, 4}, {-6, 6, 12}, {10, 4, 16}},
      {{12, 0, 0}, {0, 6, 0}, {0, 0, 2}},
      {{4, 6}, {6, 10}, {2, 2}},
      {{1, 2, 3, 4}, {2, 4, 6, 8}, {3, 6, 9, 13}},
      {{-3, 1, 7}, {5, -2, 1}, {1, 0, 15}, {2, -1, -6}},
      {{6, 10, 15}}
    },
    Function[m,
      SmithInvariants[m] === DeleteCases[Abs[Diagonal[SmithDecomposition[m][[2]]]], 0]
    ]
  ],
  True,
  TestID -> "Graded-SmithInvariants-builtin"
]

(* a circle: Z in degrees 0 and 1.  A disc: a point.  An edge glued to its
   vertex twice, and a face glued to a loop three times: torsion *)

VerificationTest[
  {
    ChainHomology[
      {{v1, v2, v3}, {e12, e23, e13}},
      Function[e,
        Replace[e, {
          e12 -> LBasis[v2] - LBasis[v1],
          e23 -> LBasis[v3] - LBasis[v2],
          e13 -> LBasis[v3] - LBasis[v1],
          _ -> 0
        }]
      ]
    ],
    ChainHomology[
      {{v1, v2, v3}, {e12, e23, e13}, {f123}},
      Function[e,
        Replace[e, {
          e12 -> LBasis[v2] - LBasis[v1],
          e23 -> LBasis[v3] - LBasis[v2],
          e13 -> LBasis[v3] - LBasis[v1],
          f123 -> LBasis[e23] - LBasis[e13] + LBasis[e12],
          _ -> 0
        }]
      ]
    ],
    ChainHomology[{{v1}, {e12}}, Function[e, Replace[e, {e12 -> 2 LBasis[v1], _ -> 0}]]],
    ChainHomology[
      {{v1}, {e12}, {f123}},
      Function[e, Replace[e, {f123 -> 3 LBasis[e12], _ -> 0}]]
    ]
  },
  {
    {{0}, {0}},
    {{0}, {}, {}},
    {{2}, {}},
    {{0}, {3}, {}}
  },
  TestID -> "Graded-ChainHomology"
]

(* a basis over the integers of the integer solutions of m . x = 0: the
   solutions, the right number of them, and nothing missing (the basis is
   saturated: its invariant factors are all 1) *)

VerificationTest[
  {
    IntegerKernel[{{2, 4, 6}}],
    IntegerKernel[{{1, 0}, {0, 1}}],
    IntegerKernel[{{0, 0}}],
    AllTrue[
      {
        {{2, 4, 6}},
        {{1, 1, 0}, {0, 1, 1}},
        {{2, 0, 3}, {0, 4, 6}},
        {{6, 10, 15}},
        {{1, 2}, {2, 4}, {3, 6}},
        {{2, 4, 4}, {-6, 6, 12}, {10, 4, 16}},
        {{1, 2, 3, 4}, {2, 4, 6, 8}, {3, 6, 9, 13}},
        {{0, 0, 0}, {0, 0, 0}}
      },
      Function[m,
        With[{ker = IntegerKernel[m]},
          Length[ker] === Length[First[m]] - Length[SmithInvariants[m]] &&
            AllTrue[ker, Function[z, AllTrue[m . z, Function[e, e === 0]]]] &&
            (ker === {} || SmithInvariants[ker] === ConstantArray[1, Length[ker]])
        ]
      ]
    ]
  },
  {{{-2, 1, 0}, {-3, 0, 1}}, {}, {{1, 0}, {0, 1}}, True},
  TestID -> "Graded-IntegerKernel"
]

(* Betti numbers with coefficients in Z_p from the integral homology: a
   summand Z_t with p dividing t counts in its own degree and in the next *)

VerificationTest[
  {
    ModularBetti[{{0}, {0}, {2}, {}}, 2],
    ModularBetti[{{0}, {0}, {2}, {2}, {3}, {}}, 2],
    ModularBetti[{{0}, {0}, {2}, {2}, {3}, {}}, 3],
    ModularBetti[{{0}, {2}, {}, {0}}, 2],
    ModularBetti[{{0}, {2}, {}, {0}}, 3],
    ModularBetti[{{0, 0}, {4, 6}}, 2]
  },
  {{1, 1, 1, 1}, {1, 1, 1, 2, 1, 0}, {1, 1, 0, 0, 1, 1}, {1, 1, 1, 1}, {1, 0, 0, 1}, {2, 2}},
  TestID -> "Graded-modular-Betti"
]
