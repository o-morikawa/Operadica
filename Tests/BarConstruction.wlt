(* BarConstruction: the iterated bar construction of a finite abelian group
   and the Eilenberg-MacLane spaces K(A, n).
   The expected values are those of reference/bar_reference.py. *)

(* ---------------------------------------------------------------------- *)
(* generators                                                             *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    BarGenerators[{3}, 0, 0],
    BarGenerators[{3}, 1, 2],
    BarGenerators[{2}, 2, 2],
    BarGenerators[{2}, 2, 3],
    BarGenerators[{2}, 2, 4],
    BarGenerators[{2}, 3, 5],
    BarGenerators[{2, 2}, 1, 1],
    BarGenerators[{2}, 2, 1],
    BarGenerators[{2}, 1, 0]
  },
  {
    {{1}, {2}},
    {BarWord[{1}, {1}], BarWord[{1}, {2}], BarWord[{2}, {1}], BarWord[{2}, {2}]},
    {BarWord[BarWord[{1}]]},
    {BarWord[BarWord[{1}, {1}]]},
    {BarWord[BarWord[{1}], BarWord[{1}]], BarWord[BarWord[{1}, {1}, {1}]]},
    {BarWord[BarWord[BarWord[{1}], BarWord[{1}]]], BarWord[BarWord[BarWord[{1}, {1}, {1}]]]},
    {BarWord[{0, 1}], BarWord[{1, 0}], BarWord[{1, 1}]},
    {},
    {}
  },
  TestID -> "BarConstruction-generators"
]

(* the numbers of generators of B^1, ..., B^4 in the degrees n, ..., n + 3 *)

VerificationTest[
  Table[
    Table[Length[BarGenerators[orders, n, k]], {n, 1, 4}, {k, n, n + 3}],
    {orders, {{2}, {3}, {4}, {2, 2}}}
  ],
  {
    {{1, 1, 1, 1}, {1, 1, 2, 3}, {1, 1, 2, 4}, {1, 1, 2, 4}},
    {{2, 4, 8, 16}, {2, 4, 12, 32}, {2, 4, 12, 36}, {2, 4, 12, 36}},
    {{3, 9, 27, 81}, {3, 9, 36, 135}, {3, 9, 36, 144}, {3, 9, 36, 144}},
    {{3, 9, 27, 81}, {3, 9, 36, 135}, {3, 9, 36, 144}, {3, 9, 36, 144}}
  },
  TestID -> "BarConstruction-generator-counts"
]

VerificationTest[
  {
    BarLevel[{1}],
    BarLevel[BarWord[{1}, {2}]],
    BarLevel[BarWord[BarWord[{1}], BarWord[{2}]]],
    BarDegree[{1}],
    BarDegree[BarWord[{1}, {2}, {1}]],
    BarDegree[BarWord[BarWord[{1}], BarWord[{2}]]],
    BarDegree[BarWord[BarWord[{1}, {2}], BarWord[{1}]]],
    BarDegree[BarWord[BarWord[BarWord[{1}]], BarWord[BarWord[{2}]]]],
    AllTrue[BarGenerators[{3}, 3, 6], Function[g, BarLevel[g] === 3 && BarDegree[g] === 6]]
  },
  {0, 1, 2, 0, 3, 4, 5, 6, True},
  TestID -> "BarConstruction-level-and-degree"
]

(* ---------------------------------------------------------------------- *)
(* the differential                                                       *)
(* ---------------------------------------------------------------------- *)

(* B^1 is the complex of group homology: d[a|b] = [b] - [a+b] + [a], and the
   word [0] is dropped.  Here the group is Z_3 *)

VerificationTest[
  With[{d = BarDifferential[{3}]},
    {
      d[BarWord[{1}]],
      d[BarWord[{1}, {2}]],
      d[BarWord[{1}, {1}]],
      d[BarWord[{1}, {2}, {1}]],
      d[BarWord[{2}, {2}, {1}]],
      d[BarWord[{1}, {1}, {1}, {2}]]
    }
  ],
  {
    0,
    LBasis[BarWord[{2}]] + LBasis[BarWord[{1}]],
    -LBasis[BarWord[{2}]] + 2 LBasis[BarWord[{1}]],
    LBasis[BarWord[{2}, {1}]] - LBasis[BarWord[{1}, {2}]],
    -LBasis[BarWord[{1}, {1}]] + LBasis[BarWord[{2}, {1}]] - LBasis[BarWord[{2}, {2}]],
    -LBasis[BarWord[{2}, {1}, {2}]] + LBasis[BarWord[{1}, {2}, {2}]] +
      LBasis[BarWord[{1}, {1}, {2}]] + LBasis[BarWord[{1}, {1}, {1}]]
  },
  TestID -> "BarConstruction-differential-level-1"
]

(* B^2: the letters are multiplied by the shuffle product.
   d[a || b] = [[a|b]] - [[b|a]] *)

VerificationTest[
  With[{d = BarDifferential[{3}]},
    {
      d[BarWord[BarWord[{1}], BarWord[{2}]]],
      d[BarWord[BarWord[{1}, {2}], BarWord[{1}]]],
      d[BarWord[BarWord[{1}], BarWord[{1}, {2}]]],
      d[BarWord[BarWord[{1}, {1}, {2}]]],
      d[BarWord[BarWord[{1}], BarWord[{2}], BarWord[{1}]]]
    }
  ],
  {
    LBasis[BarWord[BarWord[{1}, {2}]]] - LBasis[BarWord[BarWord[{2}, {1}]]],
    -LBasis[BarWord[BarWord[{2}], BarWord[{1}]]] - LBasis[BarWord[BarWord[{1}], BarWord[{1}]]] -
      LBasis[BarWord[BarWord[{1}, {2}, {1}]]],
    LBasis[BarWord[BarWord[{1}, {2}, {1}]]] - LBasis[BarWord[BarWord[{1}], BarWord[{2}]]] -
      LBasis[BarWord[BarWord[{1}], BarWord[{1}]]],
    LBasis[BarWord[BarWord[{2}, {2}]]] - LBasis[BarWord[BarWord[{1}, {2}]]] +
      LBasis[BarWord[BarWord[{1}, {1}]]],
    LBasis[BarWord[BarWord[{1}, {2}], BarWord[{1}]]] - LBasis[BarWord[BarWord[{2}, {1}], BarWord[{1}]]] +
      LBasis[BarWord[BarWord[{1}], BarWord[{2}, {1}]]] - LBasis[BarWord[BarWord[{1}], BarWord[{1}, {2}]]]
  },
  TestID -> "BarConstruction-differential-level-2"
]

VerificationTest[
  With[{d = BarDifferential[{3}]},
    {
      d[BarWord[BarWord[{1}, {1}], BarWord[{2}, {2}]]],
      d[BarWord[BarWord[BarWord[{1}]], BarWord[BarWord[{2}]]]],
      d[BarWord[BarWord[BarWord[{1}, {2}]], BarWord[BarWord[{1}]]]],
      d[2 LBasis[BarWord[{1}, {2}]] - LBasis[BarWord[{1}, {1}]]]
    }
  ],
  {
    LBasis[BarWord[BarWord[{2}], BarWord[{2}, {2}]]] - 2 LBasis[BarWord[BarWord[{1}], BarWord[{2}, {2}]]] -
      LBasis[BarWord[BarWord[{1}, {1}, {2}, {2}]]] + LBasis[BarWord[BarWord[{1}, {2}, {1}, {2}]]] -
      LBasis[BarWord[BarWord[{1}, {2}, {2}, {1}]]] - LBasis[BarWord[BarWord[{2}, {1}, {1}, {2}]]] +
      LBasis[BarWord[BarWord[{2}, {1}, {2}, {1}]]] - LBasis[BarWord[BarWord[{2}, {2}, {1}, {1}]]] -
      LBasis[BarWord[BarWord[{1}, {1}], BarWord[{1}]]] + 2 LBasis[BarWord[BarWord[{1}, {1}], BarWord[{2}]]],
    -LBasis[BarWord[BarWord[BarWord[{1}], BarWord[{2}]]]] - LBasis[BarWord[BarWord[BarWord[{2}], BarWord[{1}]]]],
    LBasis[BarWord[BarWord[BarWord[{2}]], BarWord[BarWord[{1}]]]] +
      LBasis[BarWord[BarWord[BarWord[{1}]], BarWord[BarWord[{1}]]]] +
      LBasis[BarWord[BarWord[BarWord[{1}, {2}], BarWord[{1}]]]] +
      LBasis[BarWord[BarWord[BarWord[{1}], BarWord[{1}, {2}]]]],
    3 LBasis[BarWord[{2}]]
  },
  TestID -> "BarConstruction-differential-level-3"
]

(* d d = 0 on all generators: B^1, ..., B^4 of Z_2 and Z_3, and B^2 of Z_2 x Z_2 *)

VerificationTest[
  {
    Table[
      AllTrue[
        Flatten[Table[BarGenerators[orders, n, k], {k, n, n + 4}], 1],
        Function[g, BarDifferential[orders][BarDifferential[orders][g]] === 0]
      ],
      {orders, {{2}, {3}}}, {n, 1, 4}
    ],
    AllTrue[
      Flatten[Table[BarGenerators[{2, 2}, 2, k], {k, 2, 5}], 1],
      Function[g, BarDifferential[{2, 2}][BarDifferential[{2, 2}][g]] === 0]
    ],
    (* the differential lowers the degree by one *)
    AllTrue[
      BarGenerators[{3}, 2, 5],
      Function[g,
        AllTrue[LinearTerms[BarDifferential[{3}][g]], Function[tm, BarDegree[tm[[2]]] === 4]]
      ]
    ]
  },
  {{{True, True, True, True}, {True, True, True, True}}, True, True},
  TestID -> "BarConstruction-differential-squares-to-zero"
]

(* ---------------------------------------------------------------------- *)
(* the product                                                            *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{mul = BarProduct[{3}]},
    {
      mul[{1}, {2}],
      mul[{1}, {1}],
      mul[BarWord[{1}], BarWord[{2}]],
      mul[BarWord[{1}, {2}], BarWord[{1}]],
      mul[BarWord[{1}], BarWord[{1}, {2}]],
      mul[BarWord[{1}, {2}], BarWord[{2}, {1}]],
      mul[BarWord[BarWord[{1}]], BarWord[BarWord[{2}]]],
      mul[BarWord[BarWord[{1}, {2}]], BarWord[BarWord[{1}]]],
      mul[BarWord[BarWord[{1}], BarWord[{2}]], BarWord[BarWord[{1}]]],
      mul[LBasis[BarWord[{1}]] + LBasis[BarWord[{2}]], 2 LBasis[BarWord[{1}]]]
    }
  ],
  {
    0,
    LBasis[{2}],
    LBasis[BarWord[{1}, {2}]] - LBasis[BarWord[{2}, {1}]],
    LBasis[BarWord[{1}, {2}, {1}]],
    LBasis[BarWord[{1}, {2}, {1}]],
    LBasis[BarWord[{1}, {2}, {1}, {2}]] + LBasis[BarWord[{2}, {1}, {2}, {1}]],
    LBasis[BarWord[BarWord[{1}], BarWord[{2}]]] + LBasis[BarWord[BarWord[{2}], BarWord[{1}]]],
    LBasis[BarWord[BarWord[{1}, {2}], BarWord[{1}]]] + LBasis[BarWord[BarWord[{1}], BarWord[{1}, {2}]]],
    LBasis[BarWord[BarWord[{1}], BarWord[{2}], BarWord[{1}]]] +
      2 LBasis[BarWord[BarWord[{1}], BarWord[{1}], BarWord[{2}]]],
    2 LBasis[BarWord[{2}, {1}]] - 2 LBasis[BarWord[{1}, {2}]]
  },
  TestID -> "BarConstruction-product"
]

(* graded commutative: x y = (-1)^(|x| |y|) y x.  For words of odd degree
   this makes the squares vanish, as for differential forms *)

VerificationTest[
  Table[
    With[{gs = Flatten[Table[BarGenerators[{3}, n, k], {k, n, n + 2}], 1], mul = BarProduct[{3}]},
      AllTrue[
        Tuples[gs, 2],
        Function[pair,
          LinearZeroQ[
            mul[pair[[1]], pair[[2]]] -
              (-1)^(BarDegree[pair[[1]]] BarDegree[pair[[2]]]) mul[pair[[2]], pair[[1]]]
          ]
        ]
      ]
    ],
    {n, 1, 2}
  ],
  {True, True},
  TestID -> "BarConstruction-product-graded-commutative"
]

VerificationTest[
  Table[
    With[{gs = Flatten[Table[BarGenerators[{3}, n, k], {k, n, n + 1}], 1], mul = BarProduct[{3}]},
      AllTrue[
        Tuples[gs, 3],
        Function[tr,
          LinearZeroQ[
            mul[mul[tr[[1]], tr[[2]]], LBasis[tr[[3]]]] - mul[LBasis[tr[[1]]], mul[tr[[2]], tr[[3]]]]
          ]
        ]
      ]
    ],
    {n, 1, 2}
  ],
  {True, True},
  TestID -> "BarConstruction-product-associative"
]

(* d is a derivation: d(x y) = dx y + (-1)^|x| x dy.  This is what allows the
   bar construction to be iterated *)

VerificationTest[
  Table[
    With[{
        gs = Flatten[Table[BarGenerators[orders, n, k], {k, n, n + 2}], 1],
        mul = BarProduct[orders],
        d = BarDifferential[orders]
      },
      AllTrue[
        Tuples[gs, 2],
        Function[pair,
          LinearZeroQ[
            d[mul[pair[[1]], pair[[2]]]] -
              mul[d[pair[[1]]], LBasis[pair[[2]]]] -
              (-1)^BarDegree[pair[[1]]] mul[LBasis[pair[[1]]], d[pair[[2]]]]
          ]
        ]
      ]
    ],
    {orders, {{2}, {3}}}, {n, 1, 2}
  ],
  {{True, True}, {True, True}},
  TestID -> "BarConstruction-Leibniz"
]

(* the suspension x -> [x] raises the level and the degree, and d[x] = -[dx] *)

VerificationTest[
  {
    BarSuspension[BarWord[{1}, {2}]],
    BarSuspension[{1}],
    BarSuspension[LBasis[BarWord[{1}]] - 2 LBasis[BarWord[{2}]]],
    Table[
      AllTrue[
        Flatten[Table[BarGenerators[{3}, n, k], {k, n, n + 3}], 1],
        Function[g,
          MemberQ[BarGenerators[{3}, n + 1, BarDegree[g] + 1], BarSuspension[g]] &&
            LinearZeroQ[
              BarDifferential[{3}][BarSuspension[g]] + BarSuspension[BarDifferential[{3}][g]]
            ]
        ]
      ],
      {n, 1, 3}
    ]
  },
  {
    BarWord[BarWord[{1}, {2}]],
    BarWord[{1}],
    LBasis[BarWord[BarWord[{1}]]] - 2 LBasis[BarWord[BarWord[{2}]]],
    {True, True, True}
  },
  TestID -> "BarConstruction-suspension"
]

(* ---------------------------------------------------------------------- *)
(* homology: the Eilenberg-MacLane spaces                                 *)
(* ---------------------------------------------------------------------- *)

(* K(Z_N, 1), the classifying space of Z_N (a lens space of infinite
   dimension): Z_N in odd degrees *)

VerificationTest[
  {
    Table[BarHomology[{nn}, 1, k], {nn, 2, 5}, {k, 1, 3}],
    Table[BarHomology[{2}, 1, k], {k, 1, 6}]
  },
  {
    {{{2}, {}, {2}}, {{3}, {}, {3}}, {{4}, {}, {4}}, {{5}, {}, {5}}},
    {{2}, {}, {2}, {}, {2}, {}}
  },
  TestID -> "BarConstruction-homology-K1"
]

(* K(Z_N, 2): H_4 = Z_(N gcd(2, N)), the home of the quadratic forms *)

VerificationTest[
  {
    Table[BarHomology[{nn}, 2, k], {nn, 2, 4}, {k, 2, 4}],
    Table[BarHomology[{2}, 2, k], {k, 1, 6}]
  },
  {
    {{{2}, {}, {4}}, {{3}, {}, {3}}, {{4}, {}, {8}}},
    {{}, {2}, {}, {4}, {2}, {2}}
  },
  TestID -> "BarConstruction-homology-K2"
]

(* K(Z_N, 3) and K(Z_N, 4): H_(n+2) = Z_gcd(2, N), the stable value *)

VerificationTest[
  {
    Table[BarHomology[{nn}, 3, k], {nn, 2, 4}, {k, 3, 5}],
    Table[BarHomology[{nn}, 4, k], {nn, 2, 4}, {k, 4, 6}],
    Table[BarHomology[{2}, 3, k], {k, 1, 7}]
  },
  {
    {{{2}, {}, {2}}, {{3}, {}, {}}, {{4}, {}, {2}}},
    {{{2}, {}, {2}}, {{3}, {}, {}}, {{4}, {}, {2}}},
    {{}, {}, {2}, {}, {2}, {2}, {2}}
  },
  TestID -> "BarConstruction-homology-K3-K4"
]

(* a group with two generators *)

VerificationTest[
  {
    Table[BarHomology[{2, 2}, 1, k], {k, 1, 3}],
    Table[BarHomology[{2, 2}, 2, k], {k, 2, 4}],
    Table[BarHomology[{2, 2}, 3, k], {k, 3, 5}],
    Table[BarHomology[{2, 4}, 1, k], {k, 1, 2}]
  },
  {
    {{2, 2}, {2}, {2, 2, 2}},
    {{2, 2}, {}, {2, 4, 4}},
    {{2, 2}, {}, {2, 2}},
    {{2, 4}, {2}}
  },
  TestID -> "BarConstruction-homology-two-generators"
]

(* ---------------------------------------------------------------------- *)
(* the simplicial sets K(A, n): flat n-form gauge fields on simplices     *)
(* ---------------------------------------------------------------------- *)

(* a 2-simplex of K(Z_2, 1) is a flat Z_2 gauge field on a triangle, with
   the values on the edges 01, 02, 12 *)

VerificationTest[
  {
    EilenbergMacLaneSimplices[{2}, 1, 2],
    EilenbergMacLaneSimplices[{2}, 2, 3],
    EilenbergMacLaneSimplices[{3}, 2, 1],
    Table[Length[EilenbergMacLaneSimplices[{2}, 2, k]], {k, 0, 4}],
    Table[Length[EilenbergMacLaneSimplices[{3}, 1, k]], {k, 0, 4}],
    Table[Length[EilenbergMacLaneSimplices[{2}, 3, k]], {k, 0, 5}]
  },
  {
    {
      EMSimplex[2, {{0}, {0}, {0}}], EMSimplex[2, {{0}, {1}, {1}}],
      EMSimplex[2, {{1}, {0}, {1}}], EMSimplex[2, {{1}, {1}, {0}}]
    },
    {
      EMSimplex[3, {{0}, {0}, {0}, {0}}], EMSimplex[3, {{0}, {0}, {1}, {1}}],
      EMSimplex[3, {{0}, {1}, {0}, {1}}], EMSimplex[3, {{0}, {1}, {1}, {0}}],
      EMSimplex[3, {{1}, {0}, {0}, {1}}], EMSimplex[3, {{1}, {0}, {1}, {0}}],
      EMSimplex[3, {{1}, {1}, {0}, {0}}], EMSimplex[3, {{1}, {1}, {1}, {1}}]
    },
    {EMSimplex[1, {}]},
    {1, 1, 2, 8, 64},
    {1, 3, 9, 27, 81},
    {1, 1, 1, 2, 16, 1024}
  },
  TestID -> "BarConstruction-EM-simplices"
]

VerificationTest[
  {
    AllTrue[EilenbergMacLaneSimplices[{2}, 2, 4], EilenbergMacLaneCocycleQ[{2}, 2]],
    AllTrue[EilenbergMacLaneSimplices[{3}, 1, 3], EilenbergMacLaneCocycleQ[{3}, 1]],
    AllTrue[EilenbergMacLaneSimplices[{2, 4}, 1, 2], EilenbergMacLaneCocycleQ[{2, 4}, 1]],
    EilenbergMacLaneCocycleQ[{2}, 2][EMSimplex[3, {{1}, {0}, {0}, {0}}]],
    EilenbergMacLaneCocycleQ[{3}, 1][EMSimplex[2, {{1}, {1}, {1}}]],
    EilenbergMacLaneCocycleQ[{3}, 1][EMSimplex[2, {{1}, {2}, {1}}]]
  },
  {True, True, True, False, False, True},
  TestID -> "BarConstruction-EM-flat"
]

(* faces restrict the field, degeneracies pull it back *)

VerificationTest[
  With[{x = EMSimplex[3, {{0}, {1}, {2}, {1}, {2}, {1}}], y = EMSimplex[3, {{1}, {0}, {1}, {0}}]},
    {
      Table[EilenbergMacLaneFace[1][x, i], {i, 0, 3}],
      EilenbergMacLaneDegeneracy[{3}, 1][x, 0],
      EilenbergMacLaneDegeneracy[{3}, 1][x, 2],
      Table[EilenbergMacLaneFace[2][y, i], {i, 0, 3}],
      EilenbergMacLaneDegeneracy[{2}, 2][y, 1]
    }
  ],
  {
    {
      EMSimplex[2, {{1}, {2}, {1}}], EMSimplex[2, {{1}, {2}, {1}}],
      EMSimplex[2, {{0}, {2}, {2}}], EMSimplex[2, {{0}, {1}, {1}}]
    },
    EMSimplex[4, {{0}, {0}, {1}, {2}, {0}, {1}, {2}, {1}, {2}, {1}}],
    EMSimplex[4, {{0}, {1}, {1}, {2}, {1}, {1}, {2}, {0}, {1}, {1}}],
    {EMSimplex[2, {{0}}], EMSimplex[2, {{1}}], EMSimplex[2, {{0}}], EMSimplex[2, {{1}}]},
    EMSimplex[4, {{0}, {1}, {0}, {1}, {0}, {1}, {0}, {0}, {0}, {0}}]
  },
  TestID -> "BarConstruction-EM-faces-and-degeneracies"
]

(* the simplicial identities d_i d_j = d_(j-1) d_i for i < j, and
   d_i s_i = d_(i+1) s_i = 1 *)

VerificationTest[
  Table[
    With[{
        face = EilenbergMacLaneFace[spec[[2]]],
        deg = EilenbergMacLaneDegeneracy[spec[[1]], spec[[2]]],
        k = spec[[3]]
      },
      AllTrue[
        EilenbergMacLaneSimplices[spec[[1]], spec[[2]], k],
        Function[x,
          AllTrue[
            Subsets[Range[0, k], {2}],
            Function[ij, face[face[x, ij[[2]]], ij[[1]]] === face[face[x, ij[[1]]], ij[[2]] - 1]]
          ] &&
          AllTrue[
            Range[0, k],
            Function[i, face[deg[x, i], i] === x && face[deg[x, i], i + 1] === x]
          ]
        ]
      ]
    ],
    {spec, {{{3}, 1, 3}, {{2}, 2, 4}, {{2}, 3, 4}, {{2, 2}, 1, 2}}}
  ],
  {True, True, True, True},
  TestID -> "BarConstruction-EM-simplicial-identities"
]

(* the numbers of nondegenerate simplices *)

VerificationTest[
  Table[
    Table[
      Count[
        EilenbergMacLaneSimplices[spec[[1]], spec[[2]], k],
        _?(Function[x, ! EilenbergMacLaneDegenerateQ[spec[[1]], spec[[2]]][x]])
      ],
      {k, 0, 4}
    ],
    {spec, {{{2}, 1}, {{3}, 1}, {{2}, 2}, {{2}, 3}}}
  ],
  {{1, 1, 1, 1, 1}, {1, 2, 4, 8, 16}, {1, 0, 1, 4, 41}, {1, 0, 0, 1, 11}},
  TestID -> "BarConstruction-EM-nondegenerate"
]

(* K(A, n) has the single homotopy group pi_n = A *)

VerificationTest[
  {
    EilenbergMacLaneHomotopy[{2}, 1, 3],
    EilenbergMacLaneHomotopy[{3}, 1, 3],
    EilenbergMacLaneHomotopy[{4}, 1, 2],
    EilenbergMacLaneHomotopy[{2, 2}, 1, 2],
    EilenbergMacLaneHomotopy[{2}, 2, 3],
    EilenbergMacLaneHomotopy[{3}, 2, 3],
    EilenbergMacLaneHomotopy[{2}, 3, 4]
  },
  {
    {1, 2, 1, 1},
    {1, 3, 1, 1},
    {1, 4, 1},
    {1, 4, 1},
    {1, 1, 2, 1},
    {1, 1, 3, 1},
    {1, 1, 1, 2, 1}
  },
  TestID -> "BarConstruction-EM-homotopy"
]

(* the homology of the space is the homology of the bar construction *)

VerificationTest[
  {
    Table[EilenbergMacLaneHomology[{2}, 1, k], {k, 1, 3}],
    Table[EilenbergMacLaneHomology[{3}, 1, k], {k, 1, 3}],
    Table[EilenbergMacLaneHomology[{2, 2}, 1, k], {k, 1, 2}],
    Table[EilenbergMacLaneHomology[{2}, 2, k], {k, 1, 3}],
    EilenbergMacLaneHomology[{2}, 3, 3],
    Table[EilenbergMacLaneHomology[{3}, 1, k] === BarHomology[{3}, 1, k], {k, 1, 3}],
    Table[EilenbergMacLaneHomology[{2}, 2, k] === BarHomology[{2}, 2, k], {k, 1, 3}]
  },
  {
    {{2}, {}, {2}},
    {{3}, {}, {3}},
    {{2, 2}, {2}},
    {{}, {2}, {}},
    {2},
    {True, True, True},
    {True, True, True}
  },
  TestID -> "BarConstruction-EM-homology"
]

(* H_4(K(Z_2, 2)) = Z_4, from the 41 and 768 nondegenerate simplices of
   dimension 4 and 5: the group of which the semion, with spin 1/4, is the
   generator *)

VerificationTest[
  {EilenbergMacLaneHomology[{2}, 2, 4], BarHomology[{2}, 2, 4]},
  {{4}, {4}},
  TestID -> "BarConstruction-EM-homology-K-Z2-2-degree-4"
]

(* ---------------------------------------------------------------------- *)
(* cycles and cocycles on K(A, n)                                         *)
(* ---------------------------------------------------------------------- *)

(* K(Z_2, 1) has one nondegenerate simplex in each dimension, with boundary
   0, 2, 0, ...: one cycle in odd dimensions *)

VerificationTest[
  {
    EilenbergMacLaneCycles[{2}, 1, 1],
    Table[Length[EilenbergMacLaneCycles[{2}, 1, k]], {k, 1, 3}],
    {Length[EilenbergMacLaneCycles[{2}, 2, 3]], Length[EilenbergMacLaneCycles[{2}, 2, 4]]}
  },
  {
    {LBasis[EMSimplex[1, {{1}}]]},
    {1, 0, 1},
    {3, 38}
  },
  TestID -> "BarConstruction-EM-cycles"
]

(* a cocycle of degree 1 on K(Z_4, 1) is a character of Z_4; a / 3 is not one.
   The values of a simplex x are x[[2]], one group element for each face *)

VerificationTest[
  {
    CharacteristicCocycleQ[{4}, 1, 1, Function[x, x[[2, 1, 1]] / 4]],
    CharacteristicClassOrder[{4}, 1, 1, Function[x, x[[2, 1, 1]] / 4]],
    CharacteristicClassOrder[{4}, 1, 1, Function[x, 2 x[[2, 1, 1]] / 4]],
    CharacteristicCocycleQ[{4}, 1, 1, Function[x, x[[2, 1, 1]] / 3]]
  },
  {True, 4, 2, False},
  TestID -> "BarConstruction-characteristic-cocycle-degree-1"
]

(* the value of the field itself is a cocycle of degree n on K(Z_2, n); the
   product a b c / 2 of the values on the edges 01, 12, 23 is the cocycle of
   degree 3 on K(Z_2, 1); a / 2 on the edge 01 alone is not normalized *)

VerificationTest[
  {
    CharacteristicCocycleQ[{2}, 2, 2, Function[x, x[[2, 1, 1]] / 2]],
    CharacteristicClassOrder[{2}, 2, 2, Function[x, x[[2, 1, 1]] / 2]],
    CharacteristicCocycleQ[{2}, 1, 3, Function[x, x[[2, 1, 1]] x[[2, 4, 1]] x[[2, 6, 1]] / 2]],
    CharacteristicClassOrder[{2}, 1, 3, Function[x, x[[2, 1, 1]] x[[2, 4, 1]] x[[2, 6, 1]] / 2]],
    CharacteristicCocycleQ[{2}, 1, 3, Function[x, x[[2, 1, 1]] / 2]]
  },
  {True, 2, True, 2, False},
  TestID -> "BarConstruction-characteristic-cocycle"
]

(* ---------------------------------------------------------------------- *)
(* loop spaces of suspensions, rationally                                 *)
(* ---------------------------------------------------------------------- *)

(* the free graded Lie algebra, by {weight, degree}.  On one odd generator x
   it is spanned by x and [x, x]; on one even generator by x alone *)

VerificationTest[
  {
    FreeLieDimensions[{1}, 4],
    FreeLieDimensions[{2}, 4],
    FreeLieDimensions[{2, 2}, 4],
    FreeLieDimensions[{1, 1}, 4],
    FreeLieDimensions[{1, 2}, 4]
  },
  {
    <|{1, 1} -> 1, {2, 2} -> 1|>,
    <|{1, 2} -> 1|>,
    <|{1, 2} -> 2, {2, 4} -> 1, {3, 6} -> 2, {4, 8} -> 3|>,
    <|{1, 1} -> 2, {2, 2} -> 3, {3, 3} -> 2, {4, 4} -> 3|>,
    <|
      {1, 1} -> 1, {1, 2} -> 1, {2, 2} -> 1, {2, 3} -> 1, {3, 4} -> 1, {3, 5} -> 1,
      {4, 5} -> 1, {4, 6} -> 2, {4, 7} -> 1
    |>
  },
  TestID -> "BarConstruction-free-Lie"
]

(* Omega^2 S^4: a polynomial class of degree 2 and an exterior class of degree
   5.  Omega^3 S^4: an exterior class of degree 1 and a polynomial class of
   degree 4.  Omega^2 S^3: rationally a circle.  Omega Sigma (S^1 v S^1): the
   tensor algebra *)

VerificationTest[
  {
    LoopSuspensionDimensions[2, {2}, 4],
    LoopSuspensionDimensions[3, {1}, 4],
    LoopSuspensionDimensions[2, {1}, 4],
    LoopSuspensionDimensions[1, {1, 1}, 4],
    LoopSuspensionDimensions[2, {1, 1}, 4]
  },
  {
    <|1 -> <|2 -> 1|>, 2 -> <|4 -> 1, 5 -> 1|>, 3 -> <|6 -> 1, 7 -> 1|>, 4 -> <|8 -> 1, 9 -> 1|>|>,
    <|1 -> <|1 -> 1|>, 2 -> <|4 -> 1|>, 3 -> <|5 -> 1|>, 4 -> <|8 -> 1|>|>,
    <|1 -> <|1 -> 1|>, 2 -> <||>, 3 -> <||>, 4 -> <||>|>,
    <|1 -> <|1 -> 2|>, 2 -> <|2 -> 4|>, 3 -> <|3 -> 8|>, 4 -> <|4 -> 16|>|>,
    <|1 -> <|1 -> 2|>, 2 -> <|2 -> 1, 3 -> 1|>, 3 -> <|4 -> 2, 5 -> 2|>, 4 -> <|5 -> 1, 6 -> 4, 7 -> 3|>|>
  },
  TestID -> "BarConstruction-loop-suspension"
]

(* the polynomial algebra over Z_2 on x, Q x, Q Q x, ...: for a class of
   degree 1 the homology modulo 2 of the double loop space of the 3-sphere,
   with generators in the degrees 1, 3, 7, ... *)

VerificationTest[
  {
    KudoArakiDimensions[0, 4],
    KudoArakiDimensions[1, 4],
    Lookup[KudoArakiDimensions[0, 8], 8]
  },
  {
    <|1 -> <|0 -> 1|>, 2 -> <|0 -> 1, 1 -> 1|>, 3 -> <|0 -> 1, 1 -> 1|>,
      4 -> <|0 -> 1, 1 -> 1, 2 -> 1, 3 -> 1|>|>,
    <|1 -> <|1 -> 1|>, 2 -> <|2 -> 1, 3 -> 1|>, 3 -> <|3 -> 1, 4 -> 1|>,
      4 -> <|4 -> 1, 5 -> 1, 6 -> 1, 7 -> 1|>|>,
    <|0 -> 1, 1 -> 1, 2 -> 1, 3 -> 2, 4 -> 2, 5 -> 1, 6 -> 1, 7 -> 1|>
  },
  TestID -> "BarConstruction-Kudo-Araki"
]
