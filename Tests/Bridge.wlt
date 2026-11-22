(* Bridge: statements that connect the layers *)

(* ---------------------------------------------------------------------- *)
(* operad <-> lattice                                                     *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {CupAlgebraOverAsQ[2], CupAlgebraOverAsQ[3]},
  {True, True},
  TestID -> "Bridge-cup-algebra-over-As"
]

(* the higher cup products are the arity-2 part of an E-infinity action *)

VerificationTest[
  {EInfinityArityTwoQ[2], EInfinityArityTwoQ[3]},
  {True, True},
  TestID -> "Bridge-E-infinity-arity-two"
]

(* ---------------------------------------------------------------------- *)
(* operad <-> operad: the homology of the little cubes is P_n             *)
(* ---------------------------------------------------------------------- *)

(* two cubes: the sphere S^(n-1) carries the product (degree 0) and the
   bracket (degree n - 1); three little squares: 1, 3, 2 is the Gerstenhaber
   operad in arity 3; little intervals: k! components, the associative operad *)

VerificationTest[
  {
    Table[LittleCubesHomologyQ[n, 2], {n, 1, 4}],
    LittleCubesHomologyQ[2, 3],
    LittleCubesHomologyQ[1, 3],
    LittleCubesHomologyQ[1, 4]
  },
  {{True, True, True, True}, True, True, True},
  TestID -> "Bridge-little-cubes-homology"
]

(* control: the Betti numbers distinguish the operads P_n *)

VerificationTest[
  With[{betti = SimplicialBetti[FacetNerve[SeparationNerve[2, 3]]]},
    {
      Table[Lookup[OperadDimensionsByDegree[GerstenhaberOperad[], 3], Key[j], 0], {j, 0, 5}] === betti,
      Table[Lookup[OperadDimensionsByDegree[PoissonOperad[3], 3], Key[j], 0], {j, 0, 5}] === betti,
      Table[Lookup[OperadDimensionsByDegree[PoissonOperad[], 3], Key[j], 0], {j, 0, 5}] === betti
    }
  ],
  {True, False, False},
  TestID -> "Bridge-little-cubes-homology-control"
]

(* the same for the stages of the Barratt-Eccles operad, a combinatorial E_n
   operad; it reaches three points in three dimensions, and it agrees with the
   nerve of the little squares *)

VerificationTest[
  {
    Table[BarrattEcclesHomologyQ[n, 2], {n, 1, 4}],
    BarrattEcclesHomologyQ[1, 3],
    BarrattEcclesHomologyQ[2, 3],
    BarrattEcclesHomologyQ[3, 3],
    BarrattEcclesBetti[2, 3] === Take[SimplicialBetti[FacetNerve[SeparationNerve[2, 3]]], 4]
  },
  {{True, True, True, True}, True, True, True, True},
  TestID -> "Bridge-Barratt-Eccles-homology"
]

(* ---------------------------------------------------------------------- *)
(* operad <-> category                                                    *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    ReassociationPhase[Semion[], OpTensor[OpTensor[OpLeaf, OpLeaf], OpLeaf], {{1}, {1}, {1}}],
    ReassociationPhase[Semion[], OpTensor[OpLeaf, OpTensor[OpLeaf, OpLeaf]], {{1}, {1}, {1}}],
    ReassociationPhase[VecZN[3, 1],
      OpTensor[OpTensor[OpTensor[OpLeaf, OpLeaf], OpLeaf], OpLeaf], {{1}, {2}, {2}, {1}}]
  },
  {1/2, 0, 0},
  TestID -> "Bridge-reassociation-phase"
]

VerificationTest[
  Sort[ReassociationSteps[VecZN[3, 1],
    OpTensor[OpTensor[OpTensor[OpLeaf, OpLeaf], OpLeaf], OpLeaf], {{1}, {2}, {2}, {1}}]],
  Sort[{
    {0, OpTensor[OpTensor[{1}, {2}], OpTensor[{2}, {1}]]},
    {1/3, OpTensor[OpTensor[{1}, OpTensor[{2}, {2}]], {1}]}
  }],
  TestID -> "Bridge-reassociation-steps"
]

(* coherence: the phase of a reassociation does not depend on the path *)

VerificationTest[
  {
    Table[MacLaneCoherenceQ[Semion[], n], {n, 3, 6}],
    Table[MacLaneCoherenceQ[VecZN[3, 1], n], {n, 3, 5}]
  },
  {{True, True, True, True}, {True, True, True}},
  TestID -> "Bridge-MacLane-coherence"
]

(* without the pentagon equation it fails, first for four objects *)

VerificationTest[
  With[{cat = PointedCategory[{3}, Function[{a, b, c}, a[[1]]^2 b[[1]] / 3]]},
    {PentagonQ[cat], MacLaneCoherenceQ[cat, 3], MacLaneCoherenceQ[cat, 4]}
  ],
  {False, True, False},
  TestID -> "Bridge-coherence-needs-pentagon"
]

(* ---------------------------------------------------------------------- *)
(* category <-> lattice                                                   *)
(* ---------------------------------------------------------------------- *)

(* the weight exp(2 pi i (p / 2n) sum P(B)) on a 't Hooft flux background of
   the four-torus is the mutual braiding of the fluxes in Z_n^(p) *)

VerificationTest[
  With[{z = {{0, 1, 2, -1}, {-1, 0, 3, 5}, {-2, -3, 0, 7}, {1, -5, -7, 0}}, dims = {2, 2, 2, 2}},
    Table[
      {PontryaginFluxPhase[np[[1]], np[[2]], z, dims], FluxBraidingPhase[ZNAnyons[np[[1]], np[[2]]], z]},
      {np, {{2, 1}, {4, 1}, {4, 3}, {6, 2}}}
    ]
  ],
  {{0, 0}, {1/2, 1/2}, {1/2, 1/2}, {0, 0}},
  TestID -> "Bridge-flux-braiding"
]

VerificationTest[
  With[{z = {{0, 1, 0, 0}, {-1, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, -1, 0}}},
    {
      PontryaginFluxPhase[4, 1, z, {2, 2, 2, 2}],
      FluxBraidingPhase[ZNAnyons[4, 1], z],
      MutualBraiding[ZNAnyons[4, 1], {1}, {1}]
    }
  ],
  {1/4, 1/4, 1/4},
  TestID -> "Bridge-flux-braiding-unit"
]

(* ---------------------------------------------------------------------- *)
(* delooping <-> category                                                 *)
(*   the associator and the braiding are a cochain on the iterated bar    *)
(*   construction: phi[a|b|c] = w(a, b, c), phi[a || b] = c(a, b)         *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{cat = ZNAnyons[4, 1]},
    {
      BarCochainValue[cat, BarWord[{3}, {3}, {3}]],
      BarCochainValue[cat, BarWord[BarWord[{3}, {3}, {3}]]],
      BarCochainValue[cat, BarWord[BarWord[{1}], BarWord[{3}]]],
      BarCochainValue[cat, BarWord[BarWord[BarWord[{1}], BarWord[{3}]]]],
      BarCochainValue[cat, BarWord[BarWord[BarWord[{3}, {3}, {3}]]]],
      BarCochainValue[cat,
        2 LBasis[BarWord[BarWord[{1}], BarWord[{3}]]] - LBasis[BarWord[BarWord[{3}], BarWord[{3}]]] +
          LBasis[BarWord[BarWord[{3}, {3}, {3}]]]
      ],
      BarCochainValue[cat, 0]
    }
  ],
  {1/2, 1/2, 3/8, 3/8, 1/2, 1/8, 0},
  TestID -> "Bridge-bar-cochain"
]

(* the coboundary of the cochain is made of the pentagon and hexagon
   expressions (left side minus right side) and of the double braiding.
   The data are generic, so that all of them are non-zero somewhere:
     B^1  [a|b|c|d]    pentagon
     B^2  [[a|b|c|d]]  - pentagon,   [a|b || c]  hexagon 2,   [a || b|c]  hexagon 1
     B^3  the suspensions of these with the opposite signs, and
          [a ||| b]    - (c(a, b) + c(b, a))
   Each entry: the number of generators, the number of vanishing values, and
   the agreement of all values *)

VerificationTest[
  Table[
    Module[{w, c, plus, pent, hex1, hex2, cat, expected},
      w = Function[{x, y, z},
        If[x[[1]] y[[1]] z[[1]] === 0,
          0,
          (x[[1]]^2 y[[1]] + 2 y[[1]] z[[1]]^2 + 3 x[[1]] z[[1]] + 1) / 7
        ]
      ];
      c = Function[{x, y},
        If[x[[1]] y[[1]] === 0, 0, (x[[1]] y[[1]]^2 + 2 x[[1]] + 1) / 5]
      ];
      plus = Function[{x, y}, Mod[x + y, {nn}]];
      pent = Function[{h1, h2, h3, h4},
        w[h2, h3, h4] - w[plus[h1, h2], h3, h4] + w[h1, plus[h2, h3], h4] -
          w[h1, h2, plus[h3, h4]] + w[h1, h2, h3]
      ];
      hex1 = Function[{h1, h2, h3},
        (w[h2, h3, h1] + c[h1, plus[h2, h3]] + w[h1, h2, h3]) -
          (c[h1, h3] + w[h2, h1, h3] + c[h1, h2])
      ];
      hex2 = Function[{h1, h2, h3},
        (-w[h3, h1, h2] + c[plus[h1, h2], h3] - w[h1, h2, h3]) -
          (c[h1, h3] - w[h1, h3, h2] + c[h2, h3])
      ];
      cat = PointedCategory[{nn}, w, c];
      expected = Function[g,
        Mod[
          Replace[g, {
            BarWord[u1_List, u2_List, u3_List, u4_List] :> pent[u1, u2, u3, u4],
            BarWord[BarWord[u1_List, u2_List, u3_List, u4_List]] :> -pent[u1, u2, u3, u4],
            BarWord[BarWord[u1_List, u2_List], BarWord[u3_List]] :> hex2[u1, u2, u3],
            BarWord[BarWord[u1_List], BarWord[u2_List, u3_List]] :> hex1[u1, u2, u3],
            BarWord[BarWord[BarWord[u1_List, u2_List, u3_List, u4_List]]] :> pent[u1, u2, u3, u4],
            BarWord[BarWord[BarWord[u1_List, u2_List], BarWord[u3_List]]] :> -hex2[u1, u2, u3],
            BarWord[BarWord[BarWord[u1_List], BarWord[u2_List, u3_List]]] :> -hex1[u1, u2, u3],
            BarWord[BarWord[BarWord[u1_List]], BarWord[BarWord[u2_List]]] :> -c[u1, u2] - c[u2, u1]
          }],
          1
        ]
      ];
      Table[
        With[{table = BarCoboundaryTable[cat, n]},
          {
            Length[table],
            Count[Values[table], 0],
            AllTrue[Keys[table], Function[g, Lookup[table, Key[g]] === expected[g]]]
          }
        ],
        {n, 1, 3}
      ]
    ],
    {nn, {3, 4}}
  ],
  {
    {{16, 5, True}, {32, 5, True}, {36, 5, True}},
    {{81, 11, True}, {135, 13, True}, {144, 13, True}}
  },
  TestID -> "Bridge-bar-coboundary-pentagon-hexagon"
]

(* an E_n-monoidal structure is a cocycle of degree n + 2 on B^n: monoidal,
   braided and symmetric are the cases n = 1, 2, 3 *)

VerificationTest[
  Map[
    Function[cat, {BarCocycleQ[cat, 1], BarCocycleQ[cat, 2], BarCocycleQ[cat, 3]}],
    {
      SuperVec[],
      Semion[],
      ToricCode[],
      VecZN[3, 1],
      PointedCategory[{3}, VecZN[3, 1]["Associator"], Function[{x, y}, 0]],
      ZNAnyons[3, 1]
    }
  ],
  {
    {True, True, True},
    {True, True, False},
    {True, True, False},
    {True, False, False},
    {True, False, False},
    {False, False, False}
  },
  TestID -> "Bridge-bar-cocycle"
]

VerificationTest[
  With[{
      family = Join[
        Table[ZNAnyons[2, p], {p, 0, 3}],
        Table[ZNAnyons[3, p], {p, 0, 5}],
        Table[ZNAnyons[4, p], {p, 0, 3}],
        {
          VecZN[2, 1], VecZN[3, 1], VecZN[4, 2], ToricCode[],
          PointedCategory[{3}, VecZN[3, 1]["Associator"], Function[{x, y}, 0]]
        }
      ]
    },
    {
      AllTrue[family, DeloopingClassificationQ],
      Map[EnLevel, family]
    }
  ],
  {
    True,
    {
      Infinity, 2, Infinity, 2,
      Infinity, 0, 2, 0, 2, 0,
      Infinity, 2, 2, 2,
      1, 1, 1, 2,
      1
    }
  },
  TestID -> "Bridge-delooping-classification"
]

(* the number of structures is the order of H_(n+2)(K(A, n)): on Z_N there
   are N monoidal, N gcd(2, N) braided and gcd(2, N) symmetric structures,
   and nothing changes after n = 3.  For n = 2 this is the count by the
   quadratic form of the spins *)

VerificationTest[
  {
    Table[EnStructureCount[{nn}, n], {n, 1, 4}, {nn, 2, 4}],
    Table[EnStructureCount[{2, 2}, n], {n, 1, 3}],
    Table[
      With[{valid = Select[Range[0, 2 nn - 1], Function[p, EvenQ[nn] || EvenQ[p]]]},
        Length[Union[Map[Function[p, Values[SpinTable[ZNAnyons[nn, p]]]], valid]]] ===
          EnStructureCount[{nn}, 2]
      ],
      {nn, 2, 4}
    ]
  },
  {
    {{2, 3, 4}, {4, 3, 8}, {2, 1, 2}, {2, 1, 2}},
    {8, 32, 4},
    {True, True, True}
  },
  TestID -> "Bridge-En-structure-count"
]

(* [a || a] and [a || b] + [b || a] are cycles of B^2, and the cocycle of a
   braided category takes on them the spin and the mutual braiding *)

VerificationTest[
  Table[
    With[{orders = cat["Group"], els = Rest[CategoryObjects[cat]]},
      {
        AllTrue[
          els,
          Function[a,
            BarDifferential[orders][BarWord[BarWord[a], BarWord[a]]] === 0 &&
              BarCochainValue[cat, BarWord[BarWord[a], BarWord[a]]] === TopologicalSpin[cat, a]
          ]
        ],
        AllTrue[
          Subsets[els, {2}],
          Function[ab,
            With[{
                cyc = LBasis[BarWord[BarWord[ab[[1]]], BarWord[ab[[2]]]]] +
                  LBasis[BarWord[BarWord[ab[[2]]], BarWord[ab[[1]]]]]
              },
              BarDifferential[orders][cyc] === 0 &&
                BarCochainValue[cat, cyc] === MutualBraiding[cat, ab[[1]], ab[[2]]]
            ]
          ]
        ]
      }
    ],
    {cat, {ZNAnyons[4, 1], ZNAnyons[3, 2], ToricCode[]}}
  ],
  {{True, True}, {True, True}, {True, True}},
  TestID -> "Bridge-spin-and-braiding-on-cycles"
]

(* in B^3 these cycles bound: d[a ||| b] = -[[a || b] + [b || a]] and
   d[a ||| a] = -2 [[a || a]].  A symmetric structure has no mutual braiding,
   and twice its spin vanishes: bosons and fermions *)

VerificationTest[
  {
    BarDifferential[{4}][BarWord[BarWord[BarWord[{1}]], BarWord[BarWord[{3}]]]],
    BarDifferential[{4}][BarWord[BarWord[BarWord[{1}]], BarWord[BarWord[{1}]]]],
    Values[SpinTable[SuperVec[]]],
    Values[SpinTable[Semion[]]]
  },
  {
    -LBasis[BarWord[BarWord[BarWord[{1}], BarWord[{3}]]]] -
      LBasis[BarWord[BarWord[BarWord[{3}], BarWord[{1}]]]],
    -2 LBasis[BarWord[BarWord[BarWord[{1}], BarWord[{1}]]]],
    {0, 1/2},
    {0, 1/4}
  },
  TestID -> "Bridge-symmetric-means-boson-or-fermion"
]

(* the spin of the generator of Z_N has the denominator N gcd(2, N): the
   class of [1 || 1] generates H_4(K(Z_N, 2)) *)

VerificationTest[
  Table[
    {
      BarCochainValue[
        ZNAnyons[nn, If[EvenQ[nn], 1, 2]],
        BarWord[BarWord[{1}], BarWord[{1}]]
      ],
      EnStructureCount[{nn}, 2]
    },
    {nn, 2, 4}
  ],
  {{1/4, 4}, {1/3, 3}, {1/8, 8}},
  TestID -> "Bridge-spin-generates-H4"
]

(* equivalent categories are cohomologous cocycles: a gauge transformation by
   f changes the cochain by (-1)^(n-1) times the coboundary of the cochain
   psi[a|b] = f(a, b) *)

VerificationTest[
  Table[
    Module[{f, cat, cat2, psi, orders},
      f = Function[{x, y},
        If[x[[1]] y[[1]] === 0, 0, (x[[1]]^2 + 3 y[[1]] + x[[1]] y[[1]]) / 11]
      ];
      cat = ZNAnyons[np[[1]], np[[2]]];
      cat2 = GaugeTransformCategory[cat, f];
      orders = cat["Group"];
      psi = Function[g,
        Replace[g, {
          BarWord[u1_List, u2_List] :> f[u1, u2],
          BarWord[BarWord[u1_List, u2_List]] :> f[u1, u2],
          BarWord[BarWord[BarWord[u1_List, u2_List]]] :> f[u1, u2]
        }]
      ];
      {
        Table[
          AllTrue[
            BarGenerators[orders, n, n + 2],
            Function[g,
              Mod[
                BarCochainValue[cat2, g] - BarCochainValue[cat, g] -
                  (-1)^(n - 1) Total[
                    Map[
                      Function[tm, tm[[1]] psi[tm[[2]]]],
                      LinearTerms[BarDifferential[orders][g]]
                    ]
                  ],
                1
              ] === 0
            ]
          ],
          {n, 1, 3}
        ],
        (* the values change, the class does not *)
        Count[
          BarGenerators[orders, 2, 4],
          _?(Function[g, BarCochainValue[cat2, g] =!= BarCochainValue[cat, g]])
        ],
        {BarCocycleQ[cat2, 1], BarCocycleQ[cat2, 2], BarCocycleQ[cat2, 3]},
        SpinTable[cat2] === SpinTable[cat]
      }
    ],
    {np, {{4, 1}, {3, 2}}}
  ],
  {
    {{True, True, True}, 26, {True, True, False}, True},
    {{True, True, True}, 4, {True, True, False}, True}
  },
  TestID -> "Bridge-gauge-transformations-are-coboundaries"
]

(* ---------------------------------------------------------------------- *)
(* lattice <-> delooping <-> category                                     *)
(*   a lattice action, evaluated on a flat field on a simplex, is a       *)
(*   cocycle on K(Z_N, n)                                                 *)
(* ---------------------------------------------------------------------- *)

(* a flat Z_4 gauge field on a tetrahedron, with the values 3, 2, 3 on the
   edges 01, 12, 23.  Its lift to integers is not closed: dA = 4 on the
   triangle 012, the carry of 3 + 2 *)

VerificationTest[
  With[{x = EMSimplex[3, {{3}, {1}, {0}, {2}, {1}, {3}}]},
    {
      EilenbergMacLaneCocycleQ[{4}, 1][x],
      SimplexValue[FlatFieldCochain[1][x], {1, 2}],
      SimplexValue[Coboundary[FlatFieldCochain[1][x]], {0, 1, 2}],
      SimplexValue[Cup[FlatFieldCochain[1][x], Coboundary[FlatFieldCochain[1][x]]], {0, 1, 2, 3}],
      DijkgraafWittenWeight[4, 1][x],
      Mod[VecZN[4, 1]["Associator"][{3}, {2}, {3}], 1]
    }
  ],
  {True, 2, 4, 12, 3/4, 3/4},
  TestID -> "Bridge-flat-field-cochain"
]

(* the Dijkgraaf-Witten action (k / N^2) A cup dA on a tetrahedron is the
   associator of Vec_(Z_N)^k, for every flat field *)

VerificationTest[
  Table[DijkgraafWittenAssociatorQ[nn, kk], {nn, 2, 4}, {kk, 0, nn - 1}],
  {{True, True}, {True, True, True}, {True, True, True, True}},
  TestID -> "Bridge-Dijkgraaf-Witten-is-associator"
]

(* it is a cocycle on K(Z_N, 1), and for k = 1 its class generates
   H^3(K(Z_N, 1); U(1)) = Z_N *)

VerificationTest[
  {
    Table[
      {
        CharacteristicCocycleQ[{nn}, 1, 3, DijkgraafWittenWeight[nn, kk]],
        CharacteristicClassOrder[{nn}, 1, 3, DijkgraafWittenWeight[nn, kk]]
      },
      {nn, 2, 3}, {kk, 0, nn - 1}
    ],
    Table[EnStructureCount[{nn}, 1], {nn, 2, 3}]
  },
  {
    {{{True, 1}, {True, 2}}, {{True, 1}, {True, 3}, {True, 3}}},
    {2, 3}
  },
  TestID -> "Bridge-Dijkgraaf-Witten-class"
]

(* the Pontryagin square (p / 2N) P(B) on K(Z_2, 2): a cocycle for every p,
   and the order of its class is the denominator of the spin p / 4 of the
   anyons Z_2^(p).  The semion (p = 1) generates H^4(K(Z_2, 2); U(1)) = Z_4 *)

VerificationTest[
  {
    Union[Map[PontryaginWeight[2, 1], EilenbergMacLaneSimplices[{2}, 2, 4]]],
    Table[PontryaginSpinQ[2, p], {p, 0, 3}],
    Table[CharacteristicClassOrder[{2}, 2, 4, PontryaginWeight[2, p]], {p, 0, 3}],
    Table[Denominator[TopologicalSpin[ZNAnyons[2, p], {1}]], {p, 0, 3}],
    EnStructureCount[{2}, 2]
  },
  {
    {0, 1/4, 1/2, 3/4},
    {True, True, True, True},
    {1, 4, 2, 4},
    {1, 4, 2, 4},
    4
  },
  TestID -> "Bridge-Pontryagin-spin"
]

(* on K(Z_3, 2), with 636 nondegenerate 4-simplices: p must be even, and
   p = 2 generates H^4(K(Z_3, 2); U(1)) = Z_3 *)

VerificationTest[
  {
    CharacteristicClassOrder[{3}, 2, 4, PontryaginWeight[3, 2]],
    Denominator[TopologicalSpin[ZNAnyons[3, 2], {1}]],
    EnStructureCount[{3}, 2]
  },
  {3, 3, 3},
  TestID -> "Bridge-Pontryagin-generates-Z3"
]

(* the cup-1 term of the Pontryagin square is needed: B cup B / 4 alone is
   not a cocycle on K(Z_2, 2).  B cup B / 2 is one, of order 2: the fermion *)

VerificationTest[
  {
    CharacteristicCocycleQ[{2}, 2, 4,
      Function[x,
        Mod[SimplexValue[Cup[FlatFieldCochain[2][x], FlatFieldCochain[2][x]], Range[0, 4]] / 4, 1]
      ]
    ],
    CharacteristicCocycleQ[{2}, 2, 4,
      Function[x,
        Mod[SimplexValue[Cup[FlatFieldCochain[2][x], FlatFieldCochain[2][x]], Range[0, 4]] / 2, 1]
      ]
    ],
    CharacteristicClassOrder[{2}, 2, 4,
      Function[x,
        Mod[SimplexValue[Cup[FlatFieldCochain[2][x], FlatFieldCochain[2][x]], Range[0, 4]] / 2, 1]
      ]
    ]
  },
  {False, True, 2},
  TestID -> "Bridge-Pontryagin-needs-cup-1"
]

(* ---------------------------------------------------------------------- *)
(* operad <-> loop spaces: the approximation theorem                      *)
(*   C_n X ~ Omega^n Sigma^n X for connected X.  Rationally: the free     *)
(*   algebra over P_n = H_*(E_n) on the homology of X has the Poincare    *)
(*   series of Omega^n Sigma^n X.  Here by arity, up to arity 4            *)
(* ---------------------------------------------------------------------- *)

(* one sphere: Omega^n S^(n+d) *)

VerificationTest[
  Table[ApproximationTheoremQ[n, {d}, 4], {n, 1, 3}, {d, 1, 4}],
  {{True, True, True, True}, {True, True, True, True}, {True, True, True, True}},
  TestID -> "Bridge-approximation-theorem-spheres"
]

(* wedges of spheres; and the wrong n does not fit: the free Gerstenhaber
   algebra on a class of degree 2 has [x, x], which Omega^3 S^5 has not *)

VerificationTest[
  {
    Table[
      ApproximationTheoremQ[n, degrees, 4],
      {n, 1, 3}, {degrees, {{1, 1}, {1, 2}, {2, 3}, {1, 1, 1}, {1, 2, 3}}}
    ],
    FreeAlgebraDimensions[PoissonOperad[2], {2}, 3] === LoopSuspensionDimensions[3, {2}, 3],
    FreeAlgebraDimensions[PoissonOperad[3], {1, 2}, 4]
  },
  {
    {
      {True, True, True, True, True},
      {True, True, True, True, True},
      {True, True, True, True, True}
    },
    False,
    <|
      1 -> <|1 -> 1, 2 -> 1|>,
      2 -> <|3 -> 1, 4 -> 2, 5 -> 1|>,
      3 -> <|5 -> 2, 6 -> 3, 7 -> 1, 8 -> 1, 9 -> 1|>,
      4 -> <|7 -> 2, 8 -> 4, 9 -> 3, 10 -> 2, 11 -> 2, 12 -> 2, 13 -> 1|>
    |>
  },
  TestID -> "Bridge-approximation-theorem-wedges"
]
