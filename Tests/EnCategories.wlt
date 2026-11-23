(* EnCategories: pointed E_n-monoidal categories on a finite abelian group.
   Phases are rational numbers modulo 1.  The expected values are those of
   reference/encategory_reference.py. *)

VerificationTest[
  {CategoryObjects[ZNAnyons[3, 2]], CategoryObjects[ToricCode[]], CategoryTensor[ToricCode[], {1, 0}, {1, 1}]},
  {{{0}, {1}, {2}}, {{0, 0}, {0, 1}, {1, 0}, {1, 1}}, {0, 1}},
  TestID -> "EnCategories-objects"
]

(* E_1: the pentagon equation says that the associator is a 3-cocycle *)

VerificationTest[
  Table[PentagonQ[VecZN[n, k]], {n, 1, 4}, {k, 0, n - 1}],
  {{True}, {True, True}, {True, True, True}, {True, True, True, True}},
  TestID -> "EnCategories-pentagon-VecZN"
]

VerificationTest[
  PentagonQ[PointedCategory[{3}, Function[{a, b, c}, a[[1]]^2 b[[1]] / 3]]],
  False,
  TestID -> "EnCategories-pentagon-fails"
]

(* E_2: the hexagon equations.  Z_n^(p) is braided when n is even or p is even *)

VerificationTest[
  Table[PentagonQ[ZNAnyons[n, p]] && HexagonQ[ZNAnyons[n, p]], {n, 2, 5}, {p, 0, 3}],
  {
    {True, True, True, True},
    {True, False, True, False},
    {True, True, True, True},
    {True, False, True, False}
  },
  TestID -> "EnCategories-hexagon-ZNAnyons"
]

VerificationTest[
  {PentagonQ[DoubleZN[2]], HexagonQ[DoubleZN[2]], PentagonQ[DoubleZN[3]], HexagonQ[DoubleZN[3]]},
  {True, True, True, True},
  TestID -> "EnCategories-hexagon-DoubleZN"
]

(* a 3-cocycle of order 3 admits no braiding of this form *)

VerificationTest[
  With[{cat = PointedCategory[{3}, VecZN[3, 1]["Associator"], Function[{a, b}, a[[1]] b[[1]] / 3]]},
    {PentagonQ[cat], HexagonQ[cat]}
  ],
  {True, False},
  TestID -> "EnCategories-no-braiding-on-order-3"
]

(* E_n levels: 0 not monoidal, 1 monoidal, 2 braided, Infinity symmetric *)

VerificationTest[
  {
    EnLevel[ZNAnyons[4, 1]], EnLevel[ZNAnyons[4, 4]], EnLevel[VecZN[3, 1]], EnLevel[ZNAnyons[3, 1]],
    EnLevel[ToricCode[]], EnLevel[SuperVec[]], EnLevel[ZNAnyons[2, 0]], EnLevel[Semion[]], EnLevel[ZNAnyons[3, 2]]
  },
  {2, Infinity, 1, 0, 2, Infinity, Infinity, 2, 2},
  TestID -> "EnCategories-levels"
]

(* spins and mutual braiding *)

VerificationTest[
  {
    TopologicalSpin[Semion[], {1}],
    TopologicalSpin[SuperVec[], {1}],
    Values[SpinTable[ZNAnyons[4, 1]]],
    Values[SpinTable[ZNAnyons[4, 3]]]
  },
  {1/4, 1/2, {0, 1/8, 1/2, 1/8}, {0, 3/8, 1/2, 3/8}},
  TestID -> "EnCategories-spins"
]

VerificationTest[
  With[{tc = ToricCode[]},
    {
      TopologicalSpin[tc, {1, 0}], TopologicalSpin[tc, {0, 1}], TopologicalSpin[tc, {1, 1}],
      MutualBraiding[tc, {1, 0}, {0, 1}], MutualBraiding[tc, {1, 0}, {1, 0}]
    }
  ],
  {0, 0, 1/2, 1/2, 0},
  TestID -> "EnCategories-toric-code"
]

(* the spin is a quadratic form with the mutual braiding as its bilinear form *)

VerificationTest[
  With[{cat = ZNAnyons[6, 5]},
    AllTrue[
      Tuples[CategoryObjects[cat], 2],
      Function[t,
        Mod[
          TopologicalSpin[cat, CategoryTensor[cat, t[[1]], t[[2]]]] -
            TopologicalSpin[cat, t[[1]]] - TopologicalSpin[cat, t[[2]]] -
            MutualBraiding[cat, t[[1]], t[[2]]],
          1
        ] === 0
      ]
    ]
  ],
  True,
  TestID -> "EnCategories-quadratic-form"
]

(* Mueger center and modularity *)

VerificationTest[
  {
    MugerCenter[ZNAnyons[4, 2]], ModularQ[ZNAnyons[4, 2]],
    MugerCenter[ZNAnyons[4, 1]], ModularQ[ZNAnyons[4, 1]],
    ModularQ[ToricCode[]], ModularQ[DoubleZN[3]], ModularQ[Semion[]], ModularQ[SuperVec[]]
  },
  {{{0}, {2}}, False, {{0}}, True, True, True, True, False},
  TestID -> "EnCategories-Mueger-center"
]

(* gauge transformations change the data, not the category *)

VerificationTest[
  With[{cat = ZNAnyons[4, 1]},
    With[{g = GaugeTransformCategory[cat, Function[{a, b}, (a[[1]]^2 b[[1]] + 3 a[[1]]) / 5]]},
      {
        PentagonQ[g], HexagonQ[g],
        SpinTable[g] === SpinTable[cat],
        AllTrue[Tuples[CategoryObjects[cat], 2], MutualBraiding[g, #[[1]], #[[2]]] === MutualBraiding[cat, #[[1]], #[[2]]] &],
        AllTrue[Tuples[CategoryObjects[cat], 3],
          Mod[g["Associator"] @@ # - cat["Associator"] @@ #, 1] === 0 &]
      }
    ]
  ],
  {True, True, True, True, False},
  TestID -> "EnCategories-gauge-invariance"
]

(* classification on Z_n by the quadratic form:
     braided structures    n gcd(2, n)   = |H^4(K(Z_n, 2), U(1))|
     symmetric structures  gcd(2, n)     = |H^5(K(Z_n, 3), U(1))| *)

VerificationTest[
  Table[
    With[{valid = Select[Range[0, 2 n - 1], Function[p, EvenQ[n] || EvenQ[p]]]},
      {
        Length[Union[Map[Function[p, Values[SpinTable[ZNAnyons[n, p]]]], valid]]],
        Length[Union[Map[Function[p, Values[SpinTable[ZNAnyons[n, p]]]],
          Select[valid, Function[p, SymmetricBraidingQ[ZNAnyons[n, p]]]]]]]
      }
    ],
    {n, 2, 6}
  ],
  {{4, 2}, {3, 1}, {8, 2}, {5, 1}, {12, 2}},
  TestID -> "EnCategories-classification-ZN"
]

(* ---------------------------------------------------------------------- *)
(* the braid groups                                                       *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    BraidPhase[ZNAnyons[4, 1], {{1}, {3}, {2}}, 1],
    BraidPhase[ZNAnyons[4, 1], {{1}, {3}, {2}}, 2],
    BraidPhase[Semion[], {{1}, {1}, {1}}, 1],
    BraidPhase[Semion[], {{1}, {1}, {1}}, 2],
    BraidWord[{{1}, {3}, {2}}, 1]
  },
  {7/8, 3/4, 1/4, 1/4, {{3}, {1}, {2}}},
  TestID -> "EnCategories-braid-phase"
]

(* braiding twice is the mutual braiding; in a symmetric category it is trivial *)

VerificationTest[
  With[{cat = ZNAnyons[4, 1], word = {{1}, {3}, {2}}},
    {
      Mod[BraidPhase[cat, word, 1] + BraidPhase[cat, BraidWord[word, 1], 1], 1],
      MutualBraiding[cat, {1}, {3}],
      Mod[2 BraidPhase[SuperVec[], {{1}, {1}}, 1], 1],
      BraidPhase[SuperVec[], {{1}, {1}}, 1]
    }
  ],
  {3/4, 3/4, 0, 1/2},
  TestID -> "EnCategories-double-braiding"
]

VerificationTest[
  {
    BraidRelationQ[ZNAnyons[4, 1], 3], BraidRelationQ[ZNAnyons[4, 3], 4],
    BraidRelationQ[ToricCode[], 3], BraidRelationQ[Semion[], 5]
  },
  {True, True, True, True},
  TestID -> "EnCategories-braid-relation"
]

(* a braid is a list of generators: i for sigma_i, -i for its inverse.  The
   phase goes from the right-nested product of the word to that of the
   permuted word *)

VerificationTest[
  With[{z4 = ZNAnyons[4, 1], word = {{1}, {3}, {2}}},
    {
      BraidPathPhase[Semion[], {{1}, {1}}, {1}],
      BraidPathPhase[Semion[], {{1}, {1}}, {1, 1}],
      BraidPathPhase[Semion[], {{1}, {1}}, {-1}],
      BraidPathPhase[Semion[], {{1}, {1}}, {}],
      BraidPathPhase[z4, word, {1, 2}],
      BraidPathPhase[z4, word, {-2, 1}],
      BraidPathPhase[z4, word, {2, -1, -1}],
      BraidWord[word, {1, 2}],
      BraidWord[word, {-2, 1}],
      AllTrue[
        Tuples[CategoryObjects[z4], 3],
        Function[w3,
          BraidPathPhase[z4, w3, {1, -1}] === 0 && BraidPathPhase[z4, w3, {-2, 2}] === 0 &&
            BraidPathPhase[z4, w3, {1, 2, 1, -2, -1, -2}] === 0
        ]
      ]
    }
  ],
  {1/4, 1/2, 3/4, 0, 1/8, 0, 1/4, {{3}, {2}, {1}}, {{2}, {1}, {3}}, True},
  TestID -> "EnCategories-braid-path-phase"
]

(* under a gauge transformation the phase of a braid changes by terms at its
   two ends only: pure braids are invariant, and one exchange of a and b
   changes by f(b, a) - f(a, b) *)

VerificationTest[
  With[{cat = ZNAnyons[4, 1], f = Function[{a, b}, (a[[1]]^2 b[[1]] + 3 a[[1]]) / 5]},
    With[{
        g = GaugeTransformCategory[cat, f],
        pure = {{1, 1}, {2, 2}, {1, 2, 2, -1}, {1, 2, 1, 2, 1, 2}, {-2, 1, 1, 2}}
      },
      {
        AllTrue[
          Tuples[CategoryObjects[cat], 3],
          Function[w3,
            AllTrue[
              pure,
              Function[braid,
                BraidWord[w3, braid] === w3 &&
                  BraidPathPhase[g, w3, braid] === BraidPathPhase[cat, w3, braid]
              ]
            ]
          ]
        ],
        AllTrue[
          Tuples[CategoryObjects[cat], 2],
          Function[w2,
            Mod[
              BraidPathPhase[g, w2, {1}] - BraidPathPhase[cat, w2, {1}] -
                (f[w2[[2]], w2[[1]]] - f[w2[[1]], w2[[2]]]),
              1
            ] === 0
          ]
        ],
        BraidPathPhase[cat, {{1}, {3}}, {1}],
        BraidPathPhase[g, {{1}, {3}}, {1}]
      }
    ]
  ],
  {True, True, 3/8, 31/40},
  TestID -> "EnCategories-braid-path-gauge"
]

(* modular means: a braided category with a non-degenerate double braiding.
   For n odd and p odd the data of ZNAnyons[n, p] fail the pentagon equation;
   their double braiding is non-degenerate all the same, but there is no
   category to call modular.  The same for data that fail the hexagons *)

VerificationTest[
  {
    EnLevel[ZNAnyons[5, 3]],
    MugerCenter[ZNAnyons[5, 3]],
    ModularQ[ZNAnyons[5, 3]],
    ModularQ[ZNAnyons[5, 2]],
    ModularQ[ZNAnyons[3, 1]],
    ModularQ[VecZN[3, 1]],
    ModularQ[PointedCategory[{3}, VecZN[3, 1]["Associator"], Function[{x, y}, x[[1]] y[[1]] / 3]]]
  },
  {0, {{0}}, False, True, False, False, False},
  TestID -> "EnCategories-modular-requires-braided"
]

(* the lines of U(1) Chern-Simons theory at level k, with spin j^2 / (2 k).
   Even k: modular, on Z_k.  Odd k: on Z_(2 k), with the transparent fermion
   j = k; the category is ZNAnyons[k, 4] times SuperVec[], and it is the
   centralizer of the fermion in the level 4 k theory *)

VerificationTest[
  {
    Map[Function[k, ModularQ[ChernSimonsAnyons[k]]], {2, 4, 6}],
    Map[Function[k, Length[CategoryObjects[ChernSimonsAnyons[k]]]], {2, 4, 1, 3, 5}],
    Map[Function[k, Sort[MugerCenter[ChernSimonsAnyons[k]]]], {1, 3, 5}],
    Map[Function[k, TopologicalSpin[ChernSimonsAnyons[k], {k}]], {1, 3, 5}],
    Map[Function[k, EnLevel[ChernSimonsAnyons[k]]], {2, 3}],
    Map[Function[j, TopologicalSpin[ChernSimonsAnyons[3], {j}]], Range[0, 5]],
    Map[ChernSimonsSpinSplitQ, {1, 3, 5, 7, 2}],
    Map[ChernSimonsFermionCondensationQ, {1, 3, 5, 2}],
    ModularQ[ChernSimonsAnyons[3]]
  },
  {
    {True, True, True},
    {2, 4, 2, 6, 10},
    {{{0}, {1}}, {{0}, {3}}, {{0}, {5}}},
    {1/2, 1/2, 1/2},
    {2, 2},
    {0, 1/6, 2/3, 1/2, 2/3, 1/6},
    {True, True, True, True, False},
    {True, True, True, False},
    False
  },
  TestID -> "EnCategories-Chern-Simons-odd-level"
]
