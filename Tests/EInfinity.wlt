(* EInfinity: the Barratt-Eccles operad acts on the cochains of the hypercubic
   lattice.  Every identity is checked with generic cochains at a symbolic
   base point, so it holds on every lattice of the given dimension.
   The laws and signs are those of reference/einfinity_reference.py. *)

(* ---------------------------------------------------------------------- *)
(* the operations                                                         *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{a = Cochain[1, al], b = Cochain[2, be], c = Cochain[1, ga]},
    {
      EInfinityOperation[{{1, 2}, {2, 1}}][a, b],
      EInfinityOperation[0][a, b],
      EInfinityOperation[2 LBasis[{{1, 2}}] - LBasis[{{2, 1}}]][a, b] ===
        2 LocalOperation[CubeCoaction[{{1, 2}}], 0][a, b] - LocalOperation[CubeCoaction[{{2, 1}}], 0][a, b],
      CochainQ[HirschHomotopy[a, b, c]],
      CochainDegree[HirschHomotopy[a, b, c]],
      CochainDegree[EInfinityOperation[HigherCupElement[2]][b, b]],
      HirschHomotopy[a, b, c] === EInfinityOperation[HirschElement[]][a, b, c]
    }
  ],
  {
    LocalOperation[CubeCoaction[{{1, 2}, {2, 1}}], 1][Cochain[1, al], Cochain[2, be]],
    0,
    True,
    True,
    2,
    2,
    True
  },
  TestID -> "EInfinity-operation"
]

(* the word {1, 2} is the cup product, {1, 2, 3} the triple cup product, and
   a permuted word permutes the factors with the Koszul sign *)

VerificationTest[
  With[{a = Cochain[1, al], b = Cochain[1, be], c = Cochain[1, ga], x = {x1, x2}},
    {
      Expand[
        CochainValue[EInfinityOperation[{{1, 2}}][a, b], x, {1, 2}] -
          (al[x, {1}] be[x + {1, 0}, {2}] - al[x, {2}] be[x + {0, 1}, {1}])
      ],
      CochainEqualQ[EInfinityOperation[{{1, 2, 3}}][a, b, c], Cup[Cup[a, b], c], 3],
      CochainEqualQ[EInfinityOperation[{{1, 2, 3}}][a, b, c], Cup[a, Cup[b, c]], 3],
      CochainEqualQ[EInfinityOperation[{{2, 1, 3}}][a, b, c], -Cup[b, a, c], 3],
      CochainEqualQ[EInfinityOperation[{{2, 1, 3}}][a, b, c], Cup[b, a, c], 3]
    }
  ],
  {0, True, True, True, False},
  TestID -> "EInfinity-words-are-cup-products"
]

(* arity 2: the elements e_i = {{1,2},{2,1},{1,2},...} are the higher cup
   products, theta(e_i)(a, b) = (-1)^(i(p+q) + i(i-1)/2) a u_i b *)

VerificationTest[
  {
    AllTrue[
      Select[
        Flatten[Table[{i, p, q}, {i, 0, 3}, {p, i, 3}, {q, i, 3}], 2],
        Function[t, t[[2]] + t[[3]] - t[[1]] <= 3]
      ],
      Function[t, EInfinityHigherCupQ[t[[1]], {t[[2]], t[[3]]}, 3]]
    ],
    EInfinityHigherCupQ[1, {2, 2}, 4],
    EInfinityHigherCupQ[2, {2, 3}, 4],
    EInfinityHigherCupQ[3, {3, 3}, 4]
  },
  {True, True, True, True},
  TestID -> "EInfinity-higher-cup"
]

(* control: the sign matters *)

VerificationTest[
  With[{a = Cochain[1, al], b = Cochain[2, be]},
    {
      CochainEqualQ[EInfinityOperation[HigherCupElement[1]][a, b], -HigherCup[1][a, b], 3],
      CochainEqualQ[EInfinityOperation[HigherCupElement[1]][a, b], HigherCup[1][a, b], 3]
    }
  ],
  {True, False},
  TestID -> "EInfinity-higher-cup-control"
]

(* ---------------------------------------------------------------------- *)
(* the three laws                                                         *)
(* ---------------------------------------------------------------------- *)

(* (L) the coboundary of an operation: arity 2, degrees 0, 1, 2 of the operad *)

VerificationTest[
  AllTrue[
    Flatten[
      Table[
        {s, {p, q}},
        {s, Flatten[Table[BarrattEcclesElements[2, m], {m, 0, 2}], 1]}, {p, 0, 3}, {q, 0, 3}
      ],
      2
    ],
    Function[x,
      With[{m = Length[x[[1]]] - 1, total = Total[x[[2]]]},
        total < m || total - m + 1 > 3 || EInfinityLeibnizQ[x[[1]], x[[2]], 3]
      ]
    ]
  ],
  True,
  TestID -> "EInfinity-Leibniz-arity-two"
]

(* (L) arity 3 *)

VerificationTest[
  AllTrue[
    Flatten[
      Table[
        {s, degs},
        {s, {
          {{1, 2, 3}},
          {{1, 2, 3}, {2, 1, 3}},
          {{1, 2, 3}, {3, 2, 1}},
          {{2, 3, 1}, {1, 3, 2}},
          HirschElement[],
          {{1, 2, 3}, {3, 2, 1}, {2, 1, 3}}
        }},
        {degs, Tuples[{0, 1, 2}, 3]}
      ],
      1
    ],
    Function[x,
      With[{m = Length[x[[1]]] - 1, total = Total[x[[2]]]},
        total < m || total - m + 1 > 3 || EInfinityLeibnizQ[x[[1]], x[[2]], 3]
      ]
    ]
  ],
  True,
  TestID -> "EInfinity-Leibniz-arity-three"
]

(* control: without the term of the differential of the element the law fails *)

VerificationTest[
  With[{a = Cochain[1, al], b = Cochain[1, be], th = EInfinityOperation[HigherCupElement[1]]},
    {
      CochainEqualQ[
        Coboundary[th[a, b]],
        -(th[Coboundary[a], b] - th[a, Coboundary[b]]) +
          EInfinityOperation[BarrattEcclesDifferential[HigherCupElement[1]]][a, b],
        2
      ],
      CochainEqualQ[
        Coboundary[th[a, b]],
        -(th[Coboundary[a], b] - th[a, Coboundary[b]]),
        2
      ]
    }
  ],
  {True, False},
  TestID -> "EInfinity-Leibniz-control"
]

(* (C) composition in the operad is composition of the operations *)

VerificationTest[
  With[{e0 = HigherCupElement[0], e1 = HigherCupElement[1], e2 = HigherCupElement[2], e1t = {{2, 1}, {1, 2}}},
    AllTrue[
      Flatten[
        Table[
          {st, j, degs},
          {st, {{e1, e0}, {e0, e1}, {e1, e1}, {e2, e1}, {e1, e2}, {e1t, e1}, {e1, e1t}, {e2, e2}}},
          {j, 1, 2},
          {degs, {{1, 1, 1}, {1, 2, 1}, {2, 1, 1}, {1, 1, 2}, {2, 2, 1}, {1, 2, 2}, {2, 2, 2}}}
        ],
        2
      ],
      Function[x,
        With[{s = x[[1, 1]], t = x[[1, 2]], j = x[[2]], degs = x[[3]]},
          With[{ds = Length[s] - 1, dt = Length[t] - 1},
            Total[degs] - ds - dt < 0 || Total[degs] - ds - dt > 3 ||
              Total[Take[degs, {j, j + 1}]] < dt ||
              EInfinityCompositionQ[s, j, t, degs, 3]
          ]
        ]
      ]
    ]
  ],
  True,
  TestID -> "EInfinity-composition"
]

VerificationTest[
  {
    EInfinityCompositionQ[HirschElement[], 1, HigherCupElement[1], {1, 1, 1, 1}, 3],
    EInfinityCompositionQ[HirschElement[], 3, HigherCupElement[0], {1, 1, 1, 1}, 3],
    EInfinityCompositionQ[HigherCupElement[1], 2, HirschElement[], {1, 1, 1, 2}, 3],
    EInfinityCompositionQ[HigherCupElement[0], 1, {{1, 2, 3}, {3, 2, 1}}, {1, 1, 1, 1}, 3]
  },
  {True, True, True, True},
  TestID -> "EInfinity-composition-arity-three"
]

(* control: the sign (-1)^(|s||t|) for two operations of degree 1 *)

VerificationTest[
  With[{a = Cochain[1, al], b = Cochain[1, be], c = Cochain[2, ga], e1 = HigherCupElement[1]},
    {
      CochainEqualQ[
        EInfinityOperation[BarrattEcclesCompose[e1, 1, e1]][a, b, c],
        -EInfinityOperation[e1][EInfinityOperation[e1][a, b], c],
        3
      ],
      CochainEqualQ[
        EInfinityOperation[BarrattEcclesCompose[e1, 1, e1]][a, b, c],
        EInfinityOperation[e1][EInfinityOperation[e1][a, b], c],
        3
      ]
    }
  ],
  {True, False},
  TestID -> "EInfinity-composition-control"
]

(* (E) the symmetric groups *)

VerificationTest[
  {
    AllTrue[
      Flatten[
        Table[
          {s, perm, degs},
          {s, {HigherCupElement[1], HigherCupElement[2], {{2, 1}, {1, 2}}}},
          {perm, Permutations[Range[2]]},
          {degs, {{1, 1}, {1, 2}, {2, 1}, {2, 2}, {3, 2}}}
        ],
        2
      ],
      Function[x,
        Total[x[[3]]] - Length[x[[1]]] + 1 > 3 || EInfinityEquivarianceQ[x[[1]], x[[2]], x[[3]], 3]
      ]
    ],
    AllTrue[
      Flatten[
        Table[
          {s, perm, degs},
          {s, {{{1, 2, 3}}, {{1, 2, 3}, {3, 2, 1}}, HirschElement[]}},
          {perm, Permutations[Range[3]]},
          {degs, {{1, 1, 1}, {1, 1, 2}, {1, 2, 1}, {2, 1, 2}}}
        ],
        2
      ],
      Function[x,
        Total[x[[3]]] - Length[x[[1]]] + 1 > 3 || EInfinityEquivarianceQ[x[[1]], x[[2]], x[[3]], 3]
      ]
    ]
  },
  {True, True},
  TestID -> "EInfinity-equivariance"
]

(* ---------------------------------------------------------------------- *)
(* the Hirsch formula up to homotopy                                      *)
(* ---------------------------------------------------------------------- *)

(* (a u b) u_1 c - a u (b u_1 c) - (-1)^(q(r-1)) (a u_1 c) u b
     = (-1)^(p+q+r) [ dH(a,b,c) - H(da,b,c) - (-1)^p H(a,db,c) - (-1)^(p+q) H(a,b,dc) ] *)

VerificationTest[
  {
    HirschFormulaQ[{1, 1, 1}, 2],
    HirschFormulaQ[{1, 1, 1}, 3],
    HirschFormulaQ[{1, 1, 2}, 3],
    HirschFormulaQ[{1, 2, 1}, 3],
    HirschFormulaQ[{2, 1, 1}, 3]
  },
  {True, True, True, True, True},
  TestID -> "EInfinity-Hirsch"
]

VerificationTest[
  {
    HirschFormulaQ[{1, 1, 1}, 4],
    HirschFormulaQ[{2, 2, 1}, 4],
    HirschFormulaQ[{1, 2, 2}, 4],
    HirschFormulaQ[{2, 1, 2}, 4],
    HirschFormulaQ[{1, 1, 3}, 4]
  },
  {True, True, True, True, True},
  TestID -> "EInfinity-Hirsch-four-dimensions"
]

(* the homotopy in components: on a plaquette it has one term, for the degrees
   (1, 1, 2); on a 3-cell three terms for each of the degrees (1, 1, 3),
   (1, 2, 2), (2, 1, 2).  It vanishes when c is a 1-cochain.  It is an
   operation of the E_2 stage *)

VerificationTest[
  With[{a = Cochain[1, al], b = Cochain[1, be], c = Cochain[2, ga], x = {x1, x2}},
    {
      Expand[
        CochainValue[HirschHomotopy[a, b, c], x, {1, 2}] +
          al[x, {2}] be[x + {0, 1}, {1}] ga[x, {1, 2}]
      ],
      CochainValue[HirschHomotopy[a, b, Cochain[1, ga]], x, {1}],
      CochainValue[HirschHomotopy[Cochain[2, al], b, Cochain[1, ga]], x, {1, 2}],
      BarrattEcclesLevel[HirschElement[]],
      TableReduction[HirschElement[]]
    }
  ],
  {0, 0, 0, 2, 0},
  TestID -> "EInfinity-Hirsch-homotopy-components"
]
