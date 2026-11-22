(* BarrattEccles: the Barratt-Eccles operad, its E_n stages, table reduction,
   and its action on the interval and on cubes.
   The expected values are those of reference/einfinity_reference.py. *)

(* ---------------------------------------------------------------------- *)
(* elements and the differential                                          *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    Table[Length[BarrattEcclesElements[3, d]], {d, 0, 3}],
    Table[Length[BarrattEcclesElements[2, d]], {d, 0, 4}],
    BarrattEcclesElements[2, 1],
    BarrattEcclesElements[1, 0],
    BarrattEcclesElements[1, 1],
    Map[HigherCupElement, {0, 1, 2}],
    HirschElement[]
  },
  {
    {6, 30, 150, 750},
    {2, 2, 2, 2, 2},
    {{{1, 2}, {2, 1}}, {{2, 1}, {1, 2}}},
    {{{1}}},
    {},
    {{{1, 2}}, {{1, 2}, {2, 1}}, {{1, 2}, {2, 1}, {1, 2}}},
    {{1, 2, 3}, {1, 3, 2}, {3, 1, 2}}
  },
  TestID -> "BarrattEccles-elements"
]

VerificationTest[
  {
    BarrattEcclesDifferential[{{1, 2}}],
    BarrattEcclesDifferential[{{1, 2}, {2, 1}}],
    BarrattEcclesDifferential[{{1, 2}, {2, 1}, {1, 2}}],
    BarrattEcclesDifferential[HirschElement[]],
    BarrattEcclesDifferential[2 LBasis[{{1, 2}, {2, 1}}] + LBasis[{{2, 1}, {1, 2}}]]
  },
  {
    0,
    LBasis[{{2, 1}}] - LBasis[{{1, 2}}],
    LBasis[{{2, 1}, {1, 2}}] + LBasis[{{1, 2}, {2, 1}}],
    LBasis[{{1, 3, 2}, {3, 1, 2}}] - LBasis[{{1, 2, 3}, {3, 1, 2}}] + LBasis[{{1, 2, 3}, {1, 3, 2}}],
    LBasis[{{2, 1}}] - LBasis[{{1, 2}}]
  },
  TestID -> "BarrattEccles-differential"
]

VerificationTest[
  {
    AllTrue[
      Join[BarrattEcclesElements[3, 2], BarrattEcclesElements[3, 3], BarrattEcclesElements[2, 4]],
      Function[s, BarrattEcclesDifferential[BarrattEcclesDifferential[s]] === 0]
    ],
    (* E(2) and E(3) have the homology of a point *)
    Most[ChainBetti[Table[BarrattEcclesElements[2, d], {d, 0, 5}], BarrattEcclesDifferential]],
    Most[ChainBetti[Table[BarrattEcclesElements[3, d], {d, 0, 3}], BarrattEcclesDifferential]]
  },
  {True, {1, 0, 0, 0, 0}, {1, 0, 0}},
  TestID -> "BarrattEccles-acyclic"
]

(* ---------------------------------------------------------------------- *)
(* composition and the symmetric groups                                   *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{e0 = HigherCupElement[0], e1 = HigherCupElement[1]},
    {
      BarrattEcclesCompose[e1, 1, e0],
      BarrattEcclesCompose[e0, 2, e1],
      BarrattEcclesCompose[e0, 1, e1],
      BarrattEcclesCompose[e1, 1, e1],
      BarrattEcclesCompose[e1, 2, e1],
      BarrattEcclesCompose[2 LBasis[{{1, 2}}], 1, LBasis[{{2, 1}}]],
      BarrattEcclesCompose[{{1}}, 1, e1],
      BarrattEcclesCompose[e1, 2, {{1}}]
    }
  ],
  {
    LBasis[{{1, 2, 3}, {3, 1, 2}}],
    LBasis[{{1, 2, 3}, {1, 3, 2}}],
    LBasis[{{1, 2, 3}, {2, 1, 3}}],
    LBasis[{{1, 2, 3}, {3, 1, 2}, {3, 2, 1}}] - LBasis[{{1, 2, 3}, {2, 1, 3}, {3, 2, 1}}],
    LBasis[{{1, 2, 3}, {2, 3, 1}, {3, 2, 1}}] - LBasis[{{1, 2, 3}, {1, 3, 2}, {3, 2, 1}}],
    2 LBasis[{{2, 1, 3}}],
    LBasis[{{1, 2}, {2, 1}}],
    LBasis[{{1, 2}, {2, 1}}]
  },
  TestID -> "BarrattEccles-compose"
]

(* in degree 0 the Barratt-Eccles operad is the operad of words *)

VerificationTest[
  With[{wo = WordOperad[]},
    {
      AllTrue[
        Flatten[Table[{w, i, v}, {w, Permutations[Range[3]]}, {v, Permutations[Range[2]]}, {i, 1, 3}], 2],
        Function[x,
          BarrattEcclesCompose[{x[[1]]}, x[[2]], {x[[3]]}] ===
            LBasis[{wo["Compose"][x[[1]], x[[2]], x[[3]]]}]
        ]
      ],
      AllTrue[
        Tuples[Permutations[Range[3]], 2],
        Function[x, BarrattEcclesAct[{x[[1]]}, x[[2]]] === {wo["Action"][x[[1]], x[[2]]]}]
      ]
    }
  ],
  {True, True},
  TestID -> "BarrattEccles-degree-zero-is-words"
]

VerificationTest[
  {
    BarrattEcclesAct[{{1, 2, 3}, {1, 3, 2}}, {2, 3, 1}],
    BarrattEcclesAct[LBasis[{{1, 2}, {2, 1}}] - 3 LBasis[{{2, 1}, {1, 2}}], {2, 1}],
    (* a right action: (u.s).t = u.(s t) with (s t)(j) = s(t(j)) *)
    AllTrue[
      Tuples[Permutations[Range[3]], 2],
      Function[st,
        BarrattEcclesAct[BarrattEcclesAct[HirschElement[], st[[1]]], st[[2]]] ===
          BarrattEcclesAct[HirschElement[], st[[1]][[st[[2]]]]]
      ]
    ]
  },
  {
    {{3, 1, 2}, {3, 2, 1}},
    LBasis[{{2, 1}, {1, 2}}] - 3 LBasis[{{1, 2}, {2, 1}}],
    True
  },
  TestID -> "BarrattEccles-action"
]

(* equivariance: (a.s) o_i (b.t) = (a o_s(i) b).(s o_i t) *)

VerificationTest[
  With[{e2 = Flatten[Table[BarrattEcclesElements[2, d], {d, 0, 2}], 1]},
    AllTrue[
      Join[
        Flatten[
          Table[{a, b, s, t, i},
            {a, e2}, {b, e2}, {s, Permutations[Range[2]]}, {t, Permutations[Range[2]]}, {i, 1, 2}],
          4
        ],
        Flatten[
          Table[{a, b, s, t, i},
            {a, BarrattEcclesElements[3, 1]}, {b, BarrattEcclesElements[2, 1]},
            {s, Permutations[Range[3]]}, {t, Permutations[Range[2]]}, {i, 1, 3}],
          4
        ]
      ],
      Function[x,
        BarrattEcclesCompose[BarrattEcclesAct[x[[1]], x[[3]]], x[[5]], BarrattEcclesAct[x[[2]], x[[4]]]] ===
          BarrattEcclesAct[
            BarrattEcclesCompose[x[[1]], x[[3]][[x[[5]]]], x[[2]]],
            PermutationCompose[x[[3]], x[[5]], x[[4]]]
          ]
      ]
    ]
  ],
  True,
  TestID -> "BarrattEccles-equivariance"
]

(* a differential graded operad: unit, sequential and parallel axioms with
   Koszul signs, d d = 0, Leibniz rule *)

VerificationTest[
  With[{check = DGOperadCheck[BarrattEcclesOperad[1], 3]},
    {check["Passed"], Keys[check["Checked"]], Min[Values[check["Checked"]]] > 0}
  ],
  {True, {"Unit", "Sequential", "Parallel", "Square", "Leibniz"}, True},
  TestID -> "BarrattEccles-dg-operad"
]

(* associativity of three elements of arity 2, in degrees up to 2 *)

VerificationTest[
  With[{e2 = Flatten[Table[BarrattEcclesElements[2, d], {d, 0, 2}], 1]},
    AllTrue[
      Tuples[e2, 3],
      Function[x,
        With[{a = x[[1]], b = x[[2]], c = x[[3]]},
          AllTrue[
            Tuples[{1, 2}, 2],
            Function[ij,
              BarrattEcclesCompose[BarrattEcclesCompose[a, ij[[1]], b], ij[[1]] + ij[[2]] - 1, c] ===
                BarrattEcclesCompose[a, ij[[1]], BarrattEcclesCompose[b, ij[[2]], c]]
            ]
          ] &&
          BarrattEcclesCompose[BarrattEcclesCompose[a, 1, b], 3, c] ===
            LinearCollect[
              (-1)^((Length[b] - 1) (Length[c] - 1)) *
                BarrattEcclesCompose[BarrattEcclesCompose[a, 2, c], 1, b]
            ]
        ]
      ]
    ]
  ],
  True,
  TestID -> "BarrattEccles-associativity"
]

(* control: without the Koszul sign the parallel axiom fails *)

VerificationTest[
  With[{e1 = HigherCupElement[1]},
    {
      BarrattEcclesCompose[BarrattEcclesCompose[e1, 1, e1], 3, e1] ===
        BarrattEcclesCompose[BarrattEcclesCompose[e1, 2, e1], 1, e1],
      LinearZeroQ[
        BarrattEcclesCompose[BarrattEcclesCompose[e1, 1, e1], 3, e1] +
          BarrattEcclesCompose[BarrattEcclesCompose[e1, 2, e1], 1, e1]
      ]
    }
  ],
  {False, True},
  TestID -> "BarrattEccles-parallel-sign"
]

(* ---------------------------------------------------------------------- *)
(* the filtration by E_n operads                                          *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    Table[BarrattEcclesLevel[HigherCupElement[i]], {i, 0, 3}],
    BarrattEcclesLevel[HirschElement[]],
    BarrattEcclesLevel[{{1, 2, 3}, {3, 2, 1}, {1, 2, 3}}],
    Map[Length, BarrattEcclesFiltration[2, 3]],
    Map[Length, BarrattEcclesFiltration[3, 3]],
    BarrattEcclesFiltration[1, 3] === {Map[List, Permutations[Range[3]]]},
    (* a stage is closed under composition, the differential and the symmetric groups *)
    AllTrue[
      Flatten[
        Table[
          LinearTerms[BarrattEcclesCompose[a, i, b]],
          {a, Flatten[BarrattEcclesFiltration[2, 3], 1]}, {b, Flatten[BarrattEcclesFiltration[2, 2], 1]}, {i, 1, 3}
        ],
        3
      ],
      Function[tm, BarrattEcclesLevel[tm[[2]]] <= 2]
    ]
  },
  {{1, 2, 3, 4}, 2, 3, {6, 30, 36, 12}, {6, 30, 150, 360, 420, 228, 48}, True, True},
  TestID -> "BarrattEccles-filtration"
]

(* the homology of the stage F_n in arity k: the configuration space of k
   points in R^n.  F_3 in arity 3 is out of reach of the nerve of the little
   cubes *)

VerificationTest[
  {
    BarrattEcclesBetti[1, 3],
    BarrattEcclesBetti[2, 2],
    BarrattEcclesBetti[3, 2],
    BarrattEcclesBetti[4, 2],
    BarrattEcclesBetti[2, 3],
    BarrattEcclesBetti[3, 3]
  },
  {{6}, {1, 1}, {1, 0, 1}, {1, 0, 0, 1}, {1, 3, 2, 0}, {1, 0, 3, 0, 2, 0, 0}},
  TestID -> "BarrattEccles-Betti"
]

(* ---------------------------------------------------------------------- *)
(* table reduction: the surjection operad                                 *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    Table[TableReduction[HigherCupElement[i]], {i, 0, 3}],
    TableReduction[{{1, 2, 3}, {3, 2, 1}}],
    TableReduction[{{1, 2, 3}, {2, 1, 3}}],
    TableReduction[HirschElement[]],
    Sort[TableReductionTables[{{1, 2}, {2, 1}}]]
  },
  {
    {LBasis[{1, 2}], LBasis[{1, 2, 1}], LBasis[{1, 2, 1, 2}], LBasis[{1, 2, 1, 2, 1}]},
    LBasis[{1, 3, 2, 1}] + LBasis[{1, 2, 3, 2}],
    LBasis[{1, 2, 1, 3}],
    0,
    Sort[{{{1}, {2, 1}}, {{1, 2}, {2}}}]
  },
  TestID -> "BarrattEccles-table-reduction"
]

VerificationTest[
  {
    SurjectionDifferential[{1, 2, 1}],
    SurjectionDifferential[{1, 2}],
    SurjectionDifferential[SurjectionDifferential[{1, 2, 1, 3, 1, 2}]],
    (* the table reduction is a chain map *)
    AllTrue[
      Join[
        Flatten[Table[BarrattEcclesElements[2, d], {d, 0, 3}], 1],
        Flatten[Table[BarrattEcclesElements[3, d], {d, 0, 2}], 1],
        BarrattEcclesElements[4, 1]
      ],
      Function[s,
        SurjectionDifferential[TableReduction[s]] === TableReduction[BarrattEcclesDifferential[s]]
      ]
    ]
  },
  {LBasis[{2, 1}] - LBasis[{1, 2}], 0, 0, True},
  TestID -> "BarrattEccles-surjections"
]

(* ---------------------------------------------------------------------- *)
(* the action on the interval and on cubes                                *)
(* ---------------------------------------------------------------------- *)

(* a term is {coefficient, pattern}; 0, 1, 2 = initial vertex, final vertex, edge *)

VerificationTest[
  {
    Sort[IntervalCoaction[{{1, 2}}]],
    Sort[IntervalCoaction[{{2, 1}}]],
    IntervalCoaction[{{1, 2}, {2, 1}}],
    IntervalCoaction[{{1, 2}, {2, 1}, {1, 2}}],
    Sort[IntervalCoaction[{{1, 2, 3}}]],
    IntervalCoaction[{{1, 2, 3}, {1, 3, 2}}],
    Sort[IntervalCoaction[{{1, 2, 3}, {3, 2, 1}}]],
    IntervalCoaction[HirschElement[]]
  },
  {
    {{1, {0, 2}}, {1, {2, 1}}},
    {{1, {1, 2}}, {1, {2, 0}}},
    {{1, {2, 2}}},
    {},
    {{1, {0, 0, 2}}, {1, {0, 2, 1}}, {1, {2, 1, 1}}},
    {{1, {0, 2, 2}}},
    {{1, {0, 2, 2}}, {1, {2, 1, 2}}, {1, {2, 2, 0}}},
    {}
  },
  TestID -> "BarrattEccles-interval"
]

VerificationTest[
  {
    CubeCoaction[{{1, 2}}, 0],
    CubeCoaction[{{1, 2}, {2, 1}}, 0],
    Sort[CubeCoaction[{{1, 2}}, 2]],
    Sort[CubeCoaction[{{1, 2}, {2, 1}}, 2]],
    CubeCoaction[HirschElement[], 1],
    CubeCoaction[HirschElement[], 2],
    Sort[CubeCoaction[HirschElement[], 3]],
    CubeCoaction[HirschElement[]][2] === CubeCoaction[HirschElement[], 2]
  },
  {
    {{1, {{}, {}}}},
    {},
    {{-1, {{0, 2}, {2, 1}}}, {1, {{0, 0}, {2, 2}}}, {1, {{2, 0}, {1, 2}}}, {1, {{2, 2}, {1, 1}}}},
    {{-1, {{2, 2}, {1, 2}}}, {-1, {{2, 2}, {2, 0}}}, {1, {{0, 2}, {2, 2}}}, {1, {{2, 1}, {2, 2}}}},
    {},
    {{-1, {{0, 2}, {2, 1}, {2, 2}}}},
    {
      {-1, {{0, 0, 2}, {0, 2, 1}, {2, 2, 2}}}, {-1, {{0, 0, 2}, {2, 1, 1}, {2, 2, 2}}},
      {-1, {{0, 2, 0}, {2, 1, 2}, {2, 2, 0}}}, {-1, {{0, 2, 1}, {2, 1, 1}, {2, 2, 2}}},
      {-1, {{2, 0, 2}, {1, 2, 1}, {1, 2, 2}}}, {1, {{0, 0, 2}, {2, 2, 1}, {1, 2, 2}}},
      {1, {{0, 0, 2}, {2, 2, 1}, {2, 0, 2}}}, {1, {{0, 2, 2}, {2, 1, 1}, {2, 1, 2}}},
      {1, {{0, 2, 2}, {2, 1, 1}, {2, 2, 0}}}
    },
    True
  },
  TestID -> "BarrattEccles-cube"
]

VerificationTest[
  Table[
    Length[CubeCoaction[s, n]],
    {s, {HigherCupElement[0], HigherCupElement[1], HigherCupElement[2], {{1, 2, 3}}, HirschElement[]}},
    {n, 1, 4}
  ],
  {{2, 4, 8, 16}, {1, 4, 12, 32}, {0, 1, 6, 24}, {3, 9, 27, 81}, {0, 1, 9, 54}},
  TestID -> "BarrattEccles-cube-term-counts"
]

(* ---------------------------------------------------------------------- *)
(* unordered configurations: orbits of the symmetric group                *)
(*   expected values: reference/braidgroup_reference.py                   *)
(* ---------------------------------------------------------------------- *)

(* two unordered little n-cubes: the real projective space of dimension
   n - 1 *)

VerificationTest[
  {
    BarrattEcclesOrbits[2, 2],
    Map[Length, BarrattEcclesOrbits[2, 3]],
    Map[Length, BarrattEcclesOrbits[3, 3]],
    Table[BarrattEcclesOrbitHomology[n, 2], {n, 2, 5}]
  },
  {
    {{{{1, 2}}}, {{{1, 2}, {2, 1}}}},
    {1, 5, 6, 2},
    {1, 5, 25, 60, 70, 38, 8},
    {
      {{0}, {0}},
      {{0}, {2}, {}},
      {{0}, {2}, {}, {0}},
      {{0}, {2}, {}, {2}, {}}
    }
  },
  TestID -> "BarrattEccles-orbits-projective-spaces"
]

(* the braid groups, from the complex of Fuks and Vainshtein: H_1 = Z, and
   the rest is torsion.  H^i has the torsion of H_(i-1) *)

VerificationTest[
  {
    Table[BraidGroupHomology[k], {k, 1, 6}],
    BraidGroupHomology[8],
    BraidGroupCohomology[4],
    BraidGroupCohomology[6]
  },
  {
    {
      {{0}},
      {{0}, {0}},
      {{0}, {0}, {}},
      {{0}, {0}, {2}, {}},
      {{0}, {0}, {2}, {}, {}},
      {{0}, {0}, {2}, {2}, {3}, {}}
    },
    {{0}, {0}, {2}, {2}, {6}, {3}, {2}, {}},
    {{0}, {0}, {}, {2}},
    {{0}, {0}, {}, {2}, {2}, {3}}
  },
  TestID -> "BarrattEccles-braid-group-homology"
]

(* the stage F_2 gives the braid group again, by an independent computation;
   in three dimensions, and for the whole operad (the symmetric groups),
   H_1 is Z_2 *)

VerificationTest[
  {
    BarrattEcclesOrbitHomology[2, 3] === Join[BraidGroupHomology[3], {{}}],
    BarrattEcclesOrbitHomology[3, 3],
    BarrattEcclesOrbitHomology[Infinity, 2, 3],
    BarrattEcclesOrbitHomology[Infinity, 3, 2],
    BarrattEcclesOrbitHomology[Infinity, 4, 1]
  },
  {
    True,
    {{0}, {2}, {}, {3}, {}, {}, {}},
    {{0}, {2}, {}, {2}},
    {{0}, {2}, {}},
    {{0}, {2}}
  },
  TestID -> "BarrattEccles-orbits-braid-and-symmetric-groups"
]
