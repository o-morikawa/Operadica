(* Loops: the little n-cubes act on n-fold loop spaces.
   The expected values are those of reference/loops_reference.py. *)

(* ---------------------------------------------------------------------- *)
(* loops and their composition                                            *)
(* ---------------------------------------------------------------------- *)

(* the composition of two loops is the action of the two half intervals *)

VerificationTest[
  With[{half = {{{0, 1/2}}, {{1/2, 1}}}},
    With[{prod = LoopAction[half][GenericLoop[g1], GenericLoop[g2]]},
      {
        GenericLoop[g1][{1/3}],
        GenericLoop[g1][{0}],
        GenericLoop[g1][{1/3, 1}],
        prod[{1/4}],
        prod[{7/8}],
        prod[{1/2}],
        prod[{0}]
      }
    ]
  ],
  {g1[{1/3}], LoopBase, LoopBase, g1[{1/2}], g2[{3/4}], LoopBase, LoopBase},
  TestID -> "Loops-composition"
]

(* the two ways to compose three loops are two different configurations of
   three intervals, and two different maps; the straight path between the
   configurations stays inside the operad: associativity up to homotopy *)

VerificationTest[
  With[{half = {{{0, 1/2}}, {{1/2, 1}}}, gs = {GenericLoop[g1], GenericLoop[g2], GenericLoop[g3]}},
    With[{left = LittleCubesCompose[half, 1, half], right = LittleCubesCompose[half, 2, half]},
      {
        left,
        right,
        (LoopAction[left] @@ gs)[{3/8}],
        (LoopAction[right] @@ gs)[{3/8}],
        LoopEqualQ[LoopAction[left] @@ gs, LoopAction[right] @@ gs, Join[left, right]],
        AllTrue[Range[0, 1, 1/8], Function[s, LittleCubesQ[(1 - s) left + s right, 1]]]
      }
    ]
  ],
  {
    {{{0, 1/4}}, {{1/4, 1/2}}, {{1/2, 1}}},
    {{{0, 1/2}}, {{1/2, 3/4}}, {{3/4, 1}}},
    g2[{1/2}],
    g1[{3/4}],
    False,
    True
  },
  TestID -> "Loops-associativity-up-to-homotopy"
]

VerificationTest[
  With[{half = {{{0, 1/2}}, {{1/2, 1}}}},
    {
      LoopSamplePoints[half],
      Length[LoopSamplePoints[{{{0, 1/3}, {0, 1/2}}, {{1/2, 1}, {1/4, 3/4}}, {{0, 1/3}, {1/2, 1}}}]],
      LittleCubesComposeAll[half, {half, half}],
      LittleCubesComposeAll[half, {half, {{{0, 1}}}}]
    }
  ],
  {
    {{1/4}, {3/8}, {3/4}, {7/8}},
    36,
    {{{0, 1/4}}, {{1/4, 1/2}}, {{1/2, 3/4}}, {{3/4, 1}}},
    {{{0, 1/4}}, {{1/4, 1/2}}, {{1/2, 1}}}
  },
  TestID -> "Loops-sample-points"
]

(* ---------------------------------------------------------------------- *)
(* the axioms of an algebra over the little cubes                         *)
(* ---------------------------------------------------------------------- *)

(* unit, and composition: theta(c o_i d; .., h1, h2, ..) =
   theta(c; .., theta(d; h1, h2), ..), for three little squares c and two d *)

VerificationTest[
  With[{
      c = {{{0, 1/3}, {0, 1/2}}, {{1/2, 1}, {1/4, 3/4}}, {{0, 1/3}, {1/2, 1}}},
      d = {{{1/10, 1/2}, {0, 1}}, {{1/2, 9/10}, {1/5, 4/5}}},
      g = {GenericLoop[g1], GenericLoop[g2], GenericLoop[g3]},
      h = {GenericLoop[h1], GenericLoop[h2]}
    },
    {
      LittleCubesQ[c, 2] && LittleCubesQ[d, 2],
      (LoopAction[c] @@ g)[{3/4, 1/2}],
      (LoopAction[c] @@ g)[{1/6, 3/4}],
      LoopEqualQ[LoopAction[{{{0, 1}, {0, 1}}}][g[[1]]], g[[1]], c],
      LittleCubesCompose[c, 2, d],
      Table[
        With[{cd = LittleCubesCompose[c, i, d]},
          LoopEqualQ[
            LoopAction[cd] @@ Join[Take[g, i - 1], h, Drop[g, i]],
            LoopAction[c] @@ Join[Take[g, i - 1], {LoopAction[d] @@ h}, Drop[g, i]],
            Join[cd, c]
          ]
        ],
        {i, 1, 3}
      ]
    }
  ],
  {
    True,
    g2[{1/2, 1/2}],
    g3[{1/2, 1/2}],
    True,
    {
      {{0, 1/3}, {0, 1/2}}, {{11/20, 3/4}, {1/4, 3/4}}, {{3/4, 19/20}, {7/20, 13/20}},
      {{0, 1/3}, {1/2, 1}}
    },
    {True, True, True}
  },
  TestID -> "Loops-algebra-composition"
]

(* equivariance: theta(c . s; g1, g2, g3) = theta(c; g_(s^-1(1)), ..) *)

VerificationTest[
  With[{
      c = {{{0, 1/3}, {0, 1/2}}, {{1/2, 1}, {1/4, 3/4}}, {{0, 1/3}, {1/2, 1}}},
      g = {GenericLoop[g1], GenericLoop[g2], GenericLoop[g3]}
    },
    {
      LoopEqualQ[LoopAction[LittleCubesAct[c, {2, 3, 1}]] @@ g, LoopAction[c][g[[3]], g[[1]], g[[2]]], c],
      LoopEqualQ[LoopAction[LittleCubesAct[c, {2, 3, 1}]] @@ g, LoopAction[c] @@ g, c]
    }
  ],
  {True, False},
  TestID -> "Loops-algebra-equivariance"
]

(* the same in one and in three dimensions *)

VerificationTest[
  {
    With[{
        c = {{{1/10, 2/5}}, {{1/2, 9/10}}},
        d = {{{0, 1/3}}, {{1/3, 1/2}}, {{3/5, 1}}},
        g = {GenericLoop[g1], GenericLoop[g2]},
        h = {GenericLoop[h1], GenericLoop[h2], GenericLoop[h3]}
      },
      Table[
        With[{cd = LittleCubesCompose[c, i, d]},
          LoopEqualQ[
            LoopAction[cd] @@ Join[Take[g, i - 1], h, Drop[g, i]],
            LoopAction[c] @@ Join[Take[g, i - 1], {LoopAction[d] @@ h}, Drop[g, i]],
            Join[cd, c]
          ]
        ],
        {i, 1, 2}
      ]
    ],
    With[{
        c = {{{0, 1/2}, {0, 1}, {1/4, 3/4}}, {{1/2, 1}, {0, 1/2}, {0, 1}}},
        d = {{{0, 1}, {0, 1/2}, {0, 1/2}}, {{1/5, 4/5}, {1/2, 1}, {1/2, 1}}},
        g = {GenericLoop[g1], GenericLoop[g2]},
        h = {GenericLoop[h1], GenericLoop[h2]}
      },
      Table[
        With[{cd = LittleCubesCompose[c, i, d]},
          LittleCubesQ[cd, 3] &&
            LoopEqualQ[
              LoopAction[cd] @@ Join[Take[g, i - 1], h, Drop[g, i]],
              LoopAction[c] @@ Join[Take[g, i - 1], {LoopAction[d] @@ h}, Drop[g, i]],
              Join[cd, c]
            ]
        ],
        {i, 1, 2}
      ]
    ]
  },
  {{True, True}, {True, True}},
  TestID -> "Loops-algebra-composition-dimensions-1-and-3"
]

(* ---------------------------------------------------------------------- *)
(* the approximation map C_n X -> Omega^n Sigma^n X                       *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{half = {{{0, 1/2}}, {{1/2, 1}}}},
    {
      SuspensionUnit[x][{1/3}],
      SuspensionUnit[x][{1}],
      ApproximationMap[half, {x, y}][{1/4}],
      ApproximationMap[half, {x, y}][{7/8}],
      ApproximationMap[half, {x, y}][{1/2}]
    }
  ],
  {
    SuspensionPoint[{1/3}, x],
    LoopBase,
    SuspensionPoint[{1/2}, x],
    SuspensionPoint[{3/4}, y],
    LoopBase
  },
  TestID -> "Loops-approximation-map"
]

(* it is a map of algebras: the image of the composed configuration is the
   action of c on the images of the configurations d1, d2, d3 *)

VerificationTest[
  With[{
      c = {{{0, 1/3}, {0, 1/2}}, {{1/2, 1}, {1/4, 3/4}}, {{0, 1/3}, {1/2, 1}}},
      ds = {
        {{{1/10, 1/2}, {0, 1}}, {{1/2, 9/10}, {1/5, 4/5}}},
        {{{0, 1}, {0, 1}}},
        {{{0, 1/2}, {0, 1}}, {{1/2, 1}, {0, 1}}}
      },
      labels = {{x1, x2}, {y1}, {z1, z2}}
    },
    With[{big = LittleCubesComposeAll[c, ds]},
      {
        LittleCubesQ[big, 2],
        Length[big],
        ApproximationMap[big, Flatten[labels]][{3/4, 1/2}],
        ApproximationMap[big, Flatten[labels]][{1/9, 1/4}],
        LoopEqualQ[
          ApproximationMap[big, Flatten[labels]],
          LoopAction[c] @@ MapThread[ApproximationMap, {ds, labels}],
          Join[big, c]
        ]
      }
    ]
  ],
  {
    True,
    5,
    SuspensionPoint[{1/2, 1/2}, y1],
    SuspensionPoint[{7/12, 1/2}, x1],
    True
  },
  TestID -> "Loops-approximation-map-of-algebras"
]

(* ---------------------------------------------------------------------- *)
(* commutativity up to homotopy for n >= 2                                *)
(* ---------------------------------------------------------------------- *)

(* two little squares move around each other: a path in the operad from a
   configuration to the same configuration with the cubes exchanged.  In one
   dimension there is no such path *)

VerificationTest[
  {
    SwapPath[2][0],
    SwapPath[2][1/2],
    SwapPath[3][1/4],
    Table[
      AllTrue[Range[0, 2, 1/16], Function[s, LittleCubesQ[SwapPath[n][s], n]]] &&
        SwapPath[n][1] === LittleCubesAct[SwapPath[n][0], {2, 1}] &&
        SwapPath[n][2] === SwapPath[n][0],
      {n, 2, 3}
    ],
    LoopEqualQ[
      LoopAction[SwapPath[2][1]][GenericLoop[g1], GenericLoop[g2]],
      LoopAction[SwapPath[2][0]][GenericLoop[g2], GenericLoop[g1]],
      SwapPath[2][0]
    ],
    LoopEqualQ[
      LoopAction[SwapPath[2][0]][GenericLoop[g1], GenericLoop[g2]],
      LoopAction[SwapPath[2][0]][GenericLoop[g2], GenericLoop[g1]],
      SwapPath[2][0]
    ]
  },
  {
    {{{1/8, 3/8}, {3/8, 5/8}}, {{5/8, 7/8}, {3/8, 5/8}}},
    {{{3/8, 5/8}, {1/8, 3/8}}, {{3/8, 5/8}, {5/8, 7/8}}},
    {{{1/8, 3/8}, {1/8, 3/8}, {0, 1}}, {{5/8, 7/8}, {5/8, 7/8}, {0, 1}}},
    {True, True},
    True,
    False
  },
  TestID -> "Loops-commutativity-up-to-homotopy"
]
