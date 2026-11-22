(* LittleCubes: the little n-cubes operads, the geometric E_n operads *)

(* composition in one dimension: little intervals *)

VerificationTest[
  With[{c = {{{0, 1/2}}, {{1/2, 1}}}, d = {{{0, 1/3}}, {{2/3, 1}}}},
    {LittleCubesCompose[c, 1, d], LittleCubesCompose[c, 2, d]}
  ],
  {
    {{{0, 1/6}}, {{1/3, 1/2}}, {{1/2, 1}}},
    {{{0, 1/2}}, {{1/2, 2/3}}, {{5/6, 1}}}
  },
  TestID -> "LittleCubes-compose-intervals"
]

VerificationTest[
  {
    LittleCubesQ[{{{0, 1/2}}, {{1/2, 1}}}, 1],
    LittleCubesQ[{{{0, 2/3}}, {{1/2, 1}}}, 1],
    LittleCubesQ[{{{0, 1/2}, {0, 1}}, {{1/4, 1}, {0, 1/2}}}, 2],
    LittleCubesQ[{{{0, 1/2}, {0, 1}}, {{1/2, 1}, {0, 1/2}}}, 2],
    LittleCubesQ[{{{0, 1/2}, {0, 1}}, {{1/4, 1}, {0, 1/2}}}, 1]
  },
  {True, False, False, True, False},
  TestID -> "LittleCubes-validity"
]

VerificationTest[
  LittleCubesAct[{{{0, 1/3}}, {{1/3, 2/3}}, {{2/3, 1}}}, {2, 3, 1}],
  {{{1/3, 2/3}}, {{2/3, 1}}, {{0, 1/3}}},
  TestID -> "LittleCubes-action"
]

(* the operad axioms as identities in the endpoints *)

VerificationTest[
  Table[OperadAxiomsQ[LittleCubesOperad[n], 3], {n, 1, 3}],
  {True, True, True},
  TestID -> "LittleCubes-axioms-symbolic"
]

VerificationTest[
  Table[OperadEquivariantQ[LittleCubesOperad[n], 3], {n, 1, 2}],
  {True, True},
  TestID -> "LittleCubes-equivariance-symbolic"
]

VerificationTest[
  StringContainsQ[OperadAxiomCheck[LittleCubesOperad[2], 2]["Strength"], "symbolic"],
  True,
  TestID -> "LittleCubes-strength-note"
]

(* a wrong insertion rule is caught *)

VerificationTest[
  OperadAxiomsQ[
    Join[LittleCubesOperad[1],
      <|"Compose" -> Function[{c, i, d}, Join[Take[c, i - 1], d, Drop[c, i]]]|>],
    3
  ],
  False,
  TestID -> "LittleCubes-wrong-composition-detected"
]

(* random rational configurations are valid and compose to valid ones *)

VerificationTest[
  (
    SeedRandom[42];
    With[{c = RandomLittleCubes[2, 3], d = RandomLittleCubes[2, 4]},
      {
        LittleCubesQ[c, 2], LittleCubesQ[d, 2], Length[c], Length[d],
        AllTrue[Range[3], LittleCubesQ[LittleCubesCompose[c, #, d], 2] &],
        Length[LittleCubesCompose[c, 2, d]]
      }
    ]
  ),
  {True, True, 3, 4, True, 6},
  TestID -> "LittleCubes-random"
]

VerificationTest[
  (
    SeedRandom[43];
    With[{samples = Association[Table[k -> Table[RandomLittleCubes[3, k], {2}], {k, 1, 3}]]},
      {
        OperadAxiomsQ[LittleCubesOperad[3], 4, "Elements" -> samples],
        OperadEquivariantQ[LittleCubesOperad[3], 3, "Elements" -> samples]
      }
    ]
  ),
  {True, True},
  TestID -> "LittleCubes-axioms-sampled"
]

(* C_n -> C_(n+1) is a map of operads *)

VerificationTest[
  (
    SeedRandom[44];
    With[{c = RandomLittleCubes[2, 3], d = RandomLittleCubes[2, 2]},
      {
        LittleCubesQ[LittleCubesStabilize[c], 3],
        AllTrue[Range[3],
          LittleCubesStabilize[LittleCubesCompose[c, #, d]] ===
            LittleCubesCompose[LittleCubesStabilize[c], #, LittleCubesStabilize[d]] &]
      }
    ]
  ),
  {True, True},
  TestID -> "LittleCubes-stabilization"
]

(* simplicial homology *)

VerificationTest[
  {
    SimplicialBetti[{{1, 2}, {2, 3}, {1, 3}}],
    SimplicialBetti[{{1, 2, 3}}],
    SimplicialBetti[{{1}, {2}, {3}}],
    SimplicialBetti[{{1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}}]
  },
  {{1, 1}, {1, 0, 0}, {3}, {1, 0, 1}},
  TestID -> "LittleCubes-Betti-basic"
]

(* C_n(2) has the homotopy type of the sphere S^(n-1):
     n = 1  two components         the product is not commutative
     n = 2  a circle               a braiding, whose square is not trivial
     n = 3  a 2-sphere             the braiding is symmetric *)

VerificationTest[
  Table[SimplicialBetti[SeparationNerve[n]], {n, 1, 4}],
  {{2}, {1, 1}, {1, 0, 1}, {1, 0, 0, 1}},
  TestID -> "LittleCubes-arity-two-spheres"
]

(* ---------------------------------------------------------------------- *)
(* arity k: the nerve of the cover of C_n(k) by convex sets               *)
(* ---------------------------------------------------------------------- *)

(* for two cubes it is the cross-polytope again, each vertex wrapped in a list *)

VerificationTest[
  {
    Sort[SeparationNerve[3, 2]] === Sort[Map[Function[f, Sort[Map[List, f]]], SeparationNerve[3]]],
    Length[SeparationNerve[2, 3]],
    Length[Union[Flatten[SeparationNerve[2, 3], 1]]],
    Union[Map[Length, SeparationNerve[2, 3]]],
    First[SeparationNerve[2, 3]],
    SeparationNerve[1, 3]
  },
  {
    True,
    36,
    60,
    {8},
    {
      {{1, 1}, {1, 1}, {1, 1}}, {{1, 1}, {1, 1}, {2, 1}}, {{1, 1}, {2, 1}, {1, 1}}, {{1, 1}, {2, 1}, {2, 1}},
      {{2, 1}, {1, 1}, {1, 1}}, {{2, 1}, {1, 1}, {2, 1}}, {{2, 1}, {2, 1}, {1, 1}}, {{2, 1}, {2, 1}, {2, 1}}
    },
    {
      {{{1, 1}, {1, 1}, {1, 1}}}, {{{1, 1}, {1, 1}, {1, -1}}}, {{{1, -1}, {1, 1}, {1, 1}}},
      {{{1, -1}, {1, -1}, {1, 1}}}, {{{1, 1}, {1, -1}, {1, -1}}}, {{{1, -1}, {1, -1}, {1, -1}}}
    }
  },
  TestID -> "LittleCubes-separation-nerve"
]

(* the nerve of the cover by the facets has the same homotopy type *)

VerificationTest[
  {
    FacetNerve[{{1, 2}, {2, 3}, {1, 3}}],
    SimplicialBetti[FacetNerve[{{1, 2}, {2, 3}, {1, 3}}]],
    SimplicialBetti[FacetNerve[{{1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}}]],
    Table[SimplicialBetti[FacetNerve[SeparationNerve[n]]], {n, 1, 4}],
    Table[SimplicialBetti[FacetNerve[SeparationNerve[n, 2]]], {n, 1, 3}]
  },
  {
    {{1, 2}, {1, 3}, {2, 3}},
    {1, 1},
    {1, 0, 1},
    {{2}, {1, 1}, {1, 0, 1, 0}, {1, 0, 0, 1, 0, 0, 0, 0}},
    {{2}, {1, 1}, {1, 0, 1, 0}}
  },
  TestID -> "LittleCubes-facet-nerve"
]

(* three little squares: the Betti numbers 1, 3, 2 of the configuration space
   of three points in the plane; three little intervals: 3! components *)

VerificationTest[
  {
    Length[FacetNerve[SeparationNerve[2, 3]]],
    Union[Map[Length, FacetNerve[SeparationNerve[2, 3]]]],
    SimplicialBetti[FacetNerve[SeparationNerve[2, 3]]],
    SimplicialBetti[FacetNerve[SeparationNerve[1, 3]]],
    SimplicialBetti[FacetNerve[SeparationNerve[1, 4]]]
  },
  {60, {3, 6}, {1, 3, 2, 0, 0, 0}, {6}, {24}},
  TestID -> "LittleCubes-three-cubes"
]
