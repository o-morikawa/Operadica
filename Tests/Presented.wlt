(* Presented: symmetric operads by generators and relations, with Koszul signs.
   The expected values are those of reference/presented_reference.py. *)

(* ---------------------------------------------------------------------- *)
(* labelled trees                                                         *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    Table[Length[ShuffleTrees[LieOperad[], n]], {n, 1, 6}],
    Table[Length[ShuffleTrees[PresentedAssociativeOperad[], n]], {n, 1, 5}],
    ShuffleTrees[LieOperad[], 3],
    ShuffleTrees[{OpCom}, {5, 2}],
    AllTrue[ShuffleTrees[PoissonOperad[], 4], ShuffleTreeQ],
    ShuffleTreeQ[OpLie[OpLie[2, 3], 1]]
  },
  {
    {1, 1, 3, 15, 105, 945},
    {1, 2, 12, 120, 1680},
    {OpLie[1, OpLie[2, 3]], OpLie[OpLie[1, 3], 2], OpLie[OpLie[1, 2], 3]},
    {OpCom[2, 5]},
    True,
    False
  },
  TestID -> "Presented-shuffle-trees"
]

(* the symmetry of the generators brings every tree to a shuffle tree *)

VerificationTest[
  {
    ShuffleNormalize[LieOperad[], LBasis[OpLie[3, OpLie[2, 1]]]],
    ShuffleNormalize[LieOperad[], LBasis[OpLie[2, 1]]],
    ShuffleNormalize[PresentedCommutativeOperad[], LBasis[OpCom[OpCom[3, 4], OpCom[1, 2]]]],
    ShuffleNormalize[PresentedAssociativeOperad[], LBasis[OpAss[2, 1]]],
    ShuffleNormalize[PresentedAssociativeOperad[], LBasis[OpAss[OpAss[3, 1], 2]]]
  },
  {
    LBasis[OpLie[OpLie[1, 2], 3]],
    -LBasis[OpLie[1, 2]],
    LBasis[OpCom[OpCom[1, 2], OpCom[3, 4]]],
    LBasis[OpAssOp[1, 2]],
    LBasis[OpAss[OpAssOp[1, 3], 2]]
  },
  TestID -> "Presented-normalize"
]

(* Koszul sign: two subtrees of odd degree anticommute when they are swapped *)

VerificationTest[
  With[{t = LBasis[OpLie[OpLie[3, 4], OpLie[1, 2]]], u = LBasis[OpLie[OpLie[1, 2], OpLie[3, 4]]]},
    {
      ShuffleNormalize[PresentedOperad[{OpLie -> 1}, {}], t] === u,
      ShuffleNormalize[PresentedOperad[{OpLie -> {1, 1}}, {}], t] === -u,
      ShuffleNormalize[PresentedOperad[{OpLie -> {1, 2}}, {}], t] === u,
      ShuffleNormalize[GerstenhaberOperad[], t] === -u,
      ShuffleNormalize[GerstenhaberOperad[], LBasis[OpLie[2, 1]]] === LBasis[OpLie[1, 2]],
      ShuffleNormalize[PoissonOperad[3], LBasis[OpLie[2, 1]]] === -LBasis[OpLie[1, 2]]
    }
  ],
  {True, True, True, True, True, True},
  TestID -> "Presented-Koszul-swap"
]

VerificationTest[
  {
    PresentedOperad[{OpAss -> OpAssOp}, {}]["Generators"],
    GerstenhaberOperad[]["Spec"],
    Lookup[PoissonOperad[3]["Spec"], Key[OpLie]],
    Length[LieOperad[]["Relations"]],
    Table[OperadDimension[PresentedOperad[{OpLie -> -1}, {}], n], {n, 1, 4}]
  },
  {
    {OpAss, OpAssOp},
    <|OpCom -> {1, OpCom, 0}, OpLie -> {1, OpLie, 1}|>,
    {-1, OpLie, 2},
    2,
    {1, 1, 3, 15}
  },
  TestID -> "Presented-presentation"
]

VerificationTest[
  Quiet[
    {
      PresentedOperad[{OpLie -> 2}, {}],
      PresentedOperad[{OpLie -> -1}, {LBasis[OpCom[OpCom[1, 2], 3]]}],
      PresentedOperad[{OpLie -> -1}, {LBasis[OpLie[OpLie[1, 2], 4]]}],
      PresentedOperad[{OpCom -> 1, OpLie -> {1, 1}},
        {LBasis[OpLie[OpLie[1, 2], 3]] + LBasis[OpCom[OpCom[1, 2], 3]]}],
      ShuffleNormalize[LieOperad[], LBasis[OpLie[1, 1]]],
      OperadReduce[LieOperad[], LBasis[OpLie[1, 3]]]
    }
  ],
  {$Failed, $Failed, $Failed, $Failed, $Failed, $Failed},
  TestID -> "Presented-invalid-input"
]

(* ---------------------------------------------------------------------- *)
(* dimensions                                                             *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    Table[OperadDimension[PresentedCommutativeOperad[], n], {n, 1, 5}],
    Table[OperadDimension[LieOperad[], n], {n, 1, 5}],
    Table[OperadDimension[PresentedAssociativeOperad[], n], {n, 1, 4}],
    Table[OperadDimension[PoissonOperad[], n], {n, 1, 4}]
  },
  {{1, 1, 1, 1, 1}, {1, 1, 2, 6, 24}, {1, 2, 6, 24}, {1, 2, 6, 24}},
  TestID -> "Presented-dimensions"
]

(* P_n = H_*(E_n): the dimensions by degree are the Betti numbers of the
   configuration space of k points in R^n, the coefficients of
   (1 + t)(1 + 2 t) ... (1 + (k - 1) t), with t of degree n - 1 *)

VerificationTest[
  {
    Table[OperadDimensionsByGenerator[PoissonOperad[], k, OpLie], {k, 1, 4}],
    Table[OperadDimensionsByGenerator[GerstenhaberOperad[], k, OpLie], {k, 1, 4}],
    Table[OperadDimensionsByGenerator[PoissonOperad[3], k, OpLie], {k, 1, 4}] ===
      Table[CoefficientList[Product[1 + j tt, {j, 1, k - 1}], tt], {k, 1, 4}]
  },
  {
    {{1}, {1, 1}, {1, 3, 2}, {1, 6, 11, 6}},
    {{1}, {1, 1}, {1, 3, 2}, {1, 6, 11, 6}},
    True
  },
  TestID -> "Presented-Poincare-polynomials"
]

VerificationTest[
  {
    OperadDimensionsByDegree[PoissonOperad[], 4],
    OperadDimensionsByDegree[GerstenhaberOperad[], 4],
    OperadDimensionsByDegree[PoissonOperad[3], 4],
    OperadDimensionsByDegree[PoissonOperad[4], 3],
    Table[OperadDimension[PresentedOperad[{OpLie -> {1, 1}}, LieOperad[]["GivenRelations"]], n], {n, 1, 5}]
  },
  {
    <|0 -> 24|>,
    <|0 -> 1, 1 -> 6, 2 -> 11, 3 -> 6|>,
    <|0 -> 1, 2 -> 6, 4 -> 11, 6 -> 6|>,
    <|0 -> 1, 3 -> 3, 6 -> 2|>,
    {1, 1, 2, 6, 24}
  },
  TestID -> "Presented-dimensions-by-degree"
]

(* controls: the same relations without the Koszul signs (a symmetric
   bracket of degree 0) present different, smaller operads; without the
   Leibniz rule the operad is larger; a wrong sign in the Jacobi relation
   kills the brackets of three elements *)

VerificationTest[
  {
    Table[OperadDimension[PresentedOperad[{OpLie -> 1}, LieOperad[]["GivenRelations"]], n], {n, 1, 5}],
    Table[
      OperadDimension[PresentedOperad[{OpCom -> 1, OpLie -> 1}, PoissonOperad[]["GivenRelations"]], n],
      {n, 1, 4}
    ],
    OperadDimension[PresentedOperad[{OpCom -> 1, OpLie -> -1}, Take[PoissonOperad[]["GivenRelations"], 2]], 3],
    OperadDimension[
      PresentedOperad[{OpLie -> -1},
        {LBasis[OpLie[OpLie[1, 2], 3]] + LBasis[OpLie[OpLie[2, 3], 1]] - LBasis[OpLie[OpLie[3, 1], 2]]}],
      3
    ]
  },
  {{1, 1, 2, 5, 15}, {1, 2, 6, 20}, 9, 0},
  TestID -> "Presented-controls"
]

(* ---------------------------------------------------------------------- *)
(* normal forms                                                           *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    OperadBasis[PresentedCommutativeOperad[], 4],
    OperadBasis[LieOperad[], 3],
    Sort[OperadBasis[LieOperad[], 4]] ===
      Sort[Table[OpLie[OpLie[OpLie[1, p[[1]]], p[[2]]], p[[3]]], {p, Permutations[{2, 3, 4}]}]],
    OperadBasis[PoissonOperad[], 3],
    OperadBasis[GerstenhaberOperad[], 3] === OperadBasis[PoissonOperad[], 3],
    AllTrue[OperadBasis[PoissonOperad[], 4], Function[t, FreeQ[t, OpLie[___, _OpCom, ___]]]],
    AllTrue[OperadBasis[GerstenhaberOperad[], 4], Function[t, FreeQ[t, OpLie[___, _OpCom, ___]]]]
  },
  {
    {OpCom[OpCom[OpCom[1, 2], 3], 4]},
    {OpLie[OpLie[1, 3], 2], OpLie[OpLie[1, 2], 3]},
    True,
    {
      OpCom[1, OpLie[2, 3]], OpCom[OpLie[1, 3], 2], OpLie[OpLie[1, 3], 2],
      OpCom[OpCom[1, 2], 3], OpCom[OpLie[1, 2], 3], OpLie[OpLie[1, 2], 3]
    },
    True,
    True,
    True
  },
  TestID -> "Presented-bases"
]

(* the Jacobi relation as a rewriting rule; in the Gerstenhaber operad the
   bracket has degree 1 and the signs change *)

VerificationTest[
  With[{t = LBasis[OpLie[1, OpLie[2, 3]]], x = LBasis[OpLie[OpLie[1, 2], 3]], y = LBasis[OpLie[OpLie[1, 3], 2]]},
    {
      OperadReduce[LieOperad[], t] === x - y,
      OperadReduce[PoissonOperad[], t] === x - y,
      OperadReduce[GerstenhaberOperad[], t] === -x - y,
      OperadReduce[PoissonOperad[3], t] === x - y,
      OperadZeroQ[LieOperad[], t - x + y],
      OperadZeroQ[LieOperad[], t - x - y]
    }
  ],
  {True, True, True, True, True, False},
  TestID -> "Presented-Jacobi-normal-form"
]

VerificationTest[
  With[{
      b = LBasis[OpLie[OpLie[1, 2], OpLie[3, 4]]],
      x = LBasis[OpLie[OpLie[OpLie[1, 2], 3], 4]],
      y = LBasis[OpLie[OpLie[OpLie[1, 2], 4], 3]]
    },
    {
      OperadReduce[LieOperad[], b] === x - y,
      OperadReduce[PoissonOperad[3], b] === x - y,
      OperadReduce[GerstenhaberOperad[], b] === x + y
    }
  ],
  {True, True, True},
  TestID -> "Presented-bracket-of-brackets"
]

(* the bracket is a derivation of the product in each argument *)

VerificationTest[
  Table[
    {
      OperadReduce[op, LBasis[OpLie[1, OpCom[2, 3]]]] ===
        LBasis[OpCom[OpLie[1, 2], 3]] + LBasis[OpCom[OpLie[1, 3], 2]],
      OperadReduce[op, LBasis[OpLie[OpCom[1, 2], 3]]] ===
        LBasis[OpCom[1, OpLie[2, 3]]] + LBasis[OpCom[OpLie[1, 3], 2]],
      OperadReduce[op, LBasis[OpCom[1, OpCom[2, 3]]]] === LBasis[OpCom[OpCom[1, 2], 3]]
    },
    {op, {PoissonOperad[], GerstenhaberOperad[], PoissonOperad[3]}}
  ],
  {{True, True, True}, {True, True, True}, {True, True, True}},
  TestID -> "Presented-Leibniz-normal-form"
]

(* an identity of arity 4 that follows from the relations:
   {ab, cd} = a{b,c}d + ac{b,d} + b{a,c}d + bc{a,d} *)

VerificationTest[
  With[{
      lhs = LBasis[OpLie[OpCom[1, 2], OpCom[3, 4]]],
      t1 = LBasis[OpCom[OpCom[1, OpLie[2, 3]], 4]],
      t2 = LBasis[OpCom[OpCom[1, 3], OpLie[2, 4]]],
      t3 = LBasis[OpCom[OpCom[2, OpLie[1, 3]], 4]],
      t4 = LBasis[OpCom[OpCom[2, 3], OpLie[1, 4]]]
    },
    {
      OperadZeroQ[PoissonOperad[], lhs - t1 - t2 - t3 - t4],
      OperadZeroQ[GerstenhaberOperad[], lhs - t1 - t2 - t3 - t4],
      OperadZeroQ[PoissonOperad[], lhs - t1 - t2 - t3 + t4],
      OperadReduce[PoissonOperad[], lhs] ===
        LBasis[OpCom[OpCom[1, OpLie[2, 3]], 4]] + LBasis[OpCom[OpCom[OpLie[1, 3], 2], 4]] +
          LBasis[OpCom[OpCom[1, OpLie[2, 4]], 3]] + LBasis[OpCom[OpCom[OpLie[1, 4], 2], 3]]
    }
  ],
  {True, True, False, True},
  TestID -> "Presented-identity-arity-four"
]

VerificationTest[
  With[{op = PoissonOperad[]},
    {
      OperadIdealBasis[LieOperad[], 3],
      Length[OperadIdealBasis[op, 3]],
      Length[OperadIdealBasis[op, 4]],
      AllTrue[OperadIdealBasis[op, 4], Function[v, OperadZeroQ[op, v]]],
      OperadIdealBasis[op, 2]
    }
  ],
  {
    {LBasis[OpLie[1, OpLie[2, 3]]] + LBasis[OpLie[OpLie[1, 3], 2]] - LBasis[OpLie[OpLie[1, 2], 3]]},
    6,
    96,
    True,
    {}
  },
  TestID -> "Presented-ideal"
]

(* ---------------------------------------------------------------------- *)
(* composition and the symmetric groups                                   *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{lie = LieOperad[], ger = GerstenhaberOperad[], br = LBasis[OpLie[1, 2]]},
    {
      PresentedCompose[lie][br, 1, br],
      PresentedCompose[lie][br, 2, br],
      PresentedCompose[lie][LBasis[OpLie[1, OpLie[2, 3]]], 1, br],
      (* the bracket of degree 1 passes the vertex to the right of input 1 *)
      PresentedCompose[ger][LBasis[OpLie[1, OpLie[2, 3]]], 1, br],
      PresentedCompose[ger][LBasis[OpLie[OpLie[1, 2], 3]], 3, br],
      PresentedCompose[ger][LBasis[OpLie[1, OpLie[2, 3]]], 1, LBasis[OpCom[1, 2]]],
      PresentedCompose[lie][br - 2 LBasis[OpLie[2, 1]], 1, LBasis[1]]
    }
  ],
  {
    LBasis[OpLie[OpLie[1, 2], 3]],
    LBasis[OpLie[1, OpLie[2, 3]]],
    LBasis[OpLie[OpLie[1, 2], OpLie[3, 4]]],
    -LBasis[OpLie[OpLie[1, 2], OpLie[3, 4]]],
    LBasis[OpLie[OpLie[1, 2], OpLie[3, 4]]],
    LBasis[OpLie[OpCom[1, 2], OpLie[3, 4]]],
    3 LBasis[OpLie[1, 2]]
  },
  TestID -> "Presented-compose"
]

VerificationTest[
  {
    PresentedAct[LieOperad[]][LBasis[OpLie[OpLie[1, 2], 3]], {2, 3, 1}],
    PresentedAct[GerstenhaberOperad[]][LBasis[OpLie[OpLie[1, 2], 3]], {2, 3, 1}],
    PresentedAct[PresentedAssociativeOperad[]][LBasis[OpAss[OpAss[1, 2], 3]], {2, 3, 1}],
    PresentedAct[LieOperad[]][LBasis[OpLie[1, 2]], {2, 1}],
    PresentedAct[LieOperad[]][LBasis[OpLie[OpLie[1, 2], 3]], {1, 2, 3}]
  },
  {
    -LBasis[OpLie[OpLie[1, 3], 2]],
    LBasis[OpLie[OpLie[1, 3], 2]],
    LBasis[OpAss[OpAssOp[1, 3], 2]],
    -LBasis[OpLie[1, 2]],
    LBasis[OpLie[OpLie[1, 2], 3]]
  },
  TestID -> "Presented-action"
]

(* equivariance in the quotient, with the block permutations of the operad layer:
   (a.s) o_i (b.t) = (a o_s(i) b).(s o_i t) *)

VerificationTest[
  Table[
    AllTrue[
      Flatten[
        Table[
          {a, b, s, t, i},
          {sizes, {{2, 2}, {3, 2}, {2, 3}}},
          {a, OperadBasis[op, sizes[[1]]]},
          {b, OperadBasis[op, sizes[[2]]]},
          {s, Permutations[Range[sizes[[1]]]]},
          {t, Permutations[Range[sizes[[2]]]]},
          {i, 1, sizes[[1]]}
        ],
        5
      ],
      Function[x,
        With[{a = LBasis[x[[1]]], b = LBasis[x[[2]]], s = x[[3]], t = x[[4]], i = x[[5]]},
          OperadReduce[op,
            PresentedCompose[op][PresentedAct[op][a, s], i, PresentedAct[op][b, t]]
          ] ===
          OperadReduce[op,
            PresentedAct[op][PresentedCompose[op][a, s[[i]], b], PermutationCompose[s, i, t]]
          ]
        ]
      ]
    ],
    {op, {LieOperad[], GerstenhaberOperad[], PresentedAssociativeOperad[]}}
  ],
  {True, True, True},
  TestID -> "Presented-equivariance"
]

(* the quotient is an operad: unit, sequential and parallel axioms, the last
   with the Koszul sign (-1)^(|b| |c|) *)

VerificationTest[
  {
    DGOperadQ[GerstenhaberOperad[], 4],
    DGOperadQ[PoissonOperad[3], 3],
    DGOperadQ[PresentedAssociativeOperad[], 3],
    DGOperadCheck[GerstenhaberOperad[], 3]["Checked"]
  },
  {True, True, True, <|"Unit" -> 32, "Sequential" -> 85, "Parallel" -> 28|>},
  TestID -> "Presented-operad-axioms"
]

(* control: with the degrees forgotten, the parallel axiom fails *)

VerificationTest[
  With[{check = DGOperadCheck[Join[GerstenhaberOperad[], <|"Degree" -> Function[t, 0]|>], 4]},
    {check["Passed"], check["Failed"]["Unit"], check["Failed"]["Sequential"], check["Failed"]["Parallel"] > 0}
  ],
  {False, 0, 0, True},
  TestID -> "Presented-operad-axioms-control"
]

(* the presented associative operad is the operad of words of the operad layer *)

VerificationTest[
  With[{pa = PresentedAssociativeOperad[], wo = WordOperad[]},
    {
      Table[
        Sort[Map[OpAssWord, OperadBasis[pa, n]]] === Sort[Permutations[Range[n]]],
        {n, 1, 4}
      ],
      AllTrue[
        Flatten[
          Table[
            {a, i, b},
            {sizes, {{2, 2}, {2, 3}, {3, 2}}},
            {a, OperadBasis[pa, sizes[[1]]]},
            {b, OperadBasis[pa, sizes[[2]]]},
            {i, 1, sizes[[1]]}
          ],
          3
        ],
        Function[x,
          With[{res = pa["Compose"][x[[1]], x[[2]], x[[3]]]},
            MatchQ[res, LBasis[_]] &&
              OpAssWord[First[res]] === wo["Compose"][OpAssWord[x[[1]]], x[[2]], OpAssWord[x[[3]]]]
          ]
        ]
      ],
      AllTrue[
        Flatten[Table[{a, s}, {a, OperadBasis[pa, 3]}, {s, Permutations[Range[3]]}], 1],
        Function[x,
          With[{res = pa["Action"][x[[1]], x[[2]]]},
            MatchQ[res, LBasis[_]] &&
              OpAssWord[First[res]] === wo["Action"][OpAssWord[x[[1]]], x[[2]]]
          ]
        ]
      ],
      OperadReduce[pa, LBasis[OpAss[1, OpAss[2, 3]]]],
      OpAssWord[OpAssOp[OpAss[1, 3], 2]]
    }
  ],
  {{True, True, True, True}, True, True, LBasis[OpAss[OpAss[1, 2], 3]], {2, 1, 3}},
  TestID -> "Presented-associative-words"
]

(* ---------------------------------------------------------------------- *)
(* morphisms                                                              *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{com = PresentedCommutativeOperad[], lie = LieOperad[], ass = PresentedAssociativeOperad[],
      pois = PoissonOperad[], ger = GerstenhaberOperad[]},
    {
      (* the commutator of an associative product is a Lie bracket *)
      OperadMorphismQ[lie, ass, {OpLie -> LBasis[OpAss[1, 2]] - LBasis[OpAssOp[1, 2]]}],
      (* a commutative algebra is an associative algebra *)
      OperadMorphismQ[ass, com, {OpAss -> LBasis[OpCom[1, 2]], OpAssOp -> LBasis[OpCom[1, 2]]}],
      OperadMorphismQ[lie, pois, {OpLie -> LBasis[OpLie[1, 2]]}],
      OperadMorphismQ[com, pois, {OpCom -> LBasis[OpCom[1, 2]]}],
      OperadMorphismQ[com, ger, {OpCom -> LBasis[OpCom[1, 2]]}],
      (* the trivial bracket *)
      OperadMorphismQ[pois, com, {OpCom -> LBasis[OpCom[1, 2]], OpLie -> 0}]
    }
  ],
  {True, True, True, True, True, True},
  TestID -> "Presented-morphisms"
]

VerificationTest[
  With[{com = PresentedCommutativeOperad[], lie = LieOperad[], ass = PresentedAssociativeOperad[],
      pois = PoissonOperad[], ger = GerstenhaberOperad[]},
    {
      (* the anticommutator is not antisymmetric *)
      OperadMorphismQ[lie, ass, {OpLie -> LBasis[OpAss[1, 2]] + LBasis[OpAssOp[1, 2]]}],
      (* the anticommutator (Jordan product) is commutative but not associative *)
      OperadMorphismQ[com, ass, {OpCom -> LBasis[OpAss[1, 2]] + LBasis[OpAssOp[1, 2]]}],
      (* a product alone is not a bracket *)
      OperadMorphismQ[lie, ass, {OpLie -> LBasis[OpAss[1, 2]]}],
      OperadMorphismQ[com, pois, {OpCom -> LBasis[OpLie[1, 2]]}],
      (* the bracket of the Gerstenhaber operad has degree 1 *)
      OperadMorphismQ[lie, ger, {OpLie -> LBasis[OpLie[1, 2]]}],
      OperadMorphismQ[lie, ass, {}]
    }
  ],
  {False, False, False, False, False, False},
  TestID -> "Presented-morphisms-control"
]

VerificationTest[
  With[{ass = PresentedAssociativeOperad[]},
    OperadReduce[ass,
      OperadMorphismImage[ass, {OpLie -> LBasis[OpAss[1, 2]] - LBasis[OpAssOp[1, 2]]}][
        LBasis[OpLie[OpLie[1, 2], 3]]
      ]
    ]
  ],
  (* [[x1, x2], x3] = x1 x2 x3 - x2 x1 x3 - x3 x1 x2 + x3 x2 x1 *)
  LBasis[OpAss[OpAss[1, 2], 3]] - LBasis[OpAss[OpAssOp[1, 2], 3]] -
    LBasis[OpAss[OpAssOp[1, 3], 2]] + LBasis[OpAssOp[1, OpAssOp[2, 3]]],
  TestID -> "Presented-commutator-image"
]

(* ---------------------------------------------------------------------- *)
(* generating series of Koszul dual operads                               *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{
      com = Table[OperadDimension[PresentedCommutativeOperad[], n], {n, 1, 5}],
      lie = Table[OperadDimension[LieOperad[], n], {n, 1, 5}],
      ass = Table[OperadDimension[PresentedAssociativeOperad[], n], {n, 1, 4}],
      pois = Table[OperadDimension[PoissonOperad[], n], {n, 1, 4}]
    },
    {
      KoszulSeriesQ[com, lie],
      KoszulSeriesQ[lie, com],
      KoszulSeriesQ[ass, ass],
      KoszulSeriesQ[pois, pois],
      KoszulSeriesQ[com, com],
      KoszulSeriesQ[{1, 1, 1, 1, 1, 1}, {1, 1, 2, 6, 24, 120}]
    }
  ],
  {True, True, True, True, False, True},
  TestID -> "Presented-Koszul-series"
]

(* ---------------------------------------------------------------------- *)
(* characters of the symmetric groups, and free algebras                  *)
(* ---------------------------------------------------------------------- *)

(* the cycle types are listed as in IntegerPartitions[k]: the identity is
   last.  Com(k) is the trivial representation, Ass(k) the regular one, and
   Lie(3), Lie(4) have the characters (-1, 0, 2) and (0, 0, -2, 0, 6) *)

VerificationTest[
  With[{values = Function[{oper, arity}, Map[Function[tr, Lookup[tr, 0, 0]], Values[OperadCharacter[oper, arity]]]]},
    {
      Keys[OperadCharacter[LieOperad[], 3]],
      Keys[OperadCharacter[LieOperad[], 4]],
      Table[values[PresentedCommutativeOperad[], k], {k, 2, 4}],
      Table[values[PresentedAssociativeOperad[], k], {k, 2, 4}],
      Table[values[LieOperad[], k], {k, 2, 4}],
      OperadCharacter[LieOperad[], 1]
    }
  ],
  {
    {{3}, {2, 1}, {1, 1, 1}},
    {{4}, {3, 1}, {2, 2}, {2, 1, 1}, {1, 1, 1, 1}},
    {{1, 1}, {1, 1, 1}, {1, 1, 1, 1, 1}},
    {{0, 2}, {0, 0, 6}, {0, 0, 0, 0, 24}},
    {{-1, 1}, {-1, 0, 2}, {0, 0, -2, 0, 6}},
    <|{1} -> <|0 -> 1|>|>
  },
  TestID -> "Presented-characters"
]

(* the Gerstenhaber operad in arity 3, by the number of brackets; the Poisson
   operad is the regular representation *)

VerificationTest[
  {
    OperadCharacter[GerstenhaberOperad[], 3],
    Table[Map[Total, Values[OperadCharacter[PoissonOperad[1], k]]], {k, 2, 4}]
  },
  {
    <|
      {3} -> <|0 -> 1, 2 -> -1|>,
      {2, 1} -> <|0 -> 1, 1 -> 1|>,
      {1, 1, 1} -> <|0 -> 1, 1 -> 3, 2 -> 2|>
    |>,
    {{0, 2}, {0, 0, 6}, {0, 0, 0, 0, 24}}
  },
  TestID -> "Presented-characters-Poisson"
]

(* free algebras on graded generators, arity by arity: symmetric and exterior
   powers over Com, tensor powers over Ass, the free Lie algebra on two even
   and on two odd generators (2, 1, 2, 3 and 2, 3, 2, 3), and the free
   Gerstenhaber algebra on a class x of degree 2: x^k and x^(k-2) [x, x] *)

VerificationTest[
  {
    FreeAlgebraDimensions[PresentedCommutativeOperad[], {2}, 4],
    FreeAlgebraDimensions[PresentedCommutativeOperad[], {1}, 4],
    FreeAlgebraDimensions[PresentedAssociativeOperad[], {1, 1}, 4],
    FreeAlgebraDimensions[LieOperad[], {2, 2}, 4],
    FreeAlgebraDimensions[LieOperad[], {1, 1}, 4],
    FreeAlgebraDimensions[GerstenhaberOperad[], {2}, 4]
  },
  {
    <|1 -> <|2 -> 1|>, 2 -> <|4 -> 1|>, 3 -> <|6 -> 1|>, 4 -> <|8 -> 1|>|>,
    <|1 -> <|1 -> 1|>, 2 -> <||>, 3 -> <||>, 4 -> <||>|>,
    <|1 -> <|1 -> 2|>, 2 -> <|2 -> 4|>, 3 -> <|3 -> 8|>, 4 -> <|4 -> 16|>|>,
    <|1 -> <|2 -> 2|>, 2 -> <|4 -> 1|>, 3 -> <|6 -> 2|>, 4 -> <|8 -> 3|>|>,
    <|1 -> <|1 -> 2|>, 2 -> <|2 -> 3|>, 3 -> <|3 -> 2|>, 4 -> <|4 -> 3|>|>,
    <|1 -> <|2 -> 1|>, 2 -> <|4 -> 1, 5 -> 1|>, 3 -> <|6 -> 1, 7 -> 1|>, 4 -> <|8 -> 1, 9 -> 1|>|>
  },
  TestID -> "Presented-free-algebra"
]
