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
