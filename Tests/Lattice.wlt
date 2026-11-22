(* Lattice: cochains on the hypercubic lattice, coboundary, cup, higher cup.

   Generic cochains Cochain[p, f] with f an undefined symbol have independent
   symbolic values f[x, s].  Identities are tested at a symbolic base point,
   which proves them for every hypercubic lattice of that dimension.

   The expected component formulas are those of Appendix A of
   Jacobson-Sulejmanpasic, arXiv:2303.06160 (which follow Chen-Tata,
   arXiv:2106.05274). *)

(* ---------------------------------------------------------------------- *)
(* cells and evaluation                                                   *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {Length[LCells[{2, 3}, 0]], Length[LCells[{2, 3}, 1]], Length[LCells[{2, 3}, 2]], Length[LCells[{2, 2, 2, 2}, 2]]},
  {6, 12, 6, 96},
  TestID -> "Lattice-cells-count"
]

VerificationTest[
  {
    CochainValue[Cochain[2, bb], {x1, x2}, {1, 2}],
    CochainValue[Cochain[2, bb], {x1, x2}, {2, 1}],
    CochainValue[Cochain[2, bb], {x1, x2}, {1, 1}],
    CochainValue[Cochain[2, bb], {x1, x2}, {1}],
    CochainValue[Cochain[2, bb], LCell[{x1, x2}, {1, 2}]]
  },
  {bb[{x1, x2}, {1, 2}], -bb[{x1, x2}, {1, 2}], 0, 0, bb[{x1, x2}, {1, 2}]},
  TestID -> "Lattice-value-antisymmetry"
]

VerificationTest[
  {
    CochainDegree[Coboundary[Cochain[1, aa]]],
    CochainDegree[Cup[Cochain[1, aa], Cochain[2, bb]]],
    CochainDegree[HigherCup[1][Cochain[2, aa], Cochain[3, bb]]],
    CochainDegree[2 Cup[Cochain[1, aa], Cochain[1, bb]] - Coboundary[Cochain[1, aa]]]
  },
  {2, 3, 4, 2},
  TestID -> "Lattice-degree"
]

VerificationTest[
  {CochainQ[Cochain[1, aa]], CochainQ[3 Coboundary[Cochain[1, aa]]], CochainQ[aa], CochainQ[Cochain[1, aa] Cochain[1, bb]]},
  {True, True, False, False},
  TestID -> "Lattice-CochainQ"
]

(* ---------------------------------------------------------------------- *)
(* coboundary                                                             *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  CochainValue[Coboundary[Cochain[0, phi]], {x1, x2}, {2}],
  phi[{x1, 1 + x2}, {}] - phi[{x1, x2}, {}],
  TestID -> "Lattice-d-gradient"
]

(* the plaquette *)

VerificationTest[
  Expand[
    CochainValue[Coboundary[Cochain[1, aa]], {x1, x2}, {1, 2}] -
      (aa[{x1, x2}, {1}] + aa[{1 + x1, x2}, {2}] - aa[{x1, 1 + x2}, {1}] - aa[{x1, x2}, {2}])
  ],
  0,
  TestID -> "Lattice-d-plaquette"
]

VerificationTest[
  AllTrue[Range[0, 2], CochainZeroQ[Coboundary[Coboundary[Cochain[#, ff]]], 4] &],
  True,
  TestID -> "Lattice-d-squared-zero-d4"
]

(* ---------------------------------------------------------------------- *)
(* cup product                                                            *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{x = {x1, x2}},
    Expand[
      CochainValue[Cup[Cochain[1, al], Cochain[1, be]], x, {1, 2}] -
        (al[x, {1}] be[x + {1, 0}, {2}] - al[x, {2}] be[x + {0, 1}, {1}])
    ]
  ],
  0,
  TestID -> "Lattice-cup-1-1"
]

VerificationTest[
  With[{x = {x1, x2}},
    Expand[
      CochainValue[Cup[Cochain[2, be], Cochain[0, al]], x, {1, 2}] -
        be[x, {1, 2}] al[x + {1, 1}, {}]
    ]
  ],
  0,
  TestID -> "Lattice-cup-2-0"
]

VerificationTest[
  With[{x = {x1, x2, x3}},
    Expand[
      CochainValue[Cup[Cochain[1, al], Cochain[2, be]], x, {1, 2, 3}] -
        (al[x, {1}] be[x + {1, 0, 0}, {2, 3}] - al[x, {2}] be[x + {0, 1, 0}, {1, 3}] +
          al[x, {3}] be[x + {0, 0, 1}, {1, 2}])
    ]
  ],
  0,
  TestID -> "Lattice-cup-1-2"
]

VerificationTest[
  With[{x = {x1, x2, x3}},
    Expand[
      CochainValue[Cup[Cochain[2, be], Cochain[1, al]], x, {1, 2, 3}] -
        (be[x, {2, 3}] al[x + {0, 1, 1}, {1}] - be[x, {1, 3}] al[x + {1, 0, 1}, {2}] +
          be[x, {1, 2}] al[x + {1, 1, 0}, {3}])
    ]
  ],
  0,
  TestID -> "Lattice-cup-2-1"
]

(* Leibniz rule: d(a u b) = da u b + (-1)^p a u db *)

VerificationTest[
  AllTrue[
    Select[Tuples[Range[0, 3], 2], Total[#] <= 3 &],
    Function[pq,
      With[{a = Cochain[pq[[1]], fa], b = Cochain[pq[[2]], fb]},
        CochainEqualQ[
          Coboundary[Cup[a, b]],
          Cup[Coboundary[a], b] + (-1)^(pq[[1]]) Cup[a, Coboundary[b]],
          4
        ]
      ]
    ]
  ],
  True,
  TestID -> "Lattice-Leibniz-d4"
]

(* associativity: (C^*, d, u) is a dg associative algebra *)

VerificationTest[
  AllTrue[
    Select[Tuples[Range[0, 4], 3], Total[#] <= 4 &],
    Function[pqr,
      With[{a = Cochain[pqr[[1]], fa], b = Cochain[pqr[[2]], fb], c = Cochain[pqr[[3]], fc]},
        CochainEqualQ[Cup[Cup[a, b], c], Cup[a, Cup[b, c]], 4]
      ]
    ]
  ],
  True,
  TestID -> "Lattice-cup-associative-d4"
]

(* the same statement through the operad layer: the cup product makes
   generic cochains an algebra over the associative operad *)

VerificationTest[
  OpAlgebraCheck[
    {OpAssociativityRelation[m]},
    {m -> Cup},
    {{Cochain[1, fa], Cochain[1, fb], Cochain[1, fc]}, {Cochain[0, fa], Cochain[2, fb], Cochain[1, fc]}},
    "Equal" -> Function[{u, v}, CochainEqualQ[u, v, 3]]
  ]["Passed"],
  True,
  TestID -> "Lattice-cup-algebra-over-As"
]

VerificationTest[
  With[{a = Cochain[1, fa], b = Cochain[1, fb], c = Cochain[1, fc]},
    CochainEqualQ[Cup[a, b, c], Cup[Cup[a, b], c], 3]
  ],
  True,
  TestID -> "Lattice-cup-nary"
]

(* the cup product is not graded commutative on cochains *)

VerificationTest[
  CochainEqualQ[
    Cup[Cochain[1, fa], Cochain[1, fb]],
    -Cup[Cochain[1, fb], Cochain[1, fa]],
    2
  ],
  False,
  TestID -> "Lattice-cup-not-commutative"
]

(* ---------------------------------------------------------------------- *)
(* higher cup products                                                    *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  AllTrue[
    Select[Tuples[Range[0, 4], 2], Total[#] <= 4 &],
    Function[pq,
      With[{a = Cochain[pq[[1]], fa], b = Cochain[pq[[2]], fb]},
        CochainEqualQ[HigherCup[0][a, b], Cup[a, b], 4]
      ]
    ]
  ],
  True,
  TestID -> "Lattice-cup0-is-cup"
]

(* component formulas, arXiv:2303.06160 Appendix A, one and two dimensions *)

VerificationTest[
  With[{x = {x1, x2}},
    Expand[
      CochainValue[HigherCup[1][Cochain[1, al], Cochain[1, be]], x, {1}] -
        al[x, {1}] be[x, {1}]
    ]
  ],
  0,
  TestID -> "Lattice-cup1-1-1"
]

VerificationTest[
  With[{x = {x1, x2}},
    Expand[
      CochainValue[HigherCup[1][Cochain[1, al], Cochain[2, be]], x, {1, 2}] +
        (al[x, {2}] + al[x + {0, 1}, {1}]) be[x, {1, 2}]
    ]
  ],
  0,
  TestID -> "Lattice-cup1-1-2"
]

VerificationTest[
  With[{x = {x1, x2}},
    Expand[
      CochainValue[HigherCup[1][Cochain[2, be], Cochain[1, al]], x, {1, 2}] -
        be[x, {1, 2}] (al[x, {1}] + al[x + {1, 0}, {2}])
    ]
  ],
  0,
  TestID -> "Lattice-cup1-2-1"
]

VerificationTest[
  With[{x = {x1, x2}},
    Expand[
      CochainValue[HigherCup[2][Cochain[2, al], Cochain[2, be]], x, {1, 2}] -
        al[x, {1, 2}] be[x, {1, 2}]
    ]
  ],
  0,
  TestID -> "Lattice-cup2-2-2"
]

(* three dimensions *)

VerificationTest[
  With[{x = {x1, x2, x3}, s = {1, 2, 3}},
    Expand[
      CochainValue[HigherCup[1][Cochain[1, al], Cochain[3, be]], x, s] -
        (al[x, {3}] + al[x + {0, 0, 1}, {2}] + al[x + {0, 1, 1}, {1}]) be[x, s]
    ]
  ],
  0,
  TestID -> "Lattice-cup1-1-3"
]

VerificationTest[
  With[{x = {x1, x2, x3}, s = {1, 2, 3}},
    Expand[
      CochainValue[HigherCup[1][Cochain[3, be], Cochain[1, al]], x, s] -
        be[x, s] (al[x, {1}] + al[x + {1, 0, 0}, {2}] + al[x + {1, 1, 0}, {3}])
    ]
  ],
  0,
  TestID -> "Lattice-cup1-3-1"
]

VerificationTest[
  With[{x = {x1, x2, x3}, e1 = {1, 0, 0}, e2 = {0, 1, 0}, e3 = {0, 0, 1}},
    Expand[
      CochainValue[HigherCup[1][Cochain[2, al], Cochain[2, be]], x, {1, 2, 3}] -
        (
          al[x, {2, 3}] (be[x, {1, 2}] + be[x + e2, {1, 3}]) +
          al[x + e2, {1, 3}] be[x, {1, 2}] -
          al[x, {1, 3}] be[x + e1, {2, 3}] -
          al[x + e3, {1, 2}] (be[x, {1, 3}] + be[x + e1, {2, 3}])
        )
    ]
  ],
  0,
  TestID -> "Lattice-cup1-2-2"
]

VerificationTest[
  With[{x = {x1, x2, x3}, s = {1, 2, 3}},
    Expand[
      CochainValue[HigherCup[2][Cochain[2, al], Cochain[3, be]], x, s] -
        (al[x, {1, 2}] + al[x, {2, 3}] + al[x + {0, 1, 0}, {1, 3}]) be[x, s]
    ]
  ],
  0,
  TestID -> "Lattice-cup2-2-3"
]

VerificationTest[
  With[{x = {x1, x2, x3}, s = {1, 2, 3}},
    Expand[
      CochainValue[HigherCup[2][Cochain[3, be], Cochain[2, al]], x, s] -
        be[x, s] (al[x, {1, 3}] + al[x + {1, 0, 0}, {2, 3}] + al[x + {0, 0, 1}, {1, 2}])
    ]
  ],
  0,
  TestID -> "Lattice-cup2-3-2"
]

VerificationTest[
  With[{x = {x1, x2, x3}, s = {1, 2, 3}},
    Expand[
      CochainValue[HigherCup[3][Cochain[3, al], Cochain[3, be]], x, s] -
        al[x, s] be[x, s]
    ]
  ],
  0,
  TestID -> "Lattice-cup3-3-3"
]

(* the relation between cup_i and cup_{i+1}, arXiv:2303.06160 eq. (A3):
     a u_i b - (-1)^(pq+i) b u_i a
       = (-1)^(p+q+1+i) [ d(a u_{i+1} b) - da u_{i+1} b - (-1)^p a u_{i+1} db ]
   for all degrees in four dimensions *)

VerificationTest[
  AllTrue[
    Flatten[Table[{p, q, i}, {p, 0, 4}, {q, 0, 4}, {i, 0, Min[p, q]}], 2],
    Function[pqi,
      With[{p = pqi[[1]], q = pqi[[2]], i = pqi[[3]]},
        With[{a = Cochain[p, fa], b = Cochain[q, fb]},
          CochainEqualQ[
            HigherCup[i][a, b] - (-1)^(p q + i) HigherCup[i][b, a],
            (-1)^(p + q + 1 + i) (
              Coboundary[HigherCup[i + 1][a, b]] -
              HigherCup[i + 1][Coboundary[a], b] -
              (-1)^p HigherCup[i + 1][a, Coboundary[b]]
            ),
            4
          ]
        ]
      ]
    ]
  ],
  True,
  TestID -> "Lattice-cup-i-relation-d4"
]

(* Steenrod's original convention:
     d(a u_i b) = (-1)^i da u_i b + (-1)^(i+p) a u_i db
                  - (-1)^i a u_{i-1} b - (-1)^(pq) b u_{i-1} a *)

VerificationTest[
  Module[{st},
    st[i_, u_, v_] := SteenrodCupSign[CochainDegree[u], CochainDegree[v], i] HigherCup[i][u, v];
    AllTrue[
      {{1, 1, 1}, {1, 1, 2}, {1, 2, 1}, {2, 1, 1}, {2, 2, 1}, {2, 2, 2}, {2, 3, 2}, {3, 2, 2}},
      Function[pqi,
        With[{p = pqi[[1]], q = pqi[[2]], i = pqi[[3]]},
          With[{a = Cochain[p, fa], b = Cochain[q, fb]},
            CochainEqualQ[
              Coboundary[st[i, a, b]],
              (-1)^i st[i, Coboundary[a], b] + (-1)^(i + p) st[i, a, Coboundary[b]] -
                (-1)^i st[i - 1, a, b] - (-1)^(p q) st[i - 1, b, a],
              4
            ]
          ]
        ]
      ]
    ]
  ],
  True,
  TestID -> "Lattice-Steenrod-convention"
]

(* modulo 2 the signs disappear: a u b + b u a = d(a u_1 b) + da u_1 b + a u_1 db *)

VerificationTest[
  With[{a = Cochain[1, fa], b = Cochain[1, fb]},
    With[{lhs = Cup[a, b] + Cup[b, a],
        rhs = Coboundary[HigherCup[1][a, b]] + HigherCup[1][Coboundary[a], b] + HigherCup[1][a, Coboundary[b]]},
      {CochainEqualQ[lhs, rhs, 3, Modulus -> 2], CochainEqualQ[lhs, rhs, 3]}
    ]
  ],
  {True, False},
  TestID -> "Lattice-commutativity-mod-2"
]

VerificationTest[
  CochainEqualQ[SteenrodSquare[2][Cochain[2, fb]], Cup[Cochain[2, fb], Cochain[2, fb]], 4],
  True,
  TestID -> "Lattice-Sq-top"
]

(* ---------------------------------------------------------------------- *)
(* Pontryagin square                                                      *)
(* ---------------------------------------------------------------------- *)

(* d P(B) = 2 dB u B - dB u_1 dB, hence P(B) is closed modulo 2N when
   dB = 0 modulo N and N is even.  A five-dimensional identity. *)

VerificationTest[
  With[{b = Cochain[2, bb]},
    CochainEqualQ[
      Coboundary[PontryaginSquare[b]],
      2 Cup[Coboundary[b], b] - HigherCup[1][Coboundary[b], Coboundary[b]],
      5
    ]
  ],
  True,
  TestID -> "Lattice-Pontryagin-coboundary-d5"
]

(* 't Hooft flux on the four-torus: the integral of P(B) is twice the
   Pfaffian z12 z34 - z13 z24 + z14 z23 *)

VerificationTest[
  With[{z = {{0, 1, 2, -1}, {-1, 0, 3, 5}, {-2, -3, 0, 7}, {1, -5, -7, 0}}},
    Table[
      With[{b = THooftFluxCochain[z, dims]},
        {CochainZeroQ[Coboundary[b], dims], CochainIntegrate[PontryaginSquare[b], dims]}
      ],
      {dims, {{2, 2, 2, 2}, {3, 2, 3, 2}}}
    ]
  ],
  {{True, -12}, {True, -12}},
  TestID -> "Lattice-tHooft-flux"
]

(* ---------------------------------------------------------------------- *)
(* concrete fields on a periodic lattice                                  *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{c = PeriodicCochain[1, {2, 2}, <|{{0, 0}, {1}} -> 5, {{1, 0}, {2}} -> -2|>]},
    {
      CochainValue[c, {0, 0}, {1}],
      CochainValue[c, {2, 2}, {1}],
      CochainValue[c, {1, 0}, {2}],
      CochainValue[c, {1, 1}, {2}],
      CochainValue[Coboundary[c], {0, 0}, {1, 2}]
    }
  ],
  {5, 5, -2, 0, 3},
  TestID -> "Lattice-periodic-cochain"
]

(* Stokes: the integral of an exact top form over the torus vanishes *)

VerificationTest[
  (
    SeedRandom[20261122];
    With[{c = RandomCochain[2, {3, 3, 3}]},
      CochainIntegrate[Coboundary[c], {3, 3, 3}]
    ]
  ),
  0,
  TestID -> "Lattice-Stokes"
]

(* the Leibniz rule on a concrete random configuration *)

VerificationTest[
  (
    SeedRandom[7];
    With[{a = RandomCochain[1, {3, 3, 3}], b = RandomCochain[1, {3, 3, 3}]},
      CochainEqualQ[
        Coboundary[Cup[a, b]],
        Cup[Coboundary[a], b] - Cup[a, Coboundary[b]],
        {3, 3, 3}
      ]
    ]
  ),
  True,
  TestID -> "Lattice-Leibniz-numeric"
]

(* ---------------------------------------------------------------------- *)
(* cup_1 is not a derivation of the cup product                           *)
(* ---------------------------------------------------------------------- *)

(* For simplicial cochains (a u b) u_1 c = a u (b u_1 c) +- (a u_1 c) u b
   (the Hirsch formula).  For the cubical cup_1 it fails for every choice of
   signs, on either side.  For 1-cochains in two dimensions the defect is
   -a(x; 2) b(x + e_2; 1) (dc)(x; 12): it vanishes when c is closed.
   Checked in reference/cubical_reference.py, part (6). *)

VerificationTest[
  With[{a = Cochain[1, al], b = Cochain[1, be], c = Cochain[1, ga], x = {x1, x2}},
    {
      AnyTrue[
        Tuples[{1, -1}, 2],
        Function[e,
          CochainEqualQ[
            HigherCup[1][Cup[a, b], c],
            e[[1]] Cup[a, HigherCup[1][b, c]] + e[[2]] Cup[HigherCup[1][a, c], b],
            2
          ]
        ]
      ],
      AnyTrue[
        Tuples[{1, -1}, 2],
        Function[e,
          CochainEqualQ[
            HigherCup[1][a, Cup[b, c]],
            e[[1]] Cup[HigherCup[1][a, b], c] + e[[2]] Cup[b, HigherCup[1][a, c]],
            2
          ]
        ]
      ],
      Expand[
        CochainValue[
          HigherCup[1][Cup[a, b], c] - Cup[a, HigherCup[1][b, c]] - Cup[HigherCup[1][a, c], b],
          x, {1, 2}
        ] +
          al[x, {2}] be[x + {0, 1}, {1}] CochainValue[Coboundary[c], x, {1, 2}]
      ]
    }
  ],
  {False, False, 0},
  TestID -> "Lattice-Hirsch-defect"
]

(* with c exact the Hirsch formula holds, here in three dimensions *)

VerificationTest[
  With[{c = Coboundary[Cochain[0, ph]]},
    Table[
      With[{a = Cochain[pq[[1]], al], b = Cochain[pq[[2]], be]},
        CochainEqualQ[
          HigherCup[1][Cup[a, b], c],
          Cup[a, HigherCup[1][b, c]] + Cup[HigherCup[1][a, c], b],
          3
        ]
      ],
      {pq, {{1, 1}, {1, 2}, {2, 1}}}
    ]
  ],
  {True, True, True},
  TestID -> "Lattice-Hirsch-closed"
]


(* ---------------------------------------------------------------------- *)
(* local multilinear operations                                           *)
(* ---------------------------------------------------------------------- *)

(* a term is {coefficient, rows}: a row has an entry for each direction of the
   cell, 2 = extends, 1 = shifted by one step, 0 = neither.  Here: the cup
   product of two 1-cochains on a plaquette, written as a LocalOperation *)

VerificationTest[
  With[{
      a = Cochain[1, al], b = Cochain[1, be],
      f = Function[n, If[n === 2, {{1, {{2, 0}, {1, 2}}}, {-1, {{0, 2}, {2, 1}}}}, {}]]
    },
    {
      CochainQ[LocalOperation[f, 0][a, b]],
      CochainDegree[LocalOperation[f, 0][a, b]],
      CochainDegree[LocalOperation[f, 1][a, Coboundary[b]]],
      CochainValue[LocalOperation[f, 0][a, b], {x1, x2}, {1, 2}],
      CochainEqualQ[LocalOperation[f, 0][a, b], Cup[a, b], 2],
      CochainEqualQ[Coboundary[LocalOperation[f, 0][a, b]], Coboundary[Cup[a, b]], 3],
      (* terms whose rows do not have the degrees of the arguments do not contribute *)
      CochainValue[LocalOperation[f, 0][Cochain[2, al], Cochain[0, be]], {x1, x2}, {1, 2}]
    }
  ],
  {
    True,
    2,
    2,
    al[{x1, x2}, {1}] be[{1 + x1, x2}, {2}] - al[{x1, x2}, {2}] be[{x1, 1 + x2}, {1}],
    True,
    True,
    0
  },
  TestID -> "Lattice-local-operation"
]

(* ---------------------------------------------------------------------- *)
(* Steenrod squares: Sq^k x = x cup_(p-k) x                               *)
(*   expected values: reference/steenrod_reference.py                     *)
(* ---------------------------------------------------------------------- *)

(* Sq^0 x has the squares of the values of x; outside 0 <= k <= p it is 0 *)

VerificationTest[
  {
    Table[
      With[{x = {x1, x2, x3}, s = Range[p]},
        Expand[CochainValue[SteenrodSquare[0][Cochain[p, al]], x, s] - al[x, s]^2]
      ],
      {p, 0, 3}
    ],
    SteenrodSquare[3][Cochain[2, al]],
    SteenrodSquare[-1][Cochain[2, al]],
    CochainDegree[SteenrodSquare[1][Cochain[2, al]]]
  },
  {{0, 0, 0, 0}, 0, 0, 3},
  TestID -> "Lattice-Steenrod-square-zero"
]

(* d(Sq^k x) = (-1)^(p-k) (1 + (-1)^k) Sq^(k+1) x + dx cup_(p-k) x + (-1)^p x cup_(p-k) dx.
   If dx is even, Sq^k x is a cocycle modulo 2, and for even k the Bockstein
   of Sq^k x is Sq^(k+1) x *)

VerificationTest[
  Table[
    With[{p = pk[[1]], k = pk[[2]]},
      With[{x = Cochain[p, al]},
        CochainEqualQ[
          Coboundary[SteenrodSquare[k][x]],
          (-1)^(p - k) (1 + (-1)^k) SteenrodSquare[k + 1][x] +
            HigherCup[p - k][Coboundary[x], x] + (-1)^p HigherCup[p - k][x, Coboundary[x]],
          p + k + 1
        ]
      ]
    ],
    {pk, {{0, 0}, {1, 0}, {1, 1}, {2, 0}, {2, 1}, {3, 0}}}
  ],
  {True, True, True, True, True, True},
  TestID -> "Lattice-Steenrod-coboundary"
]
