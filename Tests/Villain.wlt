(* Villain: U(1) gauge fields in the modified Villain form and their
   Deligne-Beilinson product.
   The expected values are those of reference/villain_reference.py. *)

(* ---------------------------------------------------------------------- *)
(* fields, curvature, gauge transformations                               *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{aa = VillainField[Cochain[1, fa], Cochain[2, fn]], lam = Cochain[0, fl], m = Cochain[1, fm]},
    {
      VillainDegree[aa],
      VillainConnection[aa],
      VillainFlux[aa],
      VillainConnection[VillainLargeGaugeTransform[aa, m]],
      CochainEqualQ[VillainCurvature[VillainGaugeTransform[aa, lam]], VillainCurvature[aa], 2],
      CochainEqualQ[VillainCurvature[VillainLargeGaugeTransform[aa, m]], VillainCurvature[aa], 2],
      SimplexCochainEqualQ[VillainCurvature[VillainLargeGaugeTransform[aa, m]], VillainCurvature[aa]],
      CochainDegree[VillainConnection[DeligneProduct[aa, aa]]],
      CochainDegree[VillainFlux[DeligneProduct[aa, aa]]]
    }
  ],
  {
    1,
    Cochain[1, fa],
    Cochain[2, fn],
    Cochain[1, fa] + 2 Pi Cochain[1, fm],
    True,
    True,
    True,
    3,
    4
  },
  TestID -> "Villain-field"
]

(* ---------------------------------------------------------------------- *)
(* the Deligne-Beilinson product                                          *)
(*   A = (a, n) of degree p, B = (b, n2) of degree q; each identity is a   *)
(*   pair {left side, right side}                                          *)
(* ---------------------------------------------------------------------- *)

(* the curvature of the product: F_A cup F_B / 2 Pi, up to terms with dn *)

VerificationTest[
  With[{
      curv = Function[{p, q},
        With[{a = Cochain[p, fa], n = Cochain[p + 1, fn], b = Cochain[q, fb], n2 = Cochain[q + 1, fn2]},
          {
            VillainCurvature[DeligneProduct[VillainField[a, n], VillainField[b, n2]]],
            (1 / (2 Pi)) Cup[VillainCurvature[VillainField[a, n]], VillainCurvature[VillainField[b, n2]]] +
              (-1)^p (Cup[Coboundary[n], b] - Cup[a, Coboundary[n2]])
          }
        ]
      ]
    },
    {
      CochainEqualQ[curv[1, 1][[1]], curv[1, 1][[2]], 4],
      Table[SimplexCochainEqualQ[curv[p, q][[1]], curv[p, q][[2]]], {p, 1, 2}, {q, 1, 2}],
      CochainEqualQ[
        curv[1, 1][[1]],
        (1 / (2 Pi)) Cup[VillainCurvature[VillainField[Cochain[1, fa], Cochain[2, fn]]],
          VillainCurvature[VillainField[Cochain[1, fb], Cochain[2, fn2]]]],
        4
      ]
    }
  ],
  {True, {{True, True}, {True, True}}, False},
  TestID -> "Villain-Deligne-product-curvature"
]

(* gauge transformations of A or of B change the product by gauge
   transformations, up to terms with dn: the product of flat fields is
   defined on gauge classes *)

VerificationTest[
  With[{
      ids = Function[{p, q},
        With[{
            a = Cochain[p, fa], n = Cochain[p + 1, fn], b = Cochain[q, fb], n2 = Cochain[q + 1, fn2],
            lam = Cochain[p - 1, fl], mu = Cochain[q - 1, fmu], m = Cochain[p, fm], l = Cochain[q, fl2]
          },
          With[{
              aa = VillainField[a, n], bb = VillainField[b, n2],
              conn = VillainConnection[DeligneProduct[VillainField[a, n], VillainField[b, n2]]],
              flux = VillainFlux[DeligneProduct[VillainField[a, n], VillainField[b, n2]]]
            },
            {
              (* gauge transformation of A *)
              {
                VillainConnection[DeligneProduct[VillainGaugeTransform[aa, lam], bb]],
                conn + (1 / (2 Pi)) Coboundary[Cup[lam, VillainCurvature[bb]]] +
                  (-1)^(p - 1) Cup[lam, Coboundary[n2]]
              },
              (* gauge transformation of B *)
              {
                VillainConnection[DeligneProduct[aa, VillainGaugeTransform[bb, mu]]],
                conn - Coboundary[Cup[n, mu]] + Cup[Coboundary[n], mu]
              },
              (* large gauge transformation of A *)
              {
                VillainConnection[DeligneProduct[VillainLargeGaugeTransform[aa, m], bb]],
                conn - 2 Pi Cup[m, n2] + (-1)^p Coboundary[Cup[m, b]]
              },
              {
                VillainFlux[DeligneProduct[VillainLargeGaugeTransform[aa, m], bb]],
                flux - Coboundary[Cup[m, n2]] + (-1)^p Cup[m, Coboundary[n2]]
              },
              (* large gauge transformation of B *)
              {
                VillainConnection[DeligneProduct[aa, VillainLargeGaugeTransform[bb, l]]],
                conn + 2 Pi (-1)^p Cup[n, l]
              },
              {
                VillainFlux[DeligneProduct[aa, VillainLargeGaugeTransform[bb, l]]],
                flux + (-1)^p (Coboundary[Cup[n, l]] - Cup[Coboundary[n], l])
              }
            }
          ]
        ]
      ]
    },
    {
      (* cubes: all identities for (1, 1); those of degree 4 for (1, 2), (2, 1) *)
      Map[Function[id, CochainEqualQ[id[[1]], id[[2]], CochainDegree[id[[1]]]]], ids[1, 1]],
      Table[
        Map[
          Function[id, CochainEqualQ[id[[1]], id[[2]], 4]],
          Select[ids[pq[[1]], pq[[2]]], Function[id, CochainDegree[id[[1]]] === 4]]
        ],
        {pq, {{1, 2}, {2, 1}}}
      ],
      (* simplices: all identities *)
      Table[
        AllTrue[ids[p, q], Function[id, SimplexCochainEqualQ[id[[1]], id[[2]]]]],
        {p, 1, 2}, {q, 1, 2}
      ]
    }
  ],
  {
    {True, True, True, True, True, True},
    {{True, True, True, True}, {True, True, True, True}},
    {{True, True}, {True, True}}
  },
  TestID -> "Villain-Deligne-product-gauge"
]

(* ---------------------------------------------------------------------- *)
(* actions                                                                *)
(* ---------------------------------------------------------------------- *)

(* BF theory is the product of two fields, Chern-Simons theory half of the
   square with a cup-1 correction: the Lagrangian of arXiv:2303.06160 *)

VerificationTest[
  With[{a = Cochain[1, fa], n = Cochain[2, fn], b = Cochain[1, fb], n2 = Cochain[2, fn2], phi = Cochain[0, fp]},
    {
      CochainEqualQ[
        VillainConnection[DeligneProduct[VillainField[a, n], VillainField[b, n2]]],
        (1 / (2 Pi)) Cup[a, Coboundary[b]] - Cup[a, n2] - Cup[n, b],
        3
      ],
      CochainEqualQ[VillainChernSimons[kk][VillainField[a, n], phi], ModifiedVillainCS[kk][a, n, phi], 3],
      SimplexCochainEqualQ[VillainChernSimons[kk][VillainField[a, n], phi], ModifiedVillainCS[kk][a, n, phi]],
      CochainEqualQ[
        VillainChernSimons[kk][VillainField[a, n], phi],
        (kk / 2) VillainConnection[DeligneProduct[VillainField[a, n], VillainField[a, n]]] +
          Cup[phi, Coboundary[n]],
        3
      ]
    }
  ],
  {True, True, True, False},
  TestID -> "Villain-Chern-Simons"
]

(* ---------------------------------------------------------------------- *)
(* graded commutativity of the product                                    *)
(*   A * B and (-1)^((p+1)(q+1)) B * A differ by the gauge transformation  *)
(*   DeligneSwapGauge[A, B] = {lam, m}, by the gauge invariant term        *)
(*   DeligneSwapDefect[A, B], and by terms with dn, dn2                    *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{
      ids = Function[{p, q},
        With[{a = Cochain[p, fa], n = Cochain[p + 1, fn], b = Cochain[q, fb], n2 = Cochain[q + 1, fn2]},
          With[{
              aa = VillainField[a, n], bb = VillainField[b, n2],
              eps = (-1)^((p + 1) (q + 1)),
              gauge = DeligneSwapGauge[VillainField[a, n], VillainField[b, n2]]
            },
            {
              {
                VillainConnection[DeligneProduct[aa, bb]] - eps VillainConnection[DeligneProduct[bb, aa]],
                Coboundary[gauge[[1]]] + 2 Pi gauge[[2]] + DeligneSwapDefect[aa, bb] +
                  (-1)^q (HigherCup[1][a, Coboundary[n2]] - HigherCup[1][Coboundary[n], b])
              },
              {
                VillainFlux[DeligneProduct[aa, bb]] - eps VillainFlux[DeligneProduct[bb, aa]],
                Coboundary[gauge[[2]]] -
                  (-1)^(p + q) (HigherCup[1][Coboundary[n], n2] - (-1)^p HigherCup[1][n, Coboundary[n2]])
              }
            }
          ]
        ]
      ]
    },
    {
      (* cubes: both identities for (1, 1); that of degree 4 for (1, 2), (2, 1) *)
      Map[Function[id, CochainEqualQ[id[[1]], id[[2]], CochainDegree[id[[1]]]]], ids[1, 1]],
      Table[
        Map[
          Function[id, CochainEqualQ[id[[1]], id[[2]], 4]],
          Select[ids[pq[[1]], pq[[2]]], Function[id, CochainDegree[id[[1]]] === 4]]
        ],
        {pq, {{1, 2}, {2, 1}}}
      ],
      (* simplices: both identities *)
      Table[
        AllTrue[ids[p, q], Function[id, SimplexCochainEqualQ[id[[1]], id[[2]]]]],
        {p, 1, 2}, {q, 1, 2}
      ]
    }
  ],
  {
    {True, True},
    {{True}, {True}},
    {{True, True}, {True, True}}
  },
  TestID -> "Villain-Deligne-product-commutativity"
]

(* the term with F_A cup_1 F_B is needed, and it vanishes if A has no
   curvature: the two BF Lagrangians a db and b da then differ by a gauge
   transformation *)

VerificationTest[
  With[{a = Cochain[1, fa], n = Cochain[2, fn], b = Cochain[1, fb], n2 = Cochain[2, fn2]},
    With[{
        aa = VillainField[a, n], bb = VillainField[b, n2],
        flat = VillainField[Coboundary[Cochain[0, fl]] + 2 Pi Cochain[1, fm], Coboundary[Cochain[1, fm]]],
        gauge = DeligneSwapGauge[VillainField[a, n], VillainField[b, n2]]
      },
      {
        CochainDegree[gauge[[1]]],
        CochainDegree[gauge[[2]]],
        CochainDegree[DeligneSwapDefect[aa, bb]],
        CochainEqualQ[
          VillainConnection[DeligneProduct[aa, bb]] - VillainConnection[DeligneProduct[bb, aa]],
          Coboundary[gauge[[1]]] + 2 Pi gauge[[2]] -
            (HigherCup[1][a, Coboundary[n2]] - HigherCup[1][Coboundary[n], b]),
          3
        ],
        CochainZeroQ[DeligneSwapDefect[aa, bb], 3],
        CochainZeroQ[VillainCurvature[flat], 2],
        CochainZeroQ[DeligneSwapDefect[flat, bb], 3],
        SimplexCochainZeroQ[DeligneSwapDefect[flat, bb]]
      }
    ]
  ],
  {2, 3, 3, False, False, True, True, True},
  TestID -> "Villain-Deligne-swap-defect"
]

(* ---------------------------------------------------------------------- *)
(* the theta term                                                         *)
(* ---------------------------------------------------------------------- *)

(* (theta / 8 Pi^2) F cup F is (theta / 4 Pi) times the curvature of A * A,
   plus the coupling of a to the monopole current dn; the gauge variation
   of that coupling is the one of an electric charge theta / 2 Pi *)

VerificationTest[
  With[{
      ids = Function[p,
        With[{a = Cochain[p, fa], n = Cochain[p + 1, fn], lam = Cochain[p - 1, fl]},
          With[{aa = VillainField[a, n]},
            {
              {
                VillainThetaTerm[th][aa],
                (th / (4 Pi)) VillainCurvature[DeligneProduct[aa, aa]] + VillainWittenTerm[th][aa]
              },
              {
                VillainThetaTerm[th][aa],
                (th / (4 Pi)) Coboundary[VillainConnection[DeligneProduct[aa, aa]]] + (th / 2) Cup[n, n] +
                  VillainWittenTerm[th][aa]
              },
              {
                VillainThetaTerm[th][VillainGaugeTransform[aa, lam]],
                VillainThetaTerm[th][aa]
              },
              {
                VillainWittenTerm[th][VillainGaugeTransform[aa, lam]] - VillainWittenTerm[th][aa],
                -(th / (4 Pi)) Coboundary[Cup[Coboundary[n], lam] - (-1)^p Cup[lam, Coboundary[n]]]
              }
            }
          ]
        ]
      ]
    },
    {
      Map[Function[id, CochainEqualQ[id[[1]], id[[2]], 4]], ids[1]],
      Table[Map[Function[id, SimplexCochainEqualQ[id[[1]], id[[2]]]], ids[p]], {p, 1, 2}],
      CochainZeroQ[VillainWittenTerm[th][VillainField[Cochain[1, fa], Cochain[2, fn]]], 4],
      CochainDegree[VillainThetaTerm[th][VillainField[Cochain[2, fa], Cochain[3, fn]]]]
    }
  ],
  {
    {True, True, True, True},
    {{True, True, True, True}, {True, True, True, True}},
    False,
    6
  },
  TestID -> "Villain-theta-term"
]

(* on the four-torus with the flux z, the topological charge
   (1 / 8 Pi^2) sum of F cup F is the Pfaffian z12 z34 - z13 z24 + z14 z23,
   for any connection a *)

VerificationTest[
  (
    SeedRandom[20261123];
    With[{z = {{0, 1, 2, -1}, {-1, 0, 3, 5}, {-2, -3, 0, 7}, {1, -5, -7, 0}}, dims = {2, 2, 2, 2}},
      With[{
          a = (1 / 3) RandomCochain[1, dims],
          n = THooftFluxCochain[z, dims] + Coboundary[RandomCochain[1, dims]]
        },
        {
          CochainZeroQ[Coboundary[n], dims],
          Expand[CochainIntegrate[VillainThetaTerm[1][VillainField[a, n]], dims]],
          CochainIntegrate[Cup[n, n], dims] / 2,
          Expand[CochainIntegrate[VillainWittenTerm[1][VillainField[a, n]], dims]]
        }
      ]
    ]
  ),
  {True, -6, -6, 0},
  TestID -> "Villain-topological-charge"
]
