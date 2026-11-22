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

(* ---------------------------------------------------------------------- *)
(* differential cochains                                                  *)
(*   x = (c, h, w) of degree k: an integer k-cochain, a real (k-1)-cochain *)
(*   and a real k-cochain; identities are pairs of lists of components     *)
(* ---------------------------------------------------------------------- *)

(* d d = 0, the Leibniz rule and associativity, for generic components *)

VerificationTest[
  With[{
      gen = Function[{deg, uc, uh, uw},
        DifferentialCochain[Cochain[deg, uc], Cochain[deg - 1, uh], Cochain[deg, uw]]],
      comps = DifferentialComponents
    },
    With[{
        leibniz = Function[{k1, k2},
          With[{x = gen[k1, fc1, fh1, fw1], y = gen[k2, fc2, fh2, fw2]},
            {
              comps[DifferentialCoboundary[DifferentialProduct[x, y]]],
              comps[DifferentialProduct[DifferentialCoboundary[x], y]] +
                (-1)^k1 comps[DifferentialProduct[x, DifferentialCoboundary[y]]]
            }
          ]
        ],
        assoc = Function[{k1, k2, k3},
          With[{x = gen[k1, fc1, fh1, fw1], y = gen[k2, fc2, fh2, fw2], z = gen[k3, fc3, fh3, fw3]},
            {
              comps[DifferentialProduct[DifferentialProduct[x, y], z]],
              comps[DifferentialProduct[x, DifferentialProduct[y, z]]]
            }
          ]
        ],
        ddx = comps[DifferentialCoboundary[DifferentialCoboundary[gen[2, fc1, fh1, fw1]]]]
      },
      {
        DifferentialDegree[gen[2, fc1, fh1, fw1]],
        AllTrue[ddx, Function[u, CochainZeroQ[u, 4]]],
        AllTrue[ddx, SimplexCochainZeroQ],
        Table[
          DifferentialCochainEqualQ[leibniz[pr[[1]], pr[[2]]][[1]], leibniz[pr[[1]], pr[[2]]][[2]], pr[[1]] + pr[[2]] + 1],
          {pr, {{1, 1}, {1, 2}, {2, 1}, {2, 2}}}
        ],
        Table[And @@ MapThread[SimplexCochainEqualQ, leibniz[i1, i2]], {i1, 2, 3}, {i2, 2, 3}],
        DifferentialCochainEqualQ[assoc[1, 1, 1][[1]], assoc[1, 1, 1][[2]], 3],
        Table[And @@ MapThread[SimplexCochainEqualQ, assoc[2, i2, 2]], {i2, 2, 3}]
      }
    ]
  ],
  {2, True, True, {True, True, True, True}, {{True, True}, {True, True}}, True, {True, True}},
  TestID -> "Villain-differential-cochains"
]

(* Villain fields are differential cochains: the definition of the
   curvature is the vanishing of the middle component of the coboundary,
   gauge transformations add coboundaries, and the Deligne-Beilinson
   product is the product of differential cochains *)

VerificationTest[
  With[{
      a = Cochain[1, fa], n = Cochain[2, fn], b = Cochain[1, fb], n2 = Cochain[2, fn2],
      lam = Cochain[0, fl], m = Cochain[1, fm], comps = DifferentialComponents
    },
    With[{
        aa = VillainField[a, n], bb = VillainField[b, n2],
        ta = VillainDifferentialCochain[VillainField[a, n]],
        tb = VillainDifferentialCochain[VillainField[b, n2]],
        xi = DifferentialCochain[-m, -(1 / (2 Pi)) lam, Cochain[1, Function[{pt, dirs}, 0]]]
      },
      With[{
          prod = comps[DifferentialProduct[ta, tb]],
          dprod = comps[DifferentialCoboundary[DifferentialProduct[ta, tb]]],
          tprod = comps[VillainDifferentialCochain[DeligneProduct[aa, bb]]]
        },
        {
          DifferentialDegree[ta],
          (* the coboundary of a Villain field is (-dn, 0, -dn) *)
          DifferentialCochainEqualQ[
            DifferentialCoboundary[ta],
            {-Coboundary[n], Cochain[2, Function[{pt, dirs}, 0]], -Coboundary[n]},
            3
          ],
          (* gauge and large gauge transformations add the coboundary of (-m, -lam / 2 Pi, 0) *)
          DifferentialCochainEqualQ[
            VillainDifferentialCochain[VillainLargeGaugeTransform[VillainGaugeTransform[aa, lam], m]],
            comps[ta] + comps[DifferentialCoboundary[xi]],
            2
          ],
          (* the product: the first two components agree *)
          CochainEqualQ[prod[[1]], tprod[[1]], 4],
          CochainEqualQ[prod[[2]], tprod[[2]], 3],
          SimplexCochainEqualQ[prod[[1]], tprod[[1]]],
          SimplexCochainEqualQ[prod[[2]], tprod[[2]]],
          (* the third components differ by the middle component of the coboundary of the product *)
          CochainEqualQ[tprod[[3]], prod[[3]] - dprod[[2]], 4],
          CochainEqualQ[tprod[[3]], prod[[3]], 4]
        }
      ]
    ]
  ],
  {2, True, True, True, True, True, True, True, False},
  TestID -> "Villain-fields-as-differential-cochains"
]

(* the product is graded commutative up to the homotopy H; on Villain
   fields H is the gauge transformation and the defect of DeligneSwapGauge *)

VerificationTest[
  With[{
      gen = Function[{deg, uc, uh, uw},
        DifferentialCochain[Cochain[deg, uc], Cochain[deg - 1, uh], Cochain[deg, uw]]],
      comps = DifferentialComponents
    },
    With[{
        swap = Function[{k1, k2},
          With[{x = gen[k1, fc1, fh1, fw1], y = gen[k2, fc2, fh2, fw2]},
            {
              comps[DifferentialProduct[x, y]] - (-1)^(k1 k2) comps[DifferentialProduct[y, x]],
              comps[DifferentialCoboundary[DifferentialSwapHomotopy[x, y]]] +
                comps[DifferentialSwapHomotopy[DifferentialCoboundary[x], y]] +
                (-1)^k1 comps[DifferentialSwapHomotopy[x, DifferentialCoboundary[y]]]
            }
          ]
        ],
        aa = VillainField[Cochain[1, fa], Cochain[2, fn]],
        bb = VillainField[Cochain[1, fb], Cochain[2, fn2]]
      },
      {
        DifferentialCochainEqualQ[swap[2, 2][[1]], swap[2, 2][[2]], 4],
        Table[And @@ MapThread[SimplexCochainEqualQ, swap[i1, i2]], {i1, 2, 3}, {i2, 2, 3}],
        DifferentialCochainEqualQ[
          DifferentialSwapHomotopy[VillainDifferentialCochain[aa], VillainDifferentialCochain[bb]],
          {
            -DeligneSwapGauge[aa, bb][[2]],
            -(1 / (2 Pi)) DeligneSwapGauge[aa, bb][[1]],
            (1 / (2 Pi)) DeligneSwapDefect[aa, bb]
          },
          3
        ]
      }
    ]
  ],
  {True, {{True, True}, {True, True}}, True},
  TestID -> "Villain-differential-swap-homotopy"
]

(* ---------------------------------------------------------------------- *)
(* towards the quantum theory                                             *)
(* ---------------------------------------------------------------------- *)

(* zero modes of sum of a cup da on three-tori, beyond the closed
   1-cochains: two for each momentum with p1 + p2 + p3 = Pi (the staggered
   modes), none if all sides are odd *)

VerificationTest[
  {
    Map[ChernSimonsZeroModeCount, {{2, 2, 2}, {3, 3, 3}, {2, 3, 3}, {2, 2, 3}, {2, 3, 4}}],
    Map[StaggeredMomentumCount, {{2, 2, 2}, {3, 3, 3}, {2, 3, 3}, {2, 2, 3}, {2, 3, 4}, {4, 4, 4}, {3, 4, 5}, {6, 4, 2}}],
    Map[StaggeredMomentumCount, {{4, 6}, {3, 5}, {2, 2}}]
  },
  {{8, 0, 6, 4, 4}, {4, 0, 3, 2, 2, 16, 1, 4}, {2, 0, 2}},
  TestID -> "Villain-Chern-Simons-zero-modes"
]

(* large gauge transformations: the boundary term B(m; a) = -(k/2) m cup a
   of the variation composes up to k Pi m cup m2; the symmetric part of
   m cup m2 is a cup-1 expression, the obstruction at odd level *)

VerificationTest[
  With[{
      a = Cochain[1, fa], m = Cochain[1, fm], m2 = Cochain[1, fm2],
      bt = Function[{u, v}, -(kk / 2) Cup[u, v]]
    },
    With[{
        lhs = bt[m + m2, a] - bt[m, a + 2 Pi m2] - bt[m2, a],
        sym = Cup[m, m2] + Cup[m2, m],
        cup1 = -Coboundary[HigherCup[1][m, m2]] + HigherCup[1][Coboundary[m], m2] -
          HigherCup[1][m, Coboundary[m2]]
      },
      {
        CochainEqualQ[lhs, kk Pi Cup[m, m2], 2],
        SimplexCochainEqualQ[lhs, kk Pi Cup[m, m2]],
        CochainEqualQ[sym, cup1, 2],
        SimplexCochainEqualQ[sym, cup1],
        CochainZeroQ[sym, 2]
      }
    ]
  ],
  {True, True, True, True, False},
  TestID -> "Villain-large-gauge-algebra"
]
