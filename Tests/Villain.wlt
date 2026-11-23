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

(* ---------------------------------------------------------------------- *)
(* odd level                                                              *)
(* ---------------------------------------------------------------------- *)

(* in four dimensions the Chern-Simons Lagrangian L is a primitive of the
   theta term at theta = 2 Pi k up to k Pi Q(n):
     dL = (k / 4 Pi) Q(F) - k Pi Q(n) + (k a + d phi) cup dn,   Q(x) = x cup x + x cup_1 dx.
   Q is the Pontryagin square plus 2 x cup_1 dx, and its change under
   n -> n + dm is the coboundary of the anomaly q(m, n), up to 2 m cup dn *)

VerificationTest[
  With[{
      a = Cochain[1, fa], n = Cochain[2, fn], phi = Cochain[0, fp], m = Cochain[1, fm],
      qq = Function[u, Cup[u, u] + HigherCup[1][u, Coboundary[u]]]
    },
    With[{aa = VillainField[a, n], curv = Coboundary[a] - 2 Pi n},
      With[{
          lhs = Coboundary[VillainChernSimons[kk][aa, phi]],
          tail = Cup[kk a + Coboundary[phi], Coboundary[n]],
          rhs = (kk / (4 Pi)) qq[curv] - kk Pi qq[n],
          rhsP = (kk / (4 Pi)) PontryaginSquare[curv] - kk Pi PontryaginSquare[n],
          descent = {
            qq[n + Coboundary[m]] - qq[n],
            Coboundary[ChernSimonsLargeGaugeAnomaly[m, n]] + 2 Cup[m, Coboundary[n]]
          }
        },
        {
          CochainEqualQ[lhs, rhs + tail, 4],
          SimplexCochainEqualQ[lhs, rhs + tail],
          CochainEqualQ[
            (kk / (4 Pi)) qq[curv],
            VillainThetaTerm[2 Pi kk][aa] + (kk / (4 Pi)) HigherCup[1][curv, Coboundary[curv]],
            4
          ],
          CochainEqualQ[lhs, rhsP + tail - kk HigherCup[1][Coboundary[a], Coboundary[n]], 4],
          CochainEqualQ[lhs, rhsP + tail, 4],
          CochainEqualQ[qq[n], PontryaginSquare[n], 4, Modulus -> 2],
          CochainEqualQ[descent[[1]], descent[[2]], 4],
          SimplexCochainEqualQ[descent[[1]], descent[[2]]]
        }
      ]
    ]
  ],
  {True, True, True, True, False, True, True, True},
  TestID -> "Villain-odd-level-inflow"
]

(* in three dimensions: under a large gauge transformation the Lagrangian
   changes by -(k/2) d(m cup a) - k Pi q(m, n).  q is a cocycle of the group
   of the m, and modulo 2 and up to a coboundary it is m cup dm + dm cup_1 n.
   The theory at level k is the theory at level 4k with half-integer fluxes *)

VerificationTest[
  With[{
      a = Cochain[1, fa], n = Cochain[2, fn], phi = Cochain[0, fp],
      m = Cochain[1, fm], m2 = Cochain[1, fm2],
      q = ChernSimonsLargeGaugeAnomaly
    },
    With[{
        aa = VillainField[a, n],
        large = {
          VillainChernSimons[kk][VillainLargeGaugeTransform[VillainField[a, n], m], phi] -
            VillainChernSimons[kk][VillainField[a, n], phi],
          -(kk / 2) Coboundary[Cup[m, a]] - kk Pi q[m, n]
        },
        cocycle = {q[m, n] + q[m2, n + Coboundary[m]] - q[m + m2, n], -Coboundary[Cup[m2, m]]},
        guwen = Cup[m, Coboundary[m]] + HigherCup[1][Coboundary[m], n] +
          Coboundary[Cup[m, m] + HigherCup[1][m, n]],
        even = 2 (Cup[n, m] + HigherCup[1][m, Coboundary[n]] - HigherCup[1][Coboundary[m], n])
      },
      {
        CochainEqualQ[large[[1]], large[[2]], 3],
        SimplexCochainEqualQ[large[[1]], large[[2]]],
        CochainEqualQ[cocycle[[1]], cocycle[[2]], 3],
        SimplexCochainEqualQ[cocycle[[1]], cocycle[[2]]],
        CochainEqualQ[q[m, n], guwen + even, 3],
        SimplexCochainEqualQ[q[m, n], guwen + even],
        CochainEqualQ[q[m, n], guwen, 3, Modulus -> 2],
        CochainZeroQ[q[m, n], 3, Modulus -> 2],
        CochainEqualQ[
          VillainChernSimons[kk][aa, phi],
          VillainChernSimons[4 kk][VillainField[a / 2, n / 2], 2 phi],
          3
        ]
      }
    ]
  ],
  {True, True, True, True, True, True, True, False, True},
  TestID -> "Villain-odd-level-anomaly"
]

(* on a three-torus the sum of the anomaly can be odd, so that exp(i S) is
   not invariant at odd level: m = 1 on two links that meet at a corner is
   the smallest example.  A closed m does not see the anomaly *)

VerificationTest[
  With[{dims = {3, 3, 3}, q = ChernSimonsLargeGaugeAnomaly},
    With[{
        field = Function[{p, f},
          PeriodicCochain[p, dims,
            Association[Map[Function[c, {c[[1]], c[[2]]} -> f[c[[1]], c[[2]]]], LCells[dims, p]]]
          ]
        ]
      },
      With[{
          zero = PeriodicCochain[2, dims, <||>],
          one = PeriodicCochain[1, dims, <|{{0, 0, 0}, {1}} -> 1|>],
          two = PeriodicCochain[1, dims, <|{{0, 0, 0}, {1}} -> 1, {{1, 0, 0}, {2}} -> 1|>],
          m1 = field[1, Function[{y, s}, Mod[y[[1]] + 2 y[[2]] + 3 y[[3]] + s[[1]] (1 + y[[1]] y[[2]] + y[[3]]), 3] - 1]],
          m2 = field[1, Function[{y, s}, Mod[s[[1]] y[[1]] + y[[2]] y[[3]] + 2 s[[1]] y[[3]] + y[[1]] + s[[1]], 2]]],
          mu0 = field[0, Function[{y, s}, Mod[y[[1]] y[[2]] + 2 y[[3]] + y[[2]], 3]]],
          wall = field[1, Function[{y, s}, Boole[s === {3} && y[[3]] === 0]]],
          flux = THooftFluxCochain[{{0, 1, -2}, {-1, 0, 3}, {2, -3, 0}}, dims]
        },
        With[{n1 = flux + Coboundary[m1]},
          {
            CochainZeroQ[Coboundary[n1], dims],
            CochainIntegrate[q[one, zero], dims],
            CochainIntegrate[q[two, zero], dims],
            CochainIntegrate[q[m2, n1], dims],
            CochainZeroQ[Coboundary[Coboundary[mu0] + wall], dims],
            Mod[CochainIntegrate[q[Coboundary[mu0] + wall, n1], dims], 2]
          }
        ]
      ]
    ]
  ],
  {True, 0, 1, 17, True, 0},
  TestID -> "Villain-odd-level-obstruction"
]

(* the signs that cancel the anomaly on a three-torus:
     z(n + dm) = z(n) (-1)^(sum of q(m, n)),
     z(n + n') = z(n) z(n') (-1)^(sum of n cup_1 n').
   The eight choices are labelled by the signs of the three unit fluxes, and
   two of them differ by (-1)^(sum of alpha cup n) with alpha flat.  The
   flux dm of the two links above has the sign -1 for every choice *)

VerificationTest[
  With[{dims = {3, 3, 3}, q = ChernSimonsLargeGaugeAnomaly},
    With[{
        field = Function[{p, f},
          PeriodicCochain[p, dims,
            Association[Map[Function[c, {c[[1]], c[[2]]} -> f[c[[1]], c[[2]]]], LCells[dims, p]]]
          ]
        ],
        unit = Function[c,
          THooftFluxCochain[{{0, c[[1]], c[[2]]}, {-c[[1]], 0, c[[3]]}, {-c[[2]], -c[[3]], 0}}, dims]
        ],
        sg = Function[sig, SpinStructureSign[dims, sig]]
      },
      With[{
          zero = PeriodicCochain[2, dims, <||>],
          one = PeriodicCochain[1, dims, <|{{0, 0, 0}, {1}} -> 1|>],
          two = PeriodicCochain[1, dims, <|{{0, 0, 0}, {1}} -> 1, {{1, 0, 0}, {2}} -> 1|>],
          m1 = field[1, Function[{y, s}, Mod[y[[1]] + 2 y[[2]] + 3 y[[3]] + s[[1]] (1 + y[[1]] y[[2]] + y[[3]]), 3] - 1]],
          m2 = field[1, Function[{y, s}, Mod[s[[1]] y[[1]] + y[[2]] y[[3]] + 2 s[[1]] y[[3]] + y[[1]] + s[[1]], 2]]],
          wall = field[1, Function[{y, s}, Boole[s === {3} && y[[3]] === 0]]],
          flux = THooftFluxCochain[{{0, 1, -2}, {-1, 0, 3}, {2, -3, 0}}, dims]
        },
        With[{n1 = flux + Coboundary[m1], n2 = unit[{1, 1, 0}] + Coboundary[m2]},
          {
            sg[{1, 1, 1}][zero],
            Map[
              Function[c, sg[{-1, 1, -1}][unit[c]]],
              {{1, 0, 0}, {0, 1, 0}, {0, 0, 1}, {1, 1, 0}, {1, 1, 1}}
            ],
            {sg[{1, 1, 1}][Coboundary[two]], sg[{-1, -1, -1}][Coboundary[two]], sg[{1, 1, 1}][Coboundary[one]]},
            Map[
              Function[st,
                sg[st][n1 + Coboundary[m2]] sg[st][n1] === (-1)^CochainIntegrate[q[m2, n1], dims]
              ],
              {{1, 1, 1}, {-1, 1, -1}}
            ],
            Map[
              Function[st,
                sg[st][n1 + n2] sg[st][n1] sg[st][n2] ===
                  (-1)^CochainIntegrate[HigherCup[1][n1, n2], dims]
              ],
              {{1, 1, 1}, {-1, 1, -1}}
            ],
            sg[{1, 1, 1}][n1] sg[{-1, 1, 1}][n1] === (-1)^CochainIntegrate[Cup[wall, n1], dims],
            {sg[{1, 1, 1}][n1], sg[{1, 1, 1}][n2], sg[{1, 1, 1}][n1 + n2], sg[{-1, 1, -1}][n1], sg[{-1, 1, -1}][n2]},
            {CochainIntegrate[HigherCup[1][n1, n2], dims], CochainIntegrate[Cup[wall, n1], dims]},
            sg[{1, 1, 1}][PeriodicCochain[2, dims, <|{{0, 0, 0}, {1, 2}} -> 1|>]]
          }
        ]
      ]
    ]
  ],
  {1, {-1, 1, -1, 1, -1}, {-1, -1, 1}, {True, True}, {True, True}, True, {-1, -1, -1, -1, 1}, {15, 1}, $Failed},
  TestID -> "Villain-spin-structure-sign"
]

(* fluxes in a coordinate plane.  For m along the direction rho and n on the
   plaquettes that contain rho, m cup n + n cup m + dm cup m vanishes, so
   the anomaly q(m, n) reduces to m cup_1 dn, which is zero for closed n:
   planar deformations do not change the sign z *)

VerificationTest[
  With[{
      line = Function[{rho, f}, Cochain[1, Function[{x, s}, If[s === {rho}, f[x, s], 0]]]],
      sheet = Function[{rho, f}, Cochain[2, Function[{x, s}, If[MemberQ[s, rho], f[x, s], 0]]]],
      part = Function[{u, v}, Cup[u, v] + Cup[v, u] + Cup[Coboundary[u], u]]
    },
    {
      Table[CochainZeroQ[part[line[dir, fm], sheet[dir, fn]], 3], {dir, 1, 3}],
      Table[
        CochainEqualQ[
          ChernSimonsLargeGaugeAnomaly[line[dir, fm], sheet[dir, fn]],
          HigherCup[1][line[dir, fm], Coboundary[sheet[dir, fn]]],
          3
        ],
        {dir, 1, 3}
      ],
      CochainZeroQ[part[line[1, fm], Cochain[2, fn]], 3],
      CochainZeroQ[part[Cochain[1, fm], sheet[1, fn]], 3]
    }
  ],
  {{True, True, True}, {True, True, True}, False, False},
  TestID -> "Villain-odd-level-planar"
]

(* on the fluxes in a coordinate plane the sign z depends only on the class
   (wa, wb) of the dual curve in the plane: z = sa^wa sb^wb (-1)^(wa wb).
   It is 1 on contractible curves and minus the holonomy otherwise: the
   quadratic form of a spin structure on the two-torus.  Below: the plane
   x1 = 1 with the classes 0, (line along 3), (line along 2), (both), and
   the plane x3 = 0 with 0, (line along 2), (line along 1), (both) *)

VerificationTest[
  With[{dims = {3, 3, 3}},
    With[{
        field = Function[{p, f},
          PeriodicCochain[p, dims,
            Association[Map[Function[c, {c[[1]], c[[2]]} -> f[c[[1]], c[[2]]]], LCells[dims, p]]]
          ]
        ],
        sg = Function[sig, SpinStructureSign[dims, sig]]
      },
      With[{
          tube = Function[{pl, pos},
            field[2,
              Function[{y, s}, Boole[s === pl && y[[pl[[1]]]] === pos[[1]] && y[[pl[[2]]]] === pos[[2]]]]
            ]
          ],
          mp1 = field[1, Function[{y, s}, If[s === {1} && y[[1]] === 1, Mod[y[[2]] y[[3]] + y[[2]] + 1, 2], 0]]],
          mp3 = field[1, Function[{y, s}, If[s === {3} && y[[3]] === 0, Mod[y[[1]] + y[[1]] y[[2]], 2], 0]]]
        },
        With[{
            plane1 = {
              Coboundary[mp1],
              tube[{1, 2}, {1, 0}] + Coboundary[mp1],
              tube[{1, 3}, {1, 2}] + Coboundary[mp1],
              tube[{1, 2}, {1, 0}] + tube[{1, 3}, {1, 2}] + Coboundary[mp1]
            },
            plane3 = {
              Coboundary[mp3],
              tube[{1, 3}, {2, 0}] + Coboundary[mp3],
              tube[{2, 3}, {1, 0}] + Coboundary[mp3],
              tube[{1, 3}, {2, 0}] + tube[{2, 3}, {1, 0}] + Coboundary[mp3]
            },
            all = {{1, 1, 1}, {-1, 1, 1}, {-1, -1, 1}, {1, -1, -1}}
          },
          {
            Map[Function[st, {Map[sg[st], plane1], Map[sg[st], plane3]}], all],
            Map[SpinStructureHolonomy, all],
            Map[
              Function[st,
                Map[sg[st], plane1] ===
                  {1, -SpinStructureHolonomy[st][[3]], -SpinStructureHolonomy[st][[2]],
                    -SpinStructureHolonomy[st][[3]] SpinStructureHolonomy[st][[2]]}
              ],
              all
            ]
          }
        ]
      ]
    ]
  ],
  {
    {
      {{1, 1, 1, -1}, {1, 1, 1, -1}},
      {{1, -1, 1, 1}, {1, 1, 1, -1}},
      {{1, -1, -1, -1}, {1, -1, 1, 1}},
      {{1, 1, -1, 1}, {1, -1, -1, -1}}
    },
    {{-1, -1, -1}, {-1, -1, 1}, {-1, 1, 1}, {1, 1, -1}},
    {True, True, True, True}
  },
  TestID -> "Villain-spin-structure-planar"
]

(* ---------------------------------------------------------------------- *)
(* the sign as a Grassmann integral                                        *)
(* ---------------------------------------------------------------------- *)

(* the Grassmann integral of the Gu-Wen type on the cubic lattice: -1 on the
   straight flux tubes (for every length), +1 on the boundary of a link, -1
   on the two links that meet at a corner, no value if n is not closed
   modulo 2.  It changes by (-1)^(sum q) under a large gauge transformation
   (here sum q = 17), and with the boundary conditions h = SpinStructureHolonomy[s]
   it is the sign SpinStructureSign[dims, s], for all 8 spin structures *)

VerificationTest[
  With[{dims = {3, 3, 3}},
    With[{
        field = Function[{p, f},
          PeriodicCochain[p, dims,
            Association[Map[Function[c, {c[[1]], c[[2]]} -> f[c[[1]], c[[2]]]], LCells[dims, p]]]
          ]
        ],
        flux = THooftFluxCochain[{{0, 1, -2}, {-1, 0, 3}, {2, -3, 0}}, dims],
        tubes = Function[d,
          Map[
            Function[z, GuWenGrassmannSign[d][THooftFluxCochain[z, d]]],
            {{{0, 1, 0}, {-1, 0, 0}, {0, 0, 0}}, {{0, 0, 1}, {0, 0, 0}, {-1, 0, 0}}, {{0, 0, 0}, {0, 0, 1}, {0, -1, 0}}}
          ]
        ],
        one = PeriodicCochain[1, dims, <|{{0, 0, 0}, {1}} -> 1|>],
        two = PeriodicCochain[1, dims, <|{{0, 0, 0}, {1}} -> 1, {{1, 0, 0}, {2}} -> 1|>]
      },
      With[{
          e0 = field[1, Function[{y, s}, Mod[y[[1]] + 2 y[[2]] + 3 y[[3]] + s[[1]] (1 + y[[1]] y[[2]] + y[[3]]), 3] - 1]],
          m2 = field[1, Function[{y, s}, Mod[s[[1]] y[[1]] + y[[2]] y[[3]] + 2 s[[1]] y[[3]] + y[[1]] + s[[1]], 2]]],
          loop = field[2, Function[{y, s}, CochainValue[Coboundary[two], y, s]]]
        },
        With[{
            n = field[2, Function[{y, s}, CochainValue[flux + Coboundary[e0], y, s]]]
          },
          With[{
              n3 = field[2, Function[{y, s}, CochainValue[n + Coboundary[m2], y, s]]]
            },
            {
              {tubes[{3, 3, 3}], tubes[{4, 4, 4}], tubes[{3, 4, 4}]},
              {GuWenGrassmannSign[dims][Coboundary[one]], GuWenGrassmannSign[dims][loop]},
              GuWenGrassmannSign[dims][PeriodicCochain[2, dims, <|{{0, 0, 0}, {1, 2}} -> 1|>]],
              {
                GuWenGrassmannSign[dims][n], GuWenGrassmannSign[dims][n3],
                CochainIntegrate[ChernSimonsLargeGaugeAnomaly[m2, n], dims]
              },
              Map[
                Function[signs,
                  {
                    GuWenGrassmannSign[dims, SpinStructureHolonomy[signs]][n],
                    GuWenGrassmannSign[dims, SpinStructureHolonomy[signs]][n3]
                  }
                ],
                Tuples[{1, -1}, 3]
              ],
              AllTrue[Tuples[{1, -1}, 3],
                Function[signs,
                  AllTrue[{n, n3, loop},
                    Function[u,
                      GuWenGrassmannSign[dims, SpinStructureHolonomy[signs]][u] === SpinStructureSign[dims, signs][u]
                    ]
                  ]
                ]
              ]
            }
          ]
        ]
      ]
    ]
  ],
  {
    {{-1, -1, -1}, {-1, -1, -1}, {-1, -1, -1}},
    {1, -1},
    $Failed,
    {-1, 1, 17},
    {{-1, 1}, {1, -1}, {-1, 1}, {1, -1}, {1, -1}, {-1, 1}, {1, -1}, {-1, 1}},
    True
  },
  TestID -> "Villain-Gu-Wen-sign"
]

(* ---------------------------------------------------------------------- *)
(* a flat Villain field as a Cech-de Rham cocycle (the form of the lattice *)
(* Deligne-Beilinson cohomology of arXiv:2601.15939)                       *)
(* ---------------------------------------------------------------------- *)

(* the cover of the three-torus by the unit cubes: A_p = a / 2 Pi - m_p with
   d m_p = n on the cube p, A_q - A_p = d Lambda_pq, and
   Lambda_qr - Lambda_pr + Lambda_pq = - N_pqr.  The Chern numbers of the
   Cech cocycle N are the fluxes of n, and the coboundary of A_p is the
   curvature over 2 Pi *)

VerificationTest[
  With[{dims = {3, 3, 3}},
    With[{
        field = Function[{p, f},
          PeriodicCochain[p, dims,
            Association[Map[Function[c, {c[[1]], c[[2]]} -> f[c[[1]], c[[2]]]], LCells[dims, p]]]
          ]
        ],
        flux = THooftFluxCochain[{{0, 1, -2}, {-1, 0, 3}, {2, -3, 0}}, dims]
      },
      With[{
          e0 = field[1, Function[{y, s}, Mod[y[[1]] + 2 y[[2]] + 3 y[[3]] + s[[1]] (1 + y[[1]] y[[2]] + y[[3]]), 3] - 1]],
          a = field[1, Function[{y, s}, Mod[2 y[[1]] + y[[2]] y[[3]] + s[[1]] y[[2]] + s[[1]], 5] - 2]]
        },
        With[{
            n = field[2, Function[{y, s}, CochainValue[flux + Coboundary[e0], y, s]]]
          },
          With[{
              aa = VillainField[a, n],
              m = VillainPatchPrimitive[n, dims]
            },
            With[{
                conn = CechDeRhamConnection[aa, dims],
                lam = CechDeRhamTransition[aa, dims],
                nn = CechDeRhamChern[aa, dims]
              },
              {
                CechDeRhamCocycleQ[aa, dims],
                CechDeRhamChernNumbers[aa, dims],
                THooftFlux[n, dims],
                CechDeRhamChernNumbers[VillainLargeGaugeTransform[aa, e0], dims],
                {m[{0, 0, 0}, {1, 0, 0}, 2], m[{0, 0, 0}, {1, 1, 0}, 3], m[{2, 2, 2}, {0, 0, 2}, 3]},
                {lam[{0, 0, 0}, {1, 0, 0}, {1, 1, 0}], lam[{0, 0, 0}, {0, 1, 0}, {1, 1, 1}]},
                {nn[{0, 0, 0}, {1, 0, 0}, {1, 1, 0}], nn[{2, 2, 2}, {0, 2, 2}, {0, 0, 2}],
                  nn[{0, 0, 0}, {0, 1, 0}, {1, 1, 0}]},
                AllTrue[{{1, 2, 3}, {1, 3, 2}, {2, 3, 1}},
                  Function[pl,
                    AllTrue[{0, 1},
                      Function[t,
                        With[{
                            p = {2, 1, 0}, mu = pl[[1]], nu = pl[[2]],
                            x = Mod[{2, 1, 0} + t UnitVector[3, pl[[3]]], dims]
                          },
                          Expand[
                              conn[p, Mod[x + UnitVector[3, mu], dims], nu] - conn[p, x, nu] -
                                conn[p, Mod[x + UnitVector[3, nu], dims], mu] + conn[p, x, mu]
                            ] ===
                            Expand[CochainValue[VillainCurvature[aa], x, {mu, nu}] / (2 Pi)]
                        ]
                      ]
                    ]
                  ]
                ],
                {m[{0, 0, 0}, {2, 0, 0}, 2], lam[{0, 0, 0}, {1, 0, 0}, {0, 0, 0}],
                  nn[{0, 0, 0}, {1, 0, 0}, {2, 0, 0}]}
              }
            ]
          ]
        ]
      ]
    ]
  ],
  {
    {True, True, True},
    {{0, 1, -2}, {-1, 0, 3}, {2, -3, 0}},
    {{0, 1, -2}, {-1, 0, 3}, {2, -3, 0}},
    {{0, 1, -2}, {-1, 0, 3}, {2, -3, 0}},
    {-1, 0, 4},
    {-1, 3},
    {1, 1, 0},
    True,
    {$Failed, $Failed, $Failed}
  },
  TestID -> "Villain-Cech-de-Rham-cocycle"
]

(* ---------------------------------------------------------------------- *)
(* the star product and its integral on the Cech-de Rham cocycle           *)
(* ---------------------------------------------------------------------- *)

(* the chain of the integral: 1 + 3 + 6 + 6 terms for every site, the last
   cube of a term is the cube based at the base point of its cell *)

VerificationTest[
  With[{dims = {3, 3, 3}},
    With[{cyc = CechDeRhamFundamentalCycle[dims]},
      {
        Map[Function[key, Length[Lookup[cyc, key]]], {3, 2, 1, 0}],
        Union[Flatten[Map[Function[key, Map[First, Lookup[cyc, key]]], {3, 2, 1, 0}]]],
        AllTrue[{3, 2, 1, 0},
          Function[key,
            AllTrue[Lookup[cyc, key],
              Function[term,
                Length[term[[3]]] === key && Length[term[[4]]] === 4 - key && Last[term[[4]]] === term[[2]] &&
                  DuplicateFreeQ[term[[4]]]
              ]
            ]
          ]
        ],
        Select[Lookup[cyc, 2], Function[term, term[[2]] === {1, 1, 1}]],
        Select[Lookup[cyc, 1], Function[term, term[[2]] === {1, 1, 1}]],
        Select[Lookup[cyc, 0], Function[term, term[[2]] === {1, 1, 1}]]
      }
    ]
  ],
  {
    {27, 81, 162, 162},
    {-1, 1},
    True,
    {
      {1, {1, 1, 1}, {2, 3}, {{0, 1, 1}, {1, 1, 1}}},
      {-1, {1, 1, 1}, {1, 3}, {{1, 0, 1}, {1, 1, 1}}},
      {1, {1, 1, 1}, {1, 2}, {{1, 1, 0}, {1, 1, 1}}}
    },
    {
      {1, {1, 1, 1}, {1}, {{1, 0, 0}, {1, 1, 0}, {1, 1, 1}}},
      {-1, {1, 1, 1}, {1}, {{1, 0, 0}, {1, 0, 1}, {1, 1, 1}}},
      {-1, {1, 1, 1}, {2}, {{0, 1, 0}, {1, 1, 0}, {1, 1, 1}}},
      {1, {1, 1, 1}, {2}, {{0, 1, 0}, {0, 1, 1}, {1, 1, 1}}},
      {1, {1, 1, 1}, {3}, {{0, 0, 1}, {1, 0, 1}, {1, 1, 1}}},
      {-1, {1, 1, 1}, {3}, {{0, 0, 1}, {0, 1, 1}, {1, 1, 1}}}
    },
    {
      {1, {1, 1, 1}, {}, {{0, 0, 0}, {0, 1, 0}, {0, 1, 1}, {1, 1, 1}}},
      {-1, {1, 1, 1}, {}, {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 1}}},
      {-1, {1, 1, 1}, {}, {{0, 0, 0}, {1, 0, 0}, {1, 0, 1}, {1, 1, 1}}},
      {1, {1, 1, 1}, {}, {{0, 0, 0}, {0, 0, 1}, {1, 0, 1}, {1, 1, 1}}},
      {1, {1, 1, 1}, {}, {{0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {1, 1, 1}}},
      {-1, {1, 1, 1}, {}, {{0, 0, 0}, {0, 1, 0}, {1, 1, 0}, {1, 1, 1}}}
    }
  },
  TestID -> "Villain-Cech-de-Rham-cycle"
]

(* for the cocycles of two flat Villain fields the four contributions are
   the sum of a cup F_B / (2 Pi)^2, 0, minus the sum of n cup b / (2 Pi), 0:
   the integral of the star product is the sum of the connection of
   DeligneProduct over 2 Pi, and for the square it is the sum of the
   Chern-Simons Lagrangian at level 2 over 2 Pi.  The two orders differ by
   cup_1 terms *)

VerificationTest[
  With[{dims = {3, 3, 3}},
    With[{
        field = Function[{p, f},
          PeriodicCochain[p, dims,
            Association[Map[Function[c, {c[[1]], c[[2]]} -> f[c[[1]], c[[2]]]], LCells[dims, p]]]
          ]
        ],
        flux = THooftFluxCochain[{{0, 1, -2}, {-1, 0, 3}, {2, -3, 0}}, dims],
        n2 = THooftFluxCochain[{{0, 2, 0}, {-2, 0, -1}, {0, 1, 0}}, dims]
      },
      With[{
          e0 = field[1, Function[{y, s}, Mod[y[[1]] + 2 y[[2]] + 3 y[[3]] + s[[1]] (1 + y[[1]] y[[2]] + y[[3]]), 3] - 1]],
          a = field[1, Function[{y, s}, Mod[2 y[[1]] + y[[2]] y[[3]] + s[[1]] y[[2]] + s[[1]], 5] - 2]],
          b = field[1, Function[{y, s}, Mod[y[[1]] y[[2]] + 2 y[[3]] + s[[1]] (y[[1]] + 1), 5] - 2]]
        },
        With[{
            n = field[2, Function[{y, s}, CochainValue[flux + Coboundary[e0], y, s]]]
          },
          With[{aa = VillainField[a, n], bb = VillainField[b, n2]},
            With[{
                self = CechDeRhamStarIntegral[aa, aa, dims],
                pair = CechDeRhamStarIntegral[aa, bb, dims],
                swap = CechDeRhamStarIntegral[bb, aa, dims]
              },
              {
                Expand[self - {20 / (2 Pi) + 20 / (2 Pi)^2, 0, 3 / (2 Pi), 0}],
                Expand[pair - {3 / (2 Pi) + 33 / (2 Pi)^2, 0, 10 / (2 Pi), 0}],
                Expand[swap - {10 / (2 Pi) - 33 / (2 Pi)^2, 0, -8 / (2 Pi), 0}],
                Expand[
                  pair - {
                      CochainIntegrate[Cup[a, VillainCurvature[bb]], dims] / (2 Pi)^2, 0,
                      -CochainIntegrate[Cup[n, b], dims] / (2 Pi), 0
                    }
                ],
                Expand[Total[pair] - CochainIntegrate[VillainConnection[DeligneProduct[aa, bb]], dims] / (2 Pi)],
                Expand[
                  Total[self] -
                    CochainIntegrate[VillainChernSimons[2][aa, PeriodicCochain[0, dims, <||>]], dims] / (2 Pi)
                ],
                Expand[
                  Total[pair] - Total[swap] +
                    CochainIntegrate[HigherCup[1][VillainCurvature[aa], VillainCurvature[bb]], dims] / (2 Pi)^2
                ],
                CochainIntegrate[HigherCup[1][n, n2], dims]
              }
            ]
          ]
        ]
      ]
    ]
  ],
  {{0, 0, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}, 0, 0, 1, 1},
  TestID -> "Villain-Cech-de-Rham-star"
]

(* the integral is defined modulo 1: a gauge transformation of the cocycle
   with xi alone moves the value between the four contributions and leaves
   the total; with mm the total changes by an integer.  The large gauge
   transformation of the Villain field changes the integral of the square
   by minus the sum of q(m, n), here the odd number 17: half of the
   integral is not defined modulo 1 *)

VerificationTest[
  With[{dims = {3, 3, 3}},
    With[{
        field = Function[{p, f},
          PeriodicCochain[p, dims,
            Association[Map[Function[c, {c[[1]], c[[2]]} -> f[c[[1]], c[[2]]]], LCells[dims, p]]]
          ]
        ],
        flux = THooftFluxCochain[{{0, 1, -2}, {-1, 0, 3}, {2, -3, 0}}, dims],
        n2 = THooftFluxCochain[{{0, 2, 0}, {-2, 0, -1}, {0, 1, 0}}, dims],
        xi = Function[{p, x},
          With[{r = Mod[x - p, dims]},
            (Mod[2 p[[1]] + p[[2]] p[[3]] + 3 r[[1]] + r[[2]] (1 + p[[3]]) + 2 r[[3]] p[[1]], 7] - 3) / 5
          ]
        ],
        mm = Function[{p, q},
          With[{
              w = Mod[q - p, dims, -1] . {1, 2, 4},
              g = Function[c, Mod[c[[1]] + 2 c[[2]] c[[3]] + c[[3]] + c[[1]] c[[2]], 3]]
            },
            If[w === 0, 0, Sign[w] (Mod[g[p] + g[q] + Abs[w], 3] - 1)]
          ]
        ],
        none = Function[{p, q}, 0]
      },
      With[{
          e0 = field[1, Function[{y, s}, Mod[y[[1]] + 2 y[[2]] + 3 y[[3]] + s[[1]] (1 + y[[1]] y[[2]] + y[[3]]), 3] - 1]],
          m2 = field[1, Function[{y, s}, Mod[s[[1]] y[[1]] + y[[2]] y[[3]] + 2 s[[1]] y[[3]] + y[[1]] + s[[1]], 2]]],
          a = field[1, Function[{y, s}, Mod[2 y[[1]] + y[[2]] y[[3]] + s[[1]] y[[2]] + s[[1]], 5] - 2]],
          b = field[1, Function[{y, s}, Mod[y[[1]] y[[2]] + 2 y[[3]] + s[[1]] (y[[1]] + 1), 5] - 2]]
        },
        With[{
            n = field[2, Function[{y, s}, CochainValue[flux + Coboundary[e0], y, s]]]
          },
          With[{
              aa = VillainField[a, n],
              big = VillainField[
                field[1, Function[{y, s}, CochainValue[a + 2 Pi m2, y, s]]],
                field[2, Function[{y, s}, CochainValue[n + Coboundary[m2], y, s]]]
              ]
            },
            With[{
                t1 = CechDeRhamTriple[aa, dims],
                t2 = CechDeRhamTriple[VillainField[b, n2], dims]
              },
              With[{
                  x1 = CechDeRhamGaugeTransform[t1, xi, none, dims],
                  g1 = CechDeRhamGaugeTransform[t1, xi, mm, dims],
                  g2 = CechDeRhamGaugeTransform[t2, xi, mm, dims]
                },
                With[{
                    s11 = CechDeRhamStarIntegral[t1, t1, dims],
                    s12 = CechDeRhamStarIntegral[t1, t2, dims],
                    sxx = CechDeRhamStarIntegral[x1, x1, dims],
                    sgg = CechDeRhamStarIntegral[g1, g1, dims],
                    sg2 = CechDeRhamStarIntegral[g1, t2, dims],
                    s1g = CechDeRhamStarIntegral[t1, g2, dims]
                  },
                  {
                    Expand[
                      sxx - {46 / 5 + (234 / 5) / (2 Pi) + 20 / (2 Pi)^2, -46 / 5 - (134 / 5) / (2 Pi),
                          16 / 5 + 3 / (2 Pi), -16 / 5}
                    ],
                    Expand[
                      sgg - {46 / 5 + (234 / 5) / (2 Pi) + 20 / (2 Pi)^2, -91 / 5 - (109 / 5) / (2 Pi),
                          -2 / (2 Pi), 15}
                    ],
                    Expand[
                      sg2 - {-1 / 5 - (8 / 5) / (2 Pi) + 33 / (2 Pi)^2, 16 / 5 + (28 / 5) / (2 Pi), 9 / (2 Pi), 0}
                    ],
                    Expand[s1g - {3 / (2 Pi) + 33 / (2 Pi)^2, 0, 16 / 5 + 10 / (2 Pi), 59 / 5}],
                    Expand[{Total[sxx], Total[sgg]} - Total[s11]],
                    Expand[{Total[sg2], Total[s1g]} - Total[s12]],
                    Expand[Total[CechDeRhamStarIntegral[big, big, dims]] - Total[s11]],
                    CochainIntegrate[ChernSimonsLargeGaugeAnomaly[m2, n], dims]
                  }
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ],
  {{0, 0, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}, {0, 6}, {3, 15}, -17, 17},
  TestID -> "Villain-Cech-de-Rham-star-gauge"
]

(* ---------------------------------------------------------------------- *)
(* background fields of the 1-form symmetry                               *)
(* ---------------------------------------------------------------------- *)

(* the level k is the level k N^2 with fluxes in Z / N.  With the flux
   n + b / N the inflow term k Pi Q(n) becomes
   k Pi (Q(n) + X(n, b) / N + Q(b) / N^2); the cross term X is, for closed n
   and db a multiple of N, a coboundary plus N times an even cochain *)

VerificationTest[
  With[{
      a = Cochain[1, fa], n = Cochain[2, fn], phi = Cochain[0, fp], b = Cochain[2, fb],
      qq = Function[u, Cup[u, u] + HigherCup[1][u, Coboundary[u]]]
    },
    With[{
        cross = Cup[n, b] + Cup[b, n] + HigherCup[1][n, Coboundary[b]] + HigherCup[1][b, Coboundary[n]],
        shifted = n + b / 3
      },
      With[{
          lhs = Coboundary[VillainChernSimons[kk][VillainField[a, shifted], phi]],
          rhs = (kk / (4 Pi)) qq[Coboundary[a] - 2 Pi shifted] -
            kk Pi (qq[n] + cross / 3 + qq[b] / 9) +
            Cup[kk a + Coboundary[phi], Coboundary[shifted]]
        },
        {
          Table[
            CochainEqualQ[
              VillainChernSimons[kk][VillainField[a, n], phi],
              VillainChernSimons[kk num^2][VillainField[a / num, n / num], num phi],
              3
            ],
            {num, {2, 3}}
          ],
          CochainEqualQ[qq[shifted], qq[n] + cross / 3 + qq[b] / 9, 4],
          CochainEqualQ[
            cross,
            2 Cup[b, n] - Coboundary[HigherCup[1][n, b]] + HigherCup[1][Coboundary[n], b] +
              2 HigherCup[1][n, Coboundary[b]] + HigherCup[1][b, Coboundary[n]],
            4
          ],
          SimplexCochainEqualQ[
            cross,
            2 Cup[b, n] - Coboundary[HigherCup[1][n, b]] + HigherCup[1][Coboundary[n], b] +
              2 HigherCup[1][n, Coboundary[b]] + HigherCup[1][b, Coboundary[n]]
          ],
          CochainEqualQ[lhs, rhs, 4],
          SimplexCochainEqualQ[lhs, rhs]
        }
      ]
    ]
  ],
  {{True, True}, True, True, True, True, True},
  TestID -> "Villain-background-field"
]
