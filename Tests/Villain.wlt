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
