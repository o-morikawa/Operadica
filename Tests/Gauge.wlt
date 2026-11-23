(* Gauge: lattice gauge theory with cochains.
   The identities are those of reference/gauge_reference.py. *)

(* ---------------------------------------------------------------------- *)
(* multilinear expansion                                                  *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{a = Cochain[1, fa], b = Cochain[1, fb], c = Cochain[2, fc]},
    {
      CochainExpand[Cup[a + b, c]] === Cup[a, c] + Cup[b, c],
      CochainExpand[Coboundary[2 a - 3 b]] === 2 Coboundary[a] - 3 Coboundary[b],
      CochainExpand[Coboundary[Coboundary[a]]],
      CochainExpand[Cup[a, Coboundary[Coboundary[c]]] + Cup[a, c] - Cup[a, c]],
      CochainExpand[HigherCup[1][kk a, c + Coboundary[b]]] ===
        kk HigherCup[1][a, c] + kk HigherCup[1][a, Coboundary[b]],
      CochainExpand[(1 + kk) Cup[a, c] - kk Cup[a, c] - Cup[a, c]]
    }
  ],
  {True, True, 0, 0, True, 0},
  TestID -> "Gauge-expand-rules"
]

VerificationTest[
  With[{b = Cochain[2, fb], lam = Cochain[1, fl]},
    CochainExpand[PontryaginSquare[b + Coboundary[lam]] - PontryaginSquare[b]] ===
      Cup[b, Coboundary[lam]] + Cup[Coboundary[lam], b] + Cup[Coboundary[lam], Coboundary[lam]] -
        HigherCup[1][Coboundary[lam], Coboundary[b]]
  ],
  True,
  TestID -> "Gauge-expand-Pontryagin"
]

(* the expansion is the same cochain *)

VerificationTest[
  With[{a = Cochain[1, fa], b = Cochain[2, fb], c = Cochain[1, fc]},
    With[{expr = Cup[a + 2 Coboundary[Cochain[0, fz]], b - Cup[a, c]] +
        HigherCup[1][b + Coboundary[a], Coboundary[a] + 3 Cup[a, c]]},
      CochainEqualQ[CochainExpand[expr], expr, 3]
    ]
  ],
  True,
  TestID -> "Gauge-expand-consistent"
]

(* ---------------------------------------------------------------------- *)
(* gauge variations                                                       *)
(* ---------------------------------------------------------------------- *)

(* BF theory, a u db: invariant under a -> a + d lambda up to a total derivative,
   and exactly invariant under b -> b + d mu *)

VerificationTest[
  With[{a = Cochain[1, fa], b = Cochain[1, fb], lam = Cochain[0, fl], mu = Cochain[0, fm]},
    {
      TotalDerivativeQ[
        GaugeVariation[Cup[a, Coboundary[b]], a -> a + Coboundary[lam]],
        Cup[lam, Coboundary[b]],
        3
      ],
      GaugeVariation[Cup[a, Coboundary[b]], b -> b + Coboundary[mu]]
    }
  ],
  {True, 0},
  TestID -> "Gauge-BF"
]

(* a u da and da u a differ by the cup-1 product *)

VerificationTest[
  With[{a = Cochain[1, fa]},
    CochainEqualQ[
      Cup[a, Coboundary[a]] - Cup[Coboundary[a], a],
      Coboundary[HigherCup[1][a, Coboundary[a]]] - HigherCup[1][Coboundary[a], Coboundary[a]],
      3
    ]
  ],
  True,
  TestID -> "Gauge-CS-commutator"
]

(* Pontryagin square under a 1-form gauge transformation:
     P(B + dl) - P(B) = d[ 2 l u B + l u dl - B u_1 dl ] + 2 l u dB + dB u_1 dl - dl u_1 dB *)

VerificationTest[
  With[{b = Cochain[2, fb], lam = Cochain[1, fl]},
    CochainEqualQ[
      PontryaginSquare[b + Coboundary[lam]] - PontryaginSquare[b],
      Coboundary[2 Cup[lam, b] + Cup[lam, Coboundary[lam]] - HigherCup[1][b, Coboundary[lam]]] +
        2 Cup[lam, Coboundary[b]] +
        HigherCup[1][Coboundary[b], Coboundary[lam]] -
        HigherCup[1][Coboundary[lam], Coboundary[b]],
      4
    ]
  ],
  True,
  TestID -> "Gauge-Pontryagin-1form-shift"
]

(* Pontryagin square under a shift by nn times an integer cochain c:
     P(B + nn c) - P(B) = 2 nn c u B + nn^2 (c u c - c u_1 dc)
                          - nn d(B u_1 c) + nn (dB u_1 c - c u_1 dB)
   so P(B) modulo 2 nn is well defined on flat Z_nn fields when nn is even *)

VerificationTest[
  With[{b = Cochain[2, fb], c = Cochain[2, fc]},
    CochainEqualQ[
      PontryaginSquare[b + nn c] - PontryaginSquare[b],
      2 nn Cup[c, b] + nn^2 (Cup[c, c] - HigherCup[1][c, Coboundary[c]]) -
        nn Coboundary[HigherCup[1][b, c]] +
        nn (HigherCup[1][Coboundary[b], c] - HigherCup[1][c, Coboundary[b]]),
      4
    ]
  ],
  True,
  TestID -> "Gauge-Pontryagin-lift-shift"
]

(* ---------------------------------------------------------------------- *)
(* modified Villain Chern-Simons theory, arXiv:2303.06160 eq. (17)         *)
(* ---------------------------------------------------------------------- *)

(* 0-form gauge transformation a -> a + d lambda, phi -> phi - k lambda:
   the Lagrangian changes by a total derivative, for every n *)

VerificationTest[
  With[{a = Cochain[1, fa], n = Cochain[2, fn], phi = Cochain[0, fp], lam = Cochain[0, fl]},
    TotalDerivativeQ[
      ModifiedVillainCS[kk][a + Coboundary[lam], n, phi - kk lam] - ModifiedVillainCS[kk][a, n, phi],
      (kk / (4 Pi)) Cup[lam, Coboundary[a]] - kk Cup[lam, n] + (kk / 2) HigherCup[1][Coboundary[lam], n],
      3
    ]
  ],
  True,
  TestID -> "Gauge-Villain-CS-0form"
]

(* without the cup-1 term this fails *)

VerificationTest[
  With[{a = Cochain[1, fa], n = Cochain[2, fn], phi = Cochain[0, fp], lam = Cochain[0, fl]},
    With[{bad = Function[{x, y, z},
        (kk / (4 Pi)) (Cup[x, Coboundary[x]] - 2 Pi (Cup[x, y] + Cup[y, x])) + Cup[z, Coboundary[y]]]},
      TotalDerivativeQ[
        bad[a + Coboundary[lam], n, phi - kk lam] - bad[a, n, phi],
        (kk / (4 Pi)) Cup[lam, Coboundary[a]] - kk Cup[lam, n] + (kk / 2) HigherCup[1][Coboundary[lam], n],
        3
      ]
    ]
  ],
  False,
  TestID -> "Gauge-Villain-CS-needs-cup1"
]

(* large gauge transformation a -> a + 2 Pi m, n -> n + dm:
   the change is a total derivative minus k Pi times an integer cochain,
   so exp(i S) is invariant for even k *)

VerificationTest[
  With[{a = Cochain[1, fa], n = Cochain[2, fn], phi = Cochain[0, fp], m = Cochain[1, fm]},
    CochainEqualQ[
      ModifiedVillainCS[kk][a + 2 Pi m, n + Coboundary[m], phi] - ModifiedVillainCS[kk][a, n, phi],
      -(kk / 2) Coboundary[Cup[m, a]] -
        kk Pi (Cup[m, n] + Cup[n, m] + HigherCup[1][m, Coboundary[n]] + Cup[Coboundary[m], m]),
      3
    ]
  ],
  True,
  TestID -> "Gauge-Villain-CS-large"
]

(* ---------------------------------------------------------------------- *)
(* concrete fields                                                        *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  With[{dims = {2, 2, 2, 2}, z = {{0, 1, 0, 0}, {-1, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, -1, 0}}},
    {
      ZNFlatQ[THooftFluxCochain[z, dims], dims, 4],
      ZNFlatQ[PeriodicCochain[1, {2, 2}, <|{{0, 0}, {1}} -> 1|>], {2, 2}, 2]
    }
  ],
  {True, False},
  TestID -> "Gauge-ZN-flat"
]


(* local multilinear operations expand like the cup products *)

VerificationTest[
  With[{a = Cochain[1, al], b = Cochain[1, be], c = Cochain[2, ga]},
    {
      CochainExpand[LocalOperation[f, 1][a + 2 b, 3 c]] ===
        3 LocalOperation[f, 1][a, c] + 6 LocalOperation[f, 1][b, c],
      CochainExpand[LocalOperation[f, 2][a, b, Coboundary[Coboundary[c]]]],
      GaugeVariation[LocalOperation[f, 1][a, c], a -> a + Coboundary[Cochain[0, la]]]
    }
  ],
  {True, 0, LocalOperation[f, 1][Coboundary[Cochain[0, la]], Cochain[2, ga]]},
  TestID -> "Gauge-expand-local-operation"
]

(* ---------------------------------------------------------------------- *)
(* the search for coefficients                                            *)
(* ---------------------------------------------------------------------- *)

(* (A3) is the unique combination of its three cup-1 terms; with the other
   sign of the second term there is no solution; candidates of another
   degree are refused *)

VerificationTest[
  With[{a = Cochain[1, fa], b = Cochain[1, fb], c = Cochain[2, fc]},
    With[{
        terms = Function[{u, v},
          {Coboundary[HigherCup[1][u, v]], HigherCup[1][Coboundary[u], v], HigherCup[1][u, Coboundary[v]]}
        ]
      },
      {
        CochainLinearSolve[Cup[a, b] + Cup[b, a], terms[a, b], 2],
        CochainLinearSolve[Cup[a, c] - Cup[c, a], terms[a, c], 3],
        CochainLinearSolve[Cup[a, b] - Cup[b, a], terms[a, b], 2],
        CochainLinearSolve[Cup[a, b], {Cup[a, c]}, 3]
      }
    ]
  ],
  {
    <|"Solvable" -> True, "Unique" -> True, "Coefficients" -> {-1, 1, -1}|>,
    <|"Solvable" -> True, "Unique" -> True, "Coefficients" -> {1, -1, 1}|>,
    <|"Solvable" -> False, "Unique" -> False, "Coefficients" -> $Failed|>,
    $Failed
  },
  TestID -> "Gauge-linear-solve"
]

(* the cup-1 term of the modified Villain Chern-Simons Lagrangian, found:
   the gauge variation of the Lagrangian without that term is a unique
   combination of the variation of a cup_1 dn and of three coboundaries.
   The first coefficient k/2 means the correction -(k/2) a cup_1 dn; the
   others are the primitive of section 5 of the design document *)

VerificationTest[
  With[{a = Cochain[1, fa], n = Cochain[2, fn], phi = Cochain[0, fp], lam = Cochain[0, fl]},
    With[{
        bare = Function[{u, ph},
          ModifiedVillainCS[kk][u, n, ph] + (kk / 2) HigherCup[1][u, Coboundary[n]]],
        cands = {
          HigherCup[1][Coboundary[lam], Coboundary[n]],
          Coboundary[Cup[lam, Coboundary[a]]],
          Coboundary[Cup[lam, n]],
          Coboundary[HigherCup[1][Coboundary[lam], n]]
        }
      },
      With[{variation = bare[a + Coboundary[lam], phi - kk lam] - bare[a, phi]},
        With[{
            full = CochainLinearSolve[variation, cands, 3],
            short = CochainLinearSolve[variation, Rest[cands], 3]
          },
          {
            full["Solvable"],
            full["Unique"],
            Simplify[full["Coefficients"] - {kk / 2, kk / (4 Pi), -kk, kk / 2}],
            short["Solvable"],
            short["Coefficients"]
          }
        ]
      ]
    ]
  ],
  {True, True, {0, 0, 0, 0}, False, $Failed},
  TestID -> "Gauge-correction-search"
]
