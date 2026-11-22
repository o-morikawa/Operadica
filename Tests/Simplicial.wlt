(* Simplicial: cochain expressions evaluated on ordered simplices, with
   Steenrod's cup-i products.  The expected values are those of
   reference/simplicial_reference.py. *)

(* ---------------------------------------------------------------------- *)
(* Steenrod's formula                                                     *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  {
    SimplexHigherCupTerms[0, 1, 2],
    SimplexHigherCupTerms[1, 1, 1],
    SimplexHigherCupTerms[1, 2, 1],
    SimplexHigherCupTerms[1, 1, 2],
    SimplexHigherCupTerms[1, 2, 2],
    SimplexHigherCupTerms[2, 2, 2],
    SimplexHigherCupTerms[2, 1, 1],
    Map[Length, {SimplexHigherCupTerms[1, 2, 3], SimplexHigherCupTerms[1, 3, 2], SimplexHigherCupTerms[1, 3, 3]}]
  },
  {
    {{1, {1, 2}, {2, 3, 4}}},
    {{1, {1, 2}, {1, 2}}},
    {{1, {1, 2, 3}, {1, 2}}, {1, {1, 2, 3}, {2, 3}}},
    {{-1, {1, 3}, {1, 2, 3}}},
    {{1, {1, 3, 4}, {1, 2, 3}}, {-1, {1, 2, 4}, {2, 3, 4}}},
    {{1, {1, 2, 3}, {1, 2, 3}}},
    {},
    {2, 3, 3}
  },
  TestID -> "Simplicial-Steenrod-terms"
]

(* generic cochains: the values f[{v0, ..., vp}] are independent symbols *)

VerificationTest[
  With[{a1 = Cochain[1, fa], b1 = Cochain[1, fb], a2 = Cochain[2, ga], b2 = Cochain[2, gb]},
    {
      SimplexValue[a1, {0, 1}],
      SimplexValue[a1, {3, 7}],
      SimplexValue[a1, {0, 1, 2}],
      SimplexValue[Coboundary[a1], {0, 1, 2}],
      SimplexValue[Cup[a1, b1], {0, 1, 2}],
      SimplexValue[Cup[a1, b2], {0, 1, 2, 3}],
      SimplexValue[HigherCup[0][a1, b1], {0, 1, 2}],
      SimplexValue[HigherCup[1][a1, b1], {0, 1}],
      SimplexValue[HigherCup[1][a2, b1], {0, 1, 2}],
      SimplexValue[HigherCup[1][a1, b2], {0, 1, 2}],
      SimplexValue[HigherCup[1][a2, b2], {0, 1, 2, 3}],
      SimplexValue[2 a1 - 3 b1, {0, 1}],
      SimplexValue[Cup[a1, b1, a1], {0, 1, 2, 3}]
    }
  ],
  {
    fa[{0, 1}],
    fa[{3, 7}],
    0,
    fa[{1, 2}] - fa[{0, 2}] + fa[{0, 1}],
    fa[{0, 1}] fb[{1, 2}],
    fa[{0, 1}] gb[{1, 2, 3}],
    fa[{0, 1}] fb[{1, 2}],
    fa[{0, 1}] fb[{0, 1}],
    ga[{0, 1, 2}] fb[{0, 1}] + ga[{0, 1, 2}] fb[{1, 2}],
    -fa[{0, 2}] gb[{0, 1, 2}],
    ga[{0, 2, 3}] gb[{0, 1, 2}] - ga[{0, 1, 3}] gb[{1, 2, 3}],
    2 fa[{0, 1}] - 3 fb[{0, 1}],
    fa[{0, 1}] fb[{1, 2}] fa[{2, 3}]
  },
  TestID -> "Simplicial-values"
]

(* a field with numbers: A = 1, 2, 0 on the edges 01, 12, 02 of a triangle has
   the curvature (dA)(012) = 2 - 0 + 1 *)

VerificationTest[
  With[{a = Cochain[1, Function[v, Replace[v, {{0, 1} -> 1, {1, 2} -> 2, {0, 2} -> 0}]]]},
    {
      SimplexValue[Coboundary[a], {0, 1, 2}],
      SimplexValue[Cup[a, a], {0, 1, 2}],
      SimplexValue[HigherCup[1][a, Coboundary[a]], {0, 1, 2}]
    }
  ],
  {3, 2, 0},
  TestID -> "Simplicial-numeric-field"
]

(* ---------------------------------------------------------------------- *)
(* identities, proved with generic cochains                               *)
(* ---------------------------------------------------------------------- *)

VerificationTest[
  Table[SimplexCochainZeroQ[Coboundary[Coboundary[Cochain[p, fa]]]], {p, 0, 4}],
  {True, True, True, True, True},
  TestID -> "Simplicial-coboundary-squares-to-zero"
]

VerificationTest[
  AllTrue[
    Tuples[Range[0, 3], 2],
    Function[pq,
      With[{a = Cochain[pq[[1]], fa], b = Cochain[pq[[2]], fb]},
        SimplexCochainEqualQ[
          Coboundary[Cup[a, b]],
          Cup[Coboundary[a], b] + (-1)^pq[[1]] Cup[a, Coboundary[b]]
        ]
      ]
    ]
  ],
  True,
  TestID -> "Simplicial-Leibniz"
]

VerificationTest[
  AllTrue[
    Tuples[Range[0, 2], 3],
    Function[pqr,
      With[{a = Cochain[pqr[[1]], fa], b = Cochain[pqr[[2]], fb], c = Cochain[pqr[[3]], fc]},
        SimplexCochainEqualQ[Cup[Cup[a, b], c], Cup[a, Cup[b, c]]]
      ]
    ]
  ],
  True,
  TestID -> "Simplicial-cup-associative"
]

(* the identity (A3) of arXiv:2303.06160, in the form used on the hypercubic
   lattice:
   a cup_i b - (-1)^(pq+i) b cup_i a
     = (-1)^(p+q+1+i) [ d(a cup_(i+1) b) - da cup_(i+1) b - (-1)^p a cup_(i+1) db ] *)

VerificationTest[
  AllTrue[
    Select[Tuples[Range[0, 3], 3], Function[t, t[[1]] + t[[2]] - t[[3]] >= 0]],
    Function[t,
      With[{a = Cochain[t[[1]], fa], b = Cochain[t[[2]], fb], p = t[[1]], q = t[[2]], i = t[[3]]},
        SimplexCochainEqualQ[
          HigherCup[i][a, b] - (-1)^(p q + i) HigherCup[i][b, a],
          (-1)^(p + q + 1 + i) (
            Coboundary[HigherCup[i + 1][a, b]] -
              HigherCup[i + 1][Coboundary[a], b] -
              (-1)^p HigherCup[i + 1][a, Coboundary[b]]
          )
        ]
      ]
    ]
  ],
  True,
  TestID -> "Simplicial-A3"
]

(* cup_i vanishes for i > min(p, q), and a cup_p a is the square of the values *)

VerificationTest[
  {
    SimplexCochainZeroQ[HigherCup[2][Cochain[1, fa], Cochain[2, fb]]],
    SimplexCochainZeroQ[HigherCup[3][Cochain[2, fa], Cochain[3, fb]]],
    SimplexValue[HigherCup[2][Cochain[2, fa], Cochain[2, fa]], {0, 1, 2}],
    SimplexCochainZeroQ[HigherCup[1][Cochain[1, fa], Cochain[1, fb]]]
  },
  {True, True, fa[{0, 1, 2}]^2, False},
  TestID -> "Simplicial-higher-cup-range"
]

(* the Hirsch formula
     (a cup b) cup_1 c = a cup (b cup_1 c) + (-1)^(q(r-1)) (a cup_1 c) cup b
   holds exactly on simplices *)

VerificationTest[
  AllTrue[
    Tuples[Range[1, 2], 3],
    Function[t,
      With[{a = Cochain[t[[1]], fa], b = Cochain[t[[2]], fb], c = Cochain[t[[3]], fc], q = t[[2]], r = t[[3]]},
        SimplexCochainZeroQ[
          HigherCup[1][Cup[a, b], c] - Cup[a, HigherCup[1][b, c]] -
            (-1)^(q (r - 1)) Cup[HigherCup[1][a, c], b]
        ]
      ]
    ]
  ],
  True,
  TestID -> "Simplicial-Hirsch"
]

(* the same expression on the two lattices: an identity on simplices, a
   defect on plaquettes *)

VerificationTest[
  With[{a = Cochain[1, fa], b = Cochain[1, fb], c = Cochain[1, fc]},
    With[{hirsch = HigherCup[1][Cup[a, b], c] - Cup[a, HigherCup[1][b, c]] - Cup[HigherCup[1][a, c], b]},
      {SimplexCochainZeroQ[hirsch], CochainZeroQ[hirsch, 2]}
    ]
  ],
  {True, False},
  TestID -> "Simplicial-Hirsch-simplices-and-cubes"
]

(* the identities of the Pontryagin square used on the hypercubic lattice hold
   on simplices in the same form: they follow from (A3) *)

VerificationTest[
  With[{b = Cochain[2, fb], lam = Cochain[1, fl]},
    SimplexCochainEqualQ[
      PontryaginSquare[b + Coboundary[lam]] - PontryaginSquare[b],
      Coboundary[2 Cup[lam, b] + Cup[lam, Coboundary[lam]] - HigherCup[1][b, Coboundary[lam]]] +
        2 Cup[lam, Coboundary[b]] +
        HigherCup[1][Coboundary[b], Coboundary[lam]] -
        HigherCup[1][Coboundary[lam], Coboundary[b]]
    ]
  ],
  True,
  TestID -> "Simplicial-Pontryagin-gauge-variation"
]

VerificationTest[
  With[{b = Cochain[2, fb], c = Cochain[2, fc]},
    SimplexCochainEqualQ[
      PontryaginSquare[b + nn c] - PontryaginSquare[b],
      2 nn Cup[c, b] + nn^2 (Cup[c, c] - HigherCup[1][c, Coboundary[c]]) -
        nn Coboundary[HigherCup[1][b, c]] +
        nn (HigherCup[1][Coboundary[b], c] - HigherCup[1][c, Coboundary[b]])
    ]
  ],
  True,
  TestID -> "Simplicial-Pontryagin-shift-by-N"
]

VerificationTest[
  With[{a = Cochain[1, fa]},
    {
      SimplexCochainEqualQ[
        Cup[a, Coboundary[a]] - Cup[Coboundary[a], a],
        Coboundary[HigherCup[1][a, Coboundary[a]]] - HigherCup[1][Coboundary[a], Coboundary[a]]
      ],
      (* (A3) with b = a: twice the square of a 1-cochain is exact up to cup_1
         terms, so that it vanishes modulo 2 but not over the integers *)
      SimplexCochainEqualQ[
        2 Cup[a, a],
        -Coboundary[HigherCup[1][a, a]] + HigherCup[1][Coboundary[a], a] - HigherCup[1][a, Coboundary[a]]
      ],
      SimplexCochainZeroQ[2 Cup[a, a], Modulus -> 2],
      SimplexCochainZeroQ[2 Cup[a, a]]
    }
  ],
  {True, True, True, False},
  TestID -> "Simplicial-Chern-Simons-identity"
]
