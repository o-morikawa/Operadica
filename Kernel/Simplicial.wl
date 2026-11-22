(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Simplicial`                                                  *)
(*                                                                        *)
(*  Cochains on simplices.  The cochain expressions of Operadica`Lattice`  *)
(*  (Cochain, Coboundary, Cup, HigherCup, sums and scalar multiples) are   *)
(*  evaluated here on an ordered simplex instead of a cell of the          *)
(*  hypercubic lattice: the same formula can be read on both.              *)
(*                                                                        *)
(*  A simplex is the increasing list of its vertices {v0, ..., vn}; a      *)
(*  generic cochain Cochain[p, f] has the value f[{v0, ..., vp}].          *)
(*                                                                        *)
(*    (d c)(v0..v(p+1))   = sum_k (-1)^k c(v0 .. omit vk .. v(p+1))        *)
(*    (a cup b)(v0..v(p+q)) = a(v0..vp) b(vp..v(p+q))                      *)
(*    (a cup_i b)(0..n), n = p + q - i: Steenrod's formula, the sum over   *)
(*        the cuts 0 <= j0 < j1 < ... < ji <= n of                         *)
(*          sign * a(0..j0, j1..j2, ...) * b(j0..j1, j2..j3, ...).         *)
(*        The pieces [0, j0], [j0, j1], ..., [ji, n] go alternately to a   *)
(*        and to b; the sign is that of the permutation (the vertices of   *)
(*        a, then the vertices of b that are not cut points).              *)
(*                                                                        *)
(*  With this sign the products satisfy the identity (A3) of               *)
(*  Operadica`Lattice` (arXiv:2303.06160) in the same form, so that the    *)
(*  identities that follow from it hold on both lattices.  The Hirsch      *)
(*  formula, which on the hypercubic lattice holds only up to a homotopy,  *)
(*  holds exactly on simplices.                                           *)
(*                                                                        *)
(*  An identity between cochain expressions built from generic cochains    *)
(*  has the same form on every ordered simplex, so that one evaluation on  *)
(*  the simplex {0, ..., p} proves it on every simplicial complex with     *)
(*  ordered vertices, over any commutative ring of coefficients.           *)
(*                                                                        *)
(*  Checked in reference/simplicial_reference.py.                         *)
(*                                                                        *)
(*  Layer: lattice gauge theory.  Depends on: Lattice.                    *)
(* ====================================================================== *)

BeginPackage["Operadica`Simplicial`", {"Operadica`Lattice`"}];

SimplexValue::usage = "SimplexValue[c, {v0, ..., vn}] evaluates the cochain expression c on the ordered simplex with the vertices v0 < ... < vn. A generic cochain Cochain[p, f] has the value f[{v0, ..., vp}]; Coboundary, Cup and HigherCup are the simplicial coboundary, the cup product, and Steenrod's cup-i products.";

SimplexHigherCupTerms::usage = "SimplexHigherCupTerms[i, p, q] lists the terms {sign, pa, pb} of the cup-i product of a p-cochain a and a q-cochain b on a simplex of dimension p + q - i: the value is the sum of sign * a(the vertices at the positions pa) * b(the vertices at the positions pb), positions counted from 1.";

SimplexCochainZeroQ::usage = "SimplexCochainZeroQ[c] gives True if the cochain expression c vanishes identically on simplices: with generic cochains, its value on the simplex {0, ..., p}, p the degree of c, expands to zero. This proves the identity on every simplicial complex with ordered vertices. The option Modulus -> n tests modulo n.";

SimplexCochainEqualQ::usage = "SimplexCochainEqualQ[a, b] gives True if the cochain expressions a and b agree identically on simplices. The option Modulus -> n compares modulo n.";

Begin["`Private`"];

(* ---------------------------------------------------------------------- *)
(* Steenrod's formula                                                     *)
(* ---------------------------------------------------------------------- *)

SimplexHigherCupTerms[i_Integer?NonNegative, p_Integer?NonNegative, q_Integer?NonNegative] :=
  SimplexHigherCupTerms[i, p, q] =
    With[{n = p + q - i},
      If[n < 0,
        {},
        Select[
          Map[
            Function[js,
              Module[{cuts = Join[{0}, js, {n}], av = {}, bv = {}, inner = {}, m},
                Do[
                  If[EvenQ[m],
                    av = Join[av, Range[cuts[[m + 1]], cuts[[m + 2]]]],
                    bv = Join[bv, Range[cuts[[m + 1]], cuts[[m + 2]]]];
                    inner = Join[inner, Range[cuts[[m + 1]] + 1, cuts[[m + 2]] - 1]]
                  ],
                  {m, 0, i + 1}
                ];
                If[Length[av] === p + 1 && Length[bv] === q + 1,
                  {Signature[Join[av, inner]], av + 1, bv + 1},
                  Null
                ]
              ]
            ],
            Subsets[Range[0, n], {i + 1}]
          ],
          ListQ
        ]
      ]
    ];


(* ---------------------------------------------------------------------- *)
(* evaluation                                                             *)
(* ---------------------------------------------------------------------- *)

SimplexValue::notcochain = "`1` is not a cochain expression that can be evaluated on a simplex.";

sv[0, _] := 0;

sv[Cochain[p_, f_], v_] := If[Length[v] === p + 1, f[v], 0];

sv[u_Plus, v_] := Map[Function[t, sv[t, v]], u];

sv[u_Times, v_] :=
  With[{cs = Select[List @@ u, CochainQ], ks = Select[List @@ u, Function[t, ! CochainQ[t]]]},
    If[Length[cs] === 1,
      (Times @@ ks) * sv[First[cs], v],
      Message[SimplexValue::notcochain, u]; $Failed
    ]
  ];

sv[Coboundary[c_], v_] :=
  Total[Table[(-1)^(k - 1) * sv[c, Delete[v, k]], {k, 1, Length[v]}]];

sv[Cup[a_, b_], v_] :=
  With[{p = CochainDegree[a], q = CochainDegree[b]},
    If[Length[v] =!= p + q + 1,
      0,
      sv[a, Take[v, p + 1]] * sv[b, Drop[v, p]]
    ]
  ];

sv[Cup[a_, b_, rest__], v_] := sv[Cup[Cup[a, b], rest], v];

sv[HigherCup[i_Integer][a_, b_], v_] :=
  With[{p = CochainDegree[a], q = CochainDegree[b]},
    If[i < 0 || Length[v] =!= p + q - i + 1,
      0,
      Total[
        Map[
          Function[tm, tm[[1]] * sv[a, v[[tm[[2]]]]] * sv[b, v[[tm[[3]]]]]],
          SimplexHigherCupTerms[i, p, q]
        ]
      ]
    ]
  ];

sv[u_, _] := (Message[SimplexValue::notcochain, u]; $Failed);

SimplexValue[c_, v_List] := sv[c, v];


(* ---------------------------------------------------------------------- *)
(* identities                                                             *)
(* ---------------------------------------------------------------------- *)

reduce[val_, 0] := Expand[val];
reduce[val_, n_Integer?Positive] :=
  With[{e = Expand[val]},
    If[Head[e] === Plus,
      Map[Function[t, reduceTerm[t, n]], e],
      reduceTerm[e, n]
    ]
  ];

reduceTerm[t_Integer, n_] := Mod[t, n];
reduceTerm[Times[c_Integer, rest__], n_] := Mod[c, n] * Times[rest];
reduceTerm[t_, n_] := Mod[1, n] * t;

Options[SimplexCochainZeroQ] = {Modulus -> 0};

SimplexCochainZeroQ[0, OptionsPattern[]] := True;

SimplexCochainZeroQ[u_, OptionsPattern[]] :=
  With[{p = CochainDegree[u], n = OptionValue[Modulus]},
    IntegerQ[p] && p >= 0 && reduce[sv[u, Range[0, p]], n] === 0
  ];

Options[SimplexCochainEqualQ] = {Modulus -> 0};

SimplexCochainEqualQ[u_, v_, opts : OptionsPattern[]] := SimplexCochainZeroQ[u - v, opts];

End[];

EndPackage[];
