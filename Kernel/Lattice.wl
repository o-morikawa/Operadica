(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Lattice`                                                     *)
(*                                                                        *)
(*  Cochains on the hypercubic lattice Z^d.                                *)
(*                                                                        *)
(*  A cell is LCell[x, s]: base point x, increasing list of directions s.  *)
(*  A cochain expression is built from                                    *)
(*      Cochain[p, f]          value f[x, s] on LCell[x, s]               *)
(*      Coboundary[c]          lattice exterior derivative                *)
(*      Cup[a, b]              cup product (System`Cup, typed a \[Cup] b) *)
(*      HigherCup[i][a, b]     higher cup product                         *)
(*      sums and scalar multiples                                         *)
(*  and stays symbolic until CochainValue evaluates it on a cell.         *)
(*                                                                        *)
(*  Conventions (checked in reference/cubical_reference.py):              *)
(*                                                                        *)
(*   (dc)(x; m1<...<mk) = Sum_j (-1)^(j-1)                                *)
(*          [ c(x + e_mj; ..without mj..) - c(x; ..without mj..) ]        *)
(*                                                                        *)
(*   (a u b)(x; s) = Sum over p-subsets A of s, B = s minus A,            *)
(*          sign(A, B) a(x; A) b(x + e_A; B)                              *)
(*                                                                        *)
(*   a u_i b :  eq. (A3) of Jacobson-Sulejmanpasic, arXiv:2303.06160,     *)
(*          a u_i b - (-1)^(pq+i) b u_i a = (-1)^(p+q+1+i)                *)
(*             [ d(a u_{i+1} b) - da u_{i+1} b - (-1)^p a u_{i+1} db ]    *)
(*      and the component formulas of its Appendix A (which follow        *)
(*      Chen-Tata, arXiv:2106.05274).                                     *)
(*                                                                        *)
(*  Layer: lattice.  Depends on: nothing.                                 *)
(* ====================================================================== *)

BeginPackage["Operadica`Lattice`"];

LCell::usage = "LCell[x, s] is the cell of the hypercubic lattice with base point x (a list of d coordinates) spanned by the directions s (an increasing list of integers between 1 and d).";

LCells::usage = "LCells[dims, p] lists all p-cells of the periodic lattice with side lengths dims.";

Cochain::usage = "Cochain[p, f] is the p-cochain whose value on the cell LCell[x, s] is f[x, s]. With f an undefined symbol this is a generic cochain, suitable for proving identities.";

Coboundary::usage = "Coboundary[c] is the lattice coboundary (exterior derivative) of the cochain c. It stays unevaluated until it is evaluated on a cell with CochainValue.";

HigherCup::usage = "HigherCup[i][a, b] is the higher cup product of a p-cochain a and a q-cochain b, of degree p + q - i. HigherCup[0] is the cup product Cup[a, b]. The sign convention is that of eq. (A3) of arXiv:2303.06160; see SteenrodCupSign for Steenrod's original convention.";

LocalOperation::usage = "LocalOperation[f, d][a1, ..., ar] is the cochain of degree p1 + ... + pr - d given by a local multilinear formula. On a cell with base point x and directions s = {mu_1 < ... < mu_n} its value is the sum, over the terms {c, {row_1, ..., row_r}} of the list f[n], of c a1(x + shift_1; s_1) ... ar(x + shift_r; s_r): row_j is a list of n entries, 2 if aj extends in the direction mu_k, 1 if aj is shifted by one step in that direction, 0 otherwise. Cup and HigherCup are of this form; Operadica`EInfinity` builds the operations of an E-infinity operad in this way.";

CochainQ::usage = "CochainQ[c] gives True if c is a cochain expression: built from Cochain, Coboundary, Cup, HigherCup, LocalOperation, sums and scalar multiples.";

CochainDegree::usage = "CochainDegree[c] gives the degree of a homogeneous cochain expression.";

CochainValue::usage = "CochainValue[c, x, s] evaluates the cochain expression c on the cell with base point x and directions s. CochainValue[c, LCell[x, s]] does the same. Directions given out of order pick up the sign of the permutation.";

CochainZeroQ::usage = "CochainZeroQ[c, d] gives True if the cochain expression c vanishes identically on the d-dimensional hypercubic lattice, tested at a symbolic base point. CochainZeroQ[c, {L1, ..., Ld}] tests all cells of a periodic lattice. The option Modulus -> n tests vanishing modulo n.";

CochainEqualQ::usage = "CochainEqualQ[a, b, d] gives True if the cochain expressions a and b agree identically on the d-dimensional hypercubic lattice. CochainEqualQ[a, b, {L1, ..., Ld}] compares on all cells of a periodic lattice. The option Modulus -> n compares modulo n.";

PeriodicCochain::usage = "PeriodicCochain[p, dims, data] is the p-cochain on the periodic lattice with side lengths dims whose values are given by the Association data, with keys {x, s}; missing cells have value 0.";

RandomCochain::usage = "RandomCochain[p, dims] is a p-cochain on the periodic lattice with random integer values. RandomCochain[p, dims, {min, max}] sets the range.";

THooftFluxCochain::usage = "THooftFluxCochain[z, dims] is the closed 2-cochain on the periodic lattice with side lengths dims that equals z[[mu, nu]] on the plaquette in the (mu, nu) plane at the sites whose mu and nu coordinates are both maximal, and 0 elsewhere. z is an antisymmetric matrix.";

CochainIntegrate::usage = "CochainIntegrate[c, dims] sums the top-degree cochain c over all top cells of the periodic lattice with side lengths dims.";

PontryaginSquare::usage = "PontryaginSquare[b] gives Cup[b, b] - HigherCup[1][b, Coboundary[b]].";

SteenrodSquare::usage = "SteenrodSquare[k][a] gives HigherCup[p - k][a, a] for a cochain expression a of degree p and 0 <= k <= p, and 0 for other k. If the coboundary of the integer cochain a is even, then SteenrodSquare[k][a] is a cocycle modulo 2 of degree p + k, and it represents the Steenrod square Sq^k of the class of a modulo 2. SteenrodSquare[p][a] is Cup[a, a], and the values of SteenrodSquare[0][a] are the squares of the values of a. The coboundary of SteenrodSquare[k][a] is (-1)^(p - k) (1 + (-1)^k) SteenrodSquare[k + 1][a] plus terms with the coboundary of a: for even k, SteenrodSquare[k + 1] is the Bockstein of SteenrodSquare[k]. The expression can be evaluated on cubes (CochainValue) and on simplices (SimplexValue).";

SteenrodCupSign::usage = "SteenrodCupSign[p, q, i] gives the sign (-1)^(i (p + q + 1)) relating the two conventions for higher cup products: Steenrod's cup-i of a p-cochain and a q-cochain equals SteenrodCupSign[p, q, i] times HigherCup[i].";

Begin["`Private`"];

(* ---------------------------------------------------------------------- *)
(* cells                                                                  *)
(* ---------------------------------------------------------------------- *)

latShift[x_List, dirs_List] := x + Total[Map[UnitVector[Length[x], #] &, dirs]];

latPoints[dims_List] := Tuples[Map[Range[0, # - 1] &, dims]];

LCells[dims_List, p_Integer?NonNegative] :=
  Flatten[
    Table[
      LCell[pt, dirs],
      {pt, latPoints[dims]}, {dirs, Subsets[Range[Length[dims]], {p}]}
    ],
    1
  ];


(* ---------------------------------------------------------------------- *)
(* cochain expressions                                                    *)
(* ---------------------------------------------------------------------- *)

CochainQ[_Cochain] = True;
CochainQ[Coboundary[c_]] := CochainQ[c];
CochainQ[Cup[a_, b__]] := AllTrue[{a, b}, CochainQ];
CochainQ[HigherCup[_][a_, b_]] := CochainQ[a] && CochainQ[b];
CochainQ[LocalOperation[_, _][as__]] := AllTrue[{as}, CochainQ];
CochainQ[u_Plus] := AllTrue[List @@ u, CochainQ];
CochainQ[u_Times] := Count[List @@ u, _?CochainQ, {1}] === 1;
CochainQ[_] = False;


CochainDegree::inhom = "`1` is not a homogeneous cochain expression.";

CochainDegree[Cochain[p_, _]] := p;
CochainDegree[Coboundary[c_]] := CochainDegree[c] + 1;
CochainDegree[Cup[a_, b__]] := Total[Map[CochainDegree, {a, b}]];
CochainDegree[HigherCup[i_][a_, b_]] := CochainDegree[a] + CochainDegree[b] - i;
CochainDegree[LocalOperation[_, d_][as__]] :=
  With[{ds = Map[CochainDegree, {as}]},
    If[AllTrue[ds, IntegerQ], Total[ds] - d, $Failed]
  ];
CochainDegree[u_Plus] :=
  With[{ds = Union[Map[CochainDegree, List @@ u]]},
    If[Length[ds] === 1,
      First[ds],
      Message[CochainDegree::inhom, u]; $Failed
    ]
  ];
CochainDegree[u_Times] :=
  With[{cs = Select[List @@ u, CochainQ]},
    If[Length[cs] === 1,
      CochainDegree[First[cs]],
      Message[CochainDegree::inhom, u]; $Failed
    ]
  ];
CochainDegree[u_] := (Message[CochainDegree::inhom, u]; $Failed);


(* ---------------------------------------------------------------------- *)
(* evaluation on a cell                                                   *)
(*   cv[c, x, s] assumes that s is increasing and duplicate free          *)
(* ---------------------------------------------------------------------- *)

CochainValue::notcochain = "`1` is not a cochain expression.";

cv[0, _, _] := 0;

cv[Cochain[p_, f_], x_, s_] := If[Length[s] === p, f[x, s], 0];

cv[u_Plus, x_, s_] := Map[cv[#, x, s] &, u];

cv[u_Times, x_, s_] :=
  With[{cs = Select[List @@ u, CochainQ], ks = Select[List @@ u, ! CochainQ[#] &]},
    If[Length[cs] === 1,
      (Times @@ ks) * cv[First[cs], x, s],
      Message[CochainValue::notcochain, u]; $Failed
    ]
  ];

cv[Coboundary[c_], x_, s_] :=
  Total[
    Table[
      (-1)^(k - 1) * (
        cv[c, latShift[x, {s[[k]]}], Delete[s, k]] - cv[c, x, Delete[s, k]]
      ),
      {k, 1, Length[s]}
    ]
  ];

cv[Cup[a_, b_], x_, s_] :=
  With[{p = CochainDegree[a], q = CochainDegree[b]},
    If[Length[s] =!= p + q,
      0,
      Total[
        Table[
          With[{back = Complement[s, front]},
            Signature[Join[front, back]] *
              cv[a, x, front] * cv[b, latShift[x, front], back]
          ],
          {front, Subsets[s, {p}]}
        ]
      ]
    ]
  ];

cv[Cup[a_, b_, rest__], x_, s_] := cv[Cup[Cup[a, b], rest], x, s];


(* ---- higher cup products ---------------------------------------------- *)
(*                                                                        *)
(* A word w in {1, 2, 3}^n labels each direction of the cell:             *)
(*    1 : only a extends in this direction                                *)
(*    2 : only b extends in this direction                                *)
(*    3 : both extend in this direction (exactly i of these)              *)
(* With t = number of 3's strictly before the direction:                  *)
(*    1 : b is shifted by one step in this direction iff t is even        *)
(*    2 : a is shifted by one step in this direction iff t is odd         *)
(* sign(w) = (-1)^e,                                                      *)
(*    e = i (i + 1) / 2                                                   *)
(*      + #{k < l : w_k in {2, 3} and w_l in {1, 3}}                      *)
(*      + #{k < l : w_k in {1, 2} and w_l = 3}                            *)
(* and  a u_i b = (-1)^(i (p + q + 1)) Sum_w sign(w) a(...) b(...).       *)

hcWords[p_Integer, q_Integer, i_Integer] := hcWords[p, q, i] =
  Permutations[
    Join[ConstantArray[1, p - i], ConstantArray[2, q - i], ConstantArray[3, i]]
  ];

hcWordSign[w_List] := hcWordSign[w] =
  With[{n = Length[w], i = Count[w, 3]},
    (-1)^(
      i (i + 1) / 2 +
      Total[
        Flatten[
          Table[
            Boole[MemberQ[{2, 3}, w[[k]]] && MemberQ[{1, 3}, w[[l]]]] +
              Boole[MemberQ[{1, 2}, w[[k]]] && w[[l]] === 3],
            {k, 1, n}, {l, k + 1, n}
          ]
        ]
      ]
    )
  ];

(* returns {directions of a, directions of b, shift of a, shift of b} *)
hcSplit[w_List, s_List] :=
  Module[{t = 0, sa = {}, sb = {}, sha = {}, shb = {}, k},
    Do[
      Switch[w[[k]],
        1, (AppendTo[sa, s[[k]]]; If[EvenQ[t], AppendTo[shb, s[[k]]]]),
        2, (AppendTo[sb, s[[k]]]; If[OddQ[t], AppendTo[sha, s[[k]]]]),
        3, (AppendTo[sa, s[[k]]]; AppendTo[sb, s[[k]]]; t = t + 1)
      ],
      {k, 1, Length[w]}
    ];
    {sa, sb, sha, shb}
  ];

cv[HigherCup[i_Integer][a_, b_], x_, s_] :=
  With[{p = CochainDegree[a], q = CochainDegree[b]},
    If[i < 0 || i > Min[p, q] || Length[s] =!= p + q - i,
      0,
      (-1)^(i (p + q + 1)) *
        Total[
          Table[
            With[{sp = hcSplit[w, s]},
              hcWordSign[w] *
                cv[a, latShift[x, sp[[3]]], sp[[1]]] *
                cv[b, latShift[x, sp[[4]]], sp[[2]]]
            ],
            {w, hcWords[p, q, i]}
          ]
        ]
    ]
  ];

(* ---- local multilinear operations --------------------------------------- *)

cv[LocalOperation[f_, d_Integer][as__], x_, s_] :=
  With[{args = {as}, degs = Map[CochainDegree, {as}], n = Length[s]},
    If[Total[degs] - d =!= n,
      0,
      Total[
        Map[
          Function[term,
            If[Map[Function[row, Count[row, 2]], term[[2]]] === degs,
              term[[1]] *
                Product[
                  cv[args[[j]], latShift[x, Pick[s, term[[2, j]], 1]], Pick[s, term[[2, j]], 2]],
                  {j, 1, Length[args]}
                ],
              0
            ]
          ],
          f[n]
        ]
      ]
    ]
  ];

cv[u_, _, _] := (Message[CochainValue::notcochain, u]; $Failed);


CochainValue[c_, LCell[x_List, s_List]] := CochainValue[c, x, s];

CochainValue[c_, x_List, s_List] :=
  Which[
    ! DuplicateFreeQ[s], 0,
    OrderedQ[s], cv[c, x, s],
    True, Signature[s] * cv[c, x, Sort[s]]
  ];


(* ---------------------------------------------------------------------- *)
(* identities                                                             *)
(*                                                                        *)
(* With generic cochains Cochain[p, f] (f an undefined symbol) the values *)
(* f[x, s] are independent variables.  The operations are local and       *)
(* translation invariant, so testing at one symbolic base point on every  *)
(* p-cell type proves the identity on every d-dimensional hypercubic      *)
(* lattice, of any size, over any commutative coefficient ring.           *)
(* ---------------------------------------------------------------------- *)

(* expand; for a modulus n > 0 also reduce the integer coefficient of every
   term modulo n *)
czReduce[val_, 0] := Expand[val];
czReduce[val_, n_Integer?Positive] :=
  With[{e = Expand[val]},
    If[Head[e] === Plus, Map[czTerm[#, n] &, e], czTerm[e, n]]
  ];

czTerm[t_Integer, n_] := Mod[t, n];
czTerm[Times[c_Integer, rest__], n_] := Mod[c, n] * Times[rest];
czTerm[t_, n_] := Mod[1, n] * t;

Options[CochainZeroQ] = {Modulus -> 0};

CochainZeroQ[0, _, OptionsPattern[]] := True;

CochainZeroQ[u_, d_Integer?Positive, OptionsPattern[]] :=
  With[{p = CochainDegree[u], x = Array[\[FormalX], d], n = OptionValue[Modulus]},
    IntegerQ[p] && p >= 0 &&
      AllTrue[Subsets[Range[d], {p}], czReduce[cv[u, x, #], n] === 0 &]
  ];

CochainZeroQ[u_, dims : {__Integer}, OptionsPattern[]] :=
  With[{p = CochainDegree[u], n = OptionValue[Modulus]},
    IntegerQ[p] && p >= 0 &&
      AllTrue[LCells[dims, p], czReduce[cv[u, #[[1]], #[[2]]], n] === 0 &]
  ];


Options[CochainEqualQ] = {Modulus -> 0};

CochainEqualQ[u_, v_, where_, opts : OptionsPattern[]] :=
  CochainZeroQ[u - v, where, opts];


(* ---------------------------------------------------------------------- *)
(* concrete fields on a periodic lattice                                  *)
(* ---------------------------------------------------------------------- *)

PeriodicCochain[p_Integer?NonNegative, dims_List, data_Association] :=
  Cochain[p, Function[{x, s}, Lookup[data, Key[{Mod[x, dims], s}], 0]]];

RandomCochain[p_Integer?NonNegative, dims_List] := RandomCochain[p, dims, {-3, 3}];

RandomCochain[p_Integer?NonNegative, dims_List, range_List] :=
  PeriodicCochain[p, dims,
    Association[
      Map[({#[[1]], #[[2]]} -> RandomInteger[range]) &, LCells[dims, p]]
    ]
  ];

THooftFluxCochain[z_?MatrixQ, dims_List] :=
  Cochain[2,
    Function[{x, s},
      z[[s[[1]], s[[2]]]] *
        Boole[
          Mod[x[[s[[1]]]], dims[[s[[1]]]]] == dims[[s[[1]]]] - 1 &&
          Mod[x[[s[[2]]]], dims[[s[[2]]]]] == dims[[s[[2]]]] - 1
        ]
    ]
  ];

CochainIntegrate[c_, dims_List] :=
  With[{top = Range[Length[dims]]},
    Total[Map[CochainValue[c, #, top] &, latPoints[dims]]]
  ];


(* ---------------------------------------------------------------------- *)
(* derived operations                                                     *)
(* ---------------------------------------------------------------------- *)

PontryaginSquare[b_] := Cup[b, b] - HigherCup[1][b, Coboundary[b]];

SteenrodSquare[k_Integer][a_] :=
  With[{p = CochainDegree[a]},
    Which[
      ! IntegerQ[p], $Failed,
      0 <= k <= p, HigherCup[p - k][a, a],
      True, 0
    ]
  ];

SteenrodCupSign[p_Integer, q_Integer, i_Integer] := (-1)^(i (p + q + 1));

End[];

EndPackage[];
