(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`EInfinity`                                                   *)
(*                                                                        *)
(*  The cochains of the hypercubic lattice are an algebra over the         *)
(*  Barratt-Eccles operad, an E-infinity operad.  The operations of arity  *)
(*  2 are the higher cup products; the operations of higher arity are the  *)
(*  homotopies between the ways of composing them.                         *)
(*                                                                        *)
(*  For an element s = {w0, ..., wm} of arity r and cochains a1, ..., ar   *)
(*  of degrees p1, ..., pr,                                                *)
(*                                                                        *)
(*    theta_s(a1, .., ar)(x; S) = Sum_terms c Prod_j aj(x + shift_j; S_j)  *)
(*                                                                        *)
(*  with the terms of CubeCoaction[s, n], n the dimension of the cell.     *)
(*  Its degree is p1 + ... + pr - m.  Three laws hold:                     *)
(*                                                                        *)
(*  (L)  d theta_s(a) = (-1)^m [ Sum_j (-1)^(p1+..+p(j-1))                 *)
(*                         theta_s(.., d aj, ..) - theta_(ds)(a) ]         *)
(*  (C)  theta_(s o_j t)(a) = (-1)^(|s||t| + |t|(p1+..+p(j-1)))            *)
(*                         theta_s(a1, .., theta_t(aj, ..), ..)            *)
(*  (E)  theta_(s.p)(a1, .., ar) = sign theta_s(a_(p^-1(1)), ..),          *)
(*       sign = the signature of the list of the p(i) with pi odd          *)
(*                                                                        *)
(*  In arity 2, with e_i = {{1,2},{2,1},{1,2},...} of degree i,            *)
(*       theta_(e_i)(a, b) = (-1)^(i(p+q) + i(i-1)/2) HigherCup[i][a, b].  *)
(*                                                                        *)
(*  The Hirsch formula holds up to the homotopy H = theta of               *)
(*  {{1,2,3},{1,3,2},{3,1,2}}, an operation in the E_2 stage:              *)
(*       (a u b) u_1 c - a u (b u_1 c) - (-1)^(q(r-1)) (a u_1 c) u b       *)
(*         = (-1)^(p+q+r) [ dH(a,b,c) - H(da,b,c)                          *)
(*                          - (-1)^p H(a,db,c) - (-1)^(p+q) H(a,b,dc) ].   *)
(*                                                                        *)
(*  Checked in reference/einfinity_reference.py.                          *)
(*                                                                        *)
(*  Layer: bridge.  Depends on: Graded, BarrattEccles, Lattice.           *)
(* ====================================================================== *)

BeginPackage["Operadica`EInfinity`", {
  "Operadica`Graded`",
  "Operadica`BarrattEccles`",
  "Operadica`Lattice`"
}];

EInfinityOperation::usage = "EInfinityOperation[s][a1, ..., ar] is the cochain obtained by letting the element s = {w0, ..., wm} of the Barratt-Eccles operad in arity r, or a linear combination of LBasis[element], act on the lattice cochains a1, ..., ar. Its degree is p1 + ... + pr - m. It is a cochain expression (a LocalOperation) and can be used with CochainValue, Coboundary and CochainEqualQ. EInfinityOperation[{{1, 2}}] is the cup product.";

HirschHomotopy::usage = "HirschHomotopy[a, b, c] is the cochain EInfinityOperation[HirschElement[]][a, b, c], of degree p + q + r - 2. Its coboundary measures the failure of the cup-1 product to be a derivation of the cup product; see HirschFormulaQ.";

EInfinityLeibnizQ::usage = "EInfinityLeibnizQ[s, {p1, ..., pr}, d] gives True if the coboundary of EInfinityOperation[s] on generic cochains of the given degrees is (-1)^m (Sum_j (-1)^(p1+...+p(j-1)) theta_s(.., d aj, ..) - theta_(ds)(a)), identically on the d-dimensional lattice.";

EInfinityCompositionQ::usage = "EInfinityCompositionQ[s, j, t, {p1, ...}, d] gives True if the operation of the composite s o_j t is (-1)^(|s||t| + |t|(p1+...+p(j-1))) times the operation of s with the operation of t inserted in its j-th argument, on generic cochains of the given degrees on the d-dimensional lattice.";

EInfinityEquivarianceQ::usage = "EInfinityEquivarianceQ[s, perm, {p1, ..., pr}, d] gives True if the operation of BarrattEcclesAct[s, perm] on (a1, ..., ar) is the operation of s on (a_(perm^-1(1)), ..., a_(perm^-1(r))) times the Koszul sign, on generic cochains of the given degrees on the d-dimensional lattice.";

EInfinityHigherCupQ::usage = "EInfinityHigherCupQ[i, {p, q}, d] gives True if EInfinityOperation[HigherCupElement[i]][a, b] = (-1)^(i (p + q) + i (i - 1)/2) HigherCup[i][a, b] for generic cochains of degrees p and q on the d-dimensional lattice.";

HirschFormulaQ::usage = "HirschFormulaQ[{p, q, r}, d] gives True if, for generic cochains a, b, c of degrees p, q, r >= 1 on the d-dimensional lattice, (a u b) u_1 c - a u (b u_1 c) - (-1)^(q (r - 1)) (a u_1 c) u b = (-1)^(p+q+r) (dH(a,b,c) - H(da,b,c) - (-1)^p H(a,db,c) - (-1)^(p+q) H(a,b,dc)) with H = HirschHomotopy.";

Begin["`Private`"];

elementQ[s_] := MatchQ[s, {__List}];

EInfinityOperation[0][___] := 0;

EInfinityOperation[s_?elementQ][as__] := LocalOperation[CubeCoaction[s], Length[s] - 1][as];

EInfinityOperation[u : (_Plus | _Times | _LBasis)][as__] :=
  Total[Map[Function[tm, tm[[1]] EInfinityOperation[tm[[2]]][as]], LinearTerms[u]]];

HirschHomotopy[a_, b_, c_] := EInfinityOperation[HirschElement[]][a, b, c];


(* generic cochains of the given degrees *)
genericCochains[degs_List] :=
  MapThread[
    Function[{p, f}, Cochain[p, f]],
    {degs, Take[{\[FormalA], \[FormalB], \[FormalC], \[FormalD], \[FormalE], \[FormalF]}, Length[degs]]}
  ];

degreesQ[degs_] := MatchQ[degs, {__Integer?NonNegative}] && Length[degs] <= 6;


EInfinityLeibnizQ[s_?elementQ, degs_?degreesQ, d_Integer?Positive] /;
    Length[degs] === Length[First[s]] && Total[degs] >= Length[s] - 1 :=
  With[{as = genericCochains[degs], m = Length[s] - 1, r = Length[degs]},
    CochainEqualQ[
      Coboundary[EInfinityOperation[s] @@ as],
      (-1)^m (
        Total[
          Table[
            (-1)^Total[Take[degs, j - 1]] *
              (EInfinityOperation[s] @@ ReplacePart[as, j -> Coboundary[as[[j]]]]),
            {j, 1, r}
          ]
        ] -
          (EInfinityOperation[BarrattEcclesDifferential[s]] @@ as)
      ),
      d
    ]
  ];


EInfinityCompositionQ[s_?elementQ, j_Integer?Positive, t_?elementQ, degs_?degreesQ, d_Integer?Positive] /;
    j <= Length[First[s]] && Length[degs] === Length[First[s]] + Length[First[t]] - 1 &&
      Total[Take[degs, {j, j + Length[First[t]] - 1}]] >= Length[t] - 1 &&
      Total[degs] >= Length[s] + Length[t] - 2 :=
  With[{as = genericCochains[degs], k = Length[First[t]], ds = Length[s] - 1, dt = Length[t] - 1},
    CochainEqualQ[
      EInfinityOperation[BarrattEcclesCompose[s, j, t]] @@ as,
      (-1)^(ds dt + dt Total[Take[degs, j - 1]]) *
        (EInfinityOperation[s] @@
          Join[
            Take[as, j - 1],
            {EInfinityOperation[t] @@ Take[as, {j, j + k - 1}]},
            Drop[as, j + k - 1]
          ]),
      d
    ]
  ];


EInfinityEquivarianceQ[s_?elementQ, perm_List, degs_?degreesQ, d_Integer?Positive] /;
    Length[degs] === Length[First[s]] && Sort[perm] === Range[Length[degs]] &&
      Total[degs] >= Length[s] - 1 :=
  With[{as = genericCochains[degs]},
    CochainEqualQ[
      EInfinityOperation[BarrattEcclesAct[s, perm]] @@ as,
      Signature[Pick[perm, Map[OddQ, degs]]] * (EInfinityOperation[s] @@ as[[Ordering[perm]]]),
      d
    ]
  ];


EInfinityHigherCupQ[i_Integer?NonNegative, {p_Integer, q_Integer}, d_Integer?Positive] /;
    p >= i && q >= i :=
  With[{a = Cochain[p, \[FormalA]], b = Cochain[q, \[FormalB]]},
    CochainEqualQ[
      EInfinityOperation[HigherCupElement[i]][a, b],
      (-1)^(i (p + q) + i (i - 1)/2) HigherCup[i][a, b],
      d
    ]
  ];


HirschFormulaQ[{p_Integer?Positive, q_Integer?Positive, r_Integer?Positive}, d_Integer?Positive] :=
  With[{a = Cochain[p, \[FormalA]], b = Cochain[q, \[FormalB]], c = Cochain[r, \[FormalC]]},
    CochainEqualQ[
      HigherCup[1][Cup[a, b], c] - Cup[a, HigherCup[1][b, c]] -
        (-1)^(q (r - 1)) Cup[HigherCup[1][a, c], b],
      (-1)^(p + q + r) (
        Coboundary[HirschHomotopy[a, b, c]] -
          HirschHomotopy[Coboundary[a], b, c] -
          (-1)^p HirschHomotopy[a, Coboundary[b], c] -
          (-1)^(p + q) HirschHomotopy[a, b, Coboundary[c]]
      ),
      d
    ]
  ];

End[];

EndPackage[];
