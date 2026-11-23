(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Villain`                                                     *)
(*                                                                        *)
(*  U(1) gauge fields in the modified Villain form, and their product in   *)
(*  differential cohomology (Deligne-Beilinson).                          *)
(*                                                                        *)
(*  A Villain field of degree p is a pair A = (a, n): a real p-cochain a   *)
(*  (the connection) and an integer (p+1)-cochain n (the flux), with       *)
(*                                                                        *)
(*    curvature     F = da - 2 Pi n                                        *)
(*    gauge         a -> a + d lambda                                      *)
(*    large gauge   a -> a + 2 Pi m,  n -> n + dm   (m an integer p-cochain) *)
(*                                                                        *)
(*  Both transformations leave F unchanged.  A flat field has dn = 0 (no   *)
(*  monopoles); in an action this is imposed by a Lagrange multiplier.     *)
(*  The cochains are cochain expressions of Operadica`Lattice`, so that    *)
(*  everything can be evaluated on cubes (CochainValue, CochainEqualQ) and *)
(*  on simplices (SimplexValue, SimplexCochainEqualQ).                    *)
(*                                                                        *)
(*  The Deligne-Beilinson product of A (degree p) and B = (b, n') (degree  *)
(*  q) is the Villain field of degree p + q + 1                           *)
(*                                                                        *)
(*    A * B = ( a cup F_B / (2 Pi) + (-1)^p n cup b ,  - n cup n' ).       *)
(*                                                                        *)
(*  Identities, exact for generic cochains (the terms with dn, dn' vanish  *)
(*  for flat fields):                                                     *)
(*                                                                        *)
(*    F(A * B) = F_A cup F_B / (2 Pi) + (-1)^p (dn cup b - a cup dn')      *)
(*    (A + d lambda) * B :  connection + d(lambda cup F_B / (2 Pi))        *)
(*                                     + (-1)^(p-1) lambda cup dn'         *)
(*    A * (B + d mu)     :  connection - d(n cup mu) + dn cup mu           *)
(*    large, A (by m)    :  connection + 2 Pi (- m cup n') + (-1)^p d(m cup b), *)
(*                          flux + d(- m cup n') + (-1)^p m cup dn'        *)
(*    large, B (by l)    :  connection + 2 Pi (-1)^p n cup l,              *)
(*                          flux + (-1)^p (d(n cup l) - dn cup l)          *)
(*                                                                        *)
(*  so that the product of flat fields is defined on gauge classes.  The   *)
(*  connection of A * B is the Lagrangian of the BF (mutual Chern-Simons)  *)
(*  theory, and half of the connection of A * A that of Chern-Simons       *)
(*  theory: the modified Villain Lagrangian of arXiv:2303.06160, eq. (17), *)
(*  is (k/2) (A * A) - (k/2) a cup_1 dn + phi cup dn.                      *)
(*                                                                        *)
(*  The product is graded commutative up to a gauge transformation: with  *)
(*  e = (-1)^((p+1)(q+1)) and s = (-1)^(p+q),                              *)
(*                                                                        *)
(*    lambda = ((-1)^p a cup b - (-1)^q F_A cup_1 b) / (2 Pi) - s a cup_1 n' *)
(*    m      = s n cup_1 n'                                                *)
(*    conn(A * B) - e conn(B * A) = d lambda + 2 Pi m                      *)
(*          - s F_A cup_1 F_B / (2 Pi) + (-1)^q (a cup_1 dn' - dn cup_1 b)  *)
(*    flux(A * B) - e flux(B * A) = dm - s (dn cup_1 n' - (-1)^p n cup_1 dn') *)
(*                                                                        *)
(*  The homotopy is cup_1, the operation of the E-infinity operad that     *)
(*  exchanges the two factors of the cup product.  The term with           *)
(*  F_A cup_1 F_B is gauge invariant and is not a gauge transformation: it *)
(*  comes from the cup product of cochains not being commutative, has no   *)
(*  counterpart for differential forms, and vanishes if F_A = 0 or F_B = 0. *)
(*                                                                        *)
(*  The theta term of a field of degree p in 2p + 2 dimensions is          *)
(*  (theta / 8 Pi^2) F cup F.  It equals (theta / 4 Pi) F(A * A) plus      *)
(*                                                                        *)
(*    W = - (-1)^p (theta / 4 Pi) (dn cup a - a cup dn),                   *)
(*                                                                        *)
(*  the coupling of the connection to the monopole current dn.  Under      *)
(*  a -> a + d lambda, W changes by                                        *)
(*  - (theta / 4 Pi) d(dn cup lambda - (-1)^p lambda cup dn): a monopole   *)
(*  carries the electric charge theta / 2 Pi (the Witten effect), half of  *)
(*  it from each of the two ways of placing dn next to a.                  *)
(*                                                                        *)
(*  Villain fields are differential cochains.  A differential cochain of  *)
(*  degree k is a triple x = (c, h, w): an integer k-cochain, a real       *)
(*  (k-1)-cochain and a real k-cochain; this is the differential cocycle   *)
(*  of Hopkins and Singer with the differential form replaced by a         *)
(*  cochain.                                                              *)
(*                                                                        *)
(*    d(c, h, w) = (dc, w - c - dh, dw),            d d = 0                *)
(*    x . y = (c1 cup c2, (-1)^k1 c1 cup h2 + h1 cup w2, w1 cup w2)        *)
(*    d(x . y) = dx . y + (-1)^k1 x . dy,   the product is associative     *)
(*                                                                        *)
(*  The Villain field A = (a, n) of degree p is T(A) = (-n, a / 2 Pi,      *)
(*  F / 2 Pi) of degree p + 1.  Then                                       *)
(*                                                                        *)
(*    d T(A) = (-dn, 0, -dn): the definition of F is the vanishing of the  *)
(*      middle component, and dn = 0 is the cocycle condition;             *)
(*    gauge and large gauge transformations add d(-m, -lambda / 2 Pi, 0);  *)
(*    T(A) . T(B) is T(A * B) for flat fluxes (in general the third        *)
(*      components differ by the middle component of d(T(A) . T(B))).      *)
(*                                                                        *)
(*  All identities of the product above follow from the Leibniz rule.      *)
(*  The product is graded commutative up to the homotopy                   *)
(*                                                                        *)
(*    H(x, y) = ( s c1 cup_1 c2,                                           *)
(*                (-1)^k1 h1 cup h2 - (-1)^k2 w1 cup_1 h2                  *)
(*                  - (-1)^(k1+k2) h1 cup_1 c2,                            *)
(*                s w1 cup_1 w2 ),          s = (-1)^(k1+k2+1)             *)
(*    x . y - (-1)^(k1 k2) y . x = d H(x, y) + H(dx, y) + (-1)^k1 H(x, dy) *)
(*                                                                        *)
(*  and H(T(A), T(B)) = (-m, -lambda / 2 Pi, defect / 2 Pi) with the       *)
(*  lambda, m and the defect of the commutativity above: the defect is     *)
(*  the third component of the homotopy, which a gauge transformation      *)
(*  does not have.                                                         *)
(*                                                                        *)
(*  On a three-torus with sides (L1, L2, L3) the quadratic form            *)
(*  sum of a cup da has, besides the closed 1-cochains, two zero modes for *)
(*  each momentum with p1 + p2 + p3 = Pi: 2 V / lcm(L1, L2, L3) of them if *)
(*  the lcm is even and none if all sides are odd.  These are the          *)
(*  staggered modes of arXiv:2303.06160.                                   *)
(*                                                                        *)
(*  Odd level.  With Q(x) = x cup x + x cup_1 dx (the Pontryagin square    *)
(*  plus 2 x cup_1 dx), the Chern-Simons Lagrangian L satisfies in four    *)
(*  dimensions                                                            *)
(*                                                                        *)
(*    dL = (k / 4 Pi) Q(F) - k Pi Q(n) + (k a + d phi) cup dn :            *)
(*                                                                        *)
(*  it is a primitive of the theta term at theta = 2 Pi k up to            *)
(*  k Pi Q(n), which is 2 Pi times an integer cochain only for even k.     *)
(*  Under a large gauge transformation L changes by                        *)
(*  -(k/2) d(m cup a) - k Pi q(m, n) with the integer cochain              *)
(*                                                                        *)
(*    q(m, n) = m cup n + n cup m + m cup_1 dn + dm cup m,                 *)
(*    Q(n + dm) - Q(n) = d q(m, n) + 2 m cup dn,                           *)
(*    q(m, n) + q(m', n + dm) - q(m + m', n) = - d(m' cup m),              *)
(*    q(m, n) = m cup dm + dm cup_1 n + d(m cup m + m cup_1 n) + 2 (...).  *)
(*                                                                        *)
(*  The sum of q(m, n) over a three-torus can be odd, so exp(i S) is not   *)
(*  invariant at odd level.  It is cancelled by a sign z(n), defined for   *)
(*  the integer n that are closed modulo 2, with                           *)
(*                                                                        *)
(*    z(n + dm) = z(n) (-1)^(sum of q(m, n)),                              *)
(*    z(n + n') = z(n) z(n') (-1)^(sum of n cup_1 n').                     *)
(*                                                                        *)
(*  There are eight such functions on a three-torus, labelled by their     *)
(*  values on the three unit fluxes; two of them differ by                 *)
(*  (-1)^(sum of alpha cup n) with alpha flat modulo 2.  They play the     *)
(*  role of the spin structures.  A local expression for z (Majorana       *)
(*  fermions) is not constructed here.                                     *)
(*                                                                        *)
(*  Checked in reference/villain_reference.py and                         *)
(*  reference/oddlevel_reference.py.                                      *)
(*                                                                        *)
(*  Layer: lattice gauge theory.  Depends on: Lattice.                    *)
(* ====================================================================== *)

BeginPackage["Operadica`Villain`", {"Operadica`Lattice`"}];

VillainField::usage = "VillainField[a, n] is a U(1) gauge field of degree p in the modified Villain form: a is a cochain expression of degree p, the real connection, and n a cochain expression of degree p + 1, the integer flux. Its curvature is Coboundary[a] - 2 Pi n.";

VillainConnection::usage = "VillainConnection[A] gives the connection a of the Villain field A = VillainField[a, n].";

VillainFlux::usage = "VillainFlux[A] gives the integer flux n of the Villain field A = VillainField[a, n].";

VillainDegree::usage = "VillainDegree[A] gives the degree p of the connection of the Villain field A.";

VillainCurvature::usage = "VillainCurvature[A] gives the curvature Coboundary[a] - 2 Pi n of the Villain field A = VillainField[a, n]. It does not change under VillainGaugeTransform and VillainLargeGaugeTransform.";

VillainGaugeTransform::usage = "VillainGaugeTransform[A, lam] gives the Villain field A after the gauge transformation a -> a + Coboundary[lam], for a cochain lam of degree p - 1.";

VillainLargeGaugeTransform::usage = "VillainLargeGaugeTransform[A, m] gives the Villain field A after the large gauge transformation a -> a + 2 Pi m, n -> n + Coboundary[m], for an integer cochain m of degree p.";

DeligneProduct::usage = "DeligneProduct[A, B] gives the Deligne-Beilinson product of the Villain fields A = VillainField[a, n] of degree p and B = VillainField[b, n2] of degree q: the Villain field of degree p + q + 1 with the connection Cup[a, F_B] / (2 Pi) + (-1)^p Cup[n, b] and the flux -Cup[n, n2]. For flat fields its curvature is Cup[F_A, F_B] / (2 Pi), and gauge transformations of A or B change it by gauge transformations. The connection of DeligneProduct[A, B] is the Lagrangian of the BF theory of A and B.";

VillainChernSimons::usage = "VillainChernSimons[k][A, phi] gives the Lagrangian of the U(1) Chern-Simons theory at level k for the Villain field A = VillainField[a, n] of degree 1, with the Lagrange multiplier phi (a 0-cochain) for the flatness of n: (k/2) times the connection of DeligneProduct[A, A], minus (k/2) HigherCup[1][a, Coboundary[n]], plus Cup[phi, Coboundary[n]]. It equals ModifiedVillainCS[k][a, n, phi] of Operadica`Gauge`.";

DeligneSwapGauge::usage = "DeligneSwapGauge[A, B] gives the pair {lam, m} of the gauge transformation that relates DeligneProduct[A, B] to (-1)^((p + 1) (q + 1)) times DeligneProduct[B, A], for Villain fields A = VillainField[a, n] of degree p and B = VillainField[b, n2] of degree q: lam = ((-1)^p Cup[a, b] - (-1)^q HigherCup[1][F_A, b]) / (2 Pi) - (-1)^(p + q) HigherCup[1][a, n2] and m = (-1)^(p + q) HigherCup[1][n, n2]. For flat fields, the connection of DeligneProduct[A, B] minus the sign times that of DeligneProduct[B, A] is Coboundary[lam] + 2 Pi m + DeligneSwapDefect[A, B], and the difference of the fluxes is Coboundary[m].";

DeligneSwapDefect::usage = "DeligneSwapDefect[A, B] gives -(-1)^(p + q) HigherCup[1][F_A, F_B] / (2 Pi), the gauge invariant term by which the Deligne-Beilinson product of Villain fields fails to be graded commutative up to gauge transformations. It vanishes if the curvature of A or of B vanishes.";

VillainThetaTerm::usage = "VillainThetaTerm[theta][A] gives the theta term (theta / (8 Pi^2)) Cup[F, F] of the Villain field A = VillainField[a, n], with F its curvature. For a field of degree p it is a cochain of degree 2 p + 2. It does not change under gauge transformations and large gauge transformations, and equals (theta / (4 Pi)) VillainCurvature[DeligneProduct[A, A]] + VillainWittenTerm[theta][A].";

VillainWittenTerm::usage = "VillainWittenTerm[theta][A] gives -(-1)^p (theta / (4 Pi)) (Cup[Coboundary[n], a] - Cup[a, Coboundary[n]]), the part of the theta term of A = VillainField[a, n] that couples the connection a to the monopole current Coboundary[n]. Under a -> a + Coboundary[lam] it changes by a coboundary, with the density that of an electric charge theta / (2 Pi) on the monopole (the Witten effect).";

DifferentialCochain::usage = "DifferentialCochain[c, h, w] is a differential cochain of degree k on the lattice: c is a cochain expression of degree k with integer values, h one of degree k - 1 and w one of degree k, both with real values. It is the differential cocycle of Hopkins and Singer with the differential form replaced by a cochain. Villain fields are the differential cochains given by VillainDifferentialCochain.";

DifferentialComponents::usage = "DifferentialComponents[x] gives the list {c, h, w} of the components of the differential cochain x = DifferentialCochain[c, h, w]. Linear combinations of differential cochains are formed on these lists.";

DifferentialDegree::usage = "DifferentialDegree[x] gives the degree k of the differential cochain x = DifferentialCochain[c, h, w], the degree of c.";

DifferentialCoboundary::usage = "DifferentialCoboundary[x] gives the coboundary DifferentialCochain[Coboundary[c], w - c - Coboundary[h], Coboundary[w]] of the differential cochain x = DifferentialCochain[c, h, w]. Applied twice it gives zero.";

DifferentialProduct::usage = "DifferentialProduct[x, y] gives the product DifferentialCochain[Cup[c1, c2], (-1)^k1 Cup[c1, h2] + Cup[h1, w2], Cup[w1, w2]] of the differential cochains x of degree k1 and y. It is associative and satisfies the Leibniz rule: the coboundary of the product is DifferentialProduct[dx, y] + (-1)^k1 DifferentialProduct[x, dy]. On Villain fields with flat fluxes it is DeligneProduct.";

DifferentialSwapHomotopy::usage = "DifferentialSwapHomotopy[x, y] gives the differential cochain H(x, y) of degree k1 + k2 - 1 with DifferentialProduct[x, y] - (-1)^(k1 k2) DifferentialProduct[y, x] = d H(x, y) + H(dx, y) + (-1)^k1 H(x, dy), for differential cochains x and y of degrees k1 and k2. Its components are built with HigherCup[1]. On Villain fields they are minus the m of DeligneSwapGauge, minus its lam over 2 Pi, and DeligneSwapDefect over 2 Pi.";

VillainDifferentialCochain::usage = "VillainDifferentialCochain[A] gives the Villain field A = VillainField[a, n] of degree p as the differential cochain DifferentialCochain[-n, a / (2 Pi), F / (2 Pi)] of degree p + 1, with F the curvature. Its coboundary has no middle component, and vanishes if Coboundary[n] does. Gauge transformations by lam and large gauge transformations by m add the coboundary of DifferentialCochain[-m, -lam / (2 Pi), 0].";

DifferentialCochainEqualQ::usage = "DifferentialCochainEqualQ[x, y, d] gives True if the differential cochains x and y agree identically on the d-dimensional hypercubic lattice, component by component. Each of x and y is a DifferentialCochain or a list of three components. DifferentialCochainEqualQ[x, y, {L1, ..., Ld}] compares on all cells of a periodic lattice.";

ChernSimonsZeroModeCount::usage = "ChernSimonsZeroModeCount[{L1, L2, L3}] gives the number of zero modes of the quadratic form sum of Cup[a, Coboundary[a]] on the periodic lattice with sides L1, L2, L3, beyond the closed 1-cochains (gauge transformations and flat connections). It is computed from the rank of the matrix of the form and equals 2 StaggeredMomentumCount[{L1, L2, L3}].";

ChernSimonsLargeGaugeAnomaly::usage = "ChernSimonsLargeGaugeAnomaly[m, n] gives the integer cochain q(m, n) = Cup[m, n] + Cup[n, m] + HigherCup[1][m, Coboundary[n]] + Cup[Coboundary[m], m] of degree 3, for a 1-cochain m and a 2-cochain n. Under the large gauge transformation a -> a + 2 Pi m, n -> n + Coboundary[m] the Lagrangian VillainChernSimons[k] changes by -(k/2) Coboundary[Cup[m, a]] - k Pi q(m, n), so that exp(i S) changes by (-1)^(k times the sum of q): the anomaly at odd level k. It is the descent of the four-dimensional Q(n) = Cup[n, n] + HigherCup[1][n, Coboundary[n]]: Q(n + dm) - Q(n) = Coboundary[q(m, n)] + 2 Cup[m, Coboundary[n]].";

SpinStructureSign::usage = "SpinStructureSign[{L1, L2, L3}, {s12, s13, s23}][n] gives the sign z(n) = 1 or -1 of the integer 2-cochain n on the periodic lattice with sides L1, L2, L3; n has to be closed modulo 2, otherwise the result is $Failed. The function z satisfies z(n + dm) = z(n) (-1)^(sum of ChernSimonsLargeGaugeAnomaly[m, n]) for every integer 1-cochain m, so that exp(i S) z(n) is invariant under large gauge transformations at odd level, and z(n + n') = z(n) z(n') (-1)^(sum of HigherCup[1][n, n']). The signs s12, s13, s23 (each 1 or -1) are the values of z on the unit fluxes THooftFluxCochain in the (1, 2), (1, 3) and (2, 3) planes. There are eight such functions, and they play the role of the spin structures of the three-torus. z is computed by solving n = THooftFluxCochain[c, dims] + dm modulo 2.";

StaggeredMomentumCount::usage = "StaggeredMomentumCount[{L1, ..., Ld}] gives the number of momenta p on the periodic lattice with sides L1, ..., Ld whose components add up to Pi modulo 2 Pi: L1 ... Ld / lcm(L1, ..., Ld) if the lcm is even, and 0 if all sides are odd.";

Begin["`Private`"];

VillainConnection[VillainField[a_, n_]] := a;

VillainFlux[VillainField[a_, n_]] := n;

VillainDegree[VillainField[a_, n_]] := CochainDegree[a];

VillainCurvature[VillainField[a_, n_]] := Coboundary[a] - 2 Pi n;

VillainGaugeTransform[VillainField[a_, n_], lam_] := VillainField[a + Coboundary[lam], n];

VillainLargeGaugeTransform[VillainField[a_, n_], m_] :=
  VillainField[a + 2 Pi m, n + Coboundary[m]];

DeligneProduct[VillainField[a_, n_], VillainField[b_, n2_]] :=
  With[{p = CochainDegree[a]},
    VillainField[
      (1 / (2 Pi)) Cup[a, Coboundary[b] - 2 Pi n2] + (-1)^p Cup[n, b],
      -Cup[n, n2]
    ]
  ];

VillainChernSimons[k_][VillainField[a_, n_], phi_] :=
  (k / 2) VillainConnection[DeligneProduct[VillainField[a, n], VillainField[a, n]]] -
    (k / 2) HigherCup[1][a, Coboundary[n]] +
    Cup[phi, Coboundary[n]];

DeligneSwapGauge[VillainField[a_, n_], VillainField[b_, n2_]] :=
  With[{p = CochainDegree[a], q = CochainDegree[b]},
    {
      (1 / (2 Pi)) ((-1)^p Cup[a, b] - (-1)^q HigherCup[1][Coboundary[a] - 2 Pi n, b]) -
        (-1)^(p + q) HigherCup[1][a, n2],
      (-1)^(p + q) HigherCup[1][n, n2]
    }
  ];

DeligneSwapDefect[VillainField[a_, n_], VillainField[b_, n2_]] :=
  With[{p = CochainDegree[a], q = CochainDegree[b]},
    -((-1)^(p + q) / (2 Pi)) HigherCup[1][Coboundary[a] - 2 Pi n, Coboundary[b] - 2 Pi n2]
  ];

VillainThetaTerm[theta_][VillainField[a_, n_]] :=
  (theta / (8 Pi^2)) Cup[Coboundary[a] - 2 Pi n, Coboundary[a] - 2 Pi n];

VillainWittenTerm[theta_][VillainField[a_, n_]] :=
  With[{p = CochainDegree[a]},
    -((-1)^p theta / (4 Pi)) (Cup[Coboundary[n], a] - Cup[a, Coboundary[n]])
  ];

(* ---------------------------------------------------------------------- *)
(* differential cochains                                                  *)
(* ---------------------------------------------------------------------- *)

dcList[DifferentialCochain[c_, h_, w_]] := {c, h, w};
dcList[x : {_, _, _}] := x;

DifferentialComponents[x_DifferentialCochain] := dcList[x];

DifferentialDegree[DifferentialCochain[c_, h_, w_]] := CochainDegree[c];

DifferentialCoboundary[DifferentialCochain[c_, h_, w_]] :=
  DifferentialCochain[Coboundary[c], w - c - Coboundary[h], Coboundary[w]];

DifferentialProduct[DifferentialCochain[c1_, h1_, w1_], DifferentialCochain[c2_, h2_, w2_]] :=
  With[{k1 = CochainDegree[c1]},
    DifferentialCochain[
      Cup[c1, c2],
      (-1)^k1 Cup[c1, h2] + Cup[h1, w2],
      Cup[w1, w2]
    ]
  ];

DifferentialSwapHomotopy[DifferentialCochain[c1_, h1_, w1_], DifferentialCochain[c2_, h2_, w2_]] :=
  With[{k1 = CochainDegree[c1], k2 = CochainDegree[c2]},
    DifferentialCochain[
      (-1)^(k1 + k2 + 1) HigherCup[1][c1, c2],
      (-1)^k1 Cup[h1, h2] - (-1)^k2 HigherCup[1][w1, h2] - (-1)^(k1 + k2) HigherCup[1][h1, c2],
      (-1)^(k1 + k2 + 1) HigherCup[1][w1, w2]
    ]
  ];

VillainDifferentialCochain[VillainField[a_, n_]] :=
  DifferentialCochain[-n, (1 / (2 Pi)) a, (1 / (2 Pi)) (Coboundary[a] - 2 Pi n)];

DifferentialCochainEqualQ[x_, y_, where_] :=
  With[{u = dcList[x], v = dcList[y]},
    AllTrue[Range[3], Function[i, CochainEqualQ[u[[i]], v[[i]], where]]]
  ];

(* ---------------------------------------------------------------------- *)
(* zero modes of the Chern-Simons quadratic form                          *)
(* ---------------------------------------------------------------------- *)

StaggeredMomentumCount[dims : {__Integer?Positive}] :=
  With[{l = LCM @@ dims},
    If[EvenQ[l], Quotient[Times @@ dims, l], 0]
  ];

(* the form is sum of a cup da with one variable for each link; its matrix
   is the matrix of second derivatives *)

ChernSimonsZeroModeCount[dims : {_Integer?Positive, _Integer?Positive, _Integer?Positive}] :=
  Module[{links, vars, field, poly, hess},
    links = LCells[dims, 1];
    vars = Table[csVar[i], {i, 1, Length[links]}];
    field = PeriodicCochain[1, dims,
      Association[Table[{links[[i, 1]], links[[i, 2]]} -> vars[[i]], {i, 1, Length[links]}]]
    ];
    poly = Expand[CochainIntegrate[Cup[field, Coboundary[field]], dims]];
    hess = D[poly, {vars, 2}];
    Length[vars] - MatrixRank[hess] - (Times @@ dims + 2)
  ];

(* ---------------------------------------------------------------------- *)
(* odd level: the anomaly of the large gauge transformations, and the     *)
(* signs that cancel it on a three-torus                                  *)
(* ---------------------------------------------------------------------- *)

ChernSimonsLargeGaugeAnomaly[m_, n_] :=
  Cup[m, n] + Cup[n, m] + HigherCup[1][m, Coboundary[n]] + Cup[Coboundary[m], m];

(* the antisymmetric matrix with the entries c = {c12, c13, c23} *)
ssMatrix[c_List] :=
  {{0, c[[1]], c[[2]]}, {-c[[1]], 0, c[[3]]}, {-c[[2]], -c[[3]], 0}};

(* the column of the first 1 in a row of a row-reduced matrix, or 0 *)
ssPivot[row_List] := SelectFirst[Range[Length[row]], Function[j, row[[j]] === 1], 0];

(* an integer 1-cochain m with dm = t modulo 2 on the periodic lattice, or
   $Failed if there is none: row reduction modulo 2 of the matrix of the
   coboundary, with the free variables set to 0 *)
ssSolve[t_, dims_List] :=
  Module[{links, plaqs, nl, vars, field, mat, rhs, red, pivots, rows},
    links = LCells[dims, 1];
    plaqs = LCells[dims, 2];
    nl = Length[links];
    vars = Table[ssVar[i], {i, 1, nl}];
    field = PeriodicCochain[1, dims,
      Association[Table[{links[[i, 1]], links[[i, 2]]} -> vars[[i]], {i, 1, nl}]]
    ];
    mat = D[
      Map[Function[cell, CochainValue[Coboundary[field], cell[[1]], cell[[2]]]], plaqs],
      {vars}
    ];
    rhs = Map[Function[cell, Mod[CochainValue[t, cell[[1]], cell[[2]]], 2]], plaqs];
    red = RowReduce[Join[mat, Map[List, rhs], 2], Modulus -> 2];
    pivots = Map[ssPivot, red];
    rows = Select[Range[Length[red]], Function[i, 1 <= pivots[[i]] <= nl]];
    If[MemberQ[pivots, nl + 1],
      $Failed,
      PeriodicCochain[1, dims,
        Association[
          Map[
            Function[i,
              {links[[pivots[[i]], 1]], links[[pivots[[i]], 2]]} -> red[[i, nl + 1]]
            ],
            rows
          ]
        ]
      ]
    ]
  ];

SpinStructureSign[
    dims : {_Integer?Positive, _Integer?Positive, _Integer?Positive},
    signs : {(1 | -1), (1 | -1), (1 | -1)}
  ][n_] :=
  Module[{flux, cls, rep, m, gens, pair},
    flux = THooftFlux[n, dims];
    cls = Mod[{flux[[1, 2]], flux[[1, 3]], flux[[2, 3]]}, 2];
    rep = THooftFluxCochain[ssMatrix[cls], dims];
    m = ssSolve[n - rep, dims];
    If[m === $Failed,
      $Failed,
      gens = Map[Function[u, THooftFluxCochain[ssMatrix[u], dims]], IdentityMatrix[3]];
      pair = Function[{i, j},
        cls[[i]] cls[[j]] CochainIntegrate[HigherCup[1][gens[[i]], gens[[j]]], dims]
      ];
      (Times @@ (signs^cls)) *
        (-1)^(pair[1, 2] + pair[1, 3] + pair[2, 3] +
          CochainIntegrate[ChernSimonsLargeGaugeAnomaly[m, rep], dims])
    ]
  ];

End[];

EndPackage[];
