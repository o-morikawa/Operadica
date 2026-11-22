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
(*  Checked in reference/villain_reference.py.                            *)
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

End[];

EndPackage[];
