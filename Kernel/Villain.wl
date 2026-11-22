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

End[];

EndPackage[];
