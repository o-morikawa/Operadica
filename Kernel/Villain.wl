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
(*  For m along the direction rho and n on the plaquettes that contain     *)
(*  rho (the fluxes whose dual curves lie in a plane orthogonal to rho),   *)
(*  m cup n + n cup m + dm cup m = 0.  On such planar fluxes z depends     *)
(*  only on the class of the dual curve in the plane: z = 1 if it is       *)
(*  trivial, and z = (-1)^e with e a quadratic refinement of the           *)
(*  intersection form of the two-torus.  By Johnson's theorem this is a    *)
(*  spin structure on each coordinate two-torus: the fermion is periodic   *)
(*  in the direction rho if and only if s_(mu nu) = -1, and on a curve     *)
(*  that is not contractible in the plane z is minus the holonomy.         *)
(*                                                                        *)
(*  Cech-de Rham form.  The lattice Deligne-Beilinson cohomology of        *)
(*  Y. Ikeda, arXiv:2601.15939, has the unit cubes as patches; a class of  *)
(*  degree 2 on a three-torus is a triple (A_p, Lambda_pq, N_pqr) with     *)
(*  A_q - A_p = d Lambda_pq, Lambda_qr - Lambda_pr + Lambda_pq = - N_pqr    *)
(*  and N a Cech cocycle.  A flat Villain field (a, n) gives such a triple *)
(*  by descent: with m_p the integer 1-cochain on the cube p with          *)
(*  d m_p = n (zero on a tree of links),                                   *)
(*                                                                        *)
(*    A_p = a / 2 Pi - m_p,                                                *)
(*    Lambda_pq = the sum of m_p - m_q along a path in the intersection,   *)
(*    N_pqr = - (Lambda_qr - Lambda_pr + Lambda_pq).                       *)
(*                                                                        *)
(*  Lambda and N are functions of the flux n alone, and the class of N is  *)
(*  the Chern class: its sums over the triangulated coordinate tori of     *)
(*  the nerve are the fluxes of n.                                         *)
(*                                                                        *)
(*  The star product of two triples, A cup dA', Lambda cup dA', N A',      *)
(*  N Lambda', is summed over a chain of cells with their cubes that is    *)
(*  built by cones (the last cube of a term is the cube based at the base  *)
(*  point of its cell).  The sum is defined modulo 1.  On the triples of   *)
(*  flat Villain fields it is the sum of the connection of DeligneProduct  *)
(*  over 2 Pi, term by term: for the square, the Chern-Simons action at    *)
(*  level 2.                                                               *)
(*                                                                        *)
(*  Checked in reference/villain_reference.py,                            *)
(*  reference/oddlevel_reference.py, reference/cech_reference.py and      *)
(*  reference/star_reference.py.                                          *)
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

SpinStructureSign::usage = "SpinStructureSign[{L1, L2, L3}, {s12, s13, s23}][n] gives the sign z(n) = 1 or -1 of the integer 2-cochain n on the periodic lattice with sides L1, L2, L3; n has to be closed modulo 2, otherwise the result is $Failed. The function z satisfies z(n + dm) = z(n) (-1)^(sum of ChernSimonsLargeGaugeAnomaly[m, n]) for every integer 1-cochain m, so that exp(i S) z(n) is invariant under large gauge transformations at odd level, and z(n + n') = z(n) z(n') (-1)^(sum of HigherCup[1][n, n']). The signs s12, s13, s23 (each 1 or -1) are the values of z on the unit fluxes THooftFluxCochain in the (1, 2), (1, 3) and (2, 3) planes. There are eight such functions, and they play the role of the spin structures of the three-torus: on the fluxes in a coordinate plane z is 1 on contractible curves and minus the holonomy of the spin structure otherwise, see SpinStructureHolonomy. z is computed by solving n = THooftFluxCochain[c, dims] + dm modulo 2.";

SpinStructureHolonomy::usage = "SpinStructureHolonomy[{s12, s13, s23}] gives {h1, h2, h3} = {-s23, -s13, -s12}: the boundary conditions of the fermion in the directions 1, 2, 3 for the spin structure of the three-torus that SpinStructureSign[dims, {s12, s13, s23}] defines, 1 for periodic and -1 for antiperiodic. For a flux n on the plaquettes that contain the direction rho, at one value of the coordinate in that direction, the dual curve lies in a plane orthogonal to rho, and SpinStructureSign gives 1 if the curve is contractible in that plane and minus the product of the h of the directions it winds around an odd number of times otherwise. This is the quadratic form of a spin structure on the two-torus (Johnson): it takes the value -1 on all three nonzero classes exactly if the fermion is periodic in both directions.";

VillainPatchPrimitive::usage = "VillainPatchPrimitive[n, {L1, L2, L3}][p, x, mu] gives the value on the link (x; mu) of the integer 1-cochain m_p on the unit cube with the lowest corner p, with Coboundary[m_p] = n on the plaquettes of that cube, for a closed integer 2-cochain n on the periodic lattice with sides L1, L2, L3 >= 3. m_p vanishes on the tree of the links (.; 1), ((0, ., .); 2), ((0, 0, .); 3) of the cube. The result is $Failed if the link is not in the cube.";

CechDeRhamConnection::usage = "CechDeRhamConnection[A, dims][p, x, mu] gives the value on the link (x; mu) of the local connection A_p = a / (2 Pi) - m_p of the flat Villain field A = VillainField[a, n] on the unit cube with the lowest corner p, with m_p = VillainPatchPrimitive[n, dims]. Its coboundary on the cube is the curvature F / (2 Pi). Together with CechDeRhamTransition and CechDeRhamChern it is a cocycle of Cech-de Rham type for the cover of the three-torus by the unit cubes, in the form of the lattice Deligne-Beilinson cohomology of arXiv:2601.15939: A_q - A_p = d Lambda_pq, Lambda_qr - Lambda_pr + Lambda_pq = - N_pqr, and N is a Cech cocycle.";

CechDeRhamTransition::usage = "CechDeRhamTransition[A, dims][p, q, x] gives the value at the site x of the transition function Lambda_pq of the flat Villain field A on the intersection of the unit cubes with the lowest corners p and q: the sum of m_p - m_q along a path from the lowest corner of the intersection to x. It is an integer, it depends on the flux n only, and A_q - A_p = d Lambda_pq on the links of the intersection. The result is $Failed if x is not in both cubes.";

CechDeRhamChern::usage = "CechDeRhamChern[A, dims][p, q, r] gives the integer N_pqr = -(Lambda_qr - Lambda_pr + Lambda_pq) of the flat Villain field A for three unit cubes with a common point, evaluated at the lowest corner of their intersection (it is the same at every common site). N is a Cech 2-cocycle on the nerve of the cover by the cubes, and its class is the Chern class of the field. The result is $Failed if the three cubes have no common point.";

CechDeRhamCocycleQ::usage = "CechDeRhamCocycleQ[A, {L1, L2, L3}] gives a list of three truth values for the Villain field A = VillainField[a, n] on the periodic lattice: whether Coboundary[m_p] = n on every unit cube (this fails if n is not closed), whether A_q - A_p = d Lambda_pq on the links of every intersection of two cubes, and whether Lambda_qr - Lambda_pr + Lambda_pq is the same integer -N_pqr at every common site of three cubes.";

CechDeRhamChernNumbers::usage = "CechDeRhamChernNumbers[A, {L1, L2, L3}] gives the antisymmetric matrix of the Chern numbers of the Cech cocycle N = CechDeRhamChern[A, dims]: the entry (mu, nu), mu < nu, is minus the sum of N(p, p + e_mu, p + e_mu + e_nu) - N(p, p + e_nu, p + e_mu + e_nu) over the cubes p of a coordinate plane, the pairing of N with the triangulated two-torus in the nerve. It equals THooftFlux[n, dims].";

CechDeRhamTriple::usage = "CechDeRhamTriple[A, {L1, L2, L3}] gives the list {CechDeRhamConnection[A, dims], CechDeRhamTransition[A, dims], CechDeRhamChern[A, dims]} of the flat Villain field A: the three functions conn[p, x, mu], lam[p, q, x], nn[p, q, r] of a cocycle of Cech-de Rham type for the cover of the three-torus by the unit cubes.";

CechDeRhamFundamentalCycle::usage = "CechDeRhamFundamentalCycle[{L1, L2, L3}] gives the chain over which a cocycle of Cech-de Rham type of degree 3 is summed on the periodic lattice with sides L1, L2, L3 >= 3, as an association: the key i = 3, 2, 1, 0 has the list of the terms {c, x, dirs, {p0, ..., pj}}, j = 3 - i, the cell (x; dirs) of dimension i in the cubes p0, ..., pj with the coefficient c = 1 or -1. Key 3: every cube x in itself. Key 2: the plaquette at x normal to mu in the cubes x - e_mu, x with the coefficient (-1)^(mu - 1). Key 1: two triples of cubes for every link. Key 0: six quadruples of cubes for every site. The last cube of every term is the cube with the lowest corner x. With b the boundary of the cells and bc the Cech boundary on ordered tuples, b s3 + bc s2 = 0, b s2 - bc s1 = 0 and b s1 + bc s0 = 0.";

CechDeRhamStarIntegral::usage = "CechDeRhamStarIntegral[{conn1, lam1, nn1}, {conn2, lam2, nn2}, {L1, L2, L3}] gives the list of the four contributions to the integral of the star product of two cocycles of Cech-de Rham type over CechDeRhamFundamentalCycle: the sums of A_p cup dA'_p over the cubes, of Lambda_pq cup dA'_q over the plaquettes, of N_pqr A'_r over the links and of N_pqr Lambda'_rs over the sites (the product of the lattice Deligne-Beilinson cohomology of arXiv:2601.15939). Their total does not change under CechDeRhamGaugeTransform of either factor with mm = 0, and changes by an integer with mm not 0: it is defined modulo 1. CechDeRhamStarIntegral[A, B, dims] for flat Villain fields A = VillainField[a, n] and B = VillainField[b, n2] uses CechDeRhamTriple; then the four contributions are the sum of Cup[a, F_B] / (2 Pi)^2, 0, minus the sum of Cup[n, b] / (2 Pi), and 0, and the total is the sum of VillainConnection[DeligneProduct[A, B]] / (2 Pi). For A = B it is the sum of VillainChernSimons[2] / (2 Pi): the weight at the even level 2 j is Exp[2 Pi I j (the total)]. Half of the total is not defined modulo 1 (odd level).";

CechDeRhamGaugeTransform::usage = "CechDeRhamGaugeTransform[{conn, lam, nn}, xi, mm, {L1, L2, L3}] gives the cocycle of Cech-de Rham type after the gauge transformation A_p -> A_p + d xi_p, Lambda_pq -> Lambda_pq + xi_q - xi_p - mm_pq, N_pqr -> N_pqr + mm_qr - mm_pr + mm_pq, for a function xi[p, x] on the sites x of the cube p and an alternating integer function mm[p, q] of two cubes with a common point.";

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

SpinStructureHolonomy[{s12 : (1 | -1), s13 : (1 | -1), s23 : (1 | -1)}] := {-s23, -s13, -s12};

(* ---------------------------------------------------------------------- *)
(* a flat Villain field as a Cech-de Rham cocycle for the cover of the     *)
(* three-torus by the unit cubes; a cube is labelled by its lowest corner  *)
(* ---------------------------------------------------------------------- *)

VillainPatchPrimitive[n_, dims : {_Integer, _Integer, _Integer}][p_List, x_List, mu_Integer] :=
  With[{r = Mod[x - p, dims]},
    Which[
      ! (SubsetQ[{0, 1}, r] && MemberQ[{1, 2, 3}, mu] && r[[mu]] === 0), $Failed,
      mu === 1, 0,
      mu === 2, If[r[[1]] === 1, CochainValue[n, Mod[p + {0, 0, r[[3]]}, dims], {1, 2}], 0],
      r[[1]] === 0 && r[[2]] === 0, 0,
      r[[1]] === 1 && r[[2]] === 0, CochainValue[n, Mod[p, dims], {1, 3}],
      r[[1]] === 0 && r[[2]] === 1, CochainValue[n, Mod[p, dims], {2, 3}],
      True, CochainValue[n, Mod[p + {0, 1, 0}, dims], {1, 3}] + CochainValue[n, Mod[p, dims], {2, 3}]
    ]
  ];

(* the lowest corner of the intersection of the cubes with the lowest
   corners ps, or $Failed if they have no common point *)
cdrCorner[ps_List, dims_List] :=
  With[{ds = Map[Function[q, Mod[q - First[ps], dims, -1]], ps]},
    If[Max[Abs[ds]] > 1 || AnyTrue[Transpose[ds], Function[col, Max[col] - Min[col] > 1]],
      $Failed,
      Mod[First[ps] + Map[Max, Transpose[ds]], dims]
    ]
  ];

(* the sites common to the cubes ps *)
cdrSites[ps_List, dims_List] :=
  With[{c = cdrCorner[ps, dims]},
    If[c === $Failed,
      {},
      Select[
        Map[Function[r, Mod[c + r, dims]], Tuples[{0, 1}, 3]],
        Function[x, AllTrue[ps, Function[p, SubsetQ[{0, 1}, Mod[x - p, dims]]]]]
      ]
    ]
  ];

CechDeRhamConnection[VillainField[a_, n_], dims : {_Integer, _Integer, _Integer}][p_List, x_List, mu_Integer] :=
  With[{m = VillainPatchPrimitive[n, dims][p, x, mu]},
    If[m === $Failed, $Failed, CochainValue[a, Mod[x, dims], {mu}] / (2 Pi) - m]
  ];

CechDeRhamTransition[VillainField[a_, n_], dims : {_Integer, _Integer, _Integer}][p_List, q_List, x_List] :=
  With[{c = cdrCorner[{p, q}, dims], m = VillainPatchPrimitive[n, dims]},
    If[c === $Failed || ! MemberQ[cdrSites[{p, q}, dims], Mod[x, dims]],
      $Failed,
      With[{r = Mod[x - c, dims]},
        With[{y2 = Mod[c + {r[[1]], 0, 0}, dims], y3 = Mod[c + {r[[1]], r[[2]], 0}, dims]},
          If[r[[1]] === 1, m[p, c, 1] - m[q, c, 1], 0] +
            If[r[[2]] === 1, m[p, y2, 2] - m[q, y2, 2], 0] +
            If[r[[3]] === 1, m[p, y3, 3] - m[q, y3, 3], 0]
        ]
      ]
    ]
  ];

CechDeRhamChern[aa_VillainField, dims : {_Integer, _Integer, _Integer}][p_List, q_List, r_List] :=
  With[{c = cdrCorner[{p, q, r}, dims], lam = CechDeRhamTransition[aa, dims]},
    If[c === $Failed, $Failed, -(lam[q, r, c] - lam[p, r, c] + lam[p, q, c])]
  ];

(* the eight cubes that contain the site x *)
cdrCubesAt[x_List, dims_List] := Map[Function[r, Mod[x - r, dims]], Tuples[{0, 1}, 3]];

CechDeRhamCocycleQ[aa : VillainField[a_, n_], dims : {_Integer, _Integer, _Integer}] :=
  With[{
      pts = Tuples[Map[Function[len, Range[0, len - 1]], dims]],
      m = VillainPatchPrimitive[n, dims],
      conn = CechDeRhamConnection[aa, dims],
      lam = CechDeRhamTransition[aa, dims],
      nn = CechDeRhamChern[aa, dims]
    },
    {
      AllTrue[pts,
        Function[p,
          AllTrue[{{1, 2, 3}, {1, 3, 2}, {2, 3, 1}},
            Function[pl,
              AllTrue[{0, 1},
                Function[t,
                  With[{
                      mu = pl[[1]], nu = pl[[2]],
                      x = Mod[p + t UnitVector[3, pl[[3]]], dims]
                    },
                    m[p, Mod[x + UnitVector[3, mu], dims], nu] - m[p, x, nu] -
                        m[p, Mod[x + UnitVector[3, nu], dims], mu] + m[p, x, mu] ===
                      CochainValue[n, x, {mu, nu}]
                  ]
                ]
              ]
            ]
          ]
        ]
      ],
      AllTrue[pts,
        Function[x,
          AllTrue[Subsets[cdrCubesAt[x, dims], {2}],
            Function[pq,
              With[{sites = cdrSites[pq, dims]},
                AllTrue[sites,
                  Function[y,
                    AllTrue[{1, 2, 3},
                      Function[mu,
                        With[{y2 = Mod[y + UnitVector[3, mu], dims]},
                          ! MemberQ[sites, y2] ||
                            Expand[conn[pq[[2]], y, mu] - conn[pq[[1]], y, mu]] ===
                              lam[pq[[1]], pq[[2]], y2] - lam[pq[[1]], pq[[2]], y]
                        ]
                      ]
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]
      ],
      AllTrue[pts,
        Function[x,
          AllTrue[Subsets[cdrCubesAt[x, dims], {3}],
            Function[pqr,
              Union[
                  Map[
                    Function[y,
                      lam[pqr[[2]], pqr[[3]], y] - lam[pqr[[1]], pqr[[3]], y] + lam[pqr[[1]], pqr[[2]], y]
                    ],
                    cdrSites[pqr, dims]
                  ]
                ] === {-nn[pqr[[1]], pqr[[2]], pqr[[3]]]}
            ]
          ]
        ]
      ]
    }
  ];

CechDeRhamChernNumbers[aa_VillainField, dims : {_Integer, _Integer, _Integer}] :=
  With[{
      nn = CechDeRhamChern[aa, dims],
      pts = Tuples[Map[Function[len, Range[0, len - 1]], dims]]
    },
    With[{
        plane = Function[{mu, nu},
          -Total[
            Map[
              Function[p,
                With[{
                    pm = Mod[p + UnitVector[3, mu], dims],
                    pn = Mod[p + UnitVector[3, nu], dims],
                    pmn = Mod[p + UnitVector[3, mu] + UnitVector[3, nu], dims]
                  },
                  nn[p, pm, pmn] - nn[p, pn, pmn]
                ]
              ],
              Select[pts, Function[p, p[[6 - mu - nu]] === 0]]
            ]
          ]
        ]
      },
      {
        {0, plane[1, 2], plane[1, 3]},
        {-plane[1, 2], 0, plane[2, 3]},
        {-plane[1, 3], -plane[2, 3], 0}
      }
    ]
  ];

(* ---------------------------------------------------------------------- *)
(* the star product of two cocycles of Cech-de Rham type and its integral  *)
(* ---------------------------------------------------------------------- *)

CechDeRhamTriple[aa_VillainField, dims : {_Integer, _Integer, _Integer}] :=
  {CechDeRhamConnection[aa, dims], CechDeRhamTransition[aa, dims], CechDeRhamChern[aa, dims]};

(* the cube with the lowest corner x - e_mu1 - e_mu2 - ... *)
cdrDown[x_List, mus_List, dims_List] :=
  Mod[x - Total[Map[Function[dir, UnitVector[3, dir]], mus]], dims];

cdrOthers[mu_Integer] := DeleteCases[{1, 2, 3}, mu];

(* the two terms of the chain on the link (x; mu) *)
cdrLinkTerms[x_List, mu_Integer, dims_List] :=
  With[{al = First[cdrOthers[mu]], be = Last[cdrOthers[mu]], sg = (-1)^(mu - 1)},
    With[{low = cdrDown[x, {al, be}, dims]},
      {
        {sg, x, {mu}, {low, cdrDown[x, {be}, dims], x}},
        {-sg, x, {mu}, {low, cdrDown[x, {al}, dims], x}}
      }
    ]
  ];

(* the two terms of the chain at the site x from the link (x - e_mu; mu) *)
cdrSiteTerms[x_List, mu_Integer, dims_List] :=
  Map[
    Function[term, {term[[1]], x, {}, Append[term[[4]], x]}],
    cdrLinkTerms[cdrDown[x, {mu}, dims], mu, dims]
  ];

CechDeRhamFundamentalCycle[dims : {_Integer, _Integer, _Integer}] :=
  With[{sites = Tuples[Map[Function[len, Range[0, len - 1]], dims]]},
    Association[
      3 -> Map[Function[x, {1, x, {1, 2, 3}, {x}}], sites],
      2 -> Flatten[
        Map[
          Function[x,
            Map[Function[mu, {(-1)^(mu - 1), x, cdrOthers[mu], {cdrDown[x, {mu}, dims], x}}], {1, 2, 3}]
          ],
          sites
        ],
        1
      ],
      1 -> Flatten[
        Map[Function[x, Map[Function[mu, cdrLinkTerms[x, mu, dims]], {1, 2, 3}]], sites],
        2
      ],
      0 -> Flatten[
        Map[Function[x, Map[Function[mu, cdrSiteTerms[x, mu, dims]], {1, 2, 3}]], sites],
        2
      ]
    ]
  ];

(* the coboundary of the local connection on the plaquette (x; al, be) *)
cdrCurvature[conn_, dims_List][p_List, x_List, {al_Integer, be_Integer}] :=
  conn[p, x, al] + conn[p, Mod[x + UnitVector[3, al], dims], be] -
    conn[p, Mod[x + UnitVector[3, be], dims], al] - conn[p, x, be];

CechDeRhamStarIntegral[{conn1_, lam1_, nn1_}, {conn2_, lam2_, nn2_}, dims : {_Integer, _Integer, _Integer}] :=
  With[{cyc = CechDeRhamFundamentalCycle[dims], curv = cdrCurvature[conn2, dims]},
    {
      Total[
        Map[
          Function[term,
            With[{x = term[[2]], p = term[[4, 1]]},
              term[[1]] (
                conn1[p, x, 1] curv[p, Mod[x + UnitVector[3, 1], dims], {2, 3}] -
                  conn1[p, x, 2] curv[p, Mod[x + UnitVector[3, 2], dims], {1, 3}] +
                  conn1[p, x, 3] curv[p, Mod[x + UnitVector[3, 3], dims], {1, 2}]
              )
            ]
          ],
          Lookup[cyc, 3]
        ]
      ],
      Total[
        Map[
          Function[term,
            term[[1]] lam1[term[[4, 1]], term[[4, 2]], term[[2]]] curv[term[[4, 2]], term[[2]], term[[3]]]
          ],
          Lookup[cyc, 2]
        ]
      ],
      Total[
        Map[
          Function[term,
            term[[1]] nn1[term[[4, 1]], term[[4, 2]], term[[4, 3]]] conn2[term[[4, 3]], term[[2]], term[[3, 1]]]
          ],
          Lookup[cyc, 1]
        ]
      ],
      Total[
        Map[
          Function[term,
            term[[1]] nn1[term[[4, 1]], term[[4, 2]], term[[4, 3]]] lam2[term[[4, 3]], term[[4, 4]], term[[2]]]
          ],
          Lookup[cyc, 0]
        ]
      ]
    }
  ];

CechDeRhamStarIntegral[aa_VillainField, bb_VillainField, dims : {_Integer, _Integer, _Integer}] :=
  CechDeRhamStarIntegral[CechDeRhamTriple[aa, dims], CechDeRhamTriple[bb, dims], dims];

CechDeRhamGaugeTransform[{conn_, lam_, nn_}, xi_, mm_, dims : {_Integer, _Integer, _Integer}] :=
  {
    Function[{p, x, mu}, conn[p, x, mu] + xi[p, Mod[x + UnitVector[3, mu], dims]] - xi[p, x]],
    Function[{p, q, x}, lam[p, q, x] + xi[q, x] - xi[p, x] - mm[p, q]],
    Function[{p, q, r}, nn[p, q, r] + mm[q, r] - mm[p, r] + mm[p, q]]
  };

End[];

EndPackage[];
