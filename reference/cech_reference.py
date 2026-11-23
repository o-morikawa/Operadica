"""
A flat Villain field as a Cech-de Rham cocycle, and background fields of the 1-form symmetry
(Operadica`Villain`: VillainPatchPrimitive, CechDeRhamConnection, CechDeRhamTransition,
CechDeRhamChern, CechDeRhamCocycleQ, CechDeRhamChernNumbers; Operadica`Bridge`:
ChernSimonsOneFormAnomalyQ).

Part 1.  The lattice Deligne-Beilinson cohomology of Y. Ikeda, arXiv:2601.15939, is of
Cech-de Rham type: the patches are the unit cubes of the cubic lattice (centred at the points
of the dual lattice), and a class of degree 2 on a three-torus is a triple

    A_p       a real 1-cochain on the links of the cube p,
    Lambda_pq a real 0-cochain on the sites of the intersection of the cubes p and q,
    N_pqr     an integer for three cubes with a common point,

with   A_q - A_p = d Lambda_pq,
       Lambda_qr - Lambda_pr + Lambda_pq = - N_pqr,
       N_qrs - N_prs + N_pqs - N_pqr = 0.

(Conventions as in eqs. (4.14)-(4.17), (5.4), (7.48) of that paper, read from its text; the
connection has period 1 there.)  A flat Villain field (a, n), dn = 0, gives such a triple by
descent.  A cube is labelled by its lowest corner p, and x - p is taken in {0, 1}^3.

    m_p        the integer 1-cochain on the cube p with d m_p = n there that vanishes on the
               tree of the links (.; 1), (0, ., .; 2), (0, 0, .; 3):
                   m_p((1, 0, r3); 2) = n(p + r3 e3; 12),
                   m_p((1, 0, 0); 3) = n(p; 13),      m_p((0, 1, 0); 3) = n(p; 23),
                   m_p((1, 1, 0); 3) = n(p + e2; 13) + n(p; 23).
    A_p        = a / 2 pi - m_p
    Lambda_pq  the sum of m_p - m_q along a path from the lowest corner of the intersection
    N_pqr      = - (Lambda_qr - Lambda_pr + Lambda_pq), the same at every common site

The three conditions hold, d A_p = F / 2 pi, and the class of N is the Chern class: summed over
the two triangles (p, p + e_mu, p + e_mu + e_nu) and (p, p + e_nu, p + e_mu + e_nu) of the
nerve for the cubes p of a coordinate plane, N gives minus the flux of n through that plane.
Lambda and N are functions of n alone: this is why the modified Villain form has no
transition functions.  A gauge transformation a -> a + d lambda changes A_p by
d(lambda / 2 pi) and leaves Lambda and N unchanged.

Part 2.  Background fields.  With Q(x) = x cup x + x cup_1 dx:

    Q(n + b / N) = Q(n) + X(n, b) / N + Q(b) / N^2,
    X(n, b) = n cup b + b cup n + n cup_1 db + b cup_1 dn
            = 2 b cup n - d(n cup_1 b) + dn cup_1 b + 2 n cup_1 db + b cup_1 dn,
    L_k(a, n, phi) = L_(k N^2)(a / N, n / N, N phi).

So the Lagrangian at level K with the flux n + B / N (B a Z_N background field of degree 2)
has the inflow term K pi Q(B) / N^2 = 2 pi (K / 2 N^2) Q(B), and on flat Z_N fields
(K / 2 N^2) Q(B) = (p / 2 N) P(B) modulo 1 with p = K / N: the class of the line of charge
K / N, which has the spin K / (2 N^2).

Run:  python3 reference/cech_reference.py
"""

import itertools
import random
import sys
from fractions import Fraction as Fr

import cubical_reference as cr
import simplicial_reference as sr
from oddlevel_reference import Torus, thooft, flux, add, qsquare, psquare, PLANES
from villain_reference import Calc, chern_simons


# --------------------------------------------------------------------------
# part 1: the Cech-de Rham cocycle of a flat Villain field
# --------------------------------------------------------------------------

def addv(x, v, dims):
    return tuple((a + b) % L for a, b, L in zip(x, v, dims))


def rel(x, p, dims):
    return tuple((a - b) % L for a, b, L in zip(x, p, dims))


def unit(mu):
    return tuple(int(i == mu - 1) for i in range(3))


def primitive(n, dims):
    """VillainPatchPrimitive: m(p, x, mu)"""
    def m(p, x, mu):
        r = rel(x, p, dims)
        assert all(c in (0, 1) for c in r) and r[mu - 1] == 0, (p, x, mu)
        if mu == 1:
            return 0
        if mu == 2:
            return n(addv(p, (0, 0, r[2]), dims), (1, 2)) if r[0] == 1 else 0
        if (r[0], r[1]) == (0, 0):
            return 0
        if (r[0], r[1]) == (1, 0):
            return n(p, (1, 3))
        if (r[0], r[1]) == (0, 1):
            return n(p, (2, 3))
        return n(addv(p, (0, 1, 0), dims), (1, 3)) + n(p, (2, 3))
    return m


def corner(ps, dims):
    """the lowest corner of the intersection of the cubes ps, or None (sides >= 3)"""
    c = []
    for i, L in enumerate(dims):
        ds = [(p[i] - ps[0][i] + 1) % L - 1 for p in ps]
        if max(abs(d) for d in ds) > 1 or max(ds) - min(ds) > 1:
            return None
        c.append((ps[0][i] + max(ds)) % L)
    return tuple(c)


def common_sites(ps, dims):
    c = corner(ps, dims)
    if c is None:
        return []
    out = [addv(c, r, dims) for r in itertools.product((0, 1), repeat=3)]
    return [x for x in out if all(all(v in (0, 1) for v in rel(x, p, dims)) for p in ps)]


def transition(m, dims):
    """CechDeRhamTransition: Lambda(p, q, x)"""
    def lam(p, q, x):
        c = corner([p, q], dims)
        r = rel(x, c, dims)
        tot, y = 0, c
        for mu in (1, 2, 3):
            if r[mu - 1] == 1:
                tot += m(p, y, mu) - m(q, y, mu)
                y = addv(y, unit(mu), dims)
        assert y == x
        return tot
    return lam


def chern(lam, dims):
    """CechDeRhamChern: N(p, q, r)"""
    def nn(p, q, r):
        c = corner([p, q, r], dims)
        return -(lam(q, r, c) - lam(p, r, c) + lam(p, q, c))
    return nn


def cubes_at(x, dims):
    return [addv(x, tuple(-r for r in rr), dims) for rr in itertools.product((0, 1), repeat=3)]


def cocycle_checks(a, n, dims, tau):
    """CechDeRhamCocycleQ, and the Cech cocycle condition; the connection is a / tau - m"""
    lat = Torus(dims)
    pts = list(lat.points())
    m = primitive(n, dims)
    lam = transition(m, dims)
    nn = chern(lam, dims)
    conn = lambda p, x, mu: Fr(a(x, (mu,)), tau) - m(p, x, mu)
    ok_prim = ok_c1 = ok_c2 = ok_c3 = True
    for p in pts:
        for mu, nu in PLANES:
            rho = 6 - mu - nu
            for t in (0, 1):
                x = addv(p, tuple(t * u for u in unit(rho)), dims)
                dm = (m(p, addv(x, unit(mu), dims), nu) - m(p, x, nu)
                      - m(p, addv(x, unit(nu), dims), mu) + m(p, x, mu))
                ok_prim = ok_prim and dm == n(x, (mu, nu))
    for x in pts:
        cubes = cubes_at(x, dims)
        for p, q in itertools.combinations(cubes, 2):
            S = common_sites([p, q], dims)
            for y in S:
                ok_c1 = ok_c1 and lam(p, q, y) == -lam(q, p, y)
                for mu in (1, 2, 3):
                    y2 = addv(y, unit(mu), dims)
                    if y2 in S:
                        ok_c1 = ok_c1 and (conn(q, y, mu) - conn(p, y, mu) == lam(p, q, y2) - lam(p, q, y))
        for p, q, r in itertools.combinations(cubes, 3):
            S = common_sites([p, q, r], dims)
            vals = {lam(q, r, y) - lam(p, r, y) + lam(p, q, y) for y in S}
            ok_c2 = ok_c2 and vals == {-nn(p, q, r)}
        for p, q, r, s in itertools.combinations(cubes, 4):
            ok_c3 = ok_c3 and nn(q, r, s) - nn(p, r, s) + nn(p, q, s) - nn(p, q, r) == 0
    return ok_prim, ok_c1, ok_c2, ok_c3


def chern_numbers(n, dims):
    """CechDeRhamChernNumbers: minus the sum of N over the triangulated coordinate tori"""
    lat = Torus(dims)
    nn = chern(transition(primitive(n, dims), dims), dims)
    out = {}
    for mu, nu in PLANES:
        rho = 6 - mu - nu
        tot = 0
        for p in lat.points():
            if p[rho - 1] == 0:
                pm, pn = addv(p, unit(mu), dims), addv(p, unit(nu), dims)
                pmn = addv(pm, unit(nu), dims)
                tot += nn(p, pm, pmn) - nn(p, pn, pmn)
        out[(mu, nu)] = -tot
    return out


def test_fields(lat):
    """the fields of Tests/Villain.wlt"""
    e0 = lat.formula(1, lambda x, S: (x[0] + 2 * x[1] + 3 * x[2] + S[0] * (1 + x[0] * x[1] + x[2])) % 3 - 1)
    a = lat.formula(1, lambda x, S: (2 * x[0] + x[1] * x[2] + S[0] * x[1] + S[0]) % 5 - 2)
    n = add(lat, 2, thooft(lat, {(1, 2): 1, (1, 3): -2, (2, 3): 3}), cr.delta(e0))
    return a, n


# --------------------------------------------------------------------------
# part 2: background fields
# --------------------------------------------------------------------------

def check_background(C, k, big_n, tau, rng, top):
    a, n, phi, b = C.rand(1, rng), C.rand(2, rng), C.rand(0, rng), C.rand(2, rng)
    if top == 3:
        scaled = chern_simons(C, k * big_n ** 2, C.lin(1, (Fr(1, big_n), a)), C.lin(2, (Fr(1, big_n), n)),
                              C.lin(0, (big_n, phi)), tau)
        assert C.equal(chern_simons(C, k, a, n, phi, tau), scaled, 3)
        return 1
    cross = C.lin(4, (1, C.cup(n, b)), (1, C.cup(b, n)), (1, C.cup(n, C.d(b), 1)), (1, C.cup(b, C.d(n), 1)))
    shifted = C.lin(2, (1, n), (Fr(1, big_n), b))
    assert C.equal(qsquare(C, shifted),
                   C.lin(4, (1, qsquare(C, n)), (Fr(1, big_n), cross), (Fr(1, big_n ** 2), qsquare(C, b))), 4)
    assert C.equal(cross, C.lin(4, (2, C.cup(b, n)), (-1, C.d(C.cup(n, b, 1))), (1, C.cup(C.d(n), b, 1)),
                                (2, C.cup(n, C.d(b), 1)), (1, C.cup(b, C.d(n), 1))), 4)
    # the inflow identity with the flux n + b / N
    F = C.lin(2, (1, C.d(a)), (-tau, shifted))
    lhs = C.d(chern_simons(C, k, a, shifted, phi, tau))
    rhs = C.lin(4, (Fr(k, 2 * tau), qsquare(C, F)), (Fr(-k * tau, 2), qsquare(C, shifted)),
                (k, C.cup(a, C.d(shifted))), (1, C.cup(C.d(phi), C.d(shifted))))
    assert C.equal(lhs, rhs, 4)
    return 1


def check_flat_weight(big_k, big_n, rng):
    """(K / 2 N^2) Q(B) = (p / 2 N) P(B) modulo 1, p = K / N, for B flat modulo N on the 4-simplex"""
    C = Calc("simplex", n=4)
    for _ in range(20):
        lam, c = C.rand(1, rng), C.rand(2, rng)
        b = C.lin(2, (1, C.d(lam)), (big_n, c))
        diff = C.lin(4, (Fr(big_k, 2 * big_n ** 2), qsquare(C, b)), (Fr(-big_k // big_n, 2 * big_n), psquare(C, b)))
        assert all(Fr(v).denominator == 1 for v in sr.vec(diff, 4))
    return 1


def main():
    rng = random.Random(20261123)

    for dims in ((3, 3, 3), (3, 4, 5)):
        lat = Torus(dims)
        zf = {pl: rng.randint(-3, 3) for pl in PLANES}
        n = add(lat, 2, thooft(lat, zf), cr.delta(lat.random_cochain(1, rng)))
        a = lat.random_cochain(1, rng, 5)
        assert cocycle_checks(a, n, dims, 7) == (True, True, True, True)
        assert chern_numbers(n, dims) == flux(lat, n) == zf
        # a field with a monopole has no primitive on the cubes
        bad = add(lat, 2, n, lat.table(2, {((0, 0, 0), (1, 2)): 1}))
        assert cocycle_checks(a, bad, dims, 7)[0] is False
    print("the Cech-de Rham cocycle of a flat Villain field: conditions and Chern numbers  True")

    lat = Torus((3, 3, 3))
    a, n = test_fields(lat)
    checks = cocycle_checks(a, n, (3, 3, 3), 7)
    numbers = chern_numbers(n, (3, 3, 3))
    m = primitive(n, (3, 3, 3))
    lam = transition(m, (3, 3, 3))
    nn = chern(lam, (3, 3, 3))
    sample = [m((0, 0, 0), (1, 0, 0), 2), m((0, 0, 0), (1, 1, 0), 3), m((2, 2, 2), (0, 0, 2), 3),
              lam((0, 0, 0), (1, 0, 0), (1, 1, 0)), lam((0, 0, 0), (0, 1, 0), (1, 1, 1)),
              nn((0, 0, 0), (1, 0, 0), (1, 1, 0)), nn((2, 2, 2), (0, 2, 2), (0, 0, 2)),
              nn((0, 0, 0), (0, 1, 0), (1, 1, 0))]
    print("  checks  %s   Chern numbers  %s   samples  %s" % (checks, numbers, sample))
    assert checks == (True, True, True, True)
    assert numbers == {(1, 2): 1, (1, 3): -2, (2, 3): 3}
    print("the numbers of the Wolfram Language tests  True")

    cnt = 0
    for (k, big_n, tau) in ((1, 2, 3), (2, 3, 5), (3, 2, 7)):
        for top in (3, 4):
            cnt += check_background(Calc("cube", cr.Lattice(top, 2)), k, big_n, tau, rng, top)
            cnt += check_background(Calc("simplex", n=top), k, big_n, tau, rng, top)
    for (big_k, big_n) in ((2, 2), (4, 2), (8, 2), (6, 3), (18, 3), (4, 4)):
        check_flat_weight(big_k, big_n, rng)
    print("background fields: Q(n + b/N), the cross term, level k N^2, the weight on flat fields (%d cases)  True" % cnt)
    spins = [Fr(K, 2 * N * N) % 1 for K, N in ((2, 2), (4, 2), (8, 2), (6, 3), (18, 3))]
    assert spins == [Fr(1, 4), Fr(1, 2), 0, Fr(1, 3), 0]
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
