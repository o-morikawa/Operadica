"""
The star product and the integral of the lattice Deligne-Beilinson cohomology on the
Cech-de Rham cocycle of a flat Villain field (Operadica`Villain`: CechDeRhamFundamentalCycle,
CechDeRhamStarIntegral, CechDeRhamGaugeTransform).

The cover of the three-torus by the unit cubes (a cube is labelled by its lowest corner) and a
triple (A_p, Lambda_pq, N_pqr) with

    A_q - A_p = d Lambda_pq,   Lambda_qr - Lambda_pr + Lambda_pq = - N_pqr,   N a Cech cocycle

are as in cech_reference.py.  The star product of two triples has the components

    (3, 0)   A_p cup dA'_p              on the cube p
    (2, 1)   Lambda_pq cup dA'_q        on the plaquettes of the intersection of p and q
    (1, 2)   N_pqr A'_r                 on the links of the intersection of p, q, r
    (0, 3)   N_pqr Lambda'_rs           on the sites of the intersection of p, q, r, s
    (-1, 4)  N_pqr N'_rst               an integer

(the form of arXiv:2601.15939, section 7, read from its text: the first factor takes the first
patches, the second factor the last ones, and the two share one patch).  With

    w30 = A cup dA',   w21 = Lambda cup dA',   w12 = N A',   w03 = N Lambda'

the cocycle conditions give (dc = Cech coboundary on ordered tuples, d = lattice coboundary)

    dc w30 = d w21,   dc w21 = - d w12,   dc w12 = d w03,   dc w03 = - N N'  (an integer).

The integral is the pairing with a chain s30 + s21 + s12 + s03, s_ij a combination of
(cell of dimension i; j + 1 cubes that contain it), with

    b s30 + bc s21 = 0,    b s21 - bc s12 = 0,    b s12 + bc s03 = 0

(b = boundary of the cells, bc = Cech boundary).  Such a chain is built here by cones:

    s30 = sum of (cube x; x),
    s_next restricted to a cell e = the cone, with the cube based at the base point of e put
    last, of the coefficient of e in b s_prev.

After the terms on which the products vanish are dropped (N and Lambda are alternating):

    s21 = sum over x, mu of (-1)^(mu - 1) (plaquette at x normal to mu; x - e_mu, x)
    s12 = two triples of cubes for every link, s03 = six quadruples for every site.

s21 is the chain of that paper.  s12 and s03 have the same number of terms as there; their
signs and the order of the patches have NOT been compared with the paper (they are fixed here
by the three conditions above, and the conditions are checked below).

Gauge transformations (xi_p a real 0-cochain on the cube p, mm_pq an alternating integer):

    A_p -> A_p + d xi_p,   Lambda_pq -> Lambda_pq + xi_q - xi_p - mm_pq,
    N_pqr -> N_pqr + mm_qr - mm_pr + mm_pq.

Statements checked:

 1. the three conditions on the chain, on ordered tuples, with and without the dropped terms;
 2. the integral of the star product of two triples is unchanged by xi (of either factor) and
    changes by an integer under mm (of either factor);
 3. for the triples of two flat Villain fields (a, n), (b, n') in the tree gauge of
    cech_reference.py the four contributions are, exactly,

        sum (a / tau) cup (db / tau - n'),   0,   - sum n cup (b / tau),   0

    (tau = the period, 2 pi in the package): Lambda vanishes at the base point of every
    plaquette and site of the chain, and m_p vanishes on the links at the base point of the
    cube p.  So the integral is (1 / tau) times the sum of the connection of
    DeligneProduct[(a, n), (b, n')], and for a = b it is (1 / tau) times the sum of the
    Chern-Simons Lagrangian at level 2;
 4. so the weight at an even level 2 j is exp(2 pi i j (the integral)), a function of the class.
    Half of the integral is not: (a + tau m, n + dm) and (a, n) give gauge equivalent triples
    and their integrals differ by - sum q(m, n), which can be odd (the obstruction at odd level
    of oddlevel_reference.py).

 5. on the lattice the integral is not symmetric in the two factors: for the triples of two
    flat Villain fields

        I(A, B) - I(B, A) = - sum (F_A / tau) cup_1 (F_B / tau) + sum n cup_1 n',

    so it is symmetric modulo 1 when one of the curvatures vanishes (cup is commutative only
    up to cup_1).

 6. the change of the integral of a square under one gauge transformation (xi, mm) of both
    factors is minus the pairing of the Cech cochain

        qc(mm, N)_pqrs = mm_pq N_qrs + N_pqr mm_rs + (mm_qr - mm_pr + mm_pq) mm_rs

    with the sites of the chain: m cup N + N cup m + dm cup m with the Cech cup product, the
    form of q(m, n) = m cup n + n cup m + dm cup m (+ m cup_1 dn) on the lattice.
 7. the large gauge transformation (a + tau m, n + dm) of a flat Villain field is a gauge
    transformation of its triple, with

        xi_p(x)  = the sum of m along the path of the tree of the cube p from p to x
                   (direction 3, then 2, then 1),
        mm_pq    = xi_q - xi_p at the lowest corner of the intersection,

    and qc(mm, N) paired with the chain is the sum of q(m, n).

Run:  python3 reference/star_reference.py
"""

import itertools
import random
import sys
from fractions import Fraction as Fr

import cubical_reference as cr
from oddlevel_reference import Torus, thooft, add, integrate, torus_anomaly, PLANES
from cech_reference import addv, rel, unit, primitive, transition, chern, cubes_at, corner, test_fields


# --------------------------------------------------------------------------
# chains: {(x, dirs, patches): coefficient}
# --------------------------------------------------------------------------

def put(chain, key, c):
    v = chain.get(key, 0) + c
    if v == 0:
        chain.pop(key, None)
    else:
        chain[key] = v


def cell_boundary(x, dirs, dims):
    """the boundary of the cell (x; dirs): a list of (coefficient, x', dirs')"""
    out = []
    for i, mu in enumerate(dirs):
        rest = dirs[:i] + dirs[i + 1:]
        out.append(((-1) ** i, addv(x, unit(mu), dims), rest))
        out.append((-(-1) ** i, x, rest))
    return out


def boundary(chain, dims):
    out = {}
    for (x, dirs, ps), c in chain.items():
        for (s, y, rest) in cell_boundary(x, dirs, dims):
            put(out, (y, rest, ps), s * c)
    return out


def cech_boundary(chain):
    out = {}
    for (x, dirs, ps), c in chain.items():
        for i in range(len(ps)):
            put(out, (x, dirs, ps[:i] + ps[i + 1:]), (-1) ** i * c)
    return out


def combine(u, v, c=1):
    out = dict(u)
    for key, val in v.items():
        put(out, key, c * val)
    return out


def cone(chain):
    """every term (e; p0 .. pj) becomes (e; p0 .. pj, the cube based at the base point of e)"""
    out = {}
    for (x, dirs, ps), c in chain.items():
        put(out, (x, dirs, ps + (x,)), c)
    return out


def vanishing(ps):
    """the products vanish on these tuples (N and Lambda alternating)"""
    k = len(ps)
    if k == 2:
        return ps[0] == ps[1]
    if k == 3:
        return len(set(ps)) < 3
    if k == 4:
        return len(set(ps[:3])) < 3 or ps[2] == ps[3]
    return False


def reduced(chain):
    return {key: c for key, c in chain.items() if not vanishing(key[2])}


def fundamental_cycle(dims, full=False):
    lat = Torus(dims)
    s30 = {(x, (1, 2, 3), (x,)): 1 for x in lat.points()}
    s21 = cone(boundary(s30, dims))
    s12 = cone(boundary(s21, dims))
    s03 = cone(boundary(s12, dims))
    if full:
        return s30, s21, s12, s03
    return s30, reduced(s21), reduced(s12), reduced(s03)


def cycle_conditions(cyc, dims):
    s30, s21, s12, s03 = cyc
    return (combine(boundary(s30, dims), cech_boundary(s21)) == {},
            combine(boundary(s21, dims), cech_boundary(s12), -1) == {},
            combine(boundary(s12, dims), cech_boundary(s03)) == {})


def explicit_cycle(dims):
    """the closed form of the reduced chain (the form of the Wolfram Language code)"""
    lat = Torus(dims)
    s30, s21, s12, s03 = {}, {}, {}, {}

    def sub(x, *mus):
        for mu in mus:
            x = addv(x, tuple(-c for c in unit(mu)), dims)
        return x

    for x in lat.points():
        s30[(x, (1, 2, 3), (x,))] = 1
        for mu in (1, 2, 3):
            rest = tuple(nu for nu in (1, 2, 3) if nu != mu)
            s21[(x, rest, (sub(x, mu), x))] = (-1) ** (mu - 1)
            al, be = rest
            sg = (-1) ** (mu - 1)
            # the link (x; mu): the four cubes x, x - e_al, x - e_be, x - e_al - e_be
            s12[(x, (mu,), (sub(x, al, be), sub(x, be), x))] = sg
            s12[(x, (mu,), (sub(x, al, be), sub(x, al), x))] = -sg
            # the site x, from the link (x - e_mu; mu) that ends there
            y = sub(x, mu)
            s03[(x, (), (sub(y, al, be), sub(y, be), y, x))] = sg
            s03[(x, (), (sub(y, al, be), sub(y, al), y, x))] = -sg
    return s30, s21, s12, s03


# --------------------------------------------------------------------------
# triples, the star product, gauge transformations
# --------------------------------------------------------------------------

def villain_triple(a, n, dims, tau):
    m = primitive(n, dims)
    lam = transition(m, dims)
    nn = chern(lam, dims)

    def conn(p, x, mu):
        return Fr(a(x, (mu,)), 1) / tau - m(p, x, mu)

    def lam_checked(p, q, x):
        return 0 if p == q else lam(p, q, x)

    def nn_checked(p, q, r):
        return 0 if len({p, q, r}) < 3 else nn(p, q, r)

    return conn, lam_checked, nn_checked


def curvature(conn, dims):
    def g(p, x, al, be):
        return (conn(p, x, al) + conn(p, addv(x, unit(al), dims), be)
                - conn(p, addv(x, unit(be), dims), al) - conn(p, x, be))
    return g


def star_integral(t1, t2, dims, cyc=None):
    """the four contributions (3, 0), (2, 1), (1, 2), (0, 3)"""
    conn1, lam1, nn1 = t1
    conn2, lam2, nn2 = t2
    curv2 = curvature(conn2, dims)
    s30, s21, s12, s03 = cyc if cyc is not None else explicit_cycle(dims)
    t30 = 0
    for (x, dirs, (p,)), c in s30.items():
        t30 += c * (conn1(p, x, 1) * curv2(p, addv(x, unit(1), dims), 2, 3)
                    - conn1(p, x, 2) * curv2(p, addv(x, unit(2), dims), 1, 3)
                    + conn1(p, x, 3) * curv2(p, addv(x, unit(3), dims), 1, 2))
    t21 = sum(c * lam1(p, q, x) * curv2(q, x, dirs[0], dirs[1]) for (x, dirs, (p, q)), c in s21.items())
    t12 = sum(c * nn1(p, q, r) * conn2(r, x, dirs[0]) for (x, dirs, (p, q, r)), c in s12.items())
    t03 = sum(c * nn1(p, q, r) * lam2(r, s, x) for (x, dirs, (p, q, r, s)), c in s03.items())
    return [t30, t21, t12, t03]


def gauge_transform(triple, xi, mm, dims):
    conn, lam, nn = triple

    def conn2(p, x, mu):
        return conn(p, x, mu) + xi(p, addv(x, unit(mu), dims)) - xi(p, x)

    def lam2(p, q, x):
        return lam(p, q, x) + xi(q, x) - xi(p, x) - mm(p, q)

    def nn2(p, q, r):
        return nn(p, q, r) + mm(q, r) - mm(p, r) + mm(p, q)

    return conn2, lam2, nn2


def random_gauge(dims, rng, den=5):
    xs, ms = {}, {}

    def xi(p, x):
        assert all(c in (0, 1) for c in rel(x, p, dims))
        if (p, x) not in xs:
            xs[(p, x)] = Fr(rng.randint(-6, 6), den)
        return xs[(p, x)]

    def mm(p, q):
        if p == q:
            return 0
        assert corner([p, q], dims) is not None
        key = (min(p, q), max(p, q))
        if key not in ms:
            ms[key] = rng.randint(-2, 2)
        return ms[key] if p < q else -ms[key]

    return xi, mm


def cech_anomaly(mm, nn, dims, cyc=None):
    """CechDeRhamAnomaly: the pairing of qc(mm, N) with the sites of the chain"""
    s03 = (cyc if cyc is not None else explicit_cycle(dims))[3]
    return sum(c * (mm(p, q) * nn(q, r, s) + nn(p, q, r) * mm(r, s) + (mm(q, r) - mm(p, r) + mm(p, q)) * mm(r, s))
               for (x, dirs, (p, q, r, s)), c in s03.items())


def large_gauge(m, dims):
    """CechDeRhamLargeGauge: (xi, mm) of the large gauge transformation by the lattice 1-cochain m"""
    def xi(p, x):
        r = rel(x, p, dims)
        y3 = addv(p, (0, 0, r[2]), dims)
        y2 = addv(y3, (0, r[1], 0), dims)
        return (m(p, (3,)) if r[2] else 0) + (m(y3, (2,)) if r[1] else 0) + (m(y2, (1,)) if r[0] else 0)

    def mm(p, q):
        c = corner([p, q], dims)
        return xi(q, c) - xi(p, c)

    return xi, mm


def trivial_xi(p, x):
    return 0


def trivial_mm(p, q):
    return 0


# the gauge functions of Tests/Villain.wlt
def test_xi(dims):
    def xi(p, x):
        r = rel(x, p, dims)
        return Fr((2 * p[0] + p[1] * p[2] + 3 * r[0] + r[1] * (1 + p[2]) + 2 * r[2] * p[0]) % 7 - 3, 5)
    return xi


def test_mm(dims):
    def g(p):
        return (p[0] + 2 * p[1] * p[2] + p[2] + p[0] * p[1]) % 3

    def mm(p, q):
        d = tuple((b - a + 1) % L - 1 for a, b, L in zip(p, q, dims))
        w = d[0] + 2 * d[1] + 4 * d[2]
        return 0 if w == 0 else (1 if w > 0 else -1) * ((g(p) + g(q) + abs(w)) % 3 - 1)
    return mm


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------

def check_stokes(dims, rng):
    lat = Torus(dims)
    for p in (0, 1, 2):
        u = lat.random_cochain(p, rng)
        du = cr.delta(u)
        for x in lat.points():
            for dirs in itertools.combinations((1, 2, 3), p + 1):
                assert du(x, dirs) == sum(s * u(y, rest) for (s, y, rest) in cell_boundary(x, dirs, dims))
    return True


def check_cycle(dims):
    full = fundamental_cycle(dims, full=True)
    red = fundamental_cycle(dims)
    assert cycle_conditions(full, dims) == (True, True, True)
    assert cycle_conditions(red, dims) == (True, True, True)
    assert red == explicit_cycle(dims)
    vol = dims[0] * dims[1] * dims[2]
    assert [len(s) for s in red] == [vol, 3 * vol, 6 * vol, 6 * vol]
    assert all(abs(c) == 1 for s in red for c in s.values())
    return [len(s) for s in full]


def villain_sums(lat, a, n, b, n2, tau):
    """sum (a / tau) cup (db / tau - n'),  - sum n cup (b / tau)"""
    g = add(lat, 2, cr.comb(lat, 2, [(Fr(1, tau), cr.delta(b))]), cr.comb(lat, 2, [(-1, n2)]))
    first = integrate(lat, cr.cup(cr.comb(lat, 1, [(Fr(1, tau), a)]), g))
    second = -integrate(lat, cr.cup(n, cr.comb(lat, 1, [(Fr(1, tau), b)])))
    return first, second


def check_villain(dims, rng, tau=7):
    lat = Torus(dims)
    zf = {pl: rng.randint(-2, 2) for pl in PLANES}
    zg = {pl: rng.randint(-2, 2) for pl in PLANES}
    n = add(lat, 2, thooft(lat, zf), cr.delta(lat.random_cochain(1, rng)))
    n2 = add(lat, 2, thooft(lat, zg), cr.delta(lat.random_cochain(1, rng)))
    a, b = lat.random_cochain(1, rng, 5), lat.random_cochain(1, rng, 5)
    t1, t2 = villain_triple(a, n, dims, tau), villain_triple(b, n2, dims, tau)
    full = fundamental_cycle(dims, full=True)
    for (u, un, v, vn, tu, tv) in ((a, n, b, n2, t1, t2), (a, n, a, n, t1, t1), (b, n2, a, n, t2, t1)):
        vals = star_integral(tu, tv, dims)
        first, second = villain_sums(lat, u, un, v, vn, tau)
        assert vals == [first, 0, second, 0], (vals, first, second)
        assert star_integral(tu, tv, dims, full) == vals
    # the two orders
    swap = sum(star_integral(t1, t2, dims)) - sum(star_integral(t2, t1, dims))
    g1 = cr.comb(lat, 2, [(Fr(1, tau), cr.delta(a)), (-1, n)])
    g2 = cr.comb(lat, 2, [(Fr(1, tau), cr.delta(b)), (-1, n2)])
    assert swap == -integrate(lat, cr.higher_cup(1, g1, g2)) + integrate(lat, cr.higher_cup(1, n, n2))
    # gauge transformations of either factor
    odd = 0
    for _ in range(4):
        xi, mm = random_gauge(dims, rng)
        xi2, mm2 = random_gauge(dims, rng)
        base = sum(star_integral(t1, t2, dims))
        assert sum(star_integral(gauge_transform(t1, xi, trivial_mm, dims), t2, dims)) == base
        assert sum(star_integral(t1, gauge_transform(t2, xi2, trivial_mm, dims), dims)) == base
        for (g1, g2) in ((gauge_transform(t1, xi, mm, dims), t2), (t1, gauge_transform(t2, xi2, mm2, dims)),
                         (gauge_transform(t1, xi, mm, dims), gauge_transform(t2, xi2, mm2, dims))):
            diff = sum(star_integral(g1, g2, dims)) - base
            assert Fr(diff).denominator == 1
            assert sum(star_integral(g1, g2, dims, full)) - base == diff
        # the same transformation of both factors of the square
        gg = gauge_transform(t1, xi, mm, dims)
        diff = sum(star_integral(gg, gg, dims)) - sum(star_integral(t1, t1, dims))
        assert Fr(diff).denominator == 1
        odd += int(diff % 2 == 1)
        assert diff == -cech_anomaly(mm, t1[2], dims)
    # the large gauge transformation of the Villain field
    m = lat.random_cochain(1, rng)
    a_new = add(lat, 1, a, cr.comb(lat, 1, [(tau, m)]))
    n_new = add(lat, 2, n, cr.delta(m))
    t_new = villain_triple(a_new, n_new, dims, tau)
    diff = sum(star_integral(t_new, t_new, dims)) - sum(star_integral(t1, t1, dims))
    assert diff == -integrate(lat, torus_anomaly(lat, m, n))
    # it is a gauge transformation of the triple
    xi_m, mm_m = large_gauge(m, dims)
    moved = gauge_transform(t1, xi_m, mm_m, dims)
    for x in lat.points():
        for r in itertools.product((0, 1), repeat=3):
            y = addv(x, r, dims)
            for mu in (1, 2, 3):
                if r[mu - 1] == 0:
                    assert moved[0](x, y, mu) == t_new[0](x, y, mu)
    for key_set in explicit_cycle(dims)[1:]:
        for (x, dirs, ps) in key_set:
            if len(ps) == 2:
                assert moved[1](ps[0], ps[1], x) == t_new[1](ps[0], ps[1], x)
            if len(ps) >= 3:
                assert moved[2](ps[0], ps[1], ps[2]) == t_new[2](ps[0], ps[1], ps[2])
            if len(ps) == 4:
                assert moved[1](ps[2], ps[3], x) == t_new[1](ps[2], ps[3], x)
    assert cech_anomaly(mm_m, t1[2], dims) == integrate(lat, torus_anomaly(lat, m, n))
    return odd, int(diff % 2)


def poly_in_period(f):
    """f(tau) = c0 + c1 / tau + c2 / tau^2 for every tau: the coefficients, from tau = 1, 2, 3, checked at 5"""
    v1, v2, v3 = f(1), f(2), f(3)
    # u = 1, 1/2, 1/3
    us = [Fr(1), Fr(1, 2), Fr(1, 3)]
    vs = [v1, v2, v3]
    # Lagrange interpolation in u
    coeffs = [Fr(0), Fr(0), Fr(0)]
    for i in range(3):
        others = [us[j] for j in range(3) if j != i]
        den = (us[i] - others[0]) * (us[i] - others[1])
        coeffs[0] += vs[i] * others[0] * others[1] / den
        coeffs[1] += -vs[i] * (others[0] + others[1]) / den
        coeffs[2] += vs[i] / den
    assert f(5) == coeffs[0] + coeffs[1] * Fr(1, 5) + coeffs[2] * Fr(1, 25)
    return coeffs


def test_numbers():
    """the numbers of Tests/Villain.wlt: every contribution as (c0, c1, c2), the value being
    c0 + c1 / tau + c2 / tau^2 (tau = 2 pi in the package)"""
    dims = (3, 3, 3)
    lat = Torus(dims)
    a, n = test_fields(lat)
    b = lat.formula(1, lambda x, S: (x[0] * x[1] + 2 * x[2] + S[0] * (x[0] + 1)) % 5 - 2)
    n2 = thooft(lat, {(1, 2): 2, (1, 3): 0, (2, 3): -1})
    m2 = lat.formula(1, lambda x, S: (S[0] * x[0] + x[1] * x[2] + 2 * S[0] * x[2] + x[0] + S[0]) % 2)
    xi, mm = test_xi(dims), test_mm(dims)
    for p in lat.points():
        for q in [addv(p, r, dims) for r in itertools.product((-1, 0, 1), repeat=3)]:
            assert mm(p, q) == -mm(q, p)

    def cases(tau):
        t1, t2 = villain_triple(a, n, dims, tau), villain_triple(b, n2, dims, tau)
        g1, g2 = gauge_transform(t1, xi, mm, dims), gauge_transform(t2, xi, mm, dims)
        x1 = gauge_transform(t1, xi, trivial_mm, dims)
        big = villain_triple(add(lat, 1, a, cr.comb(lat, 1, [(tau, m2)])), add(lat, 2, n, cr.delta(m2)), dims, tau)
        return {
            "self": star_integral(t1, t1, dims),
            "pair": star_integral(t1, t2, dims),
            "swap": star_integral(t2, t1, dims),
            "xi self": star_integral(x1, x1, dims),
            "gauge self": star_integral(g1, g1, dims),
            "gauge first": star_integral(g1, t2, dims),
            "gauge second": star_integral(t1, g2, dims),
            "large": star_integral(big, big, dims),
        }

    tables = {tau: cases(tau) for tau in (1, 2, 3, 5)}
    out = {}
    for key in tables[1]:
        out[key] = [poly_in_period(lambda tau, i=i: Fr(tables[tau][key][i])) for i in range(4)]
    out["q"] = integrate(lat, torus_anomaly(lat, m2, n))
    t1 = villain_triple(a, n, dims, 1)
    out["anomaly"] = (cech_anomaly(mm, t1[2], dims), cech_anomaly(large_gauge(m2, dims)[1], t1[2], dims))
    out["cup1"] = integrate(lat, cr.higher_cup(1, n, n2))
    return out


def main():
    rng = random.Random(20261124)
    for dims in ((3, 3, 3), (3, 4, 5)):
        assert check_stokes(dims, rng)
        sizes = check_cycle(dims)
        print("  %s  terms of the chain before the vanishing ones are dropped: %s" % (dims, sizes))
    print("the chain: three conditions, the closed form, 1 + 3 + 6 + 6 terms per site  True")
    odd = []
    for dims in ((3, 3, 3), (3, 3, 4), (3, 4, 5)):
        for _ in range(3):
            odd.append(check_villain(dims, rng))
    print("  odd changes (same transformation of both factors, large gauge transformation): %s" % odd)
    assert any(o[1] == 1 for o in odd)
    print("the star integral: invariance, the Villain form term by term, the change - sum q(m, n)  True")
    print("the Cech form of the anomaly, and large gauge transformations as gauge transformations of the triple  True")
    out = test_numbers()
    tot = {}
    for key, val in out.items():
        if key in ("q", "cup1", "anomaly"):
            continue
        tot[key] = [sum(c[i] for c in val) for i in range(3)]
        print("  %-13s %s   total %s" % (key, [[str(v) for v in c] for c in val], [str(v) for v in tot[key]]))
    print("  sum q(m2, n) = %s   sum n cup_1 n' = %s   Cech anomaly (test mm, large m2) = %s" % (
        out["q"], out["cup1"], out["anomaly"]))
    assert out["anomaly"] == (tot["self"][0] - tot["gauge self"][0], out["q"])
    assert tot["xi self"] == tot["self"]
    assert [a - b for a, b in zip(tot["gauge self"], tot["self"])][1:] == [0, 0]
    assert [a - b for a, b in zip(tot["large"], tot["self"])] == [-out["q"], 0, 0]
    print("  changes: gauge self %s, gauge first %s, gauge second %s, large %s" % (
        tot["gauge self"][0] - tot["self"][0], tot["gauge first"][0] - tot["pair"][0],
        tot["gauge second"][0] - tot["pair"][0], tot["large"][0] - tot["self"][0]))
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
