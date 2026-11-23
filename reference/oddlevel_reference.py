"""
U(1) Chern-Simons theory at odd level on the lattice: the obstruction and the signs that
cancel it on a three-torus  (Operadica`Villain`: ChernSimonsLargeGaugeAnomaly,
SpinStructureSign; Operadica`Lattice`: THooftFlux).

L is the modified Villain Lagrangian of arXiv:2303.06160, eq. (17),

    L = (k / 4 pi) (a cup da - 2 pi (a cup n + n cup a)) - (k/2) a cup_1 dn + phi cup dn,

F = da - 2 pi n, and  Q(x) = x cup x + x cup_1 dx  (the Pontryagin square
P(x) = x cup x - x cup_1 dx  plus  2 x cup_1 dx;  the same modulo 2).

Identities for generic cochains (cubes and simplices; 2 pi is replaced by integers tau):

  inflow        dL = (k / 4 pi) Q(F) - k pi Q(n) + (k a + d phi) cup dn         (four dimensions)
                The first term is gauge invariant: without monopoles it is the theta term at
                theta = 2 pi k.  The last term vanishes without monopoles.  So the Lagrangian
                is a primitive of the theta term up to k pi Q(n), which is 2 pi times an
                integer cochain only for even k.
  anomaly       under a -> a + 2 pi m, n -> n + dm the Lagrangian changes by
                    -(k/2) d(m cup a) - k pi q(m, n),
                    q(m, n) = m cup n + n cup m + m cup_1 dn + dm cup m      (three dimensions)
  descent       Q(n + dm) - Q(n) = d q(m, n) + 2 m cup dn                       (four dimensions)
  cocycle       q(m, n) + q(m', n + dm) - q(m + m', n) = - d(m' cup m)
  Gu-Wen form   q(m, n) = m cup dm + dm cup_1 n + d(m cup m + m cup_1 n)
                          + 2 (n cup m + m cup_1 dn - dm cup_1 n)
  level 4k      L_k(a, n, phi) = L_4k(a/2, n/2, 2 phi): the theory at level k is the theory at
                level 4k with half-integer fluxes.

On a three-torus (periodic cubic lattice with sides L1, L2, L3):

  obstruction   the sum of q(m, n) can be odd: for m equal to 1 on the links ((0,0,0); 1) and
                ((1,0,0); 2) and n = 0 it is 1.  So exp(i S) is not invariant at odd level.
  flux          a closed integer 2-cochain n is THooftFluxCochain[z] + dm with z the matrix of
                the sums of n over the coordinate planes.
  signs         a function z on the integer 2-cochains that are closed modulo 2, with values +-1:
                    (i)  z(n + dm) = z(n) (-1)^(sum of q(m, n))
                    (ii) z(n + n') = z(n) z(n') (-1)^(sum of n cup_1 n')
                It is fixed by its values (s12, s13, s23) on the three unit fluxes, so there
                are eight; two of them differ by (-1)^(sum of alpha cup n) with alpha a flat
                1-cochain modulo 2 (a torsor over H^1(T^3; Z_2), like the spin structures).
                (i) says that exp(i S) z(n) is invariant under large gauge transformations for
                odd k.  z(dm) = (-1)^(sum of dm cup m).  Every straight flux tube in the
                (mu, nu) direction has the sign s_(mu nu), wherever it is.
                z is computed by solving n = THooftFluxCochain[c] + dm modulo 2.
  planes        for m along the direction rho and n on the plaquettes that contain rho (the
                fluxes whose dual curves lie in a plane orthogonal to rho),
                m cup n + n cup m + dm cup m = 0 identically.  So on such planar fluxes z depends
                only on the class (wa, wb) of the dual curve in the plane, and
                    z = sa^wa sb^wb (-1)^(wa wb):
                1 on contractible curves, and (-1)^e with e a quadratic refinement of the
                intersection form of the two-torus.  By Johnson's theorem this is a spin
                structure on each coordinate two-torus: the fermion is periodic in the
                direction rho if and only if s_(mu nu) = -1, and z is minus the holonomy
                h = (-s23, -s13, -s12) along a curve that is not contractible in the plane.

Run:  python3 reference/oddlevel_reference.py
"""

import itertools
import random
import sys
from fractions import Fraction as Fr

import cubical_reference as cr
from villain_reference import Calc, chern_simons

PLANES = ((1, 2), (1, 3), (2, 3))


# --------------------------------------------------------------------------
# identities
# --------------------------------------------------------------------------

def anomaly(C, m, n):
    return C.lin(3, (1, C.cup(m, n)), (1, C.cup(n, m)), (1, C.cup(m, C.d(n), 1)), (1, C.cup(C.d(m), m)))


def qsquare(C, x):
    return C.lin(2 * x.p, (1, C.cup(x, x)), (1, C.cup(x, C.d(x), 1)))


def psquare(C, x):
    return C.lin(2 * x.p, (1, C.cup(x, x)), (-1, C.cup(x, C.d(x), 1)))


def check_identities(C, k, tau, rng, top):
    a, n, phi = C.rand(1, rng), C.rand(2, rng), C.rand(0, rng)
    m, m2 = C.rand(1, rng), C.rand(1, rng)
    lag = chern_simons(C, k, a, n, phi, tau)
    n_m = C.lin(2, (1, n), (1, C.d(m)))
    if top == 4:
        F = C.lin(2, (1, C.d(a)), (-tau, n))
        tail = [(k, C.cup(a, C.d(n))), (1, C.cup(C.d(phi), C.d(n)))]
        lhs = C.d(lag)
        assert C.equal(lhs, C.lin(4, (Fr(k, 2 * tau), qsquare(C, F)), (Fr(-k * tau, 2), qsquare(C, n)), *tail), 4)
        # with the Pontryagin square P there is one more term, and without it the identity fails
        with_p = [(Fr(k, 2 * tau), psquare(C, F)), (Fr(-k * tau, 2), psquare(C, n))] + tail
        assert C.equal(lhs, C.lin(4, *(with_p + [(-k, C.cup(C.d(a), C.d(n), 1))])), 4)
        if C.kind == "cube":      # on one simplex the extra term can vanish by chance
            assert not C.equal(lhs, C.lin(4, *with_p), 4)
        assert C.equal(C.lin(4, (1, qsquare(C, n_m)), (-1, qsquare(C, n))),
                       C.lin(4, (1, C.d(anomaly(C, m, n))), (2, C.cup(m, C.d(n)))), 4)
    else:
        a_m = C.lin(1, (1, a), (tau, m))
        assert C.equal(C.lin(3, (1, chern_simons(C, k, a_m, n_m, phi, tau)), (-1, lag)),
                       C.lin(3, (Fr(-k, 2), C.d(C.cup(m, a))), (Fr(-k * tau, 2), anomaly(C, m, n))), 3)
        m_sum = C.lin(1, (1, m), (1, m2))
        assert C.equal(C.lin(3, (1, anomaly(C, m, n)), (1, anomaly(C, m2, n_m)), (-1, anomaly(C, m_sum, n))),
                       C.lin(3, (-1, C.d(C.cup(m2, m)))), 3)
        assert C.equal(anomaly(C, m, n),
                       C.lin(3, (1, C.cup(m, C.d(m))), (1, C.cup(C.d(m), n, 1)),
                             (1, C.d(C.cup(m, m))), (1, C.d(C.cup(m, n, 1))),
                             (2, C.cup(n, m)), (2, C.cup(m, C.d(n), 1)), (-2, C.cup(C.d(m), n, 1))), 3)
        half_a, half_n = C.lin(1, (Fr(1, 2), a)), C.lin(2, (Fr(1, 2), n))
        assert C.equal(lag, chern_simons(C, 4 * k, half_a, half_n, C.lin(0, (2, phi)), tau), 3)
    return 1


# --------------------------------------------------------------------------
# the periodic lattice with sides dims
# --------------------------------------------------------------------------

class Torus(cr.Lattice):
    def __init__(self, dims):
        self.d, self.dims, self.L = len(dims), tuple(dims), None

    def shift(self, x, dirs):
        x = list(x)
        for mu in dirs:
            x[mu - 1] = (x[mu - 1] + 1) % self.dims[mu - 1]
        return tuple(x)

    def points(self):
        return itertools.product(*[range(L) for L in self.dims])

    def cells(self, p):
        for x in self.points():
            for S in itertools.combinations(range(1, self.d + 1), p):
                yield x, S

    def random_cochain(self, p, rng, bound=2):
        table = {c: rng.randint(-bound, bound) for c in self.cells(p)}
        return cr.Cochain(self, p, lambda x, S: table[(x, S)])

    def table(self, p, data):
        return cr.Cochain(self, p, lambda x, S: data.get((x, S), 0))

    def formula(self, p, f):
        return cr.Cochain(self, p, f)


def integrate(lat, u):
    top = tuple(range(1, lat.d + 1))
    return sum(u(x, top) for x in lat.points())


def thooft(lat, z):
    """THooftFluxCochain: z[(mu, nu)] on the (mu, nu) plaquettes at the sites whose mu and nu
    coordinates are both maximal"""
    def f(x, S):
        mu, nu = S
        return z.get(S, 0) * int(x[mu - 1] == lat.dims[mu - 1] - 1 and x[nu - 1] == lat.dims[nu - 1] - 1)
    return cr.Cochain(lat, 2, f)


def flux(lat, n):
    """THooftFlux: the sums of n over the coordinate planes through the origin"""
    out = {}
    for mu, nu in itertools.combinations(range(1, lat.d + 1), 2):
        tot = 0
        for i in range(lat.dims[mu - 1]):
            for j in range(lat.dims[nu - 1]):
                x = [0] * lat.d
                x[mu - 1], x[nu - 1] = i, j
                tot += n(tuple(x), (mu, nu))
        out[(mu, nu)] = tot
    return out


def solve_mod2(lat, t, rng=None):
    """a 1-cochain m with dm = t modulo 2, or None; with rng the columns are tried in a random
    order, which gives other solutions"""
    links, plaqs = list(lat.cells(1)), list(lat.cells(2))
    index = {c: i for i, c in enumerate(links)}
    rows = []
    for (x, S) in plaqs:
        mu, nu = S
        row = [0] * (len(links) + 1)
        for c in ((lat.shift(x, [mu]), (nu,)), (x, (nu,)), (lat.shift(x, [nu]), (mu,)), (x, (mu,))):
            row[index[c]] ^= 1
        row[-1] = t(x, S) % 2
        rows.append(row)
    order = list(range(len(links)))
    if rng is not None:
        rng.shuffle(order)
    r, pivots = 0, []
    for col in order:
        p = next((i for i in range(r, len(rows)) if rows[i][col]), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][col]:
                rows[i] = [u ^ v for u, v in zip(rows[i], rows[r])]
        pivots.append(col)
        r += 1
    if any(row[-1] for row in rows[r:]):
        return None
    return lat.table(1, {links[col]: rows[i][-1] for i, col in enumerate(pivots)})


def torus_anomaly(lat, m, n):
    return cr.comb(lat, 3, [(1, cr.cup(m, n)), (1, cr.cup(n, m)),
                            (1, cr.higher_cup(1, m, cr.delta(n))), (1, cr.cup(cr.delta(m), m))])


def add(lat, p, *us):
    return cr.comb(lat, p, [(1, u) for u in us])


def pairing(lat, u, v):
    return integrate(lat, cr.higher_cup(1, u, v)) % 2


def spin_sign(lat, signs, rng=None):
    """SpinStructureSign: signs = (s12, s13, s23)"""
    gens = [thooft(lat, {pl: 1}) for pl in PLANES]
    bb = [[pairing(lat, gens[i], gens[j]) for j in range(3)] for i in range(3)]

    def z(n):
        fl = flux(lat, n)
        c = [fl[pl] % 2 for pl in PLANES]
        rep = thooft(lat, {pl: c[i] for i, pl in enumerate(PLANES)})
        m = solve_mod2(lat, cr.comb(lat, 2, [(1, n), (-1, rep)]), rng)
        if m is None:
            return None
        e = c[0] * c[1] * bb[0][1] + c[0] * c[2] * bb[0][2] + c[1] * c[2] * bb[1][2]
        e += integrate(lat, torus_anomaly(lat, m, rep))
        s = 1
        for i in range(3):
            if c[i]:
                s *= signs[i]
        return s * (-1) ** (e % 2)
    return z, bb


def check_torus(dims, rng):
    lat = Torus(dims)
    zero = lat.table(2, {})

    def closed():
        zf = {pl: rng.randint(-3, 3) for pl in PLANES}
        return add(lat, 2, thooft(lat, zf), cr.delta(lat.random_cochain(1, rng))), zf

    # the flux
    for _ in range(3):
        n, zf = closed()
        assert all(cr.delta(n)(x, S) == 0 for x, S in lat.cells(3))
        assert flux(lat, n) == zf
    # a closed m does not see the anomaly
    for _ in range(3):
        n, zf = closed()
        wall = lat.formula(1, lambda x, S: int(S == (3,) and x[2] == 0))
        m = add(lat, 1, cr.delta(lat.random_cochain(0, rng)), wall)
        assert integrate(lat, torus_anomaly(lat, m, n)) % 2 == 0
    # flat 1-cochains measure the flux
    for rho, pl, sg in ((3, (1, 2), 1), (2, (1, 3), -1), (1, (2, 3), 1)):
        n, zf = closed()
        for pos in (0, dims[rho - 1] - 1):
            wall = lat.formula(1, lambda x, S, rho=rho, pos=pos: int(S == (rho,) and x[rho - 1] == pos))
            assert integrate(lat, cr.cup(wall, n)) == sg * zf[pl]
    seen_odd = False
    for signs in itertools.product((1, -1), repeat=3):
        z, bb = spin_sign(lat, signs)
        z_other, _ = spin_sign(lat, signs, rng)
        assert bb == [[0, 1, 1], [1, 0, 1], [1, 1, 0]]
        assert z(zero) == 1
        assert [z(thooft(lat, {pl: 1})) for pl in PLANES] == list(signs)
        for _ in range(2):
            n, zf = closed()
            n2, zf2 = closed()
            m = lat.random_cochain(1, rng)
            q = integrate(lat, torus_anomaly(lat, m, n))
            seen_odd = seen_odd or q % 2 == 1
            # (i) the anomaly is cancelled
            assert z(add(lat, 2, n, cr.delta(m))) == z(n) * (-1) ** (q % 2)
            # (ii) quadratic refinement of the cup-1 pairing
            assert z(add(lat, 2, n, n2)) == z(n) * z(n2) * (-1) ** pairing(lat, n, n2)
            # exact fluxes
            assert z(cr.delta(m)) == (-1) ** (integrate(lat, cr.cup(cr.delta(m), m)) % 2)
            assert integrate(lat, cr.cup(cr.delta(m), m)) == integrate(lat, cr.cup(m, cr.delta(m)))
            # another solution of the linear system gives the same sign
            assert z_other(n) == z(n)
            # the other spin structures
            for rho, i, sg in ((3, 0, 1), (2, 1, -1), (1, 2, 1)):
                flipped = list(signs)
                flipped[i] = -flipped[i]
                wall = lat.formula(1, lambda x, S, rho=rho: int(S == (rho,) and x[rho - 1] == 0))
                assert z(n) * spin_sign(lat, flipped)[0](n) == (-1) ** (integrate(lat, cr.cup(wall, n)) % 2)
        # straight flux tubes
        for i, (mu, nu) in enumerate(PLANES):
            for pos in itertools.product(range(dims[mu - 1]), range(dims[nu - 1])):
                tube = lat.formula(2, lambda x, S, mu=mu, nu=nu, pos=pos:
                                   int(S == (mu, nu) and (x[mu - 1], x[nu - 1]) == pos))
                assert z(tube) == signs[i]
        # not closed modulo 2
        assert z(lat.table(2, {((0, 0, 0), (1, 2)): 1})) is None
    assert seen_odd
    return 1


def tube(lat, pl, pos):
    """the plaquettes pl = (mu, nu) with (x_mu, x_nu) = pos: a straight flux tube"""
    mu, nu = pl
    return lat.formula(2, lambda x, S: int(S == pl and x[mu - 1] == pos[0] and x[nu - 1] == pos[1]))


def check_planar_identity(dims, rng):
    lat = Torus(dims)
    for rho in (1, 2, 3):
        base_m, base_n = lat.random_cochain(1, rng, 3), lat.random_cochain(2, rng, 3)
        m = lat.formula(1, lambda x, S, rho=rho, b=base_m: b(x, S) if S == (rho,) else 0)
        n = lat.formula(2, lambda x, S, rho=rho, b=base_n: b(x, S) if rho in S else 0)

        def part(u, v):
            return cr.comb(lat, 3, [(1, cr.cup(u, v)), (1, cr.cup(v, u)), (1, cr.cup(cr.delta(u), u))])
        assert all(part(m, n)(x, S) == 0 for x, S in lat.cells(3))
        assert any(part(m, base_n)(x, S) != 0 for x, S in lat.cells(3))
        assert any(part(base_m, n)(x, S) != 0 for x, S in lat.cells(3))
    return 1


def check_planar(dims, rng):
    """on the fluxes in a coordinate plane, z depends only on the class in the plane"""
    lat = Torus(dims)
    cnt = 0
    for signs in itertools.product((1, -1), repeat=3):
        z, _ = spin_sign(lat, signs)
        sgn = dict(zip(PLANES, signs))
        for rho in (1, 2, 3):
            pla, plb = [pl for pl in PLANES if rho in pl]
            for c in range(dims[rho - 1]):
                tab = {x: rng.randint(0, 1) for x in lat.points() if x[rho - 1] == c}
                mp = lat.formula(1, lambda x, S, rho=rho, tab=tab: tab.get(x, 0) if S == (rho,) else 0)
                parts = [cr.delta(mp)]
                for pl in (pla, plb):
                    for _ in range(rng.randint(0, 3)):
                        pos = tuple(c if d == rho else rng.randrange(dims[d - 1]) for d in pl)
                        parts.append(tube(lat, pl, pos))
                n = add(lat, 2, *parts)
                fl = flux(lat, n)
                wa, wb = fl[pla] % 2, fl[plb] % 2
                assert z(n) == (sgn[pla] ** wa) * (sgn[plb] ** wb) * (-1) ** (wa * wb)
                cnt += 1
    return cnt


def holonomy(signs):
    """SpinStructureHolonomy: 1 periodic, -1 antiperiodic, in the directions 1, 2, 3"""
    s12, s13, s23 = signs
    return [-s23, -s13, -s12]


def count_refinements(dims):
    """the sign functions on the eight classes that satisfy (ii) on the representatives"""
    lat = Torus(dims)
    classes = list(itertools.product((0, 1), repeat=3))
    reps = [thooft(lat, {pl: c[i] for i, pl in enumerate(PLANES)}) for c in classes]
    bb = [[pairing(lat, u, v) for v in reps] for u in reps]
    total = {(i, j): classes.index(tuple((x + y) % 2 for x, y in zip(classes[i], classes[j])))
             for i in range(8) for j in range(8)}
    return sum(1 for f in itertools.product((1, -1), repeat=8)
               if all(f[total[(i, j)]] == f[i] * f[j] * (-1) ** bb[i][j] for i in range(8) for j in range(8)))


# --------------------------------------------------------------------------
# the numbers of Tests/Villain.wlt and Tests/Lattice.wlt
# --------------------------------------------------------------------------

def test_fields(lat):
    m1 = lat.formula(1, lambda x, S: (x[0] + 2 * x[1] + 3 * x[2] + S[0] * (1 + x[0] * x[1] + x[2])) % 3 - 1)
    m2 = lat.formula(1, lambda x, S: (S[0] * x[0] + x[1] * x[2] + 2 * S[0] * x[2] + x[0] + S[0]) % 2)
    one = lat.table(1, {((0, 0, 0), (1,)): 1})
    two = lat.table(1, {((0, 0, 0), (1,)): 1, ((1, 0, 0), (2,)): 1})
    return m1, m2, one, two


def test_numbers():
    out = {}
    lat = Torus((3, 3, 3))
    zero = lat.table(2, {})
    m1, m2, one, two = test_fields(lat)
    fl = thooft(lat, {(1, 2): 1, (1, 3): -2, (2, 3): 3})
    n1 = add(lat, 2, fl, cr.delta(m1))
    unit = lambda c: thooft(lat, {pl: c[i] for i, pl in enumerate(PLANES)})
    n2 = add(lat, 2, unit((1, 1, 0)), cr.delta(m2))
    mu0 = lat.formula(0, lambda x, S: (x[0] * x[1] + 2 * x[2] + x[1]) % 3)
    wall3 = lat.formula(1, lambda x, S: int(S == (3,) and x[2] == 0))
    closed_m = add(lat, 1, cr.delta(mu0), wall3)
    out["obstruction"] = [integrate(lat, torus_anomaly(lat, one, zero)),
                          integrate(lat, torus_anomaly(lat, two, zero)),
                          integrate(lat, torus_anomaly(lat, m2, n1)),
                          integrate(lat, torus_anomaly(lat, closed_m, n1)) % 2]
    sg = lambda s: spin_sign(lat, s)[0]
    out["normalization"] = sg((1, 1, 1))(zero)
    out["labels"] = [sg((-1, 1, -1))(unit(c)) for c in ((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 1, 1))]
    out["loops"] = [sg((1, 1, 1))(cr.delta(two)), sg((-1, -1, -1))(cr.delta(two)), sg((1, 1, 1))(cr.delta(one))]
    q = integrate(lat, torus_anomaly(lat, m2, n1))
    out["cancellation"] = [sg(s)(add(lat, 2, n1, cr.delta(m2))) * sg(s)(n1) == (-1) ** (q % 2)
                           for s in ((1, 1, 1), (-1, 1, -1))]
    b12 = integrate(lat, cr.higher_cup(1, n1, n2))
    out["quadratic"] = [sg(s)(add(lat, 2, n1, n2)) * sg(s)(n1) * sg(s)(n2) == (-1) ** (b12 % 2)
                        for s in ((1, 1, 1), (-1, 1, -1))]
    out["torsor"] = sg((1, 1, 1))(n1) * sg((-1, 1, 1))(n1) == (-1) ** (integrate(lat, cr.cup(wall3, n1)) % 2)
    out["values"] = [sg((1, 1, 1))(n1), sg((1, 1, 1))(n2), sg((1, 1, 1))(add(lat, 2, n1, n2)),
                     sg((-1, 1, -1))(n1), sg((-1, 1, -1))(n2)]
    out["numbers"] = [q, b12, integrate(lat, cr.cup(wall3, n1))]
    out["open"] = sg((1, 1, 1))(lat.table(2, {((0, 0, 0), (1, 2)): 1}))
    # the planar fluxes of Tests/Villain.wlt
    mp1 = lat.formula(1, lambda x, S: (x[1] * x[2] + x[1] + 1) % 2 if S == (1,) and x[0] == 1 else 0)
    mp3 = lat.formula(1, lambda x, S: (x[0] + x[0] * x[1]) % 2 if S == (3,) and x[2] == 0 else 0)
    plane1 = [cr.delta(mp1), add(lat, 2, tube(lat, (1, 2), (1, 0)), cr.delta(mp1)),
              add(lat, 2, tube(lat, (1, 3), (1, 2)), cr.delta(mp1)),
              add(lat, 2, tube(lat, (1, 2), (1, 0)), tube(lat, (1, 3), (1, 2)), cr.delta(mp1))]
    plane3 = [cr.delta(mp3), add(lat, 2, tube(lat, (1, 3), (2, 0)), cr.delta(mp3)),
              add(lat, 2, tube(lat, (2, 3), (1, 0)), cr.delta(mp3)),
              add(lat, 2, tube(lat, (1, 3), (2, 0)), tube(lat, (2, 3), (1, 0)), cr.delta(mp3))]
    out["planar"] = [[[sg(s)(n) for n in plane1], [sg(s)(n) for n in plane3]]
                     for s in ((1, 1, 1), (-1, 1, 1), (-1, -1, 1), (1, -1, -1))]
    out["holonomy"] = [holonomy(s) for s in ((1, 1, 1), (-1, 1, 1), (-1, -1, 1), (1, -1, -1))]
    # Tests/Lattice.wlt
    lat2 = Torus((2, 3, 4))
    zf = {(1, 2): 1, (1, 3): -2, (2, 3): 3}
    m = lat2.formula(1, lambda x, S: (x[0] + 2 * x[1] * S[0] + x[2]) % 3 - 1)
    out["flux"] = [flux(lat2, thooft(lat2, zf)) == zf,
                   flux(lat2, add(lat2, 2, thooft(lat2, zf), cr.delta(m))) == zf,
                   set(flux(lat2, cr.delta(m)).values()) == {0}]
    lat4 = Torus((2, 2, 2, 2))
    z4 = {(1, 2): 1, (1, 3): 2, (1, 4): -1, (2, 3): 3, (2, 4): 5, (3, 4): 7}
    m4 = lat4.formula(1, lambda x, S: (x[0] + x[1] * x[3] + S[0] * x[2]) % 2)
    out["flux"].append(flux(lat4, add(lat4, 2, thooft(lat4, z4), cr.delta(m4))) == z4)
    return out


def main():
    rng = random.Random(20261123)

    cnt = 0
    for (k, tau) in ((1, 3), (2, 5), (3, 7)):
        for top in (3, 4):
            cnt += check_identities(Calc("cube", cr.Lattice(top, 2)), k, tau, rng, top)
            cnt += check_identities(Calc("simplex", n=top), k, tau, rng, top)
    print("inflow, anomaly, descent, cocycle, Gu-Wen form, level 4k (%d cases, cubes and simplices)  True" % cnt)

    cnt = 0
    for dims in ((2, 2, 2), (3, 3, 3), (2, 3, 4), (3, 2, 2)):
        cnt += check_torus(dims, rng)
    print("three-tori (%d): the anomaly is odd for some m, and is cancelled by the signs z  True" % cnt)

    assert [count_refinements(dims) for dims in ((2, 2, 2), (3, 3, 3), (2, 3, 4))] == [8, 8, 8]
    print("eight quadratic refinements on the classes  True")

    cnt = 0
    for dims in ((3, 3, 3), (2, 3, 4), (4, 3, 2)):
        check_planar_identity(dims, rng)
        cnt += check_planar(dims, rng)
    print("fluxes in a coordinate plane: z depends only on the class in the plane (%d cases)  True" % cnt)

    out = test_numbers()
    for key in ("obstruction", "normalization", "labels", "loops", "cancellation", "quadratic", "torsor",
                "values", "numbers", "open", "planar", "holonomy", "flux"):
        print("  %-14s %s" % (key, out[key]))
    assert out["obstruction"][:2] == [0, 1] and out["obstruction"][3] == 0
    assert out["normalization"] == 1 and out["labels"] == [-1, 1, -1, 1, -1]
    assert out["loops"] == [-1, -1, 1]
    assert all(out["cancellation"]) and all(out["quadratic"]) and out["torsor"]
    assert out["open"] is None and all(out["flux"])
    assert out["planar"] == [[[1, 1, 1, -1], [1, 1, 1, -1]], [[1, -1, 1, 1], [1, 1, 1, -1]],
                             [[1, -1, -1, -1], [1, -1, 1, 1]], [[1, 1, -1, 1], [1, -1, -1, -1]]]
    assert out["holonomy"] == [[-1, -1, -1], [-1, -1, 1], [-1, 1, 1], [1, 1, -1]]
    print("the numbers of the Wolfram Language tests  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
