#!/usr/bin/env python3
"""
Reference checks (pure Python, exact rational arithmetic) for U(1) gauge fields
in the modified Villain form and their Deligne-Beilinson product.

A Villain field of degree p is a pair A = (a, n): a real p-cochain a and an
integer (p+1)-cochain n, with

    curvature           F = da - 2 pi n
    gauge               a -> a + d lambda
    large gauge         a -> a + 2 pi m,  n -> n + dm        (m an integer p-cochain)

Both leave F unchanged.  The Deligne-Beilinson product of A (degree p) and
B = (b, n') (degree q) is the Villain field of degree p + q + 1

    A * B = ( a cup F_B / 2 pi + (-1)^p n cup b ,  - n cup n' ).

Checked, for random cochains on a hypercubic lattice and on simplices, with
2 pi replaced by several integers (the identities are polynomial in pi):

  curvature     F(A * B) = F_A cup F_B / 2 pi + (-1)^p (dn cup b - a cup dn')
  gauge of A    (A + d lambda) * B = A * B + d(lambda cup F_B / 2 pi) + (-1)^(p-1) lambda cup dn'
  gauge of B    A * (B + d mu) = A * B - d(n cup mu) + dn cup mu
  large, A      the flux changes by d(- m cup n') + (-1)^p m cup dn', the connection by
                2 pi (- m cup n') + (-1)^p d(m cup b)
  large, B      the flux changes by d((-1)^p n cup l) - (-1)^p dn cup l, the connection by
                2 pi (-1)^p n cup l
  so for closed fluxes the product is defined on gauge classes.

  Chern-Simons  the modified Villain Lagrangian of arXiv:2303.06160, eq. (17), is
                    (k / 2) (connection of A * A) - (k / 2) a cup_1 dn + phi cup dn
  flat fields   a flat Z_N gauge field with the integer lift At is the Villain field
                (2 pi At / N, d At / N), with F = 0.  On it the Chern-Simons Lagrangian over
                2 pi is - (k / 2 N^2) dAt cup At; for even k this is a cocycle on K(Z_N, 1), in
                the class of the Dijkgraaf-Witten weight of level - k / 2:
                U(1)_k restricted to Z_N is the pointed category Vec_(Z_N) with that associator.

  commutativity the product is graded commutative up to a gauge transformation and one more
                term.  With e = (-1)^((p+1)(q+1)) and s = (-1)^(p+q),
                    lambda = ((-1)^p a cup b - (-1)^q F_A cup_1 b) / 2 pi - s a cup_1 n'
                    m      = s n cup_1 n'
                    conn(A * B) - e conn(B * A) = d lambda + 2 pi m - s F_A cup_1 F_B / 2 pi
                                                  + (-1)^q (a cup_1 dn' - dn cup_1 b)
                    flux(A * B) - e flux(B * A) = dm - s (dn cup_1 n' - (-1)^p n cup_1 dn')
                The term with F_A cup_1 F_B is gauge invariant and is not a gauge transformation;
                it vanishes if one of the two fields has F = 0.
  theta term    (1 / 8 pi^2) F cup F = (1 / 4 pi) F(A * A) + W,
                    W = - (-1)^p (1 / 4 pi) (dn cup a - a cup dn),
                and under a -> a + d lambda the term W changes by
                    - (1 / 4 pi) d(dn cup lambda - (-1)^p lambda cup dn):
                the monopole current dn carries the electric charge theta / 2 pi (Witten effect).
  the charge    on the four-torus with the flux z (n = flux + dm, a arbitrary):
                    sum of (1 / 8 pi^2) F cup F = (1 / 2) sum of n cup n = Pf(z), an integer.

  differential  a differential cochain of degree k is a triple x = (c, h, w): an integer k-cochain,
  cochains      a real (k-1)-cochain and a real k-cochain (Hopkins-Singer, with the differential
                form replaced by a cochain), with
                    d(c, h, w) = (dc, w - c - dh, dw)
                    x . y      = (c1 cup c2, (-1)^k1 c1 cup h2 + h1 cup w2, w1 cup w2)
                d d = 0, d(x . y) = dx . y + (-1)^k1 x . dy, the product is associative, and
                    x . y - (-1)^(k1 k2) y . x = d H(x, y) + H(dx, y) + (-1)^k1 H(x, dy)
                    H(x, y) = ( s c1 cup_1 c2,
                                (-1)^k1 h1 cup h2 - (-1)^k2 w1 cup_1 h2 - (-1)^(k1+k2) h1 cup_1 c2,
                                s w1 cup_1 w2 ),     s = (-1)^(k1+k2+1)
                A Villain field A = (a, n) of degree p is the differential cochain
                T(A) = (-n, a / 2 pi, F / 2 pi) of degree p + 1.  These are the differential
                cochains whose coboundary has no middle component; d T(A) = (-dn, 0, -dn).
                Gauge and large gauge transformations add d(-m, -lambda / 2 pi, 0).
                T(A) . T(B) and T(A * B) have the same first two components, and the third
                components differ by the middle component of d(T(A) . T(B)), which has dn, dn'.
                H(T(A), T(B)) = (-m, -lambda / 2 pi, defect / 2 pi) with the lambda, m and the
                defect - s F_A cup_1 F_B / 2 pi of the commutativity above.
  zero modes    the quadratic form sum of a cup da on the three-torus with sides (L1, L2, L3) has,
                besides the closed 1-cochains, 2 V / lcm(L1, L2, L3) zero modes if the lcm is even
                (V = L1 L2 L3) and none if all sides are odd: two for each momentum with
                p1 + p2 + p3 = pi (the staggered modes of arXiv:2303.06160).
  large gauge   the boundary term B(m; a) = -(k/2) m cup a of the large gauge variation satisfies
                B(m + m'; a) - B(m; a + 2 pi m') - B(m'; a) = k pi m cup m'.

Run:  python3 reference/villain_reference.py
"""

import itertools
import random
import sys
from fractions import Fraction as Fr

import cubical_reference as cr
import simplicial_reference as sr
from bar_reference import EM
from encategory_reference import mod1


class Calc:
    """the operations on one kind of lattice, with the same interface"""

    def __init__(self, kind, lat=None, n=None):
        self.kind, self.lat, self.n = kind, lat, n

    def rand(self, p, rng):
        return self.lat.random_cochain(p, rng) if self.kind == "cube" else sr.rand(p, rng, self.n)

    def d(self, a):
        return cr.delta(a) if self.kind == "cube" else sr.delta(a)

    def cup(self, a, b, i=0):
        return cr.higher_cup(i, a, b) if self.kind == "cube" else sr.cupi(i, a, b)

    def lin(self, deg, *terms):
        terms = [(c, u) for c, u in terms if c != 0]
        if self.kind == "cube":
            return cr.comb(self.lat, deg, terms)
        return sr.Co(deg, lambda v: sum(c * u(v) for c, u in terms))

    def equal(self, u, v, deg):
        if self.kind == "cube":
            return cr.equal(self.lat, u, v, deg)
        return sr.vec(u, self.n) == sr.vec(v, self.n)


def curvature(C, A, tau):
    a, n = A
    return C.lin(a.p + 1, (1, C.d(a)), (-tau, n))


def product(C, A, B, tau):
    (a, n), (b, n2) = A, B
    p, q = a.p, b.p
    conn = C.lin(p + q + 1, (Fr(1, tau), C.cup(a, curvature(C, B, tau))), ((-1) ** p, C.cup(n, b)))
    flux = C.lin(p + q + 2, (-1, C.cup(n, n2)))
    return conn, flux


def check_product(C, p, q, tau, rng, top):
    """the identities of the product in the degrees up to top"""
    a, n = C.rand(p, rng), C.rand(p + 1, rng)
    b, n2 = C.rand(q, rng), C.rand(q + 1, rng)
    A, B = (a, n), (b, n2)
    conn, flux = product(C, A, B, tau)
    FA, FB = curvature(C, A, tau), curvature(C, B, tau)
    s = (-1) ** p
    done = 0
    if p + q + 2 <= top:
        lhs = curvature(C, (conn, flux), tau)
        rhs = C.lin(p + q + 2, (Fr(1, tau), C.cup(FA, FB)), (s, C.cup(C.d(n), b)), (-s, C.cup(a, C.d(n2))))
        assert C.equal(lhs, rhs, p + q + 2), ("curvature", C.kind, p, q)
        done += 1
    # small gauge transformation of A
    lam = C.rand(p - 1, rng)
    c2, f2 = product(C, (C.lin(p, (1, a), (1, C.d(lam))), n), B, tau)
    rhs = C.lin(p + q + 1, (1, conn), (Fr(1, tau), C.d(C.cup(lam, FB))), ((-1) ** (p - 1), C.cup(lam, C.d(n2))))
    assert C.equal(c2, rhs, p + q + 1), ("gauge A", C.kind, p, q)
    if p + q + 2 <= top:
        assert C.equal(f2, flux, p + q + 2)
    # small gauge transformation of B
    mu = C.rand(q - 1, rng)
    c2, f2 = product(C, A, (C.lin(q, (1, b), (1, C.d(mu))), n2), tau)
    rhs = C.lin(p + q + 1, (1, conn), (-1, C.d(C.cup(n, mu))), (1, C.cup(C.d(n), mu)))
    assert C.equal(c2, rhs, p + q + 1), ("gauge B", C.kind, p, q)
    # large gauge transformation of A
    m = C.rand(p, rng)
    c2, f2 = product(C, (C.lin(p, (1, a), (tau, m)), C.lin(p + 1, (1, n), (1, C.d(m)))), B, tau)
    rhs = C.lin(p + q + 1, (1, conn), (-tau, C.cup(m, n2)), (s, C.d(C.cup(m, b))))
    assert C.equal(c2, rhs, p + q + 1), ("large A", C.kind, p, q)
    if p + q + 2 <= top:
        rhs = C.lin(p + q + 2, (1, flux), (-1, C.d(C.cup(m, n2))), (s, C.cup(m, C.d(n2))))
        assert C.equal(f2, rhs, p + q + 2), ("large A flux", C.kind, p, q)
    # large gauge transformation of B
    l = C.rand(q, rng)
    c2, f2 = product(C, A, (C.lin(q, (1, b), (tau, l)), C.lin(q + 1, (1, n2), (1, C.d(l)))), tau)
    rhs = C.lin(p + q + 1, (1, conn), (tau * s, C.cup(n, l)))
    assert C.equal(c2, rhs, p + q + 1), ("large B", C.kind, p, q)
    if p + q + 2 <= top:
        rhs = C.lin(p + q + 2, (1, flux), (s, C.d(C.cup(n, l))), (-s, C.cup(C.d(n), l)))
        assert C.equal(f2, rhs, p + q + 2), ("large B flux", C.kind, p, q)
    return done


def check_swap(C, p, q, tau, rng, top):
    """graded commutativity of the product, up to a gauge transformation and F_A cup_1 F_B"""
    a, n = C.rand(p, rng), C.rand(p + 1, rng)
    b, n2 = C.rand(q, rng), C.rand(q + 1, rng)
    A, B = (a, n), (b, n2)
    FA, FB = curvature(C, A, tau), curvature(C, B, tau)
    eps = (-1) ** ((p + 1) * (q + 1))
    s = (-1) ** (p + q)
    sq = (-1) ** q
    c1, f1 = product(C, A, B, tau)
    c2, f2 = product(C, B, A, tau)
    lam = C.lin(p + q, (Fr((-1) ** p, tau), C.cup(a, b)), (Fr(-sq, tau), C.cup(FA, b, 1)), (-s, C.cup(a, n2, 1)))
    m = C.lin(p + q + 1, (s, C.cup(n, n2, 1)))
    lhs = C.lin(p + q + 1, (1, c1), (-eps, c2))
    rhs = C.lin(p + q + 1, (1, C.d(lam)), (tau, m), (Fr(-s, tau), C.cup(FA, FB, 1)),
                (sq, C.cup(a, C.d(n2), 1)), (-sq, C.cup(C.d(n), b, 1)))
    assert C.equal(lhs, rhs, p + q + 1), ("swap, connection", C.kind, p, q)
    # without the term F_A cup_1 F_B the identity fails
    bad = C.lin(p + q + 1, (1, C.d(lam)), (tau, m),
                (sq, C.cup(a, C.d(n2), 1)), (-sq, C.cup(C.d(n), b, 1)))
    generic = not C.equal(lhs, bad, p + q + 1)
    done = 0
    if p + q + 2 <= top:
        lhs = C.lin(p + q + 2, (1, f1), (-eps, f2))
        rhs = C.lin(p + q + 2, (1, C.d(m)), (-s, C.cup(C.d(n), n2, 1)), (s * (-1) ** p, C.cup(n, C.d(n2), 1)))
        assert C.equal(lhs, rhs, p + q + 2), ("swap, flux", C.kind, p, q)
        done = 1
    return done, generic


def check_theta(C, p, tau, rng):
    """the theta term, the curvature of A * A, and the coupling to the monopole current"""
    a, n = C.rand(p, rng), C.rand(p + 1, rng)
    lam = C.rand(p - 1, rng)
    A = (a, n)
    F = curvature(C, A, tau)
    top = 2 * p + 2
    sp = (-1) ** p

    def witten(aa):
        return C.lin(top, (Fr(-sp, 2 * tau), C.cup(C.d(n), aa)), (Fr(sp, 2 * tau), C.cup(aa, C.d(n))))
    theta = C.lin(top, (Fr(1, 2 * tau * tau), C.cup(F, F)))
    FAA = curvature(C, product(C, A, A, tau), tau)
    assert C.equal(theta, C.lin(top, (Fr(1, 2 * tau), FAA), (1, witten(a))), top), ("theta", C.kind, p)
    conn, flux = product(C, A, A, tau)
    assert C.equal(theta, C.lin(top, (Fr(1, 2 * tau), C.d(conn)), (Fr(1, 2), C.cup(n, n)), (1, witten(a))), top)
    a2 = C.lin(p, (1, a), (1, C.d(lam)))
    lhs = C.lin(top, (1, witten(a2)), (-1, witten(a)))
    rhs = C.lin(top, (Fr(-1, 2 * tau), C.d(C.cup(C.d(n), lam))), (Fr(sp, 2 * tau), C.d(C.cup(lam, C.d(n)))))
    assert C.equal(lhs, rhs, top), ("Witten", C.kind, p)
    # the theta term itself is gauge invariant
    F2 = curvature(C, (a2, n), tau)
    assert C.equal(C.cup(F2, F2), C.cup(F, F), top)


def check_charge(rng):
    """the topological charge on the four-torus is the Pfaffian of the flux"""
    out = []
    for L in (2, 3):
        lat = cr.Lattice(4, L)
        C = Calc("cube", lat)
        for trial in range(3):
            z12, z13, z14, z23, z24, z34 = [rng.randint(-3, 3) for _ in range(6)]
            z = [[0, z12, z13, z14], [-z12, 0, z23, z24], [-z13, -z23, 0, z34], [-z14, -z24, -z34, 0]]

            def f(x, S, z=z, L=L):
                m_, n_ = S
                return z[m_ - 1][n_ - 1] if (x[m_ - 1] == L - 1 and x[n_ - 1] == L - 1) else 0
            flux = cr.Cochain(lat, 2, f)
            n = C.lin(2, (1, flux), (1, C.d(C.rand(1, rng))))
            assert cr.equal(lat, C.d(n), C.lin(3), 3)
            a = C.lin(1, (Fr(1, 3), C.rand(1, rng)))
            pf = z12 * z34 - z13 * z24 + z14 * z23
            pts = list(itertools.product(range(L), repeat=4))
            assert sum(C.cup(n, n)(x, (1, 2, 3, 4)) for x in pts) == 2 * pf
            for tau in (3, 5, 7):
                F = curvature(C, (a, n), tau)
                dens = C.cup(F, F)
                total = sum(dens(x, (1, 2, 3, 4)) for x in pts)
                assert Fr(total, 2 * tau * tau) == pf, ("charge", L, z, tau)
            out.append(pf)
    return out


# ---- differential cochains: triples (c, h, w) of degrees (k, k - 1, k) ----

def dc_d(C, x, k):
    c, h, w = x
    return (C.d(c), C.lin(k, (1, w), (-1, c), (-1, C.d(h))), C.d(w))


def dc_prod(C, x, k1, y, k2):
    (c1, h1, w1), (c2, h2, w2) = x, y
    return (C.cup(c1, c2),
            C.lin(k1 + k2 - 1, ((-1) ** k1, C.cup(c1, h2)), (1, C.cup(h1, w2))),
            C.cup(w1, w2))


def dc_hom(C, x, k1, y, k2):
    (c1, h1, w1), (c2, h2, w2) = x, y
    s = (-1) ** (k1 + k2 + 1)
    hh = C.lin(k1 + k2 - 2, ((-1) ** k1, C.cup(h1, h2)), (-(-1) ** k2, C.cup(w1, h2, 1)),
               (-(-1) ** (k1 + k2), C.cup(h1, c2, 1)))
    return (C.lin(k1 + k2 - 1, (s, C.cup(c1, c2, 1))), hh, C.lin(k1 + k2 - 1, (s, C.cup(w1, w2, 1))))


def dc_add(C, k, *terms):
    return tuple(C.lin(k - (1 if i == 1 else 0), *[(co, t[i]) for co, t in terms]) for i in range(3))


def dc_equal(C, x, y, k, top):
    return all(C.equal(x[i], y[i], deg) for i, deg in ((0, k), (1, k - 1), (2, k)) if deg <= top)


def dc_of_villain(C, A, tau):
    a, n = A
    p = a.p
    return (C.lin(p + 1, (-1, n)), C.lin(p, (Fr(1, tau), a)), C.lin(p + 1, (Fr(1, tau), curvature(C, A, tau))))


def check_differential(C, k1, k2, tau, rng, top):
    """the complex of differential cochains, its product, and Villain fields inside it"""
    def gen(k):
        return (C.rand(k, rng), C.lin(k - 1, (Fr(1, 3), C.rand(k - 1, rng))), C.lin(k, (Fr(1, 2), C.rand(k, rng))))
    x, y, z = gen(k1), gen(k2), gen(k1)
    zero = lambda k: (C.lin(k), C.lin(k - 1), C.lin(k))
    assert dc_equal(C, dc_d(C, dc_d(C, x, k1), k1 + 1), zero(k1 + 2), k1 + 2, top), "d d"
    lhs = dc_d(C, dc_prod(C, x, k1, y, k2), k1 + k2)
    rhs = dc_add(C, k1 + k2 + 1, (1, dc_prod(C, dc_d(C, x, k1), k1 + 1, y, k2)),
                 ((-1) ** k1, dc_prod(C, x, k1, dc_d(C, y, k2), k2 + 1)))
    assert dc_equal(C, lhs, rhs, k1 + k2 + 1, top), ("Leibniz", C.kind, k1, k2)
    lhs = dc_prod(C, dc_prod(C, x, k1, y, k2), k1 + k2, z, k1)
    rhs = dc_prod(C, x, k1, dc_prod(C, y, k2, z, k1), k2 + k1)
    assert dc_equal(C, lhs, rhs, 2 * k1 + k2, top), ("associativity", C.kind, k1, k2)
    eps = (-1) ** (k1 * k2)
    lhs = dc_add(C, k1 + k2, (1, dc_prod(C, x, k1, y, k2)), (-eps, dc_prod(C, y, k2, x, k1)))
    rhs = dc_add(C, k1 + k2, (1, dc_d(C, dc_hom(C, x, k1, y, k2), k1 + k2 - 1)),
                 (1, dc_hom(C, dc_d(C, x, k1), k1 + 1, y, k2)),
                 ((-1) ** k1, dc_hom(C, x, k1, dc_d(C, y, k2), k2 + 1)))
    assert dc_equal(C, lhs, rhs, k1 + k2, top), ("homotopy", C.kind, k1, k2)

    # Villain fields
    p, q = k1 - 1, k2 - 1
    a, n = C.rand(p, rng), C.rand(p + 1, rng)
    b, n2 = C.rand(q, rng), C.rand(q + 1, rng)
    A, B = (a, n), (b, n2)
    TA, TB = dc_of_villain(C, A, tau), dc_of_villain(C, B, tau)
    dn = C.d(n)
    assert dc_equal(C, dc_d(C, TA, k1), (C.lin(k1 + 1, (-1, dn)), C.lin(k1), C.lin(k1 + 1, (-1, dn))), k1 + 1, top)
    lam, m = C.rand(p - 1, rng), C.rand(p, rng)
    A2 = (C.lin(p, (1, a), (1, C.d(lam)), (tau, m)), C.lin(p + 1, (1, n), (1, C.d(m))))
    xi = (C.lin(p, (-1, m)), C.lin(p - 1, (Fr(-1, tau), lam)), C.lin(p))
    assert dc_equal(C, dc_of_villain(C, A2, tau), dc_add(C, k1, (1, TA), (1, dc_d(C, xi, p))), k1, top), "gauge"
    PT = dc_prod(C, TA, k1, TB, k2)
    TP = dc_of_villain(C, product(C, A, B, tau), tau)
    mid = dc_d(C, PT, k1 + k2)[1]
    assert C.equal(PT[0], TP[0], k1 + k2) if k1 + k2 <= top else True
    assert C.equal(PT[1], TP[1], k1 + k2 - 1)
    if k1 + k2 <= top:
        assert C.equal(TP[2], C.lin(k1 + k2, (1, PT[2]), (-1, mid)), k1 + k2), "product, third component"
    # the homotopy on Villain fields is the gauge transformation of the commutativity
    FA, FB = curvature(C, A, tau), curvature(C, B, tau)
    s, sq = (-1) ** (p + q), (-1) ** q
    lam_s = C.lin(p + q, (Fr((-1) ** p, tau), C.cup(a, b)), (Fr(-sq, tau), C.cup(FA, b, 1)), (-s, C.cup(a, n2, 1)))
    m_s = C.lin(p + q + 1, (s, C.cup(n, n2, 1)))
    defect = C.lin(p + q + 1, (Fr(-s, tau), C.cup(FA, FB, 1)))
    Hv = dc_hom(C, TA, k1, TB, k2)
    assert dc_equal(C, Hv, (C.lin(p + q + 1, (-1, m_s)), C.lin(p + q, (Fr(-1, tau), lam_s)),
                            C.lin(p + q + 1, (Fr(1, tau), defect))), k1 + k2 - 1, top), "homotopy on Villain fields"


# ---- zero modes of the Chern-Simons quadratic form on a three-torus ----

def rank_mod(M, p):
    M = [row[:] for row in M]
    r, ncol = 0, len(M[0])
    for col in range(ncol):
        piv = next((i for i in range(r, len(M)) if M[i][col] % p), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][col], p - 2, p)
        M[r] = [(v * inv) % p for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col] % p:
                f = M[i][col]
                M[i] = [(u - f * v) % p for u, v in zip(M[i], M[r])]
        r += 1
    return r


def cs_matrix(dims):
    """the matrix M with  sum of a cup da = a^T M a  on the periodic lattice with sides dims"""
    sites = list(itertools.product(*[range(L) for L in dims]))
    idx = {}
    for x in sites:
        for mu in (1, 2, 3):
            idx[(x, mu)] = len(idx)

    def sh(x, *dirs):
        x = list(x)
        for mu in dirs:
            x[mu - 1] = (x[mu - 1] + 1) % dims[mu - 1]
        return tuple(x)

    def da(x, mu, nu):
        return [(1, idx[(sh(x, mu), nu)]), (-1, idx[(x, nu)]), (-1, idx[(sh(x, nu), mu)]), (1, idx[(x, mu)])]
    N = len(idx)
    M = [[0] * N for _ in range(N)]
    for x in sites:
        for mu, (b1, b2), sg in ((1, (2, 3), 1), (2, (1, 3), -1), (3, (1, 2), 1)):
            for c, j in da(sh(x, mu), b1, b2):
                M[idx[(x, mu)]][j] += sg * c
    return M, idx


def cs_zero_modes(dims):
    """zero modes of the symmetric form, beyond the closed 1-cochains"""
    M, idx = cs_matrix(dims)
    N, V = len(idx), dims[0] * dims[1] * dims[2]
    S = [[M[i][j] + M[j][i] for j in range(N)] for i in range(N)]
    r = min(rank_mod(S, 1000003), rank_mod(S, 998244353))
    return N - r - (V - 1 + 3)


def staggered_momenta(dims):
    """the number of momenta with p1 + p2 + p3 = pi"""
    return sum(1 for ns in itertools.product(*[range(L) for L in dims])
               if sum(Fr(n_, L) for n_, L in zip(ns, dims)) % 1 == Fr(1, 2))


def lcm3(dims):
    from math import gcd
    out = 1
    for L in dims:
        out = out * L // gcd(out, L)
    return out


def check_zero_modes(rng):
    # the matrix agrees with the cochain operations of cubical_reference on cubic tori
    for L in (2, 3):
        lat = cr.Lattice(3, L)
        M, idx = cs_matrix((L, L, L))
        for trial in range(3):
            a = lat.random_cochain(1, rng)
            total = sum(cr.cup(a, cr.delta(a))(x, (1, 2, 3)) for x in itertools.product(range(L), repeat=3))
            vec = [0] * len(idx)
            for (x, mu), i in idx.items():
                vec[i] = a(x, (mu,))
            assert total == sum(vec[i] * M[i][j] * vec[j] for i in range(len(vec)) for j in range(len(vec)) if M[i][j])
    table = {}
    for dims in [(2, 2, 2), (3, 3, 3), (2, 3, 3), (2, 2, 3), (2, 3, 4), (4, 4, 4), (3, 3, 5), (3, 4, 5), (6, 3, 3), (6, 4, 2)]:
        zm, ns = cs_zero_modes(dims), staggered_momenta(dims)
        V, l = dims[0] * dims[1] * dims[2], lcm3(dims)
        assert zm == 2 * ns and ns == (V // l if l % 2 == 0 else 0), (dims, zm, ns)
        table[dims] = zm
    return table


def chern_simons(C, k, a, n, phi, tau):
    """ModifiedVillainCS of Operadica`Gauge`, with 2 pi = tau"""
    return C.lin(3,
                 (Fr(k, 2 * tau), C.cup(a, C.d(a))),
                 (Fr(-k, 2), C.cup(a, n)), (Fr(-k, 2), C.cup(n, a)),
                 (Fr(-k, 2), C.cup(a, C.d(n), 1)),
                 (1, C.cup(phi, C.d(n))))


def main():
    rng = random.Random(20261123)

    # ---- the product ----
    cnt = 0
    for tau in (3, 5, 7):
        cube3, cube4 = Calc("cube", cr.Lattice(3, 2)), Calc("cube", cr.Lattice(4, 2))
        check_product(cube3, 1, 1, tau, rng, 3)
        cnt += check_product(cube4, 1, 1, tau, rng, 4)
        check_product(cube4, 1, 2, tau, rng, 4)
        check_product(cube4, 2, 1, tau, rng, 4)
        for p in (1, 2):
            for q in (1, 2):
                cnt += check_product(Calc("simplex", n=p + q + 2), p, q, tau, rng, p + q + 2)
    print("Deligne-Beilinson product: curvature, gauge and large gauge transformations (%d full cases)  True" % cnt)

    # ---- graded commutativity ----
    cnt, generic = 0, True
    for tau in (3, 5, 7):
        cube3, cube4 = Calc("cube", cr.Lattice(3, 2)), Calc("cube", cr.Lattice(4, 2))
        for C, p, q, top in ((cube3, 1, 1, 3), (cube4, 1, 1, 4), (cube4, 1, 2, 4), (cube4, 2, 1, 4)):
            done, g = check_swap(C, p, q, tau, rng, top)
            cnt, generic = cnt + done, generic and g
        for p in (1, 2):
            for q in (1, 2):
                done, g = check_swap(Calc("simplex", n=p + q + 2), p, q, tau, rng, p + q + 2)
                cnt, generic = cnt + done, generic and g
    assert generic
    print("A * B = (-1)^((p+1)(q+1)) B * A up to a gauge transformation and - (-1)^(p+q) F_A cup_1 F_B / 2 pi"
          " (%d full cases)  True" % cnt)

    # ---- the theta term ----
    for tau in (3, 5, 7):
        check_theta(Calc("cube", cr.Lattice(4, 2)), 1, tau, rng)
        check_theta(Calc("simplex", n=4), 1, tau, rng)
    check_theta(Calc("simplex", n=6), 2, 5, rng)
    print("theta term = (1/4 pi) F(A * A) + the coupling of a to the monopole current, charge theta / 2 pi  True")
    charges = check_charge(rng)
    print("topological charge on the four-torus = Pf(z):", charges, " True")

    # ---- differential cochains ----
    for tau in (3, 5):
        cube4 = Calc("cube", cr.Lattice(4, 2))
        check_differential(cube4, 2, 2, tau, rng, 4)
        for k1, k2 in ((2, 2), (2, 3), (3, 2)):
            check_differential(Calc("simplex", n=2 * k1 + k2), k1, k2, tau, rng, 2 * k1 + k2)
    check_differential(Calc("cube", cr.Lattice(5, 2)), 2, 2, 7, rng, 5)
    print("differential cochains: d d = 0, the Leibniz rule, associativity, the commutativity homotopy;"
          " Villain fields as differential cochains  True")

    # ---- zero modes of a cup da on three-tori ----
    table = check_zero_modes(rng)
    print("zero modes of a cup da beyond the closed cochains = 2 x (momenta with p1 + p2 + p3 = pi):", table, " True")

    # ---- the algebra of large gauge transformations ----
    for C in (Calc("cube", cr.Lattice(2, 3)), Calc("simplex", n=2)):
        for k in (1, 2, 3):
            for tau in (3, 5):
                a, m, m2 = C.rand(1, rng), C.rand(1, rng), C.rand(1, rng)
                bt = lambda mm, aa: C.lin(2, (Fr(-k, 2), C.cup(mm, aa)))
                lhs = C.lin(2, (1, bt(C.lin(1, (1, m), (1, m2)), a)), (-1, bt(m, C.lin(1, (1, a), (tau, m2)))), (-1, bt(m2, a)))
                assert C.equal(lhs, C.lin(2, (Fr(k * tau, 2), C.cup(m, m2))), 2)
        m, m2 = C.rand(1, rng), C.rand(1, rng)
        lhs = C.lin(2, (1, C.cup(m, m2)), (1, C.cup(m2, m)))
        rhs = C.lin(2, (-1, C.d(C.cup(m, m2, 1))), (1, C.cup(C.d(m), m2, 1)), (-1, C.cup(m, C.d(m2), 1)))
        assert C.equal(lhs, rhs, 2)
    print("large gauge transformations compose up to k pi m cup m'; its symmetric part is a cup_1 expression  True")

    # ---- Chern-Simons ----
    for tau in (3, 5, 7):
        for C in (Calc("cube", cr.Lattice(3, 2)), Calc("simplex", n=3)):
            a, n, phi = C.rand(1, rng), C.rand(2, rng), C.rand(0, rng)
            for k in (1, 2, 3):
                conn, flux = product(C, (a, n), (a, n), tau)
                rhs = C.lin(3, (Fr(k, 2), conn), (Fr(-k, 2), C.cup(a, C.d(n), 1)), (1, C.cup(phi, C.d(n))))
                assert C.equal(chern_simons(C, k, a, n, phi, tau), rhs, 3), (C.kind, k)
    print("modified Villain Chern-Simons = (k/2) (A * A) - (k/2) a cup_1 dn + phi cup dn  True")

    # ---- flat Z_N fields ----
    v = (0, 1, 2, 3)
    table = {}
    for N in (2, 3, 4, 5):
        K = EM((N,), 1)
        C = Calc("simplex", n=3)

        def cs_weight(k, tau=7):
            def w(x):
                At = sr.lift(K, x, 3)
                dAt = sr.delta(At)
                a = sr.Co(1, lambda e: Fr(tau, N) * At(e))
                n = sr.Co(2, lambda f: Fr(dAt(f), N))
                assert all(n(f).denominator == 1 for f in [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)])
                phi = sr.Co(0, lambda u: 0)
                assert curvature(C, (a, n), tau)((0, 1, 2)) == 0
                val = chern_simons(C, k, a, n, phi, tau)(v) / tau
                assert val == Fr(-k, 2 * N * N) * sr.cup(dAt, At)(v)
                return mod1(val)
            return w
        for k in range(0, 2 * N + 2):
            w = cs_weight(k)
            ok = sr.cocycle_q(K, 3, w)
            level = None
            if ok:
                for kk in range(N):
                    _, dw = sr.dw_weight(N, kk)
                    if sr.class_order(K, 3, lambda x: mod1(w(x) - dw(x))) == 1:
                        level = kk
            table[(N, k)] = (ok, level)
    for N in (2, 3, 4, 5):
        print("   N = %d:" % N, [(k, table[(N, k)]) for k in range(0, 2 * N + 2)])
    for (N, k), (ok, level) in table.items():
        if k % 2 == 0:
            assert ok and level == (-k // 2) % N, (N, k, ok, level)
    print("on flat Z_N fields: U(1)_k for even k is the Dijkgraaf-Witten class of level - k/2 mod N  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
