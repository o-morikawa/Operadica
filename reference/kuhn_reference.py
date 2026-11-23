"""
The triangulation behind the integral of the star product, and the sign of odd-level
Chern-Simons theory on its cocycles (Operadica`Villain`: CechDeRhamSpinStructureSign,
CechDeRhamCupOnePairing).

The sites of the chain of star_reference.py are the tetrahedra

    (x - e_a - e_b - e_c,  x - e_b - e_c,  x - e_c,  x),     (a, b, c) an order of (1, 2, 3),

of cubes, with the coefficient the sign of the permutation (a, b, c): the triangulation of the
dual cubic lattice with six tetrahedra in every dual cube (Kuhn, Freudenthal), the vertices of
a tetrahedron ordered along the diagonal.  It is a closed 3-manifold: 6 V tetrahedra, 12 V
triangles, each in two tetrahedra, 7 V edges, and the chain is its fundamental cycle.

So the Cech form of the anomaly (star_reference.py, statement 6) is the simplicial

    q(m, N) = m cup N + N cup m + dm cup m

summed over this triangulation, for the restrictions of m to its edges and of N to its
triangles.  Statements checked, for 2-cocycles N of the triangulation modulo 2:

 1. every N is N(n0) + dm with N(n0) the cocycle of a flux n0 = THooftFluxCochain (the Chern
    numbers of N modulo 2), and

        zc(N) = z(n0) (-1)^(sum q(m, N(n0)))

    does not depend on the solution m (z a sign of oddlevel_reference.py, here computed as
    the Grassmann integral of grassmann_reference.py);
 2. zc(N(n)) = z(n) for the cocycle of every flat Villain field: zc extends z;
 3. zc(N + dm) = zc(N) (-1)^(sum q(m, N)): with it, exp(i pi k (integral of the square)) zc(N)^k
    does not change under the gauge transformations of the cocycle, for odd k;
 4. zc(N + N') = zc(N) zc(N') (-1)^(sum N cup_1 N') with the cup-1 product of Steenrod on
    the tetrahedra, (N cup_1 N')(pqrs) = N(prs) N'(pqr) + N(pqs) N'(qrs) modulo 2;
 5. sum N(n) cup_1 N(n') = sum n cup_1 n' modulo 2: the descent takes the cup-1 pairing of the
    cubic lattice to that of the triangulation.

A local formula: the Grassmann integral of Gu and Wen on the triangulation.  Every triangle
on which N is odd carries two Grassmann variables, one in each of its two tetrahedra.  For the
tetrahedron (v0, v1, v2, v3) with the faces f_i (v_i omitted), the product of the variables of
its odd faces is taken in the order

    f0, f2, f1, f3   if the coefficient is +1,       f3, f1, f2, f0   if it is -1,

and the pair of a triangle is integrated with the weight 1 for (the variable of the
tetrahedron in which the triangle is f_i with (coefficient) (-1)^i = +1)(the other one).
sg(N) is the sign of the permutation that sorts the variables into the pairs.

 6. among the 576 pairs of orders of the four faces (one for each orientation), 32 give a
    function with (ii); the orders above (those of Gu and Wen) are one of them;
 7. sg(N + dm) = sg(N) (-1)^(sum q(m, N) + sum of m over ALL edges): the defect is linear in
    m, does not depend on N, and its chain w is the sum of all the edges of the triangulation
    (a cycle: 14 edges at every vertex).  This is the representative of the second
    Stiefel-Whitney class for this integral;
 8. w is the boundary, modulo 2, of the chain E of the triangles (p, p + e_mu, p + e_1 + e_2 +
    e_3), mu = 1, 2, 3, so  sg(N) (-1)^(sum of N over E)  satisfies (i) and (ii): a spin
    structure is a chain with the boundary w;
 9. with this E it is the sign zc of the spin structure that is periodic in the three
    directions, for every size, and with h_rho^(Chern number of N for the plane normal to
    rho) it is zc for the boundary conditions h: the same statement as for the cubic lattice
    (grassmann_reference.py).

Run:  python3 reference/kuhn_reference.py
"""

import itertools
import random
import sys

import cubical_reference as cr
from oddlevel_reference import Torus, thooft, add, integrate, torus_anomaly, PLANES
from cech_reference import addv, unit, primitive, transition, chern, test_fields
from star_reference import explicit_cycle, large_gauge, cech_anomaly, test_mm
from grassmann_reference import gu_wen, closed_sample
from grassmann_reference import perm_sign as gr_sign


def perm_sign(p):
    s = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s = -s
    return s


class Kuhn:
    def __init__(self, dims):
        self.dims, self.lat = dims, Torus(dims)
        self.tets = {ps: c for (x, dirs, ps), c in explicit_cycle(dims)[3].items()}
        self.tris = sorted({t[:i] + t[i + 1:] for t in self.tets for i in range(4)})
        self.edges = sorted({(t[i], t[j]) for t in self.tets for i in range(4) for j in range(i + 1, 4)})
        self.eidx = {e: i for i, e in enumerate(self.edges)}

    def restrict(self, nn):
        return {f: nn(*f) % 2 for f in self.tris}

    def delta(self, m):
        return {f: (m[(f[1], f[2])] + m[(f[0], f[2])] + m[(f[0], f[1])]) % 2 for f in self.tris}

    def addc(self, u, v):
        return {f: (u[f] + v[f]) % 2 for f in self.tris}

    def anomaly(self, m, N):
        tot = 0
        for (p, q, r, s), c in self.tets.items():
            dm = m[(q, r)] + m[(p, r)] + m[(p, q)]
            tot += m[(p, q)] * N[(q, r, s)] + N[(p, q, r)] * m[(r, s)] + dm * m[(r, s)]
        return tot % 2

    def cup1(self, N, N2):
        return sum(N[(p, r, s)] * N2[(p, q, r)] + N[(p, q, s)] * N2[(q, r, s)] for (p, q, r, s) in self.tets) % 2

    def chern_numbers(self, N):
        out = []
        for (mu, nu) in PLANES:
            rho = 6 - mu - nu
            tot = 0
            for p in self.lat.points():
                if p[rho - 1] == 0:
                    pm, pn = addv(p, unit(mu), self.dims), addv(p, unit(nu), self.dims)
                    pmn = addv(pm, unit(nu), self.dims)
                    tot += N[(p, pm, pmn)] + N[(p, pn, pmn)]
            out.append(tot % 2)
        return out

    def solve(self, rhs, rng=None):
        """m on the edges with delta m = rhs modulo 2, or None"""
        rows = []
        for f in self.tris:
            bits = 0
            for e in ((f[1], f[2]), (f[0], f[2]), (f[0], f[1])):
                bits ^= 1 << self.eidx[e]
            rows.append((bits, rhs[f]))
        piv = {}
        for bits, val in rows:
            while bits:
                low = bits & -bits
                if low in piv:
                    pb, pv = piv[low]
                    bits ^= pb
                    val ^= pv
                else:
                    piv[low] = (bits, val)
                    break
            else:
                if val:
                    return None
        sol = 0
        free = [1 << i for i in range(len(self.edges)) if (1 << i) not in piv]
        if rng is not None:
            for fbit in free:
                if rng.randint(0, 1):
                    sol |= fbit
        for low in sorted(piv, reverse=True):
            bits, val = piv[low]
            rest = bits ^ low
            par = bin(rest & sol).count("1") & 1
            if par ^ val:
                sol |= low
        return {e: (sol >> i) & 1 for e, i in self.eidx.items()}

    def descended(self, n):
        return self.restrict(chern(transition(primitive(n, self.dims), self.dims), self.dims))

    def sign(self, hol, rng=None):
        """the sign on the 2-cocycles of the triangulation, modulo 2"""
        base = gu_wen(self.lat, hol)
        def z(N):
            c = self.chern_numbers(N)
            n0 = thooft(self.lat, {pl: c[i] for i, pl in enumerate(PLANES)})
            N0 = self.descended(n0)
            m = self.solve(self.addc(N, N0), rng)
            if m is None:
                return None
            return base(n0) * (-1) ** self.anomaly(m, N0)
        return z


ORDER_PLUS, ORDER_MINUS = (0, 2, 1, 3), (3, 1, 2, 0)


def grassmann(K, N, op=ORDER_PLUS, om=ORDER_MINUS):
    """the Grassmann integral on the triangulation, for a cocycle N modulo 2"""
    tidx = {f: i for i, f in enumerate(K.tris)}
    seq = []
    for t in sorted(K.tets):
        c = K.tets[t]
        for i in (op if c == 1 else om):
            f = t[:i] + t[i + 1:]
            if N[f]:
                seq.append(2 * tidx[f] + (0 if c * (-1) ** i == 1 else 1))
    return gr_sign(seq)


def spin_chain(K):
    """the triangles (p, p + e_mu, p + e_1 + e_2 + e_3)"""
    return [(p, addv(p, unit(mu), K.dims), addv(p, (1, 1, 1), K.dims)) for p in K.lat.points() for mu in (1, 2, 3)]


def local_sign(K, hol=(1, 1, 1)):
    E = spin_chain(K)

    def z(N):
        c = K.chern_numbers(N)
        return (grassmann(K, N) * (-1) ** (sum(N[f] for f in E) % 2)
                * hol[0] ** c[2] * hol[1] ** c[1] * hol[2] ** c[0])
    return z


def check_orders(dims, rng):
    K = Kuhn(dims)
    S = [K.addc(K.descended(closed_sample(K.lat, rng)), K.delta({e: rng.randint(0, 1) for e in K.edges}))
         for _ in range(7)]
    pairs = [(i, j) for i in range(7) for j in range(i + 1, 7)][:16]
    good = []
    for op in itertools.permutations(range(4)):
        for om in itertools.permutations(range(4)):
            g = [grassmann(K, x, op, om) for x in S]
            if all(grassmann(K, K.addc(S[i], S[j]), op, om) * g[i] * g[j] == (-1) ** K.cup1(S[i], S[j])
                   for (i, j) in pairs):
                good.append((op, om))
    assert (ORDER_PLUS, ORDER_MINUS) in good
    return len(good)


def check_local(dims, rng, full=True):
    K = Kuhn(dims)
    lat = K.lat
    N = K.addc(K.descended(closed_sample(lat, rng)), K.delta({e: rng.randint(0, 1) for e in K.edges}))
    zero = {e: 0 for e in K.edges}
    # 7: the defect is the sum of m over all edges
    for e in (K.edges if full else K.edges[::9]):
        m = dict(zero)
        m[e] = 1
        assert grassmann(K, K.addc(N, K.delta(m))) == -grassmann(K, N) * (-1) ** K.anomaly(m, N)
    for _ in range(3):
        m = {e: rng.randint(0, 1) for e in K.edges}
        assert (grassmann(K, K.addc(N, K.delta(m)))
                == grassmann(K, N) * (-1) ** ((K.anomaly(m, N) + sum(m.values())) % 2))
    deg = {}
    for e in K.edges:
        for v in e:
            deg[v] = deg.get(v, 0) + 1
    assert set(deg.values()) == {14}
    # 8: the boundary of E is the sum of all edges
    bd = {e: 0 for e in K.edges}
    for f in spin_chain(K):
        for e in ((f[0], f[1]), (f[0], f[2]), (f[1], f[2])):
            bd[e] ^= 1
    assert set(bd.values()) == {1}
    # 9: the eight spin structures
    for hol in itertools.product((1, -1), repeat=3):
        z, zl = K.sign(hol), local_sign(K, hol)
        for _ in range(2 if full else 1):
            M = K.addc(K.descended(closed_sample(lat, rng)), K.delta({e: rng.randint(0, 1) for e in K.edges}))
            assert z(M) == zl(M)
    tubes = [K.descended(thooft(lat, {pl: 1})) for pl in PLANES]
    assert [local_sign(K)(T) for T in tubes] == [-1, -1, -1]
    return True


def check_triangulation(dims):
    K = Kuhn(dims)
    want = {}
    for x in K.lat.points():
        for (a, b, c) in itertools.permutations((1, 2, 3)):
            def sub(y, *mus):
                return tuple((y[i] - sum(1 for mu in mus if mu == i + 1)) % dims[i] for i in range(3))
            want[(sub(x, a, b, c), sub(x, b, c), sub(x, c), x)] = perm_sign((a, b, c))
    assert K.tets == want
    bd, cnt = {}, {}
    for t, c in K.tets.items():
        for i in range(4):
            f = t[:i] + t[i + 1:]
            bd[f] = bd.get(f, 0) + (-1) ** i * c
            cnt[f] = cnt.get(f, 0) + 1
    vol = dims[0] * dims[1] * dims[2]
    assert all(v == 0 for v in bd.values()) and set(cnt.values()) == {2}
    assert (len(K.tets), len(K.tris), len(K.edges)) == (6 * vol, 12 * vol, 7 * vol)
    return True


def check_sign(dims, rng, count=4):
    K = Kuhn(dims)
    lat = K.lat
    for hol in itertools.product((1, -1), repeat=3):
        z, z2, g = K.sign(hol), K.sign(hol, rng), gu_wen(lat, hol)
        for _ in range(count if hol in ((1, 1, 1), (-1, 1, -1)) else 1):
            n, n2 = closed_sample(lat, rng), closed_sample(lat, rng)
            N, N2 = K.descended(n), K.descended(n2)
            assert z(N) == g(n) and z2(N) == g(n)
            m = {e: rng.randint(0, 1) for e in K.edges}
            Ng = K.addc(N, K.delta(m))
            assert z(Ng) == z(N) * (-1) ** K.anomaly(m, N) and z2(Ng) == z(Ng)
            N2g = K.addc(N2, K.delta({e: rng.randint(0, 1) for e in K.edges}))
            assert z(K.addc(Ng, N2g)) == z(Ng) * z(N2g) * (-1) ** K.cup1(Ng, N2g)
            assert K.cup1(N, N2) == integrate(lat, cr.higher_cup(1, n, n2)) % 2
    bad = dict(K.descended(closed_sample(lat, rng)))
    bad[K.tris[0]] ^= 1
    assert K.sign((1, 1, 1))(bad) is None
    return True


def odd_mm(dims):
    """the alternating integer function of Tests/Villain.wlt with an odd anomaly: the test function of
    star_reference.py plus the large gauge transformation by one link (each of them has an even anomaly)"""
    lat = Torus(dims)
    t = test_mm(dims)
    lg = large_gauge(lat.table(1, {((0, 0, 0), (1,)): 1}), dims)[1]
    return lambda p, q: t(p, q) + lg(p, q)


def test_numbers():
    dims = (3, 3, 3)
    K = Kuhn(dims)
    lat = K.lat
    a, n = test_fields(lat)
    m2 = lat.formula(1, lambda x, S: (S[0] * x[0] + x[1] * x[2] + 2 * S[0] * x[2] + x[0] + S[0]) % 2)
    n3 = add(lat, 2, n, cr.delta(m2))
    n2 = thooft(lat, {(1, 2): 2, (1, 3): 0, (2, 3): -1})
    nn = chern(transition(primitive(n, dims), dims), dims)
    N, N3, N2 = K.descended(n), K.descended(n3), K.descended(n2)
    out = {}
    for signs in ((1, 1, 1), (-1, 1, -1)):
        hol = (-signs[2], -signs[1], -signs[0])
        z = K.sign(hol)
        out[signs] = (z(N), z(N3), z(N2), z(K.addc(N, N2)))
        assert out[signs][:2] == (gu_wen(lat, hol)(n), gu_wen(lat, hol)(n3))
    for name, mm in (("test mm", test_mm(dims)), ("odd mm", odd_mm(dims))):
        an = cech_anomaly(mm, nn, dims)
        moved = {f: (N[f] + mm(f[1], f[2]) - mm(f[0], f[2]) + mm(f[0], f[1])) % 2 for f in K.tris}
        z = K.sign((-1, -1, -1))
        assert z(moved) == z(N) * (-1) ** (an % 2)
        out[name] = an
    out["cup1"] = (K.cup1(N, N2), integrate(lat, cr.higher_cup(1, n, n2)))
    E = spin_chain(K)
    odd = odd_mm(dims)
    moved = {f: (N[f] + odd(f[1], f[2]) - odd(f[0], f[2]) + odd(f[0], f[1])) % 2 for f in K.tris}
    out["grassmann"] = (grassmann(K, N), grassmann(K, N3), grassmann(K, N2), grassmann(K, moved))
    out["chain"] = tuple(sum(X[f] for f in E) % 2 for X in (N, N3, N2))
    out["edges"] = sum(odd(*e) for e in K.edges) % 2
    for signs in ((1, 1, 1), (-1, 1, -1)):
        zl = local_sign(K, (-signs[2], -signs[1], -signs[0]))
        assert (zl(N), zl(N3), zl(N2), zl(K.addc(N, N2))) == out[signs]
    return out


def main():
    rng = random.Random(20261127)
    for dims in ((3, 3, 3), (3, 4, 5)):
        assert check_triangulation(dims)
    print("the sites of the chain: the triangulation with six tetrahedra in a dual cube, a closed 3-manifold  True")
    for dims in ((3, 3, 3), (3, 3, 4)):
        assert check_sign(dims, rng)
    print("the sign on the cocycles of the triangulation: well defined, extends z, (i), (ii) with cup_1 of Steenrod  True")
    for dims in ((3, 3, 3),):
        print("  %s  pairs of orders of the faces with (ii): %d of 576" % (dims, check_orders(dims, rng)))
    for dims, full in (((3, 3, 3), True), ((3, 3, 4), False), ((4, 4, 4), False), ((3, 4, 5), False)):
        assert check_local(dims, rng, full)
    print("the Grassmann integral on the triangulation: w = all edges, the chain E, the 8 spin structures  True")
    out = test_numbers()
    print("  the numbers of the Wolfram Language tests:", out)
    assert out["odd mm"] % 2 == 1
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
