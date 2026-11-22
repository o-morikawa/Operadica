#!/usr/bin/env python3
"""
Reference checks (pure Python, exact integer arithmetic) for the iterated bar
construction of a finite abelian group and the Eilenberg-MacLane spaces.

The bar construction.  A is a finite abelian group, Z[A] its group ring.
B^n(Z[A]) is the n-fold (normalized, reduced) bar construction; its homology is
the homology of the Eilenberg-MacLane space K(A, n) = B^n A.

  generators   level 0: the non-zero elements of A, in degree 0
               level n: the words [x_1 | .. | x_m], m >= 1, in generators of
               level n - 1;  deg [x_1|..|x_m] = sum (deg x_i + 1)
  product      level 0: addition in A (the zero element is dropped);
               level n: the shuffle product, with the Koszul sign for letters
               of degree deg x + 1
  differential d[x_1|..|x_m] = - sum_i (-1)^(e_(i-1)) [.. | d x_i | ..]
                               + sum_i (-1)^(e_i) [.. | x_i x_(i+1) | ..],
               e_i = sum_(j <= i) (deg x_j + 1);  at level 1 also the end
               terms [x_2|..|x_m] + (-1)^m [x_1|..|x_(m-1)]

The space.  A k-simplex of K(A, n) is an n-cocycle on the k-simplex with
values in A: a flat n-form gauge field on the simplex.  Faces restrict it,
degeneracies pull it back.

Cochains and categories.  The data (w, c) of a pointed category on A
(reference/encategory_reference.py) are an (n + 2)-cochain on B^n:

      phi[a|b|c] = w(a, b, c),        phi[a || b] = c(a, b).

Checked here:
  d d = 0;  the product is associative, graded commutative and satisfies the
      Leibniz rule (levels 1, 2; d d = 0 also at level 3)
  homology:  K(Z_N, 1): Z_N, 0, Z_N;   K(Z_N, 2): Z_N, 0, Z_(N gcd(2,N));
             K(Z_N, 3): Z_N, 0, Z_gcd(2,N);  Z_2 x Z_2 as well
  K(A, n) has the single homotopy group pi_n = A (Moore complex), and its
      homology (normalized chains) agrees with the bar construction
  phi(d[a|b|c|d]) = -pentagon,  phi(d[a|b||c]) = hexagon 2,
      phi(d[a||b|c]) = hexagon 1,  phi(d[a|||b]) = c(a,b) + c(b,a):
      (w, c) is a cocycle on B^1, B^2, B^3 exactly if it is a monoidal,
      braided, symmetric structure
  [a||a] and [a||b] + [b||a] are cycles of B^2: the spin and the mutual
      braiding are the values of the cocycle on them
  the number of structures:  |H_(n+2)(B^n)| = N, N gcd(2, N), gcd(2, N), and
      gcd(2, N) again for n = 4: B^4 has no new generators in degree 7
  the suspension x -> [x] from B^n to B^(n+1) satisfies d[x] = -[dx]; it restricts
      a structure on B^(n+1) to the structure on B^n that it contains

Run:  python3 reference/bar_reference.py
"""
import itertools
import os
import random
import sys
from fractions import Fraction as Fr
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from encategory_reference import (Group, Cat, mod1, pentagon, hexagons, symmetric,  # noqa: E402
                                  zn_anyons, vec_zn, double_zn, spin, mutual)


def add(d, k, v):
    if v == 0:
        return
    nv = d.get(k, 0) + v
    if nv == 0:
        d.pop(k, None)
    else:
        d[k] = nv


# ---- the iterated bar construction ------------------------------------------------

class Bar:
    def __init__(self, orders):
        self.orders = tuple(orders)
        self.zero = tuple(0 for _ in orders)
        self.els = [g for g in itertools.product(*[range(n) for n in orders]) if g != self.zero]
        self._gens = {}

    def gadd(self, a, b):
        return tuple((x + y) % n for x, y, n in zip(a, b, self.orders))

    def deg(self, x, level):
        if level == 0:
            return 0
        return sum(self.deg(y, level - 1) + 1 for y in x)

    def gens(self, level, k):
        key = (level, k)
        if key in self._gens:
            return self._gens[key]
        if level == 0:
            out = list(self.els) if k == 0 else []
        else:
            out = []
            for j in range(0, k):
                for first in self.gens(level - 1, j):
                    rest_deg = k - j - 1
                    if rest_deg == 0:
                        out.append((first,))
                    else:
                        for rest in self.gens(level, rest_deg):
                            out.append((first,) + rest)
        self._gens[key] = out
        return out

    def prod(self, x, y, level):
        if level == 0:
            s = self.gadd(x, y)
            return {} if s == self.zero else {s: 1}
        out = {}
        p, q = len(x), len(y)
        dx = [self.deg(a, level - 1) + 1 for a in x]
        dy = [self.deg(b, level - 1) + 1 for b in y]
        for pos in itertools.combinations(range(p + q), p):
            word = []
            sign = 0
            xi = yi = 0
            placed = 0                    # total degree of the letters of y placed so far
            for t in range(p + q):
                if t in pos:
                    sign += dx[xi] * placed
                    word.append(x[xi])
                    xi += 1
                else:
                    word.append(y[yi])
                    placed += dy[yi]
                    yi += 1
            add(out, tuple(word), (-1) ** sign)
        return out

    def d(self, x, level):
        out = {}
        m = len(x)
        eta = 0
        for i in range(m):
            if level >= 2:
                for t, c in self.d(x[i], level - 1).items():
                    add(out, x[:i] + (t,) + x[i + 1:], -((-1) ** eta) * c)
            eta += self.deg(x[i], level - 1) + 1
            if i < m - 1:
                for t, c in self.prod(x[i], x[i + 1], level - 1).items():
                    add(out, x[:i] + (t,) + x[i + 2:], ((-1) ** eta) * c)
        if level == 1 and m >= 2:
            add(out, x[1:], 1)
            add(out, x[:-1], (-1) ** m)
        return out

    def lin_d(self, U, level):
        out = {}
        for x, c in U.items():
            for t, ct in self.d(x, level).items():
                add(out, t, c * ct)
        return out

    def lin_prod(self, U, V, level):
        out = {}
        for x, cx in U.items():
            for y, cy in V.items():
                for t, c in self.prod(x, y, level).items():
                    add(out, t, cx * cy * c)
        return out


def smith_invariants(rows, ncols):
    """the non-zero diagonal entries of the Smith normal form of an integer matrix"""
    M = [list(r) for r in rows]
    nr = len(M)
    inv = []
    piv = 0
    while piv < min(nr, ncols):
        best = None
        for i in range(piv, nr):
            for j in range(piv, ncols):
                if M[i][j] != 0 and (best is None or abs(M[i][j]) < abs(M[best[0]][best[1]])):
                    best = (i, j)
        if best is None:
            break
        i, j = best
        M[piv], M[i] = M[i], M[piv]
        for row in M:
            row[piv], row[j] = row[j], row[piv]
        while True:
            p = M[piv][piv]
            again = False
            for i in range(piv + 1, nr):
                if M[i][piv] != 0:
                    f = M[i][piv] // p
                    M[i] = [a - f * b for a, b in zip(M[i], M[piv])]
                    if M[i][piv] != 0:
                        M[piv], M[i] = M[i], M[piv]
                        again = True
                        break
            if again:
                continue
            for j in range(piv + 1, ncols):
                if M[piv][j] != 0:
                    f = M[piv][j] // p
                    for row in M:
                        row[j] -= f * row[piv]
                    if M[piv][j] != 0:
                        for row in M:
                            row[piv], row[j] = row[j], row[piv]
                        again = True
                        break
            if again:
                continue
            bad = None
            for i in range(piv + 1, nr):
                for j in range(piv + 1, ncols):
                    if M[i][j] % p != 0:
                        bad = i
                        break
                if bad is not None:
                    break
            if bad is not None:
                M[piv] = [a + b for a, b in zip(M[piv], M[bad])]
                continue
            break
        inv.append(abs(M[piv][piv]))
        piv += 1
    return inv


def homology_from(sizes, boundary_rows):
    """sizes = (|C_(k-1)|, |C_k|, |C_(k+1)|); boundary_rows(j) the matrix of d: C_j -> C_(j-1)
    (rows indexed by C_j).  Returns the list of the cyclic summands: 0 for Z, t for Z_t."""
    lo, mid, hi = sizes
    inv_out = smith_invariants(boundary_rows(+1), mid) if hi and mid else []
    inv_in = smith_invariants(boundary_rows(0), lo) if mid and lo else []
    free = mid - len(inv_in) - len(inv_out)
    return [0] * free + sorted(x for x in inv_out if x > 1)


def bar_homology(B, level, k):
    C = {j: B.gens(level, j) if j >= 0 else [] for j in (k - 1, k, k + 1)}

    def rows(shift):
        src, tgt = C[k + shift], C[k + shift - 1]
        idx = {g: i for i, g in enumerate(tgt)}
        out = []
        for g in src:
            row = [0] * len(tgt)
            for t, c in B.d(g, level).items():
                row[idx[t]] += c
            out.append(row)
        return out
    return homology_from((len(C[k - 1]), len(C[k]), len(C[k + 1])), rows)


# ---- the simplicial Eilenberg-MacLane space ---------------------------------------

class EM:
    def __init__(self, orders, n):
        self.orders = tuple(orders)
        self.n = n
        self.zero = tuple(0 for _ in orders)
        self.els = list(itertools.product(*[range(m) for m in orders]))
        self._simp = {}

    def gadd(self, a, b):
        return tuple((x + y) % m for x, y, m in zip(a, b, self.orders))

    def gmul(self, c, a):
        return tuple((c * x) % m for x, m in zip(a, self.orders))

    def faces(self, k):
        return list(itertools.combinations(range(k + 1), self.n + 1))

    def simplices(self, k):
        """the n-cocycles on the k-simplex: tuples of values on its n-faces"""
        if k in self._simp:
            return self._simp[k]
        n = self.n
        fs = self.faces(k)
        free = [f for f in fs if f[0] == 0]            # the n-faces through the vertex 0
        out = []
        for vals in itertools.product(self.els, repeat=len(free)):
            x = dict(zip(free, vals))
            for f in fs:
                if f[0] != 0:
                    big = (0,) + f
                    tot = self.zero
                    for j in range(1, n + 2):
                        tot = self.gadd(tot, self.gmul((-1) ** j, x[big[:j] + big[j + 1:]]))
                    x[f] = self.gmul(-1, tot)
            out.append(tuple(x[f] for f in fs))
        self._simp[k] = out
        return out

    def is_cocycle(self, x, k):
        val = dict(zip(self.faces(k), x))
        for big in itertools.combinations(range(k + 1), self.n + 2):
            tot = self.zero
            for j in range(self.n + 2):
                tot = self.gadd(tot, self.gmul((-1) ** j, val[big[:j] + big[j + 1:]]))
            if tot != self.zero:
                return False
        return True

    def face(self, x, k, i):
        val = dict(zip(self.faces(k), x))
        return tuple(val[tuple(v if v < i else v + 1 for v in f)] for f in self.faces(k - 1))

    def degeneracy(self, y, k, i):
        val = dict(zip(self.faces(k), y))
        out = []
        for f in self.faces(k + 1):
            g = tuple(v if v <= i else v - 1 for v in f)
            out.append(self.zero if len(set(g)) < len(g) else val[g])
        return tuple(out)

    def degenerate(self, x, k):
        return any(self.degeneracy(self.face(x, k, i), k - 1, i) == x for i in range(k))

    def trivial(self, x):
        return all(v == self.zero for v in x)

    def homotopy_orders(self, kmax):
        """the orders of pi_0, .., pi_kmax, from the Moore complex"""
        moore = {}
        for k in range(0, kmax + 2):
            moore[k] = [x for x in self.simplices(k)
                        if all(self.trivial(self.face(x, k, i)) for i in range(1, k + 1))]
        out = []
        for k in range(0, kmax + 1):
            cycles = [x for x in moore[k] if k == 0 or self.trivial(self.face(x, k, 0))]
            bounds = {self.face(x, k + 1, 0) for x in moore[k + 1]}
            out.append(len(cycles) // len(bounds))
        return out

    def homology(self, k):
        nd = {j: ([x for x in self.simplices(j) if not self.degenerate(x, j)] if j >= 0 else [])
              for j in (k - 1, k, k + 1)}

        def rows(shift):
            j = k + shift
            idx = {x: t for t, x in enumerate(nd[j - 1])}
            out = []
            for x in nd[j]:
                row = [0] * len(nd[j - 1])
                for i in range(j + 1):
                    f = self.face(x, j, i)
                    if f in idx:
                        row[idx[f]] += (-1) ** i
                out.append(row)
            return out
        return homology_from((len(nd[k - 1]), len(nd[k]), len(nd[k + 1])), rows)


# ---- cochains from the data of a pointed category -----------------------------------

def cochain(cat, level):
    """the (level + 2)-cochain: w on [a|b|c], c on [a||b] (inside single-entry words)"""
    def phi(g):
        lv = level
        while lv > 2 and len(g) == 1:
            g, lv = g[0], lv - 1
        if lv == 1 and len(g) == 3:
            return cat.w(*g)
        if lv == 2 and len(g) == 1 and len(g[0]) == 3:
            return cat.w(*g[0])
        if lv == 2 and len(g) == 2 and len(g[0]) == 1 and len(g[1]) == 1:
            return cat.c(g[0][0], g[1][0])
        raise ValueError(g)
    return phi


def coboundary(B, cat, level):
    phi = cochain(cat, level)
    return {g: mod1(Fr(sum(c * phi(t) for t, c in B.d(g, level).items())))
            for g in B.gens(level, level + 3)}


def cocycle(B, cat, level):
    if level >= 2 and cat.c is None:
        return False
    return all(v == 0 for v in coboundary(B, cat, level).values())


def pent(cat, a, b, c, d):
    G, w = cat.G, cat.w
    return w(b, c, d) - w(G.add(a, b), c, d) + w(a, G.add(b, c), d) - w(a, b, G.add(c, d)) + w(a, b, c)


def hex1(cat, a, b, d):
    G, w, c = cat.G, cat.w, cat.c
    return (w(b, d, a) + c(a, G.add(b, d)) + w(a, b, d)) - (c(a, d) + w(b, a, d) + c(a, b))


def hex2(cat, a, b, d):
    G, w, c = cat.G, cat.w, cat.c
    return (-w(d, a, b) + c(G.add(a, b), d) - w(a, b, d)) - (c(a, d) - w(a, d, b) + c(b, d))


def random_cat(G, rng, den):
    els = [g for g in G.elements if g != G.zero]
    wt = {k: Fr(rng.randrange(den), den) for k in itertools.product(els, repeat=3)}
    ct = {k: Fr(rng.randrange(den), den) for k in itertools.product(els, repeat=2)}
    return Cat(G, lambda a, b, c: wt.get((a, b, c), Fr(0)), lambda a, b: ct.get((a, b), Fr(0)))


def main():
    rng = random.Random(20261122)

    # ---- the complexes
    for orders, tops in (((2,), (6, 7, 8)), ((3,), (6, 7, 8)), ((2, 2), (4, 6, 7))):
        B = Bar(orders)
        for level, top in zip((1, 2, 3), tops):
            cnt = 0
            for k in range(level, top + 1):
                for g in B.gens(level, k):
                    assert all(B.deg(t, level) == k - 1 for t in B.d(g, level))
                    assert B.lin_d(B.d(g, level), level) == {}, (orders, level, g)
                    cnt += 1
        print(orders, "d d = 0 at levels 1, 2, 3;  generators of B^2 by degree:",
              [len(B.gens(2, k)) for k in range(2, 7)])
    for orders in ((2,), (3,), (4,)):
        B = Bar(orders)
        for k in range(4, 8):
            for g in B.gens(4, k):
                assert B.lin_d(B.d(g, 4), 4) == {}
        # the suspension x -> [x] raises the level and the degree by one, and d[x] = -[dx]
        for level in (1, 2, 3):
            for k in range(level, level + 4):
                for g in B.gens(level, k):
                    assert (g,) in B.gens(level + 1, k + 1)
                    assert B.d((g,), level + 1) == {(t,): -c for t, c in B.d(g, level).items()}
    print("d d = 0 at level 4;  the suspension x -> [x] satisfies d[x] = -[dx]  True")
    B = Bar((2,))
    assert [len(B.gens(2, k)) for k in range(2, 8)] == [1, 1, 2, 3, 5, 8]
    assert [len(Bar((3,)).gens(3, k)) for k in range(3, 9)] == [2, 4, 12, 36, 104, 304]
    for orders in ((2,), (3,), (2, 2)):
        B = Bar(orders)
        for level in (1, 2):
            top = 5 if len(orders) == 1 else 4
            gens = [g for k in range(level, top) for g in B.gens(level, k)]
            cnt = 0
            for x in gens:
                for y in gens:
                    dx, dy = B.deg(x, level), B.deg(y, level)
                    if dx + dy > top + 1:
                        continue
                    xy = B.prod(x, y, level)
                    assert xy == {t: (-1) ** (dx * dy) * c for t, c in B.prod(y, x, level).items()}
                    rhs = B.lin_prod(B.d(x, level), {y: 1}, level)
                    for t, c in B.lin_prod({x: 1}, B.d(y, level), level).items():
                        add(rhs, t, (-1) ** dx * c)
                    assert B.lin_d(xy, level) == rhs, ("Leibniz", orders, level, x, y)
                    cnt += 1
            small = [g for g in gens if B.deg(g, level) <= level + 1][:6]
            for x, y, z in itertools.product(small, repeat=3):
                assert B.lin_prod(B.prod(x, y, level), {z: 1}, level) == \
                    B.lin_prod({x: 1}, B.prod(y, z, level), level)
    print("the shuffle product is associative, graded commutative, and d is a derivation  True")
    B = Bar((3,))
    a, b = (1,), (2,)
    assert B.d((a, b), 1) == {(b,): 1, (a,): 1}                       # a + b = 0 is dropped
    assert B.d((a, a), 1) == {(a,): 2, (b,): -1}
    assert B.prod((a,), (b,), 1) == {(a, b): 1, (b, a): -1}
    assert B.d(((a,), (b,)), 2) == {((a, b),): 1, ((b, a),): -1}
    assert B.prod((a, b), (a,), 1) == {(a, b, a): 1}                  # a a b cancels
    assert B.d(((a, b), (a,)), 2) == {((a,), (a,)): -1, ((b,), (a,)): -1, ((a, b, a),): -1}

    # ---- homology
    for N in (2, 3, 4, 5, 6):
        B = Bar((N,))
        g2 = gcd(2, N)
        assert [bar_homology(B, 1, k) for k in (1, 2, 3)] == [[N], [], [N]]
        assert [bar_homology(B, 2, k) for k in (2, 3, 4)] == [[N], [], [N * g2]]
        assert [bar_homology(B, 3, k) for k in (3, 4, 5)] == [[N], [], [g2] if g2 > 1 else []]
    for N in (2, 3, 4):
        g2 = gcd(2, N)
        assert [bar_homology(Bar((N,)), 4, k) for k in (4, 5, 6)] == [[N], [], [g2] if g2 > 1 else []]
    B = Bar((2, 2))
    assert bar_homology(B, 1, 3) == [2, 2, 2] and bar_homology(B, 2, 4) == [2, 4, 4]
    assert bar_homology(B, 3, 5) == [2, 2] and bar_homology(B, 2, 3) == []
    assert bar_homology(Bar((2,)), 2, 5) == [2] and bar_homology(Bar((4,)), 2, 5) == [2]
    print("H(K(Z_N,1)) = Z_N, 0, Z_N;  H(K(Z_N,2)) = Z_N, 0, Z_(N gcd(2,N));  H(K(Z_N,3)) = Z_N, 0, Z_gcd(2,N), and the same for K(Z_N,4)  True")

    # ---- the simplicial model
    for orders, n, kmax in (((2,), 1, 3), ((3,), 1, 3), ((2,), 2, 4), ((3,), 2, 3), ((2,), 3, 4),
                            ((2, 2), 1, 2), ((2, 2), 2, 3)):
        K = EM(orders, n)
        order = 1
        for m in orders:
            order *= m
        assert all(K.is_cocycle(x, k) for k in range(0, kmax + 2) for x in K.simplices(k)[:200])
        for k in range(1, kmax + 2):
            for x in K.simplices(k)[:40]:
                for i in range(k + 1):
                    assert K.face(K.degeneracy(x, k, i), k + 1, i) == x
                    assert K.face(K.degeneracy(x, k, i), k + 1, i + 1) == x
                    for j in range(i + 1, k + 1):
                        if k >= 2:
                            assert K.face(K.face(x, k, j), k - 1, i) == K.face(K.face(x, k, i), k - 1, j - 1)
        assert K.homotopy_orders(kmax) == [order if k == n else 1 for k in range(kmax + 1)]
    assert [len(EM((2,), 2).simplices(k)) for k in range(6)] == [1, 1, 2, 8, 64, 1024]
    print("K(A, n) has the single homotopy group pi_n = A  True")
    for orders, n, ks in (((2,), 1, (1, 2, 3)), ((3,), 1, (1, 2, 3)), ((4,), 1, (1, 2)),
                          ((2,), 2, (2, 3, 4)), ((3,), 2, (2, 3)), ((2,), 3, (3, 4))):
        K = EM(orders, n)
        B = Bar(orders)
        for k in ks:
            assert K.homology(k) == bar_homology(B, n, k), (orders, n, k)
    print("the homology of the simplicial K(A, n) is the homology of the bar construction  True")

    # ---- cochains: pentagon, hexagons, symmetry
    for orders in ((3,), (4,), (2, 2)):
        G = Group(orders)
        B = Bar(orders)
        cat = random_cat(G, rng, 12)
        for g, val in coboundary(B, cat, 1).items():
            assert val == mod1(pent(cat, *g))
        for g, val in coboundary(B, cat, 2).items():
            if len(g) == 1:
                assert val == mod1(-pent(cat, *g[0]))
            elif len(g[0]) == 2:
                assert val == mod1(hex2(cat, g[0][0], g[0][1], g[1][0]))
            else:
                assert val == mod1(hex1(cat, g[0][0], g[1][0], g[1][1]))
        for g, val in coboundary(B, cat, 3).items():
            if len(g) == 2:                                   # [a ||| b]
                a, b = g[0][0][0], g[1][0][0]
                assert val == mod1(-cat.c(a, b) - cat.c(b, a))
            else:                                             # a suspended generator of B^2
                h = g[0]
                if len(h) == 1:
                    assert val == mod1(pent(cat, *h[0]))
                elif len(h[0]) == 2:
                    assert val == mod1(-hex2(cat, h[0][0], h[0][1], h[1][0]))
                else:
                    assert val == mod1(-hex1(cat, h[0][0], h[1][0], h[1][1]))
        # B^4 has no new generators in degree 7: the conditions are those of B^3
        assert all(len(g) == 1 for g in B.gens(4, 7))
        for g, val in coboundary(B, cat, 4).items():
            assert val == mod1(-coboundary(B, cat, 3)[g[0]])
    print("phi(d[a|b|c|d]) = pentagon;  on B^2: -pentagon, hexagon 2 on [a|b||c], hexagon 1 on [a||b|c];"
          "  on B^3: the same with the opposite signs, and -(c(a,b) + c(b,a)) on [a|||b]  True")

    cats = []
    for n in (2, 3, 4):
        for p in range(0, 2 * n):
            cats.append(zn_anyons(n, p))
    cats += [double_zn(2), double_zn(3), vec_zn(3, 1), vec_zn(2, 1)]
    for n in (2, 3):
        for _ in range(40):
            cats.append(random_cat(Group((n,)), rng, 2 * n))
    valid = [0, 0, 0]
    for cat in cats:
        B = Bar(cat.G.orders)
        braided = cat.c is not None
        e1 = pentagon(cat)
        e2 = e1 and braided and hexagons(cat)
        e3 = e2 and symmetric(cat)
        assert (cocycle(B, cat, 1), cocycle(B, cat, 2), cocycle(B, cat, 3)) == (e1, e2, e3)
        valid = [valid[0] + e1, valid[1] + e2, valid[2] + e3]
    print("cocycle on B^1, B^2, B^3  <=>  monoidal, braided, symmetric: %d categories (%d, %d, %d valid)  True"
          % (len(cats), valid[0], valid[1], valid[2]))

    # ---- spins and mutual braidings are values on cycles
    for cat in (zn_anyons(4, 1), zn_anyons(3, 2), double_zn(2)):
        B = Bar(cat.G.orders)
        phi = cochain(cat, 2)
        for a in B.els:
            assert B.d(((a,), (a,)), 2) == {}
            assert mod1(phi(((a,), (a,)))) == spin(cat, a)
            for b in B.els:
                if a != b:
                    cyc = {((a,), (b,)): 1, ((b,), (a,)): 1}
                    assert B.lin_d(cyc, 2) == {}
                    assert mod1(sum(c * phi(g) for g, c in cyc.items())) == mutual(cat, a, b)
                # in B^3 the same combination is a boundary: the mutual braiding of a symmetric structure vanishes
                assert B.d((((a,),), ((b,),)), 3) in ({(((a,), (b,)),): 1, (((b,), (a,)),): 1},
                                                      {(((a,), (b,)),): -1, (((b,), (a,)),): -1},
                                                      {(((a,), (a,)),): 2}, {(((a,), (a,)),): -2})
    # the class of [1||1] generates H_4(K(Z_N, 2)): a cocycle takes on it a value of the full order
    for N in (2, 3, 4, 5, 6):
        B = Bar((N,))
        cat = zn_anyons(N, 1 if N % 2 == 0 else 2)
        assert cocycle(B, cat, 2)
        value = mod1(cochain(cat, 2)((((1,),), ((1,),))))
        assert value.denominator == N * gcd(2, N) == bar_homology(B, 2, 4)[0]
    print("[a||a] and [a||b] + [b||a] are cycles; the cocycle gives the spin and the mutual braiding;\n  the spin of the generator of Z_N has the denominator N gcd(2, N), the order of H_4(K(Z_N, 2))  True")

    # ---- the number of structures on Z_2, by brute force over quarter-integer phases
    G = Group((2,))
    one = (1,)
    sols = []
    for wv, cv in itertools.product(range(4), repeat=2):
        cat = Cat(G, lambda a, b, c, wv=wv: Fr(wv, 4) if (a, b, c) == (one, one, one) else Fr(0),
                  lambda a, b, cv=cv: Fr(cv, 4) if (a, b) == (one, one) else Fr(0))
        sols.append((pentagon(cat), pentagon(cat) and hexagons(cat),
                     pentagon(cat) and hexagons(cat) and symmetric(cat), wv, cv))
    n1 = len({s[3] for s in sols if s[0]})
    n2 = sum(1 for s in sols if s[1])
    n3 = sum(1 for s in sols if s[2])
    B = Bar((2,))
    sizes = [bar_homology(B, n, n + 2) for n in (1, 2, 3)]
    assert (n1, n2, n3) == (2, 4, 2) and sizes == [[2], [4], [2]]
    print("structures on Z_2: monoidal 2, braided 4, symmetric 2 = |H_3(B)|, |H_4(B^2)|, |H_5(B^3)|  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
