#!/usr/bin/env python3
"""
Reference implementation (pure Python, no dependencies) of cubical cochain
operations on the hypercubic lattice Z^d:

    coboundary  delta
    cup product
    higher cup products  cup_i

It exists to pin down the SIGN CONVENTIONS used by the Wolfram Language code in
Kernel/Lattice.wl.  Everything the WL code claims is checked here by exact
integer arithmetic:

  (1) W -> W (x) W diagonal of the standard Z/2-resolution is a chain map.
  (2) The cup-i coproducts Delta_i on the n-cube, built from the interval by
      the tensor-product formula, satisfy
          d Delta_i = (1 + (-1)^i T) Delta_{i-1} + (-1)^i Delta_i d .
  (3) The closed "word" formula for Delta_i (the one ported to WL) agrees
      with the recursive construction.
  (4) On a periodic lattice with random integer cochains:
          delta^2 = 0, Leibniz rule, associativity of cup,
          and the cup_i relation in the convention of
          Jacobson-Sulejmanpasic, arXiv:2303.06160, eq. (A3):
            a u_i b - (-1)^{pq+i} b u_i a
              = (-1)^{p+q+1+i} [ d(a u_{i+1} b) - da u_{i+1} b - (-1)^p a u_{i+1} db ]
  (5) The explicit low-dimensional component formulas printed in Appendix A
      of arXiv:2303.06160 (which follow Chen-Tata, arXiv:2106.05274).

Run:  python3 reference/cubical_reference.py
"""
import itertools
import random
import sys

# --------------------------------------------------------------------------
# linear combinations as dicts  basis -> integer coefficient
# --------------------------------------------------------------------------

def add(d, k, v):
    if v == 0:
        return
    nv = d.get(k, 0) + v
    if nv == 0:
        d.pop(k, None)
    else:
        d[k] = nv


def lin_add(d1, d2, c=1):
    out = dict(d1)
    for k, v in d2.items():
        add(out, k, c * v)
    return out


# --------------------------------------------------------------------------
# (1) standard resolution W of Z over Z[Z/2] and its diagonal
#     basis element (a, j) = T^a e_j ;  d e_j = e_{j-1} + (-1)^j T e_{j-1}
# --------------------------------------------------------------------------

def W_boundary(a, j):
    if j == 0:
        return {}
    out = {}
    add(out, (a, j - 1), 1)
    add(out, ((a + 1) % 2, j - 1), (-1) ** j)
    return out


def WW_boundary(x):
    (a, j), (b, k) = x
    out = {}
    for y, c in W_boundary(a, j).items():
        add(out, (y, (b, k)), c)
    for y, c in W_boundary(b, k).items():
        add(out, ((a, j), y), (-1) ** j * c)
    return out


def s_diag(i, j):
    """sign in  psi(e_i) = sum_j s(i,j) e_j (x) T^j e_{i-j}"""
    return (-1) ** (j * (i - j))


def psi(i):
    out = {}
    for j in range(i + 1):
        add(out, ((0, j), (j % 2, i - j)), s_diag(i, j))
    return out


def TT(chain):
    return {(((a + 1) % 2, j), ((b + 1) % 2, k)): c for ((a, j), (b, k)), c in chain.items()}


def check_W_diagonal(imax=8):
    for i in range(1, imax + 1):
        lhs = {}
        for x, c in psi(i).items():
            for y, cc in WW_boundary(x).items():
                add(lhs, y, c * cc)
        rhs = lin_add(psi(i - 1), TT(psi(i - 1)), (-1) ** i)
        assert lhs == rhs, ("W diagonal fails", i)
    return True


# --------------------------------------------------------------------------
# (2) chains on the n-cube: basis = tuple over {'0','1','e'}
# --------------------------------------------------------------------------

def deg(c):
    return sum(1 for s in c if s == 'e')


def cube_boundary(c):
    out = {}
    sign = 1
    for k, s in enumerate(c):
        if s == 'e':
            add(out, c[:k] + ('1',) + c[k + 1:], sign)
            add(out, c[:k] + ('0',) + c[k + 1:], -sign)
            sign = -sign
    return out


def tensor_boundary(chain):
    out = {}
    for (x, y), c in chain.items():
        for xx, cc in cube_boundary(x).items():
            add(out, (xx, y), c * cc)
        for yy, cc in cube_boundary(y).items():
            add(out, (x, yy), (-1) ** deg(x) * c * cc)
    return out


def T(chain):
    out = {}
    for (x, y), c in chain.items():
        add(out, (y, x), (-1) ** (deg(x) * deg(y)) * c)
    return out


def interval_delta(j, s):
    """Delta_j on the interval generator s in {'0','1','e'}"""
    if j == 0:
        if s == 'e':
            return {(('0',), ('e',)): 1, (('e',), ('1',)): 1}
        return {((s,), (s,)): 1}
    if j == 1 and s == 'e':
        return {(('e',), ('e',)): -1}
    return {}


_delta_cache = {}


def cube_delta(i, c):
    """Delta_i(c) for a cell c of the n-cube, by the tensor-product formula."""
    key = (i, c)
    if key in _delta_cache:
        return _delta_cache[key]
    if len(c) == 0:
        res = {((), ()): 1} if i == 0 else {}
        _delta_cache[key] = res
        return res
    c1, rest = c[0], c[1:]
    d1 = 1 if c1 == 'e' else 0
    out = {}
    for j in range(0, min(i, 1) + 1):
        left = interval_delta(j, c1)
        if not left:
            continue
        right = cube_delta(i - j, rest)
        if j % 2 == 1:
            right = T(right)
        pref = s_diag(i, j) * (-1) ** ((i - j) * d1)
        for (u, up), cu in left.items():
            for (y, yp), cy in right.items():
                sh = (-1) ** (deg(up) * deg(y))
                add(out, (u + y, up + yp), pref * cu * cy * sh)
    _delta_cache[key] = out
    return out


def cube_delta_lin(i, chain):
    out = {}
    for c, v in chain.items():
        for k, w in cube_delta(i, c).items():
            add(out, k, v * w)
    return out


def check_cube_structure(nmax=5):
    for n in range(0, nmax + 1):
        for c in itertools.product('01e', repeat=n):
            for i in range(0, n + 2):
                lhs = tensor_boundary(cube_delta(i, c))
                rhs = {}
                if i >= 1:
                    dm = cube_delta(i - 1, c)
                    rhs = lin_add(dm, T(dm), (-1) ** i)
                rhs = lin_add(rhs, cube_delta_lin(i, cube_boundary(c)), (-1) ** i)
                assert lhs == rhs, ("cube structure fails", n, c, i)
    return True


# --------------------------------------------------------------------------
# (3) closed "word" formula for Delta_i on the top cell e^n
#
#   A word w in {'a','b','c'}^n labels each direction as
#       'a' : only the first factor has an edge there
#       'b' : only the second factor has an edge there
#       'c' : both factors have an edge there (shared), exactly i of them
#   With t_k = number of 'c' strictly before position k:
#       'a' at k : second factor sits at vertex 1 if t_k even, 0 if t_k odd
#       'b' at k : first  factor sits at vertex 0 if t_k even, 1 if t_k odd
#   sign = (-1)^E,
#       E = #{k<l : w_k in {b,c}, w_l in {a,c}}        (shuffle sign)
#         + #{k<l : w_k in {a,b}, w_l = c}
#         + i(i+1)/2
# --------------------------------------------------------------------------

def word_sign(w):
    n = len(w)
    i = sum(1 for s in w if s == 'c')
    E = i * (i + 1) // 2
    for k in range(n):
        for l in range(k + 1, n):
            if w[k] in 'bc' and w[l] in 'ac':
                E += 1
            if w[k] in 'ab' and w[l] == 'c':
                E += 1
    return (-1) ** E


def word_term(w):
    """returns (first factor cell, second factor cell) for the word w"""
    x, y = [], []
    t = 0
    for s in w:
        if s == 'a':
            x.append('e')
            y.append('1' if t % 2 == 0 else '0')
        elif s == 'b':
            x.append('0' if t % 2 == 0 else '1')
            y.append('e')
        else:
            x.append('e')
            y.append('e')
            t += 1
    return tuple(x), tuple(y)


def words(n, i):
    for w in itertools.product('abc', repeat=n):
        if sum(1 for s in w if s == 'c') == i:
            yield w


def check_word_formula(nmax=6):
    for n in range(0, nmax + 1):
        top = tuple('e' for _ in range(n))
        for i in range(0, n + 1):
            closed = {}
            for w in words(n, i):
                add(closed, word_term(w), word_sign(w))
            assert closed == cube_delta(i, top), ("word formula fails", n, i)
    return True


# --------------------------------------------------------------------------
# (4) cochains on the periodic lattice (Z/L)^d
#     cell = (x, S) with x a d-tuple and S a sorted tuple of directions 1..d
#     a cochain of degree p is a function f(x, S)
# --------------------------------------------------------------------------

class Lattice:
    def __init__(self, d, L):
        self.d, self.L = d, L

    def shift(self, x, dirs):
        x = list(x)
        for mu in dirs:
            x[mu - 1] = (x[mu - 1] + 1) % self.L
        return tuple(x)

    def cells(self, p):
        for x in itertools.product(range(self.L), repeat=self.d):
            for S in itertools.combinations(range(1, self.d + 1), p):
                yield x, S

    def random_cochain(self, p, rng, bound=5):
        table = {c: rng.randint(-bound, bound) for c in self.cells(p)}
        return Cochain(self, p, lambda x, S: table[(x, S)])


class Cochain:
    def __init__(self, lat, p, f):
        self.lat, self.p, self.f = lat, p, f
        self._memo = {}

    def __call__(self, x, S):
        if len(S) != self.p:
            return 0
        key = (x, S)
        if key not in self._memo:
            self._memo[key] = self.f(x, S)
        return self._memo[key]


def perm_sign(seq):
    seq = list(seq)
    s = 1
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]:
                s = -s
    return s


def delta(a):
    lat = a.lat

    def f(x, S):
        tot = 0
        for k, mu in enumerate(S):
            rest = S[:k] + S[k + 1:]
            tot += (-1) ** k * (a(lat.shift(x, [mu]), rest) - a(x, rest))
        return tot
    return Cochain(lat, a.p + 1, f)


def cup(a, b):
    lat = a.lat
    p, q = a.p, b.p

    def f(x, S):
        tot = 0
        for A in itertools.combinations(S, p):
            B = tuple(m for m in S if m not in A)
            tot += perm_sign(A + B) * a(x, A) * b(lat.shift(x, A), B)
        return tot
    return Cochain(lat, p + q, f)


def higher_cup(i, a, b, convention="physics"):
    """
    cup_i of a p-cochain a and a q-cochain b; result has degree p+q-i.

    convention = "steenrod": (a u_i b)(c) = <a (x) b, Delta_i c>, which obeys
        d(a u_i b) = (-1)^i da u_i b + (-1)^{i+p} a u_i db
                     - (-1)^i a u_{i-1} b - (-1)^{pq} b u_{i-1} a
    convention = "physics":  multiply by (-1)^{i(p+q+1)}; obeys eq. (A3) of
        arXiv:2303.06160.
    """
    lat = a.lat
    p, q = a.p, b.p
    n = p + q - i
    if i < 0 or i > min(p, q):
        return Cochain(lat, n, lambda x, S: 0)
    eta = (-1) ** (i * (p + q + 1)) if convention == "physics" else 1
    wlist = [w for w in words(n, i) if sum(1 for s in w if s == 'a') == p - i]
    data = [(word_sign(w), w) for w in wlist]

    def f(x, S):
        tot = 0
        for sg, w in data:
            t = 0
            SA, SB, sha, shb = [], [], [], []
            for mu, s in zip(S, w):
                if s == 'a':
                    SA.append(mu)
                    if t % 2 == 0:
                        shb.append(mu)
                elif s == 'b':
                    SB.append(mu)
                    if t % 2 == 1:
                        sha.append(mu)
                else:
                    SA.append(mu)
                    SB.append(mu)
                    t += 1
            tot += sg * a(lat.shift(x, sha), tuple(SA)) * b(lat.shift(x, shb), tuple(SB))
        return eta * tot
    return Cochain(lat, n, f)


def equal(lat, u, v, p):
    return all(u(x, S) == v(x, S) for x, S in lat.cells(p))


def comb(lat, p, terms):
    """linear combination: terms = [(coeff, cochain), ...]"""
    return Cochain(lat, p, lambda x, S: sum(c * u(x, S) for c, u in terms))


def check_lattice_identities(d, L, rng):
    lat = Lattice(d, L)
    n_checked = 0
    for p in range(0, d + 1):
        a = lat.random_cochain(p, rng)
        # delta^2 = 0
        if p + 2 <= d:
            dd = delta(delta(a))
            assert all(dd(x, S) == 0 for x, S in lat.cells(p + 2)), ("d^2", d, p)
        for q in range(0, d + 1):
            b = lat.random_cochain(q, rng)
            # Leibniz
            if p + q + 1 <= d:
                lhs = delta(cup(a, b))
                rhs = comb(lat, p + q + 1, [(1, cup(delta(a), b)), ((-1) ** p, cup(a, delta(b)))])
                assert equal(lat, lhs, rhs, p + q + 1), ("Leibniz", d, p, q)
            # cup_0 is the cup product in both conventions
            if p + q <= d:
                for conv in ("physics", "steenrod"):
                    assert equal(lat, cup(a, b), higher_cup(0, a, b, conv), p + q), ("cup0", d, p, q)
            # associativity
            for r in range(0, d + 1 - p - q):
                c = lat.random_cochain(r, rng)
                assert equal(lat, cup(cup(a, b), c), cup(a, cup(b, c)), p + q + r), ("assoc", d, p, q, r)
            # cup_i relation, physics convention (A3)
            for i in range(0, min(p, q) + 1):
                if p + q - i > d:
                    continue
                lhs = comb(lat, p + q - i, [(1, higher_cup(i, a, b)),
                                             (-(-1) ** (p * q + i), higher_cup(i, b, a))])
                s = (-1) ** (p + q + 1 + i)
                rhs = comb(lat, p + q - i, [
                    (s, delta(higher_cup(i + 1, a, b))),
                    (-s, higher_cup(i + 1, delta(a), b)),
                    (-s * (-1) ** p, higher_cup(i + 1, a, delta(b))),
                ])
                assert equal(lat, lhs, rhs, p + q - i), ("A3", d, p, q, i)
                n_checked += 1
            # Steenrod's original convention
            for i in range(1, min(p, q) + 2):
                n = p + q - i + 1
                if n > d or n < 0:
                    continue
                st = lambda j, u, v: higher_cup(j, u, v, "steenrod")
                lhs = delta(st(i, a, b))
                rhs = comb(lat, n, [
                    ((-1) ** i, st(i, delta(a), b)),
                    ((-1) ** (i + p), st(i, a, delta(b))),
                    (-(-1) ** i, st(i - 1, a, b)),
                    (-(-1) ** (p * q), st(i - 1, b, a)),
                ])
                assert equal(lat, lhs, rhs, n), ("Steenrod", d, p, q, i)
    return n_checked


# --------------------------------------------------------------------------
# (5) explicit component formulas from arXiv:2303.06160, Appendix A
# --------------------------------------------------------------------------

def check_literature(rng):
    lat = Lattice(3, 4)
    e = lambda x, *dirs: lat.shift(x, dirs)
    a1, b1 = lat.random_cochain(1, rng), lat.random_cochain(1, rng)
    a2, b2 = lat.random_cochain(2, rng), lat.random_cochain(2, rng)
    a3, b3 = lat.random_cochain(3, rng), lat.random_cochain(3, rng)
    a0 = lat.random_cochain(0, rng)
    hc = higher_cup
    for x in itertools.product(range(lat.L), repeat=3):
        # ordinary cup products
        assert cup(a1, b1)(x, (1, 2)) == a1(x, (1,)) * b1(e(x, 1), (2,)) - a1(x, (2,)) * b1(e(x, 2), (1,))
        assert cup(b2, a0)(x, (1, 2)) == b2(x, (1, 2)) * a0(e(x, 1, 2), ())
        assert cup(a1, b2)(x, (1, 2, 3)) == (a1(x, (1,)) * b2(e(x, 1), (2, 3))
                                               - a1(x, (2,)) * b2(e(x, 2), (1, 3))
                                               + a1(x, (3,)) * b2(e(x, 3), (1, 2)))
        assert cup(b2, a1)(x, (1, 2, 3)) == (b2(x, (2, 3)) * a1(e(x, 2, 3), (1,))
                                               - b2(x, (1, 3)) * a1(e(x, 1, 3), (2,))
                                               + b2(x, (1, 2)) * a1(e(x, 1, 2), (3,)))
        # higher cup products, 1D and 2D
        assert hc(1, a1, b1)(x, (1,)) == a1(x, (1,)) * b1(x, (1,))
        assert hc(1, a1, b2)(x, (1, 2)) == -(a1(x, (2,)) + a1(e(x, 2), (1,))) * b2(x, (1, 2))
        assert hc(1, b2, a1)(x, (1, 2)) == b2(x, (1, 2)) * (a1(x, (1,)) + a1(e(x, 1), (2,)))
        assert hc(2, a2, b2)(x, (1, 2)) == a2(x, (1, 2)) * b2(x, (1, 2))
        # 3D, cup_1
        S = (1, 2, 3)
        assert hc(1, a1, b3)(x, S) == (a1(x, (3,)) + a1(e(x, 3), (2,)) + a1(e(x, 3, 2), (1,))) * b3(x, S)
        assert hc(1, b3, a1)(x, S) == b3(x, S) * (a1(x, (1,)) + a1(e(x, 1), (2,)) + a1(e(x, 1, 2), (3,)))
        assert hc(1, a2, b2)(x, S) == (a2(x, (2, 3)) * (b2(x, (1, 2)) + b2(e(x, 2), (1, 3)))
                                        + a2(e(x, 2), (1, 3)) * b2(x, (1, 2))
                                        - a2(x, (1, 3)) * b2(e(x, 1), (2, 3))
                                        - a2(e(x, 3), (1, 2)) * (b2(x, (1, 3)) + b2(e(x, 1), (2, 3))))
        # 3D, cup_2 and cup_3
        assert hc(2, a2, b3)(x, S) == (a2(x, (1, 2)) + a2(x, (2, 3)) + a2(e(x, 2), (1, 3))) * b3(x, S)
        assert hc(2, b3, a2)(x, S) == b3(x, S) * (a2(x, (1, 3)) + a2(e(x, 1), (2, 3)) + a2(e(x, 3), (1, 2)))
        assert hc(3, a3, b3)(x, S) == a3(x, S) * b3(x, S)
    return True


# --------------------------------------------------------------------------
# (6) cup_1 is not a derivation of the cup product: no Hirsch formula
# --------------------------------------------------------------------------

def check_hirsch_defect(rng):
    """
    For simplicial cochains  (a u b) u_1 c = a u (b u_1 c) +- (a u_1 c) u b  (Hirsch).
    For the cubical cup_1 used here this fails for every choice of signs, on
    either side.  For 1-cochains in two dimensions the defect is

      ((a u b) u_1 c - a u (b u_1 c) - (a u_1 c) u b)(x; 12)
            = - a(x; 2) b(x + e_2; 1) (dc)(x; 12),

    so it vanishes when c is closed.
    """
    signs = list(itertools.product((1, -1), repeat=2))
    lat = Lattice(2, 3)
    a, b, c = (lat.random_cochain(1, rng) for _ in range(3))
    h = lambda u, v: higher_cup(1, u, v)
    lhs = h(cup(a, b), c)
    t1, t2 = cup(a, h(b, c)), cup(h(a, c), b)
    assert not any(equal(lat, lhs, comb(lat, 2, [(e1, t1), (e2, t2)]), 2) for e1, e2 in signs)
    rhs = h(a, cup(b, c))
    s1, s2 = cup(h(a, b), c), cup(b, h(a, c))
    assert not any(equal(lat, rhs, comb(lat, 2, [(e1, s1), (e2, s2)]), 2) for e1, e2 in signs)
    dc = delta(c)
    defect = comb(lat, 2, [(1, lhs), (-1, t1), (-1, t2)])
    for x in itertools.product(range(lat.L), repeat=2):
        assert defect(x, (1, 2)) == -a(x, (2,)) * b(lat.shift(x, [2]), (1,)) * dc(x, (1, 2))
    # with c exact the formula holds, also in three dimensions
    for d, L, degs in ((2, 3, [(1, 1)]), (3, 2, [(1, 1), (1, 2), (2, 1)])):
        lat = Lattice(d, L)
        for p, q in degs:
            a, b = lat.random_cochain(p, rng), lat.random_cochain(q, rng)
            c = delta(lat.random_cochain(0, rng))
            lhs = higher_cup(1, cup(a, b), c)
            rhs = comb(lat, p + q, [(1, cup(a, higher_cup(1, b, c))), (1, cup(higher_cup(1, a, c), b))])
            assert equal(lat, lhs, rhs, p + q), ("Hirsch with c exact", d, p, q)
    return True


def main():
    rng = random.Random(20261122)
    print("(1) W diagonal is a chain map ............", check_W_diagonal())
    print("(2) cup-i coproducts on cubes, n <= 5 ....", check_cube_structure(5))
    print("(3) closed word formula, n <= 6 ..........", check_word_formula(6))
    total = 0
    for d, L in ((1, 3), (2, 3), (3, 3), (4, 2)):
        total += check_lattice_identities(d, L, rng)
    print("(4) lattice identities, d <= 4 ...........", True, f"({total} instances of (A3))")
    print("(5) literature formulas (2303.06160 App.A)", check_literature(rng))
    print("(6) no Hirsch formula; defect ~ dc ........", check_hirsch_defect(rng))
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
