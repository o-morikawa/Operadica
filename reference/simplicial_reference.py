#!/usr/bin/env python3
"""
Reference checks (pure Python, exact arithmetic) for cochains on simplices,
Steenrod's higher cup products, and characteristic classes on the
Eilenberg-MacLane spaces K(Z_N, n).

Cochains on an ordered simplex with the vertices 0 < 1 < ... < n:

  (d c)(v_0 .. v_(p+1)) = sum_k (-1)^k c(v_0 .. omit v_k .. v_(p+1))
  (a cup b)(v_0 .. v_(p+q)) = a(v_0 .. v_p) b(v_p .. v_(p+q))
  (a cup_i b)(0 .. n),  n = p + q - i:  the sum over the cuts
      0 <= j_0 < j_1 < ... < j_i <= n
  of  sign * a(0..j_0, j_1..j_2, ...) * b(j_0..j_1, j_2..j_3, ...).
  The pieces [0, j_0], [j_0, j_1], ..., [j_i, n] go alternately to a and to b,
  and the sign is that of the permutation
      (the vertices of a, then the vertices of b that are not cut points).

With this sign the products satisfy the same identity as the products of the
hypercubic lattice (Jacobson-Sulejmanpasic, arXiv:2303.06160, (A3)):

  a cup_i b - (-1)^(pq+i) b cup_i a
      = (-1)^(p+q+1+i) [ d(a cup_(i+1) b) - da cup_(i+1) b - (-1)^p a cup_(i+1) db ]

so every identity that follows from it holds on both lattices.  The Hirsch
formula, which fails on the hypercubic lattice (it holds up to the homotopy
of reference/einfinity_reference.py), holds exactly on simplices.

A k-simplex of K(Z_N, n) is a flat Z_N-valued n-form field on the k-simplex;
its lift B to integers in 0 .. N-1 is an integer cochain.  Then

  (k / N^2) (A cup dA)(0123)        on K(Z_N, 1)   (Dijkgraaf-Witten)
  (p / 2N) (B cup B - B cup_1 dB)(01234)   on K(Z_N, 2)   (Pontryagin square)

are cocycles with values modulo 1.  The first is the associator of
Vec_(Z_N)^k, value by value; the class of the second has the order of the
spin p / 2N of the braided category Z_N^(p), and for p = 1 (N even) or p = 2
(N odd) it generates H^4(K(Z_N, 2); U(1)) = Z_(N gcd(2, N)).  The cup-1 term
is needed: (1 / 2N) B cup B alone is not a cocycle.

Run:  python3 reference/simplicial_reference.py
"""
import itertools
import os
import random
import sys
from fractions import Fraction as Fr
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bar_reference import EM, smith_invariants   # noqa: E402
from encategory_reference import vec_zn, zn_anyons, spin, mod1   # noqa: E402


def perm_sign(seq):
    s = 1
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]:
                s = -s
    return s


class Co:
    """a cochain of degree p: a function on increasing tuples of vertices"""
    def __init__(self, p, f):
        self.p, self.f = p, f

    def __call__(self, v):
        return self.f(tuple(v)) if len(v) == self.p + 1 else 0


def rand(p, rng, n):
    d = {v: rng.randint(-3, 3) for v in itertools.combinations(range(n + 1), p + 1)}
    return Co(p, lambda v: d[v])


def delta(c):
    return Co(c.p + 1, lambda v: sum((-1) ** k * c(v[:k] + v[k + 1:]) for k in range(len(v))))


def lin(*terms):
    """lin((k1, c1), (k2, c2), ...) = k1 c1 + k2 c2 + ..."""
    return Co(terms[0][1].p, lambda v: sum(k * c(v) for k, c in terms))


def cupi_terms(i, p, q):
    n = p + q - i
    out = []
    for js in itertools.combinations(range(n + 1), i + 1):
        cuts = (0,) + js + (n,)
        av, bv, inner = [], [], []
        for m in range(i + 2):
            lo, hi = cuts[m], cuts[m + 1]
            if m % 2 == 0:
                av += list(range(lo, hi + 1))
            else:
                bv += list(range(lo, hi + 1))
                inner += list(range(lo + 1, hi))
        if len(av) == p + 1 and len(bv) == q + 1:
            out.append((perm_sign(av + inner), tuple(av), tuple(bv)))
    return out


def cupi(i, a, b):
    p, q = a.p, b.p
    if i < 0 or p + q - i < 0:
        return Co(p + q - i, lambda v: 0)
    T = cupi_terms(i, p, q)
    return Co(p + q - i, lambda v: sum(s * a([v[k] for k in av]) * b([v[k] for k in bv]) for s, av, bv in T))


def cup(a, b):
    return cupi(0, a, b)


def vec(c, n):
    return [c(v) for v in itertools.combinations(range(n + 1), c.p + 1)]


def pontryagin(B):
    return lin((1, cup(B, B)), (-1, cupi(1, B, delta(B))))


# ---- integer kernels ----------------------------------------------------------------

def _axpy(col, other, q):
    """col -= q * other, for sparse columns"""
    for i, v in other.items():
        t = col.get(i, 0) - q * v
        if t:
            col[i] = t
        else:
            col.pop(i, None)


def integer_kernel_sparse(M, ncols):
    """a basis over the integers of {x : M x = 0}, by column operations M V = [H | 0].
    The vectors are returned as dictionaries position -> coefficient."""
    nr = len(M)
    Mc = [{i: M[i][j] for i in range(nr) if M[i][j]} for j in range(ncols)]
    Vc = [{j: 1} for j in range(ncols)]
    c = 0
    for r in range(nr):
        if c >= ncols:
            break
        while True:
            nz = [j for j in range(c, ncols) if Mc[j].get(r, 0) != 0]
            if not nz:
                break
            j0 = min(nz, key=lambda j: abs(Mc[j][r]))
            Mc[c], Mc[j0] = Mc[j0], Mc[c]
            Vc[c], Vc[j0] = Vc[j0], Vc[c]
            p = Mc[c][r]
            for j in range(c + 1, ncols):
                e = Mc[j].get(r, 0)
                if e != 0:
                    q = e // p
                    _axpy(Mc[j], Mc[c], q)
                    _axpy(Vc[j], Vc[c], q)
            if all(Mc[j].get(r, 0) == 0 for j in range(c + 1, ncols)):
                c += 1
                break
    return Vc[c:]


def integer_kernel(M, ncols):
    return [[z.get(i, 0) for i in range(ncols)] for z in integer_kernel_sparse(M, ncols)]


# ---- characteristic classes on K(Z_N, n) ----------------------------------------------

def lift(K, x, k):
    """the integer lift of the flat field x on the k-simplex, as a cochain of degree n"""
    val = dict(zip(K.faces(k), x))
    return Co(K.n, lambda v: val[v][0])


def dw_weight(N, kk):
    K = EM((N,), 1)

    def w(x):
        A = lift(K, x, 3)
        return mod1(Fr(kk, N * N) * cup(A, delta(A))((0, 1, 2, 3)))
    return K, w


def pontryagin_weight(N, p):
    K = EM((N,), 2)

    def w(x):
        B = lift(K, x, 4)
        return mod1(Fr(p, 2 * N) * pontryagin(B)((0, 1, 2, 3, 4)))
    return K, w


def cocycle_q(K, k, w):
    """w vanishes on degenerate k-simplices and its alternating sum over the faces of
    every (k+1)-simplex vanishes modulo 1"""
    table = {x: w(x) for x in K.simplices(k)}
    if any(table[x] != 0 for x in K.simplices(k) if K.degenerate(x, k)):
        return False
    return all(mod1(sum((-1) ** i * table[K.face(y, k + 1, i)] for i in range(k + 2))) == 0
               for y in K.simplices(k + 1))


def cycles(K, k):
    nd = {j: [x for x in K.simplices(j) if not K.degenerate(x, j)] for j in (k - 1, k)}
    idx = {x: t for t, x in enumerate(nd[k - 1])}
    M = [[0] * len(nd[k]) for _ in nd[k - 1]]
    for col, x in enumerate(nd[k]):
        for i in range(k + 1):
            f = K.face(x, k, i)
            if f in idx:
                M[idx[f]][col] += (-1) ** i
    return nd[k], M, integer_kernel_sparse(M, len(nd[k]))


_cycles = {}


def class_order(K, k, w):
    key = (K.orders, K.n, k)
    if key not in _cycles:
        _cycles[key] = cycles(K, k)
    basis, M, ker = _cycles[key]
    order = 1
    for z in ker:
        val = mod1(sum(c * w(basis[t]) for t, c in z.items()))
        order = order * val.denominator // gcd(order, val.denominator)
    return order


def main():
    rng = random.Random(20261122)
    n = 6

    # ---- the products
    assert cupi_terms(1, 1, 1) == [(1, (0, 1), (0, 1))]
    assert cupi_terms(1, 2, 1) == [(1, (0, 1, 2), (0, 1)), (1, (0, 1, 2), (1, 2))]
    assert cupi_terms(1, 1, 2) == [(-1, (0, 2), (0, 1, 2))]
    assert cupi_terms(1, 2, 2) == [(1, (0, 2, 3), (0, 1, 2)), (-1, (0, 1, 3), (1, 2, 3))]
    assert cupi_terms(2, 2, 2) == [(1, (0, 1, 2), (0, 1, 2))]
    assert [len(cupi_terms(1, p, q)) for p, q in ((2, 3), (3, 2), (3, 3))] == [2, 3, 3]
    for p in range(0, 5):
        c = rand(p, rng, n)
        assert all(x == 0 for x in vec(delta(delta(c)), n))
    cnt = 0
    for p, q in itertools.product(range(0, 4), repeat=2):
        a, b = rand(p, rng, n), rand(q, rng, n)
        assert vec(delta(cup(a, b)), n) == vec(lin((1, cup(delta(a), b)), ((-1) ** p, cup(a, delta(b)))), n)
        for r in range(0, 3):
            c = rand(r, rng, n)
            assert vec(cup(cup(a, b), c), n) == vec(cup(a, cup(b, c)), n)
        for i in range(0, 5):
            if p + q - i < 0:
                continue
            lhs = lin((1, cupi(i, a, b)), (-(-1) ** (p * q + i), cupi(i, b, a)))
            s = (-1) ** (p + q + 1 + i)
            rhs = lin((s, delta(cupi(i + 1, a, b))), (-s, cupi(i + 1, delta(a), b)),
                      (-s * (-1) ** p, cupi(i + 1, a, delta(b))))
            assert vec(lhs, n) == vec(rhs, n), ("A3", p, q, i)
            if i > min(p, q):
                assert all(x == 0 for x in vec(cupi(i, a, b), n))
            cnt += 1
    print("d d = 0, the Leibniz rule, associativity, and (A3) for all degrees up to 3 (%d cases)  True" % cnt)

    # ---- the Hirsch formula holds exactly on simplices
    cnt = 0
    for p, q, r in itertools.product(range(1, 4), repeat=3):
        if p + q + r - 1 > n:
            continue
        a, b, c = rand(p, rng, n), rand(q, rng, n), rand(r, rng, n)
        hirsch = lin((1, cupi(1, cup(a, b), c)), (-1, cup(a, cupi(1, b, c))),
                     (-(-1) ** (q * (r - 1)), cup(cupi(1, a, c), b)))
        assert all(x == 0 for x in vec(hirsch, n)), ("Hirsch", p, q, r)
        cnt += 1
    print("(a cup b) cup_1 c = a cup (b cup_1 c) + (-1)^(q(r-1)) (a cup_1 c) cup b, exactly (%d cases)  True" % cnt)

    # ---- the identities of the lattice gauge theory layer hold on simplices as well
    for N in (2, 3, 4):
        B, lam, c = rand(2, rng, n), rand(1, rng, n), rand(2, rng, n)
        dB, dl = delta(B), delta(lam)
        lhs = lin((1, pontryagin(lin((1, B), (1, dl)))), (-1, pontryagin(B)))
        rhs = lin((1, delta(lin((2, cup(lam, B)), (1, cup(lam, dl)), (-1, cupi(1, B, dl))))),
                  (2, cup(lam, dB)), (1, cupi(1, dB, dl)), (-1, cupi(1, dl, dB)))
        assert vec(lhs, n) == vec(rhs, n)
        lhs = lin((1, pontryagin(lin((1, B), (N, c)))), (-1, pontryagin(B)))
        rhs = lin((2 * N, cup(c, B)), (N * N, cup(c, c)), (-N * N, cupi(1, c, delta(c))),
                  (-N, delta(cupi(1, B, c))), (N, cupi(1, dB, c)), (-N, cupi(1, c, dB)))
        assert vec(lhs, n) == vec(rhs, n)
        a = rand(1, rng, n)
        da = delta(a)
        assert vec(lin((1, cup(a, da)), (-1, cup(da, a))), n) == \
            vec(lin((1, delta(cupi(1, a, da))), (-1, cupi(1, da, da))), n)
    print("the Pontryagin-square identities of the hypercubic lattice hold on simplices  True")

    # ---- integer kernels
    for trial in range(300):
        nr, nc = rng.randint(1, 5), rng.randint(1, 7)
        M = [[rng.randint(-4, 4) for _ in range(nc)] for _ in range(nr)]
        if rng.random() < 0.4 and nr > 1:
            M[-1] = [3 * x for x in M[0]]
        ker = integer_kernel(M, nc)
        rank = len(smith_invariants(M, nc))
        assert len(ker) == nc - rank
        assert all(sum(M[i][j] * z[j] for j in range(nc)) == 0 for z in ker for i in range(nr))
        if ker:
            assert smith_invariants(ker, nc) == [1] * len(ker)        # saturated
    assert integer_kernel([[2, 4, 6]], 3) == [[-2, 1, 0], [-3, 0, 1]]
    assert integer_kernel([[1, 1, 0], [0, 1, 1]], 3) == [[1, -1, 1]]
    assert integer_kernel([[1, 0], [0, 1]], 2) == [] and integer_kernel([[0, 0]], 2) == [[1, 0], [0, 1]]
    print("integer kernels: M z = 0, the right rank, saturated  True")

    # ---- Dijkgraaf-Witten: the lattice action on a tetrahedron is the associator
    for N in (2, 3, 4, 5):
        for kk in range(N):
            K, w = dw_weight(N, kk)
            cat = vec_zn(N, kk)
            for x in K.simplices(3):
                val = dict(zip(K.faces(3), x))
                assert w(x) == mod1(cat.w(val[(0, 1)], val[(1, 2)], val[(2, 3)]))
            if N <= 4:
                assert cocycle_q(K, 3, w)
                assert class_order(K, 3, w) == N // gcd(kk, N)
    print("(k / N^2) A cup dA on a flat field on a tetrahedron = the associator of Vec_(Z_N)^k;"
          " a cocycle of order N / gcd(k, N)  True")

    # ---- the Pontryagin square on K(Z_N, 2)
    for N in (2, 3, 4):
        for p in range(2 * N):
            if N % 2 == 1 and p % 2 == 1:
                continue
            K, w = pontryagin_weight(N, p)
            if N == 2 or (N, p) == (3, 2):
                assert cocycle_q(K, 4, w), (N, p)
            order = class_order(K, 4, w)
            assert order == spin(zn_anyons(N, p), (1,)).denominator == 2 * N // gcd(p, 2 * N), (N, p, order)
        # a half-integer level is not a cocycle when N is odd
        if N == 3:
            K, w = pontryagin_weight(3, 1)
            assert not cocycle_q(K, 4, w)
    # without the cup-1 term the weight B cup B / 2N is not a cocycle; B cup B / N is one
    K = EM((2,), 2)

    def square(level):
        return lambda x: mod1(Fr(level, 4) * cup(lift(K, x, 4), lift(K, x, 4))((0, 1, 2, 3, 4)))
    assert not cocycle_q(K, 4, square(1))
    assert cocycle_q(K, 4, square(2)) and class_order(K, 4, square(2)) == 2
    basis, M, ker = cycles(K, 4)
    assert (len(basis), len(M), len(ker)) == (41, 4, 38)
    print("(p / 2N) P(B) on K(Z_N, 2): a cocycle whose class has the order of the spin p / 2N;"
          " it generates H^4 = Z_(N gcd(2, N))  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
