#!/usr/bin/env python3
"""
Reference checks (pure Python, exact integer and rational arithmetic) for
Steenrod squares at the level of cochains,

    Sq^k x = x cup_(p-k) x        (x of degree p, 0 <= k <= p),

with the higher cup products of Operadica`Lattice` (hypercubic lattice) and
Operadica`Simplicial` (simplices), in the convention of eq. (A3) of
arXiv:2303.06160.

Checked, for integer cochains x:

  Sq^0            (x cup_p x)(cell) = x(cell)^2 on simplices and on cubes: modulo 2 it is x
  coboundary      d(Sq^k x) = (-1)^(p-k) (1 + (-1)^k) Sq^(k+1) x
                              + dx cup_(p-k) x + (-1)^p x cup_(p-k) dx
                  on simplices and on cubes (a case of (A3)).  So if dx is even, then
                  Sq^k x is a cocycle modulo 2, and for even k
                      d(Sq^k x) / 2 = +- Sq^(k+1) x   modulo 2:
                  the Bockstein of Sq^(2m) is Sq^(2m+1)  (the Adem relation Sq^1 Sq^(2m) = Sq^(2m+1)).
  Bockstein       on K(Z_2, n), with the lift of the flat field to the values 0, 1:
                      Sq^1 B = dB / 2   modulo 2, as cochains;  for n = 1, A cup A = dA / 2 exactly.
  weights         (1/2) Sq^k B on the (n+k)-simplices of K(Z_2, n) is a cocycle with values in
                  R/Z.  Its class in H^(n+k)(K(Z_2, n); U(1)) has the order
                      (n, k) = (1, 1), (2, 1), (3, 1):  1   (it is the coboundary of B / 4)
                      (2, 2):  2   ((1/2) B cup B, the fermion among the anyons of Z_2)
                      (3, 2):  2   ((1/2) C cup_1 C, the generator of H^5(K(Z_2, 3); U(1)) = Z_2:
                                    the symmetric structure of the fermion, E_3 and beyond)
                  For Z_3 the weight (1/2) B cup B is not a cocycle.

Run:  python3 reference/steenrod_reference.py      (about 10 s)
"""

import itertools
import random
import sys
from fractions import Fraction as Fr

import cubical_reference as cr
import simplicial_reference as sr
from bar_reference import EM
from encategory_reference import zn_anyons, spin, mod1

Co, sdelta, cupi, lin = sr.Co, sr.delta, sr.cupi, sr.lin


def sq(k, x):
    """Sq^k on simplices"""
    p = x.p
    if k < 0 or k > p:
        return Co(p + k, lambda v: 0)
    return cupi(p - k, x, x)


def weight(K, n, k):
    """(1/2) Sq^k of the lifted flat field, on a simplex of dimension n + k"""
    top = tuple(range(n + k + 1))

    def w(x):
        return mod1(Fr(1, 2) * sq(k, sr.lift(K, x, n + k))(top))
    return w


def random_simplex(K, k, rng):
    """a random k-simplex of K(A, n): the coboundary of a random (n-1)-cochain on the k-simplex"""
    n, N = K.n, K.orders[0]
    g = {f: rng.randrange(N) for f in itertools.combinations(range(k + 1), n)}
    return tuple(((sum((-1) ** i * g[f[:i] + f[i + 1:]] for i in range(n + 1))) % N,) for f in K.faces(k))


def main():
    rng = random.Random(20261123)

    # ---- simplices ----
    for p in (0, 1, 2, 3):
        x = sr.rand(p, rng, p)
        v = tuple(range(p + 1))
        assert sq(0, x)(v) == x(v) ** 2
    cnt = 0
    for p in (1, 2, 3):
        for k in range(0, p + 1):
            n = p + k + 1
            for _ in range(2):
                x = sr.rand(p, rng, n)
                lhs = sdelta(sq(k, x))
                rhs = lin(((-1) ** (p - k) * (1 + (-1) ** k), sq(k + 1, x)),
                          (1, cupi(p - k, sdelta(x), x)),
                          ((-1) ** p, cupi(p - k, x, sdelta(x))))
                assert sr.vec(lhs, n) == sr.vec(rhs, n), (p, k)
                cnt += 1
    print("simplices: Sq^0 x = x^2 pointwise; d(Sq^k x) = (-1)^(p-k) (1 + (-1)^k) Sq^(k+1) x + ... (%d cases)  True" % cnt)

    # ---- cubes ----
    lat = cr.Lattice(4, 2)
    cnt = 0
    for p in (0, 1, 2, 3, 4):
        x = lat.random_cochain(p, rng)
        s0 = cr.higher_cup(p, x, x)
        assert all(s0(c, S) == x(c, S) ** 2 for c, S in lat.cells(p)), p
        for k in range(0, p + 1):
            if p + k + 1 > 4:
                continue
            dx = cr.delta(x)
            lhs = cr.delta(cr.higher_cup(p - k, x, x))
            terms = [(1, cr.higher_cup(p - k, dx, x)), ((-1) ** p, cr.higher_cup(p - k, x, dx))]
            if k + 1 <= p:
                terms.append(((-1) ** (p - k) * (1 + (-1) ** k), cr.higher_cup(p - k - 1, x, x)))
            assert cr.equal(lat, lhs, cr.comb(lat, p + k + 1, terms), p + k + 1), (p, k)
            cnt += 1
    print("cubes: the same two statements (%d cases in four dimensions)  True" % cnt)

    # ---- the Bockstein ----
    for n in (1, 2, 3):
        K = EM((2,), n)
        top = tuple(range(n + 2))
        for x in K.simplices(n + 1):
            B = sr.lift(K, x, n + 1)
            dB = sdelta(B)(top)
            assert dB % 2 == 0
            assert (sq(1, B)(top) - dB // 2) % 2 == 0
            if n == 1:
                assert sq(1, B)(top) == dB // 2
    print("K(Z_2, n), n = 1, 2, 3: Sq^1 B = dB / 2 modulo 2 as cochains; A cup A = dA / 2 exactly  True")

    # ---- weights ----
    orders = {}
    for n, k in [(1, 1), (2, 1), (2, 2), (3, 1)]:
        K = EM((2,), n)
        w = weight(K, n, k)
        assert sr.cocycle_q(K, n + k, w), (n, k)
        orders[(n, k)] = sr.class_order(K, n + k, w)
    K = EM((2,), 3)
    w = weight(K, 3, 2)
    table = {x: w(x) for x in K.simplices(5)}
    assert all(table[x] == 0 for x in table if K.degenerate(x, 5))
    for _ in range(20000):
        y = random_simplex(K, 6, rng)
        assert mod1(sum((-1) ** i * table[K.face(y, 6, i)] for i in range(7))) == 0
    orders[(3, 2)] = sr.class_order(K, 5, w)
    assert orders == {(1, 1): 1, (2, 1): 1, (2, 2): 2, (3, 1): 1, (3, 2): 2}, orders
    fermion = zn_anyons(2, 2)
    assert spin(fermion, (1,)) == Fr(1, 2) and spin(fermion, (1,)).denominator == orders[(2, 2)] == orders[(3, 2)]
    print("(1/2) Sq^k on K(Z_2, n): cocycles; class orders", orders, " True")

    # a single 5-simplex of K(Z_2, 3) can be a cycle: its nondegenerate faces cancel
    nd = [x for x in K.simplices(5) if not K.degenerate(x, 5)]

    def boundary(x):
        out = {}
        for i in range(6):
            f = K.face(x, 5, i)
            if not K.degenerate(f, 4):
                out[f] = out.get(f, 0) + (-1) ** i
        return {f: c for f, c in out.items() if c != 0}
    closed = [x for x in nd if not boundary(x)]
    odd = [x for x in closed if table[x] == Fr(1, 2)]
    assert len(nd) == 958 and odd
    print("K(Z_2, 3): 958 nondegenerate 5-simplices, %d of them cycles, %d of these with weight 1/2  True"
          % (len(closed), len(odd)))
    print("   one of them (values on the faces 0123, 0124, ..., 2345):", [g[0] for g in odd[0]])

    K3 = EM((3,), 2)
    assert not sr.cocycle_q(K3, 4, weight(K3, 2, 2))
    print("for Z_3 the weight (1/2) B cup B is not a cocycle  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
