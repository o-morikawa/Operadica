#!/usr/bin/env python3
"""
Reference checks (pure Python, exact rational arithmetic) for the action of the
little n-cubes on n-fold loop spaces, the statement of the recognition
theorem: an n-fold loop space is an algebra over the little n-cubes operad.

A point of Omega^n Y is a map g from the unit n-cube to Y that sends the
boundary to the base point.  A configuration c of k little cubes acts by

    theta(c; g_1, .., g_k)(t) = g_i(c_i^(-1)(t))   if t lies inside the cube c_i,
                                the base point     otherwise.

Conventions as in Operadica`LittleCubes`: a configuration is a list of cubes, a
cube a list of intervals (a, b); c o_i d inserts d into the i-th cube;
(c . s)_j = c_(s(j)).

Checked, for random configurations with rational endpoints and generic loops
(the value of g_j at an inner point u is the pair (j, u)):

  unit            theta(1; g) = g
  composition     theta(c o_i d; .., h_1, .., h_m, ..) = theta(c; .., theta(d; h_1, .., h_m), ..)
  equivariance    theta(c . s; g_1, .., g_k) = theta(c; g_(s^-1(1)), .., g_(s^-1(k)))
  approximation   alpha(c; x_1, .., x_k) = theta(c; eta(x_1), .., eta(x_k)), with the unit
                  eta(x)(t) = [t, x] of the suspension, is a map of algebras:
                  alpha(c o (d_1, .., d_k); x) = theta(c; alpha(d_1; x^1), .., alpha(d_k; x^k))
  commutativity   for n >= 2 there is a path of configurations of two cubes from c to c . (12):
                  the product of an n-fold loop space is commutative up to homotopy

Both sides of an identity are piecewise affine, so they are compared at n + 1
points of every cell of the grid of all endpoints: for the configurations
tested this is a proof at all points off the grid.

Run:  python3 reference/loops_reference.py
"""
import itertools
import random
import sys
from fractions import Fraction as Fr

BASE = "base"


def compose(c, i, d):
    """c o_i d (i counted from 1)"""
    big = c[i - 1]
    inner = [tuple((a + (b - a) * lo, a + (b - a) * hi) for (a, b), (lo, hi) in zip(big, cube)) for cube in d]
    return c[:i - 1] + inner + c[i:]


def compose_all(c, ds):
    out = c
    for i in range(len(ds), 0, -1):
        out = compose(out, i, ds[i - 1])
    return out


def act(c, s):
    return [c[j - 1] for j in s]


def valid(c, n):
    for cube in c:
        if len(cube) != n or any(not (0 <= a < b <= 1) for a, b in cube):
            return False
    for x, y in itertools.combinations(c, 2):
        if all(max(a1, a2) < min(b1, b2) for (a1, b1), (a2, b2) in zip(x, y)):
            return False
    return True


def random_cubes(n, k, rng):
    """split the unit cube k - 1 times, then shrink every box a little"""
    boxes = [tuple((Fr(0), Fr(1)) for _ in range(n))]
    while len(boxes) < k:
        q = boxes.pop(rng.randrange(len(boxes)))
        ax = rng.randrange(n)
        lo, hi = q[ax]
        cut = lo + (hi - lo) * Fr(rng.randint(1, 4), 5)
        boxes.append(q[:ax] + ((lo, cut),) + q[ax + 1:])
        boxes.append(q[:ax] + ((cut, hi),) + q[ax + 1:])
    out = []
    for q in boxes:
        cube = []
        for lo, hi in q:
            w = hi - lo
            cube.append((lo + w * Fr(rng.randint(0, 2), 10), hi - w * Fr(rng.randint(0, 2), 10)))
        out.append(tuple(cube))
    rng.shuffle(out)
    return out


def generic(name):
    return lambda t: BASE if any(v <= 0 or v >= 1 for v in t) else (name, tuple(t))


def theta(c, *gs):
    def loop(t):
        for cube, g in zip(c, gs):
            if all(a < v < b for v, (a, b) in zip(t, cube)):
                return g(tuple((v - a) / (b - a) for v, (a, b) in zip(t, cube)))
        return BASE
    return loop


def eta(x):
    return lambda t: BASE if any(v <= 0 or v >= 1 for v in t) else ("susp", tuple(t), x)


def alpha(c, xs):
    return theta(c, *[eta(x) for x in xs])


def sample_points(c, n):
    """n + 1 affinely independent points in every cell of the grid of the endpoints of c"""
    pts = []
    axes = []
    for mu in range(n):
        cuts = sorted({Fr(0), Fr(1)} | {e for cube in c for e in cube[mu]})
        axes.append(list(zip(cuts[:-1], cuts[1:])))
    for cell in itertools.product(*axes):
        mid = tuple((lo + hi) / 2 for lo, hi in cell)
        pts.append(mid)
        for mu in range(n):
            pts.append(mid[:mu] + (mid[mu] + (cell[mu][1] - cell[mu][0]) / 4,) + mid[mu + 1:])
    return pts


def equal(g, h, c, n):
    return all(g(t) == h(t) for t in sample_points(c, n))


def swap_path(n, s):
    """two cubes of side 1/4 whose centres go half way round a square: from c to c . (12)"""
    s = Fr(s)

    def q(l):
        l = l % 2
        if l <= Fr(1, 4):
            return (Fr(1, 4), Fr(1, 2) - l)
        if l <= Fr(3, 4):
            return (Fr(1, 4) + (l - Fr(1, 4)), Fr(1, 4))
        if l <= Fr(5, 4):
            return (Fr(3, 4), Fr(1, 4) + (l - Fr(3, 4)))
        if l <= Fr(7, 4):
            return (Fr(3, 4) - (l - Fr(5, 4)), Fr(3, 4))
        return (Fr(1, 4), Fr(3, 4) - (l - Fr(7, 4)))

    def cube(centre):
        return tuple((x - Fr(1, 8), x + Fr(1, 8)) for x in centre) + tuple((Fr(0), Fr(1)) for _ in range(n - 2))
    return [cube(q(s)), cube(q(s + 1))]


def main():
    rng = random.Random(20261122)
    unit = lambda n: [tuple((Fr(0), Fr(1)) for _ in range(n))]

    assert compose([((Fr(0), Fr(1, 2)),), ((Fr(1, 2), Fr(1)),)], 2, [((Fr(0), Fr(1, 2)),), ((Fr(1, 2), Fr(1)),)]) == \
        [((Fr(0), Fr(1, 2)),), ((Fr(1, 2), Fr(3, 4)),), ((Fr(3, 4), Fr(1)),)]
    g1, g2, g3 = generic(1), generic(2), generic(3)
    half = [((Fr(0), Fr(1, 2)),), ((Fr(1, 2), Fr(1)),)]
    prod = theta(half, g1, g2)
    assert prod((Fr(1, 4),)) == (1, (Fr(1, 2),)) and prod((Fr(7, 8),)) == (2, (Fr(3, 4),)) and prod((Fr(1, 2),)) == BASE
    # the two ways to multiply three loops are different maps, given by two configurations
    left = theta(compose(half, 1, half), g1, g2, g3)
    right = theta(compose(half, 2, half), g1, g2, g3)
    assert left((Fr(3, 8),)) == (2, (Fr(1, 2),)) and right((Fr(3, 8),)) == (1, (Fr(3, 4),))

    cnt = 0
    for n in (1, 2, 3):
        for trial in range(12 if n < 3 else 5):
            k, m = rng.randint(1, 3), rng.randint(1, 3)
            c, d = random_cubes(n, k, rng), random_cubes(n, m, rng)
            assert valid(c, n) and valid(d, n)
            g = [generic(("g", j)) for j in range(k)]
            h = [generic(("h", j)) for j in range(m)]
            # unit
            assert equal(theta(unit(n), g[0]), g[0], c, n)
            for i in range(1, k + 1):
                cd = compose(c, i, d)
                assert valid(cd, n)
                lhs = theta(cd, *(g[:i - 1] + h + g[i:]))
                rhs = theta(c, *(g[:i - 1] + [theta(d, *h)] + g[i:]))
                assert equal(lhs, rhs, cd + c, n)
                cnt += 1
            # equivariance
            s = list(range(1, k + 1))
            rng.shuffle(s)
            inv = [s.index(j + 1) for j in range(k)]
            assert equal(theta(act(c, s), *g), theta(c, *[g[inv[j]] for j in range(k)]), c, n)
            # the approximation map is a map of algebras
            ds = [random_cubes(n, rng.randint(1, 2), rng) for _ in range(k)]
            labels = [[("x", a, b) for b in range(len(ds[a]))] for a in range(k)]
            big = compose_all(c, ds)
            assert valid(big, n)
            lhs = alpha(big, [x for row in labels for x in row])
            rhs = theta(c, *[alpha(ds[a], labels[a]) for a in range(k)])
            assert equal(lhs, rhs, big + c, n)
    print("unit, composition (%d cases), equivariance, and the approximation map is a map of algebras  True" % cnt)

    # commutativity up to homotopy for n >= 2
    for n in (2, 3):
        steps = [Fr(j, 16) for j in range(0, 33)]
        assert all(valid(swap_path(n, s), n) for s in steps)
        assert swap_path(n, 1) == act(swap_path(n, 0), [2, 1])
        assert swap_path(n, 2) == swap_path(n, 0)
        c0 = swap_path(n, 0)
        a, b = generic("a"), generic("b")
        assert equal(theta(swap_path(n, 1), a, b), theta(c0, b, a), c0, n)
    assert swap_path(2, 0) == [((Fr(1, 8), Fr(3, 8)), (Fr(3, 8), Fr(5, 8))), ((Fr(5, 8), Fr(7, 8)), (Fr(3, 8), Fr(5, 8)))]
    assert swap_path(2, Fr(1, 2)) == [((Fr(3, 8), Fr(5, 8)), (Fr(1, 8), Fr(3, 8))), ((Fr(3, 8), Fr(5, 8)), (Fr(5, 8), Fr(7, 8)))]
    print("for n >= 2 a path of configurations exchanges the two cubes: a b ~ b a  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
