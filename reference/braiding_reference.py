#!/usr/bin/env python3
"""
Reference checks (pure Python, exact rational arithmetic) for the braid of a
path of little squares and the phase a pointed braided category gives to it.

A path of configurations of k little n-cubes (n >= 2) is read in the first two
directions.  The cubes are ordered by the centre, lexicographically in (x, y).
When two neighbours p, q (p on the left) change places between two consecutive
samples, the relative position r = centre(q) - centre(p) turns from r0 to r1,
and the generator is

    sigma_i       if r0 x r1 > 0   (counterclockwise: the cube from the left passes below)
    sigma_i^(-1)  if r0 x r1 < 0
    undefined     if r0 x r1 = 0   (a half turn in one step, or centres that coincide)

with i the position of p.  A braid is a list of nonzero integers, +i for
sigma_i and -i for its inverse.

A pointed braided category (conventions of Operadica`EnCategories`) gives the
phase c(a, b) to the counterclockwise exchange of a (left) and b (right); this
fixes the orientation of the plane.  On the right-nested product of a word the
generator sigma_i has the phase -w(a, b, x) + c(a, b) + w(b, a, x).

Checked:

  two squares     the braid of SwapPath is sigma for half of the way and sigma^2 for the whole
                  way, for every number of steps >= 2; one step is refused.  For random walks of
                  the relative position around a square the exponent sum is the number of half
                  turns, counted independently.
  three squares   one square walking around two others: the exponent sum is twice the sum of the
                  winding numbers, and finer sampling gives the same braid (compared in the Burau
                  representation at t = 2).
  composition     the half turn of two rows of m1 and m2 squares (the operad composition of
                  SwapPath with the rows) is the block braid; its phase is
                      - R(blocks) + c(A, B) + R(blocks exchanged)
                  with R the reassociation to the right-nested product.  For (1, 2) and (2, 1)
                  this is exactly the first and the second hexagon equation.
  phases          half turn of two equal objects = spin, whole turn = mutual braiding,
                  inverse generators, gauge invariance of the phases of pure braids.
  three cubes     SwapHomotopy is a homotopy, relative to the end points, between the
                  counterclockwise and the clockwise half turn inside C_3(2).  A phase that
                  depends only on the homotopy class needs c(a, b) = - c(b, a): symmetric.

Run:  python3 reference/braiding_reference.py
"""

import itertools
import random
import sys
from fractions import Fraction as Fr

import encategory_reference as ec
import loops_reference as lp


# ---- the braid of a path ------------------------------------------------------

def centre(cube):
    return tuple((a + b) / 2 for a, b in cube[:2])


def order(c):
    """labels of the cubes from left to right, or None if two centres coincide in the plane"""
    pts = [centre(q) for q in c]
    if len(set(pts)) < len(pts):
        return None
    return tuple(sorted(range(1, len(c) + 1), key=lambda j: pts[j - 1]))


def step_generators(prev, cur):
    op, oc = order(prev), order(cur)
    if op is None or oc is None:
        return None
    gens, pos, k = [], 0, len(op)
    while pos < k:
        if op[pos] == oc[pos]:
            pos += 1
            continue
        if pos + 1 < k and op[pos] == oc[pos + 1] and op[pos + 1] == oc[pos]:
            p, q = op[pos], op[pos + 1]
            r0 = [x - y for x, y in zip(centre(prev[q - 1]), centre(prev[p - 1]))]
            r1 = [x - y for x, y in zip(centre(cur[q - 1]), centre(cur[p - 1]))]
            z = r0[0] * r1[1] - r0[1] * r1[0]
            if z == 0:
                return None
            gens.append(pos + 1 if z > 0 else -(pos + 1))
            pos += 2
        else:
            return None
    return gens


def path_braid(path, s0, s1, steps):
    s0, s1 = Fr(s0), Fr(s1)
    configs = [path(s0 + (s1 - s0) * Fr(j, steps)) for j in range(steps + 1)]
    word = []
    for a, b in zip(configs[:-1], configs[1:]):
        g = step_generators(a, b)
        if g is None:
            return None
        word += g
    return word


def exponent(braid):
    return sum(1 if g > 0 else -1 for g in braid)


def burau(braid, k, t=Fr(2)):
    """the (unreduced) Burau matrix of a braid on k strands at a rational t"""
    def gen(i, inverse):
        m = [[Fr(int(r == c)) for c in range(k)] for r in range(k)]
        if not inverse:
            m[i - 1][i - 1], m[i - 1][i], m[i][i - 1], m[i][i] = 1 - t, t, Fr(1), Fr(0)
        else:
            m[i - 1][i - 1], m[i - 1][i], m[i][i - 1], m[i][i] = Fr(0), Fr(1), 1 / t, 1 - 1 / t
        return m

    def mul(x, y):
        return [[sum(x[r][j] * y[j][c] for j in range(k)) for c in range(k)] for r in range(k)]
    out = [[Fr(int(r == c)) for c in range(k)] for r in range(k)]
    for g in braid:
        out = mul(out, gen(abs(g), g < 0))
    return out


# ---- paths --------------------------------------------------------------------

def small(point, side=Fr(1, 16)):
    return tuple((x - side / 2, x + side / 2) for x in point)


RING = [(Fr(1, 4), Fr(0)), (Fr(1, 4), Fr(1, 8)), (Fr(1, 4), Fr(1, 4)), (Fr(1, 8), Fr(1, 4)),
        (Fr(0), Fr(1, 4)), (Fr(-1, 8), Fr(1, 4)), (Fr(-1, 4), Fr(1, 4)), (Fr(-1, 4), Fr(1, 8)),
        (Fr(-1, 4), Fr(0)), (Fr(-1, 4), Fr(-1, 8)), (Fr(-1, 4), Fr(-1, 4)), (Fr(-1, 8), Fr(-1, 4)),
        (Fr(0), Fr(-1, 4)), (Fr(1, 8), Fr(-1, 4)), (Fr(1, 4), Fr(-1, 4)), (Fr(1, 4), Fr(-1, 8))]
"""16 points on the square |r| = 1/4, counterclockwise from (1/4, 0); 8 of them make a half turn"""


def piecewise(points):
    """the piecewise linear path through the points, parametrised by [0, len - 1]"""
    def at(s):
        s = Fr(s)
        j = min(int(s), len(points) - 2)
        f = s - j
        return tuple((1 - f) * a + f * b for a, b in zip(points[j], points[j + 1]))
    return at


def ring_walk(rng, length):
    """a random walk on RING from index 0 to an index 0 or 8 mod 16; returns (indices, half turns)"""
    idx = [0]
    for _ in range(length):
        idx.append(idx[-1] + rng.choice([-1, 1]))
    while idx[-1] % 8 != 0:
        idx.append(idx[-1] + 1)
    return idx, idx[-1] // 8


def two_squares(idx):
    rel = piecewise([RING[i % 16] for i in idx])

    def path(s):
        r = rel(s)
        return [small((Fr(1, 2) - r[0] / 2, Fr(1, 2) - r[1] / 2), Fr(1, 8)),
                small((Fr(1, 2) + r[0] / 2, Fr(1, 2) + r[1] / 2), Fr(1, 8))]
    return path


def row(m):
    return [((Fr(j, m), Fr(j + 1, m)), (Fr(0), Fr(1))) for j in range(m)]


def block_path(m1, m2):
    return lambda s: lp.compose_all(lp.swap_path(2, s), [row(m1), row(m2)])


def block_braid(m1, m2):
    """every strand of the first block passes below every strand of the second one"""
    word = list(range(m1 + m2))
    target = list(range(m1, m1 + m2)) + list(range(m1))
    gens = []
    while word != target:
        moved = False
        pos = 0
        new, step = list(word), []
        while pos < len(word) - 1:
            if word[pos] < m1 <= word[pos + 1]:
                new[pos], new[pos + 1] = word[pos + 1], word[pos]
                step.append(pos + 1)
                pos += 2
                moved = True
            else:
                pos += 1
        assert moved
        word = new
        gens += step
    return gens


def direction(u):
    u = Fr(u)
    if u <= Fr(1, 4):
        return (Fr(1), 4 * u)
    if u <= Fr(3, 4):
        return (2 - 4 * u, Fr(1))
    return (Fr(-1), 4 - 4 * u)


def swap_homotopy(u, s):
    v = direction(u)
    out = []
    for q in (lp.swap_path(2, s)[0], lp.swap_path(2, s)[1]):
        x, y = centre(q)
        out.append(small((x, Fr(1, 2) + (y - Fr(1, 2)) * v[0], Fr(1, 2) + (y - Fr(1, 2)) * v[1]), Fr(1, 4)))
    return out


# ---- phases -------------------------------------------------------------------

def braid_phase(cat, word, braid):
    """(phase, final word) of a braid on the right-nested product of word"""
    total, word = Fr(0), tuple(word)
    for g in braid:
        if g > 0:
            ph, word = ec.braid(cat, word, g)
            total += ph
        else:
            i = -g
            before = word[:i - 1] + (word[i], word[i - 1]) + word[i + 1:]
            ph, back = ec.braid(cat, before, i)
            assert back == word
            total -= ph
            word = before
    return ec.mod1(total), word


def comb(objs):
    """the right-nested product as a tree of encategory_reference"""
    if len(objs) == 1:
        return ('x', objs[0])
    return ('m', ('x', objs[0]), comb(objs[1:]))


def total(G, objs):
    out = G.zero
    for g in objs:
        out = G.add(out, g)
    return out


def block_expected(cat, left, right):
    G = cat.G
    r0 = ec.reassoc_phase(cat, ('m', comb(left), comb(right)))
    r1 = ec.reassoc_phase(cat, ('m', comb(right), comb(left)))
    return ec.mod1(-r0 + cat.c(total(G, left), total(G, right)) + r1)


def block_holds(cat, m1, m2, braid):
    G = cat.G
    for word in itertools.product(G.elements, repeat=m1 + m2):
        left, right = word[:m1], word[m1:]
        ph, final = braid_phase(cat, word, braid)
        if final != right + left or ph != block_expected(cat, left, right):
            return False
    return True


def hexagon_one(cat):
    G, w, c = cat.G, cat.w, cat.c
    return all(ec.mod1((w(b, d, a) + c(a, G.add(b, d)) + w(a, b, d)) - (c(a, d) + w(b, a, d) + c(a, b))) == 0
               for a, b, d in itertools.product(G.elements, repeat=3))


def hexagon_two(cat):
    G, w, c = cat.G, cat.w, cat.c
    return all(ec.mod1((-w(d, a, b) + c(G.add(a, b), d) - w(a, b, d)) - (c(a, d) - w(a, d, b) + c(b, d))) == 0
               for a, b, d in itertools.product(G.elements, repeat=3))


def random_cat(orders, rng, den=4):
    G = ec.Group(orders)
    wt = {t: (Fr(0) if G.zero in t else Fr(rng.randrange(den), den))
          for t in itertools.product(G.elements, repeat=3)}
    ct = {t: (Fr(0) if G.zero in t else Fr(rng.randrange(den), den))
          for t in itertools.product(G.elements, repeat=2)}
    return ec.Cat(G, lambda a, b, c: wt[(a, b, c)], lambda a, b: ct[(a, b)])


def main():
    rng = random.Random(20261122)
    swap2 = lambda s: lp.swap_path(2, s)

    # ---- two squares ----
    assert order(swap2(0)) == (1, 2) and order(swap2(1)) == (2, 1)
    assert order(swap2(Fr(1, 2))) == (1, 2)          # equal x: the lower square comes first
    for steps in (2, 3, 4, 5, 7, 8, 16, 32):
        assert path_braid(swap2, 0, 1, steps) == [1]
        assert path_braid(swap2, 1, 2, steps) == [1]
        assert path_braid(swap2, 0, 2, 2 * steps) == [1, 1]
        assert path_braid(lambda s: swap2(1 - Fr(s)), 0, 1, steps) == [-1]
        assert path_braid(swap2, 0, Fr(1, 4), steps) == []
    assert path_braid(swap2, 0, 1, 1) is None        # a half turn in one step
    assert path_braid(swap2, 0, 2, 2) is None
    assert path_braid(swap2, 0, 2, 3) == [1, 1]
    # for n >= 3 the first two directions are read
    assert path_braid(lambda s: lp.swap_path(3, s), 0, 1, 8) == [1]
    print("the braid of SwapPath is sigma (half way) and sigma^2 (all the way)  True")

    cnt = 0
    for _ in range(300):
        idx, half = ring_walk(rng, rng.randint(1, 40))
        path = two_squares(idx)
        n = len(idx) - 1
        assert all(lp.valid(path(Fr(j, 3)), 2) for j in range(3 * n + 1))
        for steps in (n, 2 * n, 3 * n):
            b = path_braid(path, 0, n, steps)
            assert b is not None and exponent(b) == half
            assert all(g in (1, -1) for g in b)
        # coarser sampling: every second point of the square
        if n % 2 == 0:
            b = path_braid(path, 0, n, n // 2)
            assert b is not None and exponent(b) == half
        cnt += 1
    print("exponent sum = number of counterclockwise half turns (%d random walks)  True" % cnt)

    # ---- three squares: one walks around two others ----
    fixed = [(Fr(5, 16), Fr(1, 2)), (Fr(11, 16), Fr(1, 2))]
    grid = [(Fr(i, 16), Fr(j, 16)) for i in range(2, 15) for j in range(2, 15)]

    def free(pt):
        return all(max(abs(pt[0] - f[0]), abs(pt[1] - f[1])) >= Fr(1, 8) for f in fixed)

    def sector(r):
        x, y = r
        if y == 0:
            return 0 if x > 0 else 4
        if x == 0:
            return 2 if y > 0 else 6
        return {(True, True): 1, (False, True): 3, (False, False): 5, (True, False): 7}[(x > 0, y > 0)]

    def winding(points, f):
        """the number of turns of the closed polygon around f, by counting sectors"""
        tot = 0
        for a, b in zip(points[:-1], points[1:]):
            d = (sector((b[0] - f[0], b[1] - f[1])) - sector((a[0] - f[0], a[1] - f[1]))) % 8
            if d > 4:
                d -= 8
            assert d != 4
            tot += d
        assert tot % 8 == 0
        return tot // 8

    cnt = 0
    while cnt < 120:
        start = (Fr(1, 2), Fr(1, 8))
        pts = [start]
        for _ in range(rng.randint(4, 30)):
            x, y = pts[-1]
            dx, dy = rng.choice([(1, 0), (-1, 0), (0, 1), (0, -1)])
            nxt = (x + Fr(dx, 16), y + Fr(dy, 16))
            if nxt in grid and free(nxt):
                pts.append(nxt)
        # walk back to the start along the grid, avoiding the fixed squares
        while pts[-1] != start:
            x, y = pts[-1]
            options = []
            for dx, dy in [(1, 0), (-1, 0), (0, 1), (0, -1)]:
                nxt = (x + Fr(dx, 16), y + Fr(dy, 16))
                if nxt in grid and free(nxt):
                    options.append((abs(nxt[0] - start[0]) + abs(nxt[1] - start[1]), rng.random(), nxt))
            options.sort()
            pts.append(options[0][2] if rng.random() < 0.8 else options[-1][2])
            if len(pts) > 400:
                break
        if pts[-1] != start:
            continue
        mover = piecewise(pts)
        n = len(pts) - 1
        path = lambda s, mover=mover: [small(fixed[0]), small(fixed[1]), small(mover(s))]
        assert all(lp.valid(path(Fr(j, 2)), 2) for j in range(2 * n + 1))
        b1 = path_braid(path, 0, n, n)
        b2 = path_braid(path, 0, n, 3 * n)
        assert b1 is not None and b2 is not None
        assert burau(b1, 3) == burau(b2, 3)
        assert exponent(b1) == 2 * (winding(pts, fixed[0]) + winding(pts, fixed[1]))
        cnt += 1
    print("one square walking around two: exponent sum = 2 (winding numbers), refinement (%d walks)  True" % cnt)

    # ---- composition: blocks ----
    assert block_braid(1, 2) == [1, 2] and block_braid(2, 1) == [2, 1]
    assert block_braid(2, 2) == [2, 1, 3, 2]
    geo = {}
    for m1, m2 in [(1, 1), (1, 2), (2, 1), (2, 2), (1, 3), (3, 1), (2, 3), (3, 2)]:
        path = block_path(m1, m2)
        steps = 16 * m1 * m2
        assert all(lp.valid(path(Fr(j, steps)), 2) for j in range(steps + 1))
        assert order(path(0)) == tuple(range(1, m1 + m2 + 1))
        got = path_braid(path, 0, 1, steps)
        geo[(m1, m2)] = got
        # a positive word with one crossing for every pair of strands from different blocks, and the
        # permutation of the blocks: a reduced word of that permutation, so the same braid as
        # block_braid (which may list commuting generators in another order)
        assert got is not None and all(g > 0 for g in got) and len(got) == m1 * m2
        w1 = w2 = tuple(range(m1 + m2))
        for g in got:
            w1 = w1[:g - 1] + (w1[g], w1[g - 1]) + w1[g + 1:]
        for g in block_braid(m1, m2):
            w2 = w2[:g - 1] + (w2[g], w2[g - 1]) + w2[g + 1:]
        assert w1 == w2 == tuple(range(m1, m1 + m2)) + tuple(range(m1))
        assert burau(got, m1 + m2) == burau(block_braid(m1, m2), m1 + m2)
        assert burau(path_braid(path, 0, 1, 3 * steps + 1), m1 + m2) == burau(got, m1 + m2)
    assert geo[(1, 2)] == [1, 2] and geo[(2, 1)] == [2, 1] and geo[(2, 2)] == [2, 1, 3, 2]
    assert geo[(1, 3)] == [1, 2, 3] and geo[(3, 1)] == [3, 2, 1]
    assert path_braid(block_path(1, 2), 0, 1, 2) == [1, 2]
    assert path_braid(block_path(1, 2), 0, 1, 1) is None
    print("the half turn of two rows of squares is the block braid; (1,2): s1 s2, (2,1): s2 s1, (2,2): s2 s1 s3 s2  True")

    braided = [("Z2^(1) semion", ec.zn_anyons(2, 1)), ("Z2^(2) fermion", ec.zn_anyons(2, 2)),
               ("Z3^(2)", ec.zn_anyons(3, 2)), ("Z4^(1)", ec.zn_anyons(4, 1)), ("Z4^(3)", ec.zn_anyons(4, 3)),
               ("D(Z2)", ec.double_zn(2)), ("D(Z3)", ec.double_zn(3))]
    for name, cat in braided:
        assert ec.pentagon(cat) and ec.hexagons(cat), name
        for m1, m2 in [(1, 1), (1, 2), (2, 1), (2, 2)]:
            assert block_holds(cat, m1, m2, geo[(m1, m2)]), (name, m1, m2)
    for name, cat in braided[:4]:
        for m1, m2 in [(1, 3), (3, 1), (2, 3)]:
            assert block_holds(cat, m1, m2, geo[(m1, m2)]), (name, m1, m2)
            assert block_holds(cat, m1, m2, block_braid(m1, m2)), (name, m1, m2)
    print("block braid phase = - R + c(A, B) + R' for braided categories, blocks up to (2, 3)  True")

    # (1, 2) is the first hexagon and (2, 1) the second, for arbitrary data
    seen = set()
    for trial in range(400):
        cat = random_cat([2] if trial % 2 else [3], rng, den=2 if trial % 3 else 3)
        h1, h2 = hexagon_one(cat), hexagon_two(cat)
        assert block_holds(cat, 1, 2, [1, 2]) == h1
        assert block_holds(cat, 2, 1, [2, 1]) == h2
        seen.add((h1, h2))
    # the standard examples that are not braided categories
    for cat in (ec.zn_anyons(3, 1), ec.zn_anyons(5, 3), ec.vec_zn(2, 1)):
        if cat.c is None:
            cat = ec.Cat(cat.G, cat.w, lambda a, b: Fr(0))
        h1, h2 = hexagon_one(cat), hexagon_two(cat)
        assert block_holds(cat, 1, 2, [1, 2]) == h1 and block_holds(cat, 2, 1, [2, 1]) == h2
        seen.add((h1, h2))
    assert (True, True) in seen and (False, False) in seen
    print("(1, 2) holds exactly when hexagon 1 does, (2, 1) exactly when hexagon 2 does (random data; cases seen: %s)  True"
          % sorted(seen))

    # ---- phases of two objects ----
    sem = ec.zn_anyons(2, 1)
    one = (1,)
    assert braid_phase(sem, (one, one), [1]) == (Fr(1, 4), (one, one))
    assert braid_phase(sem, (one, one), [1, 1])[0] == Fr(1, 2)
    assert braid_phase(sem, (one, one), [-1])[0] == Fr(3, 4)
    for name, cat in braided:
        G = cat.G
        for a, b in itertools.product(G.elements, repeat=2):
            assert braid_phase(cat, (a, b), [1]) == (ec.mod1(cat.c(a, b)), (b, a))
            assert braid_phase(cat, (a, b), [-1]) == (ec.mod1(-cat.c(b, a)), (b, a))
            assert braid_phase(cat, (a, b), [1, 1]) == (ec.mutual(cat, a, b), (a, b))
            assert braid_phase(cat, (a, b), [1, -1]) == (Fr(0), (a, b))
            assert braid_phase(cat, (a, a), [1])[0] == ec.spin(cat, a)
        # symmetric exactly when the two half turns have the same phase
        same = all(braid_phase(cat, (a, b), [1])[0] == braid_phase(cat, (a, b), [-1])[0]
                   for a, b in itertools.product(G.elements, repeat=2))
        assert same == ec.symmetric(cat), name
    print("half turn of equal objects = spin, whole turn = mutual braiding; symmetric <=> both half turns agree  True")

    # gauge transformations: the phase of a path changes by terms at its two ends only,
    # so the phases of pure braids are invariant
    pure = [[1, 1], [2, 2], [1, 2, 2, -1], [1, 2, 1, 2, 1, 2], [-2, 1, 1, 2], [2, -1, 2, 2, 1, -2, 1, 1]]
    for name, cat in braided[:5]:
        G = cat.G
        for _ in range(4):
            f = {(a, b): (Fr(0) if G.zero in (a, b) else Fr(rng.randrange(6), 6))
                 for a in G.elements for b in G.elements}
            g = ec.gauge(cat, f)
            for word in itertools.product(G.elements, repeat=3):
                for braid in pure:
                    p1, w1 = braid_phase(cat, word, braid)
                    p2, w2 = braid_phase(g, word, braid)
                    assert w1 == word and w2 == word and p1 == p2, (name, word, braid)
            for a, b in itertools.product(G.elements, repeat=2):
                d = braid_phase(g, (a, b), [1])[0] - braid_phase(cat, (a, b), [1])[0]
                assert ec.mod1(d - (f[(b, a)] - f[(a, b)])) == 0
    z3 = ec.zn_anyons(3, 2)
    f = {(a, b): Fr(0) for a in z3.G.elements for b in z3.G.elements}
    f[((1,), (2,))] = Fr(1, 3)
    g = ec.gauge(z3, f)
    assert braid_phase(z3, ((1,), (2,)), [1])[0] == Fr(2, 3) and braid_phase(g, ((1,), (2,)), [1])[0] == Fr(1, 3)
    assert braid_phase(z3, ((1,), (2,)), [1, 1])[0] == braid_phase(g, ((1,), (2,)), [1, 1])[0] == Fr(1, 3)
    assert braid_phase(z3, ((1,), (1,)), [1])[0] == braid_phase(g, ((1,), (1,)), [1])[0] == Fr(1, 3)
    print("pure braids are gauge invariant; one exchange of a, b changes by f(b, a) - f(a, b)  True")

    # ---- three dimensions ----
    for j in range(0, 33):
        u = Fr(j, 32)
        for i in range(0, 33):
            s = Fr(i, 32)
            assert lp.valid(swap_homotopy(u, s), 3)
        assert swap_homotopy(u, 0) == swap_homotopy(0, 0) and swap_homotopy(u, 1) == swap_homotopy(0, 1)
    for i in range(0, 33):
        s = Fr(i, 32)
        for cube3, cube2 in zip(swap_homotopy(0, s), lp.swap_path(2, s)):
            assert cube3[:2] == cube2 and cube3[2] == (Fr(3, 8), Fr(5, 8))
        mirror = [(q[0], (1 - q[1][1], 1 - q[1][0])) for q in lp.swap_path(2, s)]
        assert [q[:2] for q in swap_homotopy(1, s)] == mirror
    assert path_braid(lambda s: swap_homotopy(0, s), 0, 1, 8) == [1]
    assert path_braid(lambda s: swap_homotopy(1, s), 0, 1, 8) == [-1]
    assert path_braid(lambda s: swap_homotopy(Fr(1, 8), s), 0, 1, 8) == [1]
    assert path_braid(lambda s: swap_homotopy(Fr(7, 8), s), 0, 1, 8) == [-1]
    assert path_braid(lambda s: swap_homotopy(Fr(1, 2), s), 0, 1, 8) is None
    assert path_braid(lambda s: swap_homotopy(Fr(1, 2), s), 0, 1, 7) is None
    print("in three dimensions the counterclockwise and the clockwise half turn are homotopic (33 x 33 grid)  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
