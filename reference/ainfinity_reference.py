#!/usr/bin/env python3
"""
Reference checks (pure Python) for graded operads and the A-infinity operad.

Free graded operad.  A tree monomial is the tensor product of its vertex
labels in PREORDER (the order in which the heads appear when the tree is
written as a nested expression).  Partial composition carries the Koszul sign

    s o_i t = (-1)^(|t| D) (graft t at leaf i of s),
    D = sum of the degrees of the vertices of s that come after leaf i.

With this convention the axioms are
    sequential   (a o_i b) o_(i+j-1) c = a o_i (b o_j c)
    parallel     (a o_i b) o_(k+m-1) c = (-1)^(|b||c|) (a o_k c) o_i b ,  i < k.

A derivation d of degree -1 is determined by its values on generators:
    d(h[c1..ck]) = (d h)(c1, .., ck) + sum_j (-1)^(|h|+|c1|+..+|c_(j-1)|) h[c1, .., d c_j, .., ck].

A-infinity operad: generators m_n (n >= 2) of degree n - 2 and
    d m_n = sum_{p+q=n+1, p,q>=2} sum_{i=1}^{p} (-1)^(i + q (p - i)) m_p o_i m_q .

Checked here:
  (1) the graded operad axioms on random trees with generators of both parities;
  (2) which sign rules (-1)^(bilinear form in p, q, i) give d^2 = 0, and that the
      rule above is one of them (it is the rule of Loday-Vallette, Algebraic
      Operads, with p_LV = i - 1, r_LV = p - i: sign (-1)^(p_LV + q r_LV + 1));
  (3) d is a derivation: d(a o_i b) = da o_i b + (-1)^|a| a o_i db;
  (4) the arity-n part is the cellular chain complex of the associahedron K_n:
      number of faces 1, 3, 11, 45, 197; Euler characteristic 1; homology Z in
      degree 0 only (A-infinity is a resolution of As), for n <= 7;
  (5) the graph of K_n (binary trees and single rotations): 5 vertices and 5
      edges for n = 4, 14 and 21 for n = 5, 42 and 84 for n = 6.

Run:  python3 reference/ainfinity_reference.py
"""
import itertools
import random
import sys
from fractions import Fraction

LEAF = 'L'


def add(d, k, v):
    if v == 0:
        return
    nv = d.get(k, 0) + v
    if nv == 0:
        d.pop(k, None)
    else:
        d[k] = nv


def lin(d1, d2, c=1):
    out = dict(d1)
    for k, v in d2.items():
        add(out, k, c * v)
    return out


# ---- trees ------------------------------------------------------------------

def leaf_positions(t, pos=()):
    if t == LEAF:
        return [pos]
    out = []
    for k, c in enumerate(t[1:], 1):
        out += leaf_positions(c, pos + (k,))
    return out


def vertices(t, pos=()):
    """(position, label) of the internal vertices, in preorder"""
    if t == LEAF:
        return []
    out = [(pos, t[0])]
    for k, c in enumerate(t[1:], 1):
        out += vertices(c, pos + (k,))
    return out


def arity(t):
    return len(leaf_positions(t))


def replace_at(t, pos, new):
    if pos == ():
        return new
    k = pos[0]
    return t[:k] + (replace_at(t[k], pos[1:], new),) + t[k + 1:]


def degree(t, deg):
    return sum(deg(lab) for _, lab in vertices(t))


def gcompose(s, i, t, deg):
    """signed partial composition of tree monomials: returns (sign, tree)"""
    lp = leaf_positions(s)[i - 1]
    D = sum(deg(lab) for pos, lab in vertices(s) if pos > lp)
    return (-1) ** (degree(t, deg) * D), replace_at(s, lp, t)


def gcompose_lin(x, i, y, deg):
    out = {}
    for s, cs in x.items():
        for t, ct in y.items():
            sg, tree = gcompose(s, i, t, deg)
            add(out, tree, sg * cs * ct)
    return out


def compositions(n, k):
    if k == 1:
        return [(n,)] if n >= 1 else []
    return [(a,) + r for a in range(1, n) for r in compositions(n - a, k - 1)]


_pt = {}


def planar_trees(gens, n):
    key = (tuple(gens), n)
    if key in _pt:
        return _pt[key]
    if n == 1:
        return [LEAF]
    out = []
    for h, k in gens:
        for comp in compositions(n, k):
            for tup in itertools.product(*[planar_trees(gens, c) for c in comp]):
                out.append((h,) + tup)
    _pt[key] = out
    return out


# ---- (1) graded axioms ------------------------------------------------------

def check_graded_axioms(rng):
    gens = [(('x', 2), 2), (('y', 2), 2), (('z', 3), 3)]
    deg = lambda lab: {'x': 0, 'y': 1, 'z': 1}[lab[0]]
    pool = {n: planar_trees(gens, n) for n in range(1, 5)}
    count = 0
    for _ in range(4000):
        l, m, n = rng.randint(1, 4), rng.randint(1, 4), rng.randint(1, 4)
        if l + m + n - 2 > 7:
            continue
        a, b, c = rng.choice(pool[l]), rng.choice(pool[m]), rng.choice(pool[n])
        i = rng.randint(1, l)
        j = rng.randint(1, m)
        s1, ab = gcompose(a, i, b, deg)
        s2, abc = gcompose(ab, i + j - 1, c, deg)
        t1, bc = gcompose(b, j, c, deg)
        t2, abc2 = gcompose(a, i, bc, deg)
        assert abc == abc2 and s1 * s2 == t1 * t2, "sequential"
        if l >= 2:
            i, k = sorted(rng.sample(range(1, l + 1), 2))
            s1, ab = gcompose(a, i, b, deg)
            s2, abc = gcompose(ab, k + m - 1, c, deg)
            t1, ac = gcompose(a, k, c, deg)
            t2, acb = gcompose(ac, i, b, deg)
            assert abc == acb, "parallel tree"
            assert s1 * s2 == (-1) ** (degree(b, deg) * degree(c, deg)) * t1 * t2, "parallel sign"
        count += 1
    return count


# ---- A-infinity -------------------------------------------------------------

def mdeg(lab):
    return lab[1] - 2


def corolla(n):
    return (('m', n),) + (LEAF,) * n


def make_dgen(eps):
    def dgen(n):
        out = {}
        for p in range(2, n):
            q = n + 1 - p
            for i in range(1, p + 1):
                sg, tree = gcompose(corolla(p), i, corolla(q), mdeg)
                add(out, tree, eps(p, q, i) * sg)
        return out
    return dgen


def make_d(dgen):
    cache = {}

    def d(t):
        """the derivation on a tree monomial"""
        if t == LEAF:
            return {}
        if t in cache:
            return cache[t]
        lab, children = t[0], t[1:]
        out = {}
        # (d h)(c1, .., ck): compose the children from left to right
        acc = dgen(lab[1])
        slot = 1
        for c in children:
            acc = gcompose_lin(acc, slot, {c: 1}, mdeg)
            slot += arity(c)
        out = lin(out, acc)
        # h[c1, .., d c_j, .., ck]
        before = mdeg(lab)
        for j, c in enumerate(children):
            for tc, v in d(c).items():
                add(out, (lab,) + children[:j] + (tc,) + children[j + 1:], (-1) ** before * v)
            before += degree(c, mdeg)
        cache[t] = out
        return out

    def dlin(x):
        out = {}
        for t, v in x.items():
            out = lin(out, d(t), v)
        return out
    return d, dlin


def eps_lv(p, q, i):
    return (-1) ** (i + q * (p - i))


def squares_to_zero(eps, nmax):
    d, dlin = make_d(make_dgen(eps))
    return all(dlin(d(corolla(n))) == {} for n in range(2, nmax + 1))


def search_signs(nmax=6):
    good = []
    for bits in itertools.product((0, 1), repeat=7):
        a, b, c, e, f, g, h = bits
        eps = lambda p, q, i: (-1) ** (a * p * q + b * p * i + c * q * i + e * p + f * q + g * i + h)
        if squares_to_zero(eps, nmax):
            good.append(bits)
    return good


def rank(mat):
    mat = [[Fraction(x) for x in row] for row in mat]
    r = 0
    cols = len(mat[0]) if mat else 0
    for c in range(cols):
        piv = next((i for i in range(r, len(mat)) if mat[i][c] != 0), None)
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        for i in range(r + 1, len(mat)):
            if mat[i][c] != 0:
                f = mat[i][c] / mat[r][c]
                mat[i] = [x - f * y for x, y in zip(mat[i], mat[r])]
        r += 1
    return r


def associahedron(n):
    gens = [(('m', k), k) for k in range(2, n + 1)]
    trees = planar_trees(gens, n)
    by_deg = {}
    for t in trees:
        by_deg.setdefault(degree(t, mdeg), []).append(t)
    return by_deg


def homology(n, d):
    by_deg = associahedron(n)
    top = max(by_deg)
    ranks = {}
    for k in range(1, top + 1):
        rows = {t: r for r, t in enumerate(by_deg[k - 1])}
        mat = [[0] * len(by_deg[k]) for _ in by_deg[k - 1]]
        for col, t in enumerate(by_deg[k]):
            for s, v in d(t).items():
                mat[rows[s]][col] = v
        ranks[k] = rank(mat)
    return [len(by_deg[k]) - ranks.get(k, 0) - ranks.get(k + 1, 0) for k in range(0, top + 1)]


def rotations(t):
    """single associativity moves (ab)c -> a(bc) at any subtree of a binary tree"""
    out = []
    if t == LEAF:
        return out
    lab, x, z = t
    if x != LEAF:
        out.append((lab, x[1], (lab, x[2], z)))
    out += [(lab, x2, z) for x2 in rotations(x)]
    out += [(lab, x, z2) for z2 in rotations(z)]
    return out


def main():
    rng = random.Random(4)
    print("(1) graded operad axioms ................. True  (%d random triples)" % check_graded_axioms(rng))

    good = search_signs(6)
    lv = (1, 0, 1, 0, 0, 1, 0)        # p q + q i + i  =  i + q (p - i)  mod 2
    assert lv in good, "the Loday-Vallette sign rule must square to zero"
    assert squares_to_zero(eps_lv, 8)
    assert not squares_to_zero(lambda p, q, i: 1, 5), "all signs +1 must fail"
    print("(2) sign rules with d^2 = 0 (arity <= 6):  %d of 128; the rule (-1)^(i + q(p-i)) is one  True" % len(good))

    d, dlin = make_d(make_dgen(eps_lv))
    gens = [(('m', k), k) for k in range(2, 6)]
    pool = {n: planar_trees(gens, n) for n in range(1, 5)}
    for _ in range(600):
        l, m = rng.randint(2, 4), rng.randint(2, 4)
        a, b = rng.choice(pool[l]), rng.choice(pool[m])
        i = rng.randint(1, l)
        lhs = dlin(gcompose_lin({a: 1}, i, {b: 1}, mdeg))
        rhs = lin(gcompose_lin(d(a), i, {b: 1}, mdeg),
                  gcompose_lin({a: 1}, i, d(b), mdeg), (-1) ** degree(a, mdeg))
        assert lhs == rhs, "Leibniz"
    for n in range(2, 7):
        for t in planar_trees([(('m', k), k) for k in range(2, n + 1)], n):
            assert dlin(d(t)) == {}, "d^2 on trees"
    print("(3) d is a derivation, d^2 = 0 on trees ... True")

    counts = {}
    for n in range(2, 8):
        by_deg = associahedron(n)
        f = [len(by_deg[k]) for k in sorted(by_deg)]
        counts[n] = sum(f)
        assert sum((-1) ** k * x for k, x in enumerate(f)) == 1, "Euler characteristic"
        h = homology(n, d)
        assert h == [1] + [0] * (len(h) - 1), ("homology", n, h)
    assert [counts[n] for n in range(2, 7)] == [1, 3, 11, 45, 197]
    print("(4) associahedra: faces", [counts[n] for n in range(2, 8)], " homology = Z in degree 0  True")
    print("    f-vectors:", {n: [len(associahedron(n)[k]) for k in sorted(associahedron(n))] for n in range(2, 7)})

    graph = {}
    for n in range(3, 7):
        verts = planar_trees([(('m', 2), 2)], n)
        edges = {frozenset((t, r)) for t in verts for r in rotations(t)}
        graph[n] = (len(verts), len(edges))
    assert graph == {3: (2, 1), 4: (5, 5), 5: (14, 21), 6: (42, 84)}, graph
    print("(5) graphs of K_n (vertices, edges):", graph, " True")
    print("    d m_3 =", d(corolla(3)))
    print("    d m_4 =", d(corolla(4)))
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
