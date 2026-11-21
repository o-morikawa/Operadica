#!/usr/bin/env python3
"""
Reference checks (pure Python) for the operad layer of Operadica:

  (1) the symmetric-group conventions: right action, the block permutation
      sigma o_i tau, and the equivariance axiom
          (a.sigma) o_i (b.tau) = (a o_{sigma(i)} b) . (sigma o_i tau)
      tested on the endomorphism operad, the word operad and little cubes;
  (2) little n-cubes: composition, unit, associativity on random rational
      configurations;
  (3) the nerve of the separation cover of C_n(2) (boundary of the
      cross-polytope) has the homology of the sphere S^(n-1).

Run:  python3 reference/operad_reference.py
"""
import itertools
import random
import sys
from fractions import Fraction

# ---------------------------------------------------------------------------
# permutations as tuples (s(1), ..., s(n)), 1-based values
# ---------------------------------------------------------------------------

def perm_mul(s, t):
    """(s t)(j) = s(t(j))"""
    return tuple(s[t[j] - 1] for j in range(len(s)))


def perm_inv(s):
    out = [0] * len(s)
    for j, v in enumerate(s, 1):
        out[v - 1] = j
    return tuple(out)


def perm_compose(s, i, t):
    """
    block permutation  s o_i t  in S_{m+n-1}:
        rho(phi(j))    = psi(s(j))            for j != i
        rho(i - 1 + r) = s(i) + t(r) - 1      for r = 1..n
    with phi(j) = j (j < i), j + n - 1 (j > i)
    and  psi(k) = k (k < s(i)), k + n - 1 (k > s(i)).
    """
    m, n = len(s), len(t)
    si = s[i - 1]
    rho = [0] * (m + n - 1)
    for j in range(1, m + 1):
        if j == i:
            continue
        src = j if j < i else j + n - 1
        k = s[j - 1]
        rho[src - 1] = k if k < si else k + n - 1
    for r in range(1, n + 1):
        rho[i - 1 + r - 1] = si + t[r - 1] - 1
    return tuple(rho)


# ---------------------------------------------------------------------------
# generic checkers
# ---------------------------------------------------------------------------

def check_operad(elements, comp, unit, max_arity, eq=lambda a, b: a == b):
    E = elements
    for n in E:
        for a in E[n]:
            assert eq(comp(unit, 1, a), a), "unit left"
            for i in range(1, n + 1):
                assert eq(comp(a, i, unit), a), "unit right"
    for l in E:
        for m in E:
            for n in E:
                if l + m + n - 2 > max_arity:
                    continue
                for a in E[l]:
                    for b in E[m]:
                        for c in E[n]:
                            for i in range(1, l + 1):
                                for j in range(1, m + 1):
                                    assert eq(comp(comp(a, i, b), i + j - 1, c),
                                              comp(a, i, comp(b, j, c))), "sequential"
                                for k in range(i + 1, l + 1):
                                    assert eq(comp(comp(a, i, b), k + m - 1, c),
                                              comp(comp(a, k, c), i, b)), "parallel"
    return True


def check_equivariance(elements, comp, act, max_arity, eq=lambda a, b: a == b):
    E = elements
    for m in E:
        ident = tuple(range(1, m + 1))
        perms = list(itertools.permutations(range(1, m + 1)))
        for a in E[m]:
            assert eq(act(a, ident), a), "identity acts trivially"
            for s in perms:
                for t in perms:
                    assert eq(act(act(a, s), t), act(a, perm_mul(s, t))), "right action"
    for m in E:
        for n in E:
            if m + n - 1 > max_arity:
                continue
            for a in E[m]:
                for b in E[n]:
                    for s in itertools.permutations(range(1, m + 1)):
                        for t in itertools.permutations(range(1, n + 1)):
                            for i in range(1, m + 1):
                                lhs = comp(act(a, s), i, act(b, t))
                                rhs = act(comp(a, s[i - 1], b), perm_compose(s, i, t))
                                assert eq(lhs, rhs), ("equivariance", m, n, s, t, i)
    return True


# ---------------------------------------------------------------------------
# endomorphism operad of a finite set, (f.s)(x_1..x_n) = f(x_{s^-1(1)}, ...)
# ---------------------------------------------------------------------------

X = (0, 1)


def end_elements(n, rng=None, sample=None):
    keys = list(itertools.product(X, repeat=n))
    allf = [dict(zip(keys, vals)) for vals in itertools.product(X, repeat=len(X) ** n)]
    if sample is not None and len(allf) > sample:
        return rng.sample(allf, sample)
    return allf


def end_compose(f, i, g):
    l = len(next(iter(f)))
    m = len(next(iter(g)))
    return {tup: f[tup[:i - 1] + (g[tup[i - 1:i + m - 1]],) + tup[i + m - 1:]]
            for tup in itertools.product(X, repeat=l + m - 1)}


def end_act(f, s):
    n = len(s)
    sinv = perm_inv(s)
    return {tup: f[tuple(tup[sinv[k] - 1] for k in range(n))]
            for tup in itertools.product(X, repeat=n)}


# ---------------------------------------------------------------------------
# word operad: w = (w_1..w_n) is the monomial x_{w_1} ... x_{w_n};
# (w.s)_k = s^-1(w_k)
# ---------------------------------------------------------------------------

def word_compose(w, i, v):
    m = len(v)
    out = []
    for k in w:
        if k == i:
            out += [x + i - 1 for x in v]
        elif k > i:
            out.append(k + m - 1)
        else:
            out.append(k)
    return tuple(out)


def word_act(w, s):
    sinv = perm_inv(s)
    return tuple(sinv[k - 1] for k in w)


# ---------------------------------------------------------------------------
# little n-cubes: a configuration is a tuple of cubes, a cube is a tuple of
# n intervals (a, b);  (c.s)_j = c_{s(j)}
# ---------------------------------------------------------------------------

def cube_insert(q, r):
    return tuple((a + (b - a) * u, a + (b - a) * v) for (a, b), (u, v) in zip(q, r))


def cubes_compose(c, i, d):
    q = c[i - 1]
    return c[:i - 1] + tuple(cube_insert(q, r) for r in d) + c[i:]


def cubes_act(c, s):
    return tuple(c[s[j] - 1] for j in range(len(c)))


def cubes_valid(c, n):
    for q in c:
        if len(q) != n or any(not (0 <= a < b <= 1) for a, b in q):
            return False
    for q, r in itertools.combinations(c, 2):
        if not any(b <= u or v <= a for (a, b), (u, v) in zip(q, r)):
            return False
    return True


def random_cubes(n, k, rng):
    """binary space partition of the unit cube into k boxes, each then shrunk, randomly labelled"""
    boxes = [tuple((Fraction(0), Fraction(1)) for _ in range(n))]
    while len(boxes) < k:
        q = boxes.pop(rng.randrange(len(boxes)))
        ax = rng.randrange(n)
        a, b = q[ax]
        cut = a + (b - a) * Fraction(rng.randint(1, 4), 5)
        boxes.append(q[:ax] + ((a, cut),) + q[ax + 1:])
        boxes.append(q[:ax] + ((cut, b),) + q[ax + 1:])
    out = []
    for q in boxes:
        shr = []
        for a, b in q:
            w = b - a
            shr.append((a + w * Fraction(rng.randint(0, 2), 10), b - w * Fraction(rng.randint(0, 2), 10)))
        out.append(tuple(shr))
    rng.shuffle(out)
    return tuple(out)


# ---------------------------------------------------------------------------
# simplicial homology (ranks over Q by fraction-free Gaussian elimination)
# ---------------------------------------------------------------------------

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


def betti(facets):
    simplices = set()
    for f in facets:
        f = tuple(sorted(f))
        for k in range(1, len(f) + 1):
            simplices.update(itertools.combinations(f, k))
    top = max(len(s) for s in simplices)
    by_dim = [sorted(s for s in simplices if len(s) == k + 1) for k in range(top)]
    ranks = [0] * (top + 1)
    for k in range(1, top):
        idx = {s: i for i, s in enumerate(by_dim[k - 1])}
        mat = [[0] * len(by_dim[k]) for _ in by_dim[k - 1]]
        for j, s in enumerate(by_dim[k]):
            for p in range(len(s)):
                mat[idx[s[:p] + s[p + 1:]]][j] = (-1) ** p
        ranks[k] = rank(mat)
    return [len(by_dim[k]) - ranks[k] - ranks[k + 1] for k in range(top)]


def cross_polytope_facets(n):
    """facets of the boundary of the n-dimensional cross-polytope: one sign for each axis"""
    return [tuple((ax, sg) for ax, sg in zip(range(1, n + 1), signs))
            for signs in itertools.product((1, -1), repeat=n)]


def main():
    rng = random.Random(11)

    # (1) End operad, sampled in arity 3
    E = {1: end_elements(1), 2: end_elements(2), 3: end_elements(3, rng, 6)}
    print("End: equivariance ..................", check_equivariance(E, end_compose, end_act, 3))
    W = {n: list(itertools.permutations(range(1, n + 1))) for n in (1, 2, 3)}
    print("words: equivariance ................", check_equivariance(W, word_compose, word_act, 4))
    # the block permutation is the word composition of the inverse words
    for m in (1, 2, 3):
        for n in (1, 2, 3):
            for s in itertools.permutations(range(1, m + 1)):
                for t in itertools.permutations(range(1, n + 1)):
                    for i in range(1, m + 1):
                        assert perm_compose(s, i, t) == perm_inv(
                            word_compose(perm_inv(s), i, perm_inv(t))), "block perm vs words"
    print("block permutation = word composition  True")

    # (2) little cubes
    for n in (1, 2, 3):
        C = {k: [random_cubes(n, k, rng) for _ in range(3)] for k in (1, 2, 3)}
        assert all(cubes_valid(c, n) for k in C for c in C[k])
        unit = (tuple((Fraction(0), Fraction(1)) for _ in range(n)),)
        check_operad(C, cubes_compose, unit, 5)
        check_equivariance(C, cubes_compose, cubes_act, 4)
        for k in C:
            for c in C[k]:
                for kk in C:
                    for d in C[kk]:
                        for i in range(1, k + 1):
                            assert cubes_valid(cubes_compose(c, i, d), n), "composite is valid"
    print("little cubes n = 1, 2, 3: axioms ...  True")

    # (3) nerve of the separation cover of C_n(2)
    expected = {1: [2], 2: [1, 1], 3: [1, 0, 1], 4: [1, 0, 0, 1]}
    for n in expected:
        assert betti(cross_polytope_facets(n)) == expected[n], ("betti", n, betti(cross_polytope_facets(n)))
    print("Betti numbers of the nerve, n <= 4 .  True   ", {n: betti(cross_polytope_facets(n)) for n in expected})
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
