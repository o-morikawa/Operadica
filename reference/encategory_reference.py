#!/usr/bin/env python3
"""
Reference checks (pure Python) for the category layer of Operadica:
pointed E_n-monoidal categories on a finite abelian group G.

Data (phases are rational numbers modulo 1, i.e. exp(2 pi i x)):
    associator  w(a, b, c)
    braiding    c(a, b)

Conventions: abelian 3-cocycles in the sense of Eilenberg-MacLane, in the
form used by Joyal-Street (Braided tensor categories, section 3):

  pentagon   w(b,c,d) - w(a+b,c,d) + w(a,b+c,d) - w(a,b,c+d) + w(a,b,c) = 0
  hexagon 1  w(b,c,a) + c(a,b+c) + w(a,b,c) = c(a,c) + w(b,a,c) + c(a,b)
  hexagon 2  -w(c,a,b) + c(a+b,c) - w(a,b,c) = c(a,c) - w(a,c,b) + c(b,c)

  gauge transformation by a 2-cochain f:
      w' = w + df,   c'(a,b) = c(a,b) + f(b,a) - f(a,b)
      (df)(a,b,c) = f(b,c) - f(a+b,c) + f(a,b+c) - f(a,b)

  invariants:  spin q(a) = c(a,a),  mutual braiding b(a,b) = c(a,b) + c(b,a),
               q(a+b) - q(a) - q(b) = b(a,b)

Checked here:
  (1) the standard families satisfy the axioms, and wrong families do not;
  (2) the axioms are invariant under gauge transformations, and the
      wrong-sign variants of the hexagons are not;
  (3) counts of braided / symmetric structures on Z_N by their quadratic forms;
  (4) Mac Lane coherence: the reassociation phase of a parenthesised product
      is independent of the path, for words of length <= 6, iff the pentagon holds.

Run:  python3 reference/encategory_reference.py
"""
import itertools
import random
import sys
from fractions import Fraction as Fr


def mod1(x):
    return x - (x.numerator // x.denominator)


class Group:
    def __init__(self, orders):
        self.orders = tuple(orders)
        self.elements = list(itertools.product(*[range(n) for n in self.orders]))
        self.zero = tuple(0 for _ in self.orders)

    def add(self, a, b):
        return tuple((x + y) % n for x, y, n in zip(a, b, self.orders))


class Cat:
    def __init__(self, group, w, c=None):
        self.G, self.w, self.c = group, w, c


def pentagon(cat):
    G, w = cat.G, cat.w
    for a, b, c, d in itertools.product(G.elements, repeat=4):
        v = (w(b, c, d) - w(G.add(a, b), c, d) + w(a, G.add(b, c), d)
             - w(a, b, G.add(c, d)) + w(a, b, c))
        if mod1(v) != 0:
            return False
    return True


def hexagons(cat, s1=1, s2=1):
    """s1, s2 = -1 give deliberately wrong variants (for the mutation tests)"""
    G, w, c = cat.G, cat.w, cat.c
    for a, b, d in itertools.product(G.elements, repeat=3):
        h1 = (w(b, d, a) + c(a, G.add(b, d)) + w(a, b, d)) - (c(a, d) + s1 * w(b, a, d) + c(a, b))
        h2 = (-w(d, a, b) + c(G.add(a, b), d) - w(a, b, d)) - (c(a, d) - s2 * w(a, d, b) + c(b, d))
        if mod1(h1) != 0 or mod1(h2) != 0:
            return False
    return True


def symmetric(cat):
    G, c = cat.G, cat.c
    return all(mod1(c(a, b) + c(b, a)) == 0 for a in G.elements for b in G.elements)


def spin(cat, a):
    return mod1(cat.c(a, a))


def mutual(cat, a, b):
    return mod1(cat.c(a, b) + cat.c(b, a))


def gauge(cat, f):
    G = cat.G
    df = lambda a, b, c: f[(b, c)] - f[(G.add(a, b), c)] + f[(a, G.add(b, c))] - f[(a, b)]
    w2 = lambda a, b, c: cat.w(a, b, c) + df(a, b, c)
    c2 = (lambda a, b: cat.c(a, b) + f[(b, a)] - f[(a, b)]) if cat.c else None
    return Cat(G, w2, c2)


# ---- examples ---------------------------------------------------------------

def carry(n, b, c):
    return (b + c - (b + c) % n) // n


def zn_anyons(n, p):
    """Z_N^(p):  w(a,b,c) = p a carry(b,c) / 2,  c(a,b) = p a b / (2N)"""
    G = Group([n])
    return Cat(G,
               lambda a, b, c: Fr(p * a[0] * carry(n, b[0], c[0]), 2),
               lambda a, b: Fr(p * a[0] * b[0], 2 * n))


def vec_zn(n, k):
    """Vec_{Z_N}^k:  w(a,b,c) = k a carry(b,c) / N,  no braiding"""
    G = Group([n])
    return Cat(G, lambda a, b, c: Fr(k * a[0] * carry(n, b[0], c[0]), n))


def double_zn(n):
    """D(Z_N) = Z_N x Z_N, a = (e, m):  w = 0,  c(a,b) = e_a m_b / N"""
    G = Group([n, n])
    return Cat(G, lambda a, b, c: Fr(0), lambda a, b: Fr(a[0] * b[1], n))


# ---- Mac Lane coherence -----------------------------------------------------
# a parenthesised product is a nested pair (x, y); leaves are group elements


def charge(G, t):
    if t[0] != 'm':
        return t[1]
    return G.add(charge(G, t[1]), charge(G, t[2]))


def reassoc_phase(cat, t):
    """phase of the canonical path from t to the right comb"""
    G, w = cat.G, cat.w
    if t[0] != 'm':
        return Fr(0)
    x, z = t[1], t[2]
    if x[0] == 'm':
        ph = w(charge(G, x[1]), charge(G, x[2]), charge(G, z))
        return ph + reassoc_phase(cat, ('m', x[1], ('m', x[2], z)))
    return reassoc_phase(cat, z)


def one_steps(cat, t):
    """all (phase, t') obtained by one rotation m[m[x,y],z] -> m[x,m[y,z]] at any subtree"""
    G, w = cat.G, cat.w
    out = []
    if t[0] != 'm':
        return out
    x, z = t[1], t[2]
    if x[0] == 'm':
        out.append((w(charge(G, x[1]), charge(G, x[2]), charge(G, z)), ('m', x[1], ('m', x[2], z))))
    for ph, x2 in one_steps(cat, x):
        out.append((ph, ('m', x2, z)))
    for ph, z2 in one_steps(cat, z):
        out.append((ph, ('m', x, z2)))
    return out


def binary_trees(leaves):
    if len(leaves) == 1:
        return [leaves[0]]
    out = []
    for k in range(1, len(leaves)):
        for l in binary_trees(leaves[:k]):
            for r in binary_trees(leaves[k:]):
                out.append(('m', l, r))
    return out


def coherent(cat, n, rng=None, samples=None):
    G = cat.G
    words = list(itertools.product(G.elements, repeat=n))
    if samples is not None and len(words) > samples:
        words = rng.sample(words, samples)
    for word in words:
        leaves = [('g', g) for g in word]
        for t in binary_trees(leaves):
            base = reassoc_phase(cat, t)
            for ph, t2 in one_steps(cat, t):
                if mod1(base - ph - reassoc_phase(cat, t2)) != 0:
                    return False
    return True


def main():
    rng = random.Random(5)

    # (1) families
    for n in range(1, 7):
        for p in range(0, 2 * n):
            cat = zn_anyons(n, p)
            ok = pentagon(cat) and hexagons(cat)
            expected = (n % 2 == 0) or (p % 2 == 0) or n == 1
            assert ok == expected, ("zn_anyons", n, p, ok)
            if ok:
                G = cat.G
                for a in G.elements:
                    for b in G.elements:
                        assert mod1(spin(cat, G.add(a, b)) - spin(cat, a) - spin(cat, b) - mutual(cat, a, b)) == 0
                assert symmetric(cat) == (p % n == 0), ("symmetric", n, p)
    for n in range(1, 6):
        for k in range(n):
            assert pentagon(vec_zn(n, k)), ("vec_zn", n, k)
        assert pentagon(double_zn(n)) and hexagons(double_zn(n)), ("double", n)
    tc = double_zn(2)
    e, m, em = (1, 0), (0, 1), (1, 1)
    assert (spin(tc, e), spin(tc, m), spin(tc, em), mutual(tc, e, m)) == (0, 0, Fr(1, 2), Fr(1, 2))
    assert spin(zn_anyons(2, 1), (1,)) == Fr(1, 4) and spin(zn_anyons(2, 2), (1,)) == Fr(1, 2)
    print("(1) families satisfy the axioms ..........  True")

    # a non-trivial 3-cocycle of order > 2 admits no bilinear braiding of this form
    bad = Cat(Group([3]), vec_zn(3, 1).w, lambda a, b: Fr(a[0] * b[0], 3))
    assert pentagon(bad) and not hexagons(bad)

    # (2) gauge invariance and mutation tests
    caught1 = caught2 = False
    for (n, p) in ((2, 1), (4, 1), (4, 3), (3, 2), (6, 5)):
        cat = zn_anyons(n, p)
        G = cat.G
        for _ in range(4):
            f = {(a, b): Fr(rng.randint(0, 11), 12) for a in G.elements for b in G.elements}
            g = gauge(cat, f)
            assert pentagon(g) and hexagons(g), ("gauge invariance", n, p)
            for a in G.elements:
                assert spin(g, a) == spin(cat, a)
                for b in G.elements:
                    assert mutual(g, a, b) == mutual(cat, a, b)
            caught1 = caught1 or not hexagons(g, s1=-1)
            caught2 = caught2 or not hexagons(g, s2=-1)
    assert caught1 and caught2, "wrong-sign hexagons must fail on gauge-transformed data"
    print("(2) gauge invariance, wrong signs caught .  True")

    # (3) counting by quadratic forms
    for n in range(1, 9):
        valid = [p for p in range(2 * n) if (n % 2 == 0 or p % 2 == 0)]   # for odd N only even p
        forms = {tuple(spin(zn_anyons(n, p), (a,)) for a in range(n)) for p in valid}
        sym = {tuple(spin(zn_anyons(n, p), (a,)) for a in range(n)) for p in valid if p % n == 0}
        assert len(forms) == (2 * n if n % 2 == 0 else n), ("braided count", n, len(forms))
        assert len(sym) == (2 if n % 2 == 0 else 1), ("symmetric count", n, len(sym))
    print("(3) braided: N gcd(2,N), symmetric: gcd(2,N)  True")

    # (4) Mac Lane coherence
    for cat, label in ((zn_anyons(2, 1), "semion"), (vec_zn(3, 1), "Vec_Z3^1"), (vec_zn(4, 3), "Vec_Z4^3")):
        for n in (3, 4, 5, 6):
            assert coherent(cat, n, rng, samples=60), ("coherence", label, n)
    # a function that is not a 3-cocycle fails already at length 4
    table = {k: Fr(rng.randint(0, 2), 3) for k in itertools.product(range(3), repeat=3)}
    notcocycle = Cat(Group([3]), lambda a, b, c: table[(a[0], b[0], c[0])])
    assert not pentagon(notcocycle)
    assert coherent(notcocycle, 3) and not coherent(notcocycle, 4)
    print("(4) coherence up to length 6 ..............  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
