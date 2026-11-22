#!/usr/bin/env python3
"""
Reference checks (pure Python) for symmetric operads presented by binary
generators and quadratic relations, computed by linear algebra, with Koszul
signs for generators of odd degree.

Labelled trees.  A tree is an integer (a leaf) or (g, left, right).  It stands
for the tensor product of its vertex labels in PREORDER, with the inputs
attached to the leaves as labelled.  A generator g has

    spec[g] = (sign, partner, degree),      g(x, y) = sign * partner(y, x)

    symmetric       (+1, g, d)
    antisymmetric   (-1, g, d)
    no symmetry     (+1, g_op, d)   and   g_op -> (+1, g, d)

Rules (all signs follow from "a tree is a tensor product in preorder"):

  swap     g[a, b] = sign_g (-1)^(|a| |b|) partner_g[b, a]
  graft    T o_k X = (-1)^(|X| D) T[k := X],
           D = sum of the degrees of the vertices of T after the leaf k
  action   (T . s): the leaf labelled j gets the label s^(-1)(j)

A tree is CANONICAL (a shuffle tree) if at every vertex the smallest leaf of
the left child is smaller than the smallest leaf of the right child.  The
canonical trees on {1..n} are a basis of the free symmetric operad in arity n.

Relations are linear combinations of trees on the leaves {1, 2, 3}; the images
under S_3 are added.  The ideal in arity n is spanned by all ways to plug
canonical trees X, Y, Z (on disjoint leaf sets, ordered by their smallest
leaves) into a relation and the result into a canonical context.  Then

    dim P(n) = #canonical trees - rank(ideal vectors),

and the canonical trees that are not pivots of the row-reduced ideal are a
basis of P(n).  The trees are listed in the order of trees(), stably sorted by
ORDER[name] if there is one; the first trees are eliminated first.

Checked here:
  Com   1, 1, 1, 1, 1          Lie   1, 1, 2, 6, 24
  Ass   1, 2, 6, 24            Pois  1, 2, 6, 24
  the Poisson operads P_n = H_*(E_n), n >= 2, with a bracket of degree n - 1
  (P_2 is the Gerstenhaber operad): the dimensions by degree are the
  coefficients of prod_{j<k} (1 + j t), the Betti numbers of the configuration
  space of k points in R^n;
  without the Koszul signs the same relations give a different operad;
  bases of normal forms (left-normed brackets and words, products of brackets);
  the operad axioms with Koszul signs in the quotient;
  the presented associative operad against the operad of words;
  morphisms Lie -> Ass, Ass -> Com, Lie -> Pois;
  the identity {ab, cd} = a{b,c}d + ... in Pois;
  equivariance of partial composition; consistency of swap and graft;
  the Betti numbers of the space C_n(k) of little cubes, from the nerve of a
  cover by convex sets, against the dimensions of P_n (C_2(3): 1, 3, 2);
  the generating series of Koszul dual pairs: f_P(-f_Q(-x)) = x.

Run:  python3 reference/presented_reference.py
"""
import itertools
import os
import random
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from operad_reference import perm_compose, word_compose, word_act, betti  # noqa: E402

P = 2147483629  # a prime; large ranks are computed modulo P


# ---- trees ------------------------------------------------------------------

def tmin(t):
    return t if isinstance(t, int) else min(tmin(t[1]), tmin(t[2]))


def leaves(t):
    return [t] if isinstance(t, int) else leaves(t[1]) + leaves(t[2])


def deg(spec, t):
    if isinstance(t, int):
        return 0
    return spec[t[0]][2] + deg(spec, t[1]) + deg(spec, t[2])


def normalize(spec, t):
    """(sign, canonical tree)"""
    if isinstance(t, int):
        return 1, t
    g, a, b = t
    sa, na = normalize(spec, a)
    sb, nb = normalize(spec, b)
    if tmin(na) < tmin(nb):
        return sa * sb, (g, na, nb)
    sign, partner, _ = spec[g]
    koszul = -1 if (deg(spec, na) * deg(spec, nb)) % 2 else 1
    return sa * sb * sign * koszul, (partner, nb, na)


def subst(t, mapping):
    """replace integer leaves by trees (simultaneously, no sign)"""
    if isinstance(t, int):
        return mapping.get(t, t)
    return (t[0], subst(t[1], mapping), subst(t[2], mapping))


def deg_after(spec, t, k):
    """degree of the vertices of t after the leaf k in preorder (None if k is not a leaf)"""
    if isinstance(t, int):
        return 0 if t == k else None
    r = deg_after(spec, t[1], k)
    if r is not None:
        return r + deg(spec, t[2])
    return deg_after(spec, t[2], k)


def graft(spec, t, k, x):
    """(sign, t with x at the leaf k)"""
    sign = -1 if (deg(spec, x) * deg_after(spec, t, k)) % 2 else 1
    return sign, subst(t, {k: x})


def plug3(spec, t, X, Y, Z):
    """t(X, Y, Z) for a tree t on the leaves 1, 2, 3: graft at 1, then 2, then 3"""
    s = 1
    cur = subst(t, {1: -1, 2: -2, 3: -3})
    for k, x in ((-1, X), (-2, Y), (-3, Z)):
        e, cur = graft(spec, cur, k, x)
        s *= e
    return s, cur


def plug2(spec, t, X, Y):
    s = 1
    cur = subst(t, {1: -1, 2: -2})
    for k, x in ((-1, X), (-2, Y)):
        e, cur = graft(spec, cur, k, x)
        s *= e
    return s, cur


_trees = {}


def trees(spec, labels):
    labels = tuple(sorted(labels))
    key = (tuple(spec), labels)
    if key in _trees:
        return _trees[key]
    if len(labels) == 1:
        out = [labels[0]]
    else:
        out = []
        first, rest = labels[0], labels[1:]
        for k in range(0, len(rest)):
            for extra in reversed(list(itertools.combinations(rest, k))):
                left = (first,) + extra
                right = tuple(x for x in rest if x not in extra)
                for g in spec:                      # generators in the order given
                    for a in trees(spec, left):
                        for b in trees(spec, right):
                            out.append((g, a, b))
    _trees[key] = out
    return out


# ---- linear combinations ----------------------------------------------------

def add(d, k, v):
    if v == 0:
        return
    nv = d.get(k, 0) + v
    if nv == 0:
        d.pop(k, None)
    else:
        d[k] = nv


def norm_lin(spec, combo):
    out = {}
    for t, c in combo.items():
        s, nt = normalize(spec, t)
        add(out, nt, s * c)
    return out


def orbit(spec, rel):
    """the images of a relation under the six permutations of its leaves"""
    out = []
    for perm in itertools.permutations((1, 2, 3)):
        m = dict(zip((1, 2, 3), perm))
        image = norm_lin(spec, {subst(t, m): c for t, c in rel.items()})
        if image and image not in out:
            out.append(image)
    return out


def ordered_triples(S):
    """partitions of S into three non-empty parts ordered by their smallest elements"""
    S = sorted(S)
    first, rest = S[0], S[1:]
    for assign in itertools.product((0, 1, 2), repeat=len(rest)):
        parts = [[first], [], []]
        for x, a in zip(rest, assign):
            parts[a].append(x)
        if parts[1] and parts[2] and min(parts[1]) < min(parts[2]):
            yield tuple(parts[0]), tuple(parts[1]), tuple(parts[2])


def ideal_vectors(spec, relations, n):
    labels = tuple(range(1, n + 1))
    seen = set()
    for size in range(3, n + 1):
        for S in itertools.combinations(labels, size):
            mS = S[0]
            ctx_labels = tuple(x for x in labels if x not in S) + (mS,)
            contexts = trees(spec, ctx_labels)
            for A, B, C in ordered_triples(S):
                for X in trees(spec, A):
                    for Y in trees(spec, B):
                        for Z in trees(spec, C):
                            for rel in relations:
                                block = {}
                                for t, c in rel.items():
                                    s, bt = plug3(spec, t, X, Y, Z)
                                    assert normalize(spec, bt) == (1, bt)
                                    add(block, bt, s * c)
                                for ctx in contexts:
                                    vec = {}
                                    for t, c in block.items():
                                        s, vt = graft(spec, ctx, mS, t)
                                        add(vec, vt, s * c)
                                    key = tuple(sorted(vec.items(), key=repr))
                                    if key not in seen:
                                        seen.add(key)
                                        yield vec


def rank_mod_p(rows):
    rank = 0
    pivots = {}
    for r in rows:
        r = {k: v % P for k, v in r.items() if v % P}
        while r:
            lead = min(r)
            if lead in pivots:
                piv = pivots[lead]
                f = r[lead]
                for k, v in piv.items():
                    nv = (r.get(k, 0) - f * v) % P
                    if nv:
                        r[k] = nv
                    else:
                        r.pop(k, None)
            else:
                inv = pow(r[lead], P - 2, P)
                pivots[lead] = {k: (v * inv) % P for k, v in r.items()}
                rank += 1
                break
    return rank


def dimensions(spec, relations, n, weight=None):
    basis = trees(spec, tuple(range(1, n + 1)))
    index = {t: i for i, t in enumerate(basis)}
    w = weight or (lambda t: 0)
    blocks = {}
    for t in basis:
        blocks.setdefault(w(t), []).append(t)
    rows = {}
    for vec in ideal_vectors(spec, relations, n):
        ws = {w(t) for t in vec}
        assert len(ws) == 1, "relations must be homogeneous for the weight"
        rows.setdefault(ws.pop(), []).append({index[t]: c for t, c in vec.items()})
    return {k: len(blocks[k]) - rank_mod_p(rows.get(k, [])) for k in sorted(blocks)}


def total(spec, relations, n):
    return sum(dimensions(spec, relations, n).values())


# ---- exact row reduction: normal forms --------------------------------------

_rref = {}


ORDER = {}   # name -> key function on trees; the sort is stable


def rref(spec, relations, n, name):
    """pivot -> reduced row (dict index -> Fraction); the trees are in the order of trees(),
    stably sorted by ORDER[name] if there is one; the first trees are eliminated first"""
    key = (name, n)
    if key in _rref:
        return _rref[key]
    basis = list(trees(spec, tuple(range(1, n + 1))))
    if name in ORDER:
        basis.sort(key=ORDER[name])
    index = {t: i for i, t in enumerate(basis)}
    pivots = {}
    for vec in ideal_vectors(spec, relations, n):
        r = {index[t]: Fraction(c) for t, c in vec.items()}
        while r:
            lead = min(r)
            if lead in pivots:
                f = r[lead]
                for k, v in pivots[lead].items():
                    add(r, k, -f * v)
            else:
                inv = 1 / r[lead]
                pivots[lead] = {k: v * inv for k, v in r.items()}
                break
    # back substitution: make every pivot column zero in the other rows
    for p in sorted(pivots, reverse=True):
        for q in pivots:
            if q != p and p in pivots[q]:
                f = pivots[q][p]
                for k, v in pivots[p].items():
                    add(pivots[q], k, -f * v)
    _rref[key] = (basis, index, pivots)
    return _rref[key]


def reduce_vec(spec, relations, name, combo, n):
    """normal form of a linear combination of labelled trees on {1..n}"""
    basis, index, pivots = rref(spec, relations, n, name)
    v = {}
    for t, c in norm_lin(spec, combo).items():
        add(v, index[t], Fraction(c))
    for p in sorted(pivots):
        if p in v:
            f = v[p]
            for k, c in pivots[p].items():
                add(v, k, -f * c)
    return {basis[k]: c for k, c in v.items()}


def quotient_basis(spec, relations, name, n):
    basis, index, pivots = rref(spec, relations, n, name)
    return [t for i, t in enumerate(basis) if i not in pivots]


# ---- composition and action in the symmetric operad --------------------------

def act(t, s):
    """(t . s): the leaf labelled j gets the label s^(-1)(j);  s is a tuple (s(1), .., s(n))"""
    inv = {s[j]: j + 1 for j in range(len(s))}
    return subst(t, inv)


def compose(spec, a, i, b):
    """a o_i b on labelled trees: (sign, tree)"""
    k = len(leaves(b))
    a2 = subst(a, {j: (j if j <= i else j + k - 1) for j in leaves(a)})
    b2 = subst(b, {j: j + i - 1 for j in leaves(b)})
    return graft(spec, a2, i, b2)


# ---- the standard operads ---------------------------------------------------

COM = {'c': (1, 'c', 0)}
LIE = {'l': (-1, 'l', 0)}
ASS = {'m': (1, 'mop', 0), 'mop': (1, 'm', 0)}
POIS = {'c': (1, 'c', 0), 'l': (-1, 'l', 0)}


def pn_spec(n):
    """P_n: a commutative product and a bracket of degree n - 1 with sign (-1)^n under the swap"""
    return {'c': (1, 'c', 0), 'l': ((-1) ** n, 'l', n - 1)}


assoc_c = {('c', ('c', 1, 2), 3): 1, ('c', 1, ('c', 2, 3)): -1}
jacobi = {('l', ('l', 1, 2), 3): 1, ('l', ('l', 2, 3), 1): 1, ('l', ('l', 3, 1), 2): 1}
assoc_m = {('m', ('m', 1, 2), 3): 1, ('m', 1, ('m', 2, 3)): -1}
leibniz = {('l', ('c', 1, 2), 3): 1, ('c', 1, ('l', 2, 3)): -1, ('c', ('l', 1, 3), 2): -1}


def pn_relations(spec):
    return orbit(spec, assoc_c) + orbit(spec, jacobi) + orbit(spec, leibniz)


def count(g):
    def f(t):
        if isinstance(t, int):
            return 0
        return (1 if t[0] == g else 0) + f(t[1]) + f(t[2])
    return f


def series_inverse_check(p, q, order):
    """f_P(-f_Q(-x)) = x  with f(x) = sum dim(n) x^n / n!"""
    fact = [1]
    for k in range(1, order + 1):
        fact.append(fact[-1] * k)
    fP = [Fraction(0)] + [Fraction(p[n - 1], fact[n]) for n in range(1, order + 1)]
    g = [Fraction(0)] + [-Fraction(q[n - 1], fact[n]) * (-1) ** n for n in range(1, order + 1)]

    def mul(a, b):
        out = [Fraction(0)] * (order + 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if i + j <= order:
                        out[i + j] += x * y
        return out
    tot = [Fraction(0)] * (order + 1)
    power = [Fraction(1)] + [Fraction(0)] * order
    for n in range(1, order + 1):
        power = mul(power, g)
        tot = [t + fP[n] * x for t, x in zip(tot, power)]
    return tot == [Fraction(0), Fraction(1)] + [Fraction(0)] * (order - 1)


# ---- morphisms ---------------------------------------------------------------

def apply_morphism(qspec, images, t):
    """image of a labelled tree; images[g] is a combination of trees on {1, 2}"""
    if isinstance(t, int):
        return {t: 1}
    ia = apply_morphism(qspec, images, t[1])
    ib = apply_morphism(qspec, images, t[2])
    out = {}
    for h, ch in images[t[0]].items():
        for x, cx in ia.items():
            for y, cy in ib.items():
                s, r = plug2(qspec, h, x, y)
                add(out, r, s * ch * cx * cy)
    return out


def morphism_ok(prels, qspec, qrels, qname, images):
    for rel in prels:
        image = {}
        for t, c in rel.items():
            for r, cr in apply_morphism(qspec, images, t).items():
                add(image, r, c * cr)
        if reduce_vec(qspec, qrels, qname, image, 3):
            return False
    return True


# ---- orders of the trees that give classical normal forms ----------------------

def count_below(top, bottom):
    """number of pairs (a vertex labelled top, a vertex labelled bottom below it)"""
    def cnt(t):
        return 0 if isinstance(t, int) else (1 if t[0] == bottom else 0) + cnt(t[1]) + cnt(t[2])

    def f(t):
        if isinstance(t, int):
            return 0
        here = (cnt(t[1]) + cnt(t[2])) if t[0] == top else 0
        return here + f(t[1]) + f(t[2])
    return f


def ass_planar(t):
    """write mop[a, b] as m[b, a]: a planar tree in m alone"""
    if isinstance(t, int):
        return t
    g, a, b = t
    return ('m', ass_planar(b), ass_planar(a)) if g == 'mop' else ('m', ass_planar(a), ass_planar(b))


def ass_word(t):
    return leaves(ass_planar(t))


def not_left_comb(t):
    def f(u):
        if isinstance(u, int):
            return 0
        return (0 if isinstance(u[2], int) else 1) + f(u[1]) + f(u[2])
    return f(ass_planar(t))


ORDER["Ass"] = lambda t: -not_left_comb(t)                 # normal forms: left-normed words
ORDER["Pois"] = lambda t: -count_below('l', 'c')(t)        # normal forms: products of brackets
ORDER["P2"] = ORDER["Pois"]
ORDER["P3"] = ORDER["Pois"]


# ---- the configuration spaces of little cubes ---------------------------------

def separation_nerve(n, k):
    """The nerve of the cover of C_n(k) by the convex sets V_c, where c chooses, for every
    pair i < j, an axis and which of the two cubes comes first along it.  The facets are
    indexed by the n-tuples of total orders of the cubes (the generic relative positions):
    the facet of (o_1, .., o_n) consists of the choices that hold there."""
    pairs = list(itertools.combinations(range(1, k + 1), 2))
    facets = []
    for orders in itertools.product(itertools.permutations(range(1, k + 1)), repeat=n):
        pos = [{c: r for r, c in enumerate(o)} for o in orders]
        verts = []
        for axes in itertools.product(range(1, n + 1), repeat=len(pairs)):
            verts.append(tuple((ax, 1 if pos[ax - 1][i] < pos[ax - 1][j] else -1)
                               for ax, (i, j) in zip(axes, pairs)))
        facets.append(tuple(sorted(verts)))
    return facets


def facet_nerve(facets):
    """the nerve of the cover of a simplicial complex by its facets: the vertices are the
    facets, and for every vertex v of the complex the facets containing v span a simplex"""
    star = {}
    for i, f in enumerate(facets):
        for v in f:
            star.setdefault(v, []).append(i)
    return sorted(set(tuple(x) for x in star.values()))


def show(t):
    if isinstance(t, int):
        return str(t)
    return "%s[%s,%s]" % (t[0], show(t[1]), show(t[2]))


def main():
    rng = random.Random(7)

    assert [len(trees(LIE, range(1, n + 1))) for n in range(1, 7)] == [1, 1, 3, 15, 105, 945]
    assert [len(trees(ASS, range(1, n + 1))) for n in range(1, 6)] == [1, 2, 12, 120, 1680]
    print("canonical trees: 1, 1, 3, 15, 105, 945 ..........  True")

    # ---- swap and graft are consistent (random trees, odd and even generators)
    spec = {'c': (1, 'c', 0), 'l': (1, 'l', 1), 'k': (-1, 'k', 1), 'm': (1, 'mop', 1), 'mop': (1, 'm', 1)}

    def random_tree(labels):
        labels = list(labels)
        if len(labels) == 1:
            return labels[0]
        rng.shuffle(labels)
        cut = rng.randint(1, len(labels) - 1)
        return (rng.choice(list(spec)), random_tree(labels[:cut]), random_tree(labels[cut:]))

    for _ in range(3000):
        na, nb = rng.randint(1, 5), rng.randint(1, 4)
        T = random_tree(range(1, na + 1))
        X = random_tree(range(10, 10 + nb))
        k = rng.randint(1, na)
        s1, r1 = graft(spec, T, k, X)
        e1, c1 = normalize(spec, r1)
        sT, nT = normalize(spec, T)
        sX, nX = normalize(spec, X)
        s2, r2 = graft(spec, nT, k, nX)
        e2, c2 = normalize(spec, r2)
        assert c1 == c2 and s1 * e1 == sT * sX * s2 * e2, (T, k, X)
    print("swap and graft are consistent (3000 samples) ....  True")

    # ---- equivariance of partial composition in the free operad
    perms = {n: list(itertools.permutations(range(1, n + 1))) for n in (1, 2, 3)}
    checked = 0
    for na in (2, 3):
        for nb in (2, 3):
            for a in trees(spec, range(1, na + 1))[:40]:
                for b in trees(spec, range(1, nb + 1))[:40]:
                    for s in perms[na]:
                        for t in perms[nb]:
                            for i in range(1, na + 1):
                                e1, lhs = compose(spec, act(a, s), i, act(b, t))
                                e2, mid = compose(spec, a, s[i - 1], b)
                                rhs = act(mid, perm_compose(list(s), i, list(t)))
                                n1, c1 = normalize(spec, lhs)
                                n2, c2 = normalize(spec, rhs)
                                assert c1 == c2 and e1 * n1 == e2 * n2
                                checked += 1
    print("equivariance (a.s) o_i (b.t) = (a o_s(i) b).(s o_i t): %d cases  True" % checked)

    # ---- the classical operads
    rc, rl, rm = orbit(COM, assoc_c), orbit(LIE, jacobi), orbit(ASS, assoc_m)
    rp = pn_relations(POIS)
    com = [total(COM, rc, n) for n in range(1, 6)]
    lie = [total(LIE, rl, n) for n in range(1, 6)]
    ass = [total(ASS, rm, n) for n in range(1, 5)]
    pois = [total(POIS, rp, n) for n in range(1, 5)]
    print("Com ", com)
    print("Lie ", lie)
    print("Ass ", ass)
    print("Pois", pois)
    assert com == [1, 1, 1, 1, 1] and lie == [1, 1, 2, 6, 24]
    assert ass == [1, 2, 6, 24] and pois == [1, 2, 6, 24]

    expected = {1: [1], 2: [1, 1], 3: [1, 3, 2], 4: [1, 6, 11, 6], 5: [1, 10, 35, 50, 24]}
    graded = {n: [dimensions(POIS, rp, n, count('l'))[k] for k in range(n)] for n in range(1, 6)}
    print("Pois by number of brackets:", graded)
    assert graded == expected

    # ---- P_n = H_*(E_n) with Koszul signs
    for n in (2, 3):
        sp = pn_spec(n)
        rels = pn_relations(sp)
        got = {k: [dimensions(sp, rels, k, count('l'))[j] for j in range(k)] for k in range(1, 6)}
        print("P_%d by number of brackets:" % n, got)
        assert got == expected
        # the shifted Lie operad alone
        sl = {'l': sp['l']}
        assert [total(sl, orbit(sl, jacobi), k) for k in range(1, 6)] == [1, 1, 2, 6, 24]
    print("P_2 (Gerstenhaber), P_3 and the shifted Lie operads  True")

    # ---- the same relations without Koszul signs give something else
    mock = {'l': (1, 'l', 0)}                      # a symmetric bracket of degree 0
    mock_dims = [total(mock, orbit(mock, jacobi), k) for k in range(1, 6)]
    nosign = {'c': (1, 'c', 0), 'l': (1, 'l', 0)}
    nosign_dims = [total(nosign, pn_relations(nosign), k) for k in range(1, 5)]
    print("symmetric bracket of degree 0 with the Jacobi relation:", mock_dims)
    print("Gerstenhaber relations without Koszul signs:           ", nosign_dims)
    assert mock_dims != [1, 1, 2, 6, 24] and nosign_dims != [1, 2, 6, 24]

    # ---- mutations
    nol = orbit(POIS, assoc_c) + orbit(POIS, jacobi)
    assert total(POIS, nol, 3) == 9
    bad = {('l', ('l', 1, 2), 3): 1, ('l', ('l', 2, 3), 1): 1, ('l', ('l', 3, 1), 2): -1}
    assert total(LIE, orbit(LIE, bad), 3) == 0
    print("mutations (no Leibniz: 9, wrong Jacobi: 0) ......  True")

    # ---- bases of normal forms
    g2 = pn_spec(2)
    rg = pn_relations(g2)
    g3 = pn_spec(3)
    rg3 = pn_relations(g3)

    def basis(spec, rels, name, n):
        return [show(t) for t in quotient_basis(spec, rels, name, n)]

    def nf(spec, rels, name, combo, n):
        return {show(t): int(c) for t, c in reduce_vec(spec, rels, name, combo, n).items()}

    assert basis(COM, rc, "Com", 4) == ['c[c[c[1,2],3],4]']
    assert basis(LIE, rl, "Lie", 3) == ['l[l[1,3],2]', 'l[l[1,2],3]']
    assert sorted(basis(LIE, rl, "Lie", 4)) == sorted(
        'l[l[l[1,%d],%d],%d]' % p for p in itertools.permutations((2, 3, 4)))
    for n in (2, 3, 4):
        b = quotient_basis(ASS, rm, "Ass", n)
        assert all(not_left_comb(t) == 0 for t in b)
        assert sorted(tuple(ass_word(t)) for t in b) == sorted(itertools.permutations(range(1, n + 1)))
    assert basis(POIS, rp, "Pois", 3) == ['c[1,l[2,3]]', 'c[l[1,3],2]', 'l[l[1,3],2]',
                                          'c[c[1,2],3]', 'c[l[1,2],3]', 'l[l[1,2],3]']
    assert basis(g2, rg, "P2", 3) == basis(POIS, rp, "Pois", 3)
    for sp, rels, name in ((POIS, rp, "Pois"), (g2, rg, "P2")):
        assert all(count_below('l', 'c')(t) == 0 for t in quotient_basis(sp, rels, name, 4))
    print("normal forms: left combs, left-normed brackets and words, products of brackets  True")

    assert nf(LIE, rl, "Lie", {('l', 1, ('l', 2, 3)): 1}, 3) == {'l[l[1,2],3]': 1, 'l[l[1,3],2]': -1}
    assert nf(g2, rg, "P2", {('l', 1, ('l', 2, 3)): 1}, 3) == {'l[l[1,2],3]': -1, 'l[l[1,3],2]': -1}
    assert nf(g3, rg3, "P3", {('l', 1, ('l', 2, 3)): 1}, 3) == {'l[l[1,2],3]': 1, 'l[l[1,3],2]': -1}
    for sp, rels, name in ((POIS, rp, "Pois"), (g2, rg, "P2"), (g3, rg3, "P3")):
        assert nf(sp, rels, name, {('l', 1, ('c', 2, 3)): 1}, 3) == {'c[l[1,2],3]': 1, 'c[l[1,3],2]': 1}
        assert nf(sp, rels, name, {('l', ('c', 1, 2), 3): 1}, 3) == {'c[1,l[2,3]]': 1, 'c[l[1,3],2]': 1}
    assert nf(ASS, rm, "Ass", {('m', 1, ('m', 2, 3)): 1}, 3) == {'m[m[1,2],3]': 1}
    assert nf(LIE, rl, "Lie", {('l', ('l', 1, 2), ('l', 3, 4)): 1}, 4) == \
        {'l[l[l[1,2],3],4]': 1, 'l[l[l[1,2],4],3]': -1}
    assert nf(g2, rg, "P2", {('l', ('l', 1, 2), ('l', 3, 4)): 1}, 4) == \
        {'l[l[l[1,2],3],4]': 1, 'l[l[l[1,2],4],3]': 1}
    print("[1,[2,3]] = [[1,2],3] - [[1,3],2] (Lie),  -[[1,2],3] - [[1,3],2] (P_2)   True")

    # ---- the quotient is an operad: unit, sequential and parallel axioms with Koszul signs
    def qcompose(spec, rels, name, u, i, v):
        out = {}
        for a, ca in u.items():
            for b, cb in v.items():
                e, t = compose(spec, a, i, b)
                add(out, t, e * ca * cb)
        n = len(leaves(next(iter(out)))) if out else 0
        return reduce_vec(spec, rels, name, out, n) if out else {}

    for spec_q, rels_q, name_q, top in ((g2, rg, "P2", 4), (g3, rg3, "P3", 4), (ASS, rm, "Ass", 4)):
        el = {n: quotient_basis(spec_q, rels_q, name_q, n) for n in range(1, top + 1)}
        el[1] = [1]
        checked = 0
        for la in range(1, top + 1):
            for lb in range(1, top + 1):
                for lc in range(1, top + 1):
                    if la + lb + lc - 2 > top:
                        continue
                    for a in el[la]:
                        for b in el[lb]:
                            for c in el[lc]:
                                ab = {i: qcompose(spec_q, rels_q, name_q, {a: 1}, i, {b: 1}) for i in range(1, la + 1)}
                                for i in range(1, la + 1):
                                    for j in range(1, lb + 1):
                                        lhs = qcompose(spec_q, rels_q, name_q, ab[i], i + j - 1, {c: 1})
                                        bc = qcompose(spec_q, rels_q, name_q, {b: 1}, j, {c: 1})
                                        rhs = qcompose(spec_q, rels_q, name_q, {a: 1}, i, bc)
                                        assert lhs == rhs, ("sequential", name_q, a, i, b, j, c)
                                        checked += 1
                                    for k in range(i + 1, la + 1):
                                        lhs = qcompose(spec_q, rels_q, name_q, ab[i], k + lb - 1, {c: 1})
                                        ac = qcompose(spec_q, rels_q, name_q, {a: 1}, k, {c: 1})
                                        rhs = qcompose(spec_q, rels_q, name_q, ac, i, {b: 1})
                                        sgn = -1 if (deg(spec_q, b) * deg(spec_q, c)) % 2 else 1
                                        assert lhs == {t: sgn * x for t, x in rhs.items()}, ("parallel", name_q, a, i, b, k, c)
                                        checked += 1
        print("operad axioms with Koszul signs in the quotient %-4s (arity <= %d): %d cases  True" % (name_q, top, checked))

    # ---- the presented associative operad is the operad of words
    checked = 0
    for la in (1, 2, 3):
        for lb in (1, 2, 3):
            if la + lb - 1 > 4:
                continue
            for a in ([1] if la == 1 else quotient_basis(ASS, rm, "Ass", la)):
                for b in ([1] if lb == 1 else quotient_basis(ASS, rm, "Ass", lb)):
                    for i in range(1, la + 1):
                        res = qcompose(ASS, rm, "Ass", {a: 1}, i, {b: 1})
                        assert len(res) == 1 and list(res.values()) == [1]
                        assert ass_word(next(iter(res))) == list(word_compose(tuple(ass_word(a)), i, tuple(ass_word(b))))
                        checked += 1
                    for sgm in itertools.permutations(range(1, la + 1)):
                        res = reduce_vec(ASS, rm, "Ass", {act(a, sgm): 1}, la) if la > 1 else {1: 1}
                        assert len(res) == 1
                        assert ass_word(next(iter(res))) == list(word_act(tuple(ass_word(a)), sgm))
                        checked += 1
    print("presented Ass = operad of words (composition and action): %d cases  True" % checked)

    # ---- homology of the little cubes: Betti numbers against P_n
    assert betti(facet_nerve(separation_nerve(1, 3))) == [6]
    f23 = separation_nerve(2, 3)
    assert len(f23) == 36 and len({v for f in f23 for v in f}) == 60 and all(len(f) == 8 for f in f23)
    b23 = betti(facet_nerve(f23))
    print("C_2(3): Betti numbers of the facet nerve of the separation nerve:", b23)
    assert b23[:3] == [1, 3, 2] and not any(b23[3:])
    for n in (1, 2, 3, 4):
        b = betti(facet_nerve(separation_nerve(n, 2)))
        want = [2] if n == 1 else [1] + [0] * (n - 2) + [1]
        assert b[:len(want)] == want and not any(b[len(want):]), (n, b)
    assert betti(facet_nerve(separation_nerve(1, 4))) == [24]
    print("C_n(2) = S^(n-1), C_1(k) = k! points, C_2(3): 1, 3, 2 = P_2(3) by degree   True")

    # ---- an identity in arity 4:  {ab, cd} = a{b,c}d + a c{b,d} + b{a,c}d + b c{a,d}
    def c3(x, y, z):
        return ('c', ('c', x, y), z)
    ident = {('l', ('c', 1, 2), ('c', 3, 4)): 1,
             c3(1, ('l', 2, 3), 4): -1, c3(1, 3, ('l', 2, 4)): -1,
             c3(2, ('l', 1, 3), 4): -1, c3(2, 3, ('l', 1, 4)): -1}
    assert reduce_vec(POIS, rp, "Pois", ident, 4) == {}
    assert reduce_vec(g2, rg, "P2", ident, 4) == {}     # the product has degree 0: same form in P_2
    assert nf(POIS, rp, "Pois", {('l', ('c', 1, 2), ('c', 3, 4)): 1}, 4) == {
        'c[c[1,l[2,3]],4]': 1, 'c[c[l[1,3],2],4]': 1, 'c[c[1,l[2,4]],3]': 1, 'c[c[l[1,4],2],3]': 1}
    wrong = dict(ident)
    wrong[c3(2, 3, ('l', 1, 4))] = 1
    assert reduce_vec(POIS, rp, "Pois", wrong, 4) != {}
    print("{ab, cd} = a{b,c}d + ac{b,d} + b{a,c}d + bc{a,d}   True")

    # ---- morphisms
    assert morphism_ok(rl, ASS, rm, "Ass", {'l': {('m', 1, 2): 1, ('mop', 1, 2): -1}})       # commutator
    assert not morphism_ok(rl, ASS, rm, "Ass", {'l': {('m', 1, 2): 1, ('mop', 1, 2): 1}})    # anticommutator
    assert morphism_ok(rm, COM, rc, "Com", {'m': {('c', 1, 2): 1}, 'mop': {('c', 1, 2): 1}})
    assert morphism_ok(rl, POIS, rp, "Pois", {'l': {('l', 1, 2): 1}})
    assert morphism_ok(rc, POIS, rp, "Pois", {'c': {('c', 1, 2): 1}})
    assert not morphism_ok(rc, POIS, rp, "Pois", {'c': {('l', 1, 2): 1}})
    # Jordan product in Ass is commutative but not associative
    assert not morphism_ok(rc, ASS, rm, "Ass", {'c': {('m', 1, 2): 1, ('mop', 1, 2): 1}})
    print("morphisms: Lie -> Ass (commutator), Ass -> Com, Lie, Com -> Pois  True")

    assert series_inverse_check([1, 1, 1, 1, 1, 1], [1, 1, 2, 6, 24, 120], 6)      # Com and Lie
    assert series_inverse_check([1, 2, 6, 24, 120, 720], [1, 2, 6, 24, 120, 720], 6)  # Ass is self-dual
    assert not series_inverse_check([1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1], 6)
    print("Koszul series: Com-Lie, Ass-Ass ................  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
