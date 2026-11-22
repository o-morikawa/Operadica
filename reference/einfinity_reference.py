#!/usr/bin/env python3
"""
Reference checks (pure Python, exact arithmetic) for the Barratt-Eccles operad
and its action on the cochains of the hypercubic lattice.

The Barratt-Eccles operad E.  An element of E(r) of degree d is a sequence
(w_0, .., w_d) of words: a word is a permutation of 1..r written as a
sequence, and consecutive words are different.  In degree 0 this is the operad
of words (the associative operad).

  differential   d(w_0, .., w_d) = sum_i (-1)^i (w_0, .., omit w_i, .., w_d)
  action         relabel the letters:  (w . s)_k = s^(-1)(w_k)
  composition    (u_0..u_d) o_i (v_0..v_e) = sum over the lattice paths from
                 (0, 0) to (d, e) of  sign (u_x o_i v_y  along the path),
                 with o_i the substitution of words; the sign is that of the
                 shuffle, + for the path that first runs through u
  filtration     (Berger) s lies in F_n E if the relative order of every pair
                 of letters changes fewer than n times along s; F_n E is an
                 E_n operad

The action on the interval.  N is the chain complex of the interval, with
basis v0, v1 (degree 0) and e (degree 1).  For s in E(r) of degree m,
s.e in N^(x r) is given by the table reduction of Berger and Fresse: cut the
words into rows (a row ends at a letter that comes back later); the terms are
indexed by a table and a position k in its last row; the letters before k get
v0, the letters after k get v1, the letter at k and the letters that end the
earlier rows get e; the sign is that of the sequence (row ends, letter at k).

The action on cubes.  The n-cube is the n-fold tensor product, and
  s.(x_1 x .. x x_n) = sum over 0 = i_0 <= .. <= i_n = d of the product of
  (w_{i_(m-1)}, .., w_{i_m}).x_m, with the Koszul signs.

A term is a list of r rows, one for each tensor factor; a row has an entry for
each direction of the cube: 0 (the factor sits at the lower end), 1 (at the
upper end) or 2 (the factor extends in this direction).  On cochains

  theta_s(a_1, .., a_r)(x; S) = sum_terms c  prod_j a_j(x + shift_j; S_j).

Checked here (the three laws make the cochains an algebra over E):

  the operad axioms of E with Koszul signs, d d = 0, the Leibniz rule
  Betti numbers of F_n E(k) = dimensions of P_n(k):  F_2 E(3): 1, 3, 2;
      F_3 E(3): 1, 0, 3, 0, 2;  F_2 E(4): 1, 6, 11, 6;  F_4 E(3)
  the table reduction is a chain map to the surjection complex
  (L)  d(s.c) = (ds).c + (-1)^|s| s.(dc)                      on cubes, n <= 3
  (C)  (s o_j t).c = (-1)^(|s||t|) (1 x t x 1)(s.c)            on cubes, n <= 3
  (E)  the rows of (s.p).c are the rows p(1), .., p(r) of s.c, with Koszul sign
  arity 2:  theta_{e_i}(a, b) = (-1)^(i(p+q) + i(i-1)/2) a u_i b       (d <= 4)
  the Hirsch formula up to homotopy, with H = theta of (123, 132, 312):
      (a u b) u_1 c - a u (b u_1 c) - (-1)^(q(r-1)) (a u_1 c) u b
         = (-1)^(p+q+r) [ dH(a,b,c) - H(da,b,c) - (-1)^p H(a,db,c) - (-1)^(p+q) H(a,b,dc) ]

Run:  python3 reference/einfinity_reference.py
"""
import itertools
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from operad_reference import word_compose, word_act  # noqa: E402
from presented_reference import rank_mod_p, pn_spec, pn_relations, dimensions, deg as tree_deg  # noqa: E402
import cubical_reference as cr  # noqa: E402
from cubical_reference import Lattice, Cochain, equal, comb, delta  # noqa: E402


def add(d, k, v):
    if v == 0:
        return
    nv = d.get(k, 0) + v
    if nv == 0:
        d.pop(k, None)
    else:
        d[k] = nv


def nondeg(s):
    return all(s[i] != s[i + 1] for i in range(len(s) - 1))


def perm_sign(seq):
    seq = list(seq)
    sgn = 1
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]:
                sgn = -sgn
    return sgn


# ---- the Barratt-Eccles operad ------------------------------------------------

def elements(r, d):
    ws = list(itertools.permutations(range(1, r + 1)))

    def rec(prefix, left):
        if left == 0:
            yield tuple(prefix)
            return
        for w in ws:
            if w != prefix[-1]:
                yield from rec(prefix + [w], left - 1)
    for w in ws:
        yield from rec([w], d)


def be_d(s):
    out = {}
    if len(s) == 1:
        return out
    for i in range(len(s)):
        t = s[:i] + s[i + 1:]
        if nondeg(t):
            add(out, t, (-1) ** i)
    return out


def paths(d, e):
    """lattice paths from (0,0) to (d,e) with the sign of the shuffle"""
    for hs in itertools.combinations(range(d + e), d):
        x = y = inv = 0
        pts = [(0, 0)]
        for step in range(d + e):
            if step in hs:
                x += 1
                inv += y
            else:
                y += 1
            pts.append((x, y))
        yield (-1) ** inv, pts


def be_compose(u, i, v):
    out = {}
    for sgn, pts in paths(len(u) - 1, len(v) - 1):
        t = tuple(word_compose(u[x], i, v[y]) for x, y in pts)
        if nondeg(t):
            add(out, t, sgn)
    return out


def be_act(s, perm):
    return tuple(word_act(w, perm) for w in s)


def lin(f, U):
    out = {}
    for u, cu in U.items():
        for t, c in f(u).items():
            add(out, t, cu * c)
    return out


def lin_compose(U, i, V):
    out = {}
    for u, cu in U.items():
        for v, cv in V.items():
            for t, c in be_compose(u, i, v).items():
                add(out, t, cu * cv * c)
    return out


def level(s):
    """the smallest n with s in F_n E"""
    r = len(s[0])
    best = 0
    pos = [{v: k for k, v in enumerate(w)} for w in s]
    for i in range(1, r + 1):
        for j in range(i + 1, r + 1):
            seq = [p[i] < p[j] for p in pos]
            best = max(best, sum(1 for a, b in zip(seq, seq[1:]) if a != b))
    return best + 1


def filtration(n, r):
    """the non-degenerate elements of F_n E(r), by degree"""
    ws = list(itertools.permutations(range(1, r + 1)))
    out = []
    frontier = [(w,) for w in ws]
    while frontier:
        out.append(frontier)
        frontier = [s + (w,) for s in frontier for w in ws if w != s[-1] and level(s + (w,)) <= n]
    return out


def betti(bases):
    top = len(bases) - 1
    idx = [{s: k for k, s in enumerate(b)} for b in bases]
    ranks = [0] * (top + 2)
    for d in range(1, top + 1):
        ranks[d] = rank_mod_p([{idx[d - 1][t]: c for t, c in be_d(s).items()} for s in bases[d]])
    return [len(bases[d]) - ranks[d] - ranks[d + 1] for d in range(top + 1)]


def e(i):
    """the element of E(2) of degree i: (12, 21, 12, ..)"""
    return tuple((1, 2) if k % 2 == 0 else (2, 1) for k in range(i + 1))


XI = ((1, 2, 3), (1, 3, 2), (3, 1, 2))


# ---- table reduction and surjections --------------------------------------------

def compositions(total, parts):
    if parts == 1:
        if total >= 1:
            yield (total,)
        return
    for first in range(1, total - parts + 2):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def tables(s):
    """the tables of the table reduction: lists of rows"""
    r, m = len(s[0]), len(s) - 1
    for a in compositions(r + m, m + 1):
        removed = []
        rows = []
        ok = True
        for i, w in enumerate(s):
            avail = [x for x in w if x not in removed]
            if len(avail) < a[i] or (i == m and len(avail) != a[i]):
                ok = False
                break
            row = avail[:a[i]]
            rows.append(row)
            removed += row[:-1] if i < m else row
        if ok:
            yield rows


def table_reduction(s):
    out = {}
    for rows in tables(s):
        u = tuple(x for row in rows for x in row)
        if nondeg(u):
            add(out, u, 1)
    return out


def surj_d(u):
    """Berger-Fresse: the occurrences of a value that are not the last one get alternating signs
    in the order of the sequence; the last occurrence gets the opposite of the sign of the
    previous occurrence of the same value; a value that occurs once cannot be removed"""
    out = {}
    last = {v: max(i for i, x in enumerate(u) if x == v) for v in set(u)}
    sign = {}
    prev = {}
    k = 0
    for i, x in enumerate(u):
        if i != last[x]:
            sign[i] = (-1) ** k
            k += 1
            prev[x] = sign[i]
        else:
            sign[i] = -prev[x] if x in prev else None
    for i in range(len(u)):
        if sign[i] is None:
            continue
        t = u[:i] + u[i + 1:]
        if nondeg(t):
            add(out, t, sign[i])
    return out


# ---- the action on the interval and on cubes ----------------------------------------

_edge = {}


def edge_action(s):
    """s . e as {pattern: coeff}; pattern[j-1] in {0, 1, 2}: the factor j is v0, v1 or e"""
    if s in _edge:
        return _edge[s]
    r = len(s[0])
    out = {}
    for rows in tables(s):
        caes = [row[-1] for row in rows[:-1]]
        before = [x for row in rows[:-1] for x in row]
        last = rows[-1]
        for kk in range(len(last)):
            b = before + last[:kk]
            a = last[kk + 1:]
            x = last[kk]
            if len(set(b)) != len(b) or len(set(a)) != len(a) or x in b or x in a:
                continue
            pat = tuple(2 if (j == x or (j in b and j in a)) else (0 if j in b else 1)
                        for j in range(1, r + 1))
            add(out, pat, perm_sign(caes + [x]))
    _edge[s] = out
    return out


def deg(cell):
    return sum(1 for x in cell if x == 2)


def cube_action(s, cell):
    """s . cell for a cell of the n-cube (entries 0, 1, 2 = v0, v1, e): {(row_1, .., row_r): coeff}"""
    r, d, n = len(s[0]), len(s) - 1, len(cell)
    out = {}
    if n == 0:
        return {tuple(() for _ in range(r)): 1} if d == 0 else {}

    def rec(m, i_prev, sign, cols):
        if m == n:
            inv = 0
            for m1 in range(n):
                for j1 in range(r):
                    if cols[m1][j1] != 2:
                        continue
                    for m2 in range(m1 + 1, n):
                        for j2 in range(j1):
                            if cols[m2][j2] == 2:
                                inv += 1
            rows = tuple(tuple(cols[mm][j] for mm in range(n)) for j in range(r))
            add(out, rows, sign * (-1) ** inv)
            return
        deg_before = deg(cell[:m])
        for i in range(i_prev, d + 1):
            if m == n - 1 and i != d:
                continue
            tau = s[i_prev:i + 1]
            sg = (-1) ** ((i - i_prev) * deg_before)
            if cell[m] == 2:
                for pat, c in edge_action(tau).items():
                    rec(m + 1, i, sign * sg * c, cols + [pat])
            elif i == i_prev:
                rec(m + 1, i, sign, cols + [tuple([cell[m]] * r)])
    rec(0, 0, 1, [])
    return out


def lin_action(S, X):
    out = {}
    for s, cs in S.items():
        for x, cx in X.items():
            for k, c in cube_action(s, x).items():
                add(out, k, cs * cx * c)
    return out


def cell_boundary(cell):
    out = {}
    sg = 1
    for m, x in enumerate(cell):
        if x == 2:
            add(out, cell[:m] + (1,) + cell[m + 1:], sg)
            add(out, cell[:m] + (0,) + cell[m + 1:], -sg)
            sg = -sg
    return out


def tensor_boundary(Y):
    out = {}
    for rows, c in Y.items():
        sg = 1
        for j, row in enumerate(rows):
            for f, cf in cell_boundary(row).items():
                add(out, rows[:j] + (f,) + rows[j + 1:], c * sg * cf)
            sg *= (-1) ** deg(row)
    return out


def apply_slot(Y, j, tau):
    """(1 x .. x tau x .. x 1) on the factor j, with the sign for moving tau past the factors before"""
    out = {}
    for rows, c in Y.items():
        sg = (-1) ** ((len(tau) - 1) * sum(deg(row) for row in rows[:j - 1]))
        for sub, cs in cube_action(tau, rows[j - 1]).items():
            add(out, rows[:j - 1] + sub + rows[j:], c * sg * cs)
    return out


def permute_rows(Y, p):
    """rows'_i = rows_{p(i)}, with the Koszul sign"""
    out = {}
    for rows, c in Y.items():
        new = tuple(rows[p[i] - 1] for i in range(len(p)))
        odd = [p[i] for i in range(len(p)) if deg(new[i]) % 2]
        add(out, new, c * perm_sign(odd))
    return out


# ---- the operations on lattice cochains -----------------------------------------------

_top = {}


def top_terms(s, n):
    key = (s, n)
    if key not in _top:
        _top[key] = list(cube_action(s, (2,) * n).items())
    return _top[key]


def theta(lat, S, cochains):
    """the cochain operation of a linear combination S of elements of one degree;
    returns (cochain, degree); the cochain is zero if the degree is out of range"""
    degs = [a.p for a in cochains]
    ds = {len(s) - 1 for s in S}
    assert len(ds) <= 1
    out_deg = sum(degs) - (ds.pop() if ds else 0)
    if not S or out_deg < 0 or out_deg > lat.d:
        return Cochain(lat, min(max(out_deg, 0), lat.d), lambda x, T: 0), out_deg

    def f(x, T):
        n = len(T)
        tot = 0
        for s, cs in S.items():
            for rows, c in top_terms(s, n):
                if any(deg(row) != p for row, p in zip(rows, degs)):
                    continue
                val = c * cs
                for row, a in zip(rows, cochains):
                    sh = [T[m] for m in range(n) if row[m] == 1]
                    dr = tuple(T[m] for m in range(n) if row[m] == 2)
                    val *= a(lat.shift(x, sh), dr)
                    if val == 0:
                        break
                tot += val
        return tot
    return Cochain(lat, out_deg, f), out_deg


def main():
    rng = random.Random(20261122)
    E2 = [s for d in range(0, 3) for s in elements(2, d)]
    E3 = [s for d in range(0, 2) for s in elements(3, d)]
    sample3 = E3[:12] + E3[6:40:5] + [XI, ((1, 2, 3), (3, 2, 1), (2, 1, 3))]

    # ---- the operad
    assert [len(list(elements(3, d))) for d in range(4)] == [6, 30, 150, 750]
    for r in (2, 3):
        for d in range(0, 4):
            for s in elements(r, d):
                assert lin(be_d, be_d(s)) == {}
    cnt = 0
    for u in E2 + E3:
        for v in E2 + E3:
            if len(u[0]) + len(v[0]) - 1 > 4:
                continue
            for i in range(1, len(u[0]) + 1):
                lhs = lin(be_d, be_compose(u, i, v))
                rhs = lin_compose(be_d(u), i, {v: 1})
                for t, c in lin_compose({u: 1}, i, be_d(v)).items():
                    add(rhs, t, c * (-1) ** (len(u) - 1))
                assert lhs == rhs, (u, i, v)
                cnt += 1
    print("d d = 0;  d(u o_i v) = du o_i v + (-1)^|u| u o_i dv: %d cases  True" % cnt)
    cnt = 0
    for a in E2:
        for b in E2:
            for c in E2:
                for i in (1, 2):
                    for j in (1, 2):
                        assert lin_compose(be_compose(a, i, b), i + j - 1, {c: 1}) == \
                            lin_compose({a: 1}, i, be_compose(b, j, c))
                        cnt += 1
                lhs = lin_compose(be_compose(a, 1, b), 3, {c: 1})
                rhs = lin_compose(be_compose(a, 2, c), 1, {b: 1})
                sg = (-1) ** ((len(b) - 1) * (len(c) - 1))
                assert lhs == {t: sg * x for t, x in rhs.items()}
                cnt += 1
    print("sequential and parallel axioms with Koszul signs: %d cases  True" % cnt)
    assert be_compose(e(1), 1, e(0)) == {((1, 2, 3), (3, 1, 2)): 1}
    assert be_compose(e(0), 2, e(1)) == {((1, 2, 3), (1, 3, 2)): 1}
    assert be_compose(e(0), 1, e(1)) == {((1, 2, 3), (2, 1, 3)): 1}
    assert be_compose(e(1), 1, e(1)) == {((1, 2, 3), (3, 1, 2), (3, 2, 1)): 1,
                                          ((1, 2, 3), (2, 1, 3), (3, 2, 1)): -1}
    assert be_d(XI) == {((1, 3, 2), (3, 1, 2)): 1, ((1, 2, 3), (3, 1, 2)): -1, ((1, 2, 3), (1, 3, 2)): 1}

    # ---- the filtration and its homology
    assert [level(e(i)) for i in range(4)] == [1, 2, 3, 4] and level(XI) == 2
    cnt = 0
    for u in E2 + sample3:
        for v in E2 + sample3:
            if len(u[0]) + len(v[0]) - 1 > 4:
                continue
            for i in range(1, len(u[0]) + 1):
                for t in be_compose(u, i, v):
                    assert level(t) <= max(level(u), level(v))
                    cnt += 1
        for t in be_d(u):
            assert level(t) <= level(u)
        for p in itertools.permutations(range(1, len(u[0]) + 1)):
            assert level(be_act(u, p)) == level(u)
    print("F_n E is closed under composition, d and the symmetric groups (%d composites)  True" % cnt)
    expected = {(1, 3): [6], (2, 2): [1, 1], (3, 2): [1, 0, 1], (2, 3): [1, 3, 2, 0],
                (3, 3): [1, 0, 3, 0, 2, 0, 0], (4, 3): [1, 0, 0, 3, 0, 0, 2, 0, 0, 0],
                (2, 4): [1, 6, 11, 6, 0, 0, 0]}
    for (n, k), want in expected.items():
        bases = filtration(n, k)
        got = betti(bases)
        assert got == want, (n, k, got)
        if n >= 2:
            sp = pn_spec(n)
            dims = dimensions(sp, pn_relations(sp), k, lambda t: tree_deg(sp, t))
            assert [dims.get(j, 0) for j in range(len(got))] == got
        print("F_%d E(%d): sizes %s  Betti %s" % (n, k, [len(b) for b in bases], got))
    print("the Betti numbers of F_n E(k) are the dimensions of P_n(k) by degree  True")
    for r, top in ((2, 5), (3, 3)):
        assert betti([list(elements(r, d)) for d in range(top + 1)])[:top] == [1] + [0] * (top - 1)
    print("E(2), E(3) have the homology of a point in low degrees  True")

    # ---- table reduction
    assert table_reduction(e(1)) == {(1, 2, 1): 1} and table_reduction(e(3)) == {(1, 2, 1, 2, 1): 1}
    assert table_reduction(((1, 2, 3), (3, 2, 1))) == {(1, 3, 2, 1): 1, (1, 2, 3, 2): 1}
    assert table_reduction(XI) == {}
    assert surj_d((1, 2, 1)) == {(2, 1): 1, (1, 2): -1}
    cnt = 0
    for r in (2, 3, 4):
        for d in range(0, 4 if r < 4 else 3):
            for s in elements(r, d):
                assert lin(surj_d, table_reduction(s)) == lin(table_reduction, be_d(s))
                cnt += 1
    print("the table reduction is a chain map to the surjection complex: %d cases  True" % cnt)

    # ---- the action on the interval and on cubes
    assert edge_action(e(0)) == {(2, 1): 1, (0, 2): 1}
    assert edge_action(e(1)) == {(2, 2): 1} and edge_action(e(2)) == {}
    assert cube_action(XI, (2, 2)) == {((0, 2), (2, 1), (2, 2)): -1}
    assert len(cube_action(XI, (2, 2, 2))) == 9 and cube_action(XI, (2,)) == {}
    for n in (1, 2, 3):
        cnt = 0
        for r in (2, 3):
            for d in range(0, 4 if r == 2 else 3):
                for s in elements(r, d):
                    for cell in itertools.product((0, 1, 2), repeat=n):
                        lhs = tensor_boundary(cube_action(s, cell))
                        rhs = lin_action(be_d(s), {cell: 1})
                        for k, c in lin_action({s: 1}, cell_boundary(cell)).items():
                            add(rhs, k, c * (-1) ** d)
                        assert lhs == rhs, (s, cell)
                        cnt += 1
        print("(L) chain map on the %d-cube: %d cases  True" % (n, cnt))
    cnt = 0
    for n in (1, 2, 3):
        for sg in E2:
            for tau in E2:
                if len(sg) + len(tau) - 2 > 2:
                    continue
                for j in (1, 2):
                    comp = be_compose(sg, j, tau)
                    eps = (-1) ** ((len(sg) - 1) * (len(tau) - 1))
                    for cell in itertools.product((0, 1, 2), repeat=n):
                        rhs = {k: eps * v for k, v in apply_slot(cube_action(sg, cell), j, tau).items()}
                        assert lin_action(comp, {cell: 1}) == rhs, (sg, j, tau, cell)
                        cnt += 1
    for sg, tau in [(a, b) for a in sample3 for b in E2[:4]] + [(a, b) for a in E2[:4] for b in sample3]:
        for j in range(1, len(sg[0]) + 1):
            comp = be_compose(sg, j, tau)
            eps = (-1) ** ((len(sg) - 1) * (len(tau) - 1))
            for cell in itertools.product((0, 1, 2), repeat=2):
                rhs = {k: eps * v for k, v in apply_slot(cube_action(sg, cell), j, tau).items()}
                assert lin_action(comp, {cell: 1}) == rhs, (sg, j, tau, cell)
                cnt += 1
    for sg, j, tau in ((XI, 1, e(1)), (XI, 3, e(0)), (e(1), 2, XI), (e(0), 1, ((1, 2, 3), (3, 2, 1))),
                       (((1, 2, 3), (3, 2, 1)), 2, e(1)), (e(2), 1, ((1, 2, 3), (2, 1, 3)))):
        comp = be_compose(sg, j, tau)
        eps = (-1) ** ((len(sg) - 1) * (len(tau) - 1))
        for cell in itertools.product((0, 1, 2), repeat=3):
            rhs = {k: eps * v for k, v in apply_slot(cube_action(sg, cell), j, tau).items()}
            assert lin_action(comp, {cell: 1}) == rhs, (sg, j, tau, cell)
            cnt += 1
    print("(C) composition (s o_j t).c = (-1)^(|s||t|) (1 x t x 1)(s.c): %d cases  True" % cnt)
    cnt = 0
    for sg in E2 + E3 + [XI]:
        for p in itertools.permutations(range(1, len(sg[0]) + 1)):
            for n in (1, 2):
                for cell in itertools.product((0, 1, 2), repeat=n):
                    assert cube_action(be_act(sg, p), cell) == permute_rows(cube_action(sg, cell), p)
                    cnt += 1
    for sg in E2 + [XI, ((1, 2, 3), (3, 2, 1)), ((1, 2, 3),)]:
        for p in itertools.permutations(range(1, len(sg[0]) + 1)):
            for cell in itertools.product((0, 1, 2), repeat=3):
                assert cube_action(be_act(sg, p), cell) == permute_rows(cube_action(sg, cell), p)
                cnt += 1
    print("(E) equivariance: %d cases  True" % cnt)

    # ---- on the lattice: arity 2 is the higher cup product
    for d, L in ((2, 3), (3, 2), (4, 2)):
        lat = Lattice(d, L)
        cnt = 0
        for i in range(0, d + 1):
            for p in range(i, d + 1):
                for q in range(i, d + 1):
                    if p + q - i > d:
                        continue
                    a, b = lat.random_cochain(p, rng), lat.random_cochain(q, rng)
                    th, n = theta(lat, {e(i): 1}, [a, b])
                    sgn = (-1) ** (i * (p + q) + i * (i - 1) // 2)
                    assert equal(lat, th, comb(lat, n, [(sgn, cr.higher_cup(i, a, b))]), n), (d, i, p, q)
                    cnt += 1
        print("theta_{e_i}(a, b) = (-1)^(i(p+q) + i(i-1)/2) a u_i b:  d = %d, %d cases  True" % (d, cnt))

    # ---- on the lattice: the three laws for cochains, with random cochains
    lat = Lattice(3, 2)

    def rc(p):
        return lat.random_cochain(p, rng)
    cnt = 0
    for s in E2 + sample3:
        r, m = len(s[0]), len(s) - 1
        for degs in itertools.product(range(0, 3), repeat=r):
            n = sum(degs) - m
            if n < 0 or n + 1 > lat.d:
                continue
            cs = [rc(p) for p in degs]
            lhs = delta(theta(lat, {s: 1}, cs)[0])
            terms = []
            for j in range(r):
                t, k = theta(lat, {s: 1}, cs[:j] + [delta(cs[j])] + cs[j + 1:])
                terms.append(((-1) ** (m + sum(degs[:j])), t))
            if be_d(s):
                terms.append((-(-1) ** m, theta(lat, be_d(s), cs)[0]))
            assert equal(lat, lhs, comb(lat, n + 1, terms), n + 1), ("Leibniz", s, degs)
            cnt += 1
    print("(L) d theta_s(a) = (-1)^m [ sum_j (-1)^(p_1+..+p_(j-1)) theta_s(.., da_j, ..) - theta_ds(a) ]: %d cases  True" % cnt)
    cnt = 0
    for sg in E2:
        for tau in E2:
            ds, dt = len(sg) - 1, len(tau) - 1
            for j in (1, 2):
                comp = be_compose(sg, j, tau)
                for degs in itertools.product(range(0, 3), repeat=3):
                    inner = degs[j - 1:j + 1]
                    if sum(inner) - dt < 0 or sum(degs) - ds - dt < 0 or sum(degs) - ds - dt > lat.d:
                        continue
                    if sum(inner) - dt > lat.d:
                        continue
                    cs = [rc(p) for p in degs]
                    mid, _ = theta(lat, {tau: 1}, cs[j - 1:j + 1])
                    args = cs[:j - 1] + [mid] + cs[j + 1:]
                    rhs, n = theta(lat, {sg: 1}, args)
                    lhs, n2 = theta(lat, comp, cs)
                    sgn = (-1) ** (ds * dt + dt * sum(degs[:j - 1]))
                    assert equal(lat, lhs, comb(lat, n, [(sgn, rhs)]), n), ("composition", sg, j, tau, degs)
                    cnt += 1
    print("(C) theta_{s o_j t}(a) = (-1)^(|s||t| + |t|(p_1+..+p_(j-1))) theta_s(.., theta_t(..), ..): %d cases  True" % cnt)
    cnt = 0
    for s in E2 + sample3:
        r, m = len(s[0]), len(s) - 1
        for p in itertools.permutations(range(1, r + 1)):
            for degs in itertools.product(range(0, 3), repeat=r):
                n = sum(degs) - m
                if n < 0 or n > lat.d:
                    continue
                cs = [rc(q) for q in degs]
                pinv = [p.index(i + 1) + 1 for i in range(r)]
                lhs, _ = theta(lat, {be_act(s, p): 1}, cs)
                rhs, _ = theta(lat, {s: 1}, [cs[pinv[i] - 1] for i in range(r)])
                sgn = perm_sign([p[i] for i in range(r) if degs[i] % 2])
                assert equal(lat, lhs, comb(lat, n, [(sgn, rhs)]), n), ("equivariance", s, p, degs)
                cnt += 1
    print("(E) theta_{s.p}(a_1..a_r) = sign theta_s(a_{p^-1(1)}, ..): %d cases  True" % cnt)

    # ---- the Hirsch formula up to homotopy
    for d, L in ((2, 3), (3, 2)):
        lat = Lattice(d, L)
        cnt = 0
        for p, q, r in itertools.product(range(1, d + 1), repeat=3):
            n = p + q + r - 1
            if n > d:
                continue
            a, b, c = lat.random_cochain(p, rng), lat.random_cochain(q, rng), lat.random_cochain(r, rng)
            h1 = lambda u, v: cr.higher_cup(1, u, v)
            lhs = comb(lat, n, [(1, h1(cr.cup(a, b), c)), (-1, cr.cup(a, h1(b, c))),
                                (-(-1) ** (q * (r - 1)), cr.cup(h1(a, c), b))])
            H = lambda x, y, z: theta(lat, {XI: 1}, [x, y, z])[0]
            terms = [(1, delta(H(a, b, c)))]
            if p < d:
                terms.append((-1, H(delta(a), b, c)))
            if q < d:
                terms.append((-(-1) ** p, H(a, delta(b), c)))
            if r < d:
                terms.append((-(-1) ** (p + q), H(a, b, delta(c))))
            rhs = comb(lat, n, [((-1) ** (p + q + r) * s, t) for s, t in terms])
            assert equal(lat, lhs, rhs, n), (d, p, q, r)
            cnt += 1
        print("Hirsch formula up to the homotopy H = theta_(123,132,312): d = %d, %d degree triples  True" % (d, cnt))
    lat = Lattice(4, 2)
    for p, q, r in ((1, 1, 1), (2, 2, 1), (1, 2, 2), (2, 1, 2), (1, 1, 3)):
        n = p + q + r - 1
        a, b, c = lat.random_cochain(p, rng), lat.random_cochain(q, rng), lat.random_cochain(r, rng)
        h1 = lambda u, v: cr.higher_cup(1, u, v)
        lhs = comb(lat, n, [(1, h1(cr.cup(a, b), c)), (-1, cr.cup(a, h1(b, c))),
                            (-(-1) ** (q * (r - 1)), cr.cup(h1(a, c), b))])
        H = lambda x, y, z: theta(lat, {XI: 1}, [x, y, z])[0]
        rhs = comb(lat, n, [((-1) ** (p + q + r) * s, t) for s, t in (
            (1, delta(H(a, b, c))), (-1, H(delta(a), b, c)), (-(-1) ** p, H(a, delta(b), c)),
            (-(-1) ** (p + q), H(a, b, delta(c))))])
        assert equal(lat, lhs, rhs, n), (4, p, q, r)
    print("Hirsch formula up to homotopy: d = 4, 5 degree triples  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
