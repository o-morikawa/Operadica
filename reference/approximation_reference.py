#!/usr/bin/env python3
"""
Reference checks (pure Python, exact arithmetic) for the approximation theorem
C_n X ~ Omega^n Sigma^n X (X connected) at the level of rational Poincare series.

Operad side.  The rational homology of C_n X is the free algebra over
P_n = H_*(E_n) on V = the reduced homology of X:

    F(V) = sum_k P_n(k) (x)_(S_k) V^(x k).

Its dimensions follow from the characters of the symmetric groups on P_n(k):

    dim F(V)_k = (1/k!) sum_s  trace(s on P_n(k)) * trace(s on V^(x k)),

and the trace of a cycle of length l on V^(x l) is the sum over a basis e of V
of (-1)^(|e| (l-1)) t^(l |e|) (the Koszul sign).  The characters are computed
from the presentation of P_n (reference/presented_reference.py).

Loop-space side.  For X a wedge of spheres of dimensions d_i >= 1, Sigma^n X is
a wedge of spheres of dimensions d_i + n.  Rationally (Hilton-Milnor,
Milnor-Moore) the homotopy of Omega Sigma^n X is the free graded Lie algebra L
on generators of degrees d_i + n - 1, and the homology of Omega^n Sigma^n X is
the free graded commutative algebra on L shifted down by n - 1.  (For n = 1 it
is the tensor algebra.)  The dimensions of L follow from
    1 / (1 - sum_i s t^(e_i)) = prod (1 - s^w t^e)^(-l(w,e))  [e even]
                               * prod (1 + s^w t^e)^(l(w,e))   [e odd].

Checked: the characters of Com, Ass, Lie, and their free algebras (the graded
Witt formula for the free Lie algebra); and that the two sides agree, weight
by weight (weight = arity = number of generators), up to arity 4, for n = 1,
2, 3 and several wedges of spheres.

Run:  python3 reference/approximation_reference.py
"""
import itertools
import os
import sys
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from presented_reference import (COM, LIE, ASS, assoc_c, assoc_m, jacobi, orbit, pn_spec,   # noqa: E402
                                 pn_relations, quotient_basis, reduce_vec, act, deg)


def partitions(k, largest=None):
    largest = k if largest is None else largest
    if k == 0:
        yield ()
        return
    for first in range(min(k, largest), 0, -1):
        for rest in partitions(k - first, first):
            yield (first,) + rest


def perm_of_type(lam):
    """a permutation (s(1), .., s(k)) with the cycle lengths lam"""
    s, start = [], 1
    for length in lam:
        s += [start + (j + 1) % length for j in range(length)]
        start += length
    return tuple(s)


def class_size(lam):
    k = sum(lam)
    den = 1
    for length in set(lam):
        m = lam.count(length)
        den *= length ** m * factorial(m)
    return factorial(k) // den


def character(spec, rels, name, k):
    """partition -> {degree: trace of a permutation of that cycle type on the part of that degree}"""
    basis = quotient_basis(spec, rels, name, k)
    out = {}
    for lam in partitions(k):
        s = perm_of_type(lam)
        tr = {}
        for t in basis:
            c = reduce_vec(spec, rels, name, {act(t, s): 1}, k).get(t, 0)
            assert Fr(c).denominator == 1
            tr[deg(spec, t)] = tr.get(deg(spec, t), 0) + int(c)
        out[lam] = {d: c for d, c in tr.items() if c != 0}
    return out


def padd(p, q, f=1):
    out = dict(p)
    for k, v in q.items():
        out[k] = out.get(k, 0) + f * v
        if out[k] == 0:
            del out[k]
    return out


def pmul(p, q):
    out = {}
    for a, x in p.items():
        for b, y in q.items():
            out[a + b] = out.get(a + b, 0) + x * y
    return {k: v for k, v in out.items() if v != 0}


def free_algebra_series(chars, vdegs, kmax):
    """chars[k] = character of P(k); returns arity k -> {degree: dimension}"""
    out = {}
    for k in range(1, kmax + 1):
        total = {}
        for lam, tr in chars[k].items():
            term = dict(tr)
            for length in lam:
                cyc = {}
                for d in vdegs:
                    cyc[length * d] = cyc.get(length * d, 0) + (-1) ** (d * (length - 1))
                term = pmul(term, {a: v for a, v in cyc.items() if v != 0})
            total = padd(total, term, Fr(class_size(lam), factorial(k)))
        assert all(v.denominator == 1 and v > 0 for v in total.values()), total
        out[k] = {d: int(v) for d, v in sorted(total.items())}
    return out


def bmul(p, q, kmax):
    out = {}
    for (w1, e1), x in p.items():
        for (w2, e2), y in q.items():
            if w1 + w2 <= kmax:
                key = (w1 + w2, e1 + e2)
                out[key] = out.get(key, 0) + x * y
    return {k: v for k, v in out.items() if v != 0}


def factor(w, e, mult, odd, kmax):
    """(1 + s^w t^e)^mult if odd, (1 - s^w t^e)^(-mult) otherwise, up to weight kmax"""
    one = {(0, 0): 1}
    if odd:
        base = {(0, 0): 1, (w, e): 1}
    else:
        base = {(j * w, j * e): 1 for j in range(0, kmax // w + 1)}
    out = one
    for _ in range(mult):
        out = bmul(out, base, kmax)
    return out


def free_lie_dimensions(edegs, kmax):
    """(weight, degree) -> dimension of the free graded Lie algebra on generators of degrees edegs"""
    gen = {}
    for e in edegs:
        gen[(1, e)] = gen.get((1, e), 0) + 1
    tensor = {(0, 0): 1}
    power = {(0, 0): 1}
    for _ in range(kmax):
        power = bmul(power, gen, kmax)
        tensor = padd(tensor, power)
    lie = {}
    prod = {(0, 0): 1}
    for w in range(1, kmax + 1):
        for (ww, e), c in sorted(tensor.items()):
            if ww == w:
                m = c - prod.get((w, e), 0)
                assert m >= 0
                if m:
                    lie[(w, e)] = m
        for (ww, e), m in sorted(lie.items()):
            if ww == w:
                prod = bmul(prod, factor(w, e, m, e % 2 == 1, kmax), kmax)
    assert {k: v for k, v in prod.items()} == {k: v for k, v in tensor.items()}
    return lie


def loop_suspension_series(n, vdegs, kmax):
    """arity (weight) k -> {degree: dimension} of H_*(Omega^n Sigma^n X; Q), X a wedge of spheres"""
    lie = free_lie_dimensions([d + n - 1 for d in vdegs], kmax)
    prod = {(0, 0): 1}
    for (w, e), m in sorted(lie.items()):
        shifted = e - (n - 1)
        assert shifted >= 1
        prod = bmul(prod, factor(w, shifted, m, shifted % 2 == 1, kmax), kmax)
    out = {k: {} for k in range(1, kmax + 1)}
    for (w, e), c in sorted(prod.items()):
        if w >= 1:
            out[w][e] = c
    return out


def main():
    # ---- characters
    rc, rl, rm = orbit(COM, assoc_c), orbit(LIE, jacobi), orbit(ASS, assoc_m)
    for k in (2, 3, 4):
        com = character(COM, rc, "Com", k)
        assert all(tr == {0: 1} for tr in com.values())
        ass = character(ASS, rm, "Ass", k)
        assert all(tr == ({0: factorial(k)} if lam == (1,) * k else {}) for lam, tr in ass.items())
    lie3 = character(LIE, rl, "Lie", 3)
    lie4 = character(LIE, rl, "Lie", 4)
    assert [lie3[lam].get(0, 0) for lam in ((1, 1, 1), (2, 1), (3,))] == [2, 0, -1]
    assert [lie4[lam].get(0, 0) for lam in ((1, 1, 1, 1), (2, 1, 1), (2, 2), (3, 1), (4,))] == [6, 0, -2, 0, 0]
    print("characters: Com trivial, Ass regular, Lie(3) = (2, 0, -1), Lie(4) = (6, 0, -2, 0, 0)  True")

    kmax = 4
    # the free algebra over Lie is the free graded Lie algebra, over Com the free graded
    # commutative algebra, over Ass the tensor algebra
    lie = {k: character(LIE, rl, "Lie", k) for k in range(1, kmax + 1)}
    com = {k: character(COM, rc, "Com", k) for k in range(1, kmax + 1)}
    ass = {k: character(ASS, rm, "Ass", k) for k in range(1, kmax + 1)}
    for vdegs in ([2, 2], [1, 1], [1], [2], [1, 2], [1, 1, 2]):
        by_weight = {k: {} for k in range(1, kmax + 1)}
        for (w, e), m in free_lie_dimensions(vdegs, kmax).items():
            by_weight[w][e] = m
        assert free_algebra_series(lie, vdegs, kmax) == by_weight, vdegs
        assert free_algebra_series(ass, vdegs, kmax) == loop_suspension_series(1, vdegs, kmax)
    assert free_algebra_series(com, [2], kmax) == {k: {2 * k: 1} for k in range(1, kmax + 1)}
    assert free_algebra_series(com, [1], kmax) == {1: {1: 1}, 2: {}, 3: {}, 4: {}}
    assert free_lie_dimensions([1], 4) == {(1, 1): 1, (2, 2): 1}
    assert free_lie_dimensions([2], 4) == {(1, 2): 1}
    print("free algebras over Lie, Com, Ass on graded generators: the graded Witt formula,"
          " symmetric and exterior powers, tensor powers  True")
    chars = {}
    for n in (1, 2, 3):
        spec = pn_spec(n)
        rels = pn_relations(spec)
        chars[n] = {k: character(spec, rels, "P%d" % n, k) for k in range(1, kmax + 1)}
    # the Poisson operad is the regular representation; its graded pieces are not
    for k in (2, 3, 4):
        for lam, tr in chars[1][k].items():
            assert sum(tr.values()) == (factorial(k) if lam == (1,) * k else 0)
    print("P_2(3):", {lam: chars[2][3][lam] for lam in ((1, 1, 1), (2, 1), (3,))})
    print("P_1(3):", {lam: chars[1][3][lam] for lam in ((1, 1, 1), (2, 1), (3,))})

    # ---- one sphere: Omega^n S^(n+d)
    for n in (1, 2, 3):
        for d in (1, 2, 3, 4):
            lhs = free_algebra_series(chars[n], [d], kmax)
            assert lhs == loop_suspension_series(n, [d], kmax), (n, d)
            if n >= 2:
                # S(x) if n + d is odd, S(x, [x, x]) if n + d is even
                gens = [(1, d)] + ([(2, 2 * d + n - 1)] if (n + d) % 2 == 0 else [])
                prod = {(0, 0): 1}
                for w, e in gens:
                    prod = bmul(prod, factor(w, e, 1, e % 2 == 1, kmax), kmax)
                expect = {k: {} for k in range(1, kmax + 1)}
                for (w, e), c in prod.items():
                    if w >= 1:
                        expect[w][e] = c
                assert lhs == expect, (n, d, lhs, expect)
    print("one sphere: the free P_n-algebra on a class x of degree d is S(x) or S(x, [x, x]),"
          " the rational homology of Omega^n S^(n+d)  True")

    # ---- wedges of spheres
    cnt = 0
    for n in (1, 2, 3):
        for vdegs in ([1, 1], [1, 2], [2, 2], [2, 3], [1, 1, 1], [1, 2, 3], [2, 2, 2, 2]):
            assert free_algebra_series(chars[n], vdegs, kmax) == loop_suspension_series(n, vdegs, kmax), (n, vdegs)
            cnt += 1
    print("wedges of spheres: the two Poincare series agree up to arity %d (%d cases)  True" % (kmax, cnt))
    for n, vdegs in ((2, [1]), (2, [2]), (3, [1]), (2, [1, 1]), (1, [1, 1]), (3, [1, 2])):
        print("  n = %d, spheres %s:" % (n, vdegs), free_algebra_series(chars[n], vdegs, kmax))
    print("  free Lie algebra on degrees 2, 2 (weights 1..4):", free_lie_dimensions([2, 2], 4))
    print("  free Lie algebra on degrees 1, 1 (weights 1..4):", free_lie_dimensions([1, 1], 4))
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
