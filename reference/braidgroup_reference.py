#!/usr/bin/env python3
"""
Reference checks (pure Python, exact integer arithmetic) for the homology of
the braid groups, the homology of the free E_2-algebra on a point.

The space of k unordered little squares, C_2(k) / S_k, is a K(Br_k, 1) for the
braid group Br_k.  Its cohomology is computed by the complex of Fuks and
Vainshtein: the cells are the compositions (n_1, .., n_s) of k (the points lie
on s vertical lines, n_j of them on the j-th line), in degree k - s, and

    d (n_1, .., n_s) = sum_j (-1)^(j-1) [n_j + n_(j+1) ; n_j] (.., n_j + n_(j+1), ..)

with the Gauss binomial coefficient at q = -1:  [a + b ; a] = 0 if a and b are
odd, and binomial(floor((a+b)/2), floor(a/2)) otherwise.  The homology is that
of the dual complex.

Checked:

  d d = 0 for k <= 10, and the cohomology and the homology fit together
      (universal coefficients)
  integers      H_*(Br_k; Z) for k <= 8:  H_0 = H_1 = Z (k >= 2), the rest is torsion;
                H_1 = Z is the exponent sum: one phase exp(i theta) for the exchange, anyons
  rationals     Betti numbers 1, 1: the free Gerstenhaber algebra on a class x of degree 0
                has x^k and x^(k-2) [x, x] in arity k
  modulo 2      b_j(Br_k; Z_2) = the number of ways to write k as a sum of k - j powers of 2
                (Fuks): the polynomial algebra on classes of weight 2^i and degree 2^i - 1,
                x, Q x, Q Q x, ... with the Kudo-Araki (Dyer-Lashof) operation Q
  Barratt-Eccles   the coinvariants of the stage F_n of the Barratt-Eccles operad compute the
                homology of C_n(k) / S_k:  for k = 2 the real projective space of dimension
                n - 1;  for n = 2 the braid groups again (k = 3, 4), an independent computation;
                for n = 3 and for the whole operad H_1 = Z_2: bosons and fermions

Run:  python3 reference/braidgroup_reference.py
"""

import itertools
import sys
from math import comb

import einfinity_reference as be
from bar_reference import smith_invariants


# ---- homology of a complex of free abelian groups ------------------------------------

def homology(bases, d, upto=None):
    """bases[i]: basis in degree i; d: basis element -> {element of degree i - 1: coefficient}.
    Returns the groups H_0, .., H_upto as lists of cyclic summands (0 for Z, t for Z_t).
    The group in the top degree is only correct if the complex ends there."""
    top = len(bases) - 1
    if upto is None:
        upto = top
    idx = [{x: t for t, x in enumerate(b)} for b in bases]
    inv = {}
    for i in range(1, top + 1):
        if not bases[i] or not bases[i - 1]:
            inv[i] = []
            continue
        rows = []
        for x in bases[i]:
            row = [0] * len(bases[i - 1])
            for y, c in d(x).items():
                row[idx[i - 1][y]] += c
            rows.append(row)
        inv[i] = smith_invariants(rows, len(bases[i - 1]))
    out = []
    for i in range(upto + 1):
        rank_in = len(inv.get(i, []))
        outgoing = inv.get(i + 1, [])
        free = len(bases[i]) - rank_in - len(outgoing)
        out.append([0] * free + sorted(t for t in outgoing if t > 1))
    return out


def betti_mod(groups, p):
    """Betti numbers with coefficients in Z_p, by the universal coefficient theorem"""
    out = []
    for i, g in enumerate(groups):
        b = sum(1 for t in g if t % p == 0)
        if i > 0:
            b += sum(1 for t in groups[i - 1] if t != 0 and t % p == 0)
        out.append(b)
    return out


# ---- the complex of Fuks and Vainshtein ----------------------------------------------

def compositions(k):
    if k == 0:
        yield ()
        return
    for first in range(1, k + 1):
        for rest in compositions(k - first):
            yield (first,) + rest


def gauss(a, b):
    """the Gauss binomial coefficient [a + b ; a] at q = -1"""
    if a % 2 == 1 and b % 2 == 1:
        return 0
    return comb((a + b) // 2, a // 2)


def fuks_d(n):
    """the coboundary: merge two neighbouring lines"""
    out = {}
    for j in range(len(n) - 1):
        c = (-1) ** j * gauss(n[j], n[j + 1])
        if c:
            m = n[:j] + (n[j] + n[j + 1],) + n[j + 2:]
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def fuks_dual(m):
    """the boundary of the dual complex: split one line in two"""
    out = {}
    for j in range(len(m)):
        for a in range(1, m[j]):
            c = (-1) ** j * gauss(a, m[j] - a)
            if c:
                n = m[:j] + (a, m[j] - a) + m[j + 1:]
                out[n] = out.get(n, 0) + c
    return {n: c for n, c in out.items() if c}


def braid_cohomology(k):
    # degree i = k - s; as a chain complex in the degree s - 1 = k - 1 - i
    bases = [[n for n in compositions(k) if len(n) == s] for s in range(1, k + 1)]
    return list(reversed(homology(bases, fuks_d)))


def braid_homology(k):
    bases = [[n for n in compositions(k) if len(n) == k - i] for i in range(k)]
    return homology(bases, fuks_dual)


def binary_partitions(k, parts, largest=None):
    """the number of ways to write k as a sum of the given number of powers of 2"""
    if largest is None:
        largest = 1
        while largest * 2 <= k:
            largest *= 2
    if k == 0:
        return 1 if parts == 0 else 0
    if parts <= 0 or largest < 1:
        return 0
    total = 0
    p = largest
    while p >= 1:
        if p <= k:
            total += binary_partitions(k - p, parts - 1, p)
        p //= 2
    return total


# ---- coinvariants of the Barratt-Eccles operad -----------------------------------------

def normal(s):
    """the representative of the orbit of s whose first word is the identity"""
    return be.be_act(s, s[0])


def orbit_d(s):
    out = {}
    for t, c in be.be_d(s).items():
        be.add(out, normal(t), c)
    return out


def orbit_bases(n, k, top=None):
    """the orbits of S_k on F_n E(k) by degree; n = None is the whole operad, up to the degree top"""
    ws = list(itertools.permutations(range(1, k + 1)))
    ident = tuple(range(1, k + 1))
    out, frontier = [], [(ident,)]
    while frontier and (top is None or len(out) <= top):
        out.append(frontier)
        frontier = [s + (w,) for s in frontier for w in ws
                    if w != s[-1] and (n is None or be.level(s + (w,)) <= n)]
    return out


def orbit_homology(n, k, top=None, upto=None):
    return homology(orbit_bases(n, k, top), orbit_d, upto)


def main():
    # ---- the complex ----
    for k in range(1, 11):
        for n in compositions(k):
            dd = {}
            for m, c in fuks_d(n).items():
                for l, e in fuks_d(m).items():
                    dd[l] = dd.get(l, 0) + c * e
            assert all(v == 0 for v in dd.values()), n
            # the dual complex is the transpose
            for m, c in fuks_d(n).items():
                assert fuks_dual(m).get(n) == c
    print("Fuks-Vainshtein complex: d d = 0 for k <= 10  True")

    table = {k: braid_homology(k) for k in range(1, 9)}
    for k in range(1, 9):
        coh = braid_cohomology(k)
        hom = table[k]
        for i in range(k):
            free = sum(1 for t in hom[i] if t == 0)
            tors = sorted(t for t in (hom[i - 1] if i > 0 else []) if t != 0)
            assert sorted(coh[i]) == [0] * free + tors, (k, i, coh, hom)
    assert table[1] == [[0]]
    assert table[2] == [[0], [0]]
    assert table[3] == [[0], [0], []]
    assert table[4] == [[0], [0], [2], []]
    assert table[5] == [[0], [0], [2], [], []]
    assert table[6] == [[0], [0], [2], [2], [3], []], table[6]
    print("H_*(Br_k; Z), k = 1..8:")
    for k in range(1, 9):
        print("   ", k, table[k])
    for k in range(2, 9):
        assert table[k][0] == [0] and table[k][1] == [0]
        assert all(0 not in g for g in table[k][2:])
    print("H_0 = H_1 = Z and the rest is torsion: rationally the free Gerstenhaber algebra on a point  True")

    for k in range(1, 9):
        assert betti_mod(table[k], 2) == [binary_partitions(k, k - j) for j in range(k)], k
    assert [betti_mod(table[k], 2) for k in (2, 4, 8)] == [[1, 1], [1, 1, 1, 1], [1, 1, 1, 2, 2, 1, 1, 1]]
    print("modulo 2: b_j(Br_k) = number of sums of k - j powers of 2 equal to k (k <= 8)  True")
    assert betti_mod(table[6], 3) == [1, 1, 0, 0, 1, 1] and betti_mod(table[3], 3) == [1, 1, 0]
    print("modulo 3: the first new class is in H_4(Br_6)  True")

    # ---- Barratt-Eccles ----
    rp = {2: [[0], [0]], 3: [[0], [2], []], 4: [[0], [2], [], [0]], 5: [[0], [2], [], [2], []]}
    for n in (2, 3, 4, 5):
        assert orbit_homology(n, 2) == rp[n], (n, orbit_homology(n, 2))
    print("coinvariants of F_n E(2): the homology of the real projective space of dimension n - 1  True")
    assert orbit_homology(2, 3) == table[3] + [[]], orbit_homology(2, 3)
    h24 = orbit_homology(2, 4)
    assert h24[:4] == table[4] and all(g == [] for g in h24[4:]), h24
    print("coinvariants of F_2 E(k), k = 3, 4: the homology of the braid groups again  True")
    h33 = orbit_homology(3, 3)
    assert h33[0] == [0] and h33[1] == [2], h33
    print("coinvariants of F_3 E(3):", h33, " H_1 = Z_2")
    assert orbit_homology(None, 2, top=4, upto=3) == [[0], [2], [], [2]]
    assert orbit_homology(None, 3, top=3, upto=2) == [[0], [2], []]
    assert orbit_homology(None, 4, top=2, upto=1) == [[0], [2]]
    print("coinvariants of E(k): H_1(S_k) = Z_2 for k = 2, 3, 4: bosons and fermions  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
