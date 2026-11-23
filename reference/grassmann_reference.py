"""
The sign of odd-level Chern-Simons theory as a Grassmann integral (Operadica`Villain`:
GuWenGrassmannSign).

oddlevel_reference.py characterises the signs z(n) = +1, -1 on integer 2-cochains n of the
periodic cubic lattice, closed modulo 2, by

    (i)  z(n + dm) = z(n) (-1)^(sum q(m, n)),   q(m, n) = m cup n + n cup m + m cup_1 dn + dm cup m
    (ii) z(n + n') = z(n) z(n') (-1)^(sum n cup_1 n')

and finds 8 of them on the three-torus, labelled by the signs (s12, s13, s23) of the straight
flux tubes.  Here the same functions are given by a local formula, a Grassmann integral of the
Gu-Wen type on the cubic lattice.

A plaquette is a face of two cubes: the front face F_mu of the cube x - e_mu and the back face
B_mu of the cube x, for the plaquette at x normal to mu.  Every plaquette f with n(f) odd
carries two Grassmann variables, one in each of its two cubes.  The cube x contributes the
product of the variables of its odd faces in the order

    F1, B2, F3, B1, F2, B3

(n closed modulo 2: an even number of them, so the products of different cubes commute), and
the pair of a plaquette is integrated with the weight 1 for (the variable later in this
order)(the variable earlier in it): the first of the pair is the one in a slot B1, F2, B3.
sigma(n) is the integral of the product over all cubes: the sign of the permutation that
sorts the variables, cube by cube, into the pairs.

Statements checked:

 1. among the 720 orders of the six faces exactly 12 give a function with (ii): the order
    above, read cyclically, in either direction and from any starting point.  With each of
    them (i) holds as well.  (The pairs (face of n, face of n') of n cup_1 n' on a cube are
    the pairs inside F1, B2, F3 and inside B1, F2, B3: the faces at the corners (1, 0, 1)
    and (0, 1, 0).)
 2. sigma is -1 on every straight flux tube (a closed straight world line of a fermion with
    periodic boundary conditions), for every length; +1 on the boundary of a link (four
    plaquettes), -1 on dm for the two links of oddlevel_reference.py.
 3. sigma satisfies (i) and (ii), and with h = (h1, h2, h3) = (-s23, -s13, -s12)

        z_(s12, s13, s23)(n) = sigma(n) h1^(flux through the plane x1 = 0) h2^(...) h3^(...):

    the sign of the spin structure is the Grassmann integral with the boundary condition
    h_rho (1 periodic, -1 antiperiodic) across the wall x_rho = 0.  This is the
    correspondence of boundary conditions of oddlevel_reference.py (there from the quadratic
    forms of the planes), now from the local formula.

Run:  python3 reference/grassmann_reference.py
"""

import itertools
import random
import sys

import cubical_reference as cr
from oddlevel_reference import Torus, thooft, flux, add, integrate, torus_anomaly, spin_sign, PLANES
from cech_reference import addv, unit, test_fields

COMP = {1: (2, 3), 2: (1, 3), 3: (1, 2)}
ORDER = ("F1", "B2", "F3", "B1", "F2", "B3")


def perm_sign(seq):
    """the sign of the permutation that sorts seq (distinct integers)"""
    pos = {v: i for i, v in enumerate(sorted(seq))}
    p = [pos[v] for v in seq]
    seen = [False] * len(p)
    sign = 1
    for i in range(len(p)):
        if not seen[i]:
            j, ln = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                ln += 1
            if ln % 2 == 0:
                sign = -sign
    return sign


def site_index(y, dims):
    return (y[0] * dims[1] + y[1]) * dims[2] + y[2]


def closed_mod2(lat, n):
    dn = cr.delta(n)
    return all(dn(x, (1, 2, 3)) % 2 == 0 for x in lat.points())


def grassmann(lat, n, order=ORDER, by_order=True):
    """the Grassmann integral.  by_order: the pair of a plaquette is ordered by the position
    of its two slots in the order (later first); otherwise front first"""
    dims = lat.dims
    if not closed_mod2(lat, n):
        return None
    seq = []
    for x in lat.points():
        for pos, slot in enumerate(order):
            mu = int(slot[1])
            y = addv(x, unit(mu), dims) if slot[0] == "F" else x
            if n(y, COMP[mu]) % 2:
                other = ("B" if slot[0] == "F" else "F") + slot[1]
                tag = int(pos < order.index(other)) if by_order else int(slot[0] == "B")
                seq.append(2 * (3 * site_index(y, dims) + mu - 1) + tag)
    return perm_sign(seq)


def gu_wen(lat, hol=(1, 1, 1)):
    """GuWenGrassmannSign[dims, hol]"""
    def z(n):
        g = grassmann(lat, n)
        if g is None:
            return None
        fl = flux(lat, n)
        return g * hol[0] ** (fl[(2, 3)] % 2) * hol[1] ** (fl[(1, 3)] % 2) * hol[2] ** (fl[(1, 2)] % 2)
    return z


def closed_sample(lat, rng):
    z = {pl: rng.randint(0, 1) for pl in PLANES}
    return add(lat, 2, thooft(lat, z), cr.delta(lat.random_cochain(1, rng, 1)))


def check_orders(dims, rng):
    lat = Torus(dims)
    S = [closed_sample(lat, rng) for _ in range(8)]
    pairs = [(i, j) for i in range(8) for j in range(i + 1, 8)][:20]
    cup1 = {pr: integrate(lat, cr.higher_cup(1, S[pr[0]], S[pr[1]])) % 2 for pr in pairs}
    sums = {pr: add(lat, 2, S[pr[0]], S[pr[1]]) for pr in pairs}
    ms = [lat.random_cochain(1, rng, 1) for _ in S]
    qs = [integrate(lat, torus_anomaly(lat, m, s)) % 2 for m, s in zip(ms, S)]
    shifted = [add(lat, 2, s, cr.delta(m)) for m, s in zip(ms, S)]
    good = []
    for order in itertools.permutations(ORDER):
        g = [grassmann(lat, s, order, False) for s in S]
        if all(grassmann(lat, sums[pr], order, False) * g[pr[0]] * g[pr[1]] == (-1) ** cup1[pr] for pr in pairs):
            good.append(order)
            gs = [grassmann(lat, s, order, False) for s in shifted]
            # (i) up to a product of signs of the three fluxes, which dm does not change
            assert all(a * b == (-1) ** q for a, b, q in zip(g, gs, qs))
    cyc = [ORDER[i:] + ORDER[:i] for i in range(6)]
    cyc += [tuple(reversed(c)) for c in cyc]
    assert sorted(good) == sorted(cyc)
    return len(good)


def check_cup1_pairs():
    lat, x0 = Torus((3, 3, 3)), (0, 0, 0)
    faces = {}
    for mu in (1, 2, 3):
        faces["F%d" % mu] = (addv(x0, unit(mu), lat.dims), COMP[mu])
        faces["B%d" % mu] = (x0, COMP[mu])
    found = set()
    for a, fa in faces.items():
        for b, fb in faces.items():
            if cr.higher_cup(1, lat.table(2, {fa: 1}), lat.table(2, {fb: 1}))(x0, (1, 2, 3)) % 2:
                found.add(frozenset((a, b)))
    first, second = ORDER[:3], ORDER[3:]
    want = {frozenset(pr) for tr in (first, second) for pr in itertools.combinations(tr, 2)}
    assert found == want
    return True


def two_links(lat):
    return lat.table(1, {((0, 0, 0), (1,)): 1, ((1, 0, 0), (2,)): 1})


def check_values(dims):
    lat = Torus(dims)
    tubes = [grassmann(lat, thooft(lat, {pl: 1})) for pl in PLANES]
    assert tubes == [-1, -1, -1], (dims, tubes)
    assert grassmann(lat, cr.delta(lat.table(1, {((0, 0, 0), (1,)): 1}))) == 1
    assert grassmann(lat, cr.delta(two_links(lat))) == -1
    assert grassmann(lat, lat.table(2, {((0, 0, 0), (1, 2)): 1})) is None
    return True


def check_spin_structures(dims, rng, count=5):
    lat = Torus(dims)
    for signs in itertools.product((1, -1), repeat=3):
        z, _ = spin_sign(lat, signs)
        g = gu_wen(lat, (-signs[2], -signs[1], -signs[0]))
        for _ in range(count):
            n = add(lat, 2, closed_sample(lat, rng), cr.comb(lat, 2, [(2, lat.random_cochain(2, rng, 1))]))
            assert g(n) == z(n)
    sig = gu_wen(lat)
    for _ in range(count):
        n, n2, m = closed_sample(lat, rng), closed_sample(lat, rng), lat.random_cochain(1, rng)
        assert sig(add(lat, 2, n, cr.delta(m))) == sig(n) * (-1) ** (integrate(lat, torus_anomaly(lat, m, n)) % 2)
        assert sig(add(lat, 2, n, n2)) == sig(n) * sig(n2) * (-1) ** (integrate(lat, cr.higher_cup(1, n, n2)) % 2)
    return True


def test_numbers():
    """the numbers of Tests/Villain.wlt"""
    lat = Torus((3, 3, 3))
    a, n = test_fields(lat)
    m2 = lat.formula(1, lambda x, S: (S[0] * x[0] + x[1] * x[2] + 2 * S[0] * x[2] + x[0] + S[0]) % 2)
    shifted = add(lat, 2, n, cr.delta(m2))
    sig = gu_wen(lat)
    out = [sig(n), sig(shifted), integrate(lat, torus_anomaly(lat, m2, n))]
    table = []
    for signs in itertools.product((1, -1), repeat=3):
        z, _ = spin_sign(lat, signs)
        g = gu_wen(lat, (-signs[2], -signs[1], -signs[0]))
        assert g(n) == z(n) and g(shifted) == z(shifted)
        table.append((g(n), g(shifted)))
    return out, table


def main():
    rng = random.Random(20261125)
    assert check_cup1_pairs()
    for dims in ((3, 3, 3), (3, 4, 4)):
        cnt = check_orders(dims, rng)
        print("  %s  orders of the six faces with (ii): %d of 720" % (dims, cnt))
    print("the order of the variables: the cyclic order F1 B2 F3 B1 F2 B3 and no other  True")
    for dims in ((3, 3, 3), (4, 4, 4), (3, 4, 5), (4, 3, 3), (3, 4, 3), (3, 3, 4), (4, 5, 6)):
        assert check_values(dims)
    print("straight tubes -1, the boundary of a link +1, the two links -1, not closed: no value  True")
    for dims in ((3, 3, 3), (3, 3, 4), (4, 4, 4)):
        assert check_spin_structures(dims, rng)
    print("(i), (ii), and the 8 signs as Grassmann integrals with boundary conditions  True")
    out, table = test_numbers()
    print("  sigma(n), sigma(n + dm2), sum q(m2, n): %s   the 8 structures: %s" % (out, table))
    assert out[0] * out[1] == (-1) ** out[2]
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
