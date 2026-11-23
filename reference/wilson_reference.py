"""
Framed Wilson loops of the Villain Chern-Simons theory (Operadica`Villain`:
VillainFramedWilsonLoop), after Jacobson and Sulejmanpasic, arXiv:2303.06160, section IV.

For an integer 2-cochain b (the Poincare dual of a curve of the dual lattice) the framed
Wilson loop of eq. (33) of that paper is exp(i sum W_b) with

    W_b(a, n) = (1/2) (a cup b + b cup a) - (tau / 2) b cup_1 n        (tau = 2 pi):

two lines of charge 1/2, displaced along the diagonal, and the sheet of n between them.
The Lagrangian is  L_k = (k / 2 tau) a cup da - (k / 2)(a cup n + n cup a) - (k / 2) a cup_1 dn
+ phi cup dn, with the weight exp(2 pi i (sum L_k) / tau).

Statements checked (cochain identities on a periodic lattice, general cochains):

 1. the loop is the response to a background flux:
        L_k(a, n - b / k, phi) - (tau / 2) b cup_1 n - L_k(a, n, phi)
            = W_b(a, n) + (1/2) a cup_1 db - (1 / k) phi cup db.
    For b -> k b: L_k(a, n, phi) + W_kb(a, n) = L_k(a, n - b, phi) - (k tau / 2) b cup_1 n when
    db = 0: the loop of charge k is the shift of the flux n by b, up to the sign
    (-1)^(k sum b cup_1 n).
 2. gauge invariance for closed b:
        W_b(a + d lambda, n) - W_b(a, n) = (1/2) d(lambda cup b + b cup lambda)
                                           - (1/2)(lambda cup db + db cup lambda),
        W_b(a + tau m, n + dm) - W_b(a, n) = tau b cup m - (tau / 2) d(b cup_1 m)
                                             + (tau / 2) db cup_1 m
    (a total derivative, and tau times an integer cochain).  Without the term b cup_1 n the
    second variation is (tau / 2)(m cup b + b cup m): the two lines of charge 1/2 are not
    invariant separately.
 3. deformation of the curve, b -> b + dv, with closed b and n (sums over the torus):
        sum [L_k + W_(b + dv)](a - (tau / k) v, n) - sum [L_k + W_b](a, n)
            = - (tau / 2 k) sum q(v, b) + tau sum v cup n,
    q(v, b) = dv cup v + v cup b + b cup v + v cup_1 db: the cochain of the anomaly of large
    gauge transformations (oddlevel_reference.py).  The shift of a is a change of the
    variable of integration, so <W_(b + dv)> = exp(- 2 pi i sum q(v, b) / 2 k) <W_b>, and
    for the charge c (b -> c b, v -> c v) the phase is c^2 / 2 k times sum q: the spin
    c^2 / 2 k of the line.  For c = k it is (-1)^(k sum q): the obstruction at odd level is
    the spin 1/2 of the line of charge k.
 4. numbers on the three-torus: sum q(v, 0) = sum dv cup v is the self-linking number of the
    boundary of the dual surface of v in the framing of the lattice: 0 for one link, 1 for
    the two links that meet at a corner (a twist).  For the four links around a straight tube
    b, sum q(v, b) = 2 (linking number 1: the phase 1 / k).
 5. at odd level the weight carries the sign z(n) (grassmann_reference.py), and
        z(n) z(n - b) (-1)^(sum b cup_1 n) = z(b),      sum b cup_1 b even:
    the loop of charge k is the fermion, and its value is the Grassmann sign of its world
    line.  z(dv) = (-1)^(sum q(v, 0)): one sign for every twist.

Run:  python3 reference/wilson_reference.py
"""

import itertools
import random
import sys
from fractions import Fraction as Fr

import cubical_reference as cr
from oddlevel_reference import Torus, thooft, add, integrate, torus_anomaly, PLANES
from grassmann_reference import gu_wen, closed_sample
from cech_reference import test_fields


def lin(lat, p, *terms):
    return cr.comb(lat, p, list(terms))


def lagrangian(lat, k, a, n, phi, tau):
    da, dn = cr.delta(a), cr.delta(n)
    return lin(lat, 3, (Fr(k, 2 * tau), cr.cup(a, da)), (Fr(-k, 2), cr.cup(a, n)), (Fr(-k, 2), cr.cup(n, a)),
               (Fr(-k, 2), cr.higher_cup(1, a, dn)), (1, cr.cup(phi, dn)))


def wilson(lat, b, a, n, tau):
    """VillainFramedWilsonLoop[b][VillainField[a, n]]"""
    return lin(lat, 3, (Fr(1, 2), cr.cup(a, b)), (Fr(1, 2), cr.cup(b, a)), (Fr(-tau, 2), cr.higher_cup(1, b, n)))


def check_identities(dims, rng, k, tau):
    lat = Torus(dims)
    a, n, b = lat.random_cochain(1, rng, 4), lat.random_cochain(2, rng), lat.random_cochain(2, rng)
    phi, lam, m = lat.random_cochain(0, rng), lat.random_cochain(0, rng), lat.random_cochain(1, rng)
    db = cr.delta(b)
    # 1
    for c in (1, k):
        shifted = lin(lat, 2, (1, n), (Fr(-c, k), b))
        lhs = lin(lat, 3, (1, lagrangian(lat, k, a, shifted, phi, tau)), (Fr(-c * tau, 2), cr.higher_cup(1, b, n)),
                  (-1, lagrangian(lat, k, a, n, phi, tau)))
        rhs = lin(lat, 3, (c, wilson(lat, b, a, n, tau)), (Fr(c, 2), cr.higher_cup(1, a, db)),
                  (Fr(-c, k), cr.cup(phi, db)))
        assert cr.equal(lat, lhs, rhs, 3)
    # 2
    lhs = lin(lat, 3, (1, wilson(lat, b, add(lat, 1, a, cr.delta(lam)), n, tau)), (-1, wilson(lat, b, a, n, tau)))
    rhs = lin(lat, 3, (Fr(1, 2), cr.delta(add(lat, 2, cr.cup(lam, b), cr.cup(b, lam)))),
              (Fr(-1, 2), cr.cup(lam, db)), (Fr(-1, 2), cr.cup(db, lam)))
    assert cr.equal(lat, lhs, rhs, 3)
    lhs = lin(lat, 3, (1, wilson(lat, b, lin(lat, 1, (1, a), (tau, m)), add(lat, 2, n, cr.delta(m)), tau)),
              (-1, wilson(lat, b, a, n, tau)))
    rhs = lin(lat, 3, (tau, cr.cup(b, m)), (Fr(-tau, 2), cr.delta(cr.higher_cup(1, b, m))),
              (Fr(tau, 2), cr.higher_cup(1, db, m)))
    assert cr.equal(lat, lhs, rhs, 3)
    return True


def deformation(lat, k, a, n, b, v, phi, tau):
    """the two sides of statement 3"""
    a2 = lin(lat, 1, (1, a), (Fr(-tau, k), v))
    b2 = add(lat, 2, b, cr.delta(v))
    lhs = (integrate(lat, lagrangian(lat, k, a2, n, phi, tau)) + integrate(lat, wilson(lat, b2, a2, n, tau))
           - integrate(lat, lagrangian(lat, k, a, n, phi, tau)) - integrate(lat, wilson(lat, b, a, n, tau)))
    rhs = Fr(-tau, 2 * k) * integrate(lat, torus_anomaly(lat, v, b)) + tau * integrate(lat, cr.cup(v, n))
    return lhs, rhs


def check_deformation(dims, rng, k, tau):
    lat = Torus(dims)
    a, phi, v = lat.random_cochain(1, rng, 4), lat.random_cochain(0, rng), lat.random_cochain(1, rng)
    zn = {pl: rng.randint(-2, 2) for pl in PLANES}
    zb = {pl: rng.randint(-2, 2) for pl in PLANES}
    n = add(lat, 2, thooft(lat, zn), cr.delta(lat.random_cochain(1, rng)))
    b = add(lat, 2, thooft(lat, zb), cr.delta(lat.random_cochain(1, rng)))
    lhs, rhs = deformation(lat, k, a, n, b, v, phi, tau)
    assert lhs == rhs, (lhs, rhs)
    return integrate(lat, torus_anomaly(lat, v, b)) % 2


def links(lat, *cells):
    return lat.table(1, {(x, (mu,)): 1 for (x, mu) in cells})


def numbers(dims):
    lat = Torus(dims)
    zero = lat.table(2, {})
    one = links(lat, ((0, 0, 0), 1))
    two = links(lat, ((0, 0, 0), 1), ((1, 0, 0), 2))
    top = tuple(L - 1 for L in dims)
    around = links(lat, ((top[0], top[1], 0), 3), ((0, top[1], 0), 3), ((top[0], 0, 0), 3), ((0, 0, 0), 3))
    tube = thooft(lat, {(1, 2): 1})
    q = lambda v, b: integrate(lat, torus_anomaly(lat, v, b))
    sig = gu_wen(lat)
    out = [q(one, zero), q(two, zero), q(around, zero), q(around, tube),
           integrate(lat, cr.cup(around, tube)), integrate(lat, cr.cup(tube, around))]
    assert [sig(cr.delta(v)) for v in (one, two, around)] == [(-1) ** q(v, zero) for v in (one, two, around)]
    return out


def check_fermion(dims, rng):
    lat = Torus(dims)
    sig = gu_wen(lat)
    for _ in range(6):
        n, b = closed_sample(lat, rng), closed_sample(lat, rng)
        e = integrate(lat, cr.higher_cup(1, b, n))
        assert integrate(lat, cr.higher_cup(1, b, b)) % 2 == 0
        assert sig(n) * sig(lin(lat, 2, (1, n), (-1, b))) * (-1) ** (e % 2) == sig(b)
    return True


def test_numbers():
    """the numbers of Tests/Villain.wlt (3 x 3 x 3)"""
    lat = Torus((3, 3, 3))
    a, n = test_fields(lat)
    m2 = lat.formula(1, lambda x, S: (S[0] * x[0] + x[1] * x[2] + 2 * S[0] * x[2] + x[0] + S[0]) % 2)
    tube = thooft(lat, {(1, 2): 1})
    phi = lat.table(0, {})
    out = []
    for k in (1, 2, 3):
        lhs, rhs = deformation(lat, k, a, n, tube, m2, phi, 7)
        assert lhs == rhs
        out.append(str(rhs))
    return out, integrate(lat, torus_anomaly(lat, m2, tube)), integrate(lat, cr.cup(m2, n))


def main():
    rng = random.Random(20261126)
    for dims in ((3, 3, 3), (3, 4, 5)):
        for (k, tau) in ((1, 3), (2, 5), (3, 7)):
            assert check_identities(dims, rng, k, tau)
    print("the loop as the response to a background flux, gauge invariance for closed b  True")
    odd = []
    for dims in ((3, 3, 3), (3, 3, 4)):
        for (k, tau) in ((1, 3), (2, 5), (3, 7), (4, 5)):
            odd.append(check_deformation(dims, rng, k, tau))
    assert 1 in odd
    print("the deformation of the curve: the phase - sum q(v, b) / 2 k  True")
    for dims in ((3, 3, 3), (4, 4, 4), (3, 4, 5)):
        out = numbers(dims)
        print("  %s  one link, two links, four links, four links around a tube, v cup b, b cup v: %s" % (dims, out))
        assert out[:4] == [0, 1, 0, 2]
    for dims in ((3, 3, 3), (3, 3, 4)):
        assert check_fermion(dims, rng)
    print("self-linking 0 and 1, linking 2, and the loop of charge k as the fermion at odd level  True")
    print("  the numbers of the Wolfram Language tests:", test_numbers())
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
