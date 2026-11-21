#!/usr/bin/env python3
"""
Reference checks (pure Python) for the lattice gauge theory layer of Operadica.
Uses the cochain operations of cubical_reference.py (same directory).

Identities, all exact identities of cochains (physics convention for cup_1):

 (G1) Pontryagin square under a 1-form gauge transformation, P(B) = BuB - B u1 dB:
        P(B + dl) - P(B) = d[ 2 l u B + l u dl - B u1 dl ]
                           + 2 l u dB + dB u1 dl - dl u1 dB

 (G2) Pontryagin square under a shift by N times an integer cochain c:
        P(B + N c) - P(B) = 2N c u B + N^2 (c u c - c u1 dc)
                            - N d(B u1 c) + N (dB u1 c - c u1 dB)

 (G3) a u da - da u a = d(a u1 da) - da u1 da          (a a 1-cochain)

 (G4) modified Villain Chern-Simons Lagrangian of arXiv:2303.06160, eq. (17),
      written with a = 2 pi alpha and phi = pi phi':
        L(alpha, n, phi') = k [ alpha u d alpha - alpha u n - n u alpha - alpha u1 dn ] + phi' u dn
      0-form gauge transformation  alpha -> alpha + dl,  phi' -> phi' - 2 k l :
        L' - L = k d[ l u d alpha - 2 l u n + dl u1 n ]
      large gauge transformation  alpha -> alpha + m,  n -> n + dm :
        L' - L = - k d(m u alpha) - k ( m u n + n u m + m u1 dn + dm u m )

 (G5) 't Hooft flux z on the four-torus:  sum of P(B) = 2 Pf(z), so that
        (p / 2N) sum P(B) = b(z12, z34) - b(z13, z24) + b(z14, z23)   (mod 1)
      with b(x, y) = p x y / N the mutual braiding of the Z_N^(p) anyons.

Run:  python3 reference/gauge_reference.py
"""
import importlib.util
import itertools
import os
import random
import sys
from fractions import Fraction as Fr

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("cubical_reference", os.path.join(_here, "cubical_reference.py"))
ref = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ref)

delta, cup, comb, equal = ref.delta, ref.cup, ref.comb, ref.equal


def cup1(a, b):
    return ref.higher_cup(1, a, b)


def pont(lat, b):
    return comb(lat, 4, [(1, cup(b, b)), (-1, cup1(b, delta(b)))])


def main():
    rng = random.Random(2026)

    # ---- (G1), (G2) in four dimensions --------------------------------------
    lat = ref.Lattice(4, 2)
    B = lat.random_cochain(2, rng)
    l = lat.random_cochain(1, rng)
    c = lat.random_cochain(2, rng)
    dB, dl, dc = delta(B), delta(l), delta(c)

    Bp = comb(lat, 2, [(1, B), (1, dl)])
    lhs = comb(lat, 4, [(1, pont(lat, Bp)), (-1, pont(lat, B))])
    prim = comb(lat, 3, [(2, cup(l, B)), (1, cup(l, dl)), (-1, cup1(B, dl))])
    rhs = comb(lat, 4, [(1, delta(prim)), (2, cup(l, dB)), (1, cup1(dB, dl)), (-1, cup1(dl, dB))])
    assert equal(lat, lhs, rhs, 4), "G1"

    for N in (2, 3, 4):
        Bn = comb(lat, 2, [(1, B), (N, c)])
        lhs = comb(lat, 4, [(1, pont(lat, Bn)), (-1, pont(lat, B))])
        rhs = comb(lat, 4, [
            (2 * N, cup(c, B)),
            (N * N, cup(c, c)), (-N * N, cup1(c, dc)),
            (-N, delta(cup1(B, c))),
            (N, cup1(dB, c)), (-N, cup1(c, dB)),
        ])
        assert equal(lat, lhs, rhs, 4), ("G2", N)
    print("(G1), (G2) Pontryagin square shifts ......  True")

    # ---- (G3), (G4) in three dimensions -------------------------------------
    lat = ref.Lattice(3, 3)
    a = lat.random_cochain(1, rng)
    da = delta(a)
    lhs = comb(lat, 3, [(1, cup(a, da)), (-1, cup(da, a))])
    rhs = comb(lat, 3, [(1, delta(cup1(a, da))), (-1, cup1(da, da))])
    assert equal(lat, lhs, rhs, 3), "G3"

    def lagr(k, al, n, ph):
        dn = delta(n)
        return comb(lat, 3, [
            (k, cup(al, delta(al))), (-k, cup(al, n)), (-k, cup(n, al)), (-k, cup1(al, dn)),
            (1, cup(ph, dn)),
        ])

    for k in (1, 2, 3):
        al = lat.random_cochain(1, rng)
        n = lat.random_cochain(2, rng)
        ph = lat.random_cochain(0, rng)
        lam = lat.random_cochain(0, rng)
        m = lat.random_cochain(1, rng)
        dlam, dm, dn, dal = delta(lam), delta(m), delta(n), delta(al)

        al2 = comb(lat, 1, [(1, al), (1, dlam)])
        ph2 = comb(lat, 0, [(1, ph), (-2 * k, lam)])
        lhs = comb(lat, 3, [(1, lagr(k, al2, n, ph2)), (-1, lagr(k, al, n, ph))])
        prim = comb(lat, 2, [(1, cup(lam, dal)), (-2, cup(lam, n)), (1, cup1(dlam, n))])
        assert equal(lat, lhs, comb(lat, 3, [(k, delta(prim))]), 3), ("G4 0-form", k)

        al3 = comb(lat, 1, [(1, al), (1, m)])
        n3 = comb(lat, 2, [(1, n), (1, dm)])
        lhs = comb(lat, 3, [(1, lagr(k, al3, n3, ph)), (-1, lagr(k, al, n, ph))])
        rhs = comb(lat, 3, [
            (-k, delta(cup(m, al))),
            (-k, cup(m, n)), (-k, cup(n, m)), (-k, cup1(m, dn)), (-k, cup(dm, m)),
        ])
        assert equal(lat, lhs, rhs, 3), ("G4 large", k)

        # mutation: without the cup_1 term the 0-form variation is not a total derivative of this form
        def lagr_bad(k, al, n, ph):
            dn_ = delta(n)
            return comb(lat, 3, [(k, cup(al, delta(al))), (-k, cup(al, n)), (-k, cup(n, al)), (1, cup(ph, dn_))])
        bad = comb(lat, 3, [(1, lagr_bad(k, al2, n, ph2)), (-1, lagr_bad(k, al, n, ph))])
        total = sum(bad(x, (1, 2, 3)) for x in itertools.product(range(lat.L), repeat=3))
        assert total != 0, "the action without the cup_1 term must not be gauge invariant"
    print("(G3), (G4) Chern-Simons identities .......  True")

    # ---- (G5) 't Hooft flux -------------------------------------------------
    for L in (2, 3):
        lat = ref.Lattice(4, L)
        for trial in range(5):
            z12, z13, z14, z23, z24, z34 = [rng.randint(-3, 3) for _ in range(6)]
            z = [[0, z12, z13, z14], [-z12, 0, z23, z24], [-z13, -z23, 0, z34], [-z14, -z24, -z34, 0]]

            def f(x, S, z=z, L=L):
                m_, n_ = S
                return z[m_ - 1][n_ - 1] if (x[m_ - 1] == L - 1 and x[n_ - 1] == L - 1) else 0
            flux = ref.Cochain(lat, 2, f)
            total = sum(pont(lat, flux)(x, (1, 2, 3, 4)) for x in itertools.product(range(L), repeat=4))
            pf = z12 * z34 - z13 * z24 + z14 * z23
            assert total == 2 * pf, ("G5", total, pf)
            for (N, p) in ((2, 1), (4, 3), (6, 2)):
                b = lambda x, y: Fr(p * x * y, N)
                lhs = Fr(p, 2 * N) * total
                rhs = b(z12, z34) - b(z13, z24) + b(z14, z23)
                assert (lhs - rhs).denominator == 1, "G5 phase"
    print("(G5) 't Hooft flux and mutual braiding ...  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
