"""
The search for correction terms as linear algebra  (Operadica`Gauge`, CochainLinearSolve).

Given a cochain expression (the target) and candidate expressions of the same degree, look
for coefficients x_i with  target = sum_i x_i candidate_i  as an identity of cochains.  Here
the generic cochains are sampled with random integers, on cubes and on simplices, and the
linear system for the x_i is solved over the rationals.

  (A3)          a cup b - (-1)^(pq) b cup a  from  d(a cup_1 b), da cup_1 b, a cup_1 db:
                the unique solution is (-1)^(p+q+1) (1, -1, -(-1)^p); with the other sign of
                b cup a there is no solution.
  Chern-Simons  the modified Villain Lagrangian without its cup_1 term,
                    L0 = (k / 4 pi) a cup da - (k/2) (a cup n + n cup a) + phi cup dn,
                under a -> a + d lambda, phi -> phi - k lambda.  Its variation is a combination of
                    d lambda cup_1 dn,  d(lambda cup da),  d(lambda cup n),  d(d lambda cup_1 n)
                with the unique coefficients (k/2, k / 4 pi, -k, k/2).  The first one says that
                the correction term is -(k/2) a cup_1 dn; without that candidate there is no
                solution.

Run:  python3 reference/correction_reference.py
"""

import itertools
import random
import sys
from fractions import Fraction as Fr

import cubical_reference as cr
from villain_reference import Calc, chern_simons


def cells(C, deg, d):
    if C.kind == "cube":
        L = C.lat.L
        return [(x, S) for x in itertools.product(range(L), repeat=d)
                for S in itertools.combinations(range(1, d + 1), deg)]
    return [tuple(range(deg + 1))]


def val(C, u, cell):
    return u(*cell) if C.kind == "cube" else u(cell)


def rref(M):
    M = [row[:] for row in M]
    r, piv = 0, []
    for col in range(len(M[0])):
        p = next((i for i in range(r, len(M)) if M[i][col] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [v / M[r][col] for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(col)
        r += 1
        if r == len(M):
            break
    return M, piv


def solve(make, deg, d, kind, samples=4, seed=0):
    """make(C, rng) -> (target, [candidates]);  returns (solvable, unique, solution)"""
    rng = random.Random(seed)
    rows = []
    for s in range(samples):
        C = Calc("cube", cr.Lattice(d, 2)) if kind == "cube" else Calc("simplex", n=deg)
        t, cands = make(C, rng)
        for cell in cells(C, deg, d):
            rows.append([Fr(val(C, c, cell)) for c in cands] + [Fr(val(C, t, cell))])
    r = len(rows[0]) - 1
    M, piv = rref(rows)
    solvable = r not in piv
    unique = solvable and len(piv) == r
    sol = None
    if solvable:
        sol = [Fr(0)] * r
        for i, col in enumerate(piv):
            sol[col] = M[i][r]
    return solvable, unique, sol


def main():
    # ---- (A3) ----
    for (p, q) in ((1, 1), (1, 2), (2, 1), (2, 2)):
        def terms(C, a, b):
            return [C.d(C.cup(a, b, 1)), C.cup(C.d(a), b, 1), C.cup(a, C.d(b), 1)]

        def good(C, rng, p=p, q=q):
            a, b = C.rand(p, rng), C.rand(q, rng)
            return C.lin(p + q, (1, C.cup(a, b)), (-(-1) ** (p * q), C.cup(b, a))), terms(C, a, b)

        def bad(C, rng, p=p, q=q):
            a, b = C.rand(p, rng), C.rand(q, rng)
            return C.lin(p + q, (1, C.cup(a, b)), ((-1) ** (p * q), C.cup(b, a))), terms(C, a, b)
        s = (-1) ** (p + q + 1)
        for kind in ("cube", "simplex"):
            assert solve(good, p + q, p + q, kind) == (True, True, [s, -s, -s * (-1) ** p]), (p, q, kind)
            assert solve(bad, p + q, p + q, kind)[0] is False
    print("(A3) is the unique combination of its three cup-1 terms; the other sign has no solution  True")

    # ---- the cup-1 correction of the modified Villain Chern-Simons Lagrangian ----
    for (k, tau) in ((1, 3), (2, 5), (3, 7)):
        def make(C, rng, k=k, tau=tau):
            a, n, phi, lam = C.rand(1, rng), C.rand(2, rng), C.rand(0, rng), C.rand(0, rng)

            def bare(a_, phi_):
                return C.lin(3, (1, chern_simons(C, k, a_, n, phi_, tau)), (Fr(k, 2), C.cup(a_, C.d(n), 1)))
            a2 = C.lin(1, (1, a), (1, C.d(lam)))
            phi2 = C.lin(0, (1, phi), (-k, lam))
            t = C.lin(3, (1, bare(a2, phi2)), (-1, bare(a, phi)))
            return t, [C.cup(C.d(lam), C.d(n), 1), C.d(C.cup(lam, C.d(a))), C.d(C.cup(lam, n)),
                       C.d(C.cup(C.d(lam), n, 1))]

        def short(C, rng):
            t, cands = make(C, rng)
            return t, cands[1:]
        for kind in ("cube", "simplex"):
            assert solve(make, 3, 3, kind) == (True, True, [Fr(k, 2), Fr(k, 2 * tau), Fr(-k), Fr(k, 2)]), (k, tau, kind)
            assert solve(short, 3, 3, kind)[0] is False
    print("the gauge variation of Chern-Simons fixes the correction -(k/2) a cup_1 dn and its primitive  True")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as err:
        print("CHECK FAILED:", err)
        sys.exit(1)
