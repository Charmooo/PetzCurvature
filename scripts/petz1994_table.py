"""Cross-check of the Lean closed form against Petz's 1994 numerical table.

Lean proves (`PetzCurvature.scalarCurvature_bkmChart_eq_hs`) that the scalar curvature of the
Kubo-Mori metric at a faithful state with eigenvalues l is

    S = sum_{i,j,k} hs(l_i, l_j, l_k) - sum_i hs(l_i, l_i, l_i) + (n^2 - 1)(n^2 - 2)/4,

with `hs` (`bkmHs`) built from `bkmSummand`, `bkmIntegral₂`, `bkmIntegral₃`. This script
evaluates those definitions as written (integrals over [0, 1]) and compares the result with
the table in D. Petz, J. Math. Phys. 35 (1994) 780-795, p. 791, and with the trace-state value
(n^2 - 1)(n^2 - 4)/8 of his Theorem 6.2.

Requires mpmath.  Run:  python scripts/petz1994_table.py
"""
import mpmath as mp

mp.mp.dps = 30
# Breakpoints near s = 0, where the integrands peak for small eigenvalues.
PTS = [0, mp.mpf("1e-9"), mp.mpf("1e-7"), mp.mpf("1e-5"), mp.mpf("1e-3"), mp.mpf("0.1"), 1]


def path(x, s):
    return (1 - s) * x + s


def m2(x, y):  # bkmIntegral₂
    return mp.quad(lambda s: 1 / (path(x, s) * path(y, s)), PTS)


def m3(x, y, z):  # bkmIntegral₃
    return mp.quad(lambda s: (1 - s) / (path(x, s) * path(y, s) * path(z, s)), PTS)


def summand(x, y, z):  # bkmSummand
    return (m3(x, y, z) ** 2 / (2 * (m2(x, y) * m2(y, z) * m2(z, x)))
            - x * m3(x, x, y) * m3(x, x, z) / (m2(x, y) * m2(x, z)))


def hs(x, y, z):  # bkmHs
    return (summand(x, y, z) + summand(y, z, x) + summand(z, x, y)) / 3


def scal(l):  # right-hand side of scalarCurvature_bkmChart_eq_hs
    n = len(l)
    return (sum(hs(a, b, c) for a in l for b in l for c in l)
            - sum(hs(a, a, a) for a in l)
            + mp.mpf((n * n - 1) * (n * n - 2)) / 4)


# Petz 1994, p. 791: (spectrum, Scal) for n = 3.
PETZ = [
    ("0.335", "0.333", "0.332", "4.9999"),
    ("0.339", "0.336", "0.325", "4.99769"),
    ("0.36", "0.34", "0.3", "4.95935"),
    ("0.35", "0.4", "0.25", "4.72556"),
    ("0.35", "0.5", "0.15", "3.13543"),
    ("0.5", "0.4", "0.1", "1.16438"),
    ("0.7", "0.2", "0.1", "-0.668265"),
    ("0.99", "0.001", "0.009", "-568.425"),
    ("0.999", "0.0001", "0.0009", "-5212.51"),
    ("0.99999", "0.000001", "0.000009", "-459501."),
]

if __name__ == "__main__":
    ok = True
    for *spec, petz in PETZ:
        v = scal([mp.mpf(x) for x in spec])
        # Agreement to the digits Petz printed: round to his number of significant figures.
        sig = len(petz.lstrip("-").replace(".", "").lstrip("0"))
        match = mp.nstr(v, sig) == mp.nstr(mp.mpf(petz), sig)
        ok &= match
        print(f"({', '.join(spec)}):  Lean {mp.nstr(v, 10):>16}   Petz {petz:>10}   "
              f"{'ok' if match else 'MISMATCH'}")
    for n in (2, 3, 4):
        v = scal([mp.mpf(1) / n] * n)
        expected = mp.mpf((n * n - 1) * (n * n - 4)) / 8
        match = abs(v - expected) < mp.mpf("1e-20")
        ok &= match
        print(f"trace state n={n}:  Lean {mp.nstr(v, 12)}   (n^2-1)(n^2-4)/8 = {expected}   "
              f"{'ok' if match else 'MISMATCH'}")
    raise SystemExit(0 if ok else 1)
