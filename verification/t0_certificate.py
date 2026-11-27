"""Explicit threshold t_0 for the quadratic coefficient (PROOF.md, Proposition 5.2).

full_metric_check.py proves, for every t>0 and every regular pair, that
  V^(2) = n_x^2 F_x + n_y^2 F_y + lambda_c V_c + lambda_d^2 V_dd,
  |V_c|  <= rho sqrt(Sc),        |V_dd| <= rho (2 sqrt(N1) + sqrt(N2)),
where n_x^2+n_y^2 = rho and F_x, F_y, Sc, N1, N2 are explicit functions of
(t,u), u = p1.p2. It writes them to data/quadratic_coefficients.json.
F_x and F_y are rational functions plus rational multiples of the aa,bb
profile jets f(u), f'(u), f''(u). Hence
  V^(2) >= rho G(t,u),
  G = min(F_x, F_y) - lambda_c sqrt(Sc) - lambda_d^2 (2 sqrt(N1) + sqrt(N2)).
This script proves G >= KAPPA on the whole box [0, T0] x [-1, 1] by ball
arithmetic (FLINT arb) with adaptive subdivision. Every enclosure is rigorous:
  * rational functions: exact rational coefficients, interval Horner
    evaluation, and a check that the denominator enclosure excludes 0;
  * profile jets: f^(j)(U) is contained in f^(j)(m) + [-w,w] sup|f^(j+1)| (mean
    value theorem), with f^(j)(m) summed in ball arithmetic up to n = NTERMS
    plus an explicit bound for the geometric tail, and sup|f^(j+1)| bounded
    by Markov's inequality |T_n^(i)| <= T_n^(i)(1) on [-1,1].
u = +/-1 are the coincident and antipodal pairs, so the bound is uniform up to
them.

Run from the verification directory:  python t0_certificate.py [T0] [KAPPA]
"""

import json
import os
import sys
from fractions import Fraction

import flint
import sympy as sp
from flint import arb

flint.ctx.prec = 128
NTERMS = 80
LC, LD = Fraction(1, 100), Fraction(1, 10)

# f_bb of Brendle--Hung section 5, with cos(n delta) = T_n(u):
#   f_bb(u) = sum_{n<=6} H_n T_n(u) - A sum_{n>=1} k^n T_n(u)/n^2,
#   k = 4 - sqrt 15, A = (42025/6) sqrt(5/3);   f_aa(u) = f_bb(-u).
H = [Fraction(2203841, 1920), Fraction(5579141, 153600), Fraction(214597, 103680),
     Fraction(48211, 307200), Fraction(251, 19200), Fraction(25, 165888)]
K_ = 4 - arb(15).sqrt()
A_ = arb(42025) / 6 * (arb(5) / 3).sqrt()


def q(x):
    x = Fraction(x)
    return arb(x.numerator) / x.denominator


def markov(n, j):
    """T_n^(j)(1) = max |T_n^(j)| on [-1,1]."""
    out = Fraction(1)
    for i in range(j):
        out *= Fraction(n * n - i * i, 2 * i + 1)
    return out


def coefficient(n):
    c = -A_ * K_**n / (n * n)
    if n <= 6:
        c += q(H[n - 1])
    return c


def tail_bound(j):
    """Bound for sum_{n>NTERMS} A k^n T_n^(j)(1)/n^2."""
    n = NTERMS + 1
    first = A_ * K_**n * q(markov(n, j)) / (n * n)
    # For j=0 the successive ratios k*(n/(n+1))^2 increase to k.
    ratio = K_
    if j > 1:
        # For j>=1 the n^2 factor cancels. Each remaining n^2-i^2
        # has decreasing successive ratios, so the first ratio bounds the tail.
        ratio *= q(markov(n + 1, j) * n * n / (markov(n, j) * (n + 1) ** 2))
    assert ratio < 1
    return first / (1 - ratio)


TAIL = [tail_bound(j) for j in range(4)]
# sup over [-1,1] of |f^(j)| for j = 1,2,3 (Markov bound term by term).
SUP = [None] + [
    sum((abs(coefficient(n)) * q(markov(n, j)) for n in range(1, NTERMS + 1)), arb(0)) + TAIL[j]
    for j in (1, 2, 3)
]


def chebyshev_jets(m):
    """T_n(m), T_n'(m), T_n''(m) for n = 0..NTERMS, by differentiated recurrence."""
    T = [[arb(1), m], [arb(0), arb(1)], [arb(0), arb(0)]]
    for n in range(1, NTERMS):
        T[0].append(2 * m * T[0][n] - T[0][n - 1])
        T[1].append(2 * T[0][n] + 2 * m * T[1][n] - T[1][n - 1])
        T[2].append(4 * T[1][n] + 2 * m * T[2][n] - T[2][n - 1])
    return T


def fbb_jets(lo, hi):
    """Enclosures of f_bb, f_bb', f_bb'' on [lo, hi] (exact rational endpoints)."""
    m = (q(lo) + q(hi)) / 2
    w = (q(hi) - q(lo)) / 2
    T = chebyshev_jets(m)
    out = []
    for j in range(3):
        centre = sum((coefficient(n) * T[j][n] for n in range(1, NTERMS + 1)), arb(0))
        spread = w * SUP[j + 1] + TAIL[j]
        out.append(centre + arb(0, spread.upper()))
    return out


def faa_jets(lo, hi):
    """f_aa(u) = f_bb(-u): f_aa^(j)(u) = (-1)^j f_bb^(j)(-u)."""
    j0, j1, j2 = fbb_jets(-hi, -lo)
    return [j0, -j1, j2]


class Rational2:
    """Exact rational function of (t,u), evaluated on boxes by interval Horner."""

    def __init__(self, expr):
        t, u = sp.symbols("t u")
        num, den = sp.fraction(sp.cancel(sp.sympify(expr, locals={"t": t, "u": u})))
        self.num = self._rows(sp.Poly(num, t, u))
        self.den = self._rows(sp.Poly(den, t, u))

    @staticmethod
    def _rows(poly):
        rows = {}
        for (i, j), c in poly.terms():
            rows.setdefault(i, {})[j] = q(Fraction(int(c.p), int(c.q)))
        deg = max(rows) if rows else 0
        out = []
        for i in range(deg + 1):
            r = rows.get(i, {})
            du = max(r) if r else 0
            out.append([r.get(j, arb(0)) for j in range(du + 1)])
        return out

    @staticmethod
    def _horner(rows, tb, ub):
        acc = arb(0)
        for coeffs in reversed(rows):
            inner = arb(0)
            for c in reversed(coeffs):
                inner = inner * ub + c
            acc = acc * tb + inner
        return acc

    def __call__(self, tb, ub):
        d = self._horner(self.den, tb, ub)
        if d.contains(0):
            return None
        return self._horner(self.num, tb, ub) / d


def load(path):
    with open(path) as fh:
        raw = json.load(fh)
    modes = ["aa0", "aa1", "aa2", "bb0", "bb1", "bb2"]
    funcs = {}
    for side in ("Fx", "Fy"):
        funcs[side] = (Rational2(raw[side + "_base"]), [Rational2(raw[f"{side}_{m}"]) for m in modes])
    for k in ("Sc", "N1", "N2"):
        funcs[k] = Rational2(raw[k])
    return funcs


def lower_bound(funcs, t0, t1, u0, u1):
    tb = arb.union(q(t0), q(t1)) if hasattr(arb, "union") else (q(t0) + q(t1)) / 2 + arb(0, ((q(t1) - q(t0)) / 2).upper())
    ub = (q(u0) + q(u1)) / 2 + arb(0, ((q(u1) - q(u0)) / 2).upper())
    jets = faa_jets(u0, u1) + fbb_jets(u0, u1)
    values = []
    for side in ("Fx", "Fy"):
        base, coeffs = funcs[side]
        v = base(tb, ub)
        if v is None:
            return None
        for c, f in zip(coeffs, jets):
            cv = c(tb, ub)
            if cv is None:
                return None
            v += cv * f
        values.append(v)
    parts = [funcs[k](tb, ub) for k in ("Sc", "N1", "N2")]
    if any(p is None for p in parts):
        return None
    roots = []
    for p in parts:
        hi = p.upper()
        if hi < 0:
            hi = arb(0)
        roots.append(arb(hi).sqrt().upper())  # upper bound of sqrt on the box
    loss = q(LC) * roots[0] + q(LD * LD) * (2 * roots[1] + roots[2])
    low = min(v.lower() for v in values)
    return low - loss


def certify(funcs, T0, kappa, min_width=Fraction(1, 2**22)):
    stack = [(Fraction(0), Fraction(T0), Fraction(-1), Fraction(1))]
    boxes, worst = 0, None
    while stack:
        t0, t1, u0, u1 = stack.pop()
        lb = lower_bound(funcs, t0, t1, u0, u1)
        if lb is not None and lb >= q(kappa):
            boxes += 1
            worst = lb if worst is None or lb < worst else worst
            continue
        if u1 - u0 < min_width and t1 - t0 < min_width * T0:
            return False, (t0, t1, u0, u1, lb), boxes
        if (u1 - u0) / 2 >= (t1 - t0) / Fraction(T0):
            mid = (u0 + u1) / 2
            stack += [(t0, t1, u0, mid), (t0, t1, mid, u1)]
        else:
            mid = (t0 + t1) / 2
            stack += [(t0, mid, u0, u1), (mid, t1, u0, u1)]
    return True, worst, boxes


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    funcs = load(os.path.join(here, "data", "quadratic_coefficients.json"))
    T0 = Fraction(sys.argv[1]) if len(sys.argv) > 1 else Fraction(1, 100)
    kappa = Fraction(sys.argv[2]) if len(sys.argv) > 2 else Fraction(3, 10)
    ok, info, boxes = certify(funcs, T0, kappa)
    if ok:
        print(f"CERTIFIED: V^(2) >= {kappa} rho for all 0 <= t <= {T0} and all u in [-1,1]")
        print(f"  ({boxes} boxes; smallest certified lower bound {info.mid().str(6)})")
    else:
        print(f"FAILED at box t in [{info[0]},{info[1]}], u in [{info[2]},{info[3]}], lower bound {info[4]}")
        sys.exit(1)
