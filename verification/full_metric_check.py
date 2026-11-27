"""Full-metric checks: the complete first- and second-order tensors in general position.

This script assembles the whole family
    g_t + s h^(1) + s^2 h^(2)
(the tensors of PROOF.md section 2) at points in general position and
certifies Propositions 5.1 and 6.1 of PROOF.md.

Coordinates. The chart of quadratic_coefficient.chart puts p1=(1,0,0) and
p2=(cos delta, sin delta, 0) in a local frame whose third axis is the unit normal
n of the great circle through p1,p2. The fixed axes e_x,e_y,e_z of the paper
are arbitrary orthonormal vectors in this frame: they are the columns of a
rotation matrix Rm. Then n_i = Rm[2][i], and the projections of e_x,e_z to the
circle plane are x_par=(Rm[0][0],Rm[1][0]) and z_par=(Rm[0][2],Rm[1][2]).
All results are exact in Q(t,r), r = tan(delta/2), so every statement holds
for every separation and every t>0 at the rotation tested.

Part A (quadratic, general position). Write V^(2) as a polynomial in
(lambda_c,lambda_d) with the aa,bb profile jets f(u),f'(u),f''(u) kept as
independent symbols (V^(2) is linear in h^(2)). At a set of 165 rotations
the script checks the exact identities
  V_d = V_cc = V_cd = 0,
  V_base = n_x^2 V_base(R_x) + n_y^2 V_base(R_y)          (R_x: n=e_x; R_y: n=e_y),
  V_c   = n_z [n_x A.z_par + n_y B.z_par],
  V_dd  = 2 n_z n_x x_par^T M1 z_par + n_x^2 z_par^T M2 z_par (M2 symmetric),
where A,B,M1,M2 are solved for from some of the rotations.
Every difference is a polynomial of degree <= 4 in the entries of Rm, with
coefficients in Q(t,r). On SO(3) such polynomials form a space of dimension
165, and the rotations are chosen so that their evaluation matrix on all
715 monomials has rank 165 (unisolvent_frames). A difference that vanishes at
them therefore vanishes identically: the certificate is deterministic.
It also checks the limits at t=0 stated in PROOF.md section 5:
  F_0 = V_base(R_y)|_{t=0} is the function certified > 1 in first_order_weights.py,
  |A_0|^2+|B_0|^2 < 100 and |M1_0|_F^2, |M2_0|_F^2 < 1/2 on [-1,1],
with all fitted coefficients regular at t=0 on the compactified circle.

Part B (cubic, equatorial torus). For n=e_z the cubic coefficient is a
trigonometric polynomial of degree <= 3 in the rotation angle about n (each
of the three factors carries at most one power of e_x or e_y; PROOF.md section 6).
Averaging over the four rotations by multiples of pi/2 is therefore the exact
rotation mean. The script checks, for every separation and t, with all
amplitudes equal to their final values and the complete h^(2):
  V^(2)=0 on the torus, the aa,bb profiles contribute zero to the mean, and the
  mean equals lambda_c lambda_d^2/(4(1+2t)^2) = 1/(40000(1+2t)^2).

The exact coefficient functions of (t,u) needed for the explicit threshold
t_0 are written to data/quadratic_coefficients.json; t0_certificate.py
uses them.

Run from the verification directory with Python 3, SymPy 1.14 and python-flint:
  HOPF_BACKEND=flint python full_metric_check.py                # all parts, all cores
  HOPF_BACKEND=flint python full_metric_check.py --skip-cubic   # part A only
"""

import os
import sys
from fractions import Fraction
from multiprocessing import Pool

import sympy as sp

from cd_tensor import cd_profiles
from jets import half, unit, wedge
from weights_ode import C, S, T, rational_in_cosine
from weights_ode import u as U
from quadratic_coefficient import K, chart, curvature, matrix, one, quadratic, symprod, t
from normal_corrections import profiles, solve
from first_order_weights import P, Q, gradient, regular_on_circle

LC, LD = Fraction(1, 100), Fraction(1, 10)
FMODES = ["aa0", "aa1", "aa2", "bb0", "bb1", "bb2"]
LAMBDAS = [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1), (1, 1)]
R_X = ((0, 1, 0), (0, 0, 1), (1, 0, 0))  # columns e_x,e_y,e_z; third row = n
R_Y = ((1, 0, 0), (0, 0, -1), (0, 1, 0))


def quat_rotation(a, b, c, d):
    n = a * a + b * b + c * c + d * d
    rows = [
        [a * a + b * b - c * c - d * d, 2 * (b * c - a * d), 2 * (b * d + a * c)],
        [2 * (b * c + a * d), a * a - b * b + c * c - d * d, 2 * (c * d - a * b)],
        [2 * (b * d - a * c), 2 * (c * d + a * b), a * a - b * b - c * c + d * d],
    ]
    return tuple(tuple(Fraction(x, n) for x in row) for row in rows)


def kq(x):
    x = Fraction(x)
    return K(sp.Rational(x.numerator, x.denominator))


def ujet(expr, du):
    """Second-order jet of a rational function of u=p1.p2 about u=cos(delta)."""
    out, v = [], expr
    for i in range(3):
        out.append(K.from_expr(sp.cancel(v.subs(U, C.as_expr()) / sp.factorial(i))))
        v = sp.diff(v, U)
    return out[0] + du * out[1] + du * du * out[2]


def tensors(Rm, lc, ld, mode):
    """Return (g, inv, h1, h2) as functions of the index pair.

    mode 'full': complete h^(2) with the aa,bb profile jets set to zero.
    mode 'aaK'/'bbK': h^(1) unchanged, h^(2) = the aa (bb) tensor whose
    profile jet is the K-th basis jet (f, f', f'' at u=cos(delta) set to
    unit vectors). mode 'zero': h^(2)=0.
    """
    p, q, rot, flat, g, inv, _s = chart(C, S)
    ex, ey, ez = [tuple(K(Rm[row][col]) for row in range(3)) for col in range(3)]
    dot = sum(a * b for a, b in zip(p, q))
    du = dot - C
    plus = [a + b for a, b in zip(p, q)]
    minus = [b - a for a, b in zip(p, q)]

    def co(v, w):
        return sum(a * b for a, b in zip(v, w))

    kp, km = flat(rot(plus)), flat(rot(minus))
    kx, ky, kz = (flat(rot(e)) for e in (ex, ey, ez))
    jx, jy, jz = (flat(rot(e, -1)) for e in (ex, ey, ez))
    h = 1 + 2 * t
    lc, ld = kq(lc), kq(ld)
    ma, na = (ujet(e, du) for e in profiles(T, U))
    mb, nb = (ujet(e, du) for e in profiles(T, -U))
    fcd, gcd = (ujet(e, du) for e in cd_profiles(T, U))
    gjx = co(rot(ex, -1), jx)
    gkz = co(rot(ez), kz)
    qa = 2 * dot * dot - 1
    dzx = co(q, ez) * co(q, ex) - co(p, ez) * co(p, ex)
    dzz = co(q, ez) * co(q, ez) - co(p, ez) * co(p, ez)
    basis = [K.one, du, du * du * half]

    def h1(i, j):
        def pr(a, b):
            return symprod(a, b, i, j)

        ha = P(-dot) * pr(kp, kx) + Q(-dot) * pr(km, jx)
        hb = P(dot) * pr(km, ky) + Q(dot) * pr(kp, jy)
        return ha + hb + lc * pr(kz, kz) + ld * pr(kx, jz)

    def h2(i, j):
        def pr(a, b):
            return symprod(a, b, i, j)

        if mode == "zero":
            return K.zero
        if mode != "full":
            jetf = basis[int(mode[2])]
            return 9 * jetf * (pr(kx, kx) if mode[:2] == "aa" else pr(ky, ky))
        hcc = gkz * pr(kz, kz)
        hac = co(plus, ez) * (-5 - 14 * dot + 3 * qa) * pr(kx, kz) * (one / 20)
        hbc = co(minus, ez) * (-5 + 14 * dot + 3 * qa) * pr(ky, kz) * (one / 20)
        hdd = gjx * pr(jz, jz) * (one / (4 * h))
        had = co(minus, ex) * (-406 - 92 * dot + 18 * qa) * pr(kx, kz) * (one / 400)
        had += co(minus, ez) * (-823 + 154 * dot + 9 * qa) * pr(kx, kx) * (one / 200)
        had -= ma * co(minus, ex) * pr(jx, jz) + na * co(minus, ez) * pr(jx, jx)
        hbd = co(plus, ex) * (-406 + 92 * dot + 18 * qa) * pr(ky, kz) * (one / 400)
        hbd += co(plus, ez) * (-823 - 154 * dot + 9 * qa) * pr(kx, ky) * (one / 200)
        hbd -= mb * co(plus, ex) * pr(jy, jz) + nb * co(plus, ez) * pr(jy, jx)
        hcd = -(fcd * dzx * pr(jz, jz) + gcd * dzz * pr(jx, jz)) * (one / 4)
        return (
            lc * lc * hcc
            + 2 * lc * hac
            + 2 * lc * hbc
            + ld * ld * hdd
            + 2 * ld * had
            + 2 * ld * hbd
            + 2 * lc * ld * hcd
        )

    return g, inv, h1, h2


def quadratic_task(args):
    Rm, lc, ld, mode = args
    g, inv, h1, h2 = tensors(Rm, lc, ld, mode)
    s = unit(5)
    if mode == "full":
        metric = matrix(lambda i, j: g[i][j] + s * h1(i, j) + s * s * h2(i, j))
    else:  # V^(2) is linear in h^(2): isolate the profile response
        metric = matrix(lambda i, j: g[i][j] + s * s * h2(i, j))
    return quadratic(metric, inv).value.as_expr()


def cubic_task(args):
    Rm, mode = args
    g, inv, h1, h2 = tensors(Rm, LC, LD, mode)
    amp = unit(4) + unit(5)
    metric = matrix(lambda i, j: g[i][j] + amp * h1(i, j) + amp * amp * h2(i, j))
    R = curvature(metric, inv)
    first = gradient(R, (0, 0, 0, 0, 0, 1))
    disp = solve(quadratic(g, inv).hessian, [-a for a in first])
    frame = wedge(
        [1, 0, amp * disp[0], amp * disp[1]], [0, 1, amp * disp[2], amp * disp[3]]
    )
    energy = sum(R[i][j] * frame[i] * frame[j] for i in range(6) for j in range(6))
    assert not energy.get((0, 0, 0, 0, 0, 0)) and not energy.get((0, 0, 0, 0, 0, 1))
    v2 = energy.get((0, 0, 0, 0, 0, 2), K.zero)
    # amp^3 = (c+d)^3 has c d^2 coefficient 3; c^2 and d^3 are truncated.
    v3 = energy.get((0, 0, 0, 0, 1, 2), K.zero) / 3
    return v2.as_expr(), v3.as_expr()


def to_k(expr):
    return K.from_expr(expr)


def linear_solve(rows, rhs):
    """Solve a square system with rational coefficient rows and K right sides."""
    m = sp.Matrix(rows)
    inv = m.inv()
    return [sum((kq(Fraction(str(inv[i, j]))) * rhs[j] for j in range(len(rhs))), K.zero) for i in range(len(rhs))]


def limit_r(x):
    """Assert regularity at t=0 on the compactified circle; return the t=0 value in Q(r)."""
    regular_on_circle(x)
    return K.from_expr(x.as_expr().subs(T, 0))


def uniform_limit(x):
    """As limit_r, written as a rational function of u (x must be even in r)."""
    return sp.cancel(rational_in_cosine(limit_r(x)))


def _exponents(nvars, degree):
    if nvars == 1:
        for i in range(degree + 1):
            yield (i,)
        return
    for i in range(degree + 1):
        for rest in _exponents(nvars - 1, degree - i):
            yield (i,) + rest


MONOMIALS = list(_exponents(9, 4))  # all 715 monomials of degree <= 4 in 9 entries


def quat_integer(a, b, c, d):
    n = a * a + b * b + c * c + d * d
    M = [
        [a * a + b * b - c * c - d * d, 2 * (b * c - a * d), 2 * (b * d + a * c)],
        [2 * (b * c + a * d), a * a - b * b + c * c - d * d, 2 * (c * d - a * b)],
        [2 * (b * d - a * c), 2 * (c * d + a * b), a * a - b * b - c * c + d * d],
    ]
    return M, n


def monomial_row(M, n):
    """Degree <= 4 monomials of R = M/n, scaled by n^4 to integers."""
    x = [M[i][j] for i in range(3) for j in range(3)]
    row = []
    for e in MONOMIALS:
        v = n ** (4 - sum(e))
        for xi, ei in zip(x, e):
            if ei:
                v *= xi**ei
        row.append(v)
    return row


def unisolvent_frames():
    """R_x, R_y and quaternion frames whose degree-4 evaluation matrix has rank 165.

    Restricted to SO(3), polynomials of degree <= 4 in the entries span the
    matrix coefficients of the irreducible representations with l <= 4, a
    space of dimension 1+9+25+49+81 = 165 (V_1 is the standard
    representation, and V_1^(x)k contains only V_l with l <= k). If the
    evaluation matrix at a set of frames has rank 165, evaluation there is
    injective on that space: a polynomial of degree <= 4 vanishing at those
    frames vanishes on all of SO(3).
    """
    import itertools
    import math

    import flint

    frames = [R_X, R_Y]
    rows = [monomial_row([list(r) for r in R], 1) for R in frames]
    rank = flint.fmpz_mat(rows).rank()
    quats = []
    for bound in range(1, 6):
        pool = []
        for q in itertools.product(range(-bound, bound + 1), repeat=4):
            if max(map(abs, q)) != bound or not any(q):
                continue
            if next(v for v in q if v) < 0 or math.gcd(*q) != 1:
                continue
            pool.append(q)
        pool.sort(key=lambda q: (sum(v * v for v in q), q))
        for q in pool:
            row = monomial_row(*quat_integer(*q))
            new = flint.fmpz_mat(rows + [row]).rank()
            if new > rank:
                rows.append(row)
                quats.append(q)
                frames.append(quat_rotation(*q))
                rank = new
            if rank == 165:
                return frames, quats
    raise AssertionError("no unisolvent set found")


def first_independent(rows_of, frames, size):
    """Indices of the first `size` frames whose rows are linearly independent."""
    chosen, mat = [], []
    for i, R in enumerate(frames):
        trial = mat + [rows_of(R)]
        if sp.Matrix(trial).rank() == len(trial):
            chosen.append(i)
            mat = trial
            if len(chosen) == size:
                return chosen
    raise AssertionError("fit frames are degenerate")


def export_components(coef_c, coef_dd):
    """Keep the signed sine factor in the fitted in-plane vectors and matrices."""
    names = ("A0", "A1", "B0", "B1", "M100", "M101", "M110", "M111",
             "M200", "M201", "M211")
    out = {}
    for name, value in zip(names, [*coef_c, *coef_dd], strict=True):
        out[name + "@r"] = str(value.as_expr())
        try:
            even = rational_in_cosine(value)
        except AssertionError:
            out[name + "@sin"] = str(sp.factor(rational_in_cosine(value / S)))
        else:
            out[name + "@u"] = str(sp.factor(even))
    return out


def part_a(pool, dump):
    rotations, quats = unisolvent_frames()
    tasks = [(Rm, lc, ld, "full") for Rm in rotations for lc, ld in LAMBDAS]
    tasks += [(Rm, 0, 0, m) for Rm in rotations for m in FMODES]
    print(f"Part A: {len(tasks)} curvature evaluations at {len(rotations)} unisolvent frames", flush=True)
    results = dict(zip([(id(a[0]), a[1], a[2], a[3]) for a in tasks], map(to_k, pool.map(quadratic_task, tasks, chunksize=1))))

    def comps(Rm):
        v = {lam: results[(id(Rm), lam[0], lam[1], "full")] for lam in LAMBDAS}
        base = v[(0, 0)]
        vc = (v[(1, 0)] - v[(-1, 0)]) * half
        vcc = (v[(1, 0)] + v[(-1, 0)]) * half - base
        vd = (v[(0, 1)] - v[(0, -1)]) * half
        vdd = (v[(0, 1)] + v[(0, -1)]) * half - base
        vcd = v[(1, 1)] - base - vc - vcc - vd - vdd
        f = [results[(id(Rm), 0, 0, m)] for m in FMODES]
        return dict(base=base, c=vc, cc=vcc, d=vd, dd=vdd, cd=vcd, f=f)

    data = [comps(Rm) for Rm in rotations]
    rx, ry = data[0], data[1]

    def geom(Rm):
        n = [Rm[2][i] for i in range(3)]
        xp = (Rm[0][0], Rm[1][0])
        zp = (Rm[0][2], Rm[1][2])
        return n, xp, zp

    def c_row(Rm):
        n, _, zp = geom(Rm)
        return [n[2] * n[0] * zp[0], n[2] * n[0] * zp[1], n[2] * n[1] * zp[0], n[2] * n[1] * zp[1]]

    def dd_row(Rm):
        n, xp, zp = geom(Rm)
        m1 = [2 * n[2] * n[0] * xp[i] * zp[j] for i in range(2) for j in range(2)]
        m2 = [n[0] ** 2 * zp[0] ** 2, 2 * n[0] ** 2 * zp[0] * zp[1], n[0] ** 2 * zp[1] ** 2]
        return m1 + m2

    fit_c = first_independent(c_row, rotations, 4)
    fit_dd = first_independent(dd_row, rotations, 7)
    coef_c = linear_solve([c_row(rotations[i]) for i in fit_c], [data[i]["c"] for i in fit_c])
    coef_dd = linear_solve([dd_row(rotations[i]) for i in fit_dd], [data[i]["dd"] for i in fit_dd])

    # Every residual below is a polynomial of degree <= 4 in the entries of
    # the frame with coefficients in Q(t,r) (h^(1) has degree <= 2, h^(2)
    # degree <= 4). It vanishes at all 165 unisolvent frames, so it is zero
    # on SO(3): the identities hold for every regular pair, t and separation.
    for Rm, dat in zip(rotations, data):
        n, _, _ = geom(Rm)
        assert not dat["d"] and not dat["cc"] and not dat["cd"], "mixed channel survives"
        assert dat["base"] == kq(n[0] ** 2) * rx["base"] + kq(n[1] ** 2) * ry["base"]
        for k in range(6):
            assert dat["f"][k] == kq(n[0] ** 2) * rx["f"][k] + kq(n[1] ** 2) * ry["f"][k]
        assert dat["c"] == sum((kq(a) * x for a, x in zip(c_row(Rm), coef_c)), K.zero)
        assert dat["dd"] == sum((kq(a) * x for a, x in zip(dd_row(Rm), coef_dd)), K.zero)
    print("  V_d = V_cc = V_cd = 0, V_base = n_x^2 F_t(-u) + n_y^2 F_t(u),", flush=True)
    print("  V_c and V_dd forms: exact at all 165 unisolvent frames, hence on all of SO(3)", flush=True)

    # Exact coefficient functions of (t,u) for the interval certificate of t_0.
    a0, a1, b0, b1 = coef_c
    m1, m2 = coef_dd[:4], coef_dd[4:]
    exact = {
        "Fy_base": ry["base"],
        "Fx_base": rx["base"],
        "Sc": a0 * a0 + a1 * a1 + b0 * b0 + b1 * b1,
        "N1": sum((x * x for x in m1), K.zero),
        "N2": m2[0] * m2[0] + 2 * m2[1] * m2[1] + m2[2] * m2[2],
    }
    for k, mode in enumerate(FMODES):
        exact["Fy_" + mode] = ry["f"][k]
        exact["Fx_" + mode] = rx["f"][k]
    if dump:
        import json

        out = export_components(coef_c, coef_dd)
        for k, v in exact.items():
            out[k + "@r"] = str(v.as_expr())  # always available, r = tan(delta/2)
            try:
                out[k] = str(sp.factor(rational_in_cosine(v)))  # as a function of u
            except AssertionError:
                pass
        os.makedirs(os.path.dirname(dump), exist_ok=True)
        with open(dump, "w", encoding="utf-8", newline="\n") as fh:
            json.dump(out, fh, indent=1, sort_keys=True)
        print(f"  exact coefficient functions of (t,u) written to {dump}", flush=True)

    # Uniform t -> 0 limits on the compactified circle.
    a0, a1, b0, b1 = (limit_r(x) for x in coef_c)
    sq = sp.cancel(rational_in_cosine(a0**2 + a1**2 + b0**2 + b1**2))
    num, den = sp.fraction(sp.cancel(100 - sq))
    for poly in (sp.Poly(num, U), sp.Poly(den, U)):
        assert poly.count_roots(-1, 1) == 0
    assert (num / den).subs(U, 0) > 0
    print("  |A_0|^2+|B_0|^2 < 100 on [-1,1]: the lambda_c loss is < 10|lambda_c| rho for small t", flush=True)
    m1 = [limit_r(x) for x in coef_dd[:4]]
    m2 = [limit_r(x) for x in coef_dd[4:]]
    # coef_dd[5] multiplies 2 z0 z1, so it is the off-diagonal entry of M2.
    norms = [
        sp.cancel(rational_in_cosine(sum((x * x for x in m1), K.zero))),
        sp.cancel(rational_in_cosine(m2[0] * m2[0] + 2 * m2[1] * m2[1] + m2[2] * m2[2])),
    ]
    for nm in norms:
        num, den = sp.fraction(sp.cancel(sp.Rational(1, 2) - nm))
        for poly in (sp.Poly(num, U), sp.Poly(den, U)):
            assert poly.count_roots(-1, 1) == 0
        assert (num / den).subs(U, 0) > 0
    print("  limits: |A_0|^2+|B_0|^2 =", sp.factor(sq), flush=True)
    print("          |M1_0|_F^2 =", sp.factor(norms[0]), " |M2_0|_F^2 =", sp.factor(norms[1]), flush=True)
    print("  |M1_0|_F^2, |M2_0|_F^2 < 1/2 on [-1,1]: |V_dd| <= (2|M1|+|M2|) rho < 3 rho for small t", flush=True)

    # Identify V_base(R_y) at t=0 with F_0 of first_order_weights.py:
    #   F_0 = geometric(u) - 18 f_bb''(delta), f''(delta) = (1-u^2) f''(u) - u f'(u).
    geometric = (
        1152 * U**6 - 400 * U**5 - 10400 * U**4 - 2956 * U**3 + 18544 * U**2 + 6920 * U - 4643
    ) / 400
    assert sp.cancel(uniform_limit(ry["base"]) - geometric) == 0
    fy = [uniform_limit(x) for x in ry["f"]]
    assert fy[:4] == [0, 0, 0, 0]
    assert sp.cancel(fy[4] - 18 * U) == 0 and sp.cancel(fy[5] + 18 * (1 - U**2)) == 0
    fx = [uniform_limit(x) for x in rx["f"]]
    assert sp.cancel(uniform_limit(rx["base"]) - geometric.subs(U, -U)) == 0
    assert fx[3:] == [0, 0, 0]
    # F_0(-u) = geometric(-u) - 18 g(-u) with g(v) = (1-v^2) f_bb''(v) - v f_bb'(v).
    # Since f_aa(u) = f_bb(-u): g(-u) = (1-u^2) f_aa''(u) - u f_aa'(u).
    assert fx[0] == 0 and sp.cancel(fx[1] - 18 * U) == 0 and sp.cancel(fx[2] + 18 * (1 - U**2)) == 0
    print("  V_base(R_y) -> F_0(u), V_base(R_x) -> F_0(-u) uniformly (F_0 > 1 by first_order_weights.py)", flush=True)
    print(f"  Unisolvent quaternions: {quats}", flush=True)


def check_conformal_response():
    """Linear response of the full 4D curvature to 2 h chi g on the equator."""
    _, _, _, _, g, inv, _ = chart(C, S)
    spatial = [unit(i) for i in range(4)]
    h = 1 + 2*t
    # Test a basis of all scalar two-jets, including arbitrary normal derivatives.
    tests = [(one, 0), *((x, 0) for x in spatial)]
    for i, x in enumerate(spatial):
        for j in range(i, 4):
            expected = -h if i == j == 0 else -one if i == j == 1 else 0
            monomial = x*spatial[j] * (half if i == j else one)
            tests.append((monomial, expected))
    for chi, expected in tests:
        metric = matrix(lambda i, j: g[i][j] + unit(4)*chi*g[i][j]*(2*h))
        response = curvature(metric, inv)[0][0].get((0, 0, 0, 0, 1, 0), K.zero)
        assert response == expected, ("conformal response", chi, response, expected)
    print("  fixed-plane conformal response = -h chi_xx - chi_yy (all 15 spatial two-jets)", flush=True)


def part_b(pool):
    check_conformal_response()
    quarter = [
        ((1, 0, 0), (0, 1, 0), (0, 0, 1)),
        ((0, -1, 0), (1, 0, 0), (0, 0, 1)),
        ((-1, 0, 0), (0, -1, 0), (0, 0, 1)),
        ((0, 1, 0), (-1, 0, 0), (0, 0, 1)),
    ]
    modes = ["full", "zero"] + FMODES
    tasks = [(Rm, m) for Rm in quarter for m in modes]
    print(f"Part B: {len(tasks)} cubic evaluations on the equatorial torus", flush=True)
    out = dict(zip([(id(a[0]), a[1]) for a in tasks], pool.map(cubic_task, tasks, chunksize=1)))
    # 'zero' (h2=0) is only a reference: V^(2) is linear in h^(2), so the full
    # value must vanish and each aa,bb profile mode must add nothing to it.
    for Rm in quarter:
        assert sp.cancel(out[(id(Rm), "full")][0]) == 0, "V2 nonzero on the torus"
        for m in FMODES:
            diff = out[(id(Rm), m)][0] - out[(id(Rm), "zero")][0]
            assert sp.cancel(diff) == 0, ("profile changes V2 on the torus", m)

    def mean(m):
        return sp.cancel(sum(out[(id(Rm), m)][1] for Rm in quarter) / 4)

    zero = mean("zero")
    for m in FMODES:
        assert sp.cancel(mean(m) - zero) == 0, ("profile response has nonzero mean", m)
    full = mean("full")
    assert sp.cancel(full - 1 / (40000 * (1 + 2 * T) ** 2)) == 0
    print("  V^(2) = 0 on the torus; aa,bb profiles add zero mean;", flush=True)
    print("  exact rotation mean of the full cubic =", sp.factor(full), flush=True)


if __name__ == "__main__":
    dump = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "quadratic_coefficients.json")
    with Pool(os.cpu_count()) as pool:
        if "--skip-cubic" not in sys.argv:
            part_b(pool)
        part_a(pool, dump)
    print("All full-metric checks passed.")
