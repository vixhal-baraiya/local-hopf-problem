"""Jet arithmetic, curvature from metric 2-jets, and the c d^2 cubic channel.

This module provides the exact jet machinery used by every verifier. All
Taylor coefficients belong to Q(t,r), where t is the Cheeger parameter and
r = tan(delta/2). Run as a script, it computes the torus integral of the
c d^2 cubic channel for the Brendle--Hung tensors. At t=1 this reproduces
their value pi^2/(18 sqrt 3) (arXiv:2608.19068, Proposition 5.5).
"""

import os
from functools import lru_cache
from itertools import combinations, product

from sympy import QQ, factor, pi, simplify, sqrt, symbols
from sympy.polys.fields import field

if os.environ.get("HOPF_BACKEND") in ("flint", "flint-rotation"):
    # Same field Q(t,r) on FLINT polynomials; see flint_field.py.
    from flint_field import K, cheeger, r
else:
    K, cheeger, r = field("t,r", QQ)
zero, one = K.zero, K.one
half = one / 2
indices = range(4)
origin = (0,) * 6


@lru_cache(None)
def add_orders(a, b):
    order = tuple(x + y for x, y in zip(a, b))
    if sum(order[:4]) <= 2 and order[4] <= 1 and order[5] <= 2:
        return order


class Jet(dict):
    """Taylor polynomial with spatial degree <= 2, c degree <= 1, d degree <= 2."""

    def __add__(self, other):
        out = self.copy()
        for key, value in jet(other).items():
            out[key] = out.get(key, zero) + value
            if not out[key]:
                del out[key]
        return Jet(out)

    __radd__ = __add__

    def __neg__(self):
        return Jet({key: -v for key, v in self.items()})

    def __sub__(self, other):
        return self + (-jet(other))

    def __rsub__(self, other):
        return jet(other) + (-self)

    def __mul__(self, other):
        out = {}
        for a, v in self.items():
            for b, w in jet(other).items():
                key = add_orders(a, b)
                if key is not None:
                    out[key] = out.get(key, zero) + v * w
        return Jet({k: v for k, v in out.items() if v})

    __rmul__ = __mul__


def jet(x):
    if isinstance(x, Jet):
        return x
    return Jet({origin: K(x)}) if x else Jet()


def unit(i):
    return Jet({tuple(int(i == j) for j in range(6)): one})


def derivative_at_origin(poly, *axes):
    spatial = tuple(axes.count(i) for i in indices)
    scale = 2 if 2 in spatial else 1
    return Jet(
        {(0, 0, 0, 0) + k[4:]: scale * v for k, v in poly.items() if k[:4] == spatial}
    )


def matrix(fn):
    return [[fn(i, j) for j in indices] for i in indices]


def matmul(a, b):
    return matrix(lambda i, j: sum(a[i][k] * b[k][j] for k in indices))


def inverse_jet(a, leading_inverse, order):
    """Finite Neumann series about a supplied constant inverse."""
    a0 = matrix(lambda i, j: jet(a[i][j].get(origin, zero)))
    diff = matrix(lambda i, j: a0[i][j] - a[i][j])
    left = matmul(leading_inverse, diff)
    term = leading_inverse
    result = leading_inverse
    for _ in range(order):
        term = matmul(left, term)
        result = [[result[i][j] + term[i][j] for j in indices] for i in indices]
    return result


def geometry(axis, g_value, g_slope):
    # alpha = x-y, beta = delta+x+y, heights = u,v.
    x, y, u, v, c, d = map(unit, range(6))
    cos_delta = (1 - r * r) / (1 + r * r)
    sin_delta = 2 * r / (1 + r * r)
    da, db = x - y, x + y
    ca, sa = 1 - da * da * half, da
    cb = (1 - db * db * half) * cos_delta - db * sin_delta
    sb = (1 - db * db * half) * sin_delta + db * cos_delta
    r1, r2 = 1 - u * u * half, 1 - v * v * half

    def rotation(ax, ay, az, sign2):
        # Angular and height velocities of omega cross p on each sphere.
        a1 = az - u * (ca * ax + sa * ay)
        a2 = (az - v * (cb * ax + sb * ay)) * sign2
        h1 = r1 * (sa * ax - ca * ay)
        h2 = r2 * (sb * ax - cb * ay) * sign2
        return [(a1 + a2) * half, (a2 - a1) * half, h1, h2]

    rotations = [rotation(1, 0, 0, 1), rotation(0, 1, 0, 1), rotation(0, 0, 1, 1)]
    # First two rows of the inverse longitude change are (1,1)/2 and (-1,1)/2.
    std_inv = matrix(lambda i, j: jet(0))
    std_inv[0][0] = std_inv[1][1] = (2 + u * u + v * v) * half * half
    std_inv[0][1] = std_inv[1][0] = (v * v - u * u) * half * half
    std_inv[2][2], std_inv[3][3] = 1 - u * u, 1 - v * v
    base_inv = matrix(
        lambda i, j: 2 * (std_inv[i][j] + sum(w[i] * w[j] for w in rotations) * cheeger)
    )
    base_at = matrix(lambda i, j: jet(0))
    base_at[0][0], base_at[1][1] = jet(one / (1 + 2 * cheeger)), jet(1)
    denom = 2 * ((1 + cheeger) ** 2 - (cheeger * cos_delta) ** 2)
    base_at[2][2] = base_at[3][3] = jet((1 + cheeger) / denom)
    base_at[2][3] = base_at[3][2] = jet(-cheeger * cos_delta / denom)
    leading = matrix(lambda i, j: jet(base_inv[i][j].get(origin, zero)))
    identity = matmul(leading, base_at)
    assert all(
        identity[i][j] == jet(int(i == j)) for i, j in product(indices, repeat=2)
    )
    g = inverse_jet(base_inv, base_at, 2)

    def flat(w):
        return [sum(g[i][j] * w[j] for j in indices) for i in indices]

    kx, kz = rotations[axis], rotations[2]
    jx = rotation(int(axis == 0), int(axis == 1), 0, -1)
    jz = rotation(0, 0, 1, -1)
    kxf, kzf, jxf, jzf = map(flat, (kx, kz, jx, jz))
    jx_norm = sum(jx[i] * jxf[i] for i in indices)
    p1_axis = r1 * (ca if axis == 0 else sa)
    p2_axis = r2 * (cb if axis == 0 else sb)
    # Only the first jet of G is needed: its prefactor vanishes at the equator.
    profile = g_value + 2 * y * g_slope
    cd1 = (
        -((u + v) * (p2_axis - p1_axis) + (p1_axis + p2_axis) * (v - u))
        * profile
        * (one / 8)
    )
    # Numerator already has spatial degree two, so evaluate denominator at origin.
    cd2 = (u + v) * (v - u) * (1 / (2 * (4 - cos_delta**2)))

    def tensor(i, j):
        hc = kzf[i] * kzf[j]
        hd = (kxf[i] * jzf[j] + jzf[i] * kxf[j]) * half
        hdd = jx_norm * jzf[i] * jzf[j] * (one / 12)
        hcd = cd1 * hc + cd2 * (kxf[i] * kzf[j] + kzf[i] * kxf[j]) * half
        return g[i][j] + c * hc + d * hd + d * d * hdd + 2 * c * d * hcd

    metric = matrix(tensor)
    return metric, leading


def curvature(metric, background_inverse):
    at = matrix(lambda i, j: derivative_at_origin(metric[i][j]))
    inverse = inverse_jet(at, background_inverse, 3)

    @lru_cache(None)
    def dg(i, j, *axes):
        return derivative_at_origin(metric[i][j], *axes)

    @lru_cache(None)
    def gamma(i, j, k):
        return (dg(j, k, i) + dg(i, k, j) - dg(i, j, k)) * half

    @lru_cache(None)
    def paired(i, j, k, l):
        return sum(
            gamma(i, j, a) * inverse[a][b] * gamma(k, l, b)
            for a, b in product(indices, repeat=2)
        )

    def component(i, j, k, l):
        return (
            (dg(i, l, j, k) + dg(j, k, i, l) - dg(i, k, j, l) - dg(j, l, i, k)) * half
            + paired(i, l, j, k)
            - paired(i, k, j, l)
        )

    pairs = list(combinations(indices, 2))
    return [[component(i, j, k, l) for k, l in pairs] for i, j in pairs]


def wedge(x, y):
    return [x[i] * y[j] - x[j] * y[i] for i, j in combinations(indices, 2)]


def verify_at_axis(axis, g_value, g_slope):
    # X = U + d*A and Y = V + d*B use the first variation of the
    # minimizing plane. A second-order tilt drops out by stationarity.
    return minimized_mixed_cubic(*geometry(axis, g_value, g_slope))


def minimized_mixed_cubic(metric, leading):
    """Extract c d^2 with the stationary first-order tilt of the plane."""
    R = curvature(metric, leading)
    basis = [[int(i == j) for j in indices] for i in indices]
    U, V, N1, N2 = basis
    Z = [0] * 4
    variations = [(N1, Z), (N2, Z), (Z, N1), (Z, N2)]
    W = wedge(U, V)

    def plus(a, b):
        return [x + y for x, y in zip(a, b)]

    linear = [plus(wedge(a, V), wedge(U, b)) for a, b in variations]

    def contraction(c, d, A, B):
        order = (0, 0, 0, 0, c, d)
        return sum(
            (
                a * b * R[i][j].get(order, zero)
                for i, a in enumerate(A)
                if a
                for j, b in enumerate(B)
                if b
            ),
            zero,
        )

    def hessian(i, j):
        a, b = variations[i]
        e, f = variations[j]
        second = plus(wedge(a, f), wedge(e, b))
        return 2 * (
            contraction(0, 0, linear[i], linear[j]) + contraction(0, 0, W, second)
        )

    H = matrix(hessian)
    rc = [2 * contraction(1, 0, W, w) for w in linear]
    assert not any(rc)
    rd = [2 * contraction(0, 1, W, w) for w in linear]
    # Exact Gaussian elimination over Q(t,r).
    rows = [row + [-r] for row, r in zip(H, rd)]
    for i in indices:
        pivot = rows[i][i]
        # Every pivot is positive for t>0 and real r != 0 in this chart:
        # numerator and denominator contain only even r powers and have
        # positive rational coefficients. The omitted diagonal and antidiagonal have zero area.
        for poly in (pivot.numer, pivot.denom):
            assert poly and all(
                coeff > 0 and powers[1] % 2 == 0 for powers, coeff in poly.terms()
            )
        rows[i] = [a / pivot for a in rows[i]]
        for j in indices:
            if j != i:
                weight = rows[j][i]
                rows[j] = [a - weight * b for a, b in zip(rows[j], rows[i])]
    z = [row[-1] for row in rows]
    A, B = [0, 0, *z[:2]], [0, 0, *z[2:]]
    W1, W2 = plus(wedge(A, V), wedge(U, B)), wedge(A, B)
    cubic = (
        contraction(1, 2, W, W)
        + 2 * contraction(1, 1, W, W1)
        + contraction(1, 0, W1, W1)
        + 2 * contraction(1, 0, W, W2)
    )

    quadratic_dd = (
        contraction(0, 2, W, W)
        + 2 * contraction(0, 1, W, W1)
        + contraction(0, 0, W1, W1)
        + 2 * contraction(0, 0, W, W2)
    )
    return cubic, quadratic_dd


if __name__ == "__main__":
    # The cubic term is homogeneous quadratic in the chosen horizontal axis.
    # It is affine in the profile G and its longitude derivative, as h_cd
    # already carries c*d. Compute all three responses for both axis choices.
    responses, quadratic = [], []
    for axis in (0, 1):
        base, dd = verify_at_axis(axis, 0, 0)
        value_response = verify_at_axis(axis, 1, 0)[0] - base
        slope_response = verify_at_axis(axis, 0, 1)[0] - base
        responses.append((base, value_response, slope_response))
        quadratic.append(dd)
        print(
            ("parallel", "perpendicular")[axis],
            "[constant, G, G'] =",
            [factor(term.as_expr()) for term in responses[-1]],
        )

    mean, profile, slope = [sum(terms) / 2 for terms in zip(*responses)]
    assert not profile and not slope
    assert mean == 1 / (4 * (1 + 2 * cheeger) ** 2)

    # The torus metric in x,y is diag(1/(1+2t),1). The Jacobian
    # from the two longitudes to x,y has absolute determinant 1/2.
    t_pos = symbols("t", positive=True)
    average = mean.as_expr().subs(cheeger.as_expr(), t_pos)
    area = 2 * pi**2 / sqrt(1 + 2 * t_pos)
    integral = simplify(area * average)
    print("Rotation average =", factor(average))
    print("C(t) =", integral)
    print("C(1) =", simplify(integral.subs(t_pos, 1)))
    print("Small t expansion =", integral.series(t_pos, 0, 3))
    assert simplify(integral.subs(t_pos, 1) - pi**2 / (18 * sqrt(3))) == 0
    assert integral.limit(t_pos, 0, dir="+") == pi**2 / 2

    # Check how the quadratic dd cancellation changes in the same family.
    cosine = (1 - r**2) / (1 + r**2)
    normal_det_factor = (1 + cheeger) ** 2 - (cheeger * cosine) ** 2
    assert quadratic[0] == (1 - cheeger) * cosine**2 / (6 * normal_det_factor)
    assert quadratic[1] == -quadratic[0]
    print(
        "Quadratic d^2 check, parallel and perpendicular axes:",
        [factor(q.as_expr()) for q in quadratic],
    )
