"""Drop-in fast backend for the field Q(t,r) used by every verifier.

SymPy's field("t,r", QQ) is pure Python. This module implements the same
field on top of FLINT multivariate polynomials (python-flint >= 0.7).
Elements are kept in canonical form: numerator and denominator are
coprime (FLINT gcd), and the denominator has leading coefficient 1.
Equality is therefore exact and structural, as in SymPy.

Only the part of SymPy's FracField API the verifiers use is provided:
K.zero, K.one, K(x), K.from_expr(expr), the generators, arithmetic with
ints, Fractions, SymPy rationals and field elements, ==, bool, hash, and
as_expr(). The rarely used .numer and .denom return SymPy polynomials,
so post-processing code is unchanged.

Select it with the environment variable HOPF_BACKEND=flint.
"""

import os
from fractions import Fraction

import flint
import sympy as sp
from sympy import QQ
from sympy.polys.fields import field as sympy_field

NAMES = ("t", "r", "a") if os.environ.get("HOPF_BACKEND") == "flint-rotation" else ("t", "r")
_ctx = flint.fmpq_mpoly_ctx.get(NAMES, "degrevlex")
_SK, *_ = sympy_field(",".join(NAMES), QQ)


def _scalar(x):
    if isinstance(x, int):
        return flint.fmpq(x)
    if isinstance(x, Fraction):
        return flint.fmpq(x.numerator, x.denominator)
    if isinstance(x, sp.Rational):
        return flint.fmpq(int(x.p), int(x.q))
    if isinstance(x, flint.fmpq):
        return x
    return None


def _from_sympy_poly(poly):
    return _ctx.from_dict(
        {tuple(m): flint.fmpq(int(c.numerator), int(c.denominator)) for m, c in poly.terms()}
    )


def _to_sympy_poly(poly):
    data = {}
    for m, c in zip(poly.monoms(), poly.coeffs()):
        data[tuple(m)] = QQ(int(c.p), int(c.q))
    return _SK.ring.from_dict(data) if data else _SK.ring.zero


class FF:
    __slots__ = ("n", "d")

    def __init__(self, n, d=None, normalize=True):
        if d is None:
            d = _ctx.constant(1)
        if normalize:
            if n.is_zero():
                d = _ctx.constant(1)
            else:
                g = n.gcd(d)
                if not g.is_one():
                    n, d = n // g, d // g
                lc = d.leading_coefficient()
                if lc != 1:
                    inv = 1 / lc
                    n, d = n * inv, d * inv
        self.n, self.d = n, d

    # conversions -----------------------------------------------------------
    @staticmethod
    def coerce(x):
        if isinstance(x, FF):
            return x
        s = _scalar(x)
        if s is not None:
            return FF(_ctx.constant(s), None, False)
        if hasattr(x, "numer") and hasattr(x, "denom") and hasattr(x, "field"):
            return FF(_from_sympy_poly(x.numer), _from_sympy_poly(x.denom))
        if isinstance(x, sp.Basic):
            return K.from_expr(x)
        return NotImplemented

    def to_sympy(self):
        return _SK(_to_sympy_poly(self.n)) / _SK(_to_sympy_poly(self.d))

    def as_expr(self):
        return self.to_sympy().as_expr()

    @property
    def numer(self):
        return self.to_sympy().numer

    @property
    def denom(self):
        return self.to_sympy().denom

    # arithmetic ------------------------------------------------------------
    def __add__(self, other):
        o = FF.coerce(other)
        if o is NotImplemented:
            return o
        if self.d == o.d:
            return FF(self.n + o.n, self.d)
        return FF(self.n * o.d + o.n * self.d, self.d * o.d)

    __radd__ = __add__

    def __neg__(self):
        return FF(-self.n, self.d, False)

    def __sub__(self, other):
        o = FF.coerce(other)
        if o is NotImplemented:
            return o
        return self + (-o)

    def __rsub__(self, other):
        o = FF.coerce(other)
        if o is NotImplemented:
            return o
        return o + (-self)

    def __mul__(self, other):
        o = FF.coerce(other)
        if o is NotImplemented:
            return o
        if self.n.is_zero() or o.n.is_zero():
            return K.zero
        return FF(self.n * o.n, self.d * o.d)

    __rmul__ = __mul__

    def __truediv__(self, other):
        o = FF.coerce(other)
        if o is NotImplemented:
            return o
        if o.n.is_zero():
            raise ZeroDivisionError("division by zero in Q(t,r)")
        return FF(self.n * o.d, self.d * o.n)

    def __rtruediv__(self, other):
        o = FF.coerce(other)
        if o is NotImplemented:
            return o
        return o / self

    def __pow__(self, k):
        if not isinstance(k, int):
            return NotImplemented
        if k < 0:
            return (K.one / self) ** (-k)
        return FF(self.n**k, self.d**k, False)

    # comparison ------------------------------------------------------------
    def __eq__(self, other):
        o = FF.coerce(other)
        if o is NotImplemented:
            return NotImplemented
        return self.n == o.n and self.d == o.d

    def __ne__(self, other):
        eq = self.__eq__(other)
        return eq if eq is NotImplemented else not eq

    def __bool__(self):
        return not self.n.is_zero()

    def __hash__(self):
        return hash((str(self.n), str(self.d)))

    def __repr__(self):
        return f"({self.n})/({self.d})" if not self.d.is_one() else str(self.n)

    __str__ = __repr__


class _Field:
    def __init__(self):
        self.zero = FF(_ctx.from_dict({}), None, False)
        self.one = FF(_ctx.constant(1), None, False)
        self.gens = tuple(FF(g, None, False) for g in _ctx.gens())

    def __call__(self, x):
        return FF.coerce(x)

    def from_expr(self, expr):
        return FF.coerce(_SK.from_expr(sp.sympify(expr)))


K = _Field()
cheeger, r = K.gens[:2]
