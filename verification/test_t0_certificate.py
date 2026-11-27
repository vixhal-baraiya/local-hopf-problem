from unittest import TestCase

from t0_certificate import A_, K_, NTERMS, tail_bound


class TailBoundTest(TestCase):
    def test_zeroth_tail_at_one(self):
        # T_n(1) = 1. All omitted terms have the same sign at this endpoint.
        n = NTERMS + 1
        partial_sum = sum(A_ * K_**i / i**2 for i in range(n, n + 10))
        self.assertLess(partial_sum, tail_bound(0))
