"""Construct and certify a recursive family using the proved three-speed reduction.

Every output witness is independently tested against every original speed using
exact arithmetic. This demonstrates application; it is not a new general LRC proof.
"""
from fractions import Fraction as Q
import json


def distance(x):
    r = x % 1
    return min(r, 1-r)


def ceil(x):
    return -((-x.numerator)//x.denominator)


def lift(core, triple, t):
    k = len(core)+3
    delta = Q(1, k+1)
    d, a, b = triple
    M = max(core)
    assert b == a+d and 0 < d <= a
    assert 5*(k-2)*M <= 6*d
    assert all(distance(v*t) >= Q(1, k-2) for v in core)
    R = 5*delta/(2*d)
    lo, hi = t-R, t+R
    candidates = {t, lo, hi}
    for v in triple:
        for n in range((v*lo).numerator//(v*lo).denominator-1, ceil(v*hi)+2):
            for sign in [-1, 1]:
                u = (n+sign*delta)/v
                if lo <= u <= hi:
                    candidates.add(u)
    feasible = [u for u in candidates if all(distance(v*u) >= delta for v in triple)]
    assert feasible
    s = min(feasible, key=lambda u: (abs(u-t), u))
    assert abs(s-t) <= R
    assert all(distance(v*s) >= delta for v in core+list(triple))
    return s, len(candidates)


def run():
    speeds, t = [1, 2, 3, 4], Q(1, 5)
    records = []
    for _ in range(20):
        k, M = len(speeds)+3, speeds[-1]
        d = ceil(Q(5*(k-2)*M, 6))
        a, b = d+1, 2*d+1
        assert M < d < a < b
        s, candidates = lift(speeds, (d, a, b), t)
        # All three are larger than the core. Hence this is the best possible
        # pair for the previous uniform separation test, and it still fails.
        assert a < (k-1)*d
        # The guarded pair criterion's necessary speed separation also fails.
        assert 2*a < (k-1)*d
        speeds += [d, a, b]
        records.append({'k': k, 'triple': [d, a, b], 'core_max': M,
                        'old_witness': str(t), 'lifted_witness': str(s),
                        'candidate_times_tested': candidates,
                        'minimum_distance': str(min(distance(v*s) for v in speeds))})
        t = s
    print(json.dumps({'layers': len(records), 'final_number_of_speeds': len(speeds),
                      'all_lifts_exactly_verified': True, 'records': records,
                      'scope': 'Recursive separated sum-triple family; no assertion for unstructured speed sets.'}, indent=2))


if __name__ == '__main__':
    run()
