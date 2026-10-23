"""Exact checks supporting the priority audit, not a novelty certificate.

Dubickas (2011), Theorem 1.1, uses h=floor((n+1)/(12e)).
We bound e by rational Taylor bounds before evaluating this floor.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json


def e_bounds(N=40):
    lo = sum((Q(1, factorial(j)) for j in range(N+1)), Q(0))
    hi = lo + Q(N+2, (N+1)*factorial(N+1))
    return lo, hi


def dubickas_h(n):
    lo, hi = e_bounds()
    lower = Q(n+1, 12)/hi
    upper = Q(n+1, 12)/lo
    a = lower.numerator//lower.denominator
    b = upper.numerator//upper.denominator
    assert a == b
    return a


def run():
    speeds = [1, 2, 3, 4]
    records = []
    for layer in range(1, 201):
        k, M = len(speeds)+3, speeds[-1]
        d = (5*(k-2)*M + 5)//6
        speeds.extend([d, d+1, 2*d+1])
        assert all(speeds[i+3] >= 4*speeds[i] for i in range(k-3))
        if k < 32:
            continue
        h = dubickas_h(k)
        bad = [i+1 for i in range(k-h) if speeds[i+h] < (k+1)*speeds[i]]
        covered = not bad
        # The analytic argument in PRIORITY_AUDIT.md proves this for all
        # n>=494 satisfying the every-third-speed condition, not just the grid.
        if k >= 494:
            assert covered
        records.append({'k': k, 'h': h, 'meets_Dubickas_2011': covered,
                        'first_failing_index': bad[0] if bad else None})
    lo, hi = e_bounds()
    assert hi < Q(11, 4)
    assert 4**5 >= 99*(5+1)
    # The induction step 4*99*(q+1) >= 99*(q+2) holds for q>=0.
    assert all(4*99*(q+1) >= 99*(q+2) for q in range(100))
    return {'primary_source': 'https://web.math.pmf.unizg.hr/glasnik/46.1/46(1)-05.pdf',
            'source_location': 'Theorem 1.1, printed page 26; floor, not ceiling',
            'constructed_layers': 200, 'largest_checked_k': len(speeds),
            'first_covered_k_in_scan': next(r['k'] for r in records if r['meets_Dubickas_2011']),
            'last_uncovered_k_in_scan': max(r['k'] for r in records if not r['meets_Dubickas_2011']),
            'analytic_sufficient_cutoff': 494,
            'e_upper_bound_below_11_over_4': hi < Q(11,4),
            'records': records,
            'scope': 'Finite exact premise checks support a separate analytic inclusion proof. No claim of exhaustive priority coverage.'}


if __name__ == '__main__':
    result = run()
    Path(__file__).with_name('prior-art-checks.json').write_text(
        json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k != 'records'}, indent=2))
