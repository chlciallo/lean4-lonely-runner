"""Exact interval-union checks for the compatible sum-triple theorem.

The universal statement and sharpness are checked by Lean, not inferred from this grid.
"""
from fractions import Fraction as Q
import json


def floor(x):
    return x.numerator // x.denominator


def components(delta, rho, y, z=None, lo=Q(-2), hi=Q(2)):
    if z is None:
        z = y  # after setting the slow phase to zero, compatibility means z=y
    intervals = []
    for v, phase in [(Q(1), Q(0)), (rho, y), (rho+1, z)]:
        for n in range(floor(v*lo+phase)-2, floor(v*hi+phase)+3):
            l, r = (n-delta-phase)/v, (n+delta-phase)/v
            if r > lo and l < hi:
                intervals.append((l, r))
    intervals.sort()
    merged = []
    for l, r in intervals:
        # Strict overlap: a touching boundary is a legitimate safe time.
        if merged and l < merged[-1][1]:
            merged[-1] = (merged[-1][0], max(r, merged[-1][1]))
        else:
            merged.append((l, r))
    return [(l, r) for l, r in merged if lo < l and r < hi]


def constant(delta):
    return max(5*delta/2, delta*(1+2*delta)/(1-4*delta))


def run():
    count, worst = 0, Q(0)
    for delta in (Q(j, 144) for j in range(1, 25)):
        C = constant(delta)
        for rho in (Q(j, 8) for j in range(8, 65)):
            for y in (Q(j, 16) for j in range(16)):
                blocks = components(delta, rho, y)
                assert blocks
                for l, r in blocks:
                    assert r-l <= 2*C, (delta, rho, y, l, r, C)
                    worst = max(worst, (r-l)/(2*C))
                count += 1
    near_sharp = []
    for delta in [Q(1, 6), Q(1, 7), Q(1, 8), Q(1, 12), Q(1, 24)]:
        C = constant(delta)
        for N in [10, 100, 1000]:
            if delta >= Q(1, 8):
                rho = (1-4*delta)/(2*delta) + Q(1, N)
                blocks = components(delta, rho, Q(1, 2))
                l, r = next((l, r) for l, r in blocks if l < 0 < r)
                assert (l, r) == (-(Q(1, 2)+delta)/rho, (Q(1, 2)+delta)/rho)
            else:
                rho = Q(1)
                D = 3*delta - delta/N
                l, r = next((l, r) for l, r in components(delta, rho, -D) if l < 0 < r)
                assert (l, r) == (-delta, D+delta)
            near_sharp.append({'delta': str(delta), 'N': N,
                               'ratio_to_optimum': str((r-l)/(2*C))})
    # Deliberately drop phase compatibility. The claimed constant then fails.
    delta, rho, y, z = Q(1, 9), Q(9, 8), Q(1, 12), Q(7, 12)
    l, r = max(components(delta, rho, y, z), key=lambda lr: lr[1]-lr[0])
    assert r-l > 2*constant(delta)
    print(json.dumps({'exact_parameter_cases': count,
        'largest_observed_ratio_to_bound': str(worst),
        'near_sharp_families': near_sharp,
        'incompatible_phase_counterexample': {
            'delta': str(delta), 'speeds': ['1', str(rho), str(rho+1)],
            'phases': ['0', str(y), str(z)], 'bad_component': [str(l), str(r)],
            'reference_time': str((l+r)/2), 'half_width': str((r-l)/2),
            'invalid_proposed_radius': str(constant(delta))},
        'scope': 'Exact open-interval union on (-2,2); grid checks are finite. Universal optimum is separately proved in Lean.'}, indent=2))


if __name__ == '__main__':
    run()
