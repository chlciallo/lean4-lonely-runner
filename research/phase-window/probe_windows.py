"""Exact rational tests of local hitting radii, not a proof of a universal theorem."""
from fractions import Fraction as Q
from itertools import product
import json

def floor(x):
    return x.numerator // x.denominator

def dist(x):
    r = x % 1
    return min(r, 1-r)

def bad_components(a, b, alpha, beta, x, y, lo=Q(-2), hi=Q(2)):
    intervals = []
    for v, d, phase in [(a, alpha, x), (b, beta, y)]:
        for n in range(floor(v*lo+phase)-2, floor(v*hi+phase)+3):
            l, r = (n-d-phase)/v, (n+d-phase)/v
            if r > lo and l < hi:
                intervals.append((l, r))
    intervals.sort()
    merged = []
    for l, r in intervals:
        # Open intervals that only touch have a SAFE endpoint between them.
        if merged and l < merged[-1][1]:
            merged[-1] = (merged[-1][0], max(r, merged[-1][1]))
        else:
            merged.append((l, r))
    return [(l,r) for l,r in merged if lo < l and r < hi]

def constant(alpha, beta):
    return max(alpha+beta, alpha*(1+2*beta)/(1-2*beta))

def run():
    count = 0
    worst = Q(0)
    thresholds = [(Q(i,24),Q(j,24)) for i in range(1,12) for j in range(1,12) if i+j<=12]
    for alpha,beta in thresholds:
        C=constant(alpha,beta)
        for a,b in [(Q(1),Q(j,8)) for j in range(8,65)]:
            for y in [Q(j,12) for j in range(12)]:
                # Translation sets phase of the slower runner to zero.
                for l,r in bad_components(a,b,alpha,beta,Q(0),y):
                    assert a*(r-l)<=2*C,(a,b,alpha,beta,y,l,r,C)
                    worst=max(worst,a*(r-l)/(2*C))
                count+=1
    counter = bad_components(Q(3),Q(5),Q(1,5),Q(1,5),Q(0),Q(1,2))
    component=next((l,r) for l,r in counter if l<0<r)
    assert component == (Q(-7,50),Q(7,50))
    assert Q(7,50)>2*Q(1,5)/3
    assert all(min(dist(Q((2*j+1)*v,16)) for v in [3,5,8])<Q(1,4) for j in range(8))
    print(json.dumps({'exact_parameter_cases':count, 'largest_observed_ratio_to_bound':str(worst),
                      'equal_threshold_1_5_counterexample_component':list(map(str,component)),
                      'fixed_core_phase_counterexample':[3,5,8],
                      'scope':'Finite exact rational cross-checks; the general theorem and optimality are proved separately in Lean.'},indent=2))

if __name__=='__main__':
    run()
