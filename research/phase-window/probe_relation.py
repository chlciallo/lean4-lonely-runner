"""Exact search for the relation-aware local theorem and a false weakening."""
from fractions import Fraction as Q
import json
from probe_windows import dist, floor

def local_witness(a,b,d,x,y,t,R):
    candidates={t,t-R,t+R}
    for speed,phase in [(a,x),(b,y)]:
        for n in range(floor(speed*(t-R)+phase)-1,floor(speed*(t+R)+phase)+2):
            for sign in [-1,1]:
                s=(n+sign*d-phase)/speed
                if abs(s-t)<=R:
                    candidates.add(s)
    # Safety changes only at these exact rational endpoints.
    good=[s for s in candidates if dist(a*s+x)>=d and dist(b*s+y)>=d]
    return min(good,key=lambda s:(abs(s-t),s)) if good else None

def run():
    checked=0
    guard_passed=0
    for n in range(4,21):
        d=Q(1,n)
        for rho in [Q(j,8) for j in range(8,41)]:
            threshold=2*d+abs(rho-1)*d
            for ix in range(12):
                for iy in range(12):
                    x,y=Q(ix,12),Q(iy,12)
                    checked+=1
                    if dist(y-x)<threshold:
                        continue
                    guard_passed+=1
                    assert local_witness(Q(1),rho,d,x,y,Q(0),d) is not None,(n,rho,x,y)
    assert dist(3*Q(1,2))>=Q(1,3)
    assert local_witness(Q(2),Q(5),Q(1,6),Q(0),Q(0),Q(1,2),Q(1,12)) is None
    core=[1,2,3]
    a,b,d,t,M=Q(6),Q(8),Q(1,6),Q(1,4),Q(3)
    assert all(dist(v*t)>=d+M*d/a for v in core)
    assert dist((b-a)*t)>=2*d+(b-a)*d/a
    witness=local_witness(a,b,d,Q(0),Q(0),t,d/a)
    assert witness is not None and all(dist(v*witness)>=d for v in core)
    print(json.dumps({'parameter_cases':checked,'cases_satisfying_relation_guard':guard_passed,
                      'witness_example':{'speeds':[1,2,3,6,8],'core_time':str(t),'lifted_time':str(witness)},
                      'drift_term_counterexample':{'speeds':[2,5],'time':'1/2','delta':'1/6','radius':'1/12'},
                      'scope':'Exact finite cross-check; general relation escape and descent are proved in Lean.'},indent=2))

if __name__=='__main__':
    run()
