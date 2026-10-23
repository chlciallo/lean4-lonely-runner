"""Explore the missing core-guard hypothesis with exact interval arithmetic."""
from fractions import Fraction as Q
from itertools import combinations
from math import gcd
import argparse
import json

def intersection(A,B):
    i=j=0
    out=[]
    while i<len(A) and j<len(B):
        l=max(A[i][0],B[j][0]); r=min(A[i][1],B[j][1])
        if l<=r: out.append((l,r))
        if A[i][1]<B[j][1]: i+=1
        else: j+=1
    return out

def safe_intervals(v,delta):
    return [(Q(i, v)+delta/v,Q(i+1,v)-delta/v) for i in range(v)]

def core_intervals(U,delta):
    A=[(Q(0),Q(1))]
    for v in U:
        A=intersection(A,safe_intervals(v,delta))
        if not A: break
    return A

def dist(x):
    f=x%1
    return min(f,1-f)

def capacity(A,d):
    best=Q(-1); at=None
    for l,r in A:
        candidates=[l,r]
        # Include all maxima of this triangular wave in the interval.
        for j in range((2*d*l).__floor__()-1,(2*d*r).__floor__()+2):
            if j%2:
                t=Q(j,2*d)
                if l<=t<=r:candidates.append(t)
        for t in candidates:
            value=dist(d*t)
            if value>best:best,at=value,t
    return best,at

def run(m,limit):
    delta=Q(1,m+3)
    best=None
    checked=0
    tight=[]
    counter=None
    for U in combinations(range(1,limit+1),m):
        if gcd(*U)>1:continue
        A=core_intervals(U,delta)
        assert A,(U,delta)
        for d in U:
            val,t=capacity(A,d)
            checked+=1
            if best is None or val<best[0]:best=(val,U,d,t)
            if val==2*delta and len(tight)<20:tight.append((U,d,str(t)))
            if val<2*delta:counter=(U,d,str(val),str(t));break
        if counter:break
    return {'core_size':m,'max_speed':limit,'marked_cases':checked,
            'threshold':str(delta),'guard_target':str(2*delta),
            'minimum_capacity':str(best[0]),'minimizer':best[1],'marked_speed':best[2],
            'maximizing_time':str(best[3]),'tight_samples':tight,'counterexample':counter,
            'scope':'Bounded exact search of the extra guard, not a proof of a universal mixed statement.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--size',type=int,default=3);p.add_argument('--limit',type=int,default=25)
    args=p.parse_args()
    print(json.dumps(run(args.size,args.limit),indent=2))
