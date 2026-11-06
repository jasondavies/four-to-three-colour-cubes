"""Construct a rod target using the written proof, then find its placement matching."""
from itertools import combinations
from collections import Counter
from geometry import SOURCES,MINIMAL,REDUCTION,CS,ES,cyclic,matches
PLUS={(0,1,2),(0,3,1),(0,2,3),(1,3,2)}
TYPES={}
for i in MINIMAL:
    tri={k for k in CS[i] if len(set(k))==3}
    bucket={a for a in range(4) if (a,a) in ES[i]}
    if not bucket:
        missing=next(iter(set(combinations(range(4),2))-ES[i]))
        TYPES[i]=('C',missing)
    else:
        assert tri in (PLUS,{cyclic((a,c,b)) for a,b,c in PLUS})
        TYPES[i]=('ordinary',0 if tri==PLUS else 1,bucket,max(Counter(SOURCES[i]).values())==3)

def threshold(c):
    assert c>=2
    return max(29,(24*c-1)//5)

def reduced(counts):
    out=[0]*68
    for i,n in enumerate(counts):out[REDUCTION[i]]+=n
    return out

def target(c,counts):
    assert c>=2 and len(counts)==68 and sum(counts)>=threshold(c)
    x=reduced(counts);N=sum(x);L=4*c;s=N-L
    assert s>=5 and N<=6*s+5
    ordinary=[sum(x[i] for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==j) for j in (0,1)]
    missing={e:sum(x[i] for i in MINIMAL if TYPES[i]==('C',e)) for e in combinations(range(4),2)}
    degree={v:sum(n for e,n in missing.items() if v in e) for v in range(4)}
    A,B=sorted(ordinary,reverse=True)
    good=[v for v in range(4) if A+degree[v]>=4 and B+degree[v]>=4 and A+B+degree[v]>=8]
    if good:
        for v in good:
            others=set(range(4))-{v}
            for a,b in combinations(sorted(others),2):
                if missing[a,b]<=s:
                    d=next(iter(others-{a,b}))
                    return (a,a,b,b,d,d),'D'
        raise AssertionError('Heavy-pair propagation should produce a usable D target')
    majority=0 if ordinary[0]>=ordinary[1] else 1
    A=ordinary[majority]
    assert A>=N-6 and max(missing.values())<=3
    for a in range(4):
        bucket=[i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==majority and a in TYPES[i][2]]
        if sum(x[i] for i in bucket)>=8:
            # Select eight physical copies, then use their two frequent aax types.
            chosen=[]
            for i in bucket:chosen.extend([i]*min(x[i],8-len(chosen)))
            freq={b:sum(cyclic((a,a,b)) in CS[i] for i in chosen) for b in range(4) if b!=a}
            eligible=[b for b in freq if freq[b]>=4]
            assert len(eligible)>=2
            b,d=eligible[:2]
            return (a,a,b,d,a,a),'Q'
    ts={a:sum(x[i] for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==majority and TYPES[i][3] and a in TYPES[i][2]) for a in range(4)}
    assert sum(ts.values())>=18 and max(ts.values())>=5
    a=max(ts,key=ts.get)
    minority=next(i for i in MINIMAL if x[i] and (TYPES[i][0]=='C' or TYPES[i][1]!=majority))
    minority_tri=[set(k) for k in CS[minority] if len(set(k))==3 and a in k]
    for triple in minority_tri:
        for b in sorted(triple-{a}):
            if ts[b]>=2:
                d=next(iter(triple-{a,b}))
                return (a,a,b,d,a,b),'H'
    raise AssertionError('The minority source and T counts should supply an H target')
