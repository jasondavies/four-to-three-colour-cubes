"""Constructive candidate for all four-to-three cuboid thresholds.
The written proof, not the tests, supplies the universal guarantee.
"""
from pathlib import Path
import sys
from itertools import combinations, permutations
from collections import Counter
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'thin-cuboids'))
from geometry import SOURCES, MINIMAL, CS, ES, corners, REDUCTION, ROT, cyclic
from construct import TYPES, reduced


def threshold(a,b,c):
    assert 2 <= a <= b <= c
    return max(16*a-3,4*(a+b+c)-16,(24*c-1)//5)


def requirements(t,shape):
    out=Counter(('corner',k) for k in corners(t))
    for axis,length in enumerate(shape):
        u,v=[i for i in range(3) if i!=axis]
        for f in (2*u,2*u+1):
            for g in (2*v,2*v+1):
                out['edge',tuple(sorted((t[f],t[g])))]+=length-2
    return {r:n for r,n in out.items() if n}


def construct(shape,counts):
    a,b,c=shape;N=sum(counts)
    assert N>=threshold(a,b,c) and len(counts)==68
    x=reduced(counts)
    ords=[sum(x[i] for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==j) for j in (0,1)]
    missing={e:sum(x[i] for i in MINIMAL if TYPES[i]==('C',e)) for e in combinations(range(4),2)}
    z={v:sum(n for e,n in missing.items() if v in e) for v in range(4)}
    good=[v for v in range(4) if min(ords)+z[v]>=4 and sum(ords)+z[v]>=8]
    if good:
        for v in good:
            for u,w,t in permutations(set(range(4))-{v}):
                # Pairs uw,ut,wt run along c,b,a respectively.
                if missing[tuple(sorted((u,w)))]<=N-4*c and missing[tuple(sorted((u,t)))]<=N-4*b and missing[tuple(sorted((w,t)))]<=N-4*a:
                    return (u,u,w,w,t,t),'D'
        raise AssertionError(('D selection',shape,counts,ords,missing))
    majority=0 if ords[0]>=ords[1] else 1
    A=ords[majority];M=N-A
    assert M<=6 and A>=23 and max(missing.values())<=3
    for u in range(4):
        bucket=[i for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==majority and u in TYPES[i][2]]
        if sum(x[i] for i in bucket)>=4*a:
            chosen=[]
            for i in bucket:chosen.extend([i]*min(x[i],8-len(chosen)))
            freq={w:sum(cyclic((u,u,w)) in CS[i] for i in chosen) for w in range(4) if w!=u}
            # Repeated-colour cyclic class is the minimum of its rotations.
            eligible=[w for w,n in freq.items() if n>=4]
            assert len(eligible)>=2
            w,t=eligible[:2]
            return (w,t,u,u,u,u),'Q'
    ts={u:sum(x[i] for i in MINIMAL if TYPES[i][0]=='ordinary' and TYPES[i][1]==majority and TYPES[i][3] and u in TYPES[i][2]) for u in range(4)}
    assert sum(ts.values())>=16*a-14 and max(ts.values())<=4*a-1
    minorities=[i for i in MINIMAL if x[i] and (TYPES[i][0]=='C' or TYPES[i][1]!=majority)]
    assert minorities
    for u,w,t in permutations(range(4),3):
        if not any(set((u,w,t))==set(k) for i in minorities for k in CS[i] if len(set(k))==3):continue
        if ts[u]>=2*a and ts[w]>=b:
            return (w,t,u,u,u,w),'H-short'
    raise AssertionError(('no H supply',shape,N,ts,M,counts))


# Exact integral flow on a fixed-size graph; capacities keep large dimensions cheap.
def flow(adj,source,sink):
    result=0
    while True:
        levels=[-1]*len(adj);levels[source]=0;q=[source]
        for v in q:
            for w,cap,rev in adj[v]:
                if cap and levels[w]<0:levels[w]=levels[v]+1;q.append(w)
        if levels[sink]<0:return result
        pos=[0]*len(adj)
        def push(v,k):
            if v==sink:return k
            while pos[v]<len(adj[v]):
                edge=adj[v][pos[v]];w,cap,rev=edge
                if cap and levels[w]==levels[v]+1:
                    used=push(w,min(k,cap))
                    if used:edge[1]-=used;adj[w][rev][1]+=used;return used
                pos[v]+=1
            return 0
        while (n:=push(source,10**12)):result+=n


def matching(counts,demands,masks):
    k=len(demands);sink=69+k;adj=[[] for _ in range(sink+1)]
    def edge(a,b,c):
        adj[a].append([b,c,len(adj[b])]);adj[b].append([a,0,len(adj[a])-1])
    for i,n in enumerate(counts):
        if n:edge(0,i+1,n)
    for j,(n,mask) in enumerate(zip(demands,masks)):
        edge(69+j,sink,n)
        for i,c in enumerate(counts):
            if c and mask>>i&1:edge(i+1,69+j,n)
    return flow(adj,0,sink)==sum(demands)
