#!/usr/bin/env python3
"""Generate position tags for frame constructions; Lean checks every tag."""
from itertools import product
from pathlib import Path
from cube_geometry import canonical, corners, ROT
S=sorted({canonical(c) for c in product(range(4),repeat=6) if len(set(c))==4})
T=sorted({canonical(c) for c in product(range(4),repeat=6) if len(set(c))==3})
E=[(f,g) for f in range(6) for g in range(f+1,6) if f//2!=g//2]
plus={(0,1,2),(0,3,1),(0,2,3),(1,3,2)}
def vec(xs):return '!['+', '.join(map(str,xs))+']'
def tab(shape,fn,args=()):
    return str(fn(*args)) if not shape else vec(tab(shape[1:],fn,args+(i,)) for i in range(shape[0]))
def q(a,b,c): return canonical((b,c,a,a,a,a)) if len({a,b,c})==3 else T[0]
def u(a,b,c): return canonical((a,b,a,b,a,c)) if len({a,b,c})==3 else T[0]
def d(a):return canonical(tuple(x for x in range(4) if x!=a for _ in range(2)))
def qt(a,b,c):
    return vec(0 if b in t else 1 for t in corners(q(a,b,c)))
def qe(a,b,c):return vec(2 if q(a,b,c)[f]==q(a,b,c)[g]==a else 3 for f,g in E)
def dt(a):return vec(0 if t in plus else 1 for t in corners(d(a)))
def de(a):
    pairs=sorted({tuple(sorted((d(a)[f],d(a)[g]))) for f,g in E})
    return vec(2+pairs.index(tuple(sorted((d(a)[f],d(a)[g])))) for f,g in E)
def ut(a,b,c,s):
    return vec(0 if t.count(a)>=2 else 1 if t.count(b)>=2 else 3 if ((t in plus)==(s==0)) else 2 for t in corners(u(a,b,c)))
def ue(a,b,c):return vec(0 if u(a,b,c)[f]==u(a,b,c)[g]==a else 1 if u(a,b,c)[f]==u(a,b,c)[g]==b else 3 for f,g in E)
lines=['module','public import ThreeColour.FrameDefs','@[expose] public section','namespace ThreeColour']
for name,shape,ret,fn in [
 ('edgeRotation',[24],'Fin 12 → Fin 12',lambda r:vec(E.index(tuple(sorted((ROT[r][f],ROT[r][g])))) for f,g in E)),
 ('uTarget',[4,4,4],'Target',lambda a,b,c:T.index(u(a,b,c))),
 ('qCornerTag',[4,4,4],'Slot → Fin 4',qt),('qEdgeTag',[4,4,4],'Fin 12 → Fin 4',qe),
 ('dEdgeRepresentative',[4],'Fin 3 → Fin 12',lambda a: vec(next(i for i in range(12) if 2+j==int(de(a)[2:-1].split(', ')[i])) for j in range(3))),
 ('checkerFrameOmitted',[6],'Colour',lambda j: sorted(set(range(4))-{a for a in range(4) if S[[i for i in range(68) if all(len(set(t))==3 for t in corners(S[i]))][j]].count(a)==2})[0]),
 ('dCornerTag',[4],'Slot → Fin 5',dt),('dEdgeTag',[4],'Fin 12 → Fin 5',de),
 ('uCornerTag',[4,4,4,2],'Slot → Fin 4',ut),('uEdgeTag',[4,4,4],'Fin 12 → Fin 4',ue)]:
    lines.append('def '+name+' : '+''.join(f'Fin {n} → ' for n in shape)+ret+' := '+tab(shape,fn))
lines.append('end ThreeColour')
(Path(__file__).resolve().parents[1]/'ThreeColour'/'FrameData.lean').write_text('\n\n'.join(lines)+'\n')
