"""Proper cube rotations and cyclic corner types used by the data generator."""
import itertools
import math

def require(condition,message):
    if not condition: raise ValueError(message)


def cyclic(t):
    return min(t,t[1:]+t[:1],t[2:]+t[:2])


def rotations():
    result=[]
    for p in itertools.permutations(range(3)):
        parity=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
        for signs in itertools.product((-1,1),repeat=3):
            if parity*math.prod(signs)!=1: continue
            move=[None]*6
            for i in range(3):
                for s in (-1,1):
                    source=2*i+(s<0); dest=2*p[i]+(s*signs[i]<0)
                    move[dest]=source
            result.append(tuple(move))
    require(len(set(result))==24,'Expected 24 proper rotations')
    return sorted(result)


ROT=rotations()
POSITIONS=list(itertools.product((0,1),repeat=3))
FACES=[tuple(2*i+p[i] for i in range(3)) for p in POSITIONS]


def rotate(cube,r): return tuple(cube[i] for i in r)
def canonical(cube): return min(rotate(cube,r) for r in ROT)


def corners(cube):
    result=[]
    for p,faces in zip(POSITIONS,FACES):
        values=tuple(cube[i] for i in faces)
        if sum(p)%2: values=(values[0],values[2],values[1])
        result.append(cyclic(values))
    return tuple(result)


