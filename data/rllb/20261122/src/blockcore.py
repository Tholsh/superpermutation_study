"""Independent block-level Pantone/Halfar row and literal slice implementation.

Input: K-letter rows (x,v) for a complete (m,r) block, m+r=K.
Port and slice rules cross-checked against the supplied n10 implementation and
Halfar's public selection/gcore.py (same conventions).
"""
from __future__ import annotations
from collections import Counter
from dataclasses import dataclass
from itertools import permutations
from math import factorial
from typing import Iterable
ALPH='0123456789ABCDEFGHIJ'


def rot(x, j):
    n=len(x);j%=n;return x[j:]+x[:j]

def canon(x):
    return rot(x,x.index(0))

def gstep(x,v):
    K=len(x)
    if v==K:return x[1:-1]+x[:1]+x[-1:]
    if not 1<=v<=K-2:raise ValueError(f'unsupported G_v={v}')
    return x[v+1:]+x[:v-1]+x[v:v+1]+x[v-1:v]

def port(v,K):
    if v==K:return tuple((j-1)%(K-1) for j in range(K-1))
    if not 1<=v<=K-2:raise ValueError('invalid row grade')
    a=tuple(j+K-v-1 if j<v else (K-v-2 if j==v else j-v-1) for j in range(K-1))
    assert sorted(a)==list(range(K-1))
    return a

def block_loops(m,r):
    if m<3 or r<0:raise ValueError('invalid block dimensions')
    base=[tuple(range(m))]
    for t in range(m,m+r):
        base=[c[:i]+(t,)+c[i:] for c in base for i in range(1,len(c)+1)]
    ret=tuple(sorted(set(canon(c) for c in base)))
    assert len(ret)==factorial(m+r-1)//factorial(m-1)
    return ret

def load_selection(path,m=7,strict=True):
    data={};K=None
    for n,line in enumerate(open(path),1):
        if not line.strip() or line.lstrip().startswith('#'):continue
        parts=line.split()
        if len(parts)<2:raise ValueError(f'{path}:{n}: expected state visibility')
        a,v=parts[:2]
        try:x=tuple(ALPH.index(k) for k in a)
        except ValueError as e:raise ValueError(f'{path}:{n}: unknown letter: {e}')
        if K is None:K=len(x)
        if len(x)!=K or sorted(x)!=list(range(K)):
            raise ValueError(f'{path}:{n}: not a K={K} permutation')
        v={'D':0,'F':K,'S':K-2}.get(v,v)
        v=int(v)
        if v not in (0,K,*range(1,K-1)):
            raise ValueError(f'{path}:{n}: bad visibility {v}')
        c=canon(x)
        if c in data:raise ValueError(f'{path}:{n}: duplicate loop')
        if not v and x!=c:raise ValueError(f'{path}:{n}: detached loop must start with 0')
        data[c]=(x if v else c,v)
    if not data:raise ValueError('empty selection')
    if strict:
        wanted=set(block_loops(m,K-m))
        if set(data)!=wanted:
            extra=set(data)-wanted;missing=wanted-set(data)
            raise ValueError(f'wrong block membership: {len(extra)} outside, {len(missing)} missing; first extras={list(extra)[:2]}, first missing={list(missing)[:2]}')
    return data

def display(x):return ''.join(ALPH[t] for t in x)

def row_walks(data):
    chosen={x:v for x,v in data.values() if v}
    nxt={}
    for x,v in chosen.items():
        y=gstep(x,v)
        if y not in chosen:raise ValueError(f'unbalanced row step {display(x)} G_{v} -> {display(y)}, not a chosen state')
        nxt[x]=y
    indeg=Counter(nxt.values())
    if set(indeg)!=set(chosen) or any(indeg[x]!=1 for x in chosen):
        raise ValueError('not incidence-balanced: active row predecessor multiplicities are not one')
    ws=[];used=set()
    for x in chosen:
        if x in used:continue
        y=x;w=[]
        while y not in used:
            used.add(y);w.append(y);y=nxt[y]
        if y!=x:raise ValueError('row chain enters a previous closed walk')
        ws.append(w)
    return ws,chosen

def ncycles(perm):
    seen=set();c=0
    for i in range(len(perm)):
        if i not in seen:
            c+=1;j=i
            while j not in seen:
                seen.add(j);j=perm[j]
    return c

def block_metrics(data):
    K=len(next(iter(data)));ws,chosen=row_walks(data)
    D=sum(v==0 for x,v in data.values())
    Q=sum(K-v for v in chosen.values())
    walk_details=[];wc=0
    for walk in ws:
        p=list(range(K-1))
        for x in walk:
            q=port(chosen[x],K)
            p=[q[j] for j in p]
        ct=ncycles(p);wc+=ct
        walk_details.append(dict(rows=len(walk),charge=sum(K-chosen[x] for x in walk),trails=ct,port_permutation=p))
    if len(chosen)+D!=len(data):raise AssertionError('lost rows')
    return dict(K=K,n=K+2,block_classes=len(data),active=len(chosen),detached=D,charge=Q,
                walk_count=len(ws),walk_trails=wc,trails=wc+D,floor=Q+D+wc,
                rows_by_visibility=dict(Counter(v for x,v in data.values())),
                walk_details=walk_details)

def slices(data):
    K=len(next(iter(data)));s=K;z=K+1;H=K-1;N=K+2
    for L,(x,v) in data.items():
        if v:
            for j in range(K):
                b=x[:j]+(z,)+x[j:]
                c=v+(j<v)
                h=b[:H];t=rot(b,c+1)[:H]
                yield (h,t,b,s,c)
        for j in range(v,K):
            b=rot(x,j)+(s,);c=K+1
            yield (b[:H],rot(b,c+1)[:H],b,z,c)

def slice_piece(b,d,c):
    """Cyclic contribution with final H symbols omitted (exact Halfar/Pantone spelling)."""
    N=len(b)+1;H=N-3;bb=b+b
    return (b+(d,)+b+tuple(k for j in range(c-1) for k in (bb[j],d,*bb[j+1:j+N])))[:-H]

@dataclass
class Trail:
    trail_id:int
    cycle: bytes
    cuts: list[tuple[bytes,int]]
    is_small:bool
    loop:tuple[int,...]|None
    length:int


def build_trails(data, literal=True):
    """Build all block-local completed closed trails, including ALL detached loops.

    With literal=True produce cyclic letter string and every legal slice cut.
    The result need not itself be a whole n-superpermutation, because a block
    is only one part of a selection.
    """
    K=len(next(iter(data)));H=K-1;N=K+2;graph={};incoming=Counter();pieces={};pieces_len={}
    for head,tail,b,d,c in slices(data):
        if head in graph:raise ValueError(f'duplicate slice head {display(head)}')
        graph[head]=tail;incoming[tail]+=1
        pieces_len[head]=2*N-1+(c-1)*(N+1)-H
        if literal:pieces[head]=slice_piece(b,d,c)
    if set(graph)!=set(incoming) or any(incoming[k]!=1 for k in graph):
        raise ValueError('literal slice endpoint graph not balanced')
    expected=K*len(data)+sum(K-v for x,v in data.values() if v)
    if len(graph)!=expected:raise AssertionError(('slice count',len(graph),expected))
    rem=set(graph);out=[];trail_lengths=[]
    while rem:
        a=min(rem);v=a;heads=[]
        while v in rem:
            rem.remove(v);heads.append(v);v=graph[v]
        if v!=a:raise AssertionError('cycle not closed')
        if literal:
            vals=[pieces[h] for h in heads]
            cyclic=bytes(k for piece in vals for k in piece)
            offsets=[];off=0
            for piece,h in zip(vals,heads):
                assert cyclic[off:off+H]==bytes(h)
                offsets.append((bytes(h),off));off+=len(piece)
            assert cyclic[:H]==bytes(a)
        else:
            cyclic=b'';offsets=[(bytes(h),-1) for h in heads]
        is_small=len(heads)==K
        length=sum(pieces_len[h] for h in heads)
        if literal and len(cyclic)!=length:raise AssertionError((len(cyclic),length))
        out.append(Trail(len(out),cyclic,offsets,is_small,None,length))
    if len(out)!=block_metrics(data)['trails']:
        raise AssertionError('port-count and literal-count disagreement')
    if literal:
        assert len({h for t in out for h,o in t.cuts})==len(graph)
    return out
