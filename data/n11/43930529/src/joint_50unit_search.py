#!/usr/bin/env python3
"""Fresh replacement for the lost 529 placement-search program.

Search 50 full n11 units with *joint*, exact fixed-order min-plus optimization
of source fiber selection, cyclic old-letter relabeling phase and 7<->8 swap.
The 2 original core sections stay literal and anchored in their order slots.
When placement changes, the complete phase/template DP is recalculated.

Provenance: NEW implementation from recovered interface rules, not the lost
historical `block_order_dp_long.cpp`. It can explore new proposals, and its
results must be checked by the independent factorial permutation verifier.
"""
from __future__ import annotations
from collections import namedtuple
from pathlib import Path
import argparse,csv,json,random,time

Mode=namedtuple('Mode','length head tail source shift swap')
CORE_SPANS={'core1':(2197740,23690189),'core2':(24239625,43747396)}

class Optimizer:
    def __init__(self,precursor:bytes,manifest:list[dict]):
        if len(precursor)!=43_930_543 or len(manifest)!=48:raise ValueError('invalid precursor/manifest')
        self.precursor=precursor
        self.D=[x['old_cycle_D'] for x in manifest]
        self.source=[precursor[int(x['start_0based_inclusive']):int(x['end_0based_exclusive'])] for x in manifest]
        self.modes={}
        for target in range(48):
            modes={}
            for src,ds in enumerate(self.D):
                w=self.source[src]
                for shift in range(7):
                    for sw in (0,1):
                        t=bytes.maketrans((ds+'78').encode(),(''.join(self.D[target][(k+shift)%7] for k in range(7))+('87' if sw else '78')).encode())
                        head=w[:10].translate(t);tail=w[-10:].translate(t)
                        z=Mode(len(w),head,tail,src,shift,sw)
                        # If two templates have equal length+boundaries, they
                        # are interchangeable for the *connection* objective;
                        # preserve one representative for literal assembly.
                        key=(z.length,z.head,z.tail)
                        if key not in modes or z.source==target:modes[key]=z
            self.modes[self.original_id(target)]=list(modes.values())
        self.modes[36]=[Mode(CORE_SPANS['core1'][1]-CORE_SPANS['core1'][0],
              precursor[CORE_SPANS['core1'][0]:CORE_SPANS['core1'][0]+10],
              precursor[CORE_SPANS['core1'][1]-10:CORE_SPANS['core1'][1]],-1,0,0)]
        self.modes[46]=[Mode(CORE_SPANS['core2'][1]-CORE_SPANS['core2'][0],
              precursor[CORE_SPANS['core2'][0]:CORE_SPANS['core2'][0]+10],
              precursor[CORE_SPANS['core2'][1]-10:CORE_SPANS['core2'][1]],-2,0,0)]
        assert len(self.modes)==50
    @staticmethod
    def original_id(fi):return fi+(fi>=36)+(fi>=45)
    @staticmethod
    def fiber_id(unit):
        if unit in (36,46):return None
        return unit-(unit>36)-(unit>46)
    def word(self,unit,mode):
        if mode.source<0:
            a,b=CORE_SPANS['core1' if mode.source==-1 else 'core2']
            return self.precursor[a:b]
        tar=self.fiber_id(unit);old=self.D[mode.source];new=self.D[tar]
        t=bytes.maketrans((old+'78').encode(),(''.join(new[(k+mode.shift)%7] for k in range(7))+('87' if mode.swap else '78')).encode())
        w=self.source[mode.source].translate(t)
        assert len(w)==mode.length and w[:10]==mode.head and w[-10:]==mode.tail
        return w
    def evaluate(self,order:list[int],materialize=False):
        if len(order)!=50 or set(order)!=set(range(50)):raise ValueError('not a 50-unit permutation')
        prev_modes=self.modes[order[0]];costs=[v.length for v in prev_modes]
        backs=[]
        for unit in order[1:]:
            nxt=self.modes[unit]
            by_suffix=[{} for _ in range(11)]
            minprev=min(range(len(costs)),key=costs.__getitem__)
            for j,p in enumerate(prev_modes):
                for k in range(1,11):
                    key=p.tail[-k:];entry=by_suffix[k].get(key)
                    if entry is None or costs[j]<entry[0]:by_suffix[k][key]=(costs[j],j)
            next_cost=[];parent=[]
            for item in nxt:
                best=costs[minprev]+item.length;idx=minprev;overlap=0
                for k in range(1,11):
                    t=by_suffix[k].get(item.head[:k])
                    if t is not None and t[0]+item.length-k<best:
                        best=t[0]+item.length-k;idx=t[1];overlap=k
                next_cost.append(best);parent.append((idx,overlap))
            costs=next_cost;prev_modes=nxt;backs.append(parent)
        ix=min(range(len(costs)),key=costs.__getitem__);total=costs[ix]
        if not materialize:return total
        indices=[None]*50;overlaps=[0]*50;indices[-1]=ix
        for j in range(49,0,-1):
            indices[j-1],overlaps[j]=backs[j-1][indices[j]]
        modes=[self.modes[u][v] for u,v in zip(order,indices)]
        return total,modes,overlaps
    def write(self,order,out_prefix):
        total,modes,ovs=self.evaluate(order,True)
        output=Path(str(out_prefix)+'.txt');plan=Path(str(out_prefix)+'.tsv')
        output.parent.mkdir(parents=True,exist_ok=True)
        data=bytearray();rows=[]
        for position,(unit,mode,ov) in enumerate(zip(order,modes,ovs)):
            w=self.word(unit,mode)
            if ov and data[-ov:]!=w[:ov]:raise ValueError('invalid saved phase')
            data+=w[ov:]
            rows.append({'position':position,'unit_id':unit,'target_fiber_index':self.fiber_id(unit),
             'source_fiber_index':mode.source,'shift':mode.shift,'swap78':mode.swap,
             'word_length':mode.length,'join_overlap':ov})
        if len(data)!=total:raise ValueError(f'length mismatch {len(data)} vs {total}')
        output.write_bytes(data)
        with plan.open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=list(rows[0]),delimiter='\t');w.writeheader();w.writerows(rows)
        print('WROTE',total,output,plan)
        return output


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--manifest',type=Path,required=True)
    p.add_argument('--order',type=Path,required=True,help='recovered 529 TSV')
    p.add_argument('--iterations',type=int,default=0,help='nonzero enables heuristic placement moves')
    p.add_argument('--seed',type=int,default=529)
    p.add_argument('--out-prefix',type=Path,default=None)
    a=p.parse_args()
    with a.manifest.open() as f:meta=list(csv.DictReader(f))
    with a.order.open() as f:rows=list(csv.DictReader(f,delimiter='\t'))
    order=[int(x['unit_id']) for x in rows];opt=Optimizer(a.source.read_bytes(),meta)
    t0=time.monotonic();baseline=opt.evaluate(order);best=baseline
    print('BASELINE fixed-order optimal selection+phase cost',baseline,'modes per fiber',len(opt.modes[0]),flush=True)
    rng=random.Random(a.seed);bestorder=order[:]
    slot_positions=[i for i,x in enumerate(order) if x not in (36,46)]
    for it in range(a.iterations):
        trial=bestorder[:]
        pos1,pos2=rng.sample(slot_positions,2)
        if it%3==0:trial[pos1],trial[pos2]=trial[pos2],trial[pos1]
        else:
            group=[trial[i] for i in slot_positions];i=slot_positions.index(pos1);j=slot_positions.index(pos2)
            item=group.pop(i);group.insert(j,item)
            for k,v in zip(slot_positions,group):trial[k]=v
        val=opt.evaluate(trial)
        if val<best:
            best=val;bestorder=trial
            print('IMPROVED',it,'length',best,'elapsed',round(time.monotonic()-t0,2),flush=True)
        if it%25==0:print('ITER',it,'current best',best,flush=True)
    print('DONE best=',best,'starting=',baseline,'iterations=',a.iterations,flush=True)
    if a.out_prefix:opt.write(bestorder,a.out_prefix)
if __name__=='__main__':main()
