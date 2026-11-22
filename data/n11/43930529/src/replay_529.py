#!/usr/bin/env python3
"""Literal n=11 43,930,529 reproduction from precursor and recovered order.

No access to the 529 witness is required for construction: the complete word is
assembled from 543 literal source, its fiber manifest, and recovered 50-unit TSV.
Historical optimizer table IDs may differ because many templates are identical.
"""
from __future__ import annotations
import argparse, csv, hashlib
from pathlib import Path

EXPECTED_LEN=43_930_529
EXPECTED_SHA='3743ea507d76b8f907b8f2ddba0f9825b5ee62159e609b0c5a4dfe30fa8d34be'
CORE_SPANS={'core1':(2197740,23690189),'core2':(24239625,43747396)}


def replay(source:Path,manifest:Path,order_file:Path,output:Path)->dict:
    precursor=source.read_bytes()
    if len(precursor)!=43_930_543:raise ValueError('543 source length mismatch')
    with manifest.open() as fh:meta=list(csv.DictReader(fh))
    with order_file.open() as fh:units=list(csv.DictReader(fh,delimiter='\t'))
    if len(meta)!=48 or len(units)!=50:raise ValueError('expected 48 fibers and 50 units')
    ds=[x['old_cycle_D'] for x in meta]
    if len(set(ds))!=48:raise ValueError('old-letter class duplicates')
    source_blocks=[precursor[int(x['start_0based_inclusive']):int(x['end_0based_exclusive'])] for x in meta]
    output.parent.mkdir(parents=True,exist_ok=True)
    digest=hashlib.sha256();current_length=0;overlap_sum=0;last_suffix=b''
    with output.open('wb') as fh:
        for p,x in enumerate(units):
            if int(x['position'])!=p:raise ValueError('bad unit order')
            if x['kind']=='fiber':
                src=int(x['source_fiber_index']);tar=int(x['target_fiber_index'])
                old=ds[src];new=ds[tar];shift=int(x['shift']);swap=int(x['swap78'])
                if x['target_old_cycle']!=new:raise ValueError('wrong target cycle')
                mapped=''.join(new[(k+shift)%7] for k in range(7))+('87' if swap else '78')
                tbl=bytes.maketrans((old+'78').encode(),mapped.encode())
                w=source_blocks[src].translate(tbl)
            else:
                a,b=CORE_SPANS[x['kind']];w=precursor[a:b]
            if len(w)!=int(x['word_length']):raise ValueError(f'length discrepancy at unit {p}')
            if int(x['start'])!=current_length-int(x['join_overlap']):raise ValueError(f'start mismatch at unit {p}')
            ov=int(x['join_overlap']);overlap_sum+=ov
            if not (0<=ov<=10):raise ValueError('join overlap is outside 0..10')
            if ov and last_suffix[-ov:]!=w[:ov]:raise ValueError('overlap mismatch')
            nonoverlap=w[ov:];fh.write(nonoverlap);digest.update(nonoverlap)
            current_length+=len(nonoverlap);last_suffix=w[-10:]
            if current_length!=int(x['end']):raise ValueError(f'end mismatch at unit {p}')
    if current_length!=EXPECTED_LEN or digest.hexdigest()!=EXPECTED_SHA:
        raise ValueError(f'replay mismatch length={current_length} sha={digest.hexdigest()}')
    return {'len':current_length,'sha256':digest.hexdigest(),'units':len(units),'join_overlap':overlap_sum}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,required=True,help='decoded n11 43,930,543 precursor')
    ap.add_argument('--manifest',type=Path,required=True)
    ap.add_argument('--plan',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();print('REPLAY PASS',replay(a.source,a.manifest,a.plan,a.out))
