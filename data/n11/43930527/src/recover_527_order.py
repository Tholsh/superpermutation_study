#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Theo H.
"""Recover an exact 527 tiling from its witness; this is not the historical order search.
Build build/spra/reduced_codec first, as explained in REPRODUCE.md.
The output is written under build/rllb-records/, leaving saved record inputs alone.
"""
import csv, hashlib, importlib.util, lzma, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parents[4]
work=root/"build/rllb-records";work.mkdir(exist_ok=True)
codec=root/"build/spra/reduced_codec"
def decode(archive,destination):
    packed=lzma.decompress(archive.read_bytes())
    with destination.open("wb") as out:subprocess.run([str(codec),"decode"],input=packed,stdout=out,check=True)
    return destination.read_bytes()
source=decode(root/"data/n11/43930529/inputs/n11_43930543.spra.xz",work/"precursor.txt")
assert hashlib.sha256(source).hexdigest()=="1089c8f86fbe08c5a85093db053056be63fc124740da3d840a0e8ab710d98917"
word=decode(root/"SPRA/words/11/43930527/superpermutation-11-43930527.spra.xz",work/"canonical-527.txt").translate(bytes.maketrans(b"123456789AB",b"2053618479A"))
assert hashlib.sha256(word).hexdigest()=="8b78860eebb7d25ffbf1147b6609d5c156e2fed2e0a16c5a23ad949cc0b5825c"
spec=importlib.util.spec_from_file_location("joint",root/"data/n11/43930529/src/joint_50unit_search.py")
joint=importlib.util.module_from_spec(spec);sys.modules["joint"]=joint;spec.loader.exec_module(joint)
with (root/"data/n11/43930529/inputs/n11_43930543_fiber_manifest.csv").open() as f:manifest=list(csv.DictReader(f))
optimizer=joint.Optimizer(source,manifest)
lookup={}
for unit,modes in optimizer.modes.items():
    for mode in modes:
        piece=optimizer.word(unit,mode)
        lookup.setdefault(piece[:64],[]).append((unit,mode,piece))
seen=set();failures=set()
def recover(end,mask,rows):
    if len(rows)==50:return rows if end==len(word) else None
    state=(end,mask)
    if state in failures:return None
    for overlap in (range(0,1) if not rows else range(10,-1,-1)):
        start=end-overlap
        if start<0:continue
        for unit,mode,piece in lookup.get(word[start:start+64],[]):
            if mask&(1<<unit):continue
            stop=start+len(piece)
            if word[start:stop]!=piece:continue
            row=dict(position=len(rows),unit_id=unit,kind="fiber" if mode.source>=0 else ("core1" if mode.source==-1 else "core2"),target_fiber_index=optimizer.fiber_id(unit),target_old_cycle=optimizer.D[optimizer.fiber_id(unit)] if mode.source>=0 else "",source_fiber_index=mode.source if mode.source>=0 else "",source_old_cycle=optimizer.D[mode.source] if mode.source>=0 else "",shift=mode.shift,swap78=mode.swap,start=start,end=stop,word_length=len(piece),join_overlap=overlap)
            result=recover(stop,mask|(1<<unit),rows+[row])
            if result is not None:return result
    failures.add(state)
    return None
rows=recover(0,0,[])
if rows is None:raise RuntimeError("527 is not tiled by the supplied 543 template family")
out=work/"recovered_527_order.tsv";out.parent.mkdir(parents=True,exist_ok=True)
with out.open("w",newline="") as f:
    writer=csv.DictWriter(f,fieldnames=list(rows[0]),delimiter="\t");writer.writeheader();writer.writerows(rows)
print("Recovered",len(rows),"units; overlap sum",sum(r["join_overlap"] for r in rows),"hash",hashlib.sha256(word).hexdigest())
print(out)
