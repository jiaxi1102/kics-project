#!/usr/bin/env python3
from __future__ import annotations
import json, pathlib, re, subprocess
from dataclasses import dataclass, asdict
from typing import Any
ROOT=pathlib.Path(__file__).resolve().parent; WORK=ROOT/'_work'
SOURCE=WORK/'LeanOpenProblems'; RESULTS=WORK/'LeanOpenProblems-results'; OUT=ROOT/'unsolved_candidates.json'
RUNS=['oeis-full-50usd-ant-j0j0g4uzligm1k41','oeis-full-50usd-oai-jajpvieznaevpoyg','oeis-full-50usd-gdm-1s7vwp2si1ap0r6d']
def sh(*a,cwd=None): return subprocess.check_output(a,cwd=cwd,text=True).strip()
def clone(url,path):
 subprocess.run(['rm','-rf',str(path)],check=True); subprocess.run(['git','clone','--depth','1',url,str(path)],check=True)
def score(path):
 try:return json.loads(path.read_text()).get('proof_scorer',{}).get('value')
 except:return None
def srcfile(name):
 base=SOURCE/'apn/data/oeis/Isolated'; exact=base/f'{name}.lean'
 if exact.exists():return exact
 rx=re.compile(rf'\b(?:theorem|def)\s+{re.escape(name)}\b')
 for p in sorted(base.glob('*.lean')):
  if rx.search(p.read_text(errors='replace')): return p
 return None
def heuristic(c,code):
 s=(c+'\n'+code).lower(); z=0
 for k,v in {'only':5,'never':5,'squarefree':5,'eventually periodic':5,'divisible':3,'congru':2,'recurrence':4,'xor':4,'digit':4,'finite':3,'verified up to':2,'bounded':2,'∀':2,'iff':2}.items(): z+=v*(k in s)
 for k,v in {'infinitely many primes':10,'prime gap':10,'collatz':12,'riemann':20,'density':7,'limsup':7,'tendsto':7,'asymptotic':7,'irreducible':5,'supercongru':6,'bernoulli':5,'hankel':5,'determinant':4,'infinitely':7}.items(): z-=v*(k in s)
 if re.search(r'≤\s*\d{1,8}|<\s*\d{1,8}',code):z+=4
 if 'noncomputable def' in code:z-=2
 z += 2 if len(code)<3500 else (-2 if len(code)>8000 else 0)
 return z
@dataclass
class C: name:str; oeis_id:str|None; conjecture:str; proposer:str|None; proposed_date:str|None; scores:dict; source_path:str|None; source_code:str; heuristic:int
def main():
 WORK.mkdir(parents=True,exist_ok=True); clone('https://github.com/epoch-research/LeanOpenProblems.git',SOURCE); clone('https://github.com/epoch-research/LeanOpenProblems-results.git',RESULTS)
 meta=json.loads((RESULTS/'metadata/conjectures.json').read_text()); cs=[]
 for name in sorted(meta):
  ss={r:score(RESULTS/'runs'/r/name/'scores.json') for r in RUNS}
  if any(v=='C' for v in ss.values()):continue
  p=srcfile(name); code=p.read_text(errors='replace') if p else ''; m=meta[name]
  cs.append(C(name,m.get('oeis_id'),m.get('conjecture',''),m.get('proposer'),m.get('proposed_date'),ss,str(p.relative_to(SOURCE)) if p else None,code,heuristic(m.get('conjecture',''),code)))
 cs.sort(key=lambda x:(-x.heuristic,x.name)); payload={'source_commit':sh('git','rev-parse','HEAD',cwd=SOURCE),'results_commit':sh('git','rev-parse','HEAD',cwd=RESULTS),'total_metadata':len(meta),'unsolved_by_all_published_runs':len(cs),'candidates':[asdict(c) for c in cs]}; OUT.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:v for k,v in payload.items() if k!='candidates'},indent=2)); print('TOP_CANDIDATES')
 for c in cs[:100]:print(f'{c.heuristic:>3}  {c.name:<60} {c.conjecture[:160]}')
if __name__=='__main__':main()
