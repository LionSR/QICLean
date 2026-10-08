"""Capture every new mathematical entry with its complete proof and mobile endpoints."""
from pathlib import Path
import importlib.util,json
from playwright.sync_api import sync_playwright
r=Path.cwd();p=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('web_checks',r/'scripts/test_blueprint_web_render.py');c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
ids=['thm:replica_good_physical_support'];result=[]
with c.serve(r/'blueprint/web') as url,sync_playwright() as api:
 b=api.chromium.launch();page=b.new_page(viewport={'width':1440,'height':3000})
 page.goto(url+'/ch-entropy.html#sec:replica_good_physical_support',wait_until='networkidle');c._settle(page)
 page.evaluate("() => {const a=document.getElementById('sec:replica_good_physical_support');for(let n=a.nextElementSibling;n&&n.tagName!=='H1';n=n.nextElementSibling)for(const h of n.querySelectorAll('.proof_heading'))h.click();}")
 page.wait_for_function("() => !window.jQuery || jQuery(':animated').length === 0");c._settle(page)
 for width,label in [(1440,'desktop'),(360,'mobile')]:
  page.set_viewport_size({'width':width,'height':3000});c._settle(page)
  for i,ident in enumerate(ids):
   facts=page.evaluate("""id => {const a=document.getElementById(id);const roots=[a];if(a.nextElementSibling?.classList.contains('proof_wrapper'))roots.push(a.nextElementSibling);a.scrollIntoView({block:'start'});const z=roots.at(-1);return {top:a.getBoundingClientRect().top+window.scrollY,bottom:z.getBoundingClientRect().bottom+window.scrollY,proofs:roots.flatMap(n=>[...n.querySelectorAll('.proof_content')].map(e=>({height:e.getBoundingClientRect().height,text:e.textContent}))),errors:roots.flatMap(n=>[...n.querySelectorAll('mjx-merror')].map(e=>e.textContent))};}""",ident)
   assert not facts['errors'];assert len(facts['proofs'])==1 and facts['proofs'][0]['height']>0,facts
   image=p/'render'/f'entry-{i+1}-{label}.png';page.screenshot(path=str(image),clip={'x':0,'y':facts['top']-3,'width':width,'height':facts['bottom']-facts['top']+6})
   facts.update({'id':ident,'view':label,'screenshot':str(image.relative_to(r))});result.append(facts)
   if label=='mobile':
    scrolls=page.evaluate("""id=>{const roots=[document.getElementById(id)];if(roots[0].nextElementSibling?.classList.contains('proof_wrapper'))roots.push(roots[0].nextElementSibling);const out=[];for(const a of roots)for(const n of a.querySelectorAll('*'))if(['auto','scroll'].includes(getComputedStyle(n).overflowX)&&n.scrollWidth>n.clientWidth+1){n.scrollLeft=n.scrollWidth;out.push({width:n.clientWidth,total:n.scrollWidth,end:n.scrollLeft});}return out;}""",ident)
    facts['horizontal_endpoints']=scrolls
    assert all(abs(v['end']-(v['total']-v['width']))<=1 for v in scrolls),scrolls
    if scrolls:page.screenshot(path=str(p/'render'/f'entry-{i+1}-mobile-endpoints.png'),clip={'x':0,'y':facts['top']-3,'width':width,'height':facts['bottom']-facts['top']+6})
 b.close()
(p/'entry-inspection.json').write_text(json.dumps(result,indent=2)+'\n');print('Two complete statement/proof views captured, with every mobile horizontal endpoint.')
