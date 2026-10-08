"""Inspect representative complete entries in all four source chapters on desktop and mobile."""
from pathlib import Path
import importlib.util,json
from playwright.sync_api import sync_playwright
r=Path.cwd();p=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('web_checks',r/'scripts/test_blueprint_web_render.py');checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
anchors=['thm:random_sample_count','thm:random_realization','thm:source_unbiased','thm:source_gaussian_error','thm:reduction_chain','thm:reduction_readout','def:construction_contraction','thm:construction_position_expansion','thm:construction_original_density_error']
report=[]
with checks.serve(r/'blueprint/web') as url,sync_playwright() as play:
 browser=play.chromium.launch();page=browser.new_page(viewport={'width':360,'height':3000},device_scale_factor=1)
 for anchor in anchors:
  docs=[q for q in (r/'blueprint/web').glob('*.html') if not q.name.startswith('dep_graph') and ('id="'+anchor+'"') in q.read_text()]
  assert len(docs)==1,(anchor,docs)
  page.set_viewport_size({'width':360,'height':3000});page.goto(url+'/'+docs[0].name+'#'+anchor,wait_until='networkidle');checks._settle(page)
  page.evaluate('''anchor=>{const e=document.getElementById(anchor);for(const h of e.querySelectorAll('.proof_heading'))h.click();let n=e.nextElementSibling;if(n&&n.classList.contains('proof_wrapper'))for(const h of n.querySelectorAll('.proof_heading'))h.click();}''',anchor)
  page.wait_for_function("() => !window.jQuery || jQuery(':animated').length===0");checks._settle(page)
  expression='''anchor=>{const first=document.getElementById(anchor);first.scrollIntoView({block:'start'});let last=first;const next=first.nextElementSibling;if(next&&next.classList.contains('proof_wrapper'))last=next;const nodes=last===first?[first]:[first,last];return {top:first.getBoundingClientRect().top,bottom:last.getBoundingClientRect().bottom,links:nodes.flatMap(n=>[...n.querySelectorAll('a.lean_decl')].map(a=>a.textContent)),errors:nodes.flatMap(n=>[...n.querySelectorAll('mjx-merror')].map(a=>a.textContent)),math:nodes.reduce((s,n)=>s+n.querySelectorAll('mjx-container').length,0),width:document.documentElement.scrollWidth,proofs:nodes.flatMap(n=>[...n.querySelectorAll('.proof_content')].map(e=>({height:e.getBoundingClientRect().height,text:e.textContent}))) }}'''
  fact=page.evaluate(expression,anchor)
  scrolls=page.evaluate("""anchor=>{const first=document.getElementById(anchor);const roots=[first];if(first.nextElementSibling&&first.nextElementSibling.classList.contains('proof_wrapper'))roots.push(first.nextElementSibling);const seen=new Set();const result=[];for(const root of roots)for(const n of root.querySelectorAll('*')){if(seen.has(n))continue;seen.add(n);if(!['auto','scroll'].includes(getComputedStyle(n).overflowX)||n.scrollWidth<=n.clientWidth+1)continue;n.scrollLeft=n.scrollWidth;result.push({class:n.className,width:n.clientWidth,scrollWidth:n.scrollWidth,scrollLeft:n.scrollLeft,maximum:n.scrollWidth-n.clientWidth});}return result;}""",anchor)
  assert all(abs(s['maximum']-s['scrollLeft'])<=1 for s in scrolls),scrolls
  assert page.evaluate('()=>document.documentElement.scrollWidth')<=361
  if scrolls:
   fact=page.evaluate(expression,anchor);name=anchor.replace(':','-')
   page.screenshot(path=str(p/'render'/f'{name}-mobile-equation-endpoints.png'),clip={'x':0,'y':max(0,fact['top']-5),'width':360,'height':fact['bottom']-fact['top']+15})
  report.append({'anchor':anchor,'local_equation_scrolls':scrolls,'page_width':page.evaluate('()=>document.documentElement.scrollWidth')})
 browser.close()
(p/'equation-scroll-inspection.json').write_text(json.dumps({'result':'passed','entries':report,'equation_scrollers_reach_right_endpoint':True,'mobile_width':360},indent=2)+'\n')
print(len(report),'entry-level checks of equation scroll endpoints and fixed mobile page width.')
