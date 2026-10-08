"""Read the complete component-moment statement and proof at two widths."""
import importlib.util,json
from pathlib import Path
from playwright.sync_api import sync_playwright
r=Path.cwd();e=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('reader',r/'scripts/test_blueprint_web_render.py');checks=importlib.util.module_from_spec(s);s.loader.exec_module(checks)
facts=[]
with checks.serve(r/'blueprint/web') as url,sync_playwright() as p:
 browser=p.chromium.launch();page=browser.new_page(viewport={'width':1280,'height':1000})
 page.goto(url+'/ch-schur_labels.html',wait_until='domcontentloaded');page.add_style_tag(content='.proof_content {display:block !important;}');checks._settle(page)
 for width in [1280,360]:
  page.set_viewport_size({'width':width,'height':1100})
  page.evaluate("document.getElementById('sec:replica_component_merge_moment').scrollIntoView({block:'start'})")
  page.screenshot(path=str(e/f'web-prelude-{width}.png'))
  for kind,selector in [('statement','[id="thm:replica_component_merge_moment"]'),('proof','[id="thm:replica_component_merge_moment"] + .proof_wrapper')]:
   loc=page.locator(selector);assert loc.count()==1
   assert loc.inner_text().strip();loc.screenshot(path=str(e/f'web-{kind}-{width}.png'))
   for n in range(loc.locator('.displaymath').count()):
    d=loc.locator('.displaymath').nth(n);f=d.evaluate("el=>({width:el.clientWidth,scrollWidth:el.scrollWidth,overflow:getComputedStyle(el).overflowX})");f.update(viewport=width,kind=kind,index=n)
    if f['scrollWidth']>f['width']+2:
     assert f['overflow'] in ['auto','scroll'],f
     f['right_endpoint']=d.evaluate("el=>{el.scrollLeft=el.scrollWidth;return {left:el.scrollLeft,max:el.scrollWidth-el.clientWidth}}")
     assert abs(f['right_endpoint']['left']-f['right_endpoint']['max'])<=2
     d.screenshot(path=str(e/f'web-{kind}-{width}-display-{n}-right.png'))
    facts.append(f)
 browser.close()
(e/'mobile-displays.json').write_text(json.dumps(facts,indent=2)+'\n')
assert len(facts)==2,facts
print('Complete component statement, proof and hypotheses rendered at1280/360; the single display checked at both widths.')
