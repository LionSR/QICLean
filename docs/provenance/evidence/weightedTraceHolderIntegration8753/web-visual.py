"""Capture every complete weighted trace theorem and proof at desktop/mobile widths."""
from pathlib import Path
import importlib.util,json
from playwright.sync_api import sync_playwright
r=Path.cwd();e=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('reader',r/'scripts/test_blueprint_web_render.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
labels=['resolution-product-coordinates','weighted-trace-holder-binary','weighted-trace-holder-finite'];facts=[]
with c.serve(r/'blueprint/web') as url,sync_playwright() as p:
 b=p.chromium.launch();page=b.new_page(viewport={'width':1280,'height':900});page.goto(url+'/ch-schur_labels.html');page.add_style_tag(content='.proof_content { display:block !important; }');c._settle(page)
 for width in [1280,360]:
  page.set_viewport_size({'width':width,'height':900})
  for label in labels:
   for kind,selector in [('statement',f'[id="thm:{label}"]'),('proof',f'[id="thm:{label}"] + .proof_wrapper')]:
    loc=page.locator(selector);loc.screenshot(path=str(e/f'web-{label}-{kind}-{width}.png'))
    if width==360:
     for i in range(loc.locator('.displaymath, .equation_content').count()):
      disp=loc.locator('.displaymath, .equation_content').nth(i);fact=disp.evaluate('el=>({width:el.clientWidth,scrollWidth:el.scrollWidth,overflow:getComputedStyle(el).overflowX})');fact.update(label=label,kind=kind,index=i)
      if fact['scrollWidth']>fact['width']+2:
       assert fact['overflow'] in ['auto','scroll'],fact
       fact['right_endpoint']=disp.evaluate('el=>{el.scrollLeft=el.scrollWidth;return {left:el.scrollLeft,max:el.scrollWidth-el.clientWidth}}');assert abs(fact['right_endpoint']['left']-fact['right_endpoint']['max'])<=2
       disp.screenshot(path=str(e/f'web-{label}-{kind}-display-{i}-360-right.png'))
      facts.append(fact)
 b.close()
(e/'mobile-equations.json').write_text(json.dumps(facts,indent=2)+'\n');print('Captured all three complete theorem/proof entries at both widths; checked every actual local mobile display right endpoint.')
