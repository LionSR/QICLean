"""Inspect the whole-region setting and the literal physical-region constants on mobile."""
import importlib.util,json
from pathlib import Path
from playwright.sync_api import sync_playwright
root=Path.cwd();out=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('reader',root/'scripts/test_blueprint_web_render.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
facts=[]
with c.serve(root/'blueprint/web') as url,sync_playwright() as p:
 b=p.chromium.launch();page=b.new_page(viewport={'width':360,'height':900});page.goto(url+'/ch-schur_labels.html');c._settle(page)
 ids=page.locator('[id="sec:replica_physical_label_moment"]').evaluate('el=>{let x=el.nextElementSibling;let ids=[];let n=0;while(x&&x.id!=="thm:replica_physical_label_moment"){x.id="physical-label-context-"+n++;ids.push(x.id);x=x.nextElementSibling;}return ids;}')
 for n,id in enumerate(ids):
  loc=page.locator('[id="'+id+'"]');loc.screenshot(path=str(out/f'web-context-{n}-360.png'))
  displays=[loc] if loc.evaluate('el=>el.classList.contains("displaymath")') else [loc.locator('.displaymath, .equation_content').nth(j) for j in range(loc.locator('.displaymath, .equation_content').count())]
  for j,disp in enumerate(displays):
   fact=disp.evaluate('el=>({width:el.clientWidth,scrollWidth:el.scrollWidth,overflow:getComputedStyle(el).overflowX})');fact.update(context=n,index=j)
   if fact['scrollWidth']>fact['width']+2:
    assert fact['overflow'] in ['auto','scroll'];fact['right_endpoint']=disp.evaluate('el=>{el.scrollLeft=el.scrollWidth;return {left:el.scrollLeft,max:el.scrollWidth-el.clientWidth};}');assert abs(fact['right_endpoint']['left']-fact['right_endpoint']['max'])<=2
    disp.screenshot(path=str(out/f'web-context-{n}-display-{j}-360-right.png'))
   facts.append(fact)
 b.close()
(out/'mobile-context-equations.json').write_text(json.dumps(facts,indent=2)+'\n');print('Physical region setting and actual full-space label exponential captured on mobile; local formula endpoints checked.')
