"""Check the actual mobile reader scroll container and the complete closing scope paragraph."""
import importlib.util,json
from pathlib import Path
from playwright.sync_api import sync_playwright
root=Path.cwd();out=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('reader',root/'scripts/test_blueprint_web_render.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
with c.serve(root/'blueprint/web') as url,sync_playwright() as p:
 b=p.chromium.launch();page=b.new_page(viewport={'width':360,'height':900});page.goto(url+'/ch-schur_labels.html');page.add_style_tag(content='.proof_content { display:block !important; }');c._settle(page)
 eq=page.locator('[id="eq:replica_physical_label_moment"]');eq.scroll_into_view_if_needed()
 fact=eq.evaluate('el=>{let x=el;while(x&&!["auto","scroll"].includes(getComputedStyle(x).overflowX))x=x.parentElement;if(!x)throw Error("no scroll container");x.scrollLeft=x.scrollWidth;return {class:x.className,width:x.clientWidth,scrollWidth:x.scrollWidth,left:x.scrollLeft,max:x.scrollWidth-x.clientWidth,overflow:getComputedStyle(x).overflowX}}')
 assert abs(fact['left']-fact['max'])<=2,fact
 page.screenshot(path=str(out/'web-equation-content-right-360.png'))
 (out/'mobile-reader-endpoint.json').write_text(json.dumps(fact,indent=2)+'\n')
 page.locator('[id="thm:replica_physical_label_moment"] + .proof_wrapper + p').screenshot(path=str(out/'web-scope-360.png'))
 page.set_viewport_size({'width':1280,'height':900});page.locator('[id="thm:replica_physical_label_moment"] + .proof_wrapper + p').screenshot(path=str(out/'web-scope-1280.png'))
 b.close()
print('Verified mobile reader right endpoint for the numbered exact identity and captured the complete scope paragraph at both widths.')
