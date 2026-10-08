"""Inspect the complete actual two-deficit component moment statement and proof at desktop and mobile widths."""
import importlib.util
from pathlib import Path
import json
from playwright.sync_api import sync_playwright
root=Path.cwd()
spec=importlib.util.spec_from_file_location("reader",root/"scripts/test_blueprint_web_render.py")
checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
out=root/"docs/provenance/evidence/replicaTwoMergeMomentIntegration8750"
facts=[]
with checks.serve(root/"blueprint/web") as url,sync_playwright() as p:
    browser=p.chromium.launch()
    page=browser.new_page(viewport={"width":1280,"height":900})
    page.goto(url+"/ch-schur_labels.html",wait_until="domcontentloaded")
    page.add_style_tag(content=".proof_content { display:block !important; }")
    checks._settle(page)
    for width in [1280,360]:
        page.set_viewport_size({"width":width,"height":900})
        for theorem,prefix in [("replica_two_merge_moment","thm")]:
            selectors=[("statement",f'[id="{prefix}:{theorem}"]')]
            if prefix=="thm":selectors.append(("proof",f'[id="{prefix}:{theorem}"] + .proof_wrapper'))
            for kind,selector in selectors:
                loc=page.locator(selector)
                loc.screenshot(path=str(out/f"web-{theorem}-{kind}-{width}.png"))
                if width==360:
                    displays=loc.locator('.displaymath')
                    for n in range(displays.count()):
                        display=displays.nth(n)
                        fact=display.evaluate("el => ({width:el.clientWidth,scrollWidth:el.scrollWidth,overflow:getComputedStyle(el).overflowX})")
                        fact.update(theorem=theorem,kind=kind,index=n)
                        if fact['scrollWidth']>fact['width']+2:
                            assert fact['overflow'] in ['auto','scroll'],fact
                            endpoint=display.evaluate("el => {el.scrollLeft=el.scrollWidth;return {left:el.scrollLeft,max:el.scrollWidth-el.clientWidth};}")
                            assert abs(endpoint['left']-endpoint['max'])<=2,endpoint
                            fact['right_endpoint']=endpoint
                            display.screenshot(path=str(out/f"web-{theorem}-{kind}-display-{n}-360-right.png"))
                        facts.append(fact)
    (out/"mobile-equations.json").write_text(json.dumps(facts,indent=2)+"\n")
    browser.close()
print("Rendered complete actual two-deficit component moment statement and proof at desktop/mobile widths; inspected display overflow endpoints.")
