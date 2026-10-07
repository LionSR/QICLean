"""Render the complete new statement and proof at desktop and mobile widths."""
import importlib.util
from pathlib import Path
import json
from playwright.sync_api import sync_playwright
root=Path.cwd()
spec=importlib.util.spec_from_file_location("reader",root/"scripts/test_blueprint_web_render.py")
checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
out=root/"docs/provenance/evidence/groupedLabelEntropyIntegration8750"
with checks.serve(root/"blueprint/web") as url,sync_playwright() as p:
    browser=p.chromium.launch()
    page=browser.new_page(viewport={"width":1280,"height":900})
    page.goto(url+"/ch-schur_labels.html",wait_until="domcontentloaded")
    page.add_style_tag(content=".proof_content { display:block !important; }")
    checks._settle(page)
    for width in [1280,360]:
        page.set_viewport_size({"width":width,"height":900})
        for label,selector in [("statement",'[id="thm:grouped_label_entropy_bounds"]'),("proof",'[id="thm:grouped_label_entropy_bounds"] + .proof_wrapper')]:
            page.locator(selector).screenshot(path=str(out/f"web-{label}-{width}.png"))
    page.set_viewport_size({"width":360,"height":900})
    facts=page.locator('[id="thm:grouped_label_entropy_bounds"] .displaymath').evaluate_all("els => els.map(el => ({id:el.id,width:el.clientWidth,scrollWidth:el.scrollWidth,overflow:getComputedStyle(el).overflowX,math:Array.from(el.querySelectorAll('mjx-container')).map(x=>({width:x.clientWidth,scrollWidth:x.scrollWidth,overflow:getComputedStyle(x).overflowX}))}))")
    (out/"mobile-equations.json").write_text(json.dumps(facts,indent=2)+"\n")
    browser.close()
print("Rendered complete statement and proof at desktop/mobile widths.")
