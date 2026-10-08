"""Inspect the newly changed entropy page using the repository's reader checks."""
import importlib.util
import json
from pathlib import Path
import re
from playwright.sync_api import sync_playwright

root=Path.cwd()
spec=importlib.util.spec_from_file_location("reader_checks",root/"scripts/test_blueprint_web_render.py")
checks=importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
web=root/"blueprint/web"
labels=[]
for fragment in ["replica_good_copy_factorization"]:
    labels+=re.findall(r"\\label\{([^}]+)\}",(root/f"blueprint/src/fragment/{fragment}.tex").read_text())
with checks.serve(web) as url, sync_playwright() as playwright:
    browser=playwright.chromium.launch()
    page=browser.new_page(viewport={"width":checks.MOBILE_WIDTH,"height":900})
    page.goto(f"{url}/ch-entropy.html",wait_until="domcontentloaded",timeout=120000)
    page.add_style_tag(content=".proof_content { display: block !important; }")
    checks._settle(page)
    facts=page.evaluate(checks.READER_TEXT,list(checks.METADATA_COMMANDS))
    checks._assert_reader_text("ch-entropy.html",facts)
    assert facts["typeset"]
    anchors=page.evaluate("ids => Object.fromEntries(ids.map(id => [id,!!document.getElementById(id)]))",labels)
    widths={}
    for width in [checks.MOBILE_WIDTH,checks.DESKTOP_WIDTH]:
        page.set_viewport_size({"width":width,"height":900})
        page.wait_for_timeout(200)
        measurements=page.evaluate(checks.OVERFLOW)
        checks._assert_page_owns_no_sideways_scroll("ch-entropy.html",width,measurements)
        widths[str(width)]=measurements
    page.set_viewport_size({"width":1280,"height":900})
    for label in ["sec:replica_good_copy","thm:replica_good_component","thm:replica_good_norm"]:
        page.locator(f'[id="{label}"]').scroll_into_view_if_needed()
        page.screenshot(path=str(root/f"docs/provenance/evidence/replicaGoodCopyIntegration8750/{label.replace(':','-')}-web.png"))
    browser.close()
print(json.dumps({"typeset":facts["typeset"],"anchors":anchors,"widths":widths}))
assert all(anchors.values()),anchors
