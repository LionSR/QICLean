"""Render and check the new actual replica prevector section of the complete blueprint."""
from pathlib import Path
import importlib.util
import json

from playwright.sync_api import sync_playwright

root = Path.cwd()
evidence = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("web_checks", root / "scripts/test_blueprint_web_render.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)

with checks.serve(root / "blueprint/web") as url, sync_playwright() as p:
    browser = p.chromium.launch()
    page = browser.new_page(viewport={"width": 1440, "height": 2400}, device_scale_factor=1)
    page.goto(url + "/ch-entropy.html#sec:replica_prevector", wait_until="networkidle")
    checks._settle(page)
    facts = page.evaluate("""() => {
      const first = document.getElementById('sec:replica_prevector');
      const nodes = [first];
      for (let n = first.nextElementSibling; n && n.tagName !== 'H1'; n = n.nextElementSibling)
        nodes.push(n);
      for (const n of nodes) for (const h of n.querySelectorAll('.proof_heading')) h.click();
      const links = nodes.flatMap(n => [...n.querySelectorAll('a.lean_decl')].map(a => a.textContent));
      const errors = nodes.flatMap(n => [...n.querySelectorAll('mjx-merror')].map(e => e.textContent));
      const top = first.getBoundingClientRect().top + window.scrollY;
      const bottom = nodes[nodes.length-1].getBoundingClientRect().bottom + window.scrollY;
      return {links, errors, top, bottom, mathElements: nodes.reduce((s,n) => s+n.querySelectorAll('mjx-container').length,0)};
    }""")
    page.wait_for_function("() => !window.jQuery || jQuery(':animated').length === 0")
    checks._settle(page)
    bounds = """() => {
      const first = document.getElementById('sec:replica_prevector');
      first.scrollIntoView({block: 'start'});
      let last = first;
      for (let n = first.nextElementSibling; n && n.tagName !== 'H1'; n = n.nextElementSibling)
        last = n;
      return {top: first.getBoundingClientRect().top,
              bottom: last.getBoundingClientRect().bottom};
    }"""
    facts.update(page.evaluate(bounds))
    expected = {entry["downstream"]["declaration"] for entry in json.loads((root / "docs/provenance/openai-math.d/replicaPrevector8753.json").read_text())["entries"]}
    assert set(facts["links"]) == expected and len(facts["links"]) == 2, facts
    assert not facts["errors"] and facts["mathElements"] > 0, facts
    page.screenshot(path=str(evidence / "render/replica-prevector-web-desktop.png"),
                    clip={"x": 0, "y": facts["top"]-10, "width": 1440,
                          "height": facts["bottom"]-facts["top"]+20})
    page.set_viewport_size({"width": 360, "height": 3000})
    checks._settle(page)
    mobile = page.evaluate(bounds)
    page.screenshot(path=str(evidence / "render/replica-prevector-web-mobile.png"),
                    clip={"x": 0, "y": mobile["top"]-5, "width": 360,
                          "height": mobile["bottom"]-mobile["top"]+10})
    facts["mobile_section_bounds"] = mobile
    facts["mobile_page_width"] = page.evaluate("() => document.documentElement.scrollWidth")
    facts["mobile_viewport_width"] = 360
    assert facts["mobile_page_width"] <= 361, facts
    browser.close()
(evidence / "web-inspection.json").write_text(json.dumps(facts, indent=2) + "\n")
print("Two replica prevector declaration links, typeset mathematics, no MathJax errors, and no mobile page overflow.")
