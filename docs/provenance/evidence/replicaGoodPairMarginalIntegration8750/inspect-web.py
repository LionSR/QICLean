"""Render and check the new exact common-density section of the complete blueprint."""
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
    page.goto(url + "/ch-entropy.html#sec:replica_good_pair_marginal", wait_until="networkidle")
    checks._settle(page)
    facts = page.evaluate("""() => {
      const first = document.getElementById('sec:replica_good_pair_marginal');
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
    facts["proofs"] = page.evaluate("""() => {const first=document.getElementById('sec:replica_good_pair_marginal');const roots=[first];for(let n=first.nextElementSibling;n&&n.tagName!=='H1';n=n.nextElementSibling)roots.push(n);return roots.flatMap(n=>[...n.querySelectorAll('.proof_content')].map(e=>({height:e.getBoundingClientRect().height,text:e.textContent})));}""")
    assert len(facts["proofs"]) == 3 and all(proof["height"]>0 for proof in facts["proofs"]), facts
    bounds = """() => {
      const first = document.getElementById('sec:replica_good_pair_marginal');
      first.scrollIntoView({block: 'start'});
      let last = first;
      for (let n = first.nextElementSibling; n && n.tagName !== 'H1'; n = n.nextElementSibling)
        last = n;
      return {top: first.getBoundingClientRect().top,
              bottom: last.getBoundingClientRect().bottom};
    }"""
    facts.update(page.evaluate(bounds))
    expected = {entry["downstream"]["declaration"] for entry in json.loads((root / "docs/provenance/openai-math.d/replicaGoodPairMarginal8750.json").read_text())["entries"]}
    assert set(facts["links"]) == expected and len(facts["links"]) == 4, facts
    assert not facts["errors"] and facts["mathElements"] > 0, facts
    page.screenshot(path=str(evidence / "render/common-density-web-desktop.png"),
                    clip={"x": 0, "y": facts["top"]-10, "width": 1440,
                          "height": facts["bottom"]-facts["top"]+20})
    page.set_viewport_size({"width": 360, "height": 3000})
    checks._settle(page)
    mobile = page.evaluate(bounds)
    page.screenshot(path=str(evidence / "render/common-density-web-mobile.png"),
                    clip={"x": 0, "y": mobile["top"]-5, "width": 360,
                          "height": mobile["bottom"]-mobile["top"]+10})
    facts["mobile_section_bounds"] = mobile
    facts["mobile_page_width"] = page.evaluate("() => document.documentElement.scrollWidth")
    facts["mobile_viewport_width"] = 360
    assert facts["mobile_page_width"] <= 361, facts
    facts["mobile_equation_scrolls"] = page.evaluate("""() => {const first=document.getElementById('sec:replica_good_pair_marginal');const roots=[first];for(let n=first.nextElementSibling;n&&n.tagName!=='H1';n=n.nextElementSibling)roots.push(n);const result=[];for(const root of roots)for(const n of root.querySelectorAll('*')){if(!['auto','scroll'].includes(getComputedStyle(n).overflowX)||n.scrollWidth<=n.clientWidth+1)continue;n.scrollLeft=n.scrollWidth;result.push({class:n.className,width:n.clientWidth,scrollWidth:n.scrollWidth,scrollLeft:n.scrollLeft,maximum:n.scrollWidth-n.clientWidth});}return result;}""")
    assert all(abs(s["scrollLeft"]-s["maximum"])<=1 for s in facts["mobile_equation_scrolls"]),facts
    if facts["mobile_equation_scrolls"]:
        page.screenshot(path=str(evidence / "render/common-density-web-mobile-equation-endpoints.png"),clip={"x":0,"y":mobile["top"]-5,"width":360,"height":mobile["bottom"]-mobile["top"]+10})
    browser.close()
(evidence / "web-inspection.json").write_text(json.dumps(facts, indent=2) + "\n")
print("Four common-density declaration links, typeset mathematics, no MathJax errors, and no mobile page overflow.")
