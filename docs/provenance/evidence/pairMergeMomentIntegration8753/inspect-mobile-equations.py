"""Check that each paired merge-moment display remains readable by horizontal scrolling on mobile."""
from pathlib import Path
import importlib.util
import json
from playwright.sync_api import sync_playwright
root = Path.cwd()
folder = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('web_checks', root / 'scripts/test_blueprint_web_render.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
with checks.serve(root / 'blueprint/web') as url, sync_playwright() as p:
    browser = p.chromium.launch()
    page = browser.new_page(viewport={'width':360,'height':3000}, device_scale_factor=1)
    page.goto(url + '/ch-schur_labels.html#sec:pair_merge_moment', wait_until='networkidle')
    page.add_style_tag(content=".proof_content { display: block !important; }")
    checks._settle(page)
    facts = page.evaluate('''() => {
      const first = document.getElementById('sec:pair_merge_moment');
      const nodes = [first];
      for (let n=first.nextElementSibling; n && n.tagName!=='H1'; n=n.nextElementSibling) nodes.push(n);
      const displays = nodes.flatMap(n => [...(n.matches('.displaymath') ? [n] : []), ...n.querySelectorAll('.displaymath')]);
      return displays.map(e => {e.scrollLeft=e.scrollWidth; return {id:e.id, clientWidth:e.clientWidth,
        scrollWidth:e.scrollWidth, scrollLeft:e.scrollLeft, overflowX:getComputedStyle(e).overflowX};});
    }''')
    assert len(facts)==5, facts
    assert all(e['clientWidth'] > 0 for e in facts), facts
    for index, equation in enumerate(facts):
        if equation['scrollWidth'] > equation['clientWidth'] + 1:
            assert equation['overflowX'] in ['auto','scroll'] and equation['scrollLeft'] > 0, equation
            page.locator('[id="'+equation['id']+'"]').screenshot(path=str(folder/'render'/f'pair-merge-moment-mobile-equation-{index}-right.png'))
    assert page.evaluate('() => document.documentElement.scrollWidth') <= 361
    browser.close()
report={'equations':facts,'result':'passed','interpretation':'Long displays use horizontal scrolling within the equation box. Each right endpoint was reached and captured; the page itself has no horizontal overflow.'}
(folder/'mobile-equations.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
