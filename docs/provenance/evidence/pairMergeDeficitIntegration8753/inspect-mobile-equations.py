"""Check that each paired merge-deficit display remains readable by horizontal scrolling on mobile."""
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
    page.goto(url + '/ch-schur_labels.html#sec:pair_merge_deficit', wait_until='networkidle')
    page.add_style_tag(content=".proof_content { display: block !important; }")
    checks._settle(page)
    facts = page.evaluate('''() => {
      const first = document.getElementById('sec:pair_merge_deficit');
      const nodes = [first];
      for (let n=first.nextElementSibling; n && n.tagName!=='H1'; n=n.nextElementSibling) nodes.push(n);
      const displays = nodes.flatMap(n => [...(n.matches('.displaymath') ? [n] : []), ...n.querySelectorAll('.displaymath')]);
      return displays.map(e => {e.scrollLeft=e.scrollWidth; return {id:e.id, clientWidth:e.clientWidth,
        scrollWidth:e.scrollWidth, scrollLeft:e.scrollLeft, overflowX:getComputedStyle(e).overflowX};});
    }''')
    assert len(facts)==3, facts
    assert all(e['clientWidth'] > 0 for e in facts), facts
    for index, equation in enumerate(facts):
        if equation['scrollWidth'] > equation['clientWidth'] + 1:
            assert equation['overflowX'] in ['auto','scroll'] and equation['scrollLeft'] > 0, equation
            page.locator('[id="'+equation['id']+'"]').screenshot(path=str(folder/'render'/f'pair-merge-deficit-mobile-equation-{index}-right.png'))
    assert page.evaluate('() => document.documentElement.scrollWidth') <= 361
    browser.close()
wide = sum(e['scrollWidth'] > e['clientWidth']+1 for e in facts)
report={'equations':facts,'result':'passed','overflowing_display_count':wide,
        'right_endpoint_capture_count':wide,
        'interpretation':('All three display boxes fit the mobile content width; no horizontal scrolling or right-endpoint capture is required.' if wide==0 else 'Long displays scroll within their equation boxes; every overflowing right endpoint was reached and captured. The page has no horizontal overflow.')}
(folder/'mobile-equations.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
