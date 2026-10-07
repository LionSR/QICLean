"""Inspect the two new mathematical entries at desktop and phone widths."""
import json
from pathlib import Path
import sys

root = Path.cwd()
sys.path.insert(0, str(root / 'scripts'))
from test_blueprint_web_render import serve, _settle
from playwright.sync_api import sync_playwright

evidence = root / 'docs/provenance/evidence/typicalStateFromTailIntegration8753'
labels = ['thm:entropy_typical_density_from_tail', 'thm:entropy_typical_pure_state_from_tail']
records = []
with serve(root / 'blueprint/web') as address, sync_playwright() as p:
    browser = p.chromium.launch()
    page = browser.new_page(viewport={'width': 1440, 'height': 1000})
    page.goto(address + '/ch-entropy.html', wait_until='domcontentloaded')
    page.add_style_tag(content='.proof_content { display: block !important; }')
    _settle(page)
    for width in [1440, 360]:
        page.set_viewport_size({'width': width, 'height': 1000})
        for index, label in enumerate(labels):
            node = page.locator('[id="' + label + '"]')
            facts = node.evaluate('''node => {
              const content = node.querySelector('[class$="thmcontent"]');
              const overflow = [...content.querySelectorAll('*')].filter(x => {
                const b = x.getBoundingClientRect();
                if (b.width <= 0 || b.right <= document.documentElement.clientWidth + 1) return false;
                let parent = x.parentElement;
                while (parent) {
                  if (['auto','scroll'].includes(getComputedStyle(parent).overflowX)) return false;
                  parent = parent.parentElement;
                }
                return true;
              }).map(x => x.tagName).slice(0,4);
              return {label:node.id,math:node.querySelectorAll('mjx-container').length,
                errors:[...node.querySelectorAll('mjx-merror')].map(x => x.textContent),
                declarations:[...node.querySelectorAll('a.lean_decl')].map(x => ({name:x.textContent,href:x.getAttribute('href')})),
                citations:[...node.querySelectorAll('a[href*="OpenAI2026AreaLaw"]')].map(x => x.getAttribute('href')),
                text:content.innerText,overflow};
            }''')
            assert facts['math'] > 0 and not facts['errors'], facts
            assert len(facts['declarations']) == 1, facts
            assert '??' not in facts['text'] and '\\begin' not in facts['text'], facts
            if index == 0:
                assert facts['citations'] == ['sect0001.html#OpenAI2026AreaLaw'], facts
            assert not facts['overflow'], facts
            node.screenshot(path=str(root / f'tmp/pdfs/typical-tail-web-{width}-{index}.png'))
            facts['width'] = width
            records.append(facts)
    browser.close()
(evidence / 'web-inspection.json').write_text(json.dumps(records, indent=2) + '\n')
print('Passed desktop/mobile inspections of both new entries, both declaration links and the manuscript citation; all displays were typeset.')
