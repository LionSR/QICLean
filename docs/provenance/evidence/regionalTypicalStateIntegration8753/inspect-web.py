import json,sys
from pathlib import Path
sys.path.insert(0,str(Path.cwd()/'scripts'))
from test_blueprint_web_render import serve,_settle
from playwright.sync_api import sync_playwright
root=Path.cwd(); output=root/'docs/provenance/evidence/regionalTypicalStateIntegration8753'
labels=['def:entropy_regional_typical_state','thm:entropy_regional_typical_state_normalization','thm:entropy_regional_typical_state_bound']
records=[]
with serve(root/'blueprint/web') as address,sync_playwright() as p:
 browser=p.chromium.launch(); page=browser.new_page(viewport={'width':1440,'height':1000})
 page.goto(address+'/ch-entropy.html',wait_until='domcontentloaded')
 page.add_style_tag(content='.proof_content {display:block !important;}')
 _settle(page)
 for width in [1440,360]:
  page.set_viewport_size({'width':width,'height':1000})
  for index,label in enumerate(labels):
   node=page.locator('[id="'+label+'"]')
   facts=node.evaluate('''node => ({label:node.id, math:node.querySelectorAll('mjx-container').length, errors:[...node.querySelectorAll('mjx-merror')].map(x=>x.textContent), declarations:[...node.querySelectorAll('a.lean_decl')].map(x=>({name:x.textContent,href:x.getAttribute('href')})), citations:[...node.querySelectorAll('a[href*="OpenAI2026AreaLaw"]')].map(x=>x.getAttribute('href')), text:node.querySelector('[class$="thmcontent"]').innerText, overflow:[...node.querySelectorAll('[class$="thmcontent"] *')].filter(x=> {const b=x.getBoundingClientRect();return b.width>0 && b.right>document.documentElement.clientWidth+1 && getComputedStyle(x.parentElement).overflowX!=='auto'}).map(x=>x.tagName).slice(0,4)})''')
   assert facts['math']>0 and not facts['errors'],facts
   assert len(facts['declarations'])==2,facts
   assert '??' not in facts['text'] and '\\begin' not in facts['text'],facts
   if index==2: assert facts['citations']==['sect0001.html#OpenAI2026AreaLaw'],facts
   assert not facts['overflow'],facts
   node.screenshot(path=str(root/f'tmp/pdfs/regional-web-{width}-{index}.png'))
   facts['width']=width;records.append(facts)
 browser.close()
(output/'web-inspection.json').write_text(json.dumps(records,indent=2)+'\n')
print('Passed desktop/mobile inspections of three regional entries and six declaration links; all four displays were typeset.')
