"""Locate and preserve the physical merge Hölder section in the complete generated book."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess

root = Path.cwd()
folder = Path(__file__).resolve().parent
pdf = root / "blueprint/print/print.pdf"
info = subprocess.check_output(["pdfinfo", str(pdf)], text=True)
pages = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))
raw = subprocess.check_output(["pdftotext", "-layout", str(pdf), "-"])
(folder / "complete-book-text.txt.gz").write_bytes(gzip.compress(raw, mtime=0))
text_pages = raw.decode().split("\f")
markers = ["The five actual exponential moments"]
located = {marker: [i+1 for i,text in enumerate(text_pages) if marker in " ".join(text.split())] for marker in markers}
assert all(len(values) == 1 for values in located.values()), located
start = min(i for values in located.values() for i in values)
# Include the page where the section begins and every page through the proof's final sentence.
heading = "Five-factor"
headings = [i+1 for i,text in enumerate(text_pages) if start-1 <= i+1 <= start and heading in text]
assert headings, headings
start = min(headings)
ends = [i+1 for i,text in enumerate(text_pages) if i+1 >= start and "Their sum is" in " ".join(text.split())]
assert ends, "Missing final proof sentence"
selected = list(range(start, min(ends)+1))
assert "Schur Labels of Tensor Powers" in raw.decode()
for i in selected:
    assert "??" not in text_pages[i-1], text_pages[i-1]
    (folder / "render" / f"physical_merge_holder-page-{i}.txt").write_text(text_pages[i-1])
    subprocess.run(["pdftoppm", "-f", str(i), "-l", str(i), "-scale-to", "1800", "-png", "-singlefile", str(pdf), str(folder / "render" / f"physical_merge_holder-page-{i}")], check=True)
report = dict(pdf="blueprint/print/print.pdf", pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),
              pages=pages, markers=located, inspected_physical_pages=selected,
              text_sha256=hashlib.sha256(raw).hexdigest(),
              compressed_text_sha256=hashlib.sha256((folder / "complete-book-text.txt.gz").read_bytes()).hexdigest(),
              deterministic_gzip_mtime=0, schur_chapter_heading_present=True,
              new_pages_have_no_unresolved_references=True, visual_review="pending")
(folder / "pdf-inspection.json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps(report, indent=2))
