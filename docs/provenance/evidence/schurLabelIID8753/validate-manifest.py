"""Check immutable source, command logs, archive contents and committed evidence."""
from pathlib import Path
import gzip
import hashlib
import json
import subprocess
import sys
import tarfile

root = Path.cwd()
folder = Path(__file__).resolve().parent
manifest = json.loads((folder / 'manifest.json').read_text())
for path, digest in manifest['artifacts'].items():
    data = (root / path).read_bytes()
    assert hashlib.sha256(data).hexdigest() == digest, path
    if '--git' in sys.argv:
        assert data == subprocess.check_output(['git', 'show', 'HEAD:' + path]), path
for path, digest in manifest['source_sha256'].items():
    assert hashlib.sha256((root / path).read_bytes()).hexdigest() == digest, path
for record_path in manifest['command_records']:
    record = json.loads((root / record_path).read_text())
    assert record['exit_code'] == 0, record_path
    assert record['source_revision'] == manifest['source_revision'], record_path
    data = (root / record['log']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == record['sha256'], record_path
    raw = gzip.decompress(data) if record['compressed'] else data
    assert hashlib.sha256(raw).hexdigest() == record['uncompressed_sha256'], record_path
    assert len(raw) == record['uncompressed_bytes'], record_path
    if record['compressed']:
        assert data == gzip.compress(raw, mtime=0), record_path
for record in json.loads((folder / 'metadata-compression.json').read_text()):
    packed = (root / record['path']).read_bytes()
    raw = gzip.decompress(packed)
    assert hashlib.sha256(packed).hexdigest() == record['sha256']
    assert hashlib.sha256(raw).hexdigest() == record['uncompressed_sha256']
    assert packed == gzip.compress(raw, mtime=0)
for packet in json.loads(gzip.decompress((folder / 'original-packets.json.gz').read_bytes())):
    packed = (root / packet['archive']).read_bytes()
    assert hashlib.sha256(packed).hexdigest() == packet['archive_sha256']
    raw = gzip.decompress(packed)
    assert hashlib.sha256(raw).hexdigest() == packet['uncompressed_tar_sha256']
    assert packed == gzip.compress(raw, mtime=0)
    with tarfile.open(root / packet['archive'], 'r:gz') as archive:
        for member in archive.getmembers():
            assert member.isfile(), member.name
            assert '.olean' not in member.name and '.ilean' not in member.name, member.name
            data = archive.extractfile(member).read()
            assert hashlib.sha256(data).hexdigest() == packet['files'][member.name]['sha256']
            data.decode('utf-8')
print(f"Validated {len(manifest['artifacts'])} artifact hashes and {len(manifest['command_records'])} successful recorded commands.")
print('Historical archives contain only text/source/log records; compiled contents and dependency symlinks are excluded.')
