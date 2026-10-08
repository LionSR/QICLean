from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent.parent/"replicaRegionalDensity8750"
subprocess.run([sys.executable,str(p/"validate-manifest.py"),"--allow-inclusion"],check=True)
