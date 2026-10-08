from pathlib import Path
import hashlib,json
root=Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/source-transport-expansion');b=Path('/private/tmp/qic-source-transport-expansion');b.mkdir(exist_ok=True);p=Path('/tmp/SourceTransportExpansion.lean');raw=p.read_text();notice='''/-
Provenance-ID: p09-qic-source-transport-expansion
Downstream declaration: QICLean.ComplexGaussian.sourceTransport_eq_sum_rankOne
Source: September 24, 2026.
Label: eq:compression-random-source
Independently formalized; no upstream Lean proof text reused.
-/
''';s=raw.replace('theorem sourceTransport_eq_sum_rankOne',notice+'theorem sourceTransport_eq_sum_rankOne');f=root/'QICLean/Probability/ComplexGaussian/SourceTransportExpansion.lean';assert not f.exists();f.write_text(s);(b/'source-original.lean').write_text(raw)
p=root/'blueprint/src/chapter/ch13_source_reduction.tex';s=p.read_text();marker='\\begin{theorem}[Unbiased ambient product sources]';insert=r'''\begin{theorem}[Rank-one expansion of transported sources]
    \label{thm:reduction_transport_rank_one}
    \lean{QICLean.ComplexGaussian.sourceTransport_eq_sum_rankOne}
    \leanok
    \uses{def:reduction_ambient_transport}
    Let $A,C$ be finite index sets and let $W,X,Y,Z$ be arbitrary index sets.
    For endpoint matrices $E,F,\widetilde E,\widetilde F$ of the indicated
    sizes, define the coordinate arrays
    $u_{ab}(w,x)=E_{wa}F_{xb}$ and
    $v_{cd}(y,z)=\widetilde E_{yc}\widetilde F_{zd}$.
    Every matrix $M$ with rows indexed by $A\times A$ and columns indexed
    by $C\times C$ satisfies
    \begin{align}
        \mathcal T(M)
        &=\sum_{a,b\in A}\sum_{c,d\in C} M_{(a,b),(c,d)}\,u_{ab}v_{cd}^{\dagger}.
        \label{eq:reduction_rank_one_expansion}
    \end{align}
    No orthonormality or spanning condition on the endpoint matrices is needed.
\end{theorem}

\begin{proof}\leanok
    \uses{def:reduction_ambient_transport}
    Expand both finite matrix products in
    $\mathcal T(M)=(E\otimes F)M(\widetilde E\otimes\widetilde F)^{\dagger}$.
    The term indexed by $(a,b,c,d)$ at row $(w,x)$ and column $(y,z)$ is
    $M_{(a,b),(c,d)}E_{wa}F_{xb}
    \overline{\widetilde E_{yc}\widetilde F_{zd}}$, which is the corresponding
    entry of the rank-one summand in (\ref{eq:reduction_rank_one_expansion}).
\end{proof}

''';assert marker in s;p.write_text(s.replace(marker,insert+marker))
old=json.loads(Path('/private/tmp/qic-orthonormal-matrix-norm/env.json').read_text());art=b/'artifacts';art.mkdir(exist_ok=True);first=Path(old['LEAN_PATH'].split(':')[0]);count=0
for p in first.rglob('*'):
 if p.is_file():
  q=art/p.relative_to(first);q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():q.symlink_to(p.resolve());count+=1
cfg={**old,'LEAN_PATH':str(art)+':'+':'.join(old['LEAN_PATH'].split(':')[1:]),'source_root':str(root),'output_root':str(art)};(b/'env.json').write_text(json.dumps(cfg,indent=2)+'\n');(b/'preparation.json').write_text(json.dumps({'base_revision':'95411dd3d2f08ec2f65c7613ab0b81c330d28f5c','original_sha256':hashlib.sha256(raw.encode()).hexdigest(),'production_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'read_only_artifact_links':count},indent=2)+'\n');print('QIC_PREPARED',count)
