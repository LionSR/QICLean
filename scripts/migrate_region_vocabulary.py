#!/usr/bin/env python3
"""Rewrite Lean sources onto QICLean's unified regional vocabulary (many-body plan, step 4.0).

QICLean used three spellings of the reduced state of a vector on a region and of its entropy:
the dimension-indexed abbreviations of `Entropy` (`SiteConfig n`, `Entropy.regionState`,
`Entropy.localLift`, ...), the `ManyBody` definitions on a site family `X`, and the
`FiniteProduct` namespace (`reducedPure`, `entropy`, `mutualInformation`, ...). One spelling
survives: `ManyBody.regionState φ D`, `ManyBody.regionEntropy φ D`,
`ManyBody.regionMutualInformation φ R T` and `ManyBody.regionMatrix ρ D`, vector first, with
the site family implicit.

This script applies the rename table to every `.lean` file below a directory:

* qualified names (`Entropy.regionState`, `FiniteProduct.entropy`, ...) everywhere;
* bare names inside files that `open` or are in `namespace Entropy` / `FiniteProduct`
  (and, for TNLean, `TNLean.Lattice`);
* argument changes: the region and the vector change places for the definitions, the explicit
  family argument of the `FiniteProduct` definitions is dropped, `n : V → ℕ` becomes
  `X := fun v ↦ Fin (n v)`, and TNLean's `reducedState Λ q Ω A` loses `Λ q`. Arguments are
  parsed with balanced brackets, so they may be arbitrary terms.

A site whose arguments cannot be parsed (a partial application, a lemma name inside `rw [...]`
that needs arguments it does not have, a bridge lemma that becomes trivial) is left unchanged
and reported with its location. A trivial bridge standing alone in a rewrite list is dropped
with its separator; a list it empties is deleted when another tactic follows at the same
indentation, and otherwise left and reported, since it may close a goal that became reflexive.

The surviving definitions `ManyBody.regionState` and `ManyBody.regionEntropy` keep their names
but now take the vector first, so their existing calls are rewritten by a separate pass,
`--part M`, which must run exactly once and before the others. The other parts are `A` (the
`Entropy` abbreviations and the module moves), `B` (`FiniteProduct` and `TNLean.Lattice`) and
`C` (below); the default `--part all` is A, B and C together. Parts A, B, C and all are
idempotent: after them no old name of the part occurs, and a second run rewrites nothing. Lines
that a rewrite makes longer than 100 characters are broken inside brackets; a line that cannot
be broken is reported.

Part C replaces `ManyBody.splitEquiv β R : Config β ≃ RegionConfig β R × RegionConfig β Rᶜ` by
`ManyBody.cutEquiv β R : Config β ≃ RegionConfig β R × ComplConfig β R` (table `PART_C`). Only
qualified names `ManyBody.splitEquiv…` are rewritten, since other namespaces have their own
`splitEquiv`; a bare old name in a file that opens or is in `ManyBody` (and declares no name of
that spelling) is reported. `splitEquiv_symm_apply_of_mem β R x y v hv` becomes
`cutEquiv_symm_apply_mem x y hv` (the same for `_of_notMem`); the deleted `splitEquiv_apply_fst`
and `_snd` are reported, as is any site with a named argument. In a file that uses a qualified
`ManyBody.splitEquiv…` name, the type `RegionConfig X Rᶜ` (also `RegionConfig X (A ∪ B)ᶜ`)
becomes `ComplConfig X R`, unless the file applies `regionState`, `regionMatrix` or
`regionEntropy` to a complement region: then those types are reported. The uses of
`ManyBody.complementEquiv` and, in such files, of `mem_compl` are reported for review (they are
not old names, so `--check` does not list them).

Contract: this is a one-time migration tool. On TNLean (and on any branch of it) it either
rewrites a site correctly or leaves it unchanged and reports it, and `--check` lists every old
name left. A construct that does not occur there, such as a renamed name inside a string, may
be left unchanged and reported rather than handled.

Usage:
    python3 scripts/migrate_region_vocabulary.py DIR --part M    # once
    python3 scripts/migrate_region_vocabulary.py DIR [--part A|B|C|all] [--check] [--report FILE]

`--check` changes nothing and reports the remaining old names and the `open` lines of a
dissolved namespace (exit status 1 if any).
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass, field

ID = r"[\w'!?₀-₉ₐ-ₜᵢ-ᵪ]"
KEYWORDS = {
    "at", "with", "using", "then", "else", "do", "in", "from", "fun", "by", "if", "let",
    "have", "show", "calc", "match", "only", "generalizing", "says", "where", "deriving",
    "theorem", "lemma", "def", "abbrev", "instance", "example", "end", "namespace", "section",
    "open", "variable", "omit", "include", "λ", "∀", "∃", "Σ", "∑", "∏",
}
OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}


@dataclass
class Rule:
    """Rewrite `old` to `new` and apply `ops` to its positional arguments.

    `ops` entries: ("drop", i) removes positional argument i; ("swap", i, j) exchanges
    positional arguments i and j; ("nfam", i) replaces the dimension function in positional
    argument i by the family `fun v ↦ Fin (n v)`; ("named", i, name) turns positional argument i
    into the named argument `(name := ...)`; ("ins", i, t) inserts the positional argument `t`
    before positional argument i. `need` is the number of positional arguments the
    operations require. `nfam_named` rewrites `(n := e)` to `(X := fun v ↦ Fin (e v))`, with
    `fam` in place of `X` when the survivor names its family otherwise.
    `trivial` marks a bridge lemma that becomes `rfl`: it is reported, not rewritten.
    `keep`, `named_ok` and `note` (part C) are described at the fields.
    `addx` supplies `(X := fun v ↦ Fin (n v))` outside comments: the survivor cannot infer the
    family from region matrices `(v : D) → Fin (n v)` alone, which the old abbreviation fixed.
    """

    old: str
    new: str
    ops: list = field(default_factory=list)
    need: int = 0
    nfam_named: bool = False
    trivial: bool = False
    addx: bool = False
    rename_unapplied: bool = False
    fam: str = "X"
    # `keep`: a deleted name with no rewrite; every site is left and reported (and `--check`
    # lists it). `named_ok = False`: a site with a named argument is left and reported, since
    # the survivor's binders have other names. `note`: the reason printed with a remaining site.
    keep: bool = False
    named_ok: bool = True
    note: str = ""


def nfam(arg: str) -> str:
    a = arg.strip()
    if a == "_":
        return a
    m = re.fullmatch(r"\(\s*fun\s+(\S+)(?:\s*:\s*[^↦=]+)?\s*(?:↦|=>)\s*(.+)\)", a, re.S)
    if m:
        var, body = m.group(1), m.group(2).strip()
        inner = body if re.fullmatch(ID + r"+", body) else f"({body})"
        return f"(fun {var} ↦ Fin {inner})"
    if re.fullmatch(r"[\w'.₀-₉]+", a):
        return f"(fun v ↦ Fin ({a} v))"
    return f"(fun v ↦ Fin ({a} v))"


def inline_site(n: str) -> str:
    """The body of `SiteConfig n`: `∀ v, Fin (n v)`, β-reduced as the abbreviation was."""
    a = n.strip()
    m = re.fullmatch(r"\(\s*fun\s+(\S+)\s*:\s*([^↦=]+?)\s*(?:↦|=>)\s*(.+)\)", a, re.S)
    if m:
        var, typ, body = m.group(1), m.group(2).strip(), m.group(3).strip()
        inner = body if re.fullmatch(ID + r"+", body) else f"({body})"
        return f"(({'_' if var == '_' else var} : {typ}) → Fin {inner})"
    if a.startswith("(") and re.match(r"\(\s*fun\b", a):
        return f"(ManyBody.Config {nfam(a)})"
    return f"(∀ v, Fin ({a} v))"


def inline_region(n: str, d: str) -> str:
    """`RegionConfig n D` as `ManyBody.RegionConfig (fun v ↦ Fin (n v)) D`. The named form keeps
    the family inferable: `RegionConfig ?X D =?= RegionConfig (fun v ↦ Fin (n v)) D` unifies the
    arguments, while the raw type `(v : {v // v ∈ D}) → Fin (n v)` leaves the non-pattern problem
    `?X ↑v =?= Fin (n ↑v)`."""
    return f"(ManyBody.RegionConfig {nfam(n.strip())} {d.strip()})"


def nfam_body(arg: str) -> str:
    """`e` in `(n := e)` to the body of `(X := ...)`."""
    return nfam(arg if arg.startswith("(") else f"({arg})" if " " in arg else arg)[1:-1]


# --------------------------------------------------------------------------------------------
# The table.

ENTROPY_RENAMES = {
    # abbreviation -> survivor; positional operations
    # duplicates of the `FiniteProduct` complement lemmas: the survivor takes the family first
    # (`_`, inferred from the vector), and `regionEntropy_compl` took the region first
    "regionEntropy_compl": ("ManyBody.regionEntropy_compl", [("swap", 0, 1), ("ins", 0, "_")], 2),
    "rank_regionState_compl": ("ManyBody.rank_regionState_compl", [("ins", 0, "_")], 2),
    "SiteConfig": ("@inline_site", [], 1),
    "RegionConfig": ("@inline_region", [], 2),
    "IsSupportedOn": ("ManyBody.IsSupportedOn", [], 0),
    "cutEquiv": ("ManyBody.cutEquiv", [("nfam", 0)], 1),
    "cutOperator": ("ManyBody.cutOperator", [], 0),
    "cutVector": ("ManyBody.cutVector", [], 0),
    "cutEquiv_symm_apply_mem": ("ManyBody.cutEquiv_symm_apply_mem", [], 0),
    "cutEquiv_symm_apply_not_mem": ("ManyBody.cutEquiv_symm_apply_not_mem", [], 0),
    "localLift": ("ManyBody.place", [], 0),
    "localLift_mul": ("ManyBody.place_mul", [], 0),
    "localLift_one": ("ManyBody.place_one", [], 0),
    "localLift_conjTranspose": ("ManyBody.place_conjTranspose", [], 0),
    "localLift_add": ("ManyBody.place_add", [], 0),
    "localLift_smul": ("ManyBody.place_smul", [("swap", 0, 1)], 2),
    "localLift_mul_localLift_inv": ("ManyBody.place_mul_place_inv", [], 0),
    "localLift_inv_mul_localLift": ("ManyBody.place_inv_mul_place", [], 0),
    "isSupportedOn_localLift": ("ManyBody.place_mem_supportedOperators", [], 0),
    "inner_localLift": ("ManyBody.inner_place", [], 0),
    "cutOperator_localLift": ("ManyBody.cutOperator_place", [], 0),
    # the temporary forwarding lemmas of the entropy layer
    "isSupportedOn_one": ("@tpl:one_mem (ManyBody.supportedOperators (fun v ↦ Fin (n v)) {0})",
                          [], 1),
    "commute_of_isSupportedOn_disjoint": (
        "@tpl:ManyBody.commute_of_mem_supportedOperators_of_disjoint {0} {1} {2s}", [], 4),
    "posSemidef_of_localLift": ("@tpl:ManyBody.posSemidef_place_iff.mp {0}", [], 1),
    "localLift_apply": ("ManyBody.place_apply", [], 0),
    "localLift_sub": ("ManyBody.place_sub", [], 0),
    # the old form took an unused configuration as its last argument
    "inner_conj_eq_of_isSupportedOn": ("ManyBody.inner_conj_eq_of_mem_supportedOperators",
                                       [("drop", 3)], 4),
    "regionState": ("ManyBody.regionState", [("swap", 0, 1)], 2),
    "regionState_isHermitian": ("ManyBody.regionState_isHermitian", [], 0),
    "regionState_posSemidef": ("ManyBody.regionState_posSemidef", [], 0),
    "trace_regionState": ("ManyBody.trace_regionState", [], 0),
    "regionEntropy": ("ManyBody.regionEntropy", [("swap", 0, 1)], 2),
    "trace_regionState_eq_one": ("ManyBody.trace_regionState_eq_one", [], 0),
    "regionEntropy_eq_entropy": (None, [], 0),
    "crossingTerms": ("ManyBody.crossingTerms", [], 0),
    "IsOneSided": ("Matrix.IsOneSided", [], 0),
    "HasProductDecomposition": ("Matrix.HasProductDecomposition", [], 0),
    "InnerConfig": ("ManyBody.InnerConfig", [], 0),
    "OuterConfig": ("ManyBody.OuterConfig", [], 0),
    "glueConfig": ("ManyBody.glueConfig", [], 0),
    "innerPart": ("ManyBody.innerPart", [], 0),
    "outerPart": ("ManyBody.outerPart", [], 0),
    "eq_glueConfig_iff": ("ManyBody.eq_glueConfig_iff", [], 0),
    "innerPart_glueConfig": ("ManyBody.innerPart_glueConfig", [], 0),
    "outerPart_glueConfig": ("ManyBody.outerPart_glueConfig", [], 0),
    "glueIsometry": ("ManyBody.glueIsometry", [], 0),
    "sliceIsometry": ("ManyBody.sliceIsometry", [], 0),
    "glueIsometry_conjTranspose_mul_self": ("ManyBody.glueIsometry_conjTranspose_mul_self", [], 0),
    "sliceIsometry_conjTranspose_mul_self": ("ManyBody.sliceIsometry_conjTranspose_mul_self", [], 0),
    # a duplicate of the existing matrix lemma
    "norm_le_one_of_isometry": ("Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one", [], 0),
    "glueIsometry_mul_conjTranspose_apply": ("ManyBody.glueIsometry_mul_conjTranspose_apply", [], 0),
    "sliceIsometry_conj_apply": ("ManyBody.sliceIsometry_conj_apply", [], 0),
    "card_innerConfig": ("ManyBody.card_innerConfig", [], 0),
    "card_innerConfig_le": ("ManyBody.card_innerConfig_le", [], 0),
    "regionState_eq_reducedPure": (None, [], 0),
}

# Moved declarations that keep their dimension function `n` (no `(n := e)` conversion).
KEEP_N = {
    "crossingTerms", "IsOneSided", "HasProductDecomposition", "InnerConfig", "OuterConfig",
    "glueConfig", "innerPart", "outerPart", "eq_glueConfig_iff", "innerPart_glueConfig",
    "outerPart_glueConfig", "glueIsometry", "sliceIsometry", "glueIsometry_conjTranspose_mul_self",
    "sliceIsometry_conjTranspose_mul_self", "norm_le_one_of_isometry",
    "glueIsometry_mul_conjTranspose_apply", "sliceIsometry_conj_apply", "card_innerConfig",
    "card_innerConfig_le",
}

# `Entropy.IsSupportedOn.foo` lemmas move to `ManyBody.IsSupportedOn.foo` (dot notation).
# `Entropy` names whose survivor is introduced with the dissolution of `FiniteProduct`
PART_B_ENTROPY = {"trace_regionState_eq_one", "regionEntropy_eq_entropy",
                  "regionState_eq_reducedPure", "regionEntropy_compl", "rank_regionState_compl"}

# `ManyBody` declarations removed as duplicates -> survivor (relative to `ManyBody`)
MANYBODY_RENAMES = {
    "apply_eq_of_mem_supportedOperators": "IsSupportedOn.apply_eq",
}

# The placement lemmas whose survivor needs the family named (see `Rule.addx`).
ADDX: set[str] = set()

ISSUPPORTEDON_DOT = {
    # dot name -> (new dot name, positional arguments to drop, exact number of positional
    # arguments the rule needs (None: at least the dropped ones)); applied in `Entropy` files only
    # `R.exists_localLift σ₀` -> `ManyBody.exists_eq_place_of_mem_supportedOperators R`
    "exists_localLift": ("@fn:ManyBody.exists_eq_place_of_mem_supportedOperators", [0], None),
    # the old `Entropy.IsSupportedOn.mul hX hY σ₀` took an unused configuration
    "mul": ("mul", [1], 2),
}

FINITE_PRODUCT_DEFS = {
    # FiniteProduct definition -> survivor, operations (the family is the first argument)
    "reducedPure": ("ManyBody.regionState", [("drop", 0)], 1),
    "reducedMatrix": ("ManyBody.regionMatrix", [("drop", 0)], 1),
    "entropy": ("ManyBody.regionEntropy", [("drop", 0)], 1),
    "mutualInformation": ("ManyBody.regionMutualInformation", [("drop", 0)], 1),
    "Configuration": ("ManyBody.RegionConfig", [], 0),
    "reducedPure_posSemidef": ("ManyBody.regionState_posSemidef", [("drop", 0), ("swap", 0, 1)], 3),
    "trace_reducedPure": ("ManyBody.trace_regionState_eq_one",
                          [("drop", 0), ("drop", 0), ("named", 1, "D")], 4),
}

LATTICE = {
    # TNLean.Lattice (TNLean/Lattice/RegionalEntropy, RegionalEntropyBridge, EntropyDimension)
    "reducedState": ("ManyBody.regionState", [("drop", 0), ("drop", 0)], 4),
    "regionalEntropy": ("ManyBody.regionEntropy", [("drop", 0), ("drop", 0)], 4),
    "reducedState_posSemidef": ("ManyBody.regionState_posSemidef",
                                [("drop", 0), ("drop", 0), ("swap", 0, 1)], 4),
    "reducedState_isHermitian": ("ManyBody.regionState_isHermitian",
                                 [("drop", 0), ("drop", 0), ("swap", 0, 1)], 4),
    "regionalEntropy_le_card_mul_log": ("ManyBody.regionEntropy_le_card_mul_log",
                                        [("drop", 0), ("drop", 0), ("drop", 0)], 5),
    "regionEntropy_le_card_mul_log": ("ManyBody.regionEntropy_le_card_mul_log", [], 0),
}
LATTICE_TRIVIAL = [
    "reducedState_eq_regionState", "regionalEntropy_eq_regionEntropy",
    "reducedState_eq_finiteProduct", "regionalEntropy_eq_finiteProduct",
]
LATTICE_HAND = [
    "regionEntropy_union_le", "regionEntropy_le_union_add", "regionEntropy_empty",
    "regionEntropy_univ", "regionEntropy_union_add_inter_le", "regionEntropy_sdiff_eq_of_eq_zero",
    "regionEntropy_union_eq_of_eq_zero", "regionEntropy_symmDiff_eq_of_eq_zero",
    "one_le_supportDim_const", "regionEntropy_eq_zero_of_localDimension_one", "card_regionConfig",
]

# Part C: `ManyBody.splitEquiv β R : Config β ≃ RegionConfig β R × RegionConfig β Rᶜ` gives way
# to `ManyBody.cutEquiv β R : Config β ≃ RegionConfig β R × ComplConfig β R`, with
# `ComplConfig β R = (v : {v // v ∉ R}) → β v`. Names relative to `ManyBody`:
# old -> (survivor, or None for a deleted name whose sites are reported; ops; need; note).
# Only the qualified spellings are rewritten: TNLean has its own `Config.splitEquiv`, a private
# `splitEquiv` and `splitEquiv_symm_comp_relabel`, and QICLean has `TensorPower.splitEquiv`.
# A bare old name in a file that opens or is in `ManyBody`, and declares no name of that
# spelling, is reported. To add a rename, add a line here.
PART_C = {
    "splitEquiv": ("cutEquiv", [], 0, ""),
    # old explicit arguments (β) (R) (x) (y) (v) (hv); new (x) (y) {v} (hv)
    "splitEquiv_symm_apply_of_mem": ("cutEquiv_symm_apply_mem",
                                     [("drop", 0), ("drop", 0), ("drop", 2)], 6, ""),
    "splitEquiv_symm_apply_of_notMem": ("cutEquiv_symm_apply_not_mem",
                                        [("drop", 0), ("drop", 0), ("drop", 2)], 6, ""),
    "splitEquiv_apply_fst": (None, [], 0, "deleted rfl simp lemma: unfold `cutEquiv` by hand"),
    "splitEquiv_apply_snd": (None, [], 0, "deleted rfl simp lemma: unfold `cutEquiv` by hand"),
    "operatorSchmidtRank_splitEquiv_le": (
        "Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_finset_le", [], 0, ""),
}
# In a file that uses a qualified `ManyBody.splitEquiv…` name, the type `RegionConfig X Rᶜ`
# becomes `ComplConfig X R`; unless the file applies one of these to a complement region,
# whose matrices stay indexed by `RegionConfig X Rᶜ`: its types are then reported.
PART_C_REGION_FUNS = ("regionState", "regionMatrix", "regionEntropy")
# Names whose sites are reported, not rewritten, in every file (the old name survives).
PART_C_REVIEW = {
    "ManyBody.complementEquiv": "hand edit: composed with `cutEquiv`, it may now be redundant",
}
PART_C_ON = False  # set by `main` for `--part C` and `--part all`


# Modules that move (old module -> new module); `import` lines are rewritten.
MODULE_MOVES: dict[str, str] = {}


def load_module_moves(path: str) -> None:
    if os.path.exists(path):
        with open(path, encoding="utf8") as f:
            for l in f:
                l = l.strip()
                if l and not l.startswith("#"):
                    old, new = l.split()
                    MODULE_MOVES[old] = new


def finite_product_lemma_name(short: str) -> str:
    s = re.sub(r"(?<![A-Za-z])reducedPure", "regionState", short)
    s = re.sub(r"(?<![A-Za-z])reducedMatrix", "regionMatrix", s)
    s = re.sub(r"(?<![A-Za-z])mutualInformation", "regionMutualInformation", s)
    s = re.sub(r"(?<![A-Za-z])entropy", "regionEntropy", s)
    return "ManyBody." + s


def load_finite_product_names(path: str) -> list[str]:
    """The short names of the old `FiniteProduct` declarations, one per line."""
    with open(path, encoding="utf8") as f:
        return [l.strip() for l in f if l.strip() and not l.startswith("#")]


def build_rules(fp_names: list[str], part: str = "all") -> tuple[dict, dict, dict]:
    qualified: dict[str, Rule] = {}
    bare: dict[str, dict[str, Rule]] = {"Entropy": {}, "FiniteProduct": {}, "Lattice": {}}
    if part == "M":
        # Run once, before the other parts: the surviving definitions keep their names and
        # take the vector first, so every former `ManyBody.regionState D φ` is swapped.
        for short in ("regionState", "regionEntropy"):
            r = Rule("ManyBody." + short, "ManyBody." + short, [("swap", 0, 1)], 2)
            qualified[r.old] = r
            bare.setdefault("ManyBody", {})[short] = Rule(short, short, [("swap", 0, 1)], 2)
        return qualified, bare, {}
    if part in ("C", "all"):
        for short, (new, ops, need, note) in PART_C.items():
            r = Rule("ManyBody." + short, ("" if not new else new if "." in new
                                           else "ManyBody." + new), ops, need,
                     keep=new is None, named_ok=False, rename_unapplied=bool(ops),
                     note=note)
            qualified[r.old] = r
            bare.setdefault("ManyBody", {})[short] = Rule(
                short, "", keep=True,
                note="bare old name of part C in a `ManyBody` file: rewrite by hand")
        if part == "C":
            return qualified, bare, {}
    if part == "A":
        fp_names = []
        # duplicates removed inside `ManyBody` itself
        for short, new in MANYBODY_RENAMES.items():
            r = Rule("ManyBody." + short, "ManyBody." + new, [], 0)
            qualified[r.old] = r
            bare.setdefault("ManyBody", {})[short] = Rule(short, new, [], 0)
    for short, (new, ops, need) in ENTROPY_RENAMES.items():
        # a survivor that part B introduces is only targeted by part B (and `all`)
        if (part == "B") != (short in PART_B_ENTROPY) and part != "all":
            continue
        r = Rule("Entropy." + short, new or "", ops, need, nfam_named=short not in KEEP_N,
                 trivial=new is None, addx=short in ADDX,
                 fam="β" if any(op[0] == "ins" for op in ops) else "X")
        qualified[r.old] = r
        bare["Entropy"][short] = r
    for short in fp_names:
        if short in FINITE_PRODUCT_DEFS:
            new, ops, need = FINITE_PRODUCT_DEFS[short]
        else:
            new, ops, need = finite_product_lemma_name(short), [], 0
        r = Rule("FiniteProduct." + short, new, ops, need,
                 rename_unapplied=short in ("entropy", "mutualInformation", "reducedMatrix",
                                            "reducedPure"))
        qualified[r.old] = r
        bare["FiniteProduct"][short] = r
    for short, (new, ops, need) in (LATTICE.items() if part != "A" else []):
        r = Rule("TNLean.Lattice." + short, new, ops, need)
        qualified[r.old] = r
        qualified["Lattice." + short] = r
        bare["Lattice"][short] = r
    for short in (LATTICE_TRIVIAL if part != "A" else []):
        r = Rule("TNLean.Lattice." + short, "", trivial=True)
        qualified[r.old] = r
        bare["Lattice"][short] = r
    for full in (("ManyBody.regionState_eq_reducedPure", "ManyBody.regionEntropy_eq_entropy")
                 if part != "A" else ()):
        r = Rule(full, "", trivial=True)
        qualified[full] = r
        bare.setdefault("Global", {})[full.split(".", 1)[1]] = r
    dot = ({"." + k: (v if v.startswith("@fn:") else "." + v, d, e)
            for k, (v, d, e) in ISSUPPORTEDON_DOT.items()}
           if part != "B" else {})
    return qualified, bare, dot


# --------------------------------------------------------------------------------------------
# Parsing.

def is_id_char(c: str) -> bool:
    return bool(re.match(ID, c)) or c == "."


def read_group(text: str, i: int) -> int:
    """`text[i]` opens a bracket; return the index after its match (or -1)."""
    stack = [OPEN[text[i]]]
    j = i + 1
    while j < len(text) and stack:
        c = text[j]
        if c in OPEN:
            stack.append(OPEN[c])
        elif c == stack[-1]:
            stack.pop()
        elif c in ")]}⟩⦄":
            return -1
        j += 1
    return j if not stack else -1


def line_indent(text: str, i: int) -> int:
    s = text.rfind("\n", 0, i) + 1
    return len(text[s:i]) - len(text[s:i].lstrip(" "))


def parse_args(text: str, i: int, head_indent: int):
    """Arguments after position `i`: a list of (sep, arg, kind) and the end position."""
    args = []
    j = i
    while True:
        k = j
        while k < len(text) and text[k] in " \t":
            k += 1
        if k < len(text) and text[k] == "\n":
            m = k
            while m < len(text) and text[m] in " \t\n":
                m += 1
            if m >= len(text) or line_indent(text, m) <= head_indent:
                break
            k = m
        if k == j and args:
            break
        if k >= len(text):
            break
        c = text[k]
        if c in OPEN:
            e = read_group(text, k)
            if e < 0:
                break
            # a projection or field access `(...).2`, `(...).symm` belongs to the argument
            while e + 1 < len(text) and text[e] == "." and is_id_char(text[e + 1]) and \
                    text[e + 1] != ".":
                e += 1
                while e < len(text) and is_id_char(text[e]):
                    e += 1
            arg = text[k:e]
            kind = "named" if re.match(r"\(\s*[\w']+\s*:=", arg) else "pos"
            args.append((text[j:k], arg, kind))
            j = e
            continue
        if c in "∅⊤⊥":
            args.append((text[j:k], c, "pos"))
            j = k + 1
            continue
        if is_id_char(c) and c != ".":
            e = k
            while e < len(text) and is_id_char(text[e]):
                e += 1
            word = text[k:e]
            if word in KEYWORDS or word.split(".")[0] in KEYWORDS:
                break
            args.append((text[j:k], word, "pos"))
            j = e
            continue
        break
    return args, j


def apply_ops(rule: Rule, args):
    pos = [i for i, a in enumerate(args) if a[2] == "pos"]
    if len(pos) < rule.need:
        return None
    vals = [list(a) for a in args]
    work = [vals[i] for i in pos]
    named_n = rule.nfam_named and any(
        a[2] == "named" and re.fullmatch(r"\(\s*n\s*:=\s*(.+)\)", a[1], re.S) for a in args)
    dropped = []
    for op in rule.ops:
        if op[0] == "drop":
            dropped.append(work.pop(op[1]))
        elif op[0] == "swap":
            a, b = op[1], op[2]
            work[a][1], work[b][1] = work[b][1], work[a][1]
        elif op[0] == "nfam":
            work[op[1]][1] = nfam(work[op[1]][1])
        elif op[0] == "named":
            work[op[1]][1] = f"({op[2]} := {work[op[1]][1]})"
        elif op[0] == "ins" and not named_n:
            # a family given by name `(n := e)` becomes `(fam := ...)`, so nothing is inserted
            work[op[1]][1] = op[2] + " " + work[op[1]][1]
    out = []
    for a in vals:
        if a[2] == "named":
            if rule.nfam_named:
                m = re.fullmatch(r"\(\s*n\s*:=\s*(.+)\)", a[1], re.S)
                if m:
                    a = [a[0], f"({rule.fam} := {nfam_body(m.group(1).strip())})", "named"]
            out.append(a)
        elif any(a is d for d in dropped):
            continue
        else:
            out.append(a)
    return "".join(sep + arg for sep, arg, _ in out)


def contexts(text: str) -> set[str]:
    ctx = set()
    if re.search(r"^\s*namespace\s+Entropy\b(?!\.)", text, re.M) or \
            re.search(r"^\s*open\b[^\n]*(?<![\w.])Entropy(?![\w.])", text, re.M):
        ctx.add("Entropy")
    if re.search(r"^\s*namespace\s+FiniteProduct\b", text, re.M) or \
            re.search(r"^\s*open\b[^\n]*(?<![\w.])FiniteProduct(?![\w.])", text, re.M):
        ctx.add("FiniteProduct")
    if re.search(r"^\s*namespace\s+ManyBody\b", text, re.M) or \
            re.search(r"^\s*open\b[^\n]*(?<![\w.])ManyBody(?![\w.])", text, re.M):
        ctx.add("ManyBody")
    if re.search(r"^\s*namespace\s+(TNLean\.)?Lattice\b", text, re.M) or \
            re.search(r"^\s*open\b[^\n]*(?<![\w.])(TNLean\.)?Lattice(?![\w.])", text, re.M):
        ctx.add("Lattice")
    return ctx


@dataclass
class Report:
    rewritten: int = 0
    files: set = field(default_factory=set)
    unhandled: list = field(default_factory=list)
    remaining: list = field(default_factory=list)
    # old name -> [sites, files] (filled for part C)
    per: dict = field(default_factory=dict)

    def count(self, name: str, path: str, n: int = 1) -> None:
        if PART_C_ON and (name.startswith("ManyBody.") and name[9:] in PART_C or
                          name == COMPL_TYPE):
            e = self.per.setdefault(name, [0, set()])
            e[0] += n
            e[1].add(path)


def comment_spans(text: str, strings: bool = False) -> list[tuple[int, int]]:
    """The comments of `text`, and its string literals too if `strings`."""
    spans, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("--", i):
            e = text.find("\n", i)
            e = n if e < 0 else e
            spans.append((i, e))
            i = e
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            spans.append((i, j))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if strings:
                spans.append((i, j + 1))
            i = j + 1
        else:
            i += 1
    return spans


def in_spans(spans, i: int):
    lo, hi = 0, len(spans)
    while lo < hi:
        mid = (lo + hi) // 2
        a, b = spans[mid]
        if b <= i:
            lo = mid + 1
        elif a > i:
            hi = mid
        else:
            return spans[mid]
    return None


DECL_BEFORE = re.compile(r"(theorem|lemma|def|abbrev|instance|structure|class)\s+(_root_\.)?$")


def lineno(text: str, i: int) -> int:
    return text.count("\n", 0, i) + 1


def receiver_start(text: str, i: int) -> int:
    """The start of the term that ends at `i`: identifiers, projections and bracket groups."""
    k = i
    while k > 0:
        c = text[k - 1]
        if c in ")]⟩":
            depth, k = 0, k - 1
            while k >= 0:
                if text[k] in ")]⟩":
                    depth += 1
                elif text[k] in "([⟨":
                    depth -= 1
                    if depth == 0:
                        break
                k -= 1
        elif is_id_char(c):
            k -= 1
        else:
            break
    return k


def symm_of(arg: str) -> str:
    """`arg.symm`, simplifying a double `.symm`."""
    if arg.endswith(".symm"):
        return arg[:-5]
    if re.fullmatch(r"[\w'.]+", arg) or (arg.startswith("(") and arg.endswith(")")):
        return arg + ".symm"
    return "(" + arg + ").symm"


def drop_open(text: str):
    """Remove the namespaces in `OPEN_DROP` from the `open` commands, with the numbers of the
    lines deleted outright (a line that keeps another namespace is edited in place), of all the
    lines changed, and of the lines left for a hand edit. Only commands outside comments and
    strings count. A trailing comment stays; a command-local `open N in` with no namespace left
    goes with its `in`; the selective forms `open N (x)`, `open N hiding x` and
    `open N renaming x → y` of a dissolved namespace are left and reported. It runs once a
    file's rewriting passes are done: the passes need the `open` line to recognize the bare
    names."""
    spans = comment_spans(text, strings=True)
    kept, removed, touched, left = [], [], [], []
    offset = 0
    for i, ln in enumerate(text.split("\n")):
        start, offset = offset, offset + len(ln) + 1
        mm = re.match(r"(\s*open (?:scoped )?)(.*?)(\s*--.*)?$", ln)
        if not mm or in_spans(spans, start + len(mm.group(1)) - 1) is not None:
            kept.append(ln)
            continue
        body, note = mm.group(2), mm.group(3) or ""
        bm = re.match(r"(.*?)(\s+in\b.*)?$", body)
        head, tail = bm.group(1), bm.group(2) or ""
        words = head.split()
        if not any(w in OPEN_DROP for w in words):
            kept.append(ln)
            continue
        touched.append(i + 1)
        if any(not re.fullmatch(r"[\w'.]+", w) for w in words) or \
                any(w in ("hiding", "renaming") for w in words):
            # a selective opening: its names moved and may be renamed
            left.append(i + 1)
            kept.append(ln)
            continue
        ws = [w for w in words if w not in OPEN_DROP]
        indent = re.match(r"\s*", ln).group(0)
        if ws:
            ln = mm.group(1) + " ".join(ws) + tail + note
        elif tail.strip() == "in" or (not tail and not note):
            removed.append(i + 1)
            continue
        elif tail:
            # `open N in cmd` on one line: the command stays, at the line's indentation
            ln = indent + re.sub(r"^\s+in\s+", "", tail) + note
        else:
            ln = indent + note.lstrip()
        kept.append(ln)
    return "\n".join(kept), removed, touched, left


def with_family(rule: Rule, text: str, start: int, span) -> str:
    """The survivor of an unapplied name, with the family supplied if `rule.addx`. A name that
    is itself an argument takes parentheses, so that the named argument is not read as one of
    the enclosing application."""
    if not rule.addx or span is not None:
        return rule.new
    before = text[:start].rstrip()
    head = not before or before[-1] in "[,(←" or before.endswith(":=") or \
        before.split()[-1] in ("by", "exact", "rw", "simp", "refine", "apply")
    return rule.new + XARG if head else "(" + rule.new + XARG + ")"


COMPL_TYPE = "RegionConfig X Rᶜ -> ComplConfig X R"
USES_SPLIT = re.compile(r"(?<![\w'.])ManyBody\.splitEquiv")
REGION_CONFIG = re.compile(r"(?<![\w'.@])(ManyBody\.)?RegionConfig(?![\w'])")


def read_term(text: str, i: int):
    """The span of the argument after `i` on the same line: an identifier or a bracket group,
    with a trailing `ᶜ` (an identifier's own `ᶜ` is one of its characters)."""
    k = i
    while k < len(text) and text[k] in " \t":
        k += 1
    if k == i or k >= len(text):
        return None
    if text[k] in OPEN:
        e = read_group(text, k)
        if e < 0:
            return None
        if text[e:e + 1] == "ᶜ":
            e += 1
        return k, e
    e = k
    while e < len(text) and (is_id_char(text[e]) or text[e] == "ᶜ"):
        e += 1
    word = text[k:e]
    if e == k or word in KEYWORDS:
        return None
    return k, e


def strip_compl(arg: str):
    """`R` for a region argument `Rᶜ`, `(A ∪ B)ᶜ` or `(Rᶜ)`, else None."""
    if arg.startswith("(") and arg.endswith(")") and read_group(arg, 0) == len(arg):
        inner = arg[1:-1].strip()
        if not inner.endswith("ᶜ"):
            return None
        core = inner[:-1]
        single = re.fullmatch(r"[\w'.]+", core) or (
            core.startswith("(") and read_group(core, 0) == len(core))
        return core if single else None
    if arg.endswith("ᶜ") and len(arg) > 1:
        core = arg[:-1]
        if re.fullmatch(r"[\w'.]+", core) or (core.startswith("(") and
                                               read_group(core, 0) == len(core)):
            return core
    return None


def complement_region_types(text: str):
    """The sites `(start, end, replacement)` of the types `RegionConfig X Rᶜ` of `text`."""
    sites = []
    for m in REGION_CONFIG.finditer(text):
        a1 = read_term(text, m.end())
        a2 = read_term(text, a1[1]) if a1 else None
        if not a2:
            continue
        core = strip_compl(text[a2[0]:a2[1]])
        if core is None:
            continue
        sites.append((m.start(), a2[1], (m.group(1) or "") + "ComplConfig" +
                      text[m.end():a2[0]] + core))
    return sites


def applies_region_fun_to_complement(text: str) -> bool:
    pat = re.compile(r"(?<![\w'.])(?:ManyBody\.)?(?:" + "|".join(PART_C_REGION_FUNS) +
                     r")(?![\w'])")
    for m in pat.finditer(text):
        a1 = read_term(text, m.end())
        a2 = read_term(text, a1[1]) if a1 else None
        if any(a and strip_compl(text[a[0]:a[1]]) is not None for a in (a1, a2)):
            return True
    return False


def complement_types(text: str, path: str, rep) -> tuple[str, int]:
    """Part C: `RegionConfig X Rᶜ` to `ComplConfig X R` in a file that uses a qualified
    `ManyBody.splitEquiv…` name outside comments, unless it applies a region function to a
    complement (then `part_c_notes` reports the types)."""
    spans = comment_spans(text, strings=True)
    if not any(in_spans(spans, m.start()) is None for m in USES_SPLIT.finditer(text)) or \
            applies_region_fun_to_complement(text):
        return text, 0
    sites = complement_region_types(text)
    for s0, e0, new in reversed(sites):
        text = text[:s0] + new + text[e0:]
    if sites:
        rep.rewritten += len(sites)
        rep.count(COMPL_TYPE, path, len(sites))
    return text, len(sites)


def part_c_notes(orig: str, final: str, path: str) -> list[str]:
    """The part C sites left for review in the final text of a file: `PART_C_REVIEW` names,
    the complement types kept in a file that applies a region function to a complement, and
    complement-membership proofs (the index of `ComplConfig X R` is `v ∉ R`, not `v ∈ Rᶜ`)."""
    notes = []
    spans = comment_spans(final)
    def code_lines(pat):
        return sorted({lineno(final, m.start()) for m in re.finditer(pat, final)
                       if in_spans(spans, m.start()) is None})
    for name, why in PART_C_REVIEW.items():
        notes += [f"{path}:{n}: `{name}`: {why}"
                  for n in code_lines(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'])")]
    cut = re.compile(r"(?<![\w'.])ManyBody\.(?:splitEquiv|cutEquiv)")
    if cut.search(orig) or cut.search(final):
        if applies_region_fun_to_complement(final):
            notes += [f"{path}:{n}: `RegionConfig X Rᶜ` kept (a region function is applied to "
                      "a complement here): use `ComplConfig X R` where it meets `cutEquiv`"
                      for n in sorted({lineno(final, s0)
                                       for s0, _, _ in complement_region_types(final)})]
        notes += [f"{path}:{n}: review `mem_compl`: `ComplConfig X R` is indexed by `v ∉ R`"
                  for n in code_lines(r"mem_compl")]
    return notes


def rewrite_text(text: str, path: str, qualified, bare, dot, swap_manybody: bool, rep: Report,
                 check: bool):
    original = text
    ctx = contexts(text)
    names: dict[str, Rule] = dict(qualified)
    for c in ctx | {"Global"}:
        if c == "ManyBody" and "Entropy" in ctx:
            continue
        for short, r in bare.get(c, {}).items():
            if c == "ManyBody" and r.keep and short in PART_C and re.search(
                    r"\b(?:def|abbrev|theorem|lemma)\s+(?:[\w'.]+\.)?" + re.escape(short) +
                    r"(?![\w'])", text):
                # the file declares a name of this spelling (its own `splitEquiv`)
                continue
            names.setdefault(short, r)
    # `export ManyBody (a b)` re-exports a survivor into the old namespace; once every old
    # spelling is rewritten to the survivor, the line has no purpose
    def drop_export(mm):
        ns = mm.group(1).split()
        if ns and all(names.get(x) is not None and names[x].new == "ManyBody." + x for x in ns):
            rep.rewritten += 1
            return ""
        return mm.group(0)
    if not check:
        text2 = re.sub(r"^export ManyBody \(([^)]*)\)\n(\n(?=\n))?", drop_export, text, flags=re.M)
        export_changed = text2 != text
        text = text2
    else:
        export_changed = False
    changed_c = False
    if PART_C_ON and not check:
        text, n_c = complement_types(text, path, rep)
        changed_c = n_c > 0
    alts = sorted(names, key=len, reverse=True)
    pat = re.compile(r"(?<![\w'.])(" + "|".join(re.escape(a) for a in alts) + r")(?![\w'])")
    out = []
    pos = 0
    changed = export_changed or changed_c
    spans = comment_spans(text)
    for m in pat.finditer(text):
        if m.start() < pos:
            continue
        name = m.group(1)
        if DECL_BEFORE.search(text[max(0, m.start() - 40):m.start()]):
            continue
        head = text[text.rfind("\n", 0, m.start()) + 1:m.start()]
        if re.match(r"\s*(?:export|open) ", head) and not re.search(r"\sin\s", head):
            # `export` and `open` lines name namespaces and the names they select; `drop_open`
            # handles the dissolved ones. The command after a same-line `open N in` is rewritten.
            continue
        limit = len(text)
        span = in_spans(spans, m.start())
        if span is not None:
            ls = text.rfind("\n", 0, m.start()) + 1
            le = text.find("\n", m.start())
            le = len(text) if le < 0 else le
            if text[ls:m.start()].count("`") % 2 == 0:
                continue
            close = text.find("`", m.end(), le)
            if close < 0:
                continue
            limit = close
        rule = names.get(name)
        if rule is None:
            continue
        line = lineno(text, m.start())
        snippet = text[m.start():text.find("\n", m.start())][:90]
        if check:
            rep.remaining.append(f"{path}:{line}: {snippet}" +
                                 (f"  [{rule.note}]" if rule.note else ""))
            continue
        if rule.keep:
            # a deleted name: the final scan reports the site with the rule's note
            continue
        if rule.trivial:
            # a bridge standing alone in a rewrite list is dropped with its arrow and comma
            if span is None:
                # the separator is read from the text already emitted, so that consecutive
                # bridges are dropped with their separators
                prev = "".join(out) + text[pos:m.start()]
                lm = re.search(r"(,\s*|\[\s*)(←\s*)?$", prev)
                after = text[m.end():]
                if lm and re.match(r"\s*[,\]]", after) and in_rewrite_list(prev, lm.end()):
                    opens = lm.group(1).startswith("[")
                    tail = re.match(r"\s*,\s*", after) if opens else None
                    # a list the drop empties is marked, so that only such lists are cleaned up
                    emptied = opens and tail is None
                    out = [prev[:lm.start()] + ("[" + EMPTIED if emptied else "[" if opens else "")]
                    pos = m.end() + (tail.end() if tail else 0)
                    rep.rewritten += 1
                    changed = True
                    continue
            rep.unhandled.append(f"{path}:{line}: bridge `{name}` becomes rfl: {snippet}")
            continue
        args, end = parse_args(text[:limit], m.end(), line_indent(text, m.start()))
        if not rule.named_ok and any(a[2] == "named" for a in args):
            rep.unhandled.append(f"{path}:{line}: `{name}` with a named argument: {snippet}")
            continue
        if rule.new.startswith("@inline"):
            pos_args = [a for a in args if a[2] == "pos"]
            if len(pos_args) < rule.need or any(a[2] != "pos" for a in args[:rule.need]):
                if not pos_args and span is not None:
                    continue
                rep.unhandled.append(f"{path}:{line}: `{name}` needs {rule.need} arguments: "
                                     f"{snippet}")
                continue
            used = args[:rule.need]
            body = (inline_site(used[0][1]) if rule.new == "@inline_site"
                    else inline_region(used[0][1], used[1][1]))
            after = m.end() + sum(len(sep) + len(arg) for sep, arg, _ in used)
            if m.start() > 0 and text[m.start() - 1] == "(" and text[after:after + 1] == ")" \
                    and body.startswith("(") and body.endswith(")"):
                body = body[1:-1]
            out.append(text[pos:m.start()])
            out.append(body)
            pos = after
            rep.rewritten += 1
            changed = True
            continue
        if rule.new.startswith("@tpl:"):
            pos_args = [a for a in args if a[2] == "pos"]
            if len(pos_args) < rule.need or any(a[2] != "pos" for a in args[:rule.need]):
                if span is None:
                    rep.unhandled.append(f"{path}:{line}: `{name}` needs {rule.need} arguments: "
                                         f"{snippet}")
                continue
            used = [a[1].strip() for a in args[:rule.need]]
            body = re.sub(r"\{(\d)(s?)\}",
                          lambda mm: symm_of(used[int(mm.group(1))]) if mm.group(2)
                          else used[int(mm.group(1))], rule.new[5:])
            rest = "".join(sep + arg for sep, arg, _ in args[rule.need:])
            after = m.end() + sum(len(sep) + len(arg) for sep, arg, _ in args)
            before = text[:m.start()].rstrip()
            head = (not before or before[-1] in "[,(←" or before.endswith(":=") or
                    before.split()[-1] in ("by", "exact", "refine", "apply")) and not rest
            out.append(text[pos:m.start()])
            out.append(body + rest if head else "(" + body + ")" + rest)
            pos = after
            rep.rewritten += 1
            changed = True
            continue
        new_args = apply_ops(rule, args) if (rule.ops or rule.nfam_named) else None
        npos = sum(1 for a in args if a[2] == "pos")
        if rule.rename_unapplied and npos == 0 and any(a[2] == "named" for a in args):
            # a named family `(β := e)` has no counterpart under the survivor's binder name
            rep.unhandled.append(f"{path}:{line}: `{name}` with a named argument: {snippet}")
            continue
        if rule.ops and new_args is None and npos == 0 and (rule.rename_unapplied or
                not any(op[0] in ("drop", "named") for op in rule.ops)):
            # An unapplied name (in `rw [...]`, `simp [...]`, a docstring): rename it only.
            new_args = None
            out.append(text[pos:m.start()])
            out.append(with_family(rule, text, m.start(), span))
            pos = m.end()
            rep.rewritten += 1
            rep.count(rule.old, path)
            changed = True
            continue
        if rule.ops and new_args is None:
            rep.unhandled.append(f"{path}:{line}: `{name}` needs {rule.need} arguments: {snippet}")
            continue
        out.append(text[pos:m.start()])
        if not args:
            out.append(with_family(rule, text, m.start(), span))
        else:
            out.append(rule.new)
            if rule.addx and span is None and not any(
                    a[2] == "named" and re.match(r"\(\s*[nX]\s*:=", a[1]) for a in args):
                out.append(XARG)
        if new_args is not None:
            out.append(new_args)
            pos = end
        else:
            pos = m.end()
        rep.rewritten += 1
        rep.count(rule.old, path)
        changed = True
    out.append(text[pos:])
    new_text = "".join(out)
    if not check:
        for old, (new, drops, exact) in (dot.items() if "Entropy" in ctx else []):
            dpat = re.compile(r"(?<=[\w')\]⟩])" + re.escape(old) + r"(?![\w'])")
            start = 0
            while True:
                dm = dpat.search(new_text, start)
                if not dm:
                    break
                args, end = parse_args(new_text, dm.end(), line_indent(new_text, dm.start()))
                pos = [i for i, a in enumerate(args) if a[2] == "pos"]
                recv = re.search(r"[\w'.]*$", new_text[:dm.start()]).group(0)
                if (exact is not None and len(pos) != exact) or (recv and recv[0].isupper()):
                    # a namespace such as `ContinuousAt.mul`, not a proof `hX.mul`
                    start = dm.end()
                    continue
                if len(pos) <= max(drops):
                    # left unchanged, as the module docstring promises, and reported
                    rep.unhandled.append(f"{path}:{lineno(new_text, dm.start())}: `{old}` "
                                         f"needs {max(drops) + 1} argument(s)")
                    start = dm.end()
                    continue
                else:
                    gone = {pos[d] for d in drops}
                    kept = "".join(sep + arg for i, (sep, arg, _) in enumerate(args)
                                   if i not in gone)
                    if new.startswith("@fn:"):
                        r0 = receiver_start(new_text, dm.start())
                        recv_txt = new_text[r0:dm.start()]
                        single = recv_txt.startswith("(") and \
                            read_group(recv_txt, 0) == len(recv_txt)
                        if not re.fullmatch(r"[\w'.]+", recv_txt) and not single:
                            recv_txt = "(" + recv_txt + ")"
                        call = new[4:] + " " + recv_txt + kept
                        if new_text[r0 - 1:r0] not in ("(", "[", " ", "\n") or kept:
                            call = "(" + call + ")"
                        new_text = new_text[:r0] + call + new_text[end:]
                        start = r0 + len(call)
                    else:
                        new_text = new_text[:dm.start()] + new + kept + new_text[end:]
                        start = dm.start() + len(new)
                rep.rewritten += 1
                changed = True
    if not check and changed:
        # a rewrite list emptied by the dropped bridges is deleted when a tactic follows at the
        # same indentation (it closed no goal, or that tactic would fail); one that ends its
        # block may close a reflexive goal, so it stays and the final scan reports it
        ls = new_text.split("\n")
        keep = []
        for i, ln in enumerate(ls):
            if EMPTY_LIST.match(ln):
                nxt = next((x for x in ls[i + 1:] if x.strip()), "")
                if line_indent_of(nxt) == line_indent_of(ln):
                    continue
            keep.append(ln)
        new_text = "\n".join(keep)
    if not check and MODULE_MOVES:
        def mv(mm):
            new = MODULE_MOVES.get(mm.group(2))
            return mm.group(1) + new if new else mm.group(0)
        # imports form the header of a Lean file: the lines before its first other command
        lines = new_text.split("\n")
        spans = comment_spans(new_text)
        offset, header = 0, len(lines)
        for i, ln in enumerate(lines):
            if ln.strip() and not ln.startswith("import ") and in_spans(spans, offset) is None \
                    and not ln.lstrip().startswith(("--", "/-")) and \
                    ln.strip() not in ("module", "prelude"):
                header = i
                break
            offset += len(ln) + 1
        # two old modules may move into one: keep its first import
        seen: set[str] = set()
        kept_lines = []
        for i, ln in enumerate(lines):
            if i < header and ln.startswith("import "):
                ln = re.sub(r"^(import\s+)(\S+)", mv, ln)
                if ln in seen:
                    continue
                seen.add(ln)
            kept_lines.append(ln)
        new_text2 = "\n".join(kept_lines)
        if new_text2 != new_text:
            new_text, changed = new_text2, True
    if new_text != original:
        rep.files.add(path)
    return new_text


MAX = 100
EMPTIED = "\ue000"  # marks a rewrite list emptied by the migration, until the report
EMPTY_LIST = re.compile(r"^[ \t]*(?:rw|rewrite|simp only|simp_rw) \[" + EMPTIED +
                        r"\](?:[ \t]+at[ \t][^\n]*)?[ \t]*$")
REWRITE_TACTIC = re.compile(r"(?:^|[\s(;>])(?:rw|rwa|rewrite|erw|simp_rw|nth_rw\s+\d+|"
                            r"nth_rewrite\s+\d+|simp|simpa|dsimp|simp_all|field_simp)[!?]?"
                            r"(?:\s+only)?\s*$")


def in_rewrite_list(text: str, end: int) -> bool:
    """Whether position `end` of `text` lies directly inside the list of a rewriting tactic
    (`rw [...]`, `simp only [...]`, ...), not in a list literal or another bracket."""
    depth, k = 0, end
    while k > 0:
        k -= 1
        c = text[k]
        if c in ")]}⟩":
            depth += 1
        elif c in "([{⟨":
            if depth == 0:
                return c == "[" and bool(REWRITE_TACTIC.search(text[:k]))
            depth -= 1
    return False


def line_indent_of(line: str) -> int:
    return len(line) - len(line.lstrip(" "))
OPEN_DROP: set[str] = set()
XARG = " (X := fun v ↦ Fin (n v))"


INFIX = ("≤", "<", "=", "+", "*", "∧", "∨", "→", "↔", "≠", "-", "•", "∣")


def wrap_line(line: str, in_doc: bool, depth0: int = 0):
    """Break `line` (longer than MAX characters) at whitespace inside a bracket (the bracket may
    be opened on an earlier line: `depth0` is the depth at the start of the line) or before a
    bracketed argument, at the shallowest such point, preferring a point before an argument;
    on a declaration line ending in `:=` also before an infix operator outside brackets;
    anywhere in a doc comment. Continuation lines are indented four more
    columns. Returns the list of lines, or None if no break point exists."""
    indent = len(line) - len(line.lstrip(" "))
    out, cur, d0 = [], line, depth0
    cont = " " * (indent + 4)
    sig = line.rstrip().endswith(":=") or line.rstrip().endswith(":= by")
    while len(cur) > MAX:
        depth, best, bestd = d0, -1, 10 ** 9
        start = len(cur) - len(cur.lstrip(" "))
        for k, c in enumerate(cur):
            if k > MAX:
                break
            if c in OPEN:
                depth += 1
            elif c in ")]}⟩⦄":
                depth -= 1
            elif c == " " and k > start and k + 1 < len(cur):
                ok_tok = cur[k - 1] not in " (" and cur[k + 1] not in " )],"
                if not ok_tok:
                    continue
                if cur[k + 1] == "[" and re.search(r"(?:^|\s)(?:rw|rwa|simp|simp only|simp_rw|"
                                                   r"nth_rw \d+|dsimp only|simpa only)$",
                                                   cur[:k]):
                    # a rewrite list stays on the line of its tactic
                    continue
                # cost: shallow first; at equal depth, before a bracketed argument or after a
                # comma rather than inside a short application such as `Fin (n v)`
                arg = cur[k + 1] in OPEN or cur[k - 1] == ","
                if in_doc:
                    d = 0
                elif depth >= 1:
                    d = 2 * depth + (0 if arg else 1)
                elif (sig and cur[k + 1:].startswith(INFIX)) or cur[k + 1] in OPEN:
                    d = 1
                else:
                    continue
                if d <= bestd:
                    best, bestd = k, d
        if best < 0:
            return None
        # bracket depth at the break, for the next piece
        dd = d0
        for c in cur[:best]:
            if c in OPEN:
                dd += 1
            elif c in ")]}⟩⦄":
                dd -= 1
        out.append(cur[:best].rstrip())
        cur, d0 = cont + cur[best + 1:].lstrip(), dd
    out.append(cur)
    return out


def line_depths(text: str) -> list[int]:
    """The bracket depth at the start of every line, outside comments and strings."""
    spans = comment_spans(text)
    depths, depth, i = [0], 0, 0
    si = 0
    while i < len(text):
        while si < len(spans) and spans[si][1] <= i:
            si += 1
        if si < len(spans) and spans[si][0] <= i < spans[si][1]:
            seg = text[i:spans[si][1]]
            depths.extend([depth] * seg.count("\n"))
            i = spans[si][1]
            continue
        c = text[i]
        if c in OPEN:
            depth += 1
        elif c in ")]}⟩⦄":
            depth = max(0, depth - 1)
        elif c == "\n":
            depths.append(depth)
        i += 1
    return depths


def wrap_changed(old: str, new: str, path: str, rep) -> str:
    import difflib
    ol, nl = old.split("\n"), new.split("\n")
    changed = set()
    for tag, _, _, j1, j2 in difflib.SequenceMatcher(None, ol, nl, autojunk=False).get_opcodes():
        if tag != "equal":
            changed.update(range(j1, j2))
    spans = comment_spans(new)
    depths = line_depths(new)
    offs, acc = [], 0
    for l in nl:
        offs.append(acc)
        acc += len(l) + 1
    res = []
    for i, l in enumerate(nl):
        if i in changed and len(l) > MAX:
            sp = in_spans(spans, offs[i] + len(l) - len(l.lstrip()))
            in_doc = sp is not None and new.startswith("/-", sp[0])
            if l.lstrip().startswith("--"):
                w = None
            else:
                w = wrap_line(l, in_doc, depths[i] if i < len(depths) else 0)
            if w is None:
                rep.unhandled.append(f"{path}:{len(res) + 1}: line longer than {MAX} characters")
                res.append(l)
            else:
                res.extend(w)
        else:
            res.append(l)
    return "\n".join(res)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("root")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--report")
    ap.add_argument("--part", choices=["M", "A", "B", "C", "all"], default="all",
                    help="M: exchange the arguments of the existing ManyBody.regionState / "
                         "regionEntropy calls, which now take the vector first (run ONCE, "
                         "before the other parts; it is not idempotent); A: the Entropy "
                         "abbreviations and module moves; B: FiniteProduct and TNLean.Lattice; "
                         "C: ManyBody.splitEquiv to ManyBody.cutEquiv; all: A, B and C")
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--finite-product-names",
                    default=os.path.join(here, "migrate_region_vocabulary_names.txt"))
    a = ap.parse_args()
    global PART_C_ON
    PART_C_ON = a.part in ("C", "all")
    load_module_moves(os.path.join(here, "migrate_region_vocabulary_modules.txt"))
    qualified, bare, dot = build_rules(load_finite_product_names(a.finite_product_names), a.part)
    if a.part in ("B", "all"):
        OPEN_DROP.add("FiniteProduct")
    rep = Report()
    for dp, dns, fs in os.walk(a.root):
        dns[:] = [d for d in dns if d not in (".lake", ".git", "build")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            with open(p, encoding="utf8") as h:
                t = h.read()
            if a.check:
                rewrite_text(t, p, qualified, bare, dot, False, rep, True)
                rep.remaining += [f"{p}:{n}: open line of a dissolved namespace"
                                  for n in drop_open(t)[2]]
                continue
            frep = Report()
            nt = rewrite_text(t, p, qualified, bare, dot, False, frep, False)
            for _ in range(4):
                # names inside the arguments of a rewritten call are rewritten on the next pass
                if nt == t or a.part == "M":
                    # the exchange of part M is not idempotent: one pass only
                    break
                t2 = rewrite_text(nt, p, qualified, bare, dot, False, frep, False)
                if t2 == nt:
                    break
                nt = t2
            if nt != t:
                nt = wrap_changed(t, nt, p, frep)
            rep.rewritten += frep.rewritten
            rep.files |= frep.files
            for k, (n, fs_) in frep.per.items():
                e = rep.per.setdefault(k, [0, set()])
                e[0] += n
                e[1] |= fs_
            # the sites left for a hand edit are the old names still in the final text, at their
            # final lines (the same list `--check` prints), with the dot sites and long lines the
            # passes could not rewrite
            final = Report()
            rewrite_text(nt, p, qualified, bare, dot, False, final, True)
            if OPEN_DROP and drop_open(nt)[2]:
                # the `open` lines go last; a remaining site moves up by the lines removed above it
                dropped, removed, _, left = drop_open(nt)
                def shift(entry):
                    mm = re.match(r"(.*?):(\d+):(.*)", entry, re.S)
                    if not mm:
                        return entry
                    n0 = int(mm.group(2))
                    return f"{mm.group(1)}:{n0 - sum(1 for r in removed if r < n0)}:{mm.group(3)}"
                final.remaining = [shift(e) for e in final.remaining]
                final.remaining += [shift(f"{p}:{n}: selective open of a dissolved namespace: "
                                          "open the survivors by hand") for n in left]
                if dropped != nt:
                    nt = dropped
                    rep.files.add(p)
            # an emptied rewrite list that ends its block is left for a hand edit; the marks of
            # the emptied lists go
            emptied = [f"{p}:{i + 1}: emptied rewrite list ends its block: delete it, or close "
                       "the goal with `rfl`"
                       for i, ln in enumerate(nt.split("\n")) if EMPTY_LIST.match(ln)]
            nt = nt.replace(EMPTIED, "")
            if nt != t:
                with open(p, "w", encoding="utf8") as h:
                    h.write(nt)
            rep.unhandled += final.remaining + emptied
            if PART_C_ON:
                rep.unhandled += part_c_notes(t, nt, p)
            rep.unhandled += [u for u in dict.fromkeys(frep.unhandled)
                              if re.search(r": (line longer than|`\.[\w']+` needs)", u)]
    lines = []
    if a.check:
        lines.append(f"remaining old names: {len(rep.remaining)}")
        lines += rep.remaining
    else:
        lines.append(f"rewritten sites: {rep.rewritten} in {len(rep.files)} files")
        lines += [f"  {k}: {n} sites in {len(fs_)} files"
                  for k, (n, fs_) in sorted(rep.per.items())]
        lines.append(f"sites left for a hand edit: {len(rep.unhandled)}")
        lines += rep.unhandled
    text = "\n".join(lines) + "\n"
    if a.report:
        with open(a.report, "w", encoding="utf8") as h:
            h.write(text)
        k = 1 if a.check else 2 + len(rep.per)
        print("\n".join(lines[:k]))
    else:
        sys.stdout.write(text)
    return 1 if a.check and rep.remaining else 0


if __name__ == "__main__":
    sys.exit(main())
