#!/usr/bin/env python3
"""Reject new pass-through declarations: one statement under a second name.

A pass-through is a declaration whose whole body applies another declaration
to its own arguments in order.  ``docs/import_structure.md``
forbids them: the caller uses the original name.

The rule is lexical and deliberately narrow.  A declaration is reported exactly
when all of the following hold, after Lean comments are removed.

1. It is a ``theorem``, ``lemma``, ``def`` or ``abbrev`` that starts in the
   first column of a module below ``QICLean/`` and outside ``QICLean/Archive``,
   after any attributes and the modifiers ``private``, ``protected``,
   ``public``, ``noncomputable`` and ``nonrec``.  An ``instance``, an
   ``example``, a structure field and a declaration nested in a ``where`` block
   are never reported.
2. Between its name and its ``:=`` there are only bracketed binders and an
   optional type.  It has at least one explicit binder ``(x y : T)``, no binder
   has a default value, and it is not followed by ``where``,
   ``termination_by`` or ``decreasing_by``.
3. Its body is ``F x₁ … xₙ``, ``by exact F x₁ … xₙ`` or
   ``by simpa using F x₁ … xₙ``, where ``x₁ … xₙ`` are exactly the names of
   its explicit binders, all of them, in the order they are bound, and
   nothing else follows.
4. ``F`` is a name without ``@``. It is not the declaration's own name,
   a binder or a module variable. If qualified, its namespace components start
   with capitals and are not bound variables (excluding hypothesis projections).

Unlike upstream's same-name-across-namespaces rule, this also catches renamed
and unqualified forwarding applications. This is a syntactic debt inventory,
not a proof that two statements are equivalent. It excludes argument changes,
named arguments, section-variable arguments, zero-argument aliases, indented
commands and more complex proofs. Review still enforces the broader architecture.

An entry is the full name of the declaration, built from the enclosing
``namespace`` commands, so that moving a module does not change it.

``PASS_THROUGH`` is a ratchet.  It lists the pass-throughs present when the
check was introduced.  A new pass-through fails, and so does an entry that is
no longer one: remove it in the change that deletes the declaration.  With
``--base-ref`` the set is also compared with its value at the merge base, and
an added entry fails, so a new pass-through cannot be admitted by recording
it. CI uses ``--base-revision`` to compare against the exact event base, including
the previous tip after a force-push.
"""

# Adapted from LionSR/TNLean scripts/check_pass_through_declarations.py at
# 7e8438a32f1f0435e3acec579a89656de1b3f07b (Apache-2.0).
# Changes: QICLean layer ownership and debt baselines; see docs/import_structure.md.

from __future__ import annotations

import argparse
import re
from collections.abc import Iterator, Mapping
from pathlib import Path

from check_import_layers import (
    ratchet_errors, records_at_merge_base, records_at_revision, tracked_sources,
)
from lean_import_syntax import strip_lean_comments

CHECKER_PATH = "scripts/check_pass_through_declarations.py"

IDENT = r"[^\W\d][\w'!?]*"
NAME = rf"{IDENT}(?:\.{IDENT})*"
ATTRIBUTES = r"(?:@\[[^\]]*\]\s*)*"
DECLARATION_RE = re.compile(
    rf"{ATTRIBUTES}(?:(?:private|protected|public|noncomputable|nonrec)\s+)*"
    rf"(?:theorem|lemma|def|abbrev)\s+({NAME})(?=[\s(\[{{⦃:])"
)
NAMESPACE_RE = re.compile(rf"namespace\s+({NAME})\s*$")
SCOPE_RE = re.compile(
    rf"{ATTRIBUTES}(?:(?:public|private|noncomputable|meta)\s+)*(?:section|mutual)\b"
)
END_RE = re.compile(r"end\b")
VARIABLE_RE = re.compile(r"variable\b")
CONTINUATION_RE = re.compile(r"(?:where|termination_by|decreasing_by)\b")
BODY_RE = re.compile(rf"(?:by\s+(?:exact|simpa\s+using)\s+)?({NAME})((?:\s+{IDENT})*)")
OPENING = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
CLOSING = frozenset(OPENING.values())


def commands(uncommented: str) -> list[str]:
    """Split a source into the blocks that start in the first column."""
    blocks: list[list[str]] = []
    for line in uncommented.splitlines():
        if line[:1].strip():
            blocks.append([line])
        elif blocks:
            blocks[-1].append(line)
    return ["\n".join(block) for block in blocks]


def matching_close(text: str, start: int) -> int | None:
    """Return the index of the bracket that closes the one at ``start``."""
    expected: list[str] = []
    for index in range(start, len(text)):
        character = text[index]
        if character in OPENING:
            expected.append(OPENING[character])
        elif character in CLOSING:
            if not expected or expected.pop() != character:
                return None
            if not expected:
                return index
    return None


def top_level_find(text: str, token: str, start: int = 0) -> int | None:
    """Return the first index at or after ``start`` of ``token`` outside all brackets."""
    index = start
    while index < len(text):
        if text[index] in OPENING:
            close = matching_close(text, index)
            if close is None:
                return None
            index = close + 1
        elif text.startswith(token, index):
            return index
        else:
            index += 1
    return None


def binder_names(group: str) -> list[str] | None:
    """Return the names bound by the inside of one binder group.

    ``None`` means the group is not a plain list of names with an optional type.
    """
    if top_level_find(group, ":=") is not None:
        return None
    colon = top_level_find(group, ":")
    names = (group if colon is None else group[:colon]).split()
    if not names or not all(re.fullmatch(IDENT, name) for name in names):
        return None
    return names


def header(block: str, start: int) -> tuple[list[str], set[str], str] | None:
    """Parse the binders after a declaration name.

    Returns the explicit binder names in order, the names of all binders, and
    the body after ``:=``; ``None`` if the declaration has another form.
    """
    explicit: list[str] = []
    bound: set[str] = set()
    index = start
    while True:
        while index < len(block) and block[index].isspace():
            index += 1
        if index >= len(block):
            return None
        character = block[index]
        if character in ("(", "{", "⦃", "["):
            close = matching_close(block, index)
            if close is None:
                return None
            group = block[index + 1 : close]
            names = binder_names(group)
            if names is None:
                if character != "[":
                    return None
                names = []
            elif character == "[" and top_level_find(group, ":") is None:
                # ``[NeZero d]`` binds no name: ``NeZero`` is a class, not a binder.
                names = []
            bound.update(names)
            if character == "(":
                explicit += names
            index = close + 1
        elif block.startswith(":=", index):
            return explicit, bound, block[index + 2 :]
        elif character == ":":
            assign = top_level_find(block, ":=", index + 1)
            if assign is None:
                return None
            return explicit, bound, block[assign + 2 :]
        else:
            return None


def variable_names(blocks: list[str]) -> set[str]:
    """Return every name bound by a ``variable`` command of a module."""
    names: set[str] = set()
    for block in blocks:
        if VARIABLE_RE.match(block) is None:
            continue
        index = 0
        while index < len(block):
            if block[index] in OPENING:
                close = matching_close(block, index)
                if close is None:
                    break
                group = block[index + 1 : close]
                if block[index] != "[" or top_level_find(group, ":") is not None:
                    names.update(binder_names(group) or [])
                index = close + 1
            else:
                index += 1
    return names


def pass_throughs_of_source(source: str) -> Iterator[str]:
    """Yield the full names of the pass-through declarations of one module."""
    uncommented, error = strip_lean_comments(source, mask_strings=True)
    if error is not None:
        raise ValueError(error)
    blocks = commands(uncommented)
    variables = variable_names(blocks)
    scopes: list[str | None] = []
    for position, block in enumerate(blocks):
        namespace = NAMESPACE_RE.match(block.strip())
        if namespace is not None:
            scopes.append(namespace.group(1))
            continue
        if SCOPE_RE.match(block) is not None:
            scopes.append(None)
            continue
        if END_RE.match(block) is not None:
            if scopes:
                scopes.pop()
            continue
        declaration = DECLARATION_RE.match(block)
        if declaration is None:
            continue
        if position + 1 < len(blocks) and CONTINUATION_RE.match(blocks[position + 1]):
            continue
        parsed = header(block, declaration.end())
        if parsed is None:
            continue
        explicit, bound, body = parsed
        application = BODY_RE.fullmatch(body.strip())
        if application is None or not explicit:
            continue
        function, arguments = application.group(1), application.group(2).split()
        namespaces = function.split(".")[:-1]
        name = declaration.group(1)
        if function in bound | variables or function == name:
            continue
        if any(not part[0].isupper() or part in bound | variables for part in namespaces):
            continue
        if arguments != explicit:
            continue
        if name.startswith("_root_."):
            yield name[len("_root_.") :]
        else:
            yield ".".join([scope for scope in scopes if scope is not None] + [name])


def pass_throughs(sources: Mapping[str, str]) -> dict[str, str]:
    """Return each pass-through declaration with the module that states it."""
    found: dict[str, str] = {}
    for module in sorted(sources):
        try:
            names = list(pass_throughs_of_source(sources[module]))
        except ValueError as error:
            raise ValueError(f"{module}: {error}") from error
        for name in names:
            if name in found:
                # Private declarations can share a lexical name across modules.
                # Do not let one recorded alias hide an additional forwarding copy.
                occurrence = 2
                key = f"{name} [{module}:{occurrence}]"
                while key in found:
                    occurrence += 1
                    key = f"{name} [{module}:{occurrence}]"
                found[key] = module
            else:
                found[name] = module
    return found


# Existing pass-throughs only, by full declaration name.  Never add an entry:
# use the original declaration at the call site.
PASS_THROUGH: frozenset[str] = frozenset({
    "ChoiJamiolkowski.choiMatrix_of_kraus_posSemidef",
    "ChoiJamiolkowski.eq_of_choiMatrix_eq",
    "ChoiJamiolkowski.exists_kraus_of_choiMatrix_eq_sum_vecMulVec",
    "ChoiJamiolkowski.exists_squareCompression_of_vector",
    "ChoiJamiolkowski.omegaCoeff_eq_inv",
    "ChoiJamiolkowski.omegaSlice_eq_single",
    "ChoiRectangular.eq_of_choiMatrix_eq",
    "ConditionalMovement.QuantumSSA.conditional_add_lower",
    "Douglas.posSemidefBB",
    "Entropy.IsSupportedOn",
    "Entropy.MarginalPhase.marginalUF",
    "Entropy.QuantumMarkovDecomposition",
    "Entropy.eq_of_forall_trace_mul_eq",
    "Entropy.inner_toEuclideanLin_eq_trace",
    "Entropy.liftXU_mulVec",
    "Entropy.localLift",
    "Entropy.regionState_isHermitian",
    "Entropy.regionState_posSemidef",
    "Entropy.strongSubadditivity",
    "IsCPMap.radon_nikodym_of_stinespring",
    "IsCPMap.tensorMapId_posSemidef",
    "IsKrausCP.tensorMapId_posSemidef",
    "IsPositiveMap.comp_unitaryConjLM_positive_tracePreserving",
    "IsPositiveMap.log_concave_jensen",
    "IsPositiveMap.rpow_concave_jensen",
    "IsPositiveMap.rpow_convex_jensen",
    "IsReducibleQDS",
    "IsTracePreservingMap.comp_unitaryConjLM_of_conj_traceAdjointMap_one",
    "Kraus.cumulativeSpan_eq_top",
    "Kraus.det_ne_zero_of_ker_all",
    "Kraus.eigenvalue_norm_le_one",
    "Kraus.eigenvalue_norm_le_one₂",
    "Kraus.gaugeEigenvector",
    "Kraus.gaugeTensor",
    "Kraus.injective_of_ker_all",
    "Kraus.isUnit_det_of_self_mul_conjTranspose_scalar",
    "Kraus.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero",
    "Kraus.scalarConditionalExpectation_mem_adjointFixedPoints",
    "Kraus.self_mul_conjTranspose_fixed_of_intertwining",
    "Kraus.spectralRadius_mixedTransfer_le_one",
    "Kraus.spectralRadius_mixedTransfer₂_le_one",
    "Kraus.transferMap",
    "Kraus.transferMap_isCPMap",
    "Kraus.ungauge_scalar_of_conjugated_scalar",
    "Kraus.wordSpan_mono_succ_of_one_mem_wordSpan_one",
    "Matrix.HolderFactor.tr_nonneg",
    "Matrix.IsHermitian.isUnitVector_eigenvectorBasis",
    "Matrix.complementaryWeylTwirl_eq_partialTraceRight_kronecker",
    "Matrix.gram_conj_eq_conjTranspose_of_dressed_adjoint",
    "Matrix.gram_conj_eq_gram_conj_of_dressed_adjoint",
    "Matrix.hasSchmidtRankLE_one_product",
    "Matrix.inner_frobeniusLinearEquiv",
    "Matrix.leftMiddleSlice",
    "Matrix.matrixReindexStarAlgEquiv",
    "Matrix.norm_ofReal_cpow_of_pos",
    "Matrix.norm_sqrt_sub_le",
    "Matrix.pureStateProj_posSemidef",
    "Matrix.tensorMapId_posSemidef_of_hasSchmidtRankLE_general",
    "Matrix.traceLeft",
    "Matrix.traceLeft_kronecker",
    "Matrix.traceNorm",
    "Matrix.traceNorm_eq_re_trace_sqrt",
    "Matrix.traceRight",
    "Matrix.trace_directSumDiagonalEmbedding",
    "TNLean.RelativeModularHalfMoment.sqrtState",
    "TensorPower.unitary_mulVec_single_mem_unitSphere",
    "TripartiteDecorrelation.marginalXB",
    "TwoSidedIdeal.ringEquiv_pi_simple_permutes_blockIdeals",
    "hermitianPart_isHermitian",
    "kraus_same_map_of_unitary_combination",
    "lieb_concavity",
    "stinespringBlock",
    "stinespringV_stinespringBlock",
    "trace_rpow_concave",
    "trace_rpow_convex",
    "unitInterval_eq_of_lowerSemicontinuous_nat_mul_eq",
    "wolf_prop_7_6_four_implies_three",
    "wolf_prop_7_6_three_implies_four",
})


def check_pass_throughs(
    sources: Mapping[str, str],
    recorded: frozenset[str] = PASS_THROUGH,
    base: frozenset[str] | None = None,
) -> list[str]:
    """Return the error messages of the check; an empty list means it passes."""
    current = pass_throughs(sources)
    return ratchet_errors(
        frozenset(current),
        recorded,
        base,
        new="Declaration only applies another declaration to its own arguments",
        stale="Declaration is no longer a pass-through but is listed in PASS_THROUGH; remove it",
        added="Entry added to PASS_THROUGH; this set may only shrink",
        describe=lambda name: f"{name} ({current[name]})" if name in current else name,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reject new declarations that only rename another declaration."
    )
    parser.add_argument("--root", type=Path, default=Path("."))
    base_options = parser.add_mutually_exclusive_group()
    base_options.add_argument("--base-revision", help="exact revision fixing the recorded entries (CI)")
    base_options.add_argument(
        "--base-ref",
        help="ref whose merge base with HEAD fixes the entries that may remain",
    )
    parser.add_argument(
        "--print-record", action="store_true", help="print the current pass-throughs and exit"
    )
    args = parser.parse_args()
    root = args.root.resolve()

    sources = tracked_sources(root)
    if args.print_record:
        for name in sorted(pass_throughs(sources)):
            print(f'        "{name}",')
        return 0

    base: frozenset[str] | None = None
    if args.base_ref is not None or args.base_revision is not None:
        try:
            read_base = records_at_revision if args.base_revision else records_at_merge_base
            revision = args.base_revision or args.base_ref
            base = read_base(root, revision, CHECKER_PATH, ("PASS_THROUGH",))[
                "PASS_THROUGH"
            ]
        except (SyntaxError, ValueError) as error:
            print(f"::error title=Pass-through check failed::{error}")
            return 1

    errors = check_pass_throughs(sources, PASS_THROUGH, base)
    for message in errors:
        print(f"::error title=Pass-through declaration policy::{message}")
    if errors:
        print(
            "A declaration must not restate another one under a second name, and "
            "PASS_THROUGH may only shrink. Use the original declaration at the call "
            "sites; see docs/import_structure.md."
        )
        return 1
    print(f"No new pass-through declarations ({len(PASS_THROUGH)} recorded ones remain).")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValueError as error:
        print(f"::error title=Pass-through check failed::{error}")
        raise SystemExit(1)
