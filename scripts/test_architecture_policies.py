#!/usr/bin/env python3
"""Architecture regression tests, including real Git base comparisons.

Adapted in part from LionSR/TNLean scripts/test_lean_file_policies.py at
7e8438a32f1f0435e3acec579a89656de1b3f07b (Apache-2.0): QICLean ownership,
broader forwarding rule, Git integration and new-layer debt checks.
"""
import subprocess
import tempfile
import unittest
from pathlib import Path

import check_import_layers as layers
import check_pass_through_declarations as forwarding
from lean_import_syntax import strip_lean_comments


class ImportLayerPolicyTests(unittest.TestCase):
    def test_layers_are_assigned_from_the_bottom_up(self) -> None:
        self.assertEqual(layers.layer_of("QICLean.Circuit.Gate.FinKronecker"), "gate")
        self.assertEqual(layers.layer_of("QICLean.ManyBody.Sites.Placement"), "sites")
        self.assertEqual(layers.layer_of("QICLean.ManyBody.Sites.PlacementNorm"), "sites")
        self.assertEqual(layers.layer_of("QICLean.ManyBody.Dynamics.Volterra"), "dynamics")
        self.assertEqual(layers.layer_of("QICLean.Circuit.LocalCircuit"), "circuit")
        self.assertEqual(layers.layer_of("QICLean.Circuit.Party.PartyWord"), "party")
        self.assertEqual(layers.layer_of("QICLean.ManyBody.Hamiltonian.Basic"), "hamiltonian")
        self.assertEqual(layers.layer_of("QICLean.ManyBody.Entropy.Cut.RegionSplit"),
                         "manybody_entropy")
        self.assertEqual(layers.layer_of("QICLean.Entropy.Defs"), "entropy")
        self.assertEqual(layers.layer_of("QICLean.Spectral.Gap.GlobalGap"), "spectral")
        self.assertIsNone(layers.layer_of("QICLean.Topology.Defs"))
        self.assertIsNone(layers.layer_of("QICLean"))

    def test_single_system_layers_form_a_chain(self) -> None:
        chain = ["Algebra", "Analysis", "Spectral", "Channel", "Kraus", "Entropy", "Probability",
                 "Representation"]
        for low, high in zip(chain, chain[1:]):
            with self.subTest(low=low, high=high):
                sources = {
                    f"QICLean.{high}.A": f"import QICLean.{low}.B\ndef a := 0\n",
                    f"QICLean.{low}.B": f"import QICLean.{high}.C\ndef b := 0\n",
                    f"QICLean.{high}.C": "def c := 0\n",
                }
                self.assertEqual(layers.violations(sources),
                                 {f"QICLean.{low}.B -> QICLean.{high}.C"})

    def test_many_body_layers_take_single_systems_not_the_reverse(self) -> None:
        allowed = [("ManyBody.Sites", "Entropy"), ("ManyBody.Entropy", "Entropy"),
                   ("ManyBody.Entropy", "ManyBody.Hamiltonian"),
                   ("ManyBody.Subspace", "Probability"), ("ManyBody.Subspace", "ManyBody.Entropy"),
                   ("ManyBody.Replica", "Representation"), ("ManyBody.Replica", "ManyBody.Entropy")]
        forbidden = [("Entropy", "ManyBody.Sites"), ("Representation", "ManyBody.Replica"),
                     ("ManyBody.Sites", "Representation"), ("ManyBody.Sites", "Probability"),
                     ("ManyBody.Hamiltonian", "ManyBody.Entropy"),
                     ("ManyBody.Subspace", "ManyBody.Replica"),
                     ("ManyBody.Replica", "ManyBody.Subspace"), ("Circuit", "Entropy"),
                     ("Circuit.Gate", "Kraus")]
        for source, target, expected in ([(s, t, False) for s, t in allowed] +
                                         [(s, t, True) for s, t in forbidden]):
            with self.subTest(source=source, target=target):
                sources = {f"QICLean.{source}.A": f"import QICLean.{target}.B\ndef a := 0\n"}
                self.assertEqual(bool(layers.violations(sources)), expected)

    def test_simulation_owns_only_its_specific_prefix(self) -> None:
        self.assertEqual(layers.layer_of("QICLean.Circuit.Simulation.TruncatedProductFormula"),
                         "simulation")
        self.assertEqual(layers.layer_of("QICLean.Circuit.Core.Circuit"), "circuit")
        self.assertEqual(layers.layer_of("QICLean.Circuit.SimulationLike"), "circuit")

    def test_simulation_may_consume_circuits_and_many_body_layers(self) -> None:
        imports = ["QICLean.Algebra.Matrix.MatrixAux", "QICLean.Channel.Basic",
                   "QICLean.ManyBody.Sites.Placement", "QICLean.Circuit.Gate.Basic",
                   "QICLean.Circuit.ProductFormula", "QICLean.ManyBody.Dynamics.TruncatedEvolution",
                   "QICLean.ManyBody.Hamiltonian.Basic"]
        sources = {"QICLean.Circuit.Simulation.TruncatedProductFormula":
                   "".join(f"import {module}\n" for module in imports) + "def simulation := 0\n"}
        self.assertEqual(layers.violations(sources), set())

    def test_simulation_is_not_a_reverse_import_route(self) -> None:
        target = "QICLean.Circuit.Simulation.TruncatedProductFormula"
        for importer in ["QICLean.Circuit.Core.Circuit", "QICLean.Circuit.ProductFormula",
                         "QICLean.Circuit.Algorithm.QFT", "QICLean.Circuit.Party.Basic",
                         "QICLean.Circuit.Gate.Basic", "QICLean.ManyBody.Sites.Placement",
                         "QICLean.ManyBody.Dynamics.HeisenbergEvolution",
                         "QICLean.ManyBody.Hamiltonian.Basic"]:
            for via in [target, "QICLean.Circuit.Simulation", "QICLean.Circuit"]:
                with self.subTest(importer=importer, via=via):
                    sources = {
                        target: "def simulation := 0\n",
                        "QICLean.Circuit.Simulation": f"import {target}\n",
                        "QICLean.Circuit": "import QICLean.Circuit.Simulation\n",
                        importer: f"import {via}\ndef consumer := 0\n",
                    }
                    self.assertEqual(layers.violations(sources), {f"{importer} -> {target}"})

    def test_simulation_does_not_widen_other_circuit_layers(self) -> None:
        for importer in ["QICLean.Circuit.Core.Circuit", "QICLean.Circuit.ProductFormula",
                         "QICLean.Circuit.Algorithm.QFT", "QICLean.Circuit.Party.Basic"]:
            for target in ["QICLean.ManyBody.Dynamics.HeisenbergEvolution",
                           "QICLean.ManyBody.Hamiltonian.Basic"]:
                with self.subTest(importer=importer, target=target):
                    sources = {importer: f"import {target}\ndef consumer := 0\n"}
                    self.assertEqual(layers.violations(sources), {f"{importer} -> {target}"})
        importer = "QICLean.Circuit.Simulation.TruncatedProductFormula"
        for target in ["QICLean.Circuit.Algorithm.QFT", "QICLean.Circuit.Party.Basic",
                       "QICLean.Circuit.Model.Protocol", "QICLean.Circuit.Compile.Encoding",
                       "QICLean.Circuit.Protocol.Example", "QICLean.Entropy.Defs"]:
            with self.subTest(target=target):
                self.assertEqual(layers.violations({importer: f"import {target}\ndef sim := 0\n"}),
                                 {f"{importer} -> {target}"})

    def test_model_compile_protocol_own_only_their_specific_prefixes(self) -> None:
        for module, layer in [("QICLean.Circuit.Model.Protocol", "model"),
                              ("QICLean.Circuit.Compile.Encoding", "compile"),
                              ("QICLean.Circuit.Protocol.Example", "protocol"),
                              ("QICLean.Circuit.ModelLike", "circuit"),
                              ("QICLean.Circuit.CompileLike", "circuit"),
                              ("QICLean.Circuit.ProtocolLike", "circuit")]:
            with self.subTest(module=module):
                self.assertEqual(layers.layer_of(module), layer)

    def test_model_compile_protocol_may_consume_lower_layers_in_order(self) -> None:
        lower = ["QICLean.Algebra.Matrix.MatrixAux", "QICLean.Channel.Basic",
                 "QICLean.ManyBody.Sites.Placement", "QICLean.Circuit.Gate.Basic",
                 "QICLean.Circuit.Core.Circuit"]
        for importer, extra in [
                ("QICLean.Circuit.Model.Protocol", []),
                ("QICLean.Circuit.Compile.Encoding", ["QICLean.Circuit.Model.Protocol"]),
                ("QICLean.Circuit.Protocol.Example",
                 ["QICLean.Circuit.Model.Protocol", "QICLean.Circuit.Compile.Encoding"])]:
            with self.subTest(importer=importer):
                sources = {importer: "".join(f"import {module}\n" for module in lower + extra)
                           + "def p := 0\n"}
                self.assertEqual(layers.violations(sources), set())

    def test_model_compile_protocol_are_not_reverse_import_routes(self) -> None:
        lower = ["QICLean.Circuit.Core.Circuit", "QICLean.Circuit.ProductFormula",
                 "QICLean.Circuit.Algorithm.QFT", "QICLean.Circuit.Party.Basic",
                 "QICLean.Circuit.Gate.Basic", "QICLean.ManyBody.Sites.Placement",
                 "QICLean.ManyBody.Dynamics.HeisenbergEvolution",
                 "QICLean.ManyBody.Hamiltonian.Basic",
                 "QICLean.Circuit.Simulation.TruncatedProductFormula"]
        for target, prefix, above in [
                ("QICLean.Circuit.Model.Protocol", "QICLean.Circuit.Model", []),
                ("QICLean.Circuit.Compile.Encoding", "QICLean.Circuit.Compile",
                 ["QICLean.Circuit.Model.Protocol"]),
                ("QICLean.Circuit.Protocol.Example", "QICLean.Circuit.Protocol",
                 ["QICLean.Circuit.Model.Protocol", "QICLean.Circuit.Compile.Encoding"])]:
            for importer in lower + above:
                for via in [target, prefix, "QICLean.Circuit"]:
                    with self.subTest(importer=importer, via=via):
                        sources = {
                            target: "def t := 0\n",
                            prefix: f"import {target}\n",
                            "QICLean.Circuit": f"import {prefix}\n",
                            importer: f"import {via}\ndef consumer := 0\n",
                        }
                        self.assertEqual(layers.violations(sources),
                                         {f"{importer} -> {target}"})

    def test_model_compile_protocol_do_not_reach_sideways(self) -> None:
        for importer in ["QICLean.Circuit.Model.Protocol", "QICLean.Circuit.Compile.Encoding",
                         "QICLean.Circuit.Protocol.Example"]:
            for target in ["QICLean.ManyBody.Dynamics.HeisenbergEvolution",
                           "QICLean.ManyBody.Hamiltonian.Basic", "QICLean.Circuit.Algorithm.QFT",
                           "QICLean.Circuit.Party.Basic",
                           "QICLean.Circuit.Simulation.TruncatedProductFormula",
                           "QICLean.Entropy.Defs"]:
                with self.subTest(importer=importer, target=target):
                    self.assertEqual(
                        layers.violations({importer: f"import {target}\ndef p := 0\n"}),
                        {f"{importer} -> {target}"})

    def test_upward_and_sideways_imports_are_violations(self) -> None:
        sources = {
            "QICLean.Circuit.Gate.A": "import QICLean.ManyBody.Sites.Placement\ntheorem a : True := trivial\n",
            "QICLean.ManyBody.Sites.Placement": "import QICLean.Circuit.Gate.A\ndef e := 0\n",
            "QICLean.Circuit.LocalCircuit": (
                "import QICLean.ManyBody.Sites.Placement\nimport QICLean.ManyBody.Hamiltonian.Basic\n"
                "def c := 0\n"
            ),
            "QICLean.ManyBody.Hamiltonian.Basic": (
                "import QICLean.Representation.Defs\ndef h := 0\n"
            ),
            "QICLean.Representation.Defs": (
                "import QICLean.ManyBody.Hamiltonian.Basic\ndef t := 0\n"
            ),
        }
        self.assertEqual(
            layers.violations(sources),
            {
                "QICLean.Circuit.Gate.A -> QICLean.ManyBody.Sites.Placement",
                "QICLean.ManyBody.Sites.Placement -> QICLean.Circuit.Gate.A",
                "QICLean.Circuit.LocalCircuit -> QICLean.ManyBody.Hamiltonian.Basic",
                "QICLean.ManyBody.Hamiltonian.Basic -> QICLean.Representation.Defs",
                "QICLean.Representation.Defs -> QICLean.ManyBody.Hamiltonian.Basic",
            },
        )

    def test_import_only_aggregators_are_exempt(self) -> None:
        sources = {
            "QICLean.ManyBody.Hamiltonian": "/- generated -/\nimport QICLean.Circuit.Party\n",
            "QICLean.Circuit.Party": "import QICLean.Circuit.Party.PartyWord\n",
        }
        self.assertEqual(layers.violations(sources), set())

    def test_comments_do_not_hide_or_create_imports(self) -> None:
        sources = {
            "QICLean.Circuit.Gate.Hidden": (
                "import QICLean.Entropy.Defs -- tensor definition\ntheorem a : True := trivial\n"
            ),
            "QICLean.Circuit.Gate.Commented": (
                "/- import QICLean.Entropy.Defs\n  /- nested -/ import QICLean.Representation.Defs -/\n"
                "-- import QICLean.Circuit.LocalCircuit\n"
                "theorem b : True := trivial\n"
            ),
        }
        self.assertEqual(
            layers.violations(sources), {"QICLean.Circuit.Gate.Hidden -> QICLean.Entropy.Defs"}
        )

    def test_comments_separate_tokens_and_multiple_imports_are_checked(self):
        sources = {"QICLean.Circuit.Gate.A":
                   "import/- nested /- comment -/ -/QICLean.Algebra.A import QICLean.Entropy.B\ndef a := 0\n"}
        self.assertEqual(layers.violations(sources),
                         {"QICLean.Circuit.Gate.A -> QICLean.Entropy.B"})

    def test_lexical_errors_fail_closed(self):
        for source in ['import QICLean.Entropy.B\n/-', 'def text := "unfinished']:
            with self.subTest(source=source):
                with self.assertRaises(ValueError):
                    layers.parse_module(source)
                with self.assertRaises(ValueError):
                    list(forwarding.pass_throughs_of_source(source))

    def test_header_whitespace_module_and_escaped_names(self):
        source = "module\npublic\n import\nQICLean.«Entropy».B\nimport QICLean.Algebra.A\n"
        self.assertEqual(layers.parse_module(source),
                         (("QICLean.Entropy.B", "QICLean.Algebra.A"), True))
        self.assertEqual(layers.violations({"QICLean.Circuit.Gate.A": source + "def a := 0"}),
                         {"QICLean.Circuit.Gate.A -> QICLean.Entropy.B"})

    def test_literals_cannot_hide_imports_or_manufacture_commands(self):
        for literal in ['"/-"', '"--"', r"'\"'", 'r#"quote \" /-"#']:
            with self.subTest(literal=literal):
                source = 'import QICLean.Entropy.B\ndef text := ' + literal + '\n'
                self.assertEqual(layers.violations({'QICLean.Circuit.Gate.A': source}),
                                 {'QICLean.Circuit.Gate.A -> QICLean.Entropy.B'})
        source = 'def text := "\nimport QICLean.Entropy.B\ntheorem fake (x : T) : P x := Original.fact x\n"\n'
        self.assertEqual(layers.parse_module(source), ((), False))
        self.assertEqual(list(forwarding.pass_throughs_of_source(source)), [])
        self.assertEqual(list(forwarding.pass_throughs_of_source(
            'def text := "/-"\ntheorem real (x : T) : P x := Original.fact x\n')), ['real'])

    def test_identifier_suffix_is_not_a_raw_string_opener(self) -> None:
        for identifier in ["addr", "αr", "x_r", "x'r", "x1r"]:
            with self.subTest(identifier=identifier):
                # The escaped quote belongs to an ordinary string, even with
                # no whitespace after the identifier. A raw-string misparse
                # would expose the fake declaration or swallow the real one.
                source = ('def text := ' + identifier + r'"escaped \"' + '\n'
                          'theorem fake (x : T) : P x := Original.fact x\n"\n'
                          'theorem real (x : T) : P x := Original.fact x\n')
                self.assertEqual(strip_lean_comments(source), (source, None))
                masked, error = strip_lean_comments(source, mask_strings=True)
                self.assertIsNone(error)
                self.assertIn(identifier + '"', masked)
                self.assertNotIn('theorem fake', masked)
                self.assertEqual(list(forwarding.pass_throughs_of_source(source)), ['real'])
                self.assertEqual(layers.parse_module(source), ((), False))

    def test_import_modifiers_are_recognized(self) -> None:
        sources = {
            "QICLean.Circuit.Gate.A": "public import QICLean.Entropy.Defs\ndef a := 0\n",
            "QICLean.Circuit.Gate.B": "public meta import QICLean.Representation.Defs\ndef b := 0\n",
            "QICLean.Circuit.Gate.C": "import all QICLean.Probability.LocalAlgebra\ndef c := 0\n",
        }
        self.assertEqual(
            layers.violations(sources),
            {
                "QICLean.Circuit.Gate.A -> QICLean.Entropy.Defs",
                "QICLean.Circuit.Gate.B -> QICLean.Representation.Defs",
                "QICLean.Circuit.Gate.C -> QICLean.Probability.LocalAlgebra",
            },
        )

    def test_imports_are_followed_through_nested_aggregators(self) -> None:
        sources = {
            "QICLean.Circuit.Outer": "import QICLean.Circuit.Inner\n",
            "QICLean.Circuit.Inner": "-- wrapper\nimport QICLean.Entropy.Defs\nimport QICLean.Circuit.Geometry\n",
            "QICLean.Circuit.Geometry": "def g := 0\n",
            "QICLean.Circuit.LocalCircuit": "import QICLean.Circuit.Outer\ndef c := 0\n",
            "QICLean.Entropy.Defs": "def t := 0\n",
        }
        self.assertEqual(
            layers.violations(sources), {"QICLean.Circuit.LocalCircuit -> QICLean.Entropy.Defs"}
        )

    def test_party_layer_may_import_circuits_but_not_hamiltonians(self) -> None:
        sources = {
            "QICLean.Circuit.Party.Example": (
                "import QICLean.Circuit.LocalCircuit\nimport QICLean.ManyBody.Hamiltonian.Basic\n"
                "def p := 0\n"
            ),
        }
        self.assertEqual(
            layers.violations(sources),
            {"QICLean.Circuit.Party.Example -> QICLean.ManyBody.Hamiltonian.Basic"},
        )

    def test_debt_may_only_shrink_against_the_base(self) -> None:
        entry = "QICLean.Circuit.Gate.A -> QICLean.Entropy.Defs"
        sources = {"QICLean.Circuit.Gate.A": "import QICLean.Entropy.Defs\ndef a := 0\n"}
        # Recording a new violation in the same change does not admit it.
        errors = layers.check_layers(sources, frozenset({entry}), frozenset())
        self.assertEqual(errors, [f"Entry added to DEBT; this set may only shrink: {entry}"])
        # The same entry is accepted when it is already recorded at the base.
        self.assertEqual(layers.check_layers(sources, frozenset({entry}), frozenset({entry})), [])
        # Without a base (the checker is being introduced) the recorded set is the baseline.
        self.assertEqual(layers.check_layers(sources, frozenset({entry}), None), [])
        # An unrecorded violation and a stale entry both fail.
        self.assertEqual(len(layers.check_layers(sources, frozenset(), frozenset())), 1)
        self.assertEqual(len(layers.check_layers({}, frozenset({entry}), frozenset({entry}))), 1)

    def test_debt_is_read_from_a_checker_revision(self) -> None:
        source = 'DEBT: frozenset[str] = frozenset(\n    {\n        "A -> B",\n    }\n)\n'
        self.assertEqual(layers.debt_from_source(source), frozenset({"A -> B"}))
        self.assertEqual(layers.debt_from_source("DEBT = frozenset({})\n"), frozenset())
        with self.assertRaises(ValueError):
            layers.debt_from_source("DEBT = compute()\n")

    def test_record_is_read_by_name_and_may_be_absent(self) -> None:
        source = 'DEBT = frozenset({})\nMUTUAL_DIRECTORIES = frozenset({"A <-> B"})\n'
        self.assertEqual(
            layers.record_from_source(source, "MUTUAL_DIRECTORIES"), frozenset({"A <-> B"})
        )
        self.assertIsNone(layers.record_from_source(source, "EXAMPLES_IMPORTS"))
        with self.assertRaises(ValueError):
            layers.record_from_source("EXAMPLES_IMPORTS = compute()\n", "EXAMPLES_IMPORTS")

    def test_recorded_debt_matches_the_tree(self) -> None:
        root = Path(__file__).resolve().parent.parent
        self.assertEqual(layers.check_layers(layers.tracked_sources(root)), [])


class PassThroughPolicyTests(unittest.TestCase):
    def found(self, source: str) -> list[str]:
        return list(forwarding.pass_throughs_of_source(source))

    def test_the_four_typical_shapes_are_found(self) -> None:
        source = (
            "namespace MPSTensor\n\n"
            "/-- The blocked dimension. -/\n"
            "noncomputable abbrev blockPhysDim (d L : ℕ) : ℕ := Kraus.blockPhysDim d L\n\n"
            "@[simp] lemma blockPhysDim_eq_pow (d L : ℕ) : blockPhysDim d L = d ^ L :=\n"
            "  Kraus.blockPhysDim_eq_pow d L\n\n"
            "lemma length_wordOfBlock (d L : ℕ) (i : Fin (blockPhysDim d L)) :\n"
            "    (wordOfBlock d L i).length = L := by\n"
            "  exact Kraus.length_wordOfBlock d L i -- forwarded\n\n"
            "protected theorem evalWord_nil {D : ℕ} [NeZero D] (A : MPSTensor d D) :\n"
            "    evalWord A [] = 1 := by simpa using Kraus.evalWord_nil A\n\n"
            "end MPSTensor\n"
        )
        self.assertEqual(
            self.found(source),
            [
                "MPSTensor.blockPhysDim",
                "MPSTensor.blockPhysDim_eq_pow",
                "MPSTensor.length_wordOfBlock",
                "MPSTensor.evalWord_nil",
            ],
        )

    def test_names_follow_namespaces_and_not_sections(self) -> None:
        source = (
            "namespace A.B\nnoncomputable section\nvariable {n : ℕ}\n"
            "theorem f (x : ℕ) : P x := Kraus.f x\n"
            "end\nend A.B\n"
            "namespace C\nsection Named\n"
            "theorem D.g (x : ℕ) : P x := Kraus.D.g x\n"
            "theorem _root_.Other.h (x : ℕ) : P x := Kraus.h x\n"
            "end Named\nend C\n"
            "theorem k (x : ℕ) : P x := Kraus.k x\n"
        )
        self.assertEqual(self.found(source), ["A.B.f", "C.D.g", "Other.h", "k"])

    def test_arguments_must_be_the_explicit_binders_in_order(self) -> None:
        for declaration in (
            "theorem f (a b : ℕ) : P a b := Kraus.f b a",
            "theorem f (a b : ℕ) : P a b := Kraus.f a",
            "theorem f (a b : ℕ) : P a b := Kraus.f a b a",
            "theorem f (a b : ℕ) : P a b := Kraus.f a (b + 0)",
            "theorem f (a b : ℕ) : P a b := Kraus.f (d := d) a b",
            "theorem f (a b : ℕ) : P a b := @Kraus.f a b",
            "theorem f (a b : ℕ) : P a b := (Kraus.f a b).symm",
            "theorem f (a b : ℕ) : P a b := by rw [Kraus.f a b]",
            "theorem f (a b : ℕ) : P a b := by\n  simp\n  exact Kraus.f a b",
            "theorem f (a b : ℕ) : P a b := by simpa [g] using Kraus.f a b",
            "theorem f {a b : ℕ} : P a b := Kraus.f a b",
            "theorem f : P := Kraus.f",
            "theorem f (a : ℕ) (b : ℕ := 0) : P a b := Kraus.f a b",
            "theorem f a b : P a b := Kraus.f a b",
        ):
            with self.subTest(declaration=declaration):
                self.assertEqual(self.found(declaration + "\n"), [])
        # An anonymous instance binder binds no name, so its class may be the namespace.
        self.assertEqual(
            self.found("theorem foo (d : ℕ) [NeZero d] : P d := NeZero.foo d\n"), ["foo"]
        )
        self.assertEqual(
            self.found("theorem foo (d : ℕ) [NeZero : C d] : P d := NeZero.foo d\n"), []
        )
        # The same holds for an anonymous instance bound by a ``variable`` command.
        self.assertEqual(
            self.found(
                "variable {β : Type*} [Fintype β]\n"
                "noncomputable def card (α : Type*) [Fintype α] : ℕ := Fintype.card α\n"
            ),
            ["card"],
        )
        # Implicit and instance binders are not arguments; explicit ones may be split.
        self.assertEqual(
            self.found(
                "theorem f {d : ℕ} [NeZero d] (a : Fin d)\n"
                "    ⦃c : ℕ⦄ (b : Fin d) : P a b := Kraus.f a b\n"
            ),
            ["f"],
        )

    def test_renamed_and_unqualified_forwarding_are_found(self):
        self.assertEqual(self.found("theorem renamed (x : T) : P x := Original.fact x\n"), ["renamed"])
        self.assertEqual(self.found("theorem renamed (x : T) : P x := fact x\n"), ["renamed"])

    def test_bound_targets_and_recursive_calls_are_excluded(self):
        for body in ("hA.fact x", "H.fact x", "f x", "x x"):
            with self.subTest(body=body):
                self.assertEqual(self.found(
                    "variable (hA : A) {H : B}\ntheorem f (x : T) : P x := " + body + "\n"), [])

    def test_other_commands_are_never_reported(self) -> None:
        source = (
            "instance blockFintype (d : ℕ) : Fintype (Block d) := Kraus.blockFintype d\n"
            "example (d : ℕ) : P d := Kraus.f d\n"
            "structure S where\n  f (d : ℕ) : ℕ := Kraus.f d\n"
            "def g (d : ℕ) : ℕ := Kraus.g d\nwhere\n  aux (d : ℕ) : ℕ := Kraus.aux d\n"
            "def r (d : ℕ) : ℕ := Kraus.r d\ntermination_by d\n"
            "/- theorem f (d : ℕ) : P d := Kraus.f d -/\n"
            "-- theorem f (d : ℕ) : P d := Kraus.f d\n"
            "def m : ℕ → ℕ\n  | d => Kraus.m d\n"
        )
        self.assertEqual(self.found(source), [])

    def test_duplicate_private_names_cannot_share_one_debt_entry(self):
        source = "private theorem f (x : T) : P x := Original.fact x\n"
        sources = {"QICLean.Analysis.A": source, "QICLean.Circuit.Gate.B": source}
        current = forwarding.pass_throughs(sources)
        self.assertEqual(len(current), 2)
        self.assertTrue(forwarding.check_pass_throughs(sources, frozenset({"f"}), frozenset({"f"})))
        self.assertEqual(len(forwarding.pass_throughs({"QICLean.Analysis.A": source + source})), 2)

    def test_archive_is_out_of_scope(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            for relative in ("QICLean/Archive/Old.lean", "QICLean/MPS/New.lean"):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("theorem f (d : ℕ) : P d := Kraus.f d\n", encoding="utf-8")
                subprocess.run(["git", "-C", str(root), "add", relative], check=True)
            sources = layers.tracked_sources(root)
        self.assertEqual(forwarding.pass_throughs(sources), {"f": "QICLean.MPS.New"})

    def test_recorded_pass_throughs_may_only_shrink_against_the_base(self) -> None:
        sources = {"QICLean.MPS.Core.Blocking": "theorem f (d : ℕ) : P d := Kraus.f d\n"}
        check = forwarding.check_pass_throughs
        self.assertEqual(
            check(sources, frozenset(), frozenset()),
            [
                "Declaration only applies another declaration to its own arguments: "
                "f (QICLean.MPS.Core.Blocking)"
            ],
        )
        self.assertEqual(
            check(sources, frozenset({"f"}), frozenset()),
            ["Entry added to PASS_THROUGH; this set may only shrink: f"],
        )
        self.assertEqual(check(sources, frozenset({"f"}), frozenset({"f"})), [])
        self.assertEqual(check(sources, frozenset({"f"}), None), [])
        self.assertEqual(len(check({}, frozenset({"f"}), frozenset({"f"}))), 1)

    def test_recorded_pass_throughs_match_the_tree(self) -> None:
        root = Path(__file__).resolve().parent.parent
        sources = layers.tracked_sources(root)
        self.assertEqual(set(forwarding.pass_throughs(sources)), forwarding.PASS_THROUGH)

class SublayerOrderTests(unittest.TestCase):
    TABLE = {
        "QICLean.Analysis": {"(top)": [], "Real": ["(top)"], "Norm": ["Real"], "Order": ["Real"],
                             "TraceNorm": ["Norm", "Order"]},
        "QICLean.Circuit": {"(top)": ["Core"], "Core": ["Geometry"], "Geometry": []},
    }

    def tables(self):
        return layers.close_sublayers(self.TABLE)

    def test_order_is_closed_transitively(self) -> None:
        closed = self.tables()["QICLean.Analysis"]
        self.assertEqual(closed["TraceNorm"], frozenset({"Norm", "Order", "Real", "(top)"}))
        self.assertEqual(closed["(top)"], frozenset())

    def test_cyclic_or_dangling_order_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "cycle"):
            layers.close_sublayers({"QICLean.Analysis": {"Norm": ["Order"], "Order": ["Norm"]}})
        with self.assertRaisesRegex(ValueError, "unlisted"):
            layers.close_sublayers({"QICLean.Analysis": {"Norm": ["Real"]}})

    def test_subdirectory_of_a_module(self) -> None:
        prefixes = ["QICLean.Circuit", "QICLean.Circuit.Gate", "QICLean.Analysis"]
        self.assertEqual(layers.sublayer_of("QICLean.Analysis.Norm.OpNorm", prefixes),
                         ("QICLean.Analysis", "Norm"))
        self.assertEqual(layers.sublayer_of("QICLean.Analysis.Norm.Schatten.P", prefixes),
                         ("QICLean.Analysis", "Norm"))
        self.assertEqual(layers.sublayer_of("QICLean.Analysis.Defs", prefixes),
                         ("QICLean.Analysis", "(top)"))
        self.assertEqual(layers.sublayer_of("QICLean.Circuit.Gate.Basic", prefixes),
                         ("QICLean.Circuit.Gate", "(top)"))
        self.assertIsNone(layers.sublayer_of("QICLean.Entropy.Defs", prefixes))

    def test_downward_and_transitive_imports_pass(self) -> None:
        sources = {
            "QICLean.Analysis.TraceNorm.A": "import QICLean.Analysis.Real.B\ndef a := 0\n",
            "QICLean.Analysis.Norm.C": "import QICLean.Analysis.Defs\ndef c := 0\n",
            "QICLean.Analysis.Real.B": "def b := 0\n",
            "QICLean.Analysis.Defs": "def d := 0\n",
        }
        self.assertEqual(layers.sublayer_violations(sources, self.tables()), set())

    def test_upward_sideways_and_unlisted_imports_are_violations(self) -> None:
        sources = {
            "QICLean.Analysis.Real.B": "import QICLean.Analysis.Norm.C\ndef b := 0\n",
            "QICLean.Analysis.Norm.C": "import QICLean.Analysis.Order.D\ndef c := 0\n",
            "QICLean.Analysis.Order.D": "import QICLean.Analysis.Parameter.E\ndef d := 0\n",
            "QICLean.Analysis.Defs": "import QICLean.Analysis.Real.B\ndef t := 0\n",
            "QICLean.Analysis.Parameter.E": "def e := 0\n",
        }
        self.assertEqual(layers.sublayer_violations(sources, self.tables()), {
            "QICLean.Analysis.Real.B -> QICLean.Analysis.Norm.C",
            "QICLean.Analysis.Norm.C -> QICLean.Analysis.Order.D",
            "QICLean.Analysis.Order.D -> QICLean.Analysis.Parameter.E",
            "QICLean.Analysis.Defs -> QICLean.Analysis.Real.B",
        })

    def test_imports_across_layers_and_within_a_subdirectory_are_not_checked(self) -> None:
        sources = {
            "QICLean.Circuit.Core.A": "import QICLean.Circuit.Geometry.B\ndef a := 0\n",
            "QICLean.Circuit.Geometry.B": "import QICLean.Analysis.Norm.C\ndef b := 0\n",
            "QICLean.Analysis.Norm.C": "import QICLean.Analysis.Norm.D\ndef c := 0\n",
            "QICLean.Analysis.Norm.D": "def d := 0\n",
        }
        self.assertEqual(layers.sublayer_violations(sources, self.tables()), set())

    def test_aggregators_do_not_hide_imports(self) -> None:
        sources = {
            "QICLean.Analysis.Norm": "import QICLean.Analysis.Norm.C\n",
            "QICLean.Analysis.Norm.C": "def c := 0\n",
            "QICLean.Analysis.Real.B": "import QICLean.Analysis.Norm\ndef b := 0\n",
        }
        self.assertEqual(layers.sublayer_violations(sources, self.tables()),
                         {"QICLean.Analysis.Real.B -> QICLean.Analysis.Norm.C"})

    def test_sublayer_debt_may_only_shrink_against_the_base(self) -> None:
        entry = "QICLean.Analysis.Real.B -> QICLean.Analysis.Norm.C"
        sources = {"QICLean.Analysis.Real.B": "import QICLean.Analysis.Norm.C\ndef b := 0\n",
                   "QICLean.Analysis.Norm.C": "def c := 0\n"}
        tables = self.tables()
        self.assertEqual(layers.check_sublayers(sources, tables, frozenset({entry}), frozenset()),
                         [f"Entry added to SUBLAYER_DEBT; this set may only shrink: {entry}"])
        self.assertEqual(
            layers.check_sublayers(sources, tables, frozenset({entry}), frozenset({entry})), [])
        self.assertEqual(len(layers.check_sublayers(sources, tables, frozenset(), None)), 1)
        self.assertEqual(len(layers.check_sublayers({}, tables, frozenset({entry}), None)), 1)

    def test_orders_inside_a_subdirectory_add_to_the_order_of_the_layer(self) -> None:
        inner = layers.close_sublayers(
            {"QICLean.Analysis.Norm": {"Low": [], "High": ["Low"]}})
        sources = {
            "QICLean.Analysis.Norm.Low.A": "import QICLean.Analysis.Norm.High.B\ndef a := 0\n",
            "QICLean.Analysis.Norm.High.B": "import QICLean.Analysis.Norm.Low.C\ndef b := 0\n",
            "QICLean.Analysis.Norm.Low.C": "import QICLean.Analysis.TraceNorm.D\ndef c := 0\n",
            "QICLean.Analysis.TraceNorm.D": "def d := 0\n",
        }
        across = "QICLean.Analysis.Norm.Low.C -> QICLean.Analysis.TraceNorm.D"
        self.assertEqual(layers.sublayer_violations(sources, self.tables(), inner), {
            "QICLean.Analysis.Norm.Low.A -> QICLean.Analysis.Norm.High.B", across})
        self.assertEqual(layers.sublayer_violations(sources, self.tables()), {across})

    def test_moved_modules_keep_their_recorded_entries(self) -> None:
        renames = {"QICLean.Analysis.Real.B": "QICLean.Analysis.Real.Sub.B"}
        self.assertEqual(
            layers.rename_entry("QICLean.Analysis.Real.B -> QICLean.Analysis.Norm.C", renames),
            "QICLean.Analysis.Real.Sub.B -> QICLean.Analysis.Norm.C")
        self.assertEqual(layers.rename_entry("QICLean.Analysis <-> QICLean.Channel", renames),
                         "QICLean.Analysis <-> QICLean.Channel")
        renamed = layers.module_renames()
        self.assertTrue(renamed)
        self.assertFalse(set(renamed.values()) & set(renamed))

    def test_repository_inner_orders_refine_a_listed_subdirectory(self) -> None:
        tables = layers.load_sublayers()
        for prefix in layers.load_inner_orders():
            with self.subTest(prefix=prefix):
                owner = layers.sublayer_of(prefix + ".M", tables)
                self.assertIsNotNone(owner)
                self.assertIn(owner[1], tables[owner[0]])
                self.assertEqual(prefix, f"{owner[0]}.{owner[1]}")

    def test_repository_table_is_an_order_of_existing_layers(self) -> None:
        tables = layers.load_sublayers()
        owned = {prefix for _, prefixes in layers.LAYERS for prefix in prefixes}
        for prefix in tables:
            with self.subTest(prefix=prefix):
                self.assertIn(prefix, owned)

    def test_recorded_sublayer_debt_matches_the_tree(self) -> None:
        root = Path(__file__).resolve().parent.parent
        self.assertEqual(
            layers.sublayer_violations(layers.tracked_sources(root), layers.load_sublayers(),
                                       layers.load_inner_orders()),
            layers.SUBLAYER_DEBT)


class RepositoryRatchetTests(unittest.TestCase):
    def test_tree_baselines_and_new_layers_start_clean(self):
        sources = layers.tracked_sources(Path(__file__).resolve().parent.parent)
        self.assertEqual(set(layers.mutual_directories(sources)), layers.MUTUAL_DIRECTORIES)
        self.assertEqual(layers.examples_imports(sources), layers.EXAMPLES_IMPORTS)
        self.assertFalse(layers.DEBT)
        self.assertFalse([name for name, module in forwarding.pass_throughs(sources).items()
                          if layers.layer_of(module) in layers.NEW_LAYERS])

    def test_directory_depth_and_new_mutual_pair(self):
        self.assertEqual(layers.directory_of('QICLean.ManyBody.Sites.Config'), 'ManyBody/Sites')
        self.assertEqual(layers.directory_of('QICLean.Circuit.Gate.Basic'), 'Circuit/Gate')
        sources = {
            'QICLean.Analysis.A': 'import QICLean.Entropy.B\ndef a := 0\n',
            'QICLean.Entropy.B': 'import QICLean.Analysis.A\ndef b := 0\n',
        }
        pair = 'Analysis <-> Entropy'
        self.assertEqual(set(layers.mutual_directories(sources)), {pair})
        self.assertTrue(layers.check_mutual_directories(sources, frozenset(), frozenset()))
        self.assertTrue(layers.check_mutual_directories(sources, frozenset({pair}), frozenset()))
        self.assertTrue(layers.check_mutual_directories({}, frozenset({pair})))

    def test_root_aggregator_cannot_hide_upward_import(self):
        sources = {
            'QICLean': 'import QICLean.Entropy.B\n',
            'QICLean.Circuit.Gate.A': 'import QICLean\ndef a := 0\n',
            'QICLean.Entropy.B': 'def b := 0\n',
        }
        self.assertEqual(layers.violations(sources), {'QICLean.Circuit.Gate.A -> QICLean.Entropy.B'})

    def test_every_new_layer_rejects_forbidden_sibling(self):
        for source, target in [('ManyBody.Sites', 'Circuit.Gate'),
                               ('Circuit.Gate', 'Channel'),
                               ('ManyBody.Dynamics', 'ManyBody.Hamiltonian'),
                               ('ManyBody.Hamiltonian', 'Circuit'),
                               ('Circuit', 'ManyBody.Dynamics'),
                               ('Circuit.Party', 'ManyBody.Hamiltonian'),
                               ('Circuit.Model', 'Circuit.Compile'),
                               ('Circuit.Compile', 'Circuit.Protocol'),
                               ('Circuit.Protocol', 'Circuit.Simulation')]:
            with self.subTest(source=source, target=target):
                self.assertTrue(layers.violations({f'QICLean.{source}.A':
                                                  f'import QICLean.{target}.B\ndef a := 0\n'}))

    def test_git_merge_base_bootstrap_and_no_growth(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(['git', '-C', directory, *args], text=True).strip()
            def commit():
                git('add', '.')
                git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
                    'commit', '-qm', 'fixture')
            git('init', '-q')
            (root / 'initial').write_text('base')
            commit()
            bootstrap = git('rev-parse', 'HEAD')
            checker = root / 'scripts/check.py'
            checker.parent.mkdir()
            checker.write_text('DEBT = frozenset({"old"})\n')
            commit()
            base = git('rev-parse', 'HEAD')
            checker.write_text('DEBT = frozenset({"old", "new"})\n')
            commit()
            self.assertEqual(layers.records_at_merge_base(root, bootstrap, 'scripts/check.py', ['DEBT']), {'DEBT': None})
            record = layers.records_at_merge_base(root, base, 'scripts/check.py', ['DEBT'])['DEBT']
            self.assertEqual(record, frozenset({'old'}))
            errors = layers.ratchet_errors(frozenset({'old', 'new'}), frozenset({'old', 'new'}),
                                           record, new='new', stale='stale', added='added')
            self.assertEqual(errors, ['added: new'])
            # Debt retired on the old tip must not reappear after a force-push
            # that diverges before that retirement. A merge base would allow it.
            git('checkout', '-q', base)
            checker.write_text('DEBT = frozenset({})\n')
            commit()
            old_tip = git('rev-parse', 'HEAD')
            git('checkout', '-q', base)
            (root / 'other').write_text('divergent branch')
            commit()
            self.assertEqual(layers.records_at_merge_base(root, old_tip, 'scripts/check.py', ['DEBT'])['DEBT'],
                             frozenset({'old'}))
            exact = layers.records_at_revision(root, old_tip, 'scripts/check.py', ['DEBT'])['DEBT']
            self.assertEqual(exact, frozenset())
            self.assertEqual(layers.ratchet_errors(frozenset({'old'}), frozenset({'old'}), exact,
                                                  new='new', stale='stale', added='added'), ['added: old'])
            with self.assertRaises(ValueError):
                layers.records_at_revision(root, 'missing-ref', 'scripts/check.py', ['DEBT'])
            with self.assertRaises(ValueError):
                layers.records_at_merge_base(root, 'missing-ref', 'scripts/check.py', ['DEBT'])

if __name__ == '__main__':
    unittest.main()
