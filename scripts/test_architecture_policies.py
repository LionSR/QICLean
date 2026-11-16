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


class ImportLayerPolicyTests(unittest.TestCase):
    def test_layers_are_assigned_from_the_bottom_up(self) -> None:
        self.assertEqual(layers.layer_of("QICLean.Circuit.Gate.FinKronecker"), "gate")
        self.assertEqual(layers.layer_of("QICLean.ManyBody.Sites.Placement"), "sites")
        self.assertEqual(layers.layer_of("QICLean.ManyBody.Sites.PlacementNorm"), "sites")
        self.assertEqual(layers.layer_of("QICLean.ManyBody.Dynamics.Volterra"), "dynamics")
        self.assertEqual(layers.layer_of("QICLean.Circuit.LocalCircuit"), "circuit")
        self.assertEqual(layers.layer_of("QICLean.Circuit.Party.PartyWord"), "party")
        self.assertEqual(layers.layer_of("QICLean.ManyBody.Hamiltonian.Basic"), "hamiltonian")
        self.assertIsNone(layers.layer_of("QICLean.Entropy.Defs"))

    def test_upward_and_sideways_imports_are_violations(self) -> None:
        sources = {
            "QICLean.Circuit.Gate.A": "import QICLean.ManyBody.Sites.Placement\ntheorem a : True := trivial\n",
            "QICLean.ManyBody.Sites.Placement": "import QICLean.Circuit.Gate.A\ndef e := 0\n",
            "QICLean.Circuit.LocalCircuit": (
                "import QICLean.ManyBody.Sites.Placement\nimport QICLean.ManyBody.Hamiltonian.Basic\n"
                "def c := 0\n"
            ),
            "QICLean.ManyBody.Hamiltonian.Basic": "import QICLean.Entropy.Defs\ndef h := 0\n",
            "QICLean.Entropy.Defs": "import QICLean.ManyBody.Hamiltonian.Basic\ndef t := 0\n",
        }
        self.assertEqual(
            layers.violations(sources),
            {
                "QICLean.Circuit.Gate.A -> QICLean.ManyBody.Sites.Placement",
                "QICLean.ManyBody.Sites.Placement -> QICLean.Circuit.Gate.A",
                "QICLean.Circuit.LocalCircuit -> QICLean.ManyBody.Hamiltonian.Basic",
                "QICLean.ManyBody.Hamiltonian.Basic -> QICLean.Entropy.Defs",
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
                   "import/- nested /- comment -/ -/QICLean.Algebra.A QICLean.Entropy.B\ndef a := 0\n"}
        self.assertEqual(layers.violations(sources),
                         {"QICLean.Circuit.Gate.A -> QICLean.Entropy.B"})

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
                               ('Circuit.Party', 'ManyBody.Hamiltonian')]:
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
            with self.assertRaises(ValueError):
                layers.records_at_merge_base(root, 'missing-ref', 'scripts/check.py', ['DEBT'])

if __name__ == '__main__':
    unittest.main()
