import json
import tempfile
import unittest
from pathlib import Path

from check_inventory import ALLOW, extract_json, source_modules, validate


class InventoryGateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "CFG").mkdir()
        (self.root / "CFG.lean").write_text("import CFG.A\n")
        (self.root / "CFG" / "A.lean").write_text("theorem a : True := by trivial\n")
        self.modules = source_modules(self.root)

    def tearDown(self):
        self.tmp.cleanup()

    def report(self):
        return {
            "status": "ENVIRONMENT_INVENTORY", "selection": "source module CFG and CFG.*",
            "source_modules": sorted(self.modules), "declaration_count": 1,
            "type_rendering": "pretty",
            "declarations": [{
                "name": "OutsideNamespace", "type": "True", "source_module": "CFG.A",
                "kind": "theorem", "is_theorem": True, "is_axiom": False,
                "is_private_or_generated": False, "recursive_axioms": sorted(ALLOW),
                "unresolved_direct_dependencies": [],
            }],
        }

    def test_valid_and_stats(self):
        result = validate(self.report(), self.modules)
        self.assertEqual(result["status"], "PASS_INVENTORY")
        self.assertEqual(result["non_cfg_namespace_count"], 1)

    def test_rejects_truncated_or_empty_log(self):
        with self.assertRaises(ValueError):
            extract_json("info: {\"status\":")
        with self.assertRaises(ValueError):
            validate({"status": "ENVIRONMENT_INVENTORY", "declarations": []}, self.modules)
        with self.assertRaises(ValueError):
            extract_json('{"status": "ok"} error: failed')
        with self.assertRaises(ValueError):
            extract_json('{"status": "ok"}\nseparator\n{"status": "again"}')

    def test_rejects_module_mismatch(self):
        report = self.report()
        report["source_modules"] = ["CFG"]
        with self.assertRaises(ValueError):
            validate(report, self.modules)

    def test_rejects_duplicate_name_unresolved_and_bad_axiom(self):
        report = self.report()
        entry = report["declarations"][0]
        entry["recursive_axioms"] = ["sorryAx"]
        with self.assertRaises(ValueError):
            validate(report, self.modules)
        report = self.report()
        report["declarations"][0]["extra"] = True
        del report["declarations"][0]["type"]
        with self.assertRaises(ValueError):
            validate(report, self.modules)
        entry["recursive_axioms"] = sorted(ALLOW)
        entry["unresolved_direct_dependencies"] = ["Missing"]
        with self.assertRaises(ValueError):
            validate(report, self.modules)

    def test_rejects_schema_types(self):
        report = self.report()
        report["declarations"][0]["is_theorem"] = "true"
        with self.assertRaises(ValueError):
            validate(report, self.modules)
        report = self.report()
        report["declarations"][0]["kind"] = False
        with self.assertRaises(ValueError):
            validate(report, self.modules)


if __name__ == "__main__":
    unittest.main(verbosity=2)
