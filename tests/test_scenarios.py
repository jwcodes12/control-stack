import json
import unittest
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import check_scenario as c

class SchemaTests(unittest.TestCase):
    def setUp(self):
        self.folder = ROOT / "scenarios" / "SC-01"
        self.original = (self.folder / "scenario.json").read_text()
    def mutation(self, fn):
        file = self.folder / "scenario.json"
        try:
            obj = json.loads(self.original)
            fn(obj)
            file.write_text(json.dumps(obj))
            with self.assertRaises(c.Invalid):
                c.load_scenario(self.folder)
        finally:
            file.write_text(self.original)
    def test_all_28(self):
        folders = sorted((ROOT / "scenarios").glob("SC-*"))
        self.assertEqual(len(folders), 28)
        for folder in folders:
            with self.subTest(scenario=folder.name):
                self.assertEqual(c.load_scenario(folder)["id"], folder.name)
    def test_missing_axis(self):
        self.mutation(lambda d: d["axes"].pop("applicability"))
    def test_false_promotion(self):
        self.mutation(lambda d: d["axes"]["proof"].update(status="verified"))
    def test_arbitrary_runner(self):
        self.mutation(lambda d: d["evidence"].update(runner="bash -c foo"))
    def test_traversal(self):
        self.mutation(lambda d: d["formal"].update(source="../escape"))
    def test_bad_adversary(self):
        self.mutation(lambda d: d["formal"].update(adversary_class="anything"))
    def test_duplicate_json(self):
        with self.assertRaises(c.Invalid):
            c.pairs_to_object([("a", 1), ("a", 2)])
    def test_not_assured(self):
        self.assertEqual(c.inspect(self.folder, False)["verdict"], "NOT_ASSURED")

if __name__ == "__main__":
    unittest.main()
