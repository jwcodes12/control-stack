"""Static consistency test for SC-03. No scenario runtime or experiment is started."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "tools"))
from check_scenario import validate_case


class PinnedCase(unittest.TestCase):
    def test_sources_and_axes(self):
        manifest = validate_case(ROOT / "scenarios" / "SC-03")
        self.assertEqual(manifest["id"], "SC-03")
        self.assertNotEqual(manifest["declared_status"], "DEPLOYMENT_ASSURED")
        self.assertEqual(len(manifest["axes"]), 6)


if __name__ == "__main__":
    unittest.main()
