"""Source-bundle reproducibility and explicit no-frozen-evidence safety gates."""
import io
import json
import tarfile
import tempfile
import unittest
from pathlib import Path
from tools import package_vm_replay as package


class TestVMSourcePackage(unittest.TestCase):
    def test_deterministic_bytes_and_pinned_manifest(self):
        a, b = package.build_bytes(), package.build_bytes()
        self.assertEqual(a, b)
        with tempfile.TemporaryDirectory() as td:
            out = Path(td) / "source.tar.gz"
            out.write_bytes(a)
            self.assertEqual(len(package.verify(out)), 64)
            out.write_bytes(a[:-3] + b"BAD")
            with self.assertRaises(ValueError):
                package.verify(out)

    def test_no_prereg_evidence_or_runtime_secrets(self):
        for path in package.SOURCES:
            self.assertNotIn("/evidence/", path)
            self.assertNotIn("/receipts/", path)
            self.assertNotIn("prereg/", path)
        with tarfile.open(fileobj=io.BytesIO(package.build_bytes()), mode="r:gz") as tar:
            self.assertTrue(all(x.name.startswith("sc01-vm-source-v1/") for x in tar))
            self.assertTrue(all(x.uid == 0 and x.gid == 0 and x.mtime == 0 for x in tar))
        self.assertIn("source only", package.manifest()["limitations"])


if __name__ == "__main__":
    unittest.main()
