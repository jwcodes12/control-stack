#!/usr/bin/env python3
"""Conservative AST regression guard for SC-01 VM receiver input fields.

Checks the explicit sender-to-receiver callsite and known receiver payload
shapes. This is a *change detector* and is not full data-flow analysis:
timing, side channels, hostile host and dynamic Python behaviors remain open.
"""
import ast
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GUEST = ROOT / "gateway/vm/guest.py"


def receiver_shapes(source):
    root = ast.parse(source)
    episode = next((n for n in root.body if isinstance(n, ast.FunctionDef) and n.name == "episode"), None)
    if episode is None:
        raise ValueError("trusted VM episode function missing")
    shapes = []
    for node in ast.walk(episode):
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "receiver_input" for t in node.targets):
            if not isinstance(node.value, ast.Dict):
                raise ValueError("receiver_input no longer explicit literal dictionary")
            if not all(isinstance(k, ast.Constant) and isinstance(k.value, str) for k in node.value.keys):
                raise ValueError("dynamic receiver payload fields require new review")
            shapes.append(tuple(sorted(k.value for k in node.value.keys)))
    send_calls = [
        n for n in ast.walk(episode) if isinstance(n, ast.Call)
        and isinstance(n.func, ast.Name) and n.func.id == "receiver_call"
    ]
    if len(send_calls) != 1 or len(send_calls[0].args) != 1 or not isinstance(send_calls[0].args[0], ast.Name) or send_calls[0].args[0].id != "receiver_input":
        raise ValueError("receiver_call argument/call count changed")
    if sorted(shapes) != [("catalog", "diagnostic", "mode"), ("mode", "view")]:
        raise ValueError(f"unreviewed receiver payload: {shapes}")
    receiver = next((n for n in root.body if isinstance(n, ast.FunctionDef) and n.name == "receiver"), None)
    if receiver is None:
        raise ValueError("receiver service missing")
    repairs = [
        n for n in ast.walk(receiver) if isinstance(n, ast.Call)
        and isinstance(n.func, ast.Name) and n.func.id == "agent"
    ]
    if len(repairs) != 1 or not repairs[0].args or not isinstance(repairs[0].args[0], ast.Constant) or repairs[0].args[0].value != "repair.py":
        raise ValueError("receiver's sandboxed agent executable changed")
    return shapes


class ReceiverBoundaryTests(unittest.TestCase):
    def test_vm_receiver_has_only_reviewed_field_shapes(self):
        self.assertEqual(sorted(receiver_shapes(GUEST.read_text())),
                         [("catalog", "diagnostic", "mode"), ("mode", "view")])

    def test_added_secret_field_is_rejected(self):
        source = GUEST.read_text()
        mutated = source.replace('"mode": mode, "view": view}',
                                 '"mode": mode, "view": view, "secret": item["secret"]}')
        self.assertNotEqual(source, mutated)
        with self.assertRaises(ValueError):
            receiver_shapes(mutated)

    def test_dynamic_receiver_payload_is_rejected(self):
        source = GUEST.read_text()
        mutated = source.replace('"mode": mode, "view": view}', '**extra_receiver_values}')
        self.assertNotEqual(source, mutated)
        with self.assertRaises(ValueError):
            receiver_shapes(mutated)


if __name__ == "__main__":
    unittest.main()
