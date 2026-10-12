#!/usr/bin/env python3
"""Adversarial negative controls against the batched Lean fixture gate.

Run on a runner with the pinned Lean toolchain and built deployment contracts.
A fake invalid positive/negative certificate MUST fail Lean compilation.
A non-standard axiom MUST be rejected by the named report parser.
"""
from pathlib import Path
from tempfile import TemporaryDirectory

from tools.check_deployment_fixture_batch import (
    HEADER, ROOT, check_axiom_reports, lean, required_axiom_report_names,
)


def must_reject(fn, label):
    try:
        fn()
    except ValueError:
        print(f"PASS: rejected {label}")
        return
    raise AssertionError(f"FAIL: negative control unexpectedly accepted {label}")


def check_parser_controls():
    required = required_axiom_report_names(1)
    clean = "\n".join(f"'{name}' does not depend on any axioms"
                      for name in required)
    check_axiom_reports(clean, 1)
    # The old batch logic checked only a total count of nine. Swapping one
    # certificate for a duplicate would pass that count but must now fail.
    names = list(required)
    substituted = names[:-1] + [names[0]]
    must_reject(
        lambda: check_axiom_reports(
            "\n".join(f"'{n}' does not depend on any axioms" for n in substituted), 1
        ),
        "substituted fixture certificate report",
    )
    corrupt_axiom = clean.replace(
        f"'{names[0]}' does not depend on any axioms",
        f"'{names[0]}' depends on axioms: [SliceBatch.unsafe_extra]",
        1,
    )
    must_reject(lambda: check_axiom_reports(corrupt_axiom, 1),
                "non-standard axiom report")


def check_live_lean_controls():
    with TemporaryDirectory(prefix="cstack-negative-certs-", dir=ROOT / ".git") as tmp:
        file = Path(tmp) / "BadCertificates.lean"
        file.write_text(
            HEADER
            + "theorem intentionally_wrong : ¬ Accepted clean := by decide\n"
            + "end SliceBatch\n"
        )
        must_reject(lambda: lean(file), "false Lean Accepted certificate")
        file.write_text(
            HEADER
            + "axiom introduced_untrusted : True\n"
            + "theorem nonstandard_report : True := introduced_untrusted\n"
            + "end SliceBatch\n"
            + "#print axioms SliceBatch.nonstandard_report\n"
        )
        report = lean(file)
        if "SliceBatch.introduced_untrusted" not in report:
            raise AssertionError("Lean did not expose injected axiom")
        # Preserve the exact expected report count and names so this control
        # reaches the *axiom allowlist* check, not merely the missing-report gate.
        expected = list(required_axiom_report_names(1))
        corrupted_name = "SliceBatch.facts_0"
        if corrupted_name not in expected:
            raise AssertionError("batch fixture naming changed")
        substitute = report.replace(
            "'SliceBatch.nonstandard_report'",
            f"'{corrupted_name}'",
        )
        standard_others = "\n".join(
            f"'{name}' does not depend on any axioms"
            for name in expected if name != corrupted_name
        )
        must_reject(
            lambda: check_axiom_reports(standard_others + "\n" + substitute, 1),
            "Lean-generated non-standard axiom with all 9 named reports present",
        )


def main():
    check_parser_controls()
    check_live_lean_controls()
    print("PASS: batched certificate negative controls (compiler + report parser)")


if __name__ == "__main__":
    main()
