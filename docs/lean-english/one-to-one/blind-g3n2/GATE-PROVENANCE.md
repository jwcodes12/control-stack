The gate helper is a byte-for-byte copy of the allowed leangate_imports.py. Banned-token and axiom checks are unchanged. The runner changes only imports, glob, and the root depth required by its output-directory relocation (parents[3] becomes parents[4]). Witness gating is performed separately by regate.py. Run Python with PYTHONDONTWRITEBYTECODE=1.

Gate SHA-256: 8bcaba822fe25a5b7ffe7493980033960d1b262995d2f9060f21f4c58e0e7e84
