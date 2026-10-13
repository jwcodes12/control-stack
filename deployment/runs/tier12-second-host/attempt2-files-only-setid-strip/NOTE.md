Attempt 2 (kept as evidence): removed `.pth` / `sitecustomize*` / `usercustomize*` and cleared setuid/setgid bits on FILES only. The scan still
returned UNASSURED: `image-python-startup-hooks` was gone, `image-setuid-setgid-binaries` remained because the scanner counts ANY archive member
with a setid bit, including setgid directories (Ubuntu ships several). Attempt 3 clears the bits on all entries. The Landlock-dependent confinement
test passed on this kernel in this run (`test_confined_effect_broker.txt`).
