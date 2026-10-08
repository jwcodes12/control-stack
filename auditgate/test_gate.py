"""Adversarial tests of the DB-level audit gate, run as the agent-controlled `app` role against real PostgreSQL 16.
Pass criterion: after every attack, (a) the reviewer-free invariant holds (audit.violations is empty) and (b) no
existing workflow.execute audit row was removed or changed. Honest operations must still work."""
import subprocess, sys

PSQL = ["docker", "exec", "-i", "-e", "PGPASSWORD=app", "cs-auditgate", "psql", "-q", "-At", "-h", "127.0.0.1",
        "-U", "app", "-d", "postgres", "-v", "ON_ERROR_STOP=1"]
SU = ["docker", "exec", "-i", "cs-auditgate", "psql", "-q", "-At", "-U", "postgres", "-d", "postgres"]


def run(sql, su=False):
    p = subprocess.run(SU if su else PSQL, input=sql, capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr).strip()


def state():
    _, v = run("SELECT count(*) FROM audit.violations;", su=True)
    _, rows = run("SELECT id||':'||metadata::text FROM audit.\"AuditLog\" WHERE \"eventType\"='workflow.execute';", su=True)
    return int(v), set(r for r in rows.splitlines() if r)


HONEST = [
    ("insert execution (API path)", 'INSERT INTO audit."Execution"("workflowId") VALUES (1);'),
    ("update execution status", 'UPDATE audit."Execution" SET status=\'success\' WHERE id=(SELECT max(id) FROM audit."Execution");'),
    ("write another audit event", 'INSERT INTO audit."AuditLog"("eventType",metadata) VALUES (\'workflow.list\',\'{}\');'),
    ("read audit log", 'SELECT count(*) FROM audit."AuditLog";'),
    ("app migrates its own tables", 'CREATE TABLE appdata.notes(id int); ALTER TABLE appdata.notes ADD COLUMN t text; DROP TABLE appdata.notes;'),
]
ATTACKS = [
    ("delete audit rows", 'DELETE FROM audit."AuditLog" WHERE "eventType"=\'workflow.execute\';'),
    ("update audit rows", 'UPDATE audit."AuditLog" SET "eventType"=\'x\';'),
    ("truncate audit", 'TRUNCATE audit."AuditLog";'),
    ("drop audit table", 'DROP TABLE audit."AuditLog";'),
    ("alter audit table", 'ALTER TABLE audit."AuditLog" RENAME TO old;'),
    ("drop trigger", 'DROP TRIGGER execution_audit ON audit."Execution";'),
    ("disable trigger", 'ALTER TABLE audit."Execution" DISABLE TRIGGER execution_audit;'),
    ("replica mode skips triggers", 'SET session_replication_role = replica; INSERT INTO audit."Execution"("workflowId") VALUES (2);'),
    ("replace trigger function", 'CREATE OR REPLACE FUNCTION audit.on_execution() RETURNS trigger LANGUAGE plpgsql AS $$BEGIN RETURN NEW; END$$;'),
    ("rule rewriting inserts", 'CREATE RULE skip AS ON INSERT TO audit."AuditLog" DO INSTEAD NOTHING;'),
    ("shadow table via search_path", 'CREATE TABLE appdata."AuditLog"(id int); SET search_path=appdata; INSERT INTO audit."Execution"("workflowId") VALUES (3);'),
    ("delete execution's audit via id spoof", 'INSERT INTO audit."AuditLog"("eventType",metadata) VALUES (\'workflow.execute\',\'{"executionId": -1}\'); DELETE FROM audit."AuditLog" WHERE id>0;'),
    ("insert execution with forged id", 'INSERT INTO audit."Execution"(id,"workflowId") VALUES (999999,4);'),
    ("copy into execution", 'COPY audit."Execution"("workflowId") FROM PROGRAM \'echo 5\';'),
    ("grant self more", 'GRANT DELETE ON audit."AuditLog" TO app;'),
    ("become owner", 'ALTER TABLE audit."AuditLog" OWNER TO app;'),
    ("set role trusted", 'SET ROLE trusted_owner; DELETE FROM audit."AuditLog";'),
    ("create superuser", 'CREATE ROLE evil SUPERUSER LOGIN;'),
]
ok = True
for name, sql in HONEST:
    rc, out = run(sql)
    print(f"HONEST {'ok  ' if rc == 0 else 'FAIL'} {name}" + ("" if rc == 0 else f": {out[:120]}"))
    ok &= rc == 0
v0, snap = state()
assert v0 == 0, "baseline invariant violated"
for name, sql in ATTACKS:
    rc, out = run(sql)
    v, rows = state()
    held = v == 0 and snap <= rows          # invariant holds and no prior audit row removed or altered
    ok &= held
    print(f"ATTACK {'held  ' if held else 'BROKEN'} rc={rc} {name}" + (f"  [{out.splitlines()[-1][:90]}]" if out else ""))
    snap = rows
print("ALL HELD" if ok else "SOME BROKEN"); sys.exit(0 if ok else 1)
