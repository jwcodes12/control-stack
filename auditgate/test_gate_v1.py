"""v1 gate tests with explicit expected outcomes (R6-3). Each attempt is classified:
DENIED (statement rejected), ALLOWED_BUT_SAFE (accepted, invariant and audit rows intact), BROKEN (invariant violated
or an audit row lost), CHECK_FAILED (the checker itself errored). A run passes only if every attempt's class equals
its declared expected class. Connection via PGHOST/PGPORT (docker locally, a service container in CI)."""
import json, os, subprocess, sys, threading

HOST, PORT = os.environ.get("PGHOST", "127.0.0.1"), os.environ.get("PGPORT", "55432")


VIA = os.environ.get("PSQL_VIA_DOCKER")  # local: run psql inside the container; CI: use the runner's psql


def psql(user, pw, sql):
    env = dict(os.environ, PGPASSWORD=pw)
    args = ["-X", "-q", "-At", "-U", user, "-d", "postgres", "-v", "ON_ERROR_STOP=1"]
    if VIA:
        cmd = ["docker", "exec", "-i", "-e", f"PGPASSWORD={pw}", VIA, "psql", "-h", "127.0.0.1", "-p", "5432"] + args
    else:
        cmd = ["psql", "-h", HOST, "-p", PORT] + args
    p = subprocess.run(cmd, input=sql, capture_output=True, text=True, env=env)
    return p.returncode, (p.stdout + p.stderr).strip()


APP = lambda sql: psql("app", "app", sql)
DISP = lambda sql: psql("dispatcher", "dispatcher", sql)
SU = lambda sql: psql("postgres", os.environ.get("PGSUPW", "trusted"), sql)


def check():
    rc, v = SU("SELECT count(*) FROM audit.violations;")
    rc2, rows = SU("SELECT request_id||':'||workflow_id||':'||requested_by FROM audit.execution_audit;")
    if rc or rc2:
        return None, None
    return int(v), set(rows.splitlines())


CASES = [  # (name, actor, sql, expected)
    ("honest: request execution", APP, "INSERT INTO audit.request(workflow_id, requested_by) VALUES (1,'alice');", "ALLOWED_BUT_SAFE"),
    ("honest: dispatcher runs it", DISP, "SELECT audit.dispatch_next();", "ALLOWED_BUT_SAFE"),
    ("honest: app event", APP, "INSERT INTO audit.app_event(event_type, metadata) VALUES ('workflow.list','{}');", "ALLOWED_BUT_SAFE"),
    ("honest: read audits", APP, "SELECT count(*) FROM audit.execution_audit;", "ALLOWED_BUT_SAFE"),
    ("honest: own-schema migration", APP, "CREATE TABLE appdata.t(id int); ALTER TABLE appdata.t ADD c text; DROP TABLE appdata.t;", "ALLOWED_BUT_SAFE"),
    ("forge mandatory audit", APP, "INSERT INTO audit.execution_audit(request_id,workflow_id,requested_by) VALUES (1,1,'x');", "DENIED"),
    ("reserved type via app_event", APP, "INSERT INTO audit.app_event(event_type, metadata) VALUES ('workflow.execute','{\"executionId\":1}');", "DENIED"),
    ("malformed id in app_event", APP, "INSERT INTO audit.app_event(event_type, metadata) VALUES ('x','{\"executionId\":\"not-an-integer\"}');", "ALLOWED_BUT_SAFE"),
    ("oversized metadata", APP, "INSERT INTO audit.app_event(event_type, metadata) VALUES ('x', jsonb_build_object('a', repeat('z', 20000)));", "DENIED"),
    ("deeply nested metadata", APP, "INSERT INTO audit.app_event(event_type, metadata) VALUES ('x', ('{\"a\":' || repeat('[', 500) || repeat(']', 500) || '}')::jsonb);", "ALLOWED_BUT_SAFE"),
    ("bounded flood of app events", APP, "INSERT INTO audit.app_event(event_type, metadata) SELECT 'noise', '{}' FROM generate_series(1,5000);", "ALLOWED_BUT_SAFE"),
    ("app performs effect directly", APP, "INSERT INTO audit.effect(request_id) VALUES (1);", "DENIED"),
    ("app calls dispatcher", APP, "SELECT audit.dispatch_next();", "DENIED"),
    ("app sets request_id", APP, "INSERT INTO audit.request(id, workflow_id, requested_by) VALUES (424242, 1, 'x');", "DENIED"),
    ("delete mandatory audit", APP, "DELETE FROM audit.execution_audit;", "DENIED"),
    ("update mandatory audit", APP, "UPDATE audit.execution_audit SET requested_by='nobody';", "DENIED"),
    ("delete request (cascade attempt)", APP, "DELETE FROM audit.request;", "DENIED"),
    ("truncate", APP, "TRUNCATE audit.execution_audit;", "DENIED"),
    ("drop FK", APP, "ALTER TABLE audit.effect DROP CONSTRAINT effect_request_id_fkey;", "DENIED"),
    ("replica mode", APP, "SET session_replication_role = replica;", "DENIED"),
    ("replace dispatcher fn", APP, "CREATE OR REPLACE FUNCTION audit.dispatch_next() RETURNS bigint LANGUAGE sql AS 'SELECT 1::bigint';", "DENIED"),
    ("self-grant", APP, "GRANT INSERT ON audit.effect TO app;", "ALLOWED_BUT_SAFE"),  # WARNING, no privilege granted
    ("become owner", APP, "ALTER TABLE audit.effect OWNER TO app;", "DENIED"),
    ("set role dispatcher", APP, "SET ROLE dispatcher;", "DENIED"),
    ("create role", APP, "CREATE ROLE evil SUPERUSER;", "DENIED"),
    ("dispatcher forges effect without audit", DISP, "INSERT INTO audit.effect(request_id) VALUES (999);", "DENIED"),
    ("dispatcher deletes audit", DISP, "DELETE FROM audit.execution_audit;", "DENIED"),
]


def main():
    ok, matrix = True, []
    v, snap = check()
    assert v == 0
    for name, actor, sql, expected in CASES:
        rc, out = actor(sql)
        v, rows = check()
        if v is None:
            got = "CHECK_FAILED"
        elif v != 0 or not snap <= rows:
            got = "BROKEN"
        elif rc != 0:
            got = "DENIED"
        else:
            got = "ALLOWED_BUT_SAFE"
        if rows is not None:
            snap = rows
        good = got == expected
        ok &= good
        matrix.append({"case": name, "expected": expected, "got": got, "rc": rc, "msg": out.splitlines()[-1][:120] if out else ""})
        print(f"{'ok  ' if good else 'FAIL'} {got:<17} (expected {expected:<17}) {name}")
    # concurrency: 20 requests, 4 dispatchers in parallel; every effect exactly once and audited
    APP("INSERT INTO audit.request(workflow_id, requested_by) SELECT 2, 'bob' FROM generate_series(1,20);")
    def worker():
        for _ in range(10):
            DISP("SELECT audit.dispatch_next();")
    ts = [threading.Thread(target=worker) for _ in range(4)]
    [t.start() for t in ts]; [t.join() for t in ts]
    _, dup = SU("SELECT count(*) - count(DISTINCT request_id) FROM audit.effect;")
    _, pend = SU("SELECT count(*) FROM audit.request q WHERE NOT EXISTS (SELECT 1 FROM audit.effect e WHERE e.request_id=q.id);")
    v, _ = check()
    conc = dup == "0" and pend == "0" and v == 0
    print(f"{'ok  ' if conc else 'FAIL'} concurrency: duplicates={dup} pending={pend} violations={v}")
    ok &= conc
    matrix.append({"case": "concurrent dispatchers (4x, 20 requests)", "expected": "no duplicate, none pending, invariant",
                   "got": f"dup={dup} pending={pend} violations={v}"})
    json.dump(matrix, open(os.path.join(os.path.dirname(__file__), "outcome_matrix.json"), "w"), indent=1)
    print("ALL AS EXPECTED" if ok else "MISMATCH"); sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
