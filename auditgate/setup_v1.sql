-- v1.1 (after chatgpt-06 and chatgpt-08): authority over the EFFECT, trusted-origin audit, typed checker,
-- transactional ordering witness. DEMO CREDENTIALS BELOW ARE FOR THROWAWAY TEST DATABASES ONLY; never deploy them.
CREATE ROLE trusted_owner NOLOGIN;
CREATE ROLE app LOGIN PASSWORD 'app' NOSUPERUSER NOCREATEROLE NOCREATEDB NOREPLICATION NOBYPASSRLS;
CREATE ROLE dispatcher LOGIN PASSWORD 'dispatcher' NOSUPERUSER NOCREATEROLE NOCREATEDB NOREPLICATION NOBYPASSRLS;
CREATE SCHEMA appdata AUTHORIZATION app;
CREATE SCHEMA audit AUTHORIZATION trusted_owner;
GRANT USAGE ON SCHEMA audit TO app, dispatcher;
SET ROLE trusted_owner;
-- the app may only REQUEST an execution
CREATE TABLE audit.request (id bigserial PRIMARY KEY, workflow_id int NOT NULL, requested_by text NOT NULL,
                            requested_at timestamptz NOT NULL DEFAULT now());
GRANT SELECT, INSERT (workflow_id, requested_by) ON audit.request TO app;
GRANT USAGE ON SEQUENCE audit.request_id_seq TO app;
-- mandatory, trusted-origin audit: NO app write privileges at all
CREATE TABLE audit.execution_audit (request_id bigint PRIMARY KEY REFERENCES audit.request(id),
                                    workflow_id int NOT NULL, requested_by text NOT NULL,
                                    audited_at timestamptz NOT NULL DEFAULT clock_timestamp(),
                                    xact xid8 NOT NULL DEFAULT pg_current_xact_id());
GRANT SELECT ON audit.execution_audit TO app;
-- the effect authorisation: FK => an effect cannot exist without its audit row (enforced by PostgreSQL)
CREATE TABLE audit.effect (request_id bigint PRIMARY KEY REFERENCES audit.execution_audit(request_id),
                           dispatched_at timestamptz NOT NULL DEFAULT clock_timestamp(),
                           xact xid8 NOT NULL DEFAULT pg_current_xact_id());
GRANT SELECT ON audit.effect TO app;
-- optional app-generated events: separate, typed, reserved types and oversized metadata rejected
CREATE TABLE audit.app_event (id bigserial PRIMARY KEY, event_type text NOT NULL, metadata jsonb NOT NULL,
  CONSTRAINT not_reserved CHECK (event_type NOT IN ('workflow.execute')),
  CONSTRAINT bounded CHECK (pg_column_size(metadata) <= 8192 AND length(event_type) <= 64));
GRANT SELECT, INSERT (event_type, metadata) ON audit.app_event TO app;
GRANT USAGE ON SEQUENCE audit.app_event_id_seq TO app;
-- the trusted dispatcher step: audit then effect, one transaction; only the dispatcher role may call it
CREATE FUNCTION audit.dispatch_next() RETURNS bigint LANGUAGE plpgsql SECURITY DEFINER SET search_path = pg_catalog AS $$
DECLARE r audit.request;
BEGIN
  SELECT * INTO r FROM audit.request q
   WHERE NOT EXISTS (SELECT 1 FROM audit.effect e WHERE e.request_id = q.id)
   ORDER BY q.id LIMIT 1 FOR UPDATE SKIP LOCKED;
  IF NOT FOUND THEN RETURN NULL; END IF;
  INSERT INTO audit.execution_audit(request_id, workflow_id, requested_by)
    VALUES (r.id, r.workflow_id, r.requested_by) ON CONFLICT (request_id) DO NOTHING;   -- idempotent on retry
  INSERT INTO audit.effect(request_id) VALUES (r.id);                                  -- PK: no double effect
  RETURN r.id;
END $$;
REVOKE ALL ON FUNCTION audit.dispatch_next() FROM PUBLIC;
GRANT EXECUTE ON FUNCTION audit.dispatch_next() TO dispatcher;
-- reviewer-free checker: typed columns, no casts. Ordering witness is TRANSACTIONAL, not wall-clock (chatgpt-08
-- note 2): the audit row and the effect row must carry the same transaction id, i.e. they committed atomically.
-- Rows returned VIOLATE effect => audit-in-the-same-transaction (the FK alone guarantees existence).
CREATE VIEW audit.violations AS
  SELECT e.request_id FROM audit.effect e
  WHERE NOT EXISTS (SELECT 1 FROM audit.execution_audit a WHERE a.request_id = e.request_id AND a.xact = e.xact);
RESET ROLE;
