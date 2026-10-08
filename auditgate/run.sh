#!/usr/bin/env bash
# Reproduce the audit-gate bypass suite against a throwaway PostgreSQL 16 container (no network exposure beyond 127.0.0.1).
set -euo pipefail
cd "$(dirname "$0")"
docker rm -f cs-auditgate >/dev/null 2>&1 || true
docker run -d --rm --name cs-auditgate -e POSTGRES_PASSWORD=trusted -p 127.0.0.1:55432:5432 postgres:16-alpine >/dev/null
until docker exec cs-auditgate pg_isready -U postgres >/dev/null 2>&1; do sleep 1; done
docker exec -i cs-auditgate psql -q -v ON_ERROR_STOP=1 -U postgres < setup.sql
python3 test_gate.py; rc=$?
docker rm -f cs-auditgate >/dev/null
exit $rc
