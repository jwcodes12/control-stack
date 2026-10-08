#!/usr/bin/env bash
# Reproduce the audit-gate suites against a throwaway PostgreSQL 16 container bound to 127.0.0.1.
set -euo pipefail
cd "$(dirname "$0")"
docker rm -f cs-auditgate >/dev/null 2>&1 || true
docker run -d --rm --name cs-auditgate -e POSTGRES_PASSWORD=trusted -p 127.0.0.1:55432:5432 postgres@sha256:721873c34ceb9f8d8fc265984940dc982404c105f19ad51be9fdc5970a6080ea >/dev/null
trap 'docker rm -f cs-auditgate >/dev/null 2>&1 || true' EXIT
until docker exec cs-auditgate pg_isready -U postgres >/dev/null 2>&1; do sleep 1; done
export PGHOST=127.0.0.1 PGPORT=55432 PGSUPW=trusted PSQL_VIA_DOCKER=cs-auditgate
docker exec -i cs-auditgate psql -X -q -v ON_ERROR_STOP=1 -U postgres -d postgres < setup_v1.sql
python3 test_gate_v1.py
