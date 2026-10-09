"""Executable transliteration of the Lean model `ControlStack.SC26` (ControlStack/Scenarios/SC26Transaction.lean).

Every definition here mirrors one Lean definition of the same name: `Tx`, `Roles`, `Req`, `St`, the six `Op`
constructors, `Checks`/`FULL`, `INIT`, `req_of` (first match, as `List.find?`), `bank_append`, the non-atomic delivery (`deliver` sends a
message to `net`; `arrive` lets the bank process the first message with that key), `step`, `run`,
`legal`, `approved`, `amt`, `inv` (the `Inv` structure, field by field), `sound`, `once` (`sc26_once`) and `good`. States are immutable tuples, so
a step never mutates its input. `guard` is NOT a Lean definition: it names the condition under which `step` takes
its non-identity branch, so the trace checker can compare the runtime's accept/refuse decision with the model's.

`lean_difftest.py` checks this transliteration against Lean's own `#eval` of `run` on random traces.
"""
from __future__ import annotations

from typing import NamedTuple, Optional


class Tx(NamedTuple):
    dest: int
    amount: int
    memo: int


class Roles(NamedTuple):
    agents: tuple
    approvers: tuple
    admins: tuple
    gate: int


class Req(NamedTuple):
    id: int
    requester: int
    tx: Tx


class St(NamedTuple):
    next: int
    reqs: tuple  # of Req
    approvals: tuple  # of (id, approver, Tx)
    reserved: tuple  # of int
    spent: int
    halted: bool
    bank: tuple  # of (key, Tx)
    net: tuple  # of (key, Tx): every message the gate ever sent to the bank (may arrive any number of times)


class Checks(NamedTuple):
    distinct: bool
    payload: bool
    nonce: bool
    cap: bool
    haltCheck: bool
    bankDedup: bool
    bankAuth: bool


FULL = Checks(True, True, True, True, True, True, True)
INIT = St(0, (), (), (), 0, False, (), ())


# Op constructors: plain tuples tagged by the Lean constructor name.
def request(caller, tx): return ("request", caller, Tx(*tx))
def approve(caller, id, tx): return ("approve", caller, id, Tx(*tx))
def execute(caller, id): return ("execute", caller, id)
def deliver(id): return ("deliver", id)
def arrive(key): return ("arrive", key)
def bankCall(caller, key, tx): return ("bankCall", caller, key, Tx(*tx))
def halt(caller): return ("halt", caller)


def req_of(s: St, id: int) -> Optional[Req]:
    for r in s.reqs:
        if r.id == id:
            return r
    return None


def bank_append(C: Checks, s: St, key: int, tx: Tx) -> St:
    if C.bankDedup and key in [e[0] for e in s.bank]:
        return s
    return s._replace(bank=s.bank + ((key, tx),))


def _halted(s, C):
    return s.halted and C.haltCheck


def step(R: Roles, cap: int, C: Checks, s: St, o) -> St:
    tag = o[0]
    if tag == "request":
        _, c, tx = o
        if _halted(s, C):
            return s
        if c in R.agents:
            return s._replace(reqs=s.reqs + (Req(s.next, c, tx),), next=s.next + 1)
        return s
    if tag == "approve":
        _, c, id, tx = o
        if _halted(s, C):
            return s
        r = req_of(s, id)
        if r is None:
            return s
        if c in R.approvers and ((not C.distinct) or c != r.requester) and ((not C.payload) or tx == r.tx):
            return s._replace(approvals=s.approvals + ((id, c, tx),))
        return s
    if tag == "execute":
        _, _c, id = o
        if _halted(s, C):
            return s
        r = req_of(s, id)
        if r is None:
            return s
        if (any(ap[0] == id for ap in s.approvals) and ((not C.nonce) or id not in s.reserved)
                and ((not C.cap) or s.spent + r.tx.amount <= cap)):
            return s._replace(reserved=s.reserved + (id,), spent=s.spent + r.tx.amount)
        return s
    if tag == "deliver":
        _, id = o
        if _halted(s, C):
            return s
        if id in s.reserved:
            r = req_of(s, id)
            if r is None:
                return s
            return s._replace(net=s.net + ((id, r.tx),))
        return s
    if tag == "arrive":
        _, key = o
        m = next((m for m in s.net if m[0] == key), None)
        if m is None:
            return s
        return bank_append(C, s, m[0], m[1])
    if tag == "bankCall":
        _, c, key, tx = o
        if C.bankAuth and c != R.gate:
            return s
        return bank_append(C, s, key, tx)
    if tag == "halt":
        _, c = o
        if c in R.admins:
            return s._replace(halted=True)
        return s
    raise ValueError(f"unknown op {o!r}")


def run(R, cap, C, s, ops):
    for o in ops:
        s = step(R, cap, C, s, o)
    return s


def guard(R: Roles, cap: int, C: Checks, s: St, o) -> bool:
    """True iff `step` takes its non-identity branch (for deliver/bankCall: reaches `bank_append`, which may still
    be a no-op on a duplicate key; for halt: the admin branch)."""
    tag = o[0]
    if tag == "halt":
        return o[1] in R.admins
    if tag == "bankCall":
        return not (C.bankAuth and o[1] != R.gate)
    if tag == "arrive":
        return any(m[0] == o[1] for m in s.net)
    if _halted(s, C):
        return False
    if tag == "request":
        return o[1] in R.agents
    if tag == "approve":
        _, c, id, tx = o
        r = req_of(s, id)
        return r is not None and c in R.approvers and ((not C.distinct) or c != r.requester) and \
            ((not C.payload) or tx == r.tx)
    if tag == "execute":
        _, _c, id = o
        r = req_of(s, id)
        return r is not None and any(ap[0] == id for ap in s.approvals) and \
            ((not C.nonce) or id not in s.reserved) and ((not C.cap) or s.spent + r.tx.amount <= cap)
    if tag == "deliver":
        return o[1] in s.reserved and req_of(s, o[1]) is not None
    raise ValueError(f"unknown op {o!r}")


def legal(R: Roles, o) -> bool:
    return not (o[0] == "bankCall" and o[1] == R.gate)


def approved(R: Roles, s: St, k: int, r: Req) -> bool:
    return any(ap[0] == k and ap[2] == r.tx and ap[1] in R.approvers and ap[1] != r.requester for ap in s.approvals)


def amt(s: St, k: int) -> int:
    r = req_of(s, k)
    return 0 if r is None else r.tx.amount


def inv(R: Roles, cap: int, s: St) -> list:
    """Return the list of violated `Inv` fields (empty iff `Inv R cap s`)."""
    bad = []
    for ap in s.approvals:
        r = req_of(s, ap[0])
        if not (r is not None and ap[2] == r.tx and ap[1] in R.approvers and ap[1] != r.requester):
            bad.append(("appr_ok", ap))
    for k in s.reserved:
        r = req_of(s, k)
        if not (r is not None and approved(R, s, k, r)):
            bad.append(("res_ok", k))
    if s.spent != sum(amt(s, k) for k in s.reserved):
        bad.append(("spent_eq", s.spent))
    if not s.spent <= cap:
        bad.append(("spent_le", s.spent))
    for e in s.bank:
        r = req_of(s, e[0])
        if not (e[0] in s.reserved and r is not None and r.tx == e[1]):
            bad.append(("bank_ok", e))
    keys = [e[0] for e in s.bank]
    if len(set(keys)) != len(keys):
        bad.append(("bank_nodup", keys))
    for m in s.net:
        r = req_of(s, m[0])
        if not (m[0] in s.reserved and r is not None and r.tx == m[1]):
            bad.append(("net_ok", m))
    return bad


def sound(C: Checks) -> bool:
    """Lean `Sound C`: the checks the safety proof needs (not `nonce`, not `haltCheck`)"""
    return C.distinct and C.payload and C.cap and C.bankDedup and C.bankAuth


def once(s: St) -> bool:
    """Lean `sc26_once`: under `full`, no id is reserved twice"""
    return len(set(s.reserved)) == len(s.reserved)


def good(R: Roles, cap: int, s: St) -> bool:
    for e in s.bank:
        r = req_of(s, e[0])
        if not (r is not None and r.tx == e[1] and e[0] in s.reserved and approved(R, s, e[0], r)):
            return False
    keys = [e[0] for e in s.bank]
    return len(set(keys)) == len(keys) and sum(e[1].amount for e in s.bank) <= cap


# ---- rendering for the Lean differential test ----

def _tx_lean(t: Tx) -> str:
    return f"⟨{t.dest}, {t.amount}, {t.memo}⟩"


def op_to_lean(o) -> str:
    tag = o[0]
    if tag == "request":
        return f"Op.request {o[1]} {_tx_lean(o[2])}"
    if tag == "approve":
        return f"Op.approve {o[1]} {o[2]} {_tx_lean(o[3])}"
    if tag == "execute":
        return f"Op.execute {o[1]} {o[2]}"
    if tag == "deliver":
        return f"Op.deliver {o[1]}"
    if tag == "arrive":
        return f"Op.arrive {o[1]}"
    if tag == "bankCall":
        return f"Op.bankCall {o[1]} {o[2]} {_tx_lean(o[3])}"
    if tag == "halt":
        return f"Op.halt {o[1]}"
    raise ValueError(o)


def to_lean(ops) -> str:
    return "[" + ", ".join(op_to_lean(o) for o in ops) + "]"


def roles_to_lean(R: Roles) -> str:
    l = lambda xs: "[" + ", ".join(map(str, xs)) + "]"
    return f"(⟨{l(R.agents)}, {l(R.approvers)}, {l(R.admins)}, {R.gate}⟩ : Roles)"


def _tx_key(t: Tx) -> str:
    return f"({t.dest},{t.amount},{t.memo})"


def state_to_key(s: St) -> str:
    """Canonical string; `lean_difftest.py` emits a Lean `canon` producing the identical format."""
    reqs = ";".join(f"{r.id}:{r.requester}:{_tx_key(r.tx)}" for r in s.reqs)
    apps = ";".join(f"{a[0]}:{a[1]}:{_tx_key(a[2])}" for a in s.approvals)
    res = ";".join(str(k) for k in s.reserved)
    bank = ";".join(f"{e[0]}:{_tx_key(e[1])}" for e in s.bank)
    net = ";".join(f"{e[0]}:{_tx_key(e[1])}" for e in s.net)
    return f"n={s.next}|r={reqs}|a={apps}|v={res}|s={s.spent}|h={'1' if s.halted else '0'}|b={bank}|m={net}"
