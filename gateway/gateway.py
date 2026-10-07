"""Fail-closed covert-channel gateway (prototype; CATASTROPHE-SPEC.md, ControlStack/CovertChannel.lean,
ControlStack/GatewayModel.lean).

Makes the premise of `covert_bound` true by construction: everything a machine receiver observes over the secret's
LIFETIME is one value in a finite set fixed in advance, with exact integer cardinality ≤ 2^budget_bits.

v2 (after reviews/covert-channel-gateway-review-2026-10-07.md):
- configuration is deep-validated and frozen (primitive enum values int/str/bool only, unique names and values, slots
  a positive int); cardinality is EXACT integer arithmetic over REACHABLE views: prod_c sum_{j<=slots_c} |schema_c|^j;
- a LifetimeLedger charges every episode's view-space size against a cumulative budget per lineage (secret lifetime ×
  receiver memory scope); an episode that would exceed it is refused before it starts (P0-1);
- alerts are fixed codes; no attacker-controlled strings are stored (P0-2);
- close() atomically freezes the delivered transcript; later sends cannot change it (P0-4).
The gateway must run outside the untrusted agents' process (see harness.py); Python object privacy is not a boundary.
"""
from __future__ import annotations

import json
import os
from dataclasses import dataclass
from pathlib import Path

NULL = None  # padding symbol; counted in the alphabet
PRIMITIVE = (int, str, bool)
ALERT_CODES = ("REFUSED_SEND", "SLOT_OVERFLOW", "UNKNOWN_CHANNEL", "AFTER_CLOSE", "DENIED_ACTION")


class GatewayError(Exception):
    pass


def _check_value(v):
    if type(v) not in PRIMITIVE:
        raise GatewayError("enum values must be int, str or bool")


@dataclass(frozen=True)
class Schema:
    fields: tuple  # ((name, (allowed values...)), ...)

    def __post_init__(self):
        if type(self.fields) is not tuple or not self.fields:
            raise GatewayError("schema fields must be a non-empty tuple")
        names = []
        for f in self.fields:
            if type(f) is not tuple or len(f) != 2 or type(f[0]) is not str or type(f[1]) is not tuple or not f[1]:
                raise GatewayError("each field is (name: str, values: non-empty tuple)")
            for v in f[1]:
                _check_value(v)
            if len({(type(v), v) for v in f[1]}) != len(f[1]):
                raise GatewayError("duplicate enum value")
            names.append(f[0])
        if len(set(names)) != len(names):
            raise GatewayError("duplicate field name")

    def size(self) -> int:
        n = 1
        for _, vals in self.fields:
            n *= len(vals)
        return n

    def validate(self, payload) -> tuple:
        if type(payload) is not dict:
            raise GatewayError("payload must be a dict")
        names = [n for n, _ in self.fields]
        if len(payload) != len(names) or any(type(k) is not str for k in payload) or set(payload) != set(names):
            raise GatewayError("fields must match the schema exactly")
        out = []
        for name, vals in self.fields:
            v = payload[name]
            if not any(type(v) is type(a) and v == a for a in vals):
                raise GatewayError("value not an exact enum member")
            out.append(v)
        return tuple(out)


@dataclass(frozen=True)
class Channel:
    name: str
    schema: Schema
    slots: int

    def __post_init__(self):
        if type(self.name) is not str or type(self.schema) is not Schema:
            raise GatewayError("bad channel")
        if type(self.slots) is not int or self.slots < 1:
            raise GatewayError("slots must be a positive int")

    def alphabet(self) -> int:
        """Exact number of REACHABLE slot tuples: j accepted values then NULLs, j = 0..slots (blanked = j = 0).
        Lean: GatewayModel.gateway_bound_reachable."""
        s = self.schema.size()
        return sum(s ** j for j in range(self.slots + 1))


def view_space_size(channels) -> int:
    n = 1
    for c in channels:
        n *= c.alphabet()
    return n


class LifetimeLedger:
    """Cumulative view-space accounting per lineage. Product of episode view-space sizes must stay ≤ 2^budget_bits
    (covert_bound applied to the product of all episode views a receiver lineage can accumulate)."""

    def __init__(self, path: Path, budget_bits: int):
        if type(budget_bits) is not int or budget_bits < 0:
            raise GatewayError("budget_bits must be a non-negative int")
        self.path, self.cap = Path(path), 2 ** budget_bits

    def _load(self) -> dict:
        return json.loads(self.path.read_text()) if self.path.exists() else {}

    def charge(self, lineage: str, size: int) -> bool:
        d = self._load()
        used = int(d.get(lineage, 1))
        if used * size > self.cap:
            return False
        d[lineage] = str(used * size)
        tmp = self.path.with_suffix(".tmp")
        tmp.write_text(json.dumps(d))
        os.replace(tmp, self.path)
        return True


class Gateway:
    def __init__(self, channels, budget_bits: int = 16, ledger: LifetimeLedger | None = None,
                 lineage: str | None = None):
        if type(budget_bits) is not int or budget_bits < 0:
            raise GatewayError("budget_bits must be a non-negative int")
        chans = tuple(channels.values()) if isinstance(channels, dict) else tuple(channels)
        if any(type(c) is not Channel for c in chans) or len({c.name for c in chans}) != len(chans):
            raise GatewayError("channels must be uniquely named Channel objects")
        self._channels = {c.name: c for c in chans}  # frozen dataclasses; the dict is private to the trusted process
        self.size = view_space_size(chans)
        if self.size > 2 ** budget_bits:
            raise GatewayError("configuration exceeds the per-episode budget")
        if ledger is not None and not ledger.charge(str(lineage), self.size):
            raise GatewayError("lifetime budget exhausted for this lineage; episode refused")
        self.alerts: list[str] = []
        self._buf = {n: [] for n in self._channels}
        self._blanked = False
        self._snapshot = None

    def _alert(self, code: str) -> None:
        assert code in ALERT_CODES
        self.alerts.append(code)

    def send(self, channel, payload) -> None:
        if self._snapshot is not None:
            self._alert("AFTER_CLOSE"); return  # cannot change the frozen transcript
        ch = self._channels.get(channel) if type(channel) is str else None
        if ch is None:
            self._alert("UNKNOWN_CHANNEL"); self._blanked = True; return
        if len(self._buf[channel]) >= ch.slots:
            self._alert("SLOT_OVERFLOW"); self._blanked = True; return
        try:
            self._buf[channel].append(ch.schema.validate(payload))
        except (GatewayError, TypeError, ValueError):
            self._alert("REFUSED_SEND"); self._blanked = True

    def act(self, kind=None, *args, **kwargs):
        self._alert("DENIED_ACTION")
        if self._snapshot is None:
            self._blanked = True
        return None

    def close(self) -> None:
        if self._snapshot is None:
            self._snapshot = tuple(
                (n, tuple([NULL] * ch.slots if self._blanked else self._buf[n] + [NULL] * (ch.slots - len(self._buf[n]))))
                for n, ch in self._channels.items())

    def deliver(self) -> dict:
        if self._snapshot is None:
            raise GatewayError("delivery only after episode close")
        return dict(self._snapshot)

    def view_space_size(self) -> int:
        return self.size
