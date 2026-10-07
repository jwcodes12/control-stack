"""Fail-closed covert-channel gateway (prototype; CATASTROPHE-SPEC.md, ControlStack/CovertChannel.lean).

Makes the premise of `covert_bound` true by construction: the only thing a machine receiver observes from an episode
is ONE value v in a finite set V fixed in advance, with |V| = prod_c (|schema_c| + 1)^{slots_c} ≤ 2^budget_bits.

Rules
- Channels carry only schema messages: a dict with exactly the declared fields, each value an EXACT member (type and
  value) of a declared finite enum. Each channel has a fixed number of slots per episode; unused slots are NULL.
- Delivery happens only at episode close, as a tuple of slot values per channel (no timestamps, no ordering across
  channels, no partial reads).
- Fail closed: any invalid send (bad field, type, value, extra slot, after close) is refused, the overseer is alerted,
  and the episode's delivery becomes all-NULL. All-NULL is itself in V, so a refusal cannot be used as a signal.
- Every other action (network, file write, process, environment) is denied by default.
- Configuration is rejected if log2|V| exceeds the budget.
Not verified code: the correspondence to the Lean model is argued in gateway/CORRESPONDENCE.md.
"""
from __future__ import annotations

import copy
import math
from dataclasses import dataclass, field

NULL = None  # the padding symbol; counted in the alphabet


class GatewayError(Exception):
    pass


@dataclass(frozen=True)
class Schema:
    fields: tuple  # ((name, (allowed values...)), ...)

    def size(self) -> int:
        n = 1
        for _, vals in self.fields:
            n *= len(vals)
        return n

    def validate(self, payload) -> tuple:
        if type(payload) is not dict:
            raise GatewayError("payload must be a dict")
        names = [n for n, _ in self.fields]
        if set(payload.keys()) != set(names) or len(payload) != len(names):
            raise GatewayError("fields must match the schema exactly")
        out = []
        for name, vals in self.fields:
            v = payload[name]
            if not any(type(v) is type(a) and v == a for a in vals):
                raise GatewayError(f"field {name!r}: value not an exact member of its enum")
            out.append(v)
        return tuple(out)


@dataclass
class Channel:
    name: str
    schema: Schema
    slots: int

    def alphabet(self) -> int:
        return (self.schema.size() + 1) ** self.slots  # +1 for NULL


@dataclass
class Gateway:
    channels: dict
    budget_bits: float = 16.0
    alerts: list = field(default_factory=list)
    _buf: dict = field(default_factory=dict)
    _closed: bool = False
    _blanked: bool = False

    def __post_init__(self):
        bits = sum(math.log2(c.alphabet()) for c in self.channels.values())
        if bits > self.budget_bits + 1e-12:
            raise GatewayError(f"configuration leaks {bits:.3f} bits > budget {self.budget_bits}")
        self.bits = bits
        self._buf = {n: [] for n in self.channels}

    # ---- sender side -------------------------------------------------------------------------------------------
    def send(self, channel: str, payload) -> None:
        try:
            if self._closed:
                raise GatewayError("episode closed")
            if channel not in self.channels:
                raise GatewayError("unknown channel")
            ch = self.channels[channel]
            if len(self._buf[channel]) >= ch.slots:
                raise GatewayError("slot budget exhausted")
            value = ch.schema.validate(copy.deepcopy(payload))
            self._buf[channel].append(value)
        except GatewayError as e:
            self.alerts.append(f"refused send on {channel!r}: {e}")
            self._blanked = True  # fail closed; the receiver sees all-NULL
        # never raise to the sender: refusal must not be observable differently from acceptance by anyone but overseer

    def act(self, kind: str, *args, **kwargs):
        self.alerts.append(f"denied action {kind!r}")
        self._blanked = True
        return None  # default deny

    # ---- receiver side -----------------------------------------------------------------------------------------
    def close(self) -> None:
        self._closed = True

    def deliver(self) -> dict:
        if not self._closed:
            raise GatewayError("delivery only after episode close")
        out = {}
        for n, ch in self.channels.items():
            vals = [NULL] * ch.slots if self._blanked else (self._buf[n] + [NULL] * (ch.slots - len(self._buf[n])))
            out[n] = tuple(vals)
        return out

    def view_space_size(self) -> int:
        n = 1
        for c in self.channels.values():
            n *= c.alphabet()
        return n
