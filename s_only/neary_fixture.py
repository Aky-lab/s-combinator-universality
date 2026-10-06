"""Independent, bounded left-move fixture for Neary's Theorem 4.3.2.

Primary source: Neary, Small universal Turing machines (2008), pp. 65-75,
Tables 4.3.1-4.3.7. This specializes the published left-move construction to
one two-state machine and records ordinary CTS execution.
"""
from dataclasses import asdict, dataclass
from hashlib import sha256
import json

from .cts import Configuration, Machine, Program

SOURCE_URL = "https://tilde.ini.uzh.ch/users/tneary/public_html/tneary_Thesis.pdf"
Q = 2
Z = 60 * Q + 121
PERIOD = 2 * Z
HALT_INDEX = 60 * Q + 50


def one_hot(offset: int, length: int) -> str:
    if not 0 <= offset < length:
        raise ValueError("one-hot offset must be inside its word")
    return "0" * offset + "1" + "0" * (length - offset - 1)


def state_object(stage: str, state: int = 1, *, spare: bool = False) -> str:
    """spare denotes the thesis's s < s' flag; it is not a new TM state."""
    if state not in (1, 2):
        raise ValueError("this fixture has only q1 and q2")
    if state == 2 and (stage != "1" or spare):
        raise ValueError("only the ordinary halt-state token is defined")
    offsets = {"1": 50, "1p": 51, "2": 42, "2p": 33, "2pp": 24, "3": 44}
    if stage not in offsets:
        raise ValueError("unknown construction stage")
    offset = 60 * state + offsets[stage] + (5 if spare else 0)
    if stage == "1":
        length = PERIOD
    elif stage == "3":
        length = Z + 60 * state + 50 + (10 if spare else 0)
    else:
        length = PERIOD + 10
    return one_hot(offset, length)


OBJECTS = {
    "a": one_hot(1, PERIOD), "b": one_hot(2, PERIOD),
    "B": one_hot(3, PERIOD),
    "a/": one_hot(4, PERIOD), "b/": one_hot(5, PERIOD),
    "B/": one_hot(6, PERIOD),
    "mu": one_hot(7, Z), "mup": one_hot(8, PERIOD),
    "mu/": one_hot(9, PERIOD),
    "ap": one_hot(10, Z), "bp": one_hot(11, Z),
    "Bp": one_hot(12, Z), "dp": one_hot(13, Z),
    "d": one_hot(13, PERIOD), "D": one_hot(69, PERIOD + 70),
}
HALT_TOKEN = state_object("1", 2)


@dataclass(frozen=True)
class SourceConfiguration:
    state: int
    tape: str
    head: int


def source_step(source: SourceConfiguration) -> SourceConfiguration:
    """Direct TM rule, separate from CTS tables and boundary recognition."""
    if source.state != 1 or not 0 <= source.head < len(source.tape):
        raise ValueError("fixture step requires q1 with its head on the tape")
    if set(source.tape) - {"a", "b"}:
        raise ValueError("source alphabet is {a,b}")
    cells = list(source.tape)
    cells[source.head] = {"a": "b", "b": "a"}[cells[source.head]]
    return SourceConfiguration(2, "".join(cells), source.head - 1)


@dataclass(frozen=True)
class Fixture:
    program: Program
    provenance: tuple[tuple[str, ...], ...]

    def program_document(self) -> dict:
        return {
            "format": "neary-left-toggle-cts-v1", "source_url": SOURCE_URL,
            "source_pages": "65-75", "state_count": Q, "z": Z,
            "phase_count": PERIOD, "halt_index": HALT_INDEX,
            "transitions": [
                {"state": 1, "read": "a", "write": "b", "direction": "L", "next": 2},
                {"state": 1, "read": "b", "write": "a", "direction": "L", "next": 2}],
            "appendants": list(self.program.appendants),
            "provenance": [list(items) for items in self.provenance],
        }


def compile_fixture() -> Fixture:
    """Expand the seven tables; reject conflicting assignments instead of guessing.

    Unused indices are epsilon. Copy rows omitted by Tables 4.3.3-4.3.5 are
    instantiated only for the object types and marker phases present there.
    """
    assigned: dict[int, str] = {}
    origins: dict[int, list[str]] = {}
    o = OBJECTS

    def put(index, value, origin):
        if not 0 <= index < PERIOD:
            raise ValueError(f"table index out of range: {index}")
        if index in assigned and assigned[index] != value:
            raise ValueError(f"conflicting table assignments at {index}: {origins[index]} / {origin}")
        assigned[index] = value
        origins.setdefault(index, []).append(origin)

    def row(obj, phase, value, origin):
        if obj.count("1") != 1:
            raise ValueError("table's input object must be one-hot")
        put((phase + obj.index("1")) % PERIOD, value, origin)

    def copy(names, phases, origin):
        for name in names:
            for phase in phases:
                row(o[name], phase, o[name], origin + ": " + name)

    # Table 4.3.1, including the z-offset flag-changing rows.
    for spare in (False, True):
        row(state_object("1", spare=spare), 0, state_object("1p", spare=spare), "4.3.1 state")
        row(state_object("1", spare=spare), Z,
            "0" * Z + state_object("1p", spare=True), "4.3.1 odd parity")
    copy(("a", "b", "B", "a/", "b/", "B/", "mup", "mu/"), (0, Z), "4.3.1 copy")
    row(o["mu"], 0, o["mu/"], "4.3.1 halve odd")
    row(o["mu"], Z, o["mup"], "4.3.1 halve even")

    # Table 4.3.2.
    for spare in (False, True):
        row(state_object("1p", spare=spare), 0, state_object("2", spare=spare), "4.3.2 continue")
        row(state_object("1p", spare=spare), Z, state_object("3", spare=spare), "4.3.2 finish")
    for name in ("a", "b", "B"):
        row(o[name], 10, o[name + "p"], "4.3.2 prime")
        row(o[name], Z + 10, o[name], "4.3.2 final pass")
    copy(("a/", "b/", "B/", "mup", "mu/"), (10, Z + 10), "4.3.2 copy")

    # Table 4.3.3 and its explicit prose rule for omitted copy rows.
    for spare in (False, True):
        row(state_object("2", spare=spare), 10, state_object("2p", spare=spare), "4.3.3 state")
    copy(("ap", "bp", "Bp", "a/", "b/", "B/", "mup", "mu/"),
         (20, Z + 20), "4.3.3 implicit copy")

    # Table 4.3.4. A full-length dummy becomes a short dummy at marker 30.
    for spare in (False, True):
        row(state_object("2p", spare=spare), 20,
            o["d"] + state_object("2pp", spare=spare) + o["dp"], "4.3.4 even")
        row(state_object("2p", spare=spare), Z + 20,
            state_object("2pp", spare=spare), "4.3.4 odd")
    row(o["d"], 30, o["dp"], "4.3.4 dummy")
    copy(("ap", "bp", "Bp", "a/", "b/", "B/", "mup", "mu/"),
         (30, Z + 30), "4.3.4 implicit copy")

    # Table 4.3.5.
    for spare in (False, True):
        row(state_object("2pp", spare=spare), 30,
            "0" * (PERIOD - 40) + state_object("1", spare=spare), "4.3.5 state")
    for phase in (40, Z + 40):
        row(o["mup"], phase, o["mu"], "4.3.5 reset counter")
        row(o["dp"], phase, "", "4.3.5 erase dummy")
    for name in ("a", "b", "B"):
        row(o[name + "p"], 40, o[name], "4.3.5 keep odd")
        row(o[name + "p"], Z + 40, o[name + "/"], "4.3.5 mark even")
    copy(("a/", "b/", "B/", "mu/"), (40, Z + 40), "4.3.5 implicit copy")

    # Table 4.3.6, specialized only at the transition-dependent appendants.
    for spare in (False, True):
        phase = 60 + (70 if spare else 60)
        row(state_object("3", spare=spare), Z + 10,
            "0" * (PERIOD - phase), "4.3.6 reset marker")
        for read, write in (("a", "b"), ("b", "a")):
            row(o[read], phase, HALT_TOKEN + o[write], "4.3.6 transition " + read)
        row(o["B"], phase,
            o["B"] + ("" if spare else o["D"]) + HALT_TOKEN + o["a"], "4.3.6 extend blank")
        for name in ("a", "b", "B"):
            row(o[name + "/"], phase, o[name], "4.3.6 restore tape")
        row(o["mu/"], phase, o["mu"], "4.3.6 restore counter")

    # Table 4.3.7, retained even though the two test seeds do not extend tape.
    row(o["D"], 0, "0" * (PERIOD - 70), "4.3.7 doubling marker")
    for state in (1, 2):
        row(state_object("1", state), 70, state_object("1", state), "4.3.7 state copy")
    copy(("a", "b", "B"), (70,), "4.3.7 tape copy")
    for name in ("mu", "mup", "mu/"):
        row(o[name], 70, o[name] * 2, "4.3.7 double counter")
    row(o["mu"], Z + 70, o["mu"] * 2, "4.3.7 double even")

    # The halt paragraph on p. 75 replaces the nonhalting state construction.
    put(HALT_INDEX, HALT_TOKEN, "p.75 designated halt self-copy")
    return Fixture(Program(tuple(assigned.get(i, "") for i in range(PERIOD))),
                   tuple(tuple(origins.get(i, ["unused: epsilon"])) for i in range(PERIOD)))


def encode_seed(read_symbol: str = "b") -> Configuration:
    """Encode tape b<read_symbol>, head on the second cell, state q1."""
    if read_symbol not in ("a", "b"):
        raise ValueError("read_symbol must be a or b")
    return Configuration(state_object("1") + OBJECTS["B"] + OBJECTS["mu"] * 4
                         + OBJECTS["B"] + OBJECTS["b"] + OBJECTS[read_symbol])


@dataclass(frozen=True)
class Boundary:
    source: SourceConfiguration
    counter_objects: tuple[str, ...]


def decode_boundary(config: Configuration) -> Boundary:
    """Parse a stage-1 macro boundary structurally, without consulting a trace.

    Accept unmarked tape and a power-of-two counter of mu/mup/mu/ objects.
    Mixed counters are needed because the thesis overlaps the next counter
    pass with the completed transition (p.74). Stage-1 marking intermediates
    with marked tape are deliberately rejected.
    """
    if config.phase != 0:
        raise ValueError("macro boundary requires marker phase 0")
    word = config.word
    state = next((s for s in (1, 2) if word.startswith(state_object("1", s))), None)
    if state is None:
        raise ValueError("no ordinary stage-1 state at the front")
    cursor = PERIOD

    def take_tape():
        nonlocal cursor
        cells = []
        while True:
            token = word[cursor:cursor + PERIOD]
            name = next((n for n in ("a", "b", "B") if token == OBJECTS[n]), None)
            if name is None:
                raise ValueError("invalid tape or boundary object")
            cursor += PERIOD
            if name == "B":
                return "".join(cells)
            cells.append(name)

    right = take_tape()
    counters = []
    while not word.startswith(OBJECTS["B"], cursor):
        name = next((n for n in ("mu", "mup", "mu/") if word.startswith(OBJECTS[n], cursor)), None)
        if name is None:
            raise ValueError("invalid counter object")
        counters.append(name)
        cursor += len(OBJECTS[name])
    cursor += PERIOD
    left = []
    while cursor < len(word):
        token = word[cursor:cursor + PERIOD]
        name = next((n for n in ("a", "b") if token == OBJECTS[n]), None)
        if name is None:
            raise ValueError("invalid left tape object or trailing data")
        left.append(name)
        cursor += PERIOD
    tape = "".join(left) + right
    expected_count = 1 << (len(tape) + 1).bit_length()
    if len(counters) != expected_count:
        raise ValueError("counter capacity does not match tape length")
    return Boundary(SourceConfiguration(state, tape, len(left) - 1), tuple(counters))


def digest(word: str) -> str:
    return sha256(word.encode("ascii")).hexdigest()


def canonical_json(value) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def run_fixture(read_symbol: str = "b", *, max_steps: int = 100_000,
                max_word_bits: int = 16_384) -> dict:
    """Execute ordinary CTS steps through halt-token use and exact recurrence.

    No anticipated step number controls execution. Macro boundaries are
    recognized by parsing bit strings. Recurrence is checked only at these
    boundaries, making its memory cost bounded by the explicit step budget.
    """
    fixture = compile_fixture()
    seed = encode_seed(read_symbol)
    initial = decode_boundary(seed)
    expected = source_step(initial.source)
    machine = Machine(fixture.program, seed, max_steps=max_steps, max_word_bits=max_word_bits)
    boundaries = []
    seen = {}
    halt_event = None
    selected_appendants = set()
    visited_phases = set()
    zero_phases = set()
    one_events = 0
    recurrence = None
    while True:
        if machine.phase == 0:
            config = machine.snapshot()
            try:
                boundary = decode_boundary(config)
            except ValueError:
                boundary = None
            if boundary is not None:
                entry = {"cts_step": machine.steps, "phase": 0,
                         "word_bits": len(config.word), "word_sha256": digest(config.word),
                         "source": asdict(boundary.source),
                         "counter_objects": list(boundary.counter_objects)}
                boundaries.append(entry)
                key = (config.phase, config.word)
                if key in seen:
                    recurrence = {"first_step": seen[key], "repeated_step": machine.steps,
                                  "period_steps": machine.steps - seen[key],
                                  "word_bits": len(config.word), "word_sha256": digest(config.word)}
                    break
                seen[key] = machine.steps
        event = machine.tick()
        visited_phases.add(event.phase)
        if event.deleted == "0":
            zero_phases.add(event.phase)
        if event.deleted == "1":
            one_events += 1
            selected_appendants.add(event.phase)
            if fixture.provenance[event.phase] == ("unused: epsilon",):
                raise AssertionError(f"unassigned appendant used at phase {event.phase}")
            if event.phase == HALT_INDEX and halt_event is None:
                if event.appended != HALT_TOKEN:
                    raise AssertionError("designated halt appendant differs from halt token")
                halt_event = {"cts_step": event.step, "phase_before": event.phase,
                              "deleted": "1", "appended_bits": len(event.appended),
                              "appended_sha256": digest(event.appended),
                              "word_bits_after": event.word_bits}
    final_boundaries = [b for b in boundaries if b["source"]["state"] == 2]
    if halt_event is None or not final_boundaries:
        raise AssertionError("recurrence is not evidence of the designated source halt")
    if any(b["source"] != asdict(expected) for b in final_boundaries):
        raise AssertionError("decoded CTS result differs from the direct source rule")
    if not machine.word_bits:
        raise AssertionError("this source-halt encoding must not empty the queue")
    return {
        "format": "neary-left-toggle-run-v1", "read_symbol": read_symbol,
        "program_sha256": digest(canonical_json(fixture.program_document())),
        "seed_bits": len(seed.word), "seed_sha256": digest(seed.word),
        "source_initial": asdict(initial.source), "source_expected": asdict(expected),
        "source_decoded": final_boundaries[0]["source"],
        "source_transition_boundary_step": final_boundaries[0]["cts_step"],
        "source_halt_event": halt_event,
        "ordinary_cts_observation": "repeated_nonempty_configuration",
        "recurrence": recurrence, "macro_boundaries": boundaries,
        "cts_steps": machine.steps, "peak_word_bits": machine.peak_word_bits,
        "max_steps": max_steps, "max_word_bits": max_word_bits,
        "selected_appendant_indices": sorted(selected_appendants),
        "consumed_one_events": one_events,
        "consumed_zero_events": machine.steps - one_events,
        "selected_unspecified_appendant_events": 0,
        "distinct_phases_visited": len(visited_phases),
        "distinct_phases_consuming_zero": len(zero_phases),
        "table_4_3_7_exercised": 69 in selected_appendants,
        "s_reductions_performed": 0,
    }
