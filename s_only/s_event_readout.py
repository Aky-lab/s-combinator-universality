"""Polynomial, current-DAG-only UT19 first-event result interface.

The fixed F17 language checks syntax, not reachability or firstness. Correct
numeric interpretation additionally needs the hypotheses in docs/s-event-readout.md.
Compilation below constructs fixed grammar code once; readout runs no compiler,
clock, reduction, source evaluator, history search, or mutable-carrier reversal.
"""
from dataclasses import dataclass

from . import cts, ut19, ut19_readout
from .cts_reader import compile_reader as _compile_reference_grammar
from .encoding import B, HALT, LIVE, PI, VALUES
from .terms import App, S

ResourceLimit = cts.ResourceLimit
_ATOM = type(S)
HALT_TAG = App(B, S)
EVENT_LABEL = (17, 1)
EVENT_ROUTE = (0, 1, 0, 0, 0, 1, 1)
AUDIT_ADDRESS = (0, 0, 0, 1)  # LLLR, relative to the matched fresh Local.


def _natural(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(name + " must be a nonnegative plain integer")


@dataclass(frozen=True, slots=True)
class SReadoutLimits:
    """Experimental refusal caps, not bounds on the source computation.

    max_word_bits includes the restored deleted 1 in the event interface;
    the generic carrier helper uses it for the carrier word alone.
    """
    max_input_nodes: int = 1_000_000
    max_word_bits: int = 19_000_000
    max_queue_symbols: int = 1_000_000
    max_counters: int = 100_000
    max_output_bits: int = 1_000_000
    max_work: int = 100_000_000

    def __post_init__(self):
        _limits(self)


def _limits(limits):
    if type(limits) is not SReadoutLimits:
        raise ValueError("limits must be an exact SReadoutLimits")
    for name in SReadoutLimits.__dataclass_fields__:
        try:
            value = object.__getattribute__(limits, name)
        except AttributeError as error:
            raise ValueError("incomplete limits") from error
        _natural(value, name)


class _Budget:
    __slots__ = ("used", "limit")

    def __init__(self, limit):
        self.used, self.limit = 0, limit

    def take(self, amount=1):
        if amount > self.limit - self.used:
            raise ResourceLimit("max_work exhausted")
        self.used += amount


@dataclass(frozen=True, slots=True)
class _Graph:
    # Postorder indices; (-1,-1) denotes any exact instance of the S atom type.
    nodes: tuple[tuple[int, int], ...]
    root: int


def _snapshot(term, max_nodes, budget):
    """Validate *all* reachable syntax before matching, retaining captured edges.

    Exact type checks precede any child reads. Identity keys never call input
    equality/hash. Cached occurrence counts and all other fields are ignored.
    """
    done, active, nodes = {}, set(), []
    pending = [(term, None)]
    while pending:
        budget.take()
        node, children = pending.pop()
        kind, identity = type(node), id(node)
        if kind is not _ATOM and kind is not App:
            raise ValueError("term must contain only exact S/App nodes")
        if identity in done:
            continue
        if children is not None:
            left, right = children
            done[identity] = len(nodes)
            nodes.append((done[id(left)], done[id(right)]))
            active.remove(identity)
        elif identity in active:
            raise ValueError("term must be acyclic")
        else:
            if len(done) + len(active) >= max_nodes:
                raise ResourceLimit("max_input_nodes exhausted")
            if kind is _ATOM:
                done[identity] = len(nodes)
                nodes.append((-1, -1))
                continue
            try:
                left = object.__getattribute__(node, "left")
                right = object.__getattribute__(node, "right")
            except AttributeError as error:
                raise ValueError("application has a missing child") from error
            active.add(identity)
            pending.extend(((node, (left, right)), (right, None), (left, None)))
    return _Graph(tuple(nodes), done[id(term)]), done


class _Miss(ValueError):
    pass


@dataclass(frozen=True, slots=True)
class _Branch:
    code: int
    left: int | None
    right: int | None
    label: tuple[int, int] | None


@dataclass(frozen=True, slots=True)
class CompiledCarrierReader:
    """Factory-produced immutable, program-static grammar; no per-call cache.

    Use compile_carrier_reader(), not direct construction or object mutation.
    The public read_carrier method reimplements the mathematical grammar with
    charged visits, including arbitrary repeated Base-continuation comparisons.
    """
    _code: _Graph
    _constants: tuple[int, ...]
    _branches: tuple[_Branch, ...]
    _history_counts: tuple[int, ...]

    @property
    def code_size(self):
        return (32 + len(self._code.nodes) + len(self._branches)
                + sum(self._history_counts))

    def read_carrier(self, term, *, limits=SReadoutLimits()):
        _limits(limits)
        budget = _Budget(limits.max_work)
        graph, _ = _snapshot(term, limits.max_input_nodes, budget)
        parser = _Parser(self, graph, budget, limits.max_word_bits)
        return parser.queue(graph.root)

    def limits_for_input_nodes(self, nodes):
        """Sufficient caps for any carrier DAG of at most nodes distinct nodes."""
        return _derived_limits(nodes, self.code_size)


def compile_carrier_reader(program):
    """Experimental setup helper, separate from all run-time readout paths.

    Compiles only the fixed CTS table. The mathematical UT19 interface below
    uses its one module-level instance, never a caller's source program.
    """
    if type(program) is not cts.Program:
        raise ValueError("program must be an exact CTS Program")
    words = program.appendants
    if type(words) is not tuple or not words:
        raise ValueError("appendants must be a nonempty exact tuple")
    for word in words:
        if type(word) is not str or any(bit not in "01" for bit in word):
            raise ValueError("appendants must be plain binary strings")
    # Reuse only setup metadata. No private reference parser method is called.
    source = _compile_reference_grammar(program)
    branches, pending = [], [source._dispatch]
    while pending:
        branch = pending.pop()
        branches.append(branch)
        if branch.label is None:
            pending.extend((branch.right, branch.left))
    positions = {id(branch): index for index, branch in enumerate(branches)}
    constants = (source.act, B, PI, HALT, HALT_TAG, *LIVE, *VALUES)
    root = S
    for item in (*constants, *(branch.code for branch in branches)):
        root = App(root, item)
    # This is code construction, not an input evaluator. Its temporary guard
    # is derived from the supplied finite table, not from any simulated run.
    code_bound = 1024 * (1 + len(words) + sum(map(len, words)))
    graph, indices = _snapshot(root, code_bound, _Budget(4 * code_bound))
    dispatch = tuple(_Branch(indices[id(branch.code)],
                             positions[id(branch.left)] if branch.left else None,
                             positions[id(branch.right)] if branch.right else None,
                             branch.label) for branch in branches)
    return CompiledCarrierReader(graph, tuple(indices[id(x)] for x in constants),
                                 dispatch, tuple(map(len, words)))


class _Parser:
    def __init__(self, grammar, graph, budget, max_bits):
        self.grammar, self.graph, self.budget = grammar, graph, budget
        self.max_bits = max_bits

    def pair(self, index):
        self.budget.take()
        left, right = self.graph.nodes[index]
        if left < 0:
            raise _Miss("application required")
        return left, right

    def atom(self, index):
        self.budget.take()
        return self.graph.nodes[index][0] < 0

    def same(self, first, second, *, code=False):
        """Exact DAG structural equality, at most 2*n*m+1 charged pair pops."""
        other = self.grammar._code if code else self.graph
        pending, seen = [(first, second)], set()
        while pending:
            self.budget.take()
            a, b = pending.pop()
            if not code and a == b:
                continue
            key = a, b
            if key in seen:
                continue
            seen.add(key)
            al, ar = self.graph.nodes[a]
            bl, br = other.nodes[b]
            if al < 0 or bl < 0:
                if (al < 0) != (bl < 0):
                    return False
            else:
                pending.extend(((ar, br), (al, bl)))
        return True

    def constant(self, index, constant):
        return self.same(index, self.grammar._constants[constant], code=True)

    def arity(self, index, count):
        arguments = []
        for _ in range(count):
            index, child = self.pair(index)
            arguments.append(child)
        if not self.atom(index):
            raise _Miss("wrong S head arity")
        arguments.reverse()
        return arguments

    def has_arity(self, index, count):
        try:
            self.arity(index, count)
            return True
        except _Miss:
            return False

    def environment(self, index):
        (body,) = self.arity(index, 1)
        action, seed = self.arity(body, 2)
        if not self.constant(action, 0):
            raise _Miss("wrong compiled action table")
        (payload,) = self.arity(seed, 1)
        return payload

    def base(self, index):
        left, _retained = self.pair(index)
        outer, alpha = self.pair(left)
        applied, inner = self.pair(alpha)
        active, dormant = self.pair(applied)
        queue = self.environment(active)
        found_b, dormant_environment = self.pair(dormant)
        if not self.constant(found_b, 1):
            raise _Miss("wrong Base prefix")
        if not self.same(outer, inner):
            raise _Miss("unequal Base continuations")
        self.environment(dormant_environment)
        return queue

    def route(self, index):
        position = 0
        while True:
            self.budget.take()
            spec = self.grammar._branches[position]
            _audit, branch = self.arity(index, 2)
            if spec.label is not None:
                return spec.label, branch
            left, right = self.pair(branch)
            if self.has_arity(left, 2):
                dormant, _audit = self.pair(right)
                if not self.same(dormant, self.grammar._branches[spec.right].code, code=True):
                    raise _Miss("wrong dormant right branch")
                index, position = left, spec.left
            else:
                dormant, _audit = self.pair(left)
                if not self.same(dormant, self.grammar._branches[spec.left].code, code=True):
                    raise _Miss("wrong dormant left branch")
                index, position = right, spec.right

    def local(self, index):
        previous, continuation_audit = self.pair(index)
        earlier, seed_audit = self.pair(previous)
        halt, route = self.pair(earlier)
        halt_function, _audit = self.pair(halt)
        if not self.constant(halt_function, 3):
            _left_audit, tagged = self.arity(halt, 2)
            tag, _right_audit = self.pair(tagged)
            if not self.constant(tag, 4):
                raise _Miss("wrong halt field")
        self.arity(seed_audit, 2)
        self.pair(continuation_audit)
        (phase, bit), completed = self.route(route)
        for _ in range(self.grammar._history_counts[phase] if bit else 0):
            completed, _history = self.pair(completed)
        head, accumulator = self.pair(completed)
        if not self.constant(head, 2):
            raise _Miss("unfinished or wrong-arity append action")
        return accumulator

    def cell(self, index):
        function, payload = self.pair(index)
        for bit in (0, 1):
            if self.constant(function, 5 + bit):
                return str(bit), False, payload
        predecessor, tagged = self.arity(index, 2)
        tag, _audit = self.pair(tagged)
        for bit in (0, 1):
            if self.constant(tag, 7 + bit):
                return str(bit), True, predecessor
        raise _Miss("unrecognized queue cell")

    def queue(self, index):
        reversed_bits, inside_base = [], False
        while True:
            self.budget.take()
            if inside_base:
                if self.atom(index):
                    self.budget.take(len(reversed_bits) + 1)
                    return "".join(reversed(reversed_bits))
            else:
                try:
                    queue = self.base(index)
                except _Miss:
                    pass
                else:
                    index, inside_base = queue, True
                    continue
                try:
                    accumulator = self.local(index)
                except _Miss:
                    pass
                else:
                    index = accumulator
                    continue
            bit, consumed, index = self.cell(index)
            if not consumed:
                if len(reversed_bits) >= self.max_bits:
                    raise ResourceLimit("max_word_bits exhausted")
                self.budget.take()
                reversed_bits.append(bit)


def _event_pattern(grammar, label):
    """Compile exact fresh completed Local syntax from fixed grammar indices."""
    descriptors, interned = [], {}

    def intern(kind, left=-1, right=-1):
        key = kind, left, right
        if key not in interned:
            interned[key] = len(descriptors)
            descriptors.append(key)
        return interned[key]

    hole, atom = intern("_"), intern("S")
    literal = []
    for left, right in grammar._code.nodes:
        literal.append(atom if left < 0 else intern("A", literal[left], literal[right]))
    pending = [(0, ())]
    while pending:
        position, path = pending.pop()
        branch = grammar._branches[position]
        if branch.label == label:
            break
        if branch.label is None:
            pending.extend(((branch.right, path + ((position, 1),)),
                            (branch.left, path + ((position, 0),))))
    else:
        raise ValueError("missing event label")
    pair = lambda left, right: intern("A", left, right)
    chosen = lambda response: pair(pair(atom, hole), response)
    response = pair(literal[grammar._constants[2]], hole)
    phase, bit = label
    for _ in range(grammar._history_counts[phase] if bit else 0):
        response = pair(response, hole)
    response = chosen(response)
    for position, side in reversed(path):
        branch = grammar._branches[position]
        sibling = grammar._branches[branch.right if side == 0 else branch.left]
        dormant = pair(literal[sibling.code], hole)
        response = chosen(pair(response, dormant) if side == 0 else pair(dormant, response))
    root = pair(pair(pair(pair(literal[grammar._constants[3]], hole), response),
                     pair(pair(atom, hole), hole)), pair(hole, hole))
    # Unused literal descriptors are harmless fixed code. They do not change
    # root matching and their evaluation is explicitly charged.
    return tuple(descriptors), root, tuple(side for _, side in path)


# Input-independent grammar preparation. No lazy compilation occurs in readers.
UT19_CARRIER_READER = compile_carrier_reader(ut19.compile_cts())
_PATTERN, _PATTERN_ROOT, _ROUTE = _event_pattern(UT19_CARRIER_READER, EVENT_LABEL)
if _ROUTE != EVENT_ROUTE or UT19_CARRIER_READER._history_counts[17] != 19:
    raise AssertionError("fixed UT19 event code differs from audited F17")
FIXED_CODE_SIZE = UT19_CARRIER_READER.code_size + len(_PATTERN)


def polynomial_work_bound(input_nodes, code_size=FIXED_CODE_SIZE):
    """Conservative sufficient charged-work bound; see the all-input proof."""
    _natural(input_nodes, "input_nodes")
    _natural(code_size, "code_size")
    return 4096 * (input_nodes + 1) ** 3 * (code_size + 1) ** 2


def _derived_limits(nodes, code_size):
    _natural(nodes, "nodes")
    return SReadoutLimits(nodes, nodes + 1, nodes + 1, nodes + 1,
                         nodes + 1, polynomial_work_bound(nodes, code_size))


def limits_for_input_nodes(nodes):
    """Sufficient event caps for every exact finite DAG of at most nodes nodes.

    Thus, using an independently known node bound realizes a mathematical total
    structural reader. Smaller experimental caps can refuse, never decide halt.
    """
    return _derived_limits(nodes, FIXED_CODE_SIZE)


def _witness(graph, budget):
    states, found = [], []
    root_mask = 1 << _PATTERN_ROOT
    for left, right in graph.nodes:
        budget.take()
        flags = 0
        for index, (kind, pl, pr) in enumerate(_PATTERN):
            budget.take()
            matches = kind == "_" or (kind == "S" and left < 0)
            if kind == "A" and left >= 0:
                matches = bool((states[left] >> pl) & (states[right] >> pr) & 1)
            if matches:
                flags |= 1 << index
        states.append(flags)
        found.append(bool(flags & root_mask) or
                     (left >= 0 and (found[left] or found[right])))
    if not found[graph.root]:
        return None
    current, path = graph.root, []
    while not states[current] & root_mask:
        budget.take()
        left, right = graph.nodes[current]
        side = 0 if found[left] else 1
        path.append(side)
        current = left if side == 0 else right
    budget.take(len(path) + 1)
    return tuple(path), current


def find_ut19_event(term, *, limits=SReadoutLimits()):
    """First preorder F17 address, or None. No payload/reachability assertion."""
    _limits(limits)
    budget = _Budget(limits.max_work)
    graph, _ = _snapshot(term, limits.max_input_nodes, budget)
    result = _witness(graph, budget)
    return None if result is None else result[0]


@dataclass(frozen=True, slots=True)
class EventReadout:
    values: tuple[int, ...]
    witness: tuple[int, ...]
    input_nodes: int
    work: int


def read_ut19_event(term, *, limits=SReadoutLimits()):
    """Locate F17, decode its LLLR carrier, restore 1, read the CTS prestate.

    Raises ValueError for absent/malformed syntax, ResourceLimit for cap refusal.
    A syntactically accepted forged shell is not evidence of a source event.
    """
    _limits(limits)
    budget = _Budget(limits.max_work)
    graph, _ = _snapshot(term, limits.max_input_nodes, budget)
    found = _witness(graph, budget)
    if found is None:
        raise ValueError("no completed F17 occurrence")
    path, current = found
    for side in AUDIT_ADDRESS:
        budget.take()
        current = graph.nodes[current][side]
    if limits.max_word_bits < 1:
        raise ResourceLimit("max_word_bits exhausted")
    parser = _Parser(UT19_CARRIER_READER, graph, budget, limits.max_word_bits - 1)
    tail = parser.queue(current)
    # Reserve before copying/constructing/scanning. The fixed CTS decoder's
    # loops are linear; 1024 units per bit also cover its output and checks.
    budget.take(1024 * (len(tail) + 2))
    word = "1" + tail
    downstream = ut19_readout.ReadoutLimits(
        limits.max_queue_symbols, limits.max_word_bits,
        limits.max_counters, limits.max_output_bits)
    values = ut19_readout.read_cts_result(cts.Configuration(word, 17), limits=downstream)
    return EventReadout(values, path, len(graph.nodes), budget.used)


def read_s_event_result(term, *, limits=SReadoutLimits()):
    """Numerical-only convenience interface for read_ut19_event."""
    return read_ut19_event(term, limits=limits).values
