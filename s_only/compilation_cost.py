"""Static allocation costs for the current literal-inlining CTS controller.

These are counts of emitted six-observation control states, not runtime ticks,
term nodes, reachable/minimized states, or memory bytes. The calculation reads
only source words. It never builds encoded terms, patterns, or controller tables.

The row construction is independently transcribed from Cinematic Strawberry,
commit 85a867988442fc423279341200f81634a1e65582. The allocation analysis here is
an independent derivation for this repository's Python implementation.
"""
from __future__ import annotations

from dataclasses import dataclass

from .cts import Program


def literal_matcher_states(node_count: int) -> int:
    """Exact nonterminal matcher allocation for a closed S tree of this size.

    W(_) = 0, W(S) = 1, W((a,b)) = 6 + W(a) + W(b). A closed full binary
    tree has (n-1)/2 applications and (n+1)/2 S leaves, even with DAG sharing.
    """
    if type(node_count) is not int or node_count < 1 or node_count % 2 != 1:
        raise ValueError("node_count must be a positive odd integer")
    return (7 * node_count - 5) // 2


def dispatcher_leaf_depths(leaf_count: int) -> tuple[int, ...]:
    """Leaf depths for adjacent pairing with odd carry, without code trees.

    At an internal subtree with n leaves, split after the largest power of two
    strictly below n. This is independent of the encoder's level-wise pairing.
    Iterative traversal visits 2*n-1 intervals, using O(n) output and O(log n)
    auxiliary stack entries. Leaves stay in occurrence order, including repeats.
    """
    if type(leaf_count) is not int or leaf_count < 1:
        raise ValueError("leaf_count must be a positive integer")
    depths = [0] * leaf_count
    pending = [(0, leaf_count, 0)]
    while pending:
        start, count, depth = pending.pop()
        if count == 1:
            depths[start] = depth
        else:
            split = 1 << ((count - 1).bit_length() - 1)
            pending.extend(((start + split, count - split, depth + 1),
                            (start, split, depth + 1)))
    return tuple(depths)


@dataclass(frozen=True, slots=True)
class PhaseCost:
    """One phase's bit-one action; its bit-zero action has no selected rows."""
    phase: int
    appendant_bits: int
    appendant_ones: int
    one_position_sum: int
    route_depth: int
    selected_rows: int
    dormant_literal_matcher_states_per_row: int
    dormant_literal_state_lower_bound: int
    selected_action_matcher_states: int
    selected_action_address_states: int
    selected_action_embedded_states: int


@dataclass(frozen=True, slots=True)
class CompilationCost:
    phase_count: int
    total_appendant_bits: int
    total_appendant_ones: int
    unique_appendant_count: int
    nonempty_appendant_count: int
    max_appendant_bits: int
    dispatcher_nodes: int
    dispatcher_matcher_states: int
    selected_action_rows: int
    dormant_literal_state_lower_bound: int
    selected_action_matcher_states: int
    selected_action_address_states: int
    selected_action_embedded_states: int
    phases: tuple[PhaseCost, ...]


def compilation_cost(program: Program) -> CompilationCost:
    """Linear formula/source scan, plus expected-linear distinct-word hashing.

    ``selected_action_embedded_states`` is the exact number added by the one
    ``builder.rows(p.selected_action_rows(), ...)`` in ``compile_endpoint``.
    It is consequently a lower bound on a successfully materialized whole
    unquotiented controller. ``dormant_literal_state_lower_bound`` counts only
    dormant sibling-code matchers inside that component, discarding other work.

    Defaults, explicit budgets, or host limits can abort compilation before
    allocating these counts. No whole graph or post-quotient size is predicted.
    Formula evaluation uses O(p+M) source inspections/arithmetic operations.
    Distinct-word counting adds expected O(p+M) hashing work. Arbitrary-
    precision integer bit costs are additional.
    """
    if not isinstance(program, Program):
        raise TypeError("program must be s_only.cts.Program")
    words = program.appendants
    period = len(words)
    bits = sum(map(len, words))
    ones = sum(word.count("1") for word in words)
    dispatcher_nodes = 32 * period - 7 + 20 * bits + 2 * ones
    dispatcher_cost = literal_matcher_states(dispatcher_nodes)
    depths = dispatcher_leaf_depths(2 * period)
    phases = []
    for phase, word in enumerate(words):
        m, o = len(word), word.count("1")
        weighted_ones = sum(index for index, bit in enumerate(word, 1) if bit == "1")
        depth = depths[2 * phase + 1]
        leaf_cost = literal_matcher_states(9 + 20 * m + 2 * o)
        siblings = dispatcher_cost - leaf_cost - 27 * depth
        row_count = 2 * m
        dormant = row_count * siblings
        # Fresh Local contributes 72; terminal chosen contributes 13; each
        # route ancestor contributes 25 plus its dormant sibling literal.
        # Summed live responses contribute 76*m^2 + 105*m + 14*weighted_ones.
        matcher = dormant + 76 * m * m + 275 * m + 50 * m * depth + 14 * weighted_ones
        # Base address length is 4+2*depth; history adds m*(m-1) in total.
        addresses = m * m + 7 * m + 4 * m * depth
        phases.append(PhaseCost(phase, m, o, weighted_ones, depth, row_count,
                                siblings, dormant, matcher, addresses,
                                matcher + addresses))
    return CompilationCost(
        period, bits, ones, len(set(words)), sum(bool(word) for word in words),
        max(map(len, words)), dispatcher_nodes, dispatcher_cost, 2 * bits,
        sum(item.dormant_literal_state_lower_bound for item in phases),
        sum(item.selected_action_matcher_states for item in phases),
        sum(item.selected_action_address_states for item in phases),
        sum(item.selected_action_embedded_states for item in phases), tuple(phases))
