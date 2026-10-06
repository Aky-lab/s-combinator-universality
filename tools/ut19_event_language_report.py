"""Bounded syntax-only UT19 F17 tree-language check, not a halt observer proof.

Run with a hard process guard:
    (ulimit -v 1048576; timeout 180s python -m tools.ut19_event_language_report \
        --output /tmp/ut19-event-language.json)

The mathematical S constructors used through existing modules are attributed
to Cinematic Strawberry, pinned commit 85a867988442fc423279341200f81634a1e65582;
the MIT notice remains in third_party/cinematic-strawberry-MIT.txt. The UT19
table is the CC0 wiki construction. This report executes no downloaded code.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from s_only import encoding, ut19
from s_only.pattern_automaton import compile_pattern, evaluate
from s_only.program_selector_parts.patterns import PatternFamily
from s_only.probes import HOLE, LITERAL_S
from s_only.reduction import contract_at
from s_only.terms import App, S, nodes


LABEL = (17, 1)
ROUTE = (0, 1, 0, 0, 0, 1, 1)
FIRST_ADDRESSES = ("0", "0", "01", "", "0", "", "10", "10")
PROVENANCE = {
    "constructors_commit": "85a867988442fc423279341200f81634a1e65582",
    "constructors_license_notice": "third_party/cinematic-strawberry-MIT.txt",
    "ut19_table": "https://esolangs.org/w/index.php?title=UT19&oldid=154545",
    "ut19_license": "CC0",
}


def _literal(term):
    """Independent iterative literal transcription; no pattern-family helper."""
    done, pending = {}, [(term, False)]
    while pending:
        node, exit_node = pending.pop()
        key = id(node)
        if key in done:
            continue
        if node is S:
            done[key] = LITERAL_S
        elif type(node) is not App:
            raise ValueError("invalid static code")
        elif exit_node:
            done[key] = done[id(node.left)], done[id(node.right)]
        else:
            pending.extend(((node, True), (node.right, False), (node.left, False)))
    return done[id(term)]


def _same_patterns(first, second):
    """Compare two fixed pattern DAGs independently of the automaton compiler."""
    seen, pending = set(), [(first, second)]
    while pending:
        a, b = pending.pop()
        key = id(a), id(b)
        if key in seen:
            continue
        seen.add(key)
        if type(a) is str or type(b) is str:
            if type(a) is not str or type(b) is not str or a != b:
                return False
        else:
            if type(a) is not tuple or type(b) is not tuple or len(a) != 2 or len(b) != 2:
                return False
            pending.extend(((a[0], b[0]), (a[1], b[1])))
    return True


def build_event_pattern():
    """Reconstruct the exact audited route, then compare its labelled record."""
    family = PatternFamily(ut19.compile_cts(), required_period=None)
    if family.program.appendants[17] != "0" * 17 + "10":
        raise AssertionError("unexpected event appendant")
    spec, siblings = family.dispatch, []
    for side in ROUTE:
        if spec.label is not None:
            raise AssertionError("route reaches a leaf too early")
        siblings.append(spec.right.code if side == 0 else spec.left.code)
        spec = spec.left if side == 0 else spec.right
    if spec.label != LABEL:
        raise AssertionError("route does not identify label (17,1)")

    action = (_literal(encoding.PI), HOLE)
    for _ in range(19):
        action = action, HOLE
    chosen = lambda response: ((LITERAL_S, HOLE), response)
    response = chosen(action)
    for side, sibling in reversed(tuple(zip(ROUTE, siblings))):
        dormant = _literal(sibling), HOLE
        response = chosen((response, dormant) if side == 0 else (dormant, response))
    fresh = ((((_literal(encoding.HALT), HOLE), response),
              ((LITERAL_S, HOLE), HOLE)), (HOLE, HOLE))

    records = tuple(record for record in family.dispatch_records() if record[2] == LABEL)
    if len(records) != 1 or records[0][1] != ROUTE:
        raise AssertionError("labelled dispatch record is not unique at the audited route")
    if not _same_patterns(fresh, family.local_pattern("fresh", records[0][0])):
        raise AssertionError("independent F17 skeleton differs from dispatch_records")
    return family, fresh


def _instantiate(pattern):
    """Give each wildcard S; this is fabricated syntax, never a reachable claim."""
    done, pending = {}, [(pattern, False)]
    while pending:
        node, exit_node = pending.pop()
        key = id(node)
        if key in done:
            continue
        if type(node) is str:
            done[key] = S
        elif exit_node:
            done[key] = App(done[id(node[0])], done[id(node[1])])
        else:
            pending.extend(((node, True), (node[1], False), (node[0], False)))
    return done[id(pattern)]


def _shape(term):
    done, pending = {}, [(term, False)]
    while pending:
        node, exit_node = pending.pop()
        key = id(node)
        if key in done:
            continue
        if node is S:
            done[key] = 0
        elif exit_node:
            done[key] = done[id(node.left)] + 1
        else:
            pending.extend(((node, True), (node.right, False), (node.left, False)))
    return {"distinct_nodes": len(done), "expanded_nodes": nodes(term),
            "maximum_head_arity": max(done.values())}


def _same_terms(first, second):
    seen, pending = set(), [(first, second)]
    while pending:
        a, b = pending.pop()
        key = id(a), id(b)
        if key in seen:
            continue
        seen.add(key)
        if a is S or b is S:
            if a is not b:
                return False
        elif type(a) is App and type(b) is App:
            pending.extend(((a.left, b.left), (a.right, b.right)))
        else:
            return False
    return True


def _checked_contract(term, address):
    focus, context = term, []
    for side in address:
        if type(focus) is not App:
            raise AssertionError("recorded address leaves the tree")
        context.append((focus, side))
        focus = focus.left if side == "0" else focus.right
    if (type(focus) is not App or type(focus.left) is not App
            or type(focus.left.left) is not App or focus.left.left.left is not S):
        raise AssertionError("recorded address is not a native S redex")
    x, y, z = focus.left.left.right, focus.left.right, focus.right
    expected = App(App(x, z), App(y, z))
    for parent, side in reversed(context):
        expected = App(expected, parent.right) if side == "0" else App(parent.left, expected)
    actual = contract_at(term, tuple(map(int, address)))
    if not _same_terms(actual, expected):
        raise AssertionError("native contraction differs from independent local rewrite")
    return actual


def make_report(replay_path=None):
    family, pattern = build_event_pattern()
    automaton = compile_pattern(pattern, max_descriptors=10_000,
                                max_pattern_nodes=100_000, max_seconds=10)
    fabricated = _instantiate(pattern)
    fabricated_state = evaluate(automaton, fabricated, max_term_nodes=100_000, max_seconds=10)
    if not automaton.matches_root(fabricated_state):
        raise AssertionError("fabricated positive does not match")
    if automaton.accepts(evaluate(automaton, S)):
        raise AssertionError("atomic negative unexpectedly matches")

    encoded = ut19.encode_source(ut19.parse_source("+1"))
    word = encoded.cts_configuration(max_word_bits=1710).word
    digest = sha256(word.encode("ascii")).hexdigest()
    term = family.compiled.encode(word)
    samples = []

    def sample(step):
        state = evaluate(automaton, term, max_term_nodes=100_000, max_seconds=10)
        samples.append({"native_step": step, **_shape(term),
                        "root_match": automaton.matches_root(state),
                        "descendant_match": automaton.accepts(state)})

    sample(0)
    if samples[0]["maximum_head_arity"] > 4 or samples[0]["descendant_match"]:
        raise AssertionError("initial arity exclusion failed")
    replay = None
    if replay_path is not None:
        with Path(replay_path).open("rb") as stream:
            raw = stream.read(1_048_577)
        if len(raw) > 1_048_576:
            raise ValueError("replay report exceeds one MiB")
        source = json.loads(raw)
        if source.get("schema") != "ut19-native-bounded-attempt-v1":
            raise ValueError("unexpected replay schema")
        records = source.get("records")
        if type(records) is not list or len(records) != len(FIRST_ADDRESSES):
            raise ValueError("only the recorded first eight contractions are supported")
        if source.get("seed_sha256") != digest:
            raise ValueError("recorded source seed differs from +1")
        for step, (record, address) in enumerate(zip(records, FIRST_ADDRESSES), 1):
            if record.get("native_step") != step or record.get("address") != address:
                raise ValueError("unexpected contraction record")
            term = _checked_contract(term, address)
            if nodes(term) != record.get("expanded_nodes"):
                raise AssertionError("replayed occurrence-node count differs")
            sample(step)
        replay = {"input_sha256": sha256(raw).hexdigest(), "addresses": FIRST_ADDRESSES,
                  "native_contractions_replayed": 8, "selector_reexecuted": False,
                  "reported_selector_state_count": source.get("state_count")}
    return {
        "schema": "ut19-event-language-v1", "provenance": PROVENANCE,
        "scope": "Syntax membership only; no source-event or reachability theorem.",
        "event_label": LABEL, "route": "".join(map(str, ROUTE)),
        "status": "fresh", "history_arguments": 19,
        "independent_dispatch_record_equality": True,
        "automaton": {"canonical_subpatterns": len(automaton.nodes),
                      "state_bits": automaton.state_bits,
                      "state_count_bound": "2^" + str(automaton.state_bits),
                      "state_space_materialized": False, "minimality_claim": False},
        "fabricated_positive": {"root_match": True,
                                "descendant_match": automaton.accepts(fabricated_state)},
        "atomic_negative": {"descendant_match": False},
        "seed": {"source": "+1", "bits": len(word), "sha256": digest},
        "samples": samples, "replay": replay,
        "bounds": {"max_descriptors": 10_000, "max_pattern_nodes": 100_000,
                   "max_term_nodes_per_sample": 100_000, "max_seconds_per_operation": 10},
        "remaining_obligation": "Generated-occurrence provenance and source-event coverage.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", type=Path,
                        help="Optional first-eight bounded native-attempt JSON report")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = json.dumps(make_report(args.replay), indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(report, end="")
    else:
        args.output.write_text(report)


if __name__ == "__main__":
    main()
