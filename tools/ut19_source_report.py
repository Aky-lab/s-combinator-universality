"""Deterministic source-only UT19 fixtures; no native S construction or run.

Recommended process guard (Linux):
    (ulimit -v 1048576; timeout 180s python -m tools.ut19_source_report \
        --output results/ut19_source.json)

All queues, steps, encoder vectors and stored recurrence configurations have
explicit bounds. A resource failure raises; it is never reported as halting.
"""
import argparse
from dataclasses import asdict
from hashlib import sha256
import json
from pathlib import Path

from s_only import alternating_tag as tag
from s_only import cts, ut19
from s_only.ut19_readout import ReadoutLimits, read_cts_result, read_tag_result

FIXTURES = ("+1", "-1", "-1 -1")
PROVENANCE = {
    "ut19": "https://esolangs.org/w/index.php?title=UT19&oldid=154545",
    "brainpocalypse_ii": "https://esolangs.org/w/index.php?title=Brainpocalypse_II&oldid=172507",
    "license": "CC0 wiki construction; independent implementation; external Perl compiler not used",
}


def _json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _digest(text):
    return sha256(text.encode("ascii")).hexdigest()


def _tag_object(state):
    return {"queue": [x + 1 for x in state.queue], "phase": state.phase}


def _tag_digest(state):
    return _digest(_json(_tag_object(state)))


def _cts_digest(state):
    return _digest(_json({"word": state.word, "phase": state.phase}))


def _source_run(program, *, max_steps, max_counters, max_counter_value):
    state = ut19.initial_source(program, max_counters=max_counters)
    seen, steps, restarts = {}, 0, 0
    while True:
        if state.pc == len(program.commands):
            outcome, recurrence = "fallthrough_halt", None
            break
        if state in seen:
            first = seen[state]
            outcome = "exact_recurrence"
            recurrence = {"first_step": first, "repeated_step": steps,
                          "period_steps": steps - first,
                          "configuration": asdict(state)}
            break
        if steps >= max_steps:
            raise cts.ResourceLimit("BP2 fixture exceeded max_source_steps")
        seen[state] = steps
        command = program.commands[state.pc]
        restarts += int(command.delta == -1 and state.counters[command.counter - 1] == 0)
        state = ut19.source_step(program, state, max_counters=max_counters,
                                 max_counter_value=max_counter_value)
        steps += 1
    return {"outcome": outcome, "commands_executed": steps, "restarts": restarts,
            "final_configuration": asdict(state), "recurrence": recurrence,
            "counter_values_are_independently_evaluated_not_decoded_from_ut19": True}


def _tag_run(encoded, program, *, max_tag_steps, max_cts_steps,
             max_queue_symbols, max_word_bits, max_seen_symbols, readout_limits):
    source = tag.Machine(ut19.TAG_PROGRAM,
                         encoded.tag_configuration(max_queue_symbols=max_queue_symbols),
                         max_steps=max_tag_steps, max_queue_symbols=max_queue_symbols)
    binary = cts.Machine(program, encoded.cts_configuration(max_word_bits=max_word_bits),
                         max_steps=max_cts_steps, max_word_bits=max_word_bits)
    seen = {}
    seen_symbols = 0
    boundaries = 0
    event_checks = 0
    # A digest per full source boundary permits reproducible prefix/cycle trace
    # fingerprints without retaining a second copy of all queue configurations.
    boundary_digests = []

    def check_event():
        nonlocal event_checks
        event_checks += 1
        # At all other phases the predicate is false without reading the queue.
        return (binary.phase == ut19.HALT_INDEX
                and tag.selected_cts_event(ut19.TAG_PROGRAM, binary.snapshot(), ut19.HALT_INDEX))

    while True:
        state = source.snapshot()
        actual = binary.snapshot()
        expected = tag.encode_configuration(ut19.TAG_PROGRAM, state,
                                             max_word_bits=max_word_bits)
        if actual != expected:
            raise AssertionError("full one-hot boundary state mismatch")
        boundaries += 1
        if ut19.selected_source_event(state):
            # Preserve the designated CTS PRE-transition state: consume the 17
            # leading zeros, not the selecting one or its appendant.
            for _ in range(ut19.HALT_INDEX):
                if check_event():
                    raise AssertionError("unexpected earlier CTS event")
                binary.tick()
            if not check_event():
                raise AssertionError("missing selected-symbol CTS event")
            final = binary.snapshot()
            end = {
                "outcome": "designated_event", "tag_completed_steps": source.steps,
                "cts_completed_steps": binary.steps, "cts_logged_step_if_executed": binary.steps + 1,
                "tag_phase": state.phase, "tag_head_label": state.queue[0] + 1,
                "tag_configuration": _tag_object(state),
                "tag_block_boundary_cts_step": 19 * source.steps,
                "cts_phase": final.phase, "cts_head_bit": final.word[0],
                "tag_configuration_sha256": _tag_digest(state),
                "cts_configuration_sha256": _cts_digest(final),
                "cts_word_bits": len(final.word),
                "earlier_cts_event_count": 0,
                "observed_before_transition": True,
                "decoded_tag_counters": read_tag_result(state, limits=readout_limits),
                "decoded_cts_counters": read_cts_result(final, limits=readout_limits),
            }
            recurrence = None
            break
        if not state.queue:
            raise AssertionError("unexpected empty queue before event or recurrence")
        if state in seen:
            first = seen[state]
            # Dictionary equality compares the complete immutable queue AND phase,
            # not a hash alone. Equal tag states have exactly equal CTS encodings.
            first_binary = tag.encode_configuration(ut19.TAG_PROGRAM, state,
                                                     max_word_bits=max_word_bits)
            if actual != first_binary:
                raise AssertionError("repeated CTS configuration differs")
            period = source.steps - first
            recurrence = {
                "first_tag_step": first, "repeated_tag_step": source.steps,
                "period_tag_steps": period,
                "first_cts_step": 19 * first, "repeated_cts_step": binary.steps,
                "period_cts_steps": 19 * period,
                "configuration": _tag_object(state),
                "first_tag_configuration_sha256": _tag_digest(state),
                "repeated_tag_configuration_sha256": _tag_digest(state),
                "first_cts_configuration_sha256": _cts_digest(first_binary),
                "repeated_cts_configuration_sha256": _cts_digest(actual),
                "exact_full_state_equality_checked": True,
                "prefix_tag_prestate_checks": first,
                "cycle_tag_prestate_checks": period,
                "prefix_cts_prestate_checks": 19 * first,
                "cycle_cts_prestate_checks": 19 * period,
                "prefix_selected_event_count": 0, "cycle_selected_event_count": 0,
                "prefix_nonempty": True, "cycle_nonempty": True,
                "prefix_boundary_digest_sha256": sha256(b"".join(boundary_digests[:first])).hexdigest(),
                "cycle_boundary_digest_sha256": sha256(b"".join(boundary_digests[first:])).hexdigest(),
                "conclusion": "This deterministic fixture runs forever without the designated event or empty queue.",
            }
            end = {"outcome": "exact_event_free_recurrence", "tag_completed_steps": source.steps,
                   "cts_completed_steps": binary.steps, "cts_phase": actual.phase,
                   "cts_word_bits": len(actual.word), "observed_before_transition": True}
            break
        if source.steps >= max_tag_steps:
            raise cts.ResourceLimit("UT19 fixture exceeded max_tag_steps")
        if seen_symbols + len(state.queue) > max_seen_symbols:
            raise cts.ResourceLimit("recurrence history exceeds max_seen_symbols")
        seen_symbols += len(state.queue)
        seen[state] = source.steps
        boundary_digests.append(bytes.fromhex(_tag_digest(state)))
        # Check every intermediate CTS prestate. A skipped 18 is harmless and
        # is intentionally not conflated with a producing 18.
        for _ in range(19):
            if check_event():
                raise AssertionError("spurious CTS event in unselected source block")
            binary.tick()
        source.tick()
    return {
        "end": end, "recurrence": recurrence,
        "full_boundaries_checked": boundaries,
        "cts_prestates_checked_for_event": event_checks,
        "peak_tag_queue_symbols": source.peak_queue_symbols,
        "peak_cts_queue_bits": binary.peak_word_bits,
        "stored_recurrence_symbols": seen_symbols,
    }


def report(*, max_source_steps=128, max_counter_value=1024,
           max_tag_steps=5000, max_cts_steps=100_000,
           max_queue_symbols=1000, max_word_bits=20_000,
           max_seen_symbols=2_000_000, encoding_limits=ut19.EncodingLimits()):
    bounds = {
        "max_source_steps": max_source_steps, "max_counter_value": max_counter_value,
        "max_tag_steps": max_tag_steps, "max_cts_steps": max_cts_steps,
        "max_queue_symbols": max_queue_symbols, "max_word_bits": max_word_bits,
        "max_seen_symbols": max_seen_symbols,
    }
    for name, value in bounds.items():
        if type(value) is not int or value < 0:
            raise ValueError(f"{name} must be a nonnegative integer")
    if type(encoding_limits) is not ut19.EncodingLimits:
        raise ValueError("encoding_limits must be EncodingLimits")
    # Preflight every fixture's materialized seed before any interpreter runs.
    encodings = tuple(ut19.encode_source(ut19.parse_source(text), limits=encoding_limits)
                      for text in FIXTURES)
    for encoded in encodings:
        if encoded.seed_symbols > max_queue_symbols or encoded.seed_bits > max_word_bits:
            raise cts.ResourceLimit("fixture seed exceeds interpreter queue limits")
    program = ut19.compile_cts()
    readout_limits = ReadoutLimits(
        max_queue_symbols=max_queue_symbols, max_word_bits=max_word_bits,
        max_counters=encoding_limits.max_counters,
        max_output_bits=encoding_limits.max_counters * max(1, max_counter_value.bit_length()))
    fixtures = []
    for encoded in encodings:
        seed = encoded.cts_configuration(max_word_bits=max_word_bits)
        fixtures.append({
            "source_program": str(encoded.source),
            "source_execution": _source_run(encoded.source, max_steps=max_source_steps,
                                             max_counters=encoding_limits.max_counters,
                                             max_counter_value=max_counter_value),
            "encoding": {"variant": "compact_unpadded",
                         "source_counters": encoded.source.counter_count,
                         "expanded_commands": encoded.expanded_commands,
                         "memory_blocks": [{"position": b.position,
                                            "desired_widths": "".join(map(str, b.desired)),
                                            "initial_bits": "".join(map(str, b.initial))}
                                           for b in encoded.blocks],
                         "seed_symbols": encoded.seed_symbols, "seed_bits": encoded.seed_bits,
                         "seed_bit_sha256": _digest(seed.word)},
            "tag_and_cts_execution": _tag_run(encoded, program, max_tag_steps=max_tag_steps,
                                               max_cts_steps=max_cts_steps,
                                               max_queue_symbols=max_queue_symbols,
                                               max_word_bits=max_word_bits,
                                               max_seen_symbols=max_seen_symbols,
                                               readout_limits=readout_limits),
        })
    for fixture in fixtures:
        end = fixture['tag_and_cts_execution']['end']
        if end['outcome'] == 'designated_event':
            source = fixture['source_execution']
            if (source['outcome'] != 'fallthrough_halt' or
                    end['decoded_tag_counters'] != source['final_configuration']['counters'] or
                    end['decoded_cts_counters'] != source['final_configuration']['counters']):
                raise AssertionError('structural result differs from the independent source result')
    return {"schema": "ut19-source-fixtures-v1", "provenance": PROVENANCE,
            "scope": "bounded BP2, alternating-tag and ordinary CTS fixtures only",
            "source_simulation_argument": {
                "path": "docs/ut19-simulation-invariants.md",
                "kind": "independently reviewed written proof",
                "scope": "nonempty dense-label BP2 programs from all-zero counters; first selected-18 event and result grammar"},
            "result_counter_decoder_implemented": True,
            "cleanup_padding_included": False,
            "native_s_terms_constructed": False, "native_s_reductions_performed": 0,
            "bounds": bounds, "encoding_limits": asdict(encoding_limits),
            "readout_limits": asdict(readout_limits),
            "fixed_program": {"tag_productions_one_based": ut19.UT19_PRODUCTIONS,
                              "cts_appendants": program.appendants,
                              "phases": len(program.appendants),
                              "nonempty_appendants": sum(bool(x) for x in program.appendants),
                              "appendant_bits": sum(map(len, program.appendants)),
                              "appendant_ones": sum(x.count("1") for x in program.appendants),
                              "maximum_appendant_bits": max(map(len, program.appendants))},
            "digest_conventions": {
                "seed": "SHA256 of ASCII binary word, no newline",
                "configuration": "SHA256 of sorted-key compact ASCII JSON; tag labels are 1-based",
                "boundary_trace": "SHA256 of concatenated raw tag-configuration SHA256 digests, one per prestate; endpoint excluded",
            },
            "fixtures": fixtures}


def generate(output: Path, **kwargs):
    result = report(**kwargs)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--max-tag-steps", type=int, default=5000)
    parser.add_argument("--max-cts-steps", type=int, default=100_000)
    parser.add_argument("--max-queue-symbols", type=int, default=1000)
    parser.add_argument("--max-word-bits", type=int, default=20_000)
    parser.add_argument("--max-seen-symbols", type=int, default=2_000_000)
    args = parser.parse_args(argv)
    try:
        result = report(max_tag_steps=args.max_tag_steps, max_cts_steps=args.max_cts_steps,
                        max_queue_symbols=args.max_queue_symbols, max_word_bits=args.max_word_bits,
                        max_seen_symbols=args.max_seen_symbols)
        rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if args.output is None:
            print(rendered, end="")
        else:
            args.output.write_text(rendered, encoding="utf-8")
    except (ValueError, cts.ResourceLimit, OSError) as error:
        parser.error(str(error))
    return result


if __name__ == "__main__":
    main()
