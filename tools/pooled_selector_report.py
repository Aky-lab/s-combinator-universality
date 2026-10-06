"""Measure bounded compile-only interning in fresh, separately traced processes.

Run with external timeout and address-space caps. Counts of reachable Python
objects, sys.getsizeof bytes, tracemalloc peaks and process RSS are distinct
observations. None estimates the memory of a 38-phase full compile.
"""
import argparse
from dataclasses import asdict, fields, is_dataclass
import gc
import hashlib
import json
from pathlib import Path
import platform
import resource
import subprocess
import sys
import time
import tracemalloc

from s_only.cts import Program
from s_only.pooled_selector import compile_with_statistics
from s_only.succinct_periodic import compile_table as unpooled_compile
from s_only.succinct_probes import _Descriptor, SuccinctProbeTable
from s_only.succinct_selector import _Fragment
from s_only.succinct_walkers import SuccinctWalkerTable

CASES = (('01',), ('1', ''), ('01', '', '01'),
         ('10', '1', '', '10'), ('01', '', '1', '01', '001'))


def reachable_values(root):
    """Traverse emitted metadata only; never a controller's source or input."""
    pending, seen = [root], set()
    while pending:
        value = pending.pop()
        if id(value) in seen:
            continue
        seen.add(id(value))
        yield value
        if type(value) is tuple:
            pending.extend(value)
        elif is_dataclass(value):
            pending.extend(getattr(value, field.name) for field in fields(value))
        elif type(value) not in (int, str, type(None)):
            raise ValueError('unexpected value in immutable controller code')


def code_sha256(root):
    """Canonical value-code digest independent of Python object identities.

    This is not the original all-transition graph digest. Exact class names,
    field order, tuple lengths and primitive values describe all emitted code;
    sharing is ignored. Walk order is explicit, with no recursive source hash.
    """
    digest, pending = hashlib.sha256(), [root]
    while pending:
        value = pending.pop()
        if type(value) is tuple:
            token = ['tuple', len(value)]
            pending.extend(reversed(value))
        elif is_dataclass(value):
            names = [field.name for field in fields(value)]
            token = ['record', type(value).__module__, type(value).__name__, names]
            pending.extend(getattr(value, name) for name in reversed(names))
        elif type(value) in (int, str, type(None)):
            token = [type(value).__name__, value]
        else:
            raise ValueError('unexpected value in immutable controller code')
        digest.update(json.dumps(token, separators=(',', ':'), ensure_ascii=True).encode('ascii'))
        digest.update(b'\n')
    return digest.hexdigest()


def probe_reference_slots(table):
    slots = 0
    for block in table.blocks:
        if type(block) is not _Fragment:
            continue
        fragment = block.table
        if type(fragment) is SuccinctWalkerTable:
            fragment = fragment.probe
        slots += 1 if type(fragment) is SuccinctProbeTable else len(fragment.patterns)
    return slots


def worker(case, pooled):
    program = Program(CASES[case])
    gc.collect()
    tracemalloc.start()
    start = time.monotonic()
    if pooled:
        table, stats = compile_with_statistics(program, max_compile_seconds=30)
    else:
        table, stats = unpooled_compile(program, max_compile_seconds=30), None
    seconds = time.monotonic() - start
    # The inherited builder/reservations facade forms a compile-only cycle.
    # Collect it before measuring retained allocations; its construction still
    # contributes to the traced peak and process high-water mark.
    gc.collect()
    current, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    # Sample process RSS before measurement traversal/hash adds its own work.
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    # Linux reports KiB; macOS reports bytes.
    rss_bytes = rss if sys.platform == 'darwin' else rss * 1024
    objects = list(reachable_values(table))
    descriptors = [value for value in objects if type(value) is _Descriptor]
    probes = [value for value in objects if type(value) is SuccinctProbeTable]
    return {
        'mode': 'pooled' if pooled else 'unpooled',
        'state_count': table.state_count,
        'start': table.start,
        'intervals': len(table.blocks),
        'referenced_metadata_slots': table.metadata_records,
        'probe_reference_slots': probe_reference_slots(table),
        'reachable_objects': len(objects),
        'reachable_descriptors': len(descriptors),
        'reachable_probe_tables': len(probes),
        'equality_distinct_probe_values': len(set(probes)),
        'reachable_sys_getsizeof_bytes': sum(sys.getsizeof(value) for value in objects),
        'reachable_descriptor_sys_getsizeof_bytes': sum(map(sys.getsizeof, descriptors)),
        'reachable_probe_header_sys_getsizeof_bytes': sum(map(sys.getsizeof, probes)),
        'compile_tracemalloc_current_bytes': current,
        'compile_tracemalloc_peak_bytes': peak,
        'compile_peak_minus_current_bytes': peak - current,
        'process_peak_rss_bytes_through_compile': rss_bytes,
        'compile_seconds_under_tracemalloc': seconds,
        'pool': asdict(stats) if stats is not None else None,
        'pool_peak_entries': stats.peak_pool_entries if stats is not None else None,
        'pool_descriptor_entries_absent_from_final_code':
            stats.descriptor_entries - len(descriptors) if stats is not None else None,
        'pool_probe_entries_absent_from_final_code':
            stats.probe_entries - len(probes) if stats is not None else None,
        'immutable_value_code_sha256': code_sha256(table),
    }


def report(*, max_seconds=160):
    if type(max_seconds) not in (int, float) or not 0 < max_seconds <= 160:
        raise ValueError('max_seconds must be positive and at most 160')
    deadline = time.monotonic() + max_seconds
    records = []
    for case, words in enumerate(CASES):
        samples = []
        for mode in ('unpooled', 'pooled'):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError('measurement deadline reached')
            result = subprocess.run(
                [sys.executable, '-m', 'tools.pooled_selector_report', '--worker', str(case), mode],
                check=True, text=True, capture_output=True, timeout=remaining)
            samples.append(json.loads(result.stdout))
        before, after = samples
        for name in ('state_count', 'start', 'intervals', 'referenced_metadata_slots',
                     'probe_reference_slots', 'equality_distinct_probe_values',
                     'immutable_value_code_sha256'):
            if before[name] != after[name]:
                raise AssertionError(f'pooled and unpooled {name} differ')
        records.append({'appendants': list(words), 'unpooled': before, 'pooled': after})
    return {
        'schema': 's-only-pooled-selector-v1',
        'python': platform.python_version(),
        'platform': platform.platform(),
        'scope': 'periods 1 through 5; at most 8 appendant bits; no UT19 full compile',
        'method': 'fresh process for every mode/program; tracemalloc covers compilation and '
                  'post-compile garbage collection; current is sampled after collection',
        'identity_caveat': 'sys.getsizeof sums each reachable object once, including scalars; not RSS',
        'peak_caveat': 'traced peak-minus-current is an allocation excess, not exact temporary bytes; '
                       'RSS includes the interpreter, imports and tracemalloc overhead',
        'pool_caveat': 'pool entries are retained until compilation ends, including unreachable values; '
                       'candidate requests are allocation attempts, not unique objects or peak temporaries',
        'equivalence': 'canonical immutable value-code hashes equal; primitive-entry and native-microtick '
                       'checks are in tests/test_pooled_selector.py',
        'hard_limit_command': "timeout 180s sh -c 'ulimit -v 524288; exec python -m "
                              "tools.pooled_selector_report --output /tmp/pooled-selector.json'",
        'programs': records,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--max-seconds', type=float, default=160)
    parser.add_argument('--worker', nargs=2, metavar=('CASE', 'MODE'), help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    if args.worker:
        case, mode = args.worker
        if not case.isdigit() or not 0 <= int(case) < len(CASES) or mode not in ('pooled', 'unpooled'):
            parser.error('invalid worker arguments')
        result = worker(int(case), mode == 'pooled')
    else:
        result = report(max_seconds=args.max_seconds)
    serialized = json.dumps(result, sort_keys=True, indent=2) + '\n'
    if args.output:
        args.output.write_text(serialized)
    else:
        print(serialized, end='')
    return result


if __name__ == '__main__':
    main()
