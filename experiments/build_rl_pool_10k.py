"""Select unchanged pool rows using static complexity and current sampler checks.

Aggregate target-hidden evaluation complexity informed the difficulty policy.
No evaluation verdicts, target assertions, per-test matching, or SFT answers
are used for selection. Difficulty is a static proxy, not measured policy
success probability.
"""
import argparse
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import random
import re
import signal
import statistics
import time

import pyarrow.parquet as pq
from rl_pipeline.common.program import parse_program, strip_postcondition, _match_paren
from rl_pipeline.sampler.example_sampler import ExampleSampler, NEGATIVE_SCHEMA_VERSION

TOKEN = re.compile(r'[A-Za-z_]\w*|0[xX][0-9a-fA-F]+|\d+|==>|==|!=|<=|>=|&&|\|\||\+\+|--|[^\s]')
KEYWORDS = set('int void long short unsigned signed char const return while if else for do break continue sizeof requires assume assert'.split())


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def family(source, constants=False):
    # Preserve all operators, control flow, and contract content.
    mapping = {}
    out = []
    for token in TOKEN.findall(source):
        if re.fullmatch(r'(unknown|nondet)\d*|__VERIFIER_nondet_\w*', token):
            token = 'NONDET'
        elif re.fullmatch(r'[A-Za-z_]\w*', token) and token not in KEYWORDS:
            token = mapping.setdefault(token, f'v{len(mapping)}')
        elif constants and re.fullmatch(r'\d+|0[xX][0-9a-fA-F]+', token) and token not in ('0', '1'):
            token = 'NUM'
        out.append(token)
    return digest(' '.join(out))


def source_of(row):
    return next(t['content'] for t in row['prompt'] if t['role'] == 'user').split('Program:\n', 1)[1]


def inspect_source(source):
    p = parse_program(source)
    if len(p.loops) != 1:
        return None, 'not_single_loop'
    if strip_postcondition(source).strip() != source.strip():
        return None, 'visible_target'
    b = p.loops[0].body
    variables = len(p.pre_vars)
    branches = len(re.findall(r'\bif\s*\(', b))
    statements = b.count(';')
    assignments = len(re.findall(r'(?<![<>=!])=(?!=)|\+\+|--|[+*/%-]=', b))
    active_variables = len(set(p.pre_vars) & set(re.findall(r'\b[A-Za-z_]\w*\b', p.loops[0].guard+' '+b)))
    decisions = branches
    for match in re.finditer(r'\bif\s*\(', b):
        end = _match_paren(b, b.index('(', match.start()))
        if end >= 0 and re.match(r'\s*(?:\{\s*)?break\s*;', b[end+1:]):
            decisions -= 1
    if re.search(r'\b(return|goto)\b', b) or re.search(r'\[[^\]]*\]', source):
        return None, 'complex_control_or_array'
    if variables > 12 or branches > 6 or statements > 24 or len(source) > 4000:
        return None, 'extreme_static_complexity'
    if assignments == 0:
        return None, 'no_loop_updates'
    nonlinear = bool(re.search(r'\b[A-Za-z_]\w*\s*\*\s*[A-Za-z_]\w*\b', b))
    if active_variables <= 2 and assignments <= 1 and decisions <= 1 and not nonlinear:
        level = 'easy'
    elif active_variables > 6 or decisions > 2 or assignments > 7 or statements > 15:
        level = 'challenging'
    else:
        level = 'medium'
    return dict(level=level, variables=variables, branches=branches,
                active_variables=active_variables, decisions=decisions,
                statements=statements, assignments=assignments, nonlinear=nonlinear), None


def audit(job):
    index, source = job
    start = time.monotonic()
    def timeout(signum, frame):
        raise TimeoutError('sampler exceeded 15 seconds')
    signal.signal(signal.SIGALRM, timeout)
    signal.alarm(15)
    try:
        examples = ExampleSampler(source, n_runs=12, seed=0).sample()
        stats = examples.stats.get(0, {})
        n = len(examples.groups())
        reason = None
        if not examples.pos() or n < 12:
            reason = 'insufficient_samples'
        elif stats.get('unsupported_state') or stats.get('untracked_state'):
            reason = 'unsupported_state'
        elif stats.get('skipped_abnormal_run_count', 0):
            reason = 'abnormal_execution'
        return dict(pool_row=index, accepted=reason is None, reason=reason,
                    negative_groups=n, positive_states=len(examples.pos()),
                    families=dict(Counter(examples.group_families())),
                    sampler_stats=stats, seconds=round(time.monotonic()-start, 3))
    except Exception as ex:
        return dict(pool_row=index, accepted=False, reason='sampler_error',
                    error=str(ex)[:500], seconds=round(time.monotonic()-start, 3))
    finally:
        signal.alarm(0)


def distribution(sources):
    counts = Counter(family(s, True) for s in sources)
    features = [inspect_source(s)[0] for s in sources]
    supported = [f for f in features if f]
    return dict(rows=len(sources), broad_families=len(counts),
                max_family_rows=max(counts.values()),
                top10_family_share=sum(n for _, n in counts.most_common(10))/len(sources),
                effective_family_count=len(sources)**2/sum(n*n for n in counts.values()),
                static_eligible=len(supported),
                difficulty_counts=dict(Counter(f['level'] for f in supported)),
                eligible_feature_medians={k:statistics.median(f[k] for f in supported)
                                          for k in ('active_variables','decisions','assignments')})


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--pool', type=Path, default=Path('traindata/craft_raw.parquet'))
    ap.add_argument('--output', type=Path, default=Path('traindata/craft_rl_10k.parquet'))
    ap.add_argument('--count', type=int, default=10000)
    ap.add_argument('--multiple', type=int, default=64)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--rebuild', action='store_true', help='Rebuild this generated output from the cached audit')
    args = ap.parse_args()
    if args.multiple < 1 or args.count < args.multiple:
        ap.error('count must be at least the positive batch multiple')
    for suffix in ('', '.manifest.json'):
        if Path(str(args.output)+suffix).exists() and not args.rebuild:
            raise FileExistsError(str(args.output)+suffix)
    table = pq.read_table(args.pool)
    rows = table.to_pylist()
    source_list = [source_of(r) for r in rows]
    seen = set(); excluded = Counter(); features = {}; groups = defaultdict(list)
    for index, source in enumerate(source_list):
        sha = digest(source)
        if sha in seen:
            excluded['duplicate_source'] += 1
            continue
        seen.add(sha)
        feat, reason = inspect_source(source)
        if reason:
            excluded[reason] += 1
            continue
        feat.update(source_sha256=sha, family=family(source), broad_family=family(source, True))
        features[index] = feat
        groups[feat['family']].append(index)
    rng = random.Random(20260906)
    keys = sorted(groups); rng.shuffle(keys)
    for values in groups.values():
        rng.shuffle(values)
    # Round-robin families first; additional variants are admitted in later passes.
    order = [groups[k][depth] for depth in range(3) for k in keys if depth < len(groups[k])]
    limits = {'easy': round(args.count*.1), 'challenging': round(args.count*.075), 'medium': args.count}
    selected = []; counts = Counter(); fam_counts = Counter(); broad_counts = Counter()
    audit_path = Path(str(args.output)+'.audit.jsonl')
    cached = {}
    if audit_path.exists():
        for line in audit_path.read_text().splitlines():
            r = json.loads(line)
            cached[r['pool_row']] = r
    all_audits = []; cursor = 0
    print(json.dumps({'eligible':len(features), 'families':len(groups), 'levels':dict(Counter(f['level'] for f in features.values())), 'exclusions':dict(excluded)}),flush=True)
    with audit_path.open('a') as ledger, ProcessPoolExecutor(max_workers=args.workers) as pool:
        while cursor < len(order) and len(selected) < args.count:
            batch = []
            while cursor < len(order) and len(batch) < 128:
                index = order[cursor]; cursor += 1; feat = features[index]
                if counts[feat['level']] >= limits[feat['level']] or fam_counts[feat['family']] >= 3 or broad_counts[feat['broad_family']] >= 8:
                    continue
                batch.append(index)
            fresh = iter(pool.map(audit, [(i,source_list[i]) for i in batch if i not in cached]))
            for index in batch:
                result = cached[index] if index in cached else next(fresh)
                if result['seconds'] > 15 and result['accepted']:
                    result = dict(result, accepted=False, reason='sampler_cost_over_15s')
                all_audits.append(result)
                if index not in cached:
                    ledger.write(json.dumps(result)+'\n'); ledger.flush()
                index = result['pool_row']; feat = features[index]
                if not result['accepted'] or len(selected) >= args.count:
                    continue
                if counts[feat['level']] >= limits[feat['level']] or fam_counts[feat['family']] >= 3 or broad_counts[feat['broad_family']] >= 8:
                    continue
                selected.append(index); counts[feat['level']] += 1
                fam_counts[feat['family']] += 1; broad_counts[feat['broad_family']] += 1
            print(f'audited={len(all_audits)} selected={len(selected)} levels={dict(counts)}',flush=True)
    rng.shuffle(selected)
    aligned_count = len(selected) // args.multiple * args.multiple
    if not aligned_count:
        raise ValueError('too few eligible rows for the requested batch multiple')
    batch_alignment_dropped = selected[aligned_count:]
    selected = selected[:aligned_count]
    counts = Counter(features[i]['level'] for i in selected)
    fam_counts = Counter(features[i]['family'] for i in selected)
    broad_counts = Counter(features[i]['broad_family'] for i in selected)
    pq.write_table(table.take(selected), args.output)
    # Verify exact row preservation against pool, including reward metadata.
    reread = pq.read_table(args.output).to_pylist()
    assert reread == [rows[i] for i in selected]
    assert len({source_list[i] for i in selected}) == len(selected)
    from experiments.gpt5nano_full832.common import discover_tasks
    evaluation_sources = [t.hidden_source for t in discover_tasks()]
    selected_sources = [source_list[i] for i in selected]
    evaluation_exact = {s.strip() for s in evaluation_sources}
    evaluation_alpha = {family(s) for s in evaluation_sources}
    comparison = {'new':distribution(selected_sources),
                  'evaluation_832':distribution(evaluation_sources),
                  'evaluation_exact_source_matches':sum(s.strip() in evaluation_exact for s in selected_sources),
                  'evaluation_alpha_matches':sum(family(s) in evaluation_alpha for s in selected_sources)}
    old_path = Path('traindata/craft_rl.parquet')
    if old_path.exists():
        comparison['old_rl'] = distribution([source_of(r) for r in pq.read_table(old_path).to_pylist()])
    lookup = {r['pool_row']:r for r in all_audits}
    report = dict(pool=str(args.pool), pool_sha256=hashlib.sha256(args.pool.read_bytes()).hexdigest(),
                  output=str(args.output), rows=len(selected), requested=args.count,
                  batch_multiple=args.multiple, batches=len(selected)//args.multiple,
                  batch_alignment_dropped_pool_rows=batch_alignment_dropped,
                  output_sha256=hashlib.sha256(args.output.read_bytes()).hexdigest(),
                  seed=20260906, sampler_schema=NEGATIVE_SCHEMA_VERSION,
                  policy='unchanged pool rows; unique source; alpha family cap 3; constant-abstract family cap 8; easy <=1000; challenging <=750 (for requested 10k); >=12 current negative groups; no abnormal runs; sampler audit timeout 15s',
                  evaluation_informed=True,
                  evaluation_use='832 target-hidden static complexity distributions inspected to refine difficulty proxies and reduce challenging-task quota; no verification labels, target assertions, per-test matching, or SFT answers used in selection',
                  difficulty_rules={'easy':'active variables <=2, updates <=1, non-exit decisions <=1, no variable multiplication', 'challenging':'active variables >6 or non-exit decisions >2 or updates >7 or statements >15', 'medium':'remaining eligible sources'},
                  difficulty_limit='Static proxy only; not measured against the trained policy.',
                  levels=dict(counts), families=len(fam_counts), broad_families=len(broad_counts),
                  static_exclusions=dict(excluded), audited=len(all_audits),
                  audit_rejections=dict(Counter(r['reason'] for r in all_audits if not r['accepted'])),
                  exact_pool_row_equality_verified=True,
                  comparison=comparison,
                  selected=[dict(output_row=j,pool_row=i,file_id=rows[i]['extra_info']['file_id'],**features[i],negative_groups=lookup[i]['negative_groups']) for j,i in enumerate(selected)])
    Path(str(args.output)+'.manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='selected'},indent=2),flush=True)


if __name__ == '__main__':
    main()
