# Version-bound resolution certificates

This repository is the standalone executable artifact for **Version-Bound
Resolution Certificates for Boolean Contract Edits**. It contains a strict JSON
ordinary-resolution checker, generic proof-survival circuits, an exact Horn
specialization, independent finite oracles, deterministic experiments, raw
results, and an evidence auditor.

## Reproduce all retained results

Requirements: Linux and Python 3.10 or newer, with assertions enabled. The full
runner and measurement drivers use the Unix-only `resource` module and Linux
peak-RSS units. The pure checker/encoding APIs and unit suite do not require
that telemetry; running them on another host is not a full reproduction.

From the repository root:

```sh
python3 reproduce.py --out reproduced-results
```

The output directory must not already exist. The runner uses only the Python
standard library and bundled inputs. It schedules at most four independent
children concurrently; every individual experiment is single-worker. Each child
has a 180-second wall timeout. No network, external SAT solver, GPU, model API,
or private dataset is used.

The retained complete Linux run wrote `reproduction.json`, reported 14 successful
children, ran 91 tests, and compared 26 scientific files across 12 result families.
Resource timings are observational and are excluded from exact equality checks;
all semantic CSV content and all non-timing JSON fields must match.
The archived `results/checks/` logs retain the earlier 88-test Linux run; their
timings and resource observations are not measurements of the current host.

Generate without comparing retained results:

```sh
python3 reproduce.py --out fresh-results --no-compare
```

Run the test suite alone:

```sh
python3 -m unittest discover -s tests -v
```

Focused file-free ready-order regressions are available separately:

```sh
python3 -B -m unittest discover -s tests -p 'test_horn_ready.py' -v
```

These six tests compare the minimum-heap order with a test-local smallest-ready
scan, including all 64 forward-edge sets and their four-atom relabelings. Small
Horn/deletion cases retain literal-truth, exact gate, witness, cut and budget
checks. The heap preserves the deterministic order; it adds no runtime claim.
The recorded 91-test Linux results are retained campaign evidence, not a fresh
execution of the expanded suite.

## Checked modes

### Ordinary proof packets

`src/certificates.py` accepts canonical clauses and topologically ordered axiom
or exact binary-resolution nodes. It recomputes every root support and rejects
unknown fields, duplicate identifiers, forward/cyclic references, wrong pivots,
wrong resolvents, body mismatches, malformed literals, and oversized inputs.

### Trace and closed resolution circuits

`src/survival.py` validates a finite certificate and compiles a monotone circuit
whose leaves are exact source identifier/body pairs.

- **Trace mode** admits an explicit checked leaf set `A` (possibly a proper
  subset of the source, including empty) and any checked subset of schemas. Layer
  zero ranges only over `A`; an omitted source identifier creates no implicit
  leaf. Trace is sound and may return false even when another retained-source
  proof exists.
- **Closed mode** requires `A` to equal the complete source identifier set and
  additionally checks the root, every non-tautological binary resolvent, the
  complete oriented schema relation, and sufficient fixed-point depth. It is
  exact for UNSAT of the exact retained-source subset, but closure can be
  exponential.

Replay and false-root cut extraction use explicit stacks plus topological gate
order rather than Python recursion. A true root is not accepted on its Boolean
value alone: the implementation first counts the exact selected ordinary proof
nodes, enforces a replay limit no larger than the ordinary checker's 100,000-node
bound, emits the packet, and checks it again. Source-positive certificates that
already exceed the limit are rejected at admission; the bundled wide-chain test
constructs the 2,301-gate circuit but rejects its 101,001-node replay before
proof materialization. If an edit exposes a larger
over-budget surviving path, `ReplayBudgetExceeded` is a resource rejection; it
is neither logical false nor proof acceptance. A false root can produce a
deterministic sufficient blocking cut. No minimum or whole-target SAT claim is
made.
Monotonicity concerns circuit truth, not budgeted acceptance. Restoring a leaf
can change the deterministic selected proof to a larger over-budget witness;
the implementation does not search for a minimum or an alternative within budget.

### Exact Horn circuits

`src/horn.py` validates that every source clause is Horn and compiles facts,
headed rules, and negative constraints over exact version leaves.

- general dependency graphs use at most `|V|` fixed-point layers;
- acyclic graphs use one topological pass and a linear-size circuit;
- every accepted positive root reconstructs and rechecks an ordinary
  resolution refutation under the same replay-node budget;
- `src/horn_oracle.py` is a separate queue-based oracle and imports neither the
  Horn compiler nor the ordinary checker.

Classical Horn satisfiability is not claimed as new. The artifact studies exact
version binding, checked proof replay, and reuse under edits.

## Repository map

- `src/certificates.py`, `src/check.py` - ordinary resolution packets and CLI.
- `src/survival.py`, `src/survival_producer.py` - generic trace/closed circuits.
- `src/horn.py`, `src/horn_oracle.py` - exact Horn compiler and independent
  retained-source oracle.
- `src/*_probe.py` - deterministic complete or bounded experiments.
- `src/result_audit.py` - independent row-level aggregation and invariants.
- `tests/` - parser, proof, circuit, Horn, reference, budget, and tamper tests,
  including the focused current ready-order regressions.
- `inputs/` - all hand-written JSON fixtures.
- `results/` - retained row-level evidence, summaries, logs, and resource record.
- `proofs/arguments.md` - mathematical definitions, proofs, and nonclaims.
- `claim_evidence_ledger.csv` - claim-to-proof/test/result map.
- `reference_audit.csv`, `external_resources.csv`, `sources.md` - literature and
  workflow provenance.

## Principal retained results

- 19,182 two-variable radius-two edit queries: closed mode accepts and rechecks
  all 16,003 retained-source UNSAT targets; one proof misses 2,319.
- 19,683 all-source/all-deletion pairs: 10,787 UNSAT targets, zero mismatch.
- 25,772 three-variable deletion queries: 4,769 UNSAT targets, 87 recovered
  selected-proof misses, zero closed miss.
- 9,921 complete small Horn pairs: 846 UNSAT, three selected-proof misses
  recovered, zero oracle or update mismatch.
- 560 generated Horn scale queries through 4,128 atoms and 16,420 clauses: 528
  UNSAT, 515 selected-proof misses recovered, zero oracle or update mismatch.
  Here the retained `horn_accept` column records circuit truth; only nine
  fixed-position positive queries were replayed. It does not record 528
  proof-carrying cache acceptances. All 846 small-family Horn positives replay.
- duplicate-unit `k=64`: `2^64` minimal supports represented by 25,155 generic
  gates.

These are complete only for the stated finite domains or deterministic generated
families. They are not industrial SAT, RTL, firmware, device, or timing results.
The recorded fanout fractions count Boolean gates re-evaluated in the marked
cone. The immutable reference update still validates and sorts complete target
snapshots, copies all gate values, scans all admitted leaves, and sorts affected
indices; the fractions are not total-work or runtime speedups.

## Trust and threat boundary

The current Ubuntu / CPython 3.12.14 reproduction passed 91 tests and all 14
commands. All 26 scientific files agreed, excluding only declared timing/RSS
fields. Elapsed time was 68.263204 seconds, aggregate child CPU 126.870280
seconds, and Horn-probe peak RSS 674,428 KiB. Current records are retained in
`results/measurements/current-linux/`; a single-child peak is not aggregate
concurrent memory.

Trusted for this artifact: the strict parser/checkers, circuit evaluators, Python
interpreter, and host operating system. Untrusted: producers, serialized proof
packets, targets, result claims, and cached support summaries. Replayed proofs
reduce the trusted surface but do not create implementation diversity or a
machine-checked theorem. The row-level auditor checks its declared coverage,
identifier, aggregate, and circuit-size invariants; it is not a general validator
of the interpreter, parser, filesystem, or the entire reproduction workflow.
Negative tests cover missing rows, generic/Horn gate corruption, uniformly
shifted Horn masks, equal-row-count query-ID substitution, and fanout-summary-only
tampering.

Persistent or distributed deployment additionally requires authenticated
formula/certificate binding, safe serialization, freshness and rollback policy,
concurrency control, and a verified source-to-CNF identity pipeline. Those are
not implemented here.

## License and third-party material

Repository-authored code and text are released under `LICENSE`. Scholarly
publications are not redistributed. `external_resources.csv` records canonical
locators, access scope, and license notes. The paper build separately retains the
supplied IEEE class and bibliography style under their own terms.
