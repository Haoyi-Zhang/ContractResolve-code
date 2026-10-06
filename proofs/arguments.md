# Mathematical arguments and guarantee boundaries

This note states the general arguments used by the reference implementation. It
is conventional mathematics, not a proof-assistant development.

## 1. Versioned formulas

A canonical non-tautological clause is a sorted duplicate-free tuple of nonzero
signed integers. A versioned formula is a finite map `F : identifier -> clause`.
For source `F` and target `G`, the exact retained source is

```text
R_F(G) = { F(i) | i is in both maps and G(i) = F(i) }.
```

Equal bodies under different identifiers remain different version leaves. This
is a provenance policy, not a claim that identifier equality is required for
logical entailment: a separately authorized rename map could safely broaden the
policy if it preserved body equality and proof replay.

## 2. Generic layered resolution circuit

A checked certificate declares an admitted identifier set `Aset` contained in
`dom(F)`, serialized as exact source pairs `(i,F(i))`, together with a finite
clause universe, exact oriented binary-resolution schemas, a root, and a depth
`d`. Trace mode may admit a proper subset, including the empty set. Closed mode
requires `Aset = dom(F)`.

For clause `C`, let `D_0(C)` be the OR of active exact leaves whose identifiers
are in `Aset` and whose body is `C`. Omitted source identifiers do not create
implicit leaves. For `t > 0`,

```text
D_t(C) = D_(t-1)(C)
         OR
         OR over checked schemas P,Q -> C of
            (D_(t-1)(P) AND D_(t-1)(Q)).
```

**Layer lemma.** `D_t(C)` is true exactly when the active admitted source leaves
have a derivation of `C` of height at most `t` using the admitted schemas.

*Proof.* Induction on `t`. Layer zero consists exactly of active admitted
axioms. At a positive layer, persistence preserves shorter derivations and every
true schema AND combines two derivations from the preceding layer. Conversely,
every gate used by a true OR branch is either persistence or a checked schema
with true parents. QED.

## 3. Replay soundness

Every source leaf is checked against the source identifier and body. Every
schema is checked to be the exact non-tautological binary resolvent with the
stated positive pivot orientation.

**Theorem.** If the root gate is true under target `G`, the admitted exact
leaves and checked schemas entail the requested root, hence `G` entails it. The
implementation selects one true proof sub-DAG with an explicit stack, processes
selected gates in topological index order, and computes the exact number of
ordinary axiom and resolution nodes before materialization. If that count is at
most the admitted replay limit `B`, it emits an ordinary proof and the ordinary
checker accepts it.

The same `B` is enforced at source admission and every later replay, and it may
not exceed the ordinary checker's `MAX_NODES`. A source-positive certificate
whose selected replay exceeds `B` is rejected during admission. A later target
may keep the circuit logically true while deleting a short path and exposing a
larger selected witness; exceeding `B` then raises `ReplayBudgetExceeded`. This
is a resource rejection, not logical false and not proof acceptance. Replay is
mandatory; increasing the Python recursion limit or bypassing replay is not part
of the contract.

Monotonicity applies to the logical root, not to acceptance under `B`. Restoring
leaves can change deterministic OR selection to a larger witness; the remaining
existence of a smaller proof does not require this implementation to find it.
For example, with an empty source axiom permitting admission at `B=5`, a target
can replay a one-antecedent Horn derivation in five nodes. Restoring a fact can
enable an earlier three-antecedent rule whose selected replay has nine nodes.
The root remains true, but the latter replay is resource-rejected.

## 4. Closed-mode exactness

Closed mode first requires `Aset = dom(F)`. It then checks that the finite
universe contains every source body and the root, contains every
non-tautological binary resolvent of its members, and lists the complete oriented
schema relation. The depth is at least the universe size.

**Finite saturation lemma.** A finite non-tautological clause set closed under
all non-tautological binary resolvents contains the empty clause iff it is
unsatisfiable.

*Argument.* Eliminate variables by the Davis--Putnam rule. For pivot `x`, keep
clauses not containing `x` or `-x` and add every non-tautological resolvent of a
positive and negative pivot clause. This transformation preserves
satisfiability: any old model satisfies the resolvents; conversely, a model of
the eliminated set can choose a value for `x` unless positive and negative
requirements conflict, in which case their violated remainders form a violated
resolvent. Repeating over the finite variable set leaves only either no clause or
the empty clause. Closure ensures every generated non-tautological resolvent was
already present. QED.

**Closed exactness theorem.** With the empty root, the final closed-mode gate is
true iff `R_F(G)` is UNSAT. Soundness follows from replay. For completeness, the
retained active set is UNSAT, so finite saturation derives the empty clause.
Each strict layer can add at least one previously unavailable clause; no more
than the finite universe size is needed.

Closure may be exponential. Closed mode is a bounded exact oracle, not a
production-scale construction.

## 5. Exact Horn specialization

A Horn clause has at most one positive literal. Write a headed clause as

```text
(-a1 OR ... OR -ak OR h)
```

and a negative constraint as

```text
(-a1 OR ... OR -ak).
```

Every clause has an exact version leaf `x_q`. Let `H_t(v)` mean that atom `v` is
forward-derivable in at most `t` rounds from active retained clauses:

```text
H_0(v) = OR of x_q for active fact clauses q = (v)
H_t(v) = H_(t-1)(v)
         OR
         OR over headed rules q with head v of
            x_q AND AND over a in antecedents(q) H_(t-1)(a).
```

The conflict root is the OR, over every negative constraint `q`, of `x_q` AND
all final antecedent gates.

**Horn exactness theorem.** At round `t`, `H_t(v)` is true exactly when retained
Horn forward chaining derives `v` in at most `t` rounds. At most `|V|` strict
rounds are needed because every productive round adds an atom. A Horn formula is
UNSAT exactly when its least forward-chaining model activates a negative
constraint. Hence the root is true iff `R_F(G)` is UNSAT.

For replay, an explicit stack selects the necessary facts, headed rules, and
negative constraint. A topological pass shares selected antecedent-unit proofs,
starts each rule from its retained Horn clause, and resolves away each negative
antecedent. A headed rule ends at its positive unit; a negative constraint ends
at the empty clause. Before allocating the packet, the checker counts one node
per selected leaf plus one resolution node per selected antecedent occurrence
and applies the same replay budget used by the ordinary checker. Within budget,
the ordinary checker validates the emitted proof; over budget, the result is an
explicit resource rejection rather than logical false.

If every headed dependency points forward in a DAG, process atoms in topological
order. Each rule fires once and every atom OR is constructed once; the result is
exact without fixed-point unrolling.

## 6. Exact size formulas

### Generic resolution circuit

With `n = |Aset|` admitted exact axiom leaves, `m` clauses, `s` schemas, and
depth `d`:

```text
N = n + (d + 1)m + ds gates
E = n + dm + 3ds parent edges.
```

The terms are respectively leaves, clause OR gates, schema AND gates, leaf-to-
layer-zero edges, persistence edges, and the two schema inputs plus schema-to-
clause edge. The implementation checks `N` before allocation. Gate bounds and replay-node
bounds are distinct: a small circuit can select an ordinary proof larger than
the checker's node limit.

### Horn circuit

Let `q` be source clauses, `v` atoms, `f` facts, `r` non-fact headed rules, `c`
negative constraints, and let `L_r` and `L_c` be total antecedent occurrences in
rules and constraints.

For acyclic dependencies:

```text
N_DAG = q + v + r + c + 1
E_DAG = f + 2r + L_r + 2c + L_c.
```

For `d` fixed-point rounds:

```text
N_FP = q + (d + 1)v + dr + c + 1
E_FP = f + d(v + 2r + L_r) + 2c + L_c.
```

Tests and the row-level auditor independently rederive these formulas.

## 7. Edit-local reevaluation

The compiled graph is acyclic and every leaf stores its outgoing fanout. The
semantic update operation changes exact-retention leaf values, marks their
transitive fanout, and recomputes marked internal gates in topological index
order.

**Theorem.** Given a correct prior evaluation of the same circuit, edit-local
update equals a full evaluation at every gate.

*Proof.* Gates outside changed-leaf fanout have identical leaf ancestors. Changed
leaves receive their new values. Every affected internal gate is recomputed only
after its parents. Induction over topological order proves equality. QED.

The immutable reference implementation is not asymptotically edit-only. It
validates and sorts the complete prior target snapshot, parses and sorts the
complete current target, copies and rematerializes all `N` gate values, scans all
`n` admitted leaves, traverses `E_delta`, sorts `k` affected gate indices, and
re-evaluates their Boolean logic. Ignoring literal canonicalization, this is

```text
O(N + g_prev log g_prev + g_next log g_next
    + n + E_delta + k log k).
```

A mutable delta API supplied with canonical changed identifiers could approach
`O(|Delta_A| + E_delta)`, but it is not implemented. The stored fanout fraction
counts only Boolean gates re-evaluated in the marked cone; it is not total work,
elapsed-time speedup, or evidence that the reference path avoids full scanning
and copying. The cone itself is conservative because it remains fully marked
even when an intermediate value does not change.

## 8. Sufficient blocking cuts

For a false gate, an explicit stack first marks the relevant false sub-DAG and
a topological pass computes the cut: a leaf contributes its identifier; a false
OR contributes the union of cuts for all parents; a false AND contributes one
deterministic false-parent cut.

**Theorem.** If every named leaf remains false, the selected gate remains false
regardless of other leaves. The result is sufficient, not minimum, necessary,
unique, or a minimal correction set.

For this fixed circuit, the contrapositive says that a leaf-only change making
the gate true must activate at least one named cut leaf, not necessarily all of
them. This necessity for fixed-circuit success does not constrain a new proof
using target additions or a different admitted schema library.

## 9. Exponential supports and representation boundary

For each `i`, include two identifiers for unit `(i)`, plus one clause
`(-1 OR ... OR -k)`. A minimal retained UNSAT support contains the negative
clause and exactly one identifier from each duplicate pair, giving `2^k`
supports. A checked chain uses `2k+1` leaves and `k` schemas, so the generic
layered circuit is polynomial for this family.

This is a separation only from explicit support listing. A suitable ROBDD may
also be linear; no canonicality or dominance over knowledge compilation is
claimed.

## 10. Old-only whole-target barrier

Take two targets with identical retained old leaves. One contains no new
conflicting clauses and is satisfiable; the other adds a fresh contradiction and
is unsatisfiable. Any predicate determined only by old retained leaves has the
same output on both targets and therefore cannot be both sound and complete for
whole-target UNSAT under arbitrary additions. This does not limit a fresh solver
or a certificate allowed to use new clauses.

## 11. Nonclaims

The arguments do not establish industrial speedup, minimum circuits/supports or
cuts, general DRAT/RAT migration, theory reasoning, semantic variable remapping,
authenticated persistent caches, source-to-CNF correctness, RTL/firmware/device
behavior, concurrency safety, or venue acceptance. The finite experiments check
implementations on their declared domains; they are not the proof of the general
theorems.
