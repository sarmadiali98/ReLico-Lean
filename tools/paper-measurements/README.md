# Measurement scripts behind the paper-corrections ledger

These three scripts produced the measured numbers cited in
[`docs/PAPER_CORRECTIONS.md`](../../docs/PAPER_CORRECTIONS.md) and in
[`docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`](../../docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md).
They live in git so that every claim in the ledger is reproducible rather than asserted. They were
previously kept in gitignored `tmp/`, which meant a single `rm -rf tmp` would have left the ledger
citing evidence nobody could regenerate.

They are not part of the benchmark pipeline. Nothing in `tests/` invokes them, no manifest references
them, and they contribute no obligations. They are read-only analysis tools, run by hand when a claim
needs rechecking.

## The external input, and why it is not in the repo

Two of the three need the **upstream ReLico example corpus**, which is a snapshot of
`github.com/sarmadiali98/ReLico` and is deliberately not vendored here. Obtain it either by cloning
that repository or from the `examples.zip` snapshot the user provided on 2026-08-17, then point the
script at the unpacked root:

~~~text
unzip examples.zip -d /tmp/relico_corpus
python3 tools/paper-measurements/measure_priority_requirement.py /tmp/relico_corpus
python3 tools/paper-measurements/census_topology_constructs.py /tmp/relico_corpus
~~~

Both walk the tree for `*.rebeca` and parse the text lexically — no Java, no RMC, no network. One
trap worth knowing: a naive `find` reports 98 models because half the entries are `__MACOSX` `._`
resource forks, so any filter must exclude `*__MACOSX*`. The real count is 49.

## What each one establishes

`measure_priority_requirement.py` compares two candidate scopes for the "absent `@priority` means
reject" rule over the 43 statically analysable models. It is the source of the 40/43 figure for the
blanket rule, the 9/43 figure for the contention-scoped rule, the finding that `KeepAlive ka` is never
a sender into a contended message server, and the finding that all three actor-priority tie models
have zero contended message servers. Those four numbers decided the frontend's well-formedness rules
and are quoted in ledger entries P4 and P5.

`census_topology_constructs.py` enumerates the constructs that defeat static topology resolution — the
A1 through A4 diagnostics — and identifies the five models that use them. It is the source of ledger
entry P6 and of the A1-A4 rejections the general exporter emits.

`lf_semantics_probe.sh` is different in kind: it must run on a machine with a real `lfc`, and it
compiles and executes small Lingua Franca programs to settle questions the LF documentation leaves
ambiguous. It established that `lfc 0.11.0` rejects `reaction(in[0])`, so multiports cannot carry the
§III-D fan-in construction and named ports are forced; that reaction declaration order does decide
same-tag order within one reactor; and that unconnected input ports are legal. Ledger entries P1, P2
and P3 rest on it. It was last run against `lfc 0.11.0` on 2026-08-17, and its conclusions should be
re-established rather than assumed if the toolchain version moves.
