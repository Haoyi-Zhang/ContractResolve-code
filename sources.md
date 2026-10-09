# Source and literature audit

## Inventory

The manuscript contains **63 unique scholarly references**, all cited in
the body. The inventory has 60 DOI locators and three official academic archive
URLs. No publication is redistributed and the manuscript contains no
`\nocite{*}` padding.

`reference_audit.csv` records, for every cited key:

- normalized title and publication year;
- canonical locator and locator type;
- audit status and access date;
- review depth actually used in this project;
- the manuscript role supported by the source.

`paper/preflight.py` fails if the BibTeX and audit inventories differ in key,
title, year, or locator, if any item is uncited, or if the expected locator
counts change. `tests/test_reference_audit.py` independently checks uniqueness
and locator structure. These checks establish inventory consistency, not that
every paper was read cover to cover or that every interpretation is immune to
scholarly disagreement.

## Review-depth labels

- **Substantive or targeted text inspection**: the relevant theorem, method,
  format, experiment, or limitation was inspected in the source text.
- **Metadata and claim-relevance inspection**: canonical bibliographic metadata
  and the source's relevance to the cited background statement were checked.

The closest and most load-bearing works received targeted text inspection,
including proof formats/checkers, incremental certification, proof-valid
caching, algebraic certificate recycling, SMT core reuse, provenance/knowledge
compilation, contract theory, and the classical Horn linear-time result.

## Closest-work boundary

The manuscript does not claim invention of AND--OR provenance, alternative
justifications, Horn forward chaining, BDD/ZDD compilation, incremental SAT, or
proof logging. Its narrow delta is the combination of:

1. exact identifier/body version binding;
2. fail-closed admission of finite resolution alternatives;
3. mandatory ordinary-proof replay for every positive result;
4. retained-source exactness in closed mode and in the Horn specialization;
5. edit-local evaluation and explicit negative-result semantics.

Recent proof-valid caching studies premise erasures and alternative proof
structure; algebraic recycling studies parameterized certificate patterns; and
Cache-a-lot studies SMT core reuse under substitutions. The manuscript presents
these as adjacent work and does not assert priority over them.

## Venue and workflow sources

`external_resources.csv` separately records the live TCAD instructions, IEEE
template selector, supplied IEEE class/style files, and the Python runtime. The
venue page was rechecked on 2026-09-20. It must be checked again immediately
before any external submission because page limits, anonymity, templates, and
AI-disclosure rules can change.
