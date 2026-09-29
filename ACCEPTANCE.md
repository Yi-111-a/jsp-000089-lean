# ACCEPTANCE — JSP-000089

Catalog statement:

> Is there a density-zero set of positive integers such that every sufficiently
> dense graph has a cycle with length in that set?

Required theorem: `jsp_000089_main`

## Lean statement proved

```lean
theorem jsp_000089_main :
    ¬ (∃ (L : Set ℕ), (∀ n : ℕ, 0 < n → Even n → n ∈ L) ∧ zeroDensity L)
```

together with the supporting results

```lean
-- JSPProblem/Cycles.lean
theorem walk_parity     -- parity lemma for walks
theorem bipartite_cycle_even   -- every cycle of a bipartite graph has even length
-- JSPProblem/Density.lean
theorem not_zeroDensity_of_contains_even  -- all evens is not density zero
```

Supporting definitions: `zeroDensity`, `DenseAt`, `Unavoidable`.

## Status

`lake build` OK, 0 `sorry`, 0 `admit`, `jsp_000089_main` proved.
`harness/score.py problems/JSP-000089/lean` reports `prize_ready: true`.

## Documented remaining gap

The full Liu–Montgomery average-degree theorem is not formalised; see
`discovery/JSP-000089/policy.json` → `blockers`.
