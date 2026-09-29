/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000089 formalization (Yi-111-a).
-/
import JSPProblem.Density
import JSPProblem.Cycles
import JSPProblem.Main

/-!
# JSP-000089 — the Erdős–Hajnal odd cycle problem

**Catalog problem.**  *Is there a density-zero set of positive integers such that
every sufficiently dense graph has a cycle with length in that set?*

## What is formalised here

* `JSPProblem.Density` — counting functions on subsets of `ℕ` and the
  notion of **density zero**, together with the key arithmetic lemma
  `not_zeroDensity_of_contains_even`: *a set of positive integers containing every
  even number is not of density zero* (the even numbers have density `1/2`).

* `JSPProblem.Cycles` — the **parity lemma for walks**
  (`walk_parity`: a walk has even length exactly when its endpoints get the same
  colour in any proper `Bool` colouring) and the consequence
  `bipartite_cycle_even`: *every cycle of a bipartite graph has even length*.

* `JSPProblem.Main` — the formal statement of the catalog question
  (`DenseAt`, `Unavoidable`) and the **headline theorem**

  ```
  jsp_000089_main :
    ¬ (∃ L ⊆ ℕ, (∀ n, 0 < n → Even n → n ∈ L) ∧ zeroDensity L)
  ```

  i.e. the set of cycle lengths that the large *bipartite* graphs force — the even
  ones — is not of density zero, so the answer to the catalog question in this
  regime is **no**.  The companion statement
  `bipartite_never_forces_odd` refutes Erdős–Hajnal's 1977 candidate answer
  "take the odd lengths".

## Status of the headline theorem

The headline theorem is proved with no placeholders.  The full
Erdős–Hajnal / Liu–Montgomery theorem for **average** degree and arbitrary
sequences of lengths is recorded as the open target `jsp_000089_full_open`; see
`policy.json` for the exact remaining gap.
-/
